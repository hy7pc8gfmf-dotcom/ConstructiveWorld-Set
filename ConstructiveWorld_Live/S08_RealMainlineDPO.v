(* ConstructiveWorld-Set — Real-layer DPO/RLHF mainline: reward recovery, attention steady state, Top-K, and eps-ified optimality (constructive Set layer). *)

(** * S08_RealMainlineDPO: Real-layer DPO/RLHF mainline.

    Mission.  Formalizes the Real-layer DPO/RLHF mainline: reward
      recovery, the Boltzmann attention steady-state equation
      [real_steady_state_boltzmann_attn], Top-K selection, PPO
      conservativity, and eps-ified optimality [real_rlhf_optimal_eps]
      ([J(pi) := -F(pi) <= J(pi_star) + D * eps], in eps-weighted residual
      form).

    Dependencies.  Stdlib [QArith.QArith], [List], [Bool], [Arith],
      [Setoid], [Morphisms], [Lia].  Requires [S01_BaseRing] through
      [S07_RealSetoidExpLog] of this development.

    References.  This development, [CW_ConstructiveWorld_219.v], the
      baseline module in ConstructiveWorld-Main whose statement names
      are carried over here verbatim (statement-face Set-carrier
      completion); this module splits its region L41233-L46820, and
      the statement body matches that region.  Abstract finite sums
      are presented through the explicit interface variable [X]
      (extension and linearity of summation, instantiable).

    Constructivity.  All named statements live in the constructive
      [Set] layer with zero admitted statements (mechanically
      checked).

    Build.  [coqc -native-compiler no -q -Q . "" S08_RealMainlineDPO.v]
      compiles cleanly (exit 0). *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.

Section OppMultMain.
(* ============ 1. real_opp_mult: opp (mult a b) == mult a (opp b) ============
   Pointwise: [-(a_n * b_n)] == [a_n * (-b_n)] holds by rational ring
   simplification at each index, so [real_eq_of_zero_diff] applies. *)
Lemma real_opp_mult : forall (a b : Real),
  real_eq (real_opp (real_mult a b)) (real_mult a (real_opp b)).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  destruct a as [ua Ha].
  destruct b as [ub Hb].
  simpl.
  ring.
Qed.

(* ============ 2. real_opp_mult_r: opp (mult a b) == mult (opp a) b ============ *)
Lemma real_opp_mult_r : forall (a b : Real),
  real_eq (real_opp (real_mult a b)) (real_mult (real_opp a) b).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  destruct a as [ua Ha].
  destruct b as [ub Hb].
  simpl.
  ring.
Qed.

(* ============ 3. real_mult_opp_l: mult a (opp b) == opp (mult a b) (mirror direction) ============ *)
Lemma real_mult_opp_l : forall (a b : Real),
  real_eq (real_mult a (real_opp b)) (real_opp (real_mult a b)).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  destruct a as [ua Ha].
  destruct b as [ub Hb].
  simpl.
  ring.
Qed.
End OppMultMain.
(* ============ Gibbs pointwise core ============
   [real_mult_div] ([p * (q/p) == q], via the abstract [inv_correct]
   chain), [real_opp_opp] (involution of [opp]),
   [real_hpq1] ([p - q == p * (-(q/p - 1))]),
   [real_hpq2] ([p * (-X) == p * (-(X + eps)) + p * eps]),
   [real_gibbs_core_eps] ([p - q <= p * (-log(q/p)) + p * eps], the
   Gibbs pointwise core).  Core block of the per-eps Real-layer form
   of the Gibbs inequality (paper-2 §9.2/§10.2). *)
Section GibbsCoreMain.
(* ============ 1. [p * (q/p) == q] (abstract chain via [inv_correct]) ============ *)
Lemma real_mult_div : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  (* p·(q·(1/p)) == (p·q)·(1/p) == (q·p)·(1/p) == q·(p·(1/p)) == q·1 == q *)
  apply (real_eq_trans _ (real_mult (real_mult p q) (real_inv_pos p Hp)) _).
  - (* p·(q·(1/p)) == (p·q)·(1/p): associativity, directly. *)
    exact (real_mult_assoc p q (real_inv_pos p Hp)).
  - (* (p·q)·(1/p) == q: the remaining chain. *)
    apply (real_eq_trans _ (real_mult (real_mult q p) (real_inv_pos p Hp)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult p q) (real_inv_pos p Hp)
                                            (real_mult q p) (real_inv_pos p Hp)).
      * apply (real_mult_comm p q).
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult q (real_mult p (real_inv_pos p Hp))) _).
      * apply (real_eq_sym (real_mult q (real_mult p (real_inv_pos p Hp)))
                           (real_mult (real_mult q p) (real_inv_pos p Hp))).
        apply (real_mult_assoc q p (real_inv_pos p Hp)).
      * apply (real_eq_trans _ (real_mult q real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat q (real_mult p (real_inv_pos p Hp))
                                                q real_one).
           ++ apply real_eq_refl.
           ++ apply (real_inv_pos_correct p Hp).
        -- apply (real_mult_one q).
Qed.

(* ============ 2. real_opp_opp: opp (opp x) == x (pointwise ring) ============ *)
Lemma real_opp_opp : forall (x : Real),
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  destruct x as [ux Hx'].
  simpl. ring.
Qed.

(* ============ 3. Hpq1: p - q == p * (-(q/p - 1)) ============
   Abstract-level chain: p * (-X) == -(p * X) == -(q - p) == p - q with
   [X := q/p - 1].  Midpoint: p * X == q - p (distributivity,
   [real_mult_div], [real_opp_mult], [real_mult_one]). *)
Lemma real_hpq1 : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_plus p (real_opp q))
          (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))).
Proof.
  intros p q Hp.
  apply real_eq_sym.
  (* Step 1, midpoint: p * (q/p - 1) == q - p. *)
  assert (Hmid : real_eq (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))
                         (real_plus q (real_opp p))).
  { (* p * (q/p - 1) == p * (q/p) + p * (-1) == q + -p. *)
    apply (real_eq_trans _ (real_plus (real_mult p (real_mult q (real_inv_pos p Hp)))
                                      (real_mult p (real_opp real_one))) _).
    - apply (real_distrib p (real_mult q (real_inv_pos p Hp)) (real_opp real_one)).
    - apply (real_eq_trans _ (real_plus q (real_opp (real_mult p real_one))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_mult p (real_mult q (real_inv_pos p Hp)))
                                              (real_mult p (real_opp real_one))
                                              q (real_opp (real_mult p real_one))).
        * apply (real_mult_div p q Hp).
        * apply (real_eq_sym (real_opp (real_mult p real_one)) (real_mult p (real_opp real_one))).
          apply (real_opp_mult p real_one).
      + apply (RealSetoid.real_eq_plus_compat q (real_opp (real_mult p real_one))
                                              q (real_opp p)).
        * apply real_eq_refl.
        * apply (RealSetoid.real_eq_opp_compat (real_mult p real_one) p).
          apply (real_mult_one p). }
  (* Step 2, goal: p * (-X) == p - q.  p * (-X) == -(p * X) by
     [real_opp_mult], == -(q - p) == p - q. *)
  apply (real_eq_trans _ (real_opp (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))) _).
  - apply (real_eq_sym (real_opp (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))
                       (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))).
    apply (real_opp_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))).
  - (* -(p * X) == p - q: rewrite via [Hmid] (p * X == q - p), then
       -(q - p) == p - q. *)
    apply (real_eq_trans _ (real_opp (real_plus q (real_opp p))) _).
    + apply (RealSetoid.real_eq_opp_compat (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))
                                           (real_plus q (real_opp p))).
      exact Hmid.
    + (* -(q - p) == p - q: [real_opp_plus], [real_opp_opp], commutativity. *)
      apply (real_eq_trans _ (real_plus (real_opp q) (real_opp (real_opp p))) _).
      * apply (real_opp_plus q (real_opp p)).
      * apply (real_eq_trans _ (real_plus (real_opp q) p) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_opp q) (real_opp (real_opp p))
                                                 (real_opp q) p).
           ++ apply real_eq_refl.
           ++ apply (real_opp_opp p).
        -- apply (real_plus_comm (real_opp q) p).
Qed.

(* ============ 4. Hpq2: p * (-X) == p * (-(X + eps)) + p * eps, [X := q/p - 1] ============ *)
Lemma real_hpq2 : forall (p q eps : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))
          (real_plus (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                     (real_mult p eps)).
Proof.
  intros p q eps Hp.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  set (pn := projT1 p n).
  set (en := projT1 eps n).
  set (Xn := projT1 (real_mult q (real_inv_pos p Hp)) n).
  assert (Hl : projT1 (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))) n ==
               pn * (- (Xn + -1))).
  { unfold pn, Xn.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult q (real_inv_pos p Hp)) (real_opp real_one) n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj q (real_inv_pos p Hp) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    cbn [projT1 real_one].
    ring. }
  assert (Hr : projT1 (real_plus (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                                 (real_mult p eps)) n ==
               (pn * (- ((Xn + -1) + en))) + pn * en).
  { unfold pn, en, Xn.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                            (real_mult p eps) n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult q (real_inv_pos p Hp)) (real_opp real_one) n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj q (real_inv_pos p Hp) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj p eps n)).
    cbn [projT1 real_one].
    ring. }
  rewrite Hl, Hr.
  assert (Hq : pn * - (Xn + -1) == pn * - (Xn + -1 + en) + pn * en).
  { ring. }
  rewrite Hq.
  ring.
Qed.

(* ============ 5. Assembly, real_gibbs_core_eps (p - q <= p * (-log(q/p)) + p * eps) ============ *)
Lemma real_gibbs_core_eps : forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_plus p (real_opp q))
          (real_plus (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                      (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
                     (real_mult p eps)).
Proof.
  intros p q Hp Hq eps Hepspos.
  (* 1. real_log_le_linear_eps (q/p) eps *)
  assert (Hlin : real_le (real_log (real_mult q (real_inv_pos p Hp))
                                   (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
                         (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)).
  { apply (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_mult q (real_inv_pos p Hp)) eps
                                   (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))).
    exact Hepspos. }
  (* 2. opp_le_compat *)
  assert (Hopp : real_le (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps))
                         (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                             (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))).
  { apply (real_opp_le_compat (real_log (real_mult q (real_inv_pos p Hp))
                                        (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
                              (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)).
    exact Hlin. }
  (* 3. le_mult_compat: A * p <= B * p (A := -(q/p - 1 + eps), B := -log(q/p)). *)
  assert (Hmult : real_le (real_mult (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)) p)
                          (real_mult (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                         (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))) p)).
  { apply (real_le_mult_compat (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps))
                               (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                   (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
                               p).
    - exact Hp.
    - exact Hopp. }
  (* 4. Assembly: p - q == p * (-(q/p - 1)) ([real_hpq1])
        == p * (-(q/p - 1 + eps)) + p * eps ([real_hpq2])
        <= p * (-log(q/p)) + p * eps (commutativity bridge on [Hmult],
        then [le_plus_compat]).
     Chain: p - q <= p * B + p * eps, where p * B == B * p (comm). *)
  apply (real_le_trans (real_plus p (real_opp q))
                       (real_plus (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                                  (real_mult p eps))
                       (real_plus (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                   (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
                                  (real_mult p eps))).
  - (* p - q <= p * (-(q/p - 1 + eps)) + p * eps: p - q == p * (-(q/p - 1))
       == p * (-(q/p - 1 + eps)) + p * eps ([real_hpq1] then [real_hpq2]). *)
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (real_plus p (real_opp q))
                         (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))
                         (real_plus (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                                    (real_mult p eps))).
    + apply (real_hpq1 p q Hp).
    + apply (real_hpq2 p q eps Hp).
  - (* p * (-(q/p - 1 + eps)) + p * eps <= p * (-log(q/p)) + p * eps:
       [real_le_plus_compat] on the commutativity bridge for [Hmult]. *)
    apply (real_le_plus_compat (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                               (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
                               (real_mult p eps) (real_mult p eps)).
    + (* p * A <= p * B: [Hmult] gives A * p <= B * p; bridge by commutativity. *)
      apply (RealSetoid.real_le_id_l (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                                     (real_mult (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)) p)
                                     (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                     (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))).
      * apply (real_mult_comm p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps))).
      * apply (RealSetoid.real_le_id_r (real_mult (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)) p)
                                       (real_mult (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                     (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))) p)
                                       (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                       (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))).
        -- apply (real_mult_comm (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                     (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))) p).
        -- exact Hmult.
    + apply real_le_refl.
Qed.
End GibbsCoreMain.

Section RealListSumMain.
Variable X : Type.

(* ============ 0. real_list_sum: Fixpoint fold of [real_plus] (nil maps to [real_zero]) ============ *)
Fixpoint real_list_sum (f : X -> Real) (l : list X) : Real :=
  match l with
  | nil => real_zero
  | w :: rest => real_plus (f w) (real_list_sum f rest)
  end.

(* ============ 1. real_list_sum_ext: pointwise [real_eq] implies summed [real_eq] ============ *)
Lemma real_list_sum_ext : forall (f g : X -> Real) (l : list X),
  (forall w : X, real_eq (f w) (g w)) -> real_eq (real_list_sum f l) (real_list_sum g l).
Proof.
  intros f g l Hfg.
  induction l as [| w rest IH]; simpl.
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum f rest) (g w) (real_list_sum g rest)).
    + exact (Hfg w).
    + exact IH.
Qed.

(* ============ 2. real_plus_swap_mid: (a+b)+(c+d) == (a+c)+(b+d) ============ *)
Lemma real_plus_swap_mid : forall (a b c d : Real),
  real_eq (real_plus (real_plus a b) (real_plus c d))
          (real_plus (real_plus a c) (real_plus b d)).
Proof.
  intros a b c d.
  (* (a+b)+(c+d) == a+(b+(c+d)) [assoc, backwards] == a+((c+d)+b) [comm]
     == a+(c+(d+b)) [assoc, backwards] == a+(c+(b+d)) [comm] == (a+c)+(b+d) [assoc]. *)
  apply (real_eq_trans _ (real_plus a (real_plus b (real_plus c d))) _).
  - apply (real_eq_sym (real_plus a (real_plus b (real_plus c d)))
                       (real_plus (real_plus a b) (real_plus c d))).
    apply (real_plus_assoc a b (real_plus c d)).
  - apply (real_eq_trans _ (real_plus a (real_plus (real_plus c d) b)) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus b (real_plus c d))
                                            a (real_plus (real_plus c d) b)).
      * apply real_eq_refl.
      * apply (real_plus_comm b (real_plus c d)).
    + apply (real_eq_trans _ (real_plus a (real_plus c (real_plus d b))) _).
      * apply (RealSetoid.real_eq_plus_compat a (real_plus (real_plus c d) b)
                                              a (real_plus c (real_plus d b))).
        -- apply real_eq_refl.
        -- apply (real_eq_sym (real_plus c (real_plus d b)) (real_plus (real_plus c d) b)).
           apply (real_plus_assoc c d b).
      * apply (real_eq_trans _ (real_plus a (real_plus c (real_plus b d))) _).
        -- apply (RealSetoid.real_eq_plus_compat a (real_plus c (real_plus d b))
                                                a (real_plus c (real_plus b d))).
           ++ apply real_eq_refl.
           ++ apply (RealSetoid.real_eq_plus_compat c (real_plus d b) c (real_plus b d)).
              ** apply real_eq_refl.
              ** apply (real_plus_comm d b).
        -- apply (real_plus_assoc a c (real_plus b d)).
Qed.

(* ============ 3. real_list_sum_add: sum(f+g) == sum(f) + sum(g) ============ *)
Lemma real_list_sum_add : forall (f g : X -> Real) (l : list X),
  real_eq (real_list_sum (fun w => real_plus (f w) (g w)) l)
          (real_plus (real_list_sum f l) (real_list_sum g l)).
Proof.
  intros f g l.
  induction l as [| w rest IH]; simpl.
  - (* zero == zero + zero *)
    apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - (* (f w + g w) + (sum f rest + sum g rest) == (f w + sum f rest) + (g w + sum g rest). *)
    apply (real_eq_trans _ (real_plus (real_plus (f w) (g w))
                                      (real_plus (real_list_sum f rest) (real_list_sum g rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_plus (f w) (g w))
                                            (real_list_sum (fun w0 => real_plus (f w0) (g w0)) rest)
                                            (real_plus (f w) (g w))
                                            (real_plus (real_list_sum f rest) (real_list_sum g rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_plus_swap_mid (f w) (g w) (real_list_sum f rest) (real_list_sum g rest)).
Qed.

(* ============ 4. real_list_sum_linear: sum(a * f w) == a * sum(f) ============ *)
Lemma real_list_sum_linear : forall (a : Real) (f : X -> Real) (l : list X),
  real_eq (real_list_sum (fun w => real_mult a (f w)) l)
          (real_mult a (real_list_sum f l)).
Proof.
  intros a f l.
  induction l as [| w rest IH]; simpl.
  - (* zero == a * zero. *)
    apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - (* a * f w + a * sum f rest == a * (f w + sum f rest): distributivity, backwards. *)
    apply (real_eq_trans _ (real_plus (real_mult a (f w)) (real_mult a (real_list_sum f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult a (f w))
                                            (real_list_sum (fun w0 => real_mult a (f w0)) rest)
                                            (real_mult a (f w))
                                            (real_mult a (real_list_sum f rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_sym (real_mult a (real_plus (f w) (real_list_sum f rest)))
                         (real_plus (real_mult a (f w)) (real_mult a (real_list_sum f rest)))).
      apply (real_distrib a (f w) (real_list_sum f rest)).
Qed.

(* ============ 5. real_list_sum_linear_r: sum(f w * a) == a * sum(f) (constant on the right) ============ *)
Lemma real_list_sum_linear_r : forall (a : Real) (f : X -> Real) (l : list X),
  real_eq (real_list_sum (fun w => real_mult (f w) a) l)
          (real_mult a (real_list_sum f l)).
Proof.
  intros a f l.
  apply (real_eq_trans _ (real_list_sum (fun w => real_mult a (f w)) l) _).
  - apply (real_list_sum_ext (fun w => real_mult (f w) a) (fun w => real_mult a (f w)) l).
    intro w. apply (real_mult_comm (f w) a).
  - apply (real_list_sum_linear a f l).
Qed.

(* ============ 6. real_opp_zero and real_list_sum_opp: sum(opp f) == opp(sum f) ============ *)
Lemma real_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  (* opp zero == (opp zero)+zero [plus_zero, backwards] == zero+(opp zero) [comm, backwards]
     == zero [plus_opp]. *)
  apply (real_eq_trans _ (real_plus (real_opp real_zero) real_zero) _).
  - apply (real_eq_sym (real_plus (real_opp real_zero) real_zero) (real_opp real_zero)).
    apply (real_plus_zero (real_opp real_zero)).
  - apply (real_eq_trans _ (real_plus real_zero (real_opp real_zero)) _).
    + apply (real_plus_comm (real_opp real_zero) real_zero).
    + apply (real_plus_opp real_zero).
Qed.

Lemma real_list_sum_opp : forall (f : X -> Real) (l : list X),
  real_eq (real_list_sum (fun w => real_opp (f w)) l)
          (real_opp (real_list_sum f l)).
Proof.
  intros f l.
  induction l as [| w rest IH]; simpl.
  - (* zero == opp zero *)
    apply (real_eq_sym (real_opp real_zero) real_zero).
    exact real_opp_zero.
  - (* (opp (f w)) + (opp (sum f rest)) == opp (f w + sum f rest). *)
    apply (real_eq_trans _ (real_plus (real_opp (f w)) (real_opp (real_list_sum f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp (f w))
                                            (real_list_sum (fun w0 => real_opp (f w0)) rest)
                                            (real_opp (f w))
                                            (real_opp (real_list_sum f rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_sym (real_opp (real_plus (f w) (real_list_sum f rest)))
                         (real_plus (real_opp (f w)) (real_opp (real_list_sum f rest)))).
      apply (real_opp_plus (f w) (real_list_sum f rest)).
Qed.

(* ============ 7. real_list_sum_le: pointwise [real_le] implies summed [real_le] ============ *)
Lemma real_list_sum_le : forall (f g : X -> Real) (l : list X),
  (forall w : X, real_le (f w) (g w)) -> real_le (real_list_sum f l) (real_list_sum g l).
Proof.
  intros f g l Hfg.
  induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (real_le_plus_compat (f w) (g w) (real_list_sum f rest) (real_list_sum g rest)).
    + exact (Hfg w).
    + exact IH.
Qed.

(* ============ 8. real_list_sum_nonneg: pointwise [0 <= f w] implies [0 <= sum f] ============ *)
Lemma real_list_sum_nonneg : forall (f : X -> Real) (l : list X),
  (forall w : X, real_le real_zero (f w)) -> real_le real_zero (real_list_sum f l).
Proof.
  intros f l Hnonneg.
  induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)
                                   (real_plus (f w) (real_list_sum f rest))).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (real_le_plus_compat real_zero (f w) real_zero (real_list_sum f rest)).
      * exact (Hnonneg w).
      * exact IH.
Qed.
(* ============ 8b. real_list_sum_pos: pointwise [0 < f w] and [l] nonempty imply [0 < sum f] ============
   (Strict version.  The genuine positivity theorem for finite list
   sums in the Real layer: once Section Alignment is instantiated with
   a concrete finite state list ([list X] + [real_list_sum]), the
   Real-layer corroboration of [sum_over_S_pos] / [Z_align_pos] takes
   exactly this form.) *)
Lemma real_list_sum_pos : forall (f : X -> Real) (l : list X),
  (forall w : X, real_lt real_zero (f w)) ->
  l <> nil ->
  real_lt real_zero (real_list_sum f l).
Proof.
  intros f l Hf Hnn.
  induction l as [| w rest IH].
  - (* nil: the sum is [real_zero]; this contradicts the nonemptiness
       premise [l <> nil] via [eq_refl]. *)
    simpl. exfalso. exact (Hnn eq_refl).
  - (* w :: rest: case on whether [rest] is empty. *)
    destruct rest as [| w' rest'].
    + (* Single element: the sum is f w + real_zero == f w
         ([real_lt_id_r] + [real_plus_zero]). *)
      simpl.
      apply (RealSetoid.real_lt_id_r real_zero (f w) (real_plus (f w) real_zero)).
      * apply (real_eq_sym (real_plus (f w) real_zero) (f w)).
        apply (real_plus_zero (f w)).
      * exact (Hf w).
    + (* Multiple elements: f w and the tail sum are both positive
         ([real_lt_id_l]: 0 == 0+0, plus [real_lt_plus_compat]). *)
      simpl.
      apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
                                    (real_plus (f w) (real_list_sum f (w' :: rest')))).
      * apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
        apply (real_plus_zero real_zero).
      * apply (real_lt_plus_compat real_zero (f w) real_zero
                                  (real_list_sum f (w' :: rest'))).
        -- exact (Hf w).
        -- apply IH. discriminate.
Qed.

(* ============ 9. real_kl_term: p * (-log(q/p)) (definitionally the RHS of real_gibbs_core_eps) ============ *)
Definition real_kl_term (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q) : Real :=
  real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                  (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))).

(* ============ 10. real_gibbs_inequality_eps: 0 <= sum_s p s * (-log(q s / p s)) + eps
   (KL >= 0 in the Real layer, per-eps, over a concrete list state space).
   Pointwise core ([real_gibbs_core_eps]) + order preservation of sums
   ([real_list_sum_le]) + normalization (sum p == 1, sum q == 1 imply
   sum (p - q) == 0) + error accumulation (sum (p * eps) == eps). *)
Lemma real_gibbs_inequality_eps :
  forall (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum p l) real_one)
    (Hnormq : real_eq (real_list_sum q l) real_one)
    (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero
          (real_plus (real_list_sum (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l) eps).
Proof.
  intros l p q Hp Hq Hnormp Hnormq eps Hepspos.
  set (KLsum := real_list_sum (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
  set (SumPE := real_list_sum (fun s => real_mult (p s) eps) l).
  (* 1. Sum pointwise: sum (p - q) <= sum (KL) + sum (p * eps)
     ([real_list_sum_le] + [real_gibbs_core_eps]). *)
  assert (Hsum : real_le (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                         (real_list_sum (fun s => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                                           (real_mult (p s) eps)) l)).
  { apply real_list_sum_le.
    intro s.
    exact (real_gibbs_core_eps (p s) (q s) (Hp s) (Hq s) eps Hepspos). }
  (* 2. sum (p - q) == 0: [real_list_sum_add], [real_list_sum_opp],
     normalization, [real_plus_opp]. *)
  assert (Hzero : real_eq (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l) real_zero).
  { apply (real_eq_trans _ (real_plus (real_list_sum p l) (real_list_sum (fun s => real_opp (q s)) l)) _).
    - apply (real_list_sum_add p (fun s => real_opp (q s)) l).
    - apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum p l)
                                              (real_list_sum (fun s => real_opp (q s)) l)
                                              real_one (real_opp real_one)).
        * exact Hnormp.
        * apply (real_eq_trans _ (real_opp (real_list_sum q l)) _).
          -- apply (real_list_sum_opp q l).
          -- apply (RealSetoid.real_eq_opp_compat (real_list_sum q l) real_one).
             exact Hnormq.
      + apply (real_plus_opp real_one).
  }
  (* 3. sum (p * eps) == eps: [real_list_sum_linear_r], normalization, [real_mult_one]. *)
  assert (Heps : real_eq (real_list_sum (fun s => real_mult (p s) eps) l) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum p l)) _).
    - apply (real_list_sum_linear_r eps p l).
    - apply (real_eq_trans _ (real_mult eps real_one) _).
      + apply (RealSetoid.real_eq_mult_compat eps (real_list_sum p l) eps real_one).
        * apply real_eq_refl.
        * exact Hnormp.
      + apply (real_mult_one eps).
  }
  (* 4a. sum (KL + per) == KLsum + SumPE ([real_list_sum_add]). *)
  assert (Hadd : real_eq (real_list_sum (fun s => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                                           (real_mult (p s) eps)) l)
                         (real_plus KLsum SumPE)).
  { unfold KLsum, SumPE.
    apply (real_list_sum_add (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                             (fun s => real_mult (p s) eps) l). }
  (* 4b. sum (p - q) <= KLsum + SumPE ([real_le_id_r] replaces the RHS of [Hsum]). *)
  assert (Hsum2 : real_le (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                          (real_plus KLsum SumPE)).
  { apply (RealSetoid.real_le_id_r (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                                   (real_list_sum (fun s => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                                                     (real_mult (p s) eps)) l)
                                   (real_plus KLsum SumPE) Hadd Hsum). }
  (* 4c. KLsum + SumPE == KLsum + eps (by [Heps]). *)
  assert (Hplus : real_eq (real_plus KLsum SumPE) (real_plus KLsum eps)).
  { apply (RealSetoid.real_eq_plus_compat KLsum SumPE KLsum eps).
    - apply real_eq_refl.
    - unfold SumPE. exact Heps. }
  (* 4d. sum (p - q) <= KLsum + eps. *)
  assert (Hsum' : real_le (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                          (real_plus KLsum eps)).
  { apply (RealSetoid.real_le_id_r (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                                   (real_plus KLsum SumPE) (real_plus KLsum eps) Hplus Hsum2). }
  (* 5. 0 <= sum (p - q) <= KLsum + eps ([real_le_trans] + [real_eq_le]). *)
  apply (real_le_trans real_zero
                       (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                       (real_plus KLsum eps)).
  - apply (RealSetoid.real_eq_le real_zero
                                 (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)).
    exact (real_eq_sym (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l) real_zero Hzero).
  - exact Hsum'.
Qed.

End RealListSumMain.

Section DpoSigmoidMain.

(* ============ 1. Denominator positivity: 0 < 1 + e^{-x} ============ *)
Lemma real_sigmoid_denom_pos : forall x : Real,
  real_lt real_zero (real_plus real_one (real_exp_neg x)).
Proof.
  intro x.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
                                (real_plus real_one (real_exp_neg x))).
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_lt_plus_compat real_zero real_one real_zero (real_exp_neg x)).
    + apply real_lt_zero_one.
    + apply (real_exp_neg_pos x).
Qed.

(* ============ 2. real_sigmoid: sigma(x) = 1/(1+e^{-x}) ============ *)
Definition real_sigmoid (x : Real) : Real :=
  real_inv_pos (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x).

(* ============ 3. 0 < 1+1 (denominator of sigma(0)) ============ *)
Lemma real_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
                                (real_plus real_one real_one)).
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_lt_plus_compat real_zero real_one real_zero real_one).
    + apply real_lt_zero_one.
    + apply real_lt_zero_one.
Qed.

(* ============ 4. Sigmoid positivity: 0 < sigma(x) ============ *)
Lemma real_sigmoid_pos : forall x : Real,
  real_lt real_zero (real_sigmoid x).
Proof.
  intro x. unfold real_sigmoid. apply real_inv_pos_pos.
Qed.

(* ============ 5. Sigmoid strictly increasing: x < y implies sigma x < sigma y ============ *)
Lemma real_sigmoid_strict_inc : forall x y : Real,
  real_lt x y -> real_lt (real_sigmoid x) (real_sigmoid y).
Proof.
  intros x y Hxy.
  unfold real_sigmoid.
  (* exp_neg_decr: x < y implies e^{-y} < e^{-x}. *)
  assert (Hexp : real_lt (real_exp_neg y) (real_exp_neg x))
    by exact (real_exp_neg_decr x y Hxy).
  (* Denominator: 1 + e^{-y} < 1 + e^{-x} ([real_le_refl] on the constant
     ones combined with [Hexp] by mixed order preservation). *)
  assert (Hden : real_lt (real_plus real_one (real_exp_neg y))
                         (real_plus real_one (real_exp_neg x)))
    by exact (real_lt_plus_compat_le_lt real_one real_one
                                        (real_exp_neg y) (real_exp_neg x)
                                        (real_le_refl real_one) Hexp).
  exact (real_inv_pos_lt_contra (real_plus real_one (real_exp_neg y))
                                (real_plus real_one (real_exp_neg x))
                                (real_sigmoid_denom_pos y)
                                (real_sigmoid_denom_pos x) Hden).
Qed.

(* ============ 6. sigma(0) = 1/(1+1) (folding by [real_inv_pos_ext]) ============ *)
Lemma real_sigmoid_zero_half :
  real_eq (real_sigmoid real_zero)
          (real_inv_pos (real_plus real_one real_one) real_two_pos).
Proof.
  unfold real_sigmoid.
  assert (He : real_eq (real_exp_neg real_zero) real_one) by exact (real_exp_neg_zero).
  assert (Hp : real_eq (real_plus real_one (real_exp_neg real_zero))
                       (real_plus real_one real_one)).
  { apply (RealSetoid.real_eq_plus_compat real_one (real_exp_neg real_zero)
                                          real_one real_one).
    - apply real_eq_refl.
    - exact He. }
  exact (real_inv_pos_ext (real_plus real_one (real_exp_neg real_zero))
                          (real_plus real_one real_one)
                          (real_sigmoid_denom_pos real_zero)
                          real_two_pos Hp).
Qed.

End DpoSigmoidMain.

Section DpoBoundMain.

(* ============ 1. real_eq_plus_cancel_l: a+b == a+c implies b == c (abstract chain) ============ *)
Lemma real_eq_plus_cancel_l : forall (a b c : Real),
  real_eq (real_plus a b) (real_plus a c) -> real_eq b c.
Proof.
  intros a b c Habc.
  (* b == (a+b)+(-a) == (a+c)+(-a) == c. *)
  apply (real_eq_trans _ (real_plus (real_plus a b) (real_opp a)) _).
  - (* b == (a+b)+(-a). *)
    apply (real_eq_sym (real_plus (real_plus a b) (real_opp a)) b).
    apply (real_eq_trans _ (real_plus a (real_plus b (real_opp a))) _).
    + apply (real_eq_sym (real_plus a (real_plus b (real_opp a)))
                         (real_plus (real_plus a b) (real_opp a))).
      apply (real_plus_assoc a b (real_opp a)).
    + apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) b)) _).
      * apply (RealSetoid.real_eq_plus_compat a (real_plus b (real_opp a))
                                              a (real_plus (real_opp a) b)).
        -- apply real_eq_refl.
        -- apply (real_plus_comm b (real_opp a)).
      * apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) b) _).
        -- apply (real_plus_assoc a (real_opp a) b).
        -- apply (real_eq_trans _ (real_plus real_zero b) _).
           ++ apply (RealSetoid.real_eq_plus_compat (real_plus a (real_opp a)) b real_zero b).
              ** apply (real_plus_opp a).
              ** apply real_eq_refl.
           ++ (* zero+b == b. *)
              apply (real_eq_sym b (real_plus real_zero b)).
              apply (real_eq_trans _ (real_plus b real_zero) _).
              ** apply (real_eq_sym (real_plus b real_zero) b).
                 apply (real_plus_zero b).
              ** apply (real_plus_comm b real_zero).
  - (* (a+b)+(-a) == (a+c)+(-a) == c. *)
    apply (real_eq_trans _ (real_plus (real_plus a c) (real_opp a)) _).
    + apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                                            (real_plus a c) (real_opp a)).
      * exact Habc.
      * apply real_eq_refl.
    + (* (a+c)+(-a) == c, the symmetric chain. *)
      apply (real_eq_sym c (real_plus (real_plus a c) (real_opp a))).
      apply (real_eq_trans _ (real_plus a (real_plus c (real_opp a))) _).
      * (* c == a+(c+(-a)): c == zero+c == (a+(-a))+c == a+((-a)+c) == a+(c+(-a)). *)
        apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) c)) _).
        -- (* c == a+((-a)+c). *)
           apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) c) _).
           ++ (* c == (a+(-a))+c. *)
              apply (real_eq_trans _ (real_plus real_zero c) _).
              ** (* c == zero+c. *)
                  apply (real_eq_sym (real_plus real_zero c) c).
                  apply (real_eq_trans _ (real_plus c real_zero) _).
                  --- apply (real_eq_sym (real_plus c real_zero) (real_plus real_zero c)).
                      apply (real_plus_comm c real_zero).
                  --- apply (real_plus_zero c).
              ** (* zero+c == (a+(-a))+c. *)
                 apply (RealSetoid.real_eq_plus_compat real_zero c (real_plus a (real_opp a)) c).
                 --- apply (real_eq_sym (real_plus a (real_opp a)) real_zero).
                     apply (real_plus_opp a).
                 --- apply real_eq_refl.
           ++ (* (a+(-a))+c == a+((-a)+c). *)
               apply (real_eq_sym (real_plus a (real_plus (real_opp a) c)) (real_plus (real_plus a (real_opp a)) c)).
               apply (real_plus_assoc a (real_opp a) c).
         -- (* a+((-a)+c) == a+(c+(-a)). *)
           apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp a) c)
                                                 a (real_plus c (real_opp a))).
           ++ apply real_eq_refl.
           ++ apply (real_plus_comm (real_opp a) c).
      * (* a+(c+(-a)) == (a+c)+(-a): associativity, forward. *)
        apply (real_plus_assoc a c (real_opp a)).
Qed.

(* ============ 2. real_eq_mult_cancel_r: a*c == b*c with c>0 implies a == b (abstract chain) ============ *)
Lemma real_eq_mult_cancel_r : forall (a b c : Real) (Hc : real_lt real_zero c),
  real_eq (real_mult a c) (real_mult b c) -> real_eq a b.
Proof.
  intros a b c Hc Habc.
  (* a == (a*c)·(inv c) == (b*c)·(inv c) == b. *)
  apply (real_eq_trans _ (real_mult (real_mult a c) (real_inv_pos c Hc)) _).
  - (* a == (a*c)·(inv c). *)
    apply (real_eq_sym (real_mult (real_mult a c) (real_inv_pos c Hc)) a).
    apply (real_eq_trans _ (real_mult a (real_mult c (real_inv_pos c Hc))) _).
    + apply (real_eq_sym (real_mult a (real_mult c (real_inv_pos c Hc)))
                         (real_mult (real_mult a c) (real_inv_pos c Hc))).
      apply (real_mult_assoc a c (real_inv_pos c Hc)).
    + apply (real_eq_trans _ (real_mult a real_one) _).
      * apply (RealSetoid.real_eq_mult_compat a (real_mult c (real_inv_pos c Hc)) a real_one).
        -- apply real_eq_refl.
        -- apply (real_inv_pos_correct c Hc).
      * apply (real_mult_one a).
  - (* (a*c)·(inv c) == (b*c)·(inv c) == b. *)
    apply (real_eq_trans _ (real_mult (real_mult b c) (real_inv_pos c Hc)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult a c) (real_inv_pos c Hc)
                                            (real_mult b c) (real_inv_pos c Hc)).
      * exact Habc.
      * apply real_eq_refl.
    + (* (b*c)·(inv c) == b, by symmetry. *)
      apply (real_eq_sym b (real_mult (real_mult b c) (real_inv_pos c Hc))).
      apply (real_eq_trans _ (real_mult b (real_mult c (real_inv_pos c Hc))) _).
      * (* b == b*(c*(inv c)): b == b*1 == b*(c*(inv c)). *)
        apply (real_eq_trans _ (real_mult b real_one) _).
        -- apply (real_eq_sym (real_mult b real_one) b).
           apply (real_mult_one b).
        -- apply (RealSetoid.real_eq_mult_compat b real_one b (real_mult c (real_inv_pos c Hc))).
           ++ apply real_eq_refl.
           ++ apply (real_eq_sym (real_mult c (real_inv_pos c Hc)) real_one).
              apply (real_inv_pos_correct c Hc).
      * (* b·(c·(inv c)) == (b·c)·(inv c): associativity, forward. *)
        apply (real_mult_assoc b c (real_inv_pos c Hc)).
Qed.

(* ============ 3. real_inv_inv: inv (inv x) == x (via [real_eq_mult_cancel_r]) ============ *)
Lemma real_inv_inv : forall (x : Real) (Hx : real_lt real_zero x)
  (Hx' : real_lt real_zero (real_inv_pos x Hx)),
  real_eq (real_inv_pos (real_inv_pos x Hx) Hx') x.
Proof.
  intros x Hx Hx'.
  apply (real_eq_mult_cancel_r (real_inv_pos (real_inv_pos x Hx) Hx') x
                               (real_inv_pos x Hx) Hx').
  apply (real_eq_trans _ real_one _).
  - (* inv(inv x) * inv x == 1. *)
    apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) (real_inv_pos (real_inv_pos x Hx) Hx')) _).
    + apply (real_mult_comm (real_inv_pos (real_inv_pos x Hx) Hx') (real_inv_pos x Hx)).
    + apply (real_inv_pos_correct (real_inv_pos x Hx) Hx').
  - (* x * inv x == 1, backwards. *)
    apply (real_eq_sym (real_mult x (real_inv_pos x Hx)) real_one).
    apply (real_inv_pos_correct x Hx).
Qed.

(* ============ 4. real_exp_neg_opp_log: e^{-log x} == inv x (x > 0)
   Anchor equation: e^{-log x}*x == e^{-log x}*e^{log x} == e^{-log x + log x}
   == e^0 == 1 == inv x * x; [real_eq_mult_cancel_r] then yields
   e^{-log x} == inv x. *)
Lemma real_exp_neg_opp_log : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (cauchy_real_exp (real_opp (real_log x Hx))) (real_inv_pos x Hx).
Proof.
  intros x Hx.
  apply (real_eq_mult_cancel_r (cauchy_real_exp (real_opp (real_log x Hx)))
                               (real_inv_pos x Hx) x Hx).
  apply (real_eq_trans _ real_one _).
  - (* e^{-log x} * x == 1. *)
    apply (real_eq_trans _ (real_mult (cauchy_real_exp (real_opp (real_log x Hx)))
                                      (cauchy_real_exp (real_log x Hx))) _).
    + (* x == e^{log x} is substituted on the right factor. *)
      apply (RealSetoid.real_eq_mult_compat (cauchy_real_exp (real_opp (real_log x Hx))) x
                                            (cauchy_real_exp (real_opp (real_log x Hx)))
                                            (cauchy_real_exp (real_log x Hx))).
      * apply real_eq_refl.
      * apply (real_eq_sym (cauchy_real_exp (real_log x Hx)) x).
        apply (cw_log_exp_right x Hx).
    + (* e^{-log x} * e^{log x} == e^{-log x + log x} == e^0 == 1. *)
      apply (real_eq_trans _ (cauchy_real_exp (real_plus (real_opp (real_log x Hx)) (real_log x Hx))) _).
      * apply (real_eq_sym (cauchy_real_exp (real_plus (real_opp (real_log x Hx)) (real_log x Hx)))
                           (real_mult (cauchy_real_exp (real_opp (real_log x Hx)))
                                      (cauchy_real_exp (real_log x Hx)))).
        apply (cauchy_real_exp_plus (real_opp (real_log x Hx)) (real_log x Hx)).
      * apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
        -- apply cauchy_real_exp_wd.
           apply (real_eq_trans _ (real_plus (real_log x Hx) (real_opp (real_log x Hx))) _).
           ++ apply (real_plus_comm (real_opp (real_log x Hx)) (real_log x Hx)).
           ++ apply (real_plus_opp (real_log x Hx)).
        -- apply cauchy_real_exp_zero.
  - (* inv x * x == 1. *)
    apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx)) _).
    + (* 1 == x * inv x. *)
      apply (real_eq_sym (real_mult x (real_inv_pos x Hx)) real_one).
      apply (real_inv_pos_correct x Hx).
    + (* x * inv x == inv x * x. *)
      apply (real_mult_comm x (real_inv_pos x Hx)).
Qed.

(* ============ 5. real_log_sigmoid_zero_neg: -log sigma(0) == log 2 (anchor method)
   e^{-log sigma0} == inv sigma0 == inv(inv 2) == 2 == e^{log 2}; weak
   trichotomy then gives equality. *)
Lemma real_log_sigmoid_zero_neg :
  real_eq (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
          (real_log (real_plus real_one real_one) real_two_pos).
Proof.
  apply (real_weak_trich (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
                         (real_log (real_plus real_one real_one) real_two_pos)).
  - (* ¬ (L < R) *)
    intro HLlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_opp (real_log (real_sigmoid real_zero)
                                                               (real_sigmoid_pos real_zero))))
                          (cauchy_real_exp (real_log (real_plus real_one real_one) real_two_pos))).
    + apply (cauchy_real_exp_mono (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
                                  (real_log (real_plus real_one real_one) real_two_pos)).
      exact HLlt.
    + (* e^L == inv sigma0 == inv(inv 2) == 2 == e^R. *)
      apply (real_eq_trans _ (real_inv_pos (real_sigmoid real_zero) (real_sigmoid_pos real_zero)) _).
      * apply (real_exp_neg_opp_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)).
      * apply (real_eq_trans _ (real_inv_pos (real_inv_pos (real_plus real_one real_one) real_two_pos)
                                             (real_inv_pos_pos (real_plus real_one real_one) real_two_pos)) _).
        -- apply (real_inv_pos_ext (real_sigmoid real_zero)
                                   (real_inv_pos (real_plus real_one real_one) real_two_pos)
                                   (real_sigmoid_pos real_zero)
                                   (real_inv_pos_pos (real_plus real_one real_one) real_two_pos)).
           apply (real_sigmoid_zero_half).
        -- apply (real_eq_trans _ (real_plus real_one real_one) _).
           ++ apply (real_inv_inv (real_plus real_one real_one) real_two_pos
                                  (real_inv_pos_pos (real_plus real_one real_one) real_two_pos)).
           ++ apply (real_eq_sym (cauchy_real_exp (real_log (real_plus real_one real_one) real_two_pos))
                                 (real_plus real_one real_one)).
              apply (cw_log_exp_right (real_plus real_one real_one) real_two_pos).
  - (* ¬ (R < L) *)
    intro HRlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log (real_plus real_one real_one) real_two_pos))
                          (cauchy_real_exp (real_opp (real_log (real_sigmoid real_zero)
                                                               (real_sigmoid_pos real_zero))))).
    + apply (cauchy_real_exp_mono (real_log (real_plus real_one real_one) real_two_pos)
                                  (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))).
      exact HRlt.
    + (* e^R == 2 == inv(inv 2) == inv sigma0 == e^L. *)
      apply (real_eq_trans _ (real_plus real_one real_one) _).
      * apply (cw_log_exp_right (real_plus real_one real_one) real_two_pos).
      * apply (real_eq_trans _ (real_inv_pos (real_inv_pos (real_plus real_one real_one) real_two_pos)
                                             (real_inv_pos_pos (real_plus real_one real_one) real_two_pos)) _).
        -- apply (real_eq_sym (real_inv_pos (real_inv_pos (real_plus real_one real_one) real_two_pos)
                                            (real_inv_pos_pos (real_plus real_one real_one) real_two_pos))
                              (real_plus real_one real_one)).
           apply (real_inv_inv (real_plus real_one real_one) real_two_pos
                               (real_inv_pos_pos (real_plus real_one real_one) real_two_pos)).
        -- apply (real_eq_trans _ (real_inv_pos (real_sigmoid real_zero) (real_sigmoid_pos real_zero)) _).
           ++ apply (real_eq_sym (real_inv_pos (real_sigmoid real_zero) (real_sigmoid_pos real_zero))
                                 (real_inv_pos (real_inv_pos (real_plus real_one real_one) real_two_pos)
                                               (real_inv_pos_pos (real_plus real_one real_one) real_two_pos))).
              apply (real_inv_pos_ext (real_sigmoid real_zero)
                                      (real_inv_pos (real_plus real_one real_one) real_two_pos)
                                      (real_sigmoid_pos real_zero)
                                      (real_inv_pos_pos (real_plus real_one real_one) real_two_pos)).
              apply (real_sigmoid_zero_half).
           ++ apply (real_eq_sym (cauchy_real_exp (real_opp (real_log (real_sigmoid real_zero)
                                                                      (real_sigmoid_pos real_zero))))
                                 (real_inv_pos (real_sigmoid real_zero) (real_sigmoid_pos real_zero))).
              apply (real_exp_neg_opp_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)).
Qed.

(* ============ 6. real_dpo_sigmoid_loss_bounded: r_l < r_w implies
   -log sigma(r_w - r_l) < log 2 — the mathematical core of DPO
   boundedness after [real_dpo_loss_at_pi_star] simplification. *)
Lemma real_dpo_sigmoid_loss_bounded :
  forall (r_w r_l : Real),
    real_lt r_l r_w ->
    real_lt (real_opp (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                (real_sigmoid_pos (real_plus r_w (real_opp r_l)))))
            (real_log (real_plus real_one real_one) real_two_pos).
Proof.
  intros r_w r_l Hrw.
  (* 1. 0 < r_w - r_l (r_l < r_w gives r_l+(-r_l) < r_w+(-r_l), with 0 == r_l+(-r_l)). *)
  assert (Hpos : real_lt real_zero (real_plus r_w (real_opp r_l))).
  { apply (RealSetoid.real_lt_id_l real_zero (real_plus r_l (real_opp r_l))
                                  (real_plus r_w (real_opp r_l))).
    - apply (real_eq_sym (real_plus r_l (real_opp r_l)) real_zero).
      apply (real_plus_opp r_l).
    - apply (real_lt_plus_compat_lt_le r_l r_w (real_opp r_l) (real_opp r_l)).
      + exact Hrw.
      + apply real_le_refl.
  }
  (* 2. sigma 0 < sigma(r_w - r_l) ([real_sigmoid_strict_inc]). *)
  assert (Hsig : real_lt (real_sigmoid real_zero)
                         (real_sigmoid (real_plus r_w (real_opp r_l))))
    by exact (real_sigmoid_strict_inc real_zero (real_plus r_w (real_opp r_l)) Hpos).
  (* 3. log sigma0 < log sigma(r_w - r_l) ([real_log_lt_mono]). *)
  assert (Hlog : real_lt (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero))
                         (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                   (real_sigmoid_pos (real_plus r_w (real_opp r_l))))).
  { apply (real_log_lt_mono (real_sigmoid real_zero)
                            (real_sigmoid (real_plus r_w (real_opp r_l)))
                            (real_sigmoid_pos real_zero)
                            (real_sigmoid_pos (real_plus r_w (real_opp r_l)))
                            Hsig). }
  (* 4. -log sigma(r_w - r_l) < -log sigma0 ([real_opp_lt_compat]). *)
  assert (Hopp : real_lt (real_opp (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                              (real_sigmoid_pos (real_plus r_w (real_opp r_l)))))
                         (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))).
  { apply (real_opp_lt_compat (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero))
                              (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                        (real_sigmoid_pos (real_plus r_w (real_opp r_l))))
                              Hlog). }
  (* 5. -log sigma0 == log 2. *)
  assert (Hval : real_eq (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
                         (real_log (real_plus real_one real_one) real_two_pos))
    by exact (real_log_sigmoid_zero_neg).
  (* 6. Assembly: -log sigma(r_w - r_l) < log 2 (replacement via [real_lt_id_r]). *)
  apply (RealSetoid.real_lt_id_r (real_opp (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                                      (real_sigmoid_pos (real_plus r_w (real_opp r_l)))))
                                 (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
                                 (real_log (real_plus real_one real_one) real_two_pos) Hval Hopp).
Qed.

End DpoBoundMain.

Section DpoPairMain.

(* ============ Part 0a. real_eq_plus_opp_swap: (a+x)+(-a) == x ============ *)
Lemma real_eq_plus_opp_swap : forall (a x : Real),
  real_eq (real_plus (real_plus a x) (real_opp a)) x.
Proof.
  intros a x.
  apply (real_eq_trans _ (real_plus a (real_plus x (real_opp a))) _).
  - apply (real_eq_sym (real_plus a (real_plus x (real_opp a)))
                       (real_plus (real_plus a x) (real_opp a))).
    apply (real_plus_assoc a x (real_opp a)).
  - apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) x)) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus x (real_opp a))
                                            a (real_plus (real_opp a) x)).
      * apply real_eq_refl.
      * apply (real_plus_comm x (real_opp a)).
    + apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) x) _).
      * apply (real_plus_assoc a (real_opp a) x).
      * apply (real_eq_trans _ (real_plus real_zero x) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus a (real_opp a)) x real_zero x).
           ++ apply (real_plus_opp a).
           ++ apply real_eq_refl.
        -- apply (real_eq_sym x (real_plus real_zero x)).
           apply (real_eq_trans _ (real_plus x real_zero) _).
           ++ apply (real_eq_sym (real_plus x real_zero) x).
              apply (real_plus_zero x).
           ++ apply (real_plus_comm x real_zero).
Qed.

(* ============ Part 0b. real_eq_plus_opp_common: (A+X)+(-(A+Y)) == X+(-Y) ============ *)
Lemma real_eq_plus_opp_common : forall (A X Y : Real),
  real_eq (real_plus (real_plus A X) (real_opp (real_plus A Y)))
          (real_plus X (real_opp Y)).
Proof.
  intros A X Y.
  apply (real_eq_trans _ (real_plus (real_plus A X) (real_plus (real_opp A) (real_opp Y))) _).
  - apply (RealSetoid.real_eq_plus_compat (real_plus A X) (real_opp (real_plus A Y))
                                          (real_plus A X) (real_plus (real_opp A) (real_opp Y))).
    + apply real_eq_refl.
    + apply (real_opp_plus A Y).
  - apply (real_eq_trans _ (real_plus (real_plus (real_plus A X) (real_opp A)) (real_opp Y)) _).
    + apply (real_plus_assoc (real_plus A X) (real_opp A) (real_opp Y)).
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_plus A X) (real_opp A)) (real_opp Y)
                                            X (real_opp Y)).
      * apply (real_eq_plus_opp_swap A X).
      * apply real_eq_refl.
Qed.

(* ============ Part 0c. real_log_inv_one_inv: log(inv x) == -log x (anchor method) ============ *)
Lemma real_log_inv_one_inv : forall (x : Real) (Hx : real_lt real_zero x)
  (Hinv : real_lt real_zero (real_inv_pos x Hx)),
  real_eq (real_log (real_inv_pos x Hx) Hinv)
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx Hinv.
  apply (real_weak_trich (real_log (real_inv_pos x Hx) Hinv) (real_opp (real_log x Hx))).
  - intro HLlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log (real_inv_pos x Hx) Hinv))
                          (cauchy_real_exp (real_opp (real_log x Hx)))).
    + apply (cauchy_real_exp_mono (real_log (real_inv_pos x Hx) Hinv)
                                  (real_opp (real_log x Hx))). exact HLlt.
    + apply (real_eq_trans _ (real_inv_pos x Hx) _).
      * apply (cw_log_exp_right (real_inv_pos x Hx) Hinv).
      * apply (real_eq_sym (cauchy_real_exp (real_opp (real_log x Hx))) (real_inv_pos x Hx)).
        apply (real_exp_neg_opp_log x Hx).
  - intro HRlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_opp (real_log x Hx)))
                          (cauchy_real_exp (real_log (real_inv_pos x Hx) Hinv))).
    + apply (cauchy_real_exp_mono (real_opp (real_log x Hx))
                                  (real_log (real_inv_pos x Hx) Hinv)). exact HRlt.
    + apply (real_eq_trans _ (real_inv_pos x Hx) _).
      * apply (real_exp_neg_opp_log x Hx).
      * apply (real_eq_sym (cauchy_real_exp (real_log (real_inv_pos x Hx) Hinv)) (real_inv_pos x Hx)).
        apply (cw_log_exp_right (real_inv_pos x Hx) Hinv).
Qed.

(* ============ Part 0d. real_log_exp_neg: log(e^{-x}) == -x (anchor method) ============ *)
Lemma real_log_exp_neg : forall (x : Real),
  real_eq (real_log (real_exp_neg x) (real_exp_neg_pos x))
          (real_opp x).
Proof.
  intro x.
  apply (real_weak_trich (real_log (real_exp_neg x) (real_exp_neg_pos x)) (real_opp x)).
  - intro HLlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log (real_exp_neg x) (real_exp_neg_pos x)))
                          (cauchy_real_exp (real_opp x))).
    + apply (cauchy_real_exp_mono (real_log (real_exp_neg x) (real_exp_neg_pos x)) (real_opp x)).
      exact HLlt.
    + apply (real_eq_trans _ (real_exp_neg x) _).
      * apply (cw_log_exp_right (real_exp_neg x) (real_exp_neg_pos x)).
      * apply real_eq_refl.
  - intro HRlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_opp x))
                          (cauchy_real_exp (real_log (real_exp_neg x) (real_exp_neg_pos x)))).
    + apply (cauchy_real_exp_mono (real_opp x) (real_log (real_exp_neg x) (real_exp_neg_pos x))).
      exact HRlt.
    + apply (real_eq_trans _ (real_exp_neg x) _).
      * apply real_eq_refl.
      * apply (real_eq_sym (cauchy_real_exp (real_log (real_exp_neg x) (real_exp_neg_pos x))) (real_exp_neg x)).
        apply (cw_log_exp_right (real_exp_neg x) (real_exp_neg_pos x)).
Qed.

(* ============ Part 0e. real_log_proof_irrel: log is independent of its positivity-proof argument (anchor method) ============ *)
Lemma real_log_proof_irrel : forall (x : Real) (Hx Hy : real_lt real_zero x),
  real_eq (real_log x Hx) (real_log x Hy).
Proof.
  intros x Hx Hy.
  apply (real_weak_trich (real_log x Hx) (real_log x Hy)).
  - intro HLlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log x Hx)) (cauchy_real_exp (real_log x Hy))).
    + apply (cauchy_real_exp_mono (real_log x Hx) (real_log x Hy)). exact HLlt.
    + apply (real_eq_trans _ x _).
      * apply (cw_log_exp_right x Hx).
      * apply real_eq_sym. apply (cw_log_exp_right x Hy).
  - intro HRlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log x Hy)) (cauchy_real_exp (real_log x Hx))).
    + apply (cauchy_real_exp_mono (real_log x Hy) (real_log x Hx)). exact HRlt.
    + apply (real_eq_trans _ x _).
      * apply (cw_log_exp_right x Hy).
      * apply real_eq_sym. apply (cw_log_exp_right x Hx).
Qed.

(* ============ Part 0f. real_log_wd: log respects [real_eq] in its argument (anchor method) ============ *)
Lemma real_log_wd : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq a b -> real_eq (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  apply (real_weak_trich (real_log a Ha) (real_log b Hb)).
  - intro HLlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log a Ha)) (cauchy_real_exp (real_log b Hb))).
    + apply (cauchy_real_exp_mono (real_log a Ha) (real_log b Hb)). exact HLlt.
    + apply (real_eq_trans _ a _).
      * apply (cw_log_exp_right a Ha).
      * apply (real_eq_trans _ b _).
        -- exact Hab.
        -- apply real_eq_sym. apply (cw_log_exp_right b Hb).
  - intro HRlt.
    apply (real_lt_not_eq (cauchy_real_exp (real_log b Hb)) (cauchy_real_exp (real_log a Ha))).
    + apply (cauchy_real_exp_mono (real_log b Hb) (real_log a Ha)). exact HRlt.
    + apply (real_eq_trans _ b _).
      * apply (cw_log_exp_right b Hb).
      * apply (real_eq_trans _ a _).
        -- apply real_eq_sym. exact Hab.
        -- apply real_eq_sym. apply (cw_log_exp_right a Ha).
Qed.

(* ============ Part 1a. Real-layer Alignment structure ([Z_align] as a Variable, abstract state space [S]) ============ *)
Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

Definition real_pi_star (s : S) : Real :=
  real_mult (real_inv_pos Z_align Z_align_pos)
            (real_mult (pi_ref s)
                       (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))).

Lemma real_pi_star_pos : forall s : S, real_lt real_zero (real_pi_star s).
Proof.
  intro s. unfold real_pi_star.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_mult_positive.
    + apply (pi_ref_pos s).
    + apply real_exp_neg_pos.
Qed.

(* Log-odds ratio: log_ratio(pi,s) := log(pi s) - log(pi_ref s). *)
Definition real_log_ratio (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s : S) : Real :=
  real_plus (real_log (pi s) (Hpi s)) (real_opp (real_log (pi_ref s) (pi_ref_pos s))).

(* Pairwise DPO loss: -log sigma( beta*log_ratio(pi,s_w) - beta*log_ratio(pi,s_l) ). *)
Definition real_dpo_loss_pair (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S) : Real :=
  real_opp (real_log (real_sigmoid (real_plus (real_mult beta (real_log_ratio pi Hpi s_w))
                                              (real_opp (real_mult beta (real_log_ratio pi Hpi s_l)))))
                     (real_sigmoid_pos (real_plus (real_mult beta (real_log_ratio pi Hpi s_w))
                                                  (real_opp (real_mult beta (real_log_ratio pi Hpi s_l)))))).

(* ============ Part 1b. real_log_pi_star: log pi*(s) == -log Z + log pi_ref(s) + r(s)/beta ============ *)
Lemma real_log_pi_star : forall (s : S),
  real_eq (real_log (real_pi_star s) (real_pi_star_pos s))
          (real_plus (real_opp (real_log Z_align Z_align_pos))
                     (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                (real_mult (real_inv_pos beta beta_pos) (reward s)))).
Proof.
  intro s.
  unfold real_pi_star.
  assert (Hpos1 : real_lt real_zero (real_inv_pos Z_align Z_align_pos))
    by exact (real_inv_pos_pos Z_align Z_align_pos).
  assert (Hpos3 : real_lt real_zero
        (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s)))))
    by exact (real_exp_neg_pos _).
  set (X := real_mult (pi_ref s)
                      (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))).
  assert (Hpos2 : real_lt real_zero X).
  { unfold X. apply real_mult_positive.
    - apply (pi_ref_pos s).
    - apply real_exp_neg_pos. }
  assert (Hlm : real_eq (real_log (real_mult (real_inv_pos Z_align Z_align_pos) X) (real_pi_star_pos s))
                        (real_plus (real_log (real_inv_pos Z_align Z_align_pos) Hpos1) (real_log X Hpos2))).
  { apply (real_eq_trans _ (real_log (real_mult (real_inv_pos Z_align Z_align_pos) X)
                                     (real_mult_positive (real_inv_pos Z_align Z_align_pos) X Hpos1 Hpos2)) _).
    - apply (real_log_proof_irrel (real_mult (real_inv_pos Z_align Z_align_pos) X)
                                  (real_pi_star_pos s)
                                  (real_mult_positive (real_inv_pos Z_align Z_align_pos) X Hpos1 Hpos2)).
    - exact (real_log_mult (real_inv_pos Z_align Z_align_pos) X Hpos1 Hpos2). }
  assert (Hli : real_eq (real_log (real_inv_pos Z_align Z_align_pos) Hpos1)
                        (real_opp (real_log Z_align Z_align_pos)))
    by exact (real_log_inv_one_inv Z_align Z_align_pos Hpos1).
  assert (Hle : real_eq
        (real_log (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s)))) Hpos3)
        (real_mult (real_inv_pos beta beta_pos) (reward s))).
  { apply (real_eq_trans _ (real_opp (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s)))) _).
    - (* log (exp_neg ...) Hpos3 == log (exp_neg ...) (exp_neg_pos ...) == opp(opp u) *)
      apply (real_eq_trans _ (real_log (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))
                                       (real_exp_neg_pos (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))) _).
      + apply (real_log_proof_irrel (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))
                                    Hpos3
                                    (real_exp_neg_pos (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))).
      + apply (real_log_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s)))).
    - apply (real_opp_opp (real_mult (real_inv_pos beta beta_pos) (reward s))).
  }
  assert (Hlm2 : real_eq (real_log X Hpos2)
                         (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                    (real_mult (real_inv_pos beta beta_pos) (reward s)))).
  { apply (real_eq_trans _ (real_log X (real_mult_positive (pi_ref s)
                                                           (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))
                                                           (pi_ref_pos s) Hpos3)) _).
    - apply (real_log_proof_irrel X Hpos2
                                  (real_mult_positive (pi_ref s)
                                                      (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))
                                                      (pi_ref_pos s) Hpos3)).
    - apply (real_eq_trans _ (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                        (real_log (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s)))) Hpos3)) _).
      + exact (real_log_mult (pi_ref s)
                             (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))
                             (pi_ref_pos s) Hpos3).
      + apply (RealSetoid.real_eq_plus_compat (real_log (pi_ref s) (pi_ref_pos s))
                                              (real_log (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s)))) Hpos3)
                                              (real_log (pi_ref s) (pi_ref_pos s))
                                              (real_mult (real_inv_pos beta beta_pos) (reward s))).
        * apply real_eq_refl.
        * exact Hle. }
  apply (real_eq_trans _ (real_plus (real_log (real_inv_pos Z_align Z_align_pos) Hpos1) (real_log X Hpos2)) _).
  - exact Hlm.
  - apply (real_eq_trans _ (real_plus (real_opp (real_log Z_align Z_align_pos)) (real_log X Hpos2)) _).
    + apply (RealSetoid.real_eq_plus_compat (real_log (real_inv_pos Z_align Z_align_pos) Hpos1)
                                            (real_log X Hpos2)
                                            (real_opp (real_log Z_align Z_align_pos))
                                            (real_log X Hpos2)).
      * exact Hli.
      * apply real_eq_refl.
    + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log Z_align Z_align_pos))
                                            (real_log X Hpos2)
                                            (real_opp (real_log Z_align Z_align_pos))
                                            (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                       (real_mult (real_inv_pos beta beta_pos) (reward s)))).
      * apply real_eq_refl.
      * exact Hlm2.
Qed.

(* ============ Part 2a. real_sigmoid_wd: sigmoid respects [real_eq] in its argument (chain) ============ *)
Lemma real_sigmoid_wd : forall (a b : Real),
  real_eq a b -> real_eq (real_sigmoid a) (real_sigmoid b).
Proof.
  intros a b Hab.
  unfold real_sigmoid.
  apply (real_inv_pos_ext (real_plus real_one (real_exp_neg a))
                          (real_plus real_one (real_exp_neg b))
                          (real_sigmoid_denom_pos a)
                          (real_sigmoid_denom_pos b)).
  apply (RealSetoid.real_eq_plus_compat real_one (real_exp_neg a)
                                        real_one (real_exp_neg b)).
  - apply real_eq_refl.
  - apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat a b). exact Hab.
Qed.

(* ============ Part 2b. real_dpo_loss_at_pi_star: L_DPO(pi*, s_w, s_l) == -log sigma(r_w - r_l) ============ *)
Lemma real_dpo_loss_at_pi_star : forall (s_w s_l : S),
  real_eq (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
          (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                              (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l)))))).
Proof.
  intros s_w s_l.
  unfold real_dpo_loss_pair, real_log_ratio.
  set (A := real_opp (real_log Z_align Z_align_pos)).
  (* Hdiff_w: log(pi_star s_w) - log(pi_ref s_w) == A + u_w. *)
  assert (Hdiff_w : real_eq
        (real_plus (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                   (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w))))
        (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_w)))).
  { apply (real_eq_trans _ (real_plus
        (real_plus A (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                                (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
        (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                                            (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))
                                            (real_plus A (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                                                                    (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                            (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))).
      * unfold A. exact (real_log_pi_star s_w).
      * apply real_eq_refl.
    - (* (A+(L+u))+(-L) == A+((L+u)+(-L)) == A+u. *)
      apply (real_eq_trans _ (real_plus A
        (real_plus (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                              (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                   (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w))))) _).
      + apply (real_eq_sym (real_plus A
        (real_plus (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                              (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                   (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))))
                           (real_plus (real_plus A (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                                                              (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                      (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w))))).
        apply (real_plus_assoc A (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                                            (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                               (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))).
      + apply (RealSetoid.real_eq_plus_compat A
        (real_plus (real_plus (real_log (pi_ref s_w) (pi_ref_pos s_w))
                              (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                   (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w))))
                                              A
        (real_mult (real_inv_pos beta beta_pos) (reward s_w))).
        * apply real_eq_refl.
        * apply (real_eq_plus_opp_swap (real_log (pi_ref s_w) (pi_ref_pos s_w))
                                       (real_mult (real_inv_pos beta beta_pos) (reward s_w))).
  }
  (* Hdiff_l, by symmetry. *)
  assert (Hdiff_l : real_eq
        (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                   (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))
        (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l)))).
  { apply (real_eq_trans _ (real_plus
        (real_plus A (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                                (real_mult (real_inv_pos beta beta_pos) (reward s_l))))
        (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                                            (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))
                                            (real_plus A (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                                                                    (real_mult (real_inv_pos beta beta_pos) (reward s_l))))
                                            (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))).
      * unfold A. exact (real_log_pi_star s_l).
      * apply real_eq_refl.
    - apply (real_eq_trans _ (real_plus A
        (real_plus (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                              (real_mult (real_inv_pos beta beta_pos) (reward s_l)))
                   (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))) _).
      + apply (real_eq_sym (real_plus A
        (real_plus (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                              (real_mult (real_inv_pos beta beta_pos) (reward s_l)))
                   (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))))
                           (real_plus (real_plus A (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                                                              (real_mult (real_inv_pos beta beta_pos) (reward s_l))))
                                      (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))).
        apply (real_plus_assoc A (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                                            (real_mult (real_inv_pos beta beta_pos) (reward s_l)))
                               (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))).
      + apply (RealSetoid.real_eq_plus_compat A
        (real_plus (real_plus (real_log (pi_ref s_l) (pi_ref_pos s_l))
                              (real_mult (real_inv_pos beta beta_pos) (reward s_l)))
                   (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))
                                              A
        (real_mult (real_inv_pos beta beta_pos) (reward s_l))).
        * apply real_eq_refl.
        * apply (real_eq_plus_opp_swap (real_log (pi_ref s_l) (pi_ref_pos s_l))
                                       (real_mult (real_inv_pos beta beta_pos) (reward s_l))).
  }
  (* Hmain: beta*(log_ratio_w) - beta*(log_ratio_l) == r_w - r_l. *)
  assert (Hmain : real_eq
        (real_plus (real_mult beta (real_plus (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                                              (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))))
                   (real_opp (real_mult beta (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                                                        (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))))))
        (real_plus (reward s_w) (real_opp (reward s_l)))).
  {
    (* 1. beta*LR_w == beta*(A+u_w) (by [Hdiff_w]), beta*LR_l == beta*(A+u_l) (by [Hdiff_l]). *)
    apply (real_eq_trans _ (real_plus (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                      (real_opp (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l)))))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_mult beta (real_plus (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                                                                        (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))))
                                            (real_opp (real_mult beta (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                                                                                  (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))))
                                            (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                            (real_opp (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l)))))).
      + apply (RealSetoid.real_eq_mult_compat beta
            (real_plus (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                       (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w))))
                                              beta
            (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_w)))).
        * apply real_eq_refl.
        * exact Hdiff_w.
      + apply (RealSetoid.real_eq_opp_compat
          (real_mult beta (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                                     (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))))
          (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l))))).
        apply (RealSetoid.real_eq_mult_compat beta
            (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                       (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))
            beta
            (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l)))).
        * apply real_eq_refl.
        * exact Hdiff_l.
    - (* 2-4. beta*(A+u_w) - beta*(A+u_l) == r_w - r_l. *)
      apply (real_eq_trans _ (real_plus (real_plus (real_mult beta A)
                                                   (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                        (real_opp (real_plus (real_mult beta A)
                                                             (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l)))))) _).
      + (* beta*(A+u_w) == beta*A + beta*u_w (distributivity, twice). *)
        apply (RealSetoid.real_eq_plus_compat (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                              (real_opp (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l)))))
                                              (real_plus (real_mult beta A)
                                                         (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                              (real_opp (real_plus (real_mult beta A)
                                                                   (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l)))))).
        * apply (real_distrib beta A (real_mult (real_inv_pos beta beta_pos) (reward s_w))).
        * apply (RealSetoid.real_eq_opp_compat
            (real_mult beta (real_plus A (real_mult (real_inv_pos beta beta_pos) (reward s_l))))
            (real_plus (real_mult beta A)
                       (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l))))).
          apply (real_distrib beta A (real_mult (real_inv_pos beta beta_pos) (reward s_l))).
      + (* 3. The common term A cancels: plus (plus BA X) (opp (plus BA Y)) == X+(-Y). *)
        apply (real_eq_trans _ (real_plus (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                                          (real_opp (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l))))) _).
        * apply (real_eq_plus_opp_common (real_mult beta A)
                                         (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                                         (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l)))).
        * (* 4. beta*(inv beta*r_w) == r_w and beta*(inv beta*r_l) == r_l. *)
          apply (RealSetoid.real_eq_plus_compat (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                                                (real_opp (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l))))
                                                (reward s_w)
                                                (real_opp (reward s_l))).
          -- (* beta*(inv beta*r_w) == r_w. *)
             apply (real_eq_trans _ (real_mult (real_mult beta (real_inv_pos beta beta_pos)) (reward s_w)) _).
             ++ apply (real_mult_assoc beta (real_inv_pos beta beta_pos) (reward s_w)).
             ++ apply (real_eq_trans _ (real_mult real_one (reward s_w)) _).
                ** apply (RealSetoid.real_eq_mult_compat (real_mult beta (real_inv_pos beta beta_pos)) (reward s_w)
                                                         real_one (reward s_w)).
                   --- apply (real_inv_pos_correct beta beta_pos).
                   --- apply real_eq_refl.
                ** apply (real_eq_trans _ (real_mult (reward s_w) real_one) _).
                   --- apply (real_mult_comm real_one (reward s_w)).
                   --- apply (real_mult_one (reward s_w)).
          -- apply (RealSetoid.real_eq_opp_compat (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l)))
                                                  (reward s_l)).
             apply (real_eq_trans _ (real_mult (real_mult beta (real_inv_pos beta beta_pos)) (reward s_l)) _).
             ++ apply (real_mult_assoc beta (real_inv_pos beta beta_pos) (reward s_l)).
             ++ apply (real_eq_trans _ (real_mult real_one (reward s_l)) _).
                ** apply (RealSetoid.real_eq_mult_compat (real_mult beta (real_inv_pos beta beta_pos)) (reward s_l)
                                                         real_one (reward s_l)).
                   --- apply (real_inv_pos_correct beta beta_pos).
                   --- apply real_eq_refl.
                ** apply (real_eq_trans _ (real_mult (reward s_l) real_one) _).
                   --- apply (real_mult_comm real_one (reward s_l)).
                   --- apply (real_mult_one (reward s_l)).
  }
  (* Assembly: opp (log (sigmoid P)) == opp (log (sigmoid Q)), with
     P := beta*LR_w - beta*LR_l and Q := r_w - r_l. *)
  set (P := real_plus (real_mult beta (real_plus (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                                                 (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))))
                      (real_opp (real_mult beta (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                                                           (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l))))))).
  set (Q := real_plus (reward s_w) (real_opp (reward s_l))).
  apply (RealSetoid.real_eq_opp_compat
          (real_log (real_sigmoid P) (real_sigmoid_pos P))
          (real_log (real_sigmoid Q) (real_sigmoid_pos Q))).
  apply (real_log_wd (real_sigmoid P) (real_sigmoid Q)
                     (real_sigmoid_pos P) (real_sigmoid_pos Q)).
  apply (real_sigmoid_wd P Q).
  exact Hmain.
Qed.

(* ============ Part 3. real_dpo_loss_pi_star_bounded_eps: r_l < r_w implies L_DPO(pi*,s_w,s_l) < log 2 ============ *)
Lemma real_dpo_loss_pi_star_bounded_eps :
  forall (s_w s_l : S),
    real_lt (reward s_l) (reward s_w) ->
    real_lt (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
            (real_log (real_plus real_one real_one) real_two_pos).
Proof.
  intros s_w s_l Hrw.
  (* Core: -log sigma(r_w - r_l) < log 2, by [real_dpo_sigmoid_loss_bounded]. *)
  assert (Hcore : real_lt
        (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                            (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
        (real_log (real_plus real_one real_one) real_two_pos))
    by exact (real_dpo_sigmoid_loss_bounded (reward s_w) (reward s_l) Hrw).
  (* at_pi_star: L_DPO(pi*,s_w,s_l) == -log sigma(r_w - r_l). *)
  apply (RealSetoid.real_lt_id_l (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
          (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                              (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
          (real_log (real_plus real_one real_one) real_two_pos)).
  - exact (real_dpo_loss_at_pi_star s_w s_l).
  - exact Hcore.
Qed.

(* ============================================================ *)
(* T1.4: two-sided quantitative bound on the DPO loss at pi*      *)
(*   (paper-1 P2 item 10).                                        *)
(*   r_l < r_w implies 0 < L_DPO(pi*,s_w,s_l) < log 2.            *)
(*   Chain 1 (lower bound): 1 < 1+e^{-x} (translation by e^{-x} > 0) *)
(*     gives sigma(x) < 1 (inv reverses order and inv 1 == 1),    *)
(*     hence log sigma < log 1 == 0, hence 0 < -log sigma         *)
(*     ([real_opp_lt_compat] + [real_opp_zero]); restate at pi*   *)
(*     via at_pi_star.  Chain 2 (upper bound): bounded_eps.       *)
(* ============================================================ *)

(* Auxiliary: 0 < x implies 1 < 1 + x (translation in the Real layer). *)
Lemma real_one_lt_succ_pos : forall (x : Real) (Hx : real_lt real_zero x),
  real_lt real_one (real_plus real_one x).
Proof.
  intros x Hx.
  apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one x)).
  - apply (real_eq_sym (real_plus real_one real_zero) real_one (real_plus_zero real_one)).
  - apply (real_lt_plus_compat_le_lt real_one real_one real_zero x).
    + apply real_le_refl.
    + exact Hx.
Qed.

(* Auxiliary: inv 1 == 1 ([real_inv_unique] applied to the correct and
   mult_one characterizations; the global [real_inv_one] is defined
   after this Section, so this local form avoids a forward reference). *)
Lemma real_inv_one_local : real_eq (real_inv_pos real_one real_lt_zero_one) real_one.
Proof.
  apply (real_inv_unique real_one (real_inv_pos real_one real_lt_zero_one) real_one).
  - apply (real_inv_pos_correct real_one real_lt_zero_one).
  - apply (real_mult_one real_one).
Qed.

(* Auxiliary: sigma(x) < 1 (from 1 < 1+e^{-x}, inv reversing order, and inv 1 == 1). *)
Lemma real_sigmoid_lt_one : forall x : Real,
  real_lt (real_sigmoid x) real_one.
Proof.
  intro x.
  unfold real_sigmoid.
  apply (RealSetoid.real_lt_id_r (real_inv_pos (real_plus real_one (real_exp_neg x))
                                               (real_sigmoid_denom_pos x))
                                 (real_inv_pos real_one real_lt_zero_one)
                                 real_one).
  - apply real_inv_one_local.
  - apply (real_inv_lt_contra real_one (real_plus real_one (real_exp_neg x))
                              real_lt_zero_one (real_sigmoid_denom_pos x)).
    apply (real_one_lt_succ_pos (real_exp_neg x) (real_exp_neg_pos x)).
Qed.

(* Auxiliary: log sigma(x) < 0 (from sigma < 1, strict monotonicity of log, and log 1 == 0). *)
Lemma real_sigmoid_log_neg : forall x : Real,
  real_lt (real_log (real_sigmoid x) (real_sigmoid_pos x)) real_zero.
Proof.
  intro x.
  apply (RealSetoid.real_lt_id_r (real_log (real_sigmoid x) (real_sigmoid_pos x))
                                 (real_log real_one real_lt_zero_one)
                                 real_zero).
  - apply real_log_one.
  - apply (real_log_lt_mono (real_sigmoid x) real_one
                            (real_sigmoid_pos x) real_lt_zero_one).
    apply (real_sigmoid_lt_one x).
Qed.

(* T1.4 main theorem: r_l < r_w implies 0 < L_DPO(pi*,s_w,s_l) < log 2 (two-sided quantitative bound). *)
Theorem real_dpo_loss_pi_star_bounded_both :
  forall (s_w s_l : S),
    real_lt (reward s_l) (reward s_w) ->
    And (real_lt real_zero (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l))
        (real_lt (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
                 (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  intros s_w s_l Hrw.
  split.
  - (* 0 < L: L == -log sigma(r_w - r_l) (at_pi_star) and 0 < -log sigma. *)
    apply (RealSetoid.real_lt_id_r real_zero
             (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                                 (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
             (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)).
    + apply (real_eq_sym (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
                         (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                                             (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
                         (real_dpo_loss_at_pi_star s_w s_l)).
    + (* 0 < -log sigma: [real_opp_lt_compat] applied to log sigma < 0,
         with the restatement opp zero == zero. *)
      apply (RealSetoid.real_lt_id_l real_zero
               (real_opp real_zero)
               (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                                   (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))).
      * apply (real_eq_sym real_zero (real_opp real_zero) (real_opp_zero)).
      * apply (real_opp_lt_compat (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                                            (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l)))))
                                  real_zero).
        apply (real_sigmoid_log_neg (real_plus (reward s_w) (real_opp (reward s_l)))).
  - exact (real_dpo_loss_pi_star_bounded_eps s_w s_l Hrw).
Qed.

(* ============================================================ *)
(* B-8-1: DPO reward recovery (Real-layer replica).              *)
(*   Real version of the abstract-level                          *)
(*   dpo_reward_recovers_up_to_baseline:                         *)
(*   beta*(log pi*(s) - log pi_ref(s)) == r(s) - beta*log Z_align, *)
(*   i.e. the DPO implicit reward at pi* recovers the true reward *)
(*   exactly, up to the baseline offset beta*log Z_align.         *)
(*   Assembly: real_log_pi_star (closed form) + a Real-layer     *)
(*   algebraic chain (cancellation of log pi_ref, distribution   *)
(*   of beta, absorption of beta*(1/beta), restatement via opp). *)
(* ============================================================ *)

(* Real-layer explicit DPO reward: beta*(log pi(s) - log pi_ref(s)). *)
Definition real_dpo_reward_explicit (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s : S) : Real :=
  real_mult beta (real_plus (real_log (pi s) (Hpi s))
                            (real_opp (real_log (pi_ref s) (pi_ref_pos s)))).

Theorem real_dpo_reward_recovers_up_to_baseline : forall (s : S),
  real_eq (real_dpo_reward_explicit real_pi_star real_pi_star_pos s)
          (real_plus (reward s) (real_opp (real_mult beta (real_log Z_align Z_align_pos)))).
Proof.
  intro s.
  unfold real_dpo_reward_explicit.
  (* log pi* == -log Z + (log pi_ref + r/beta) (closed form). *)
  assert (Hlog : real_eq (real_log (real_pi_star s) (real_pi_star_pos s))
                         (real_plus (real_opp (real_log Z_align Z_align_pos))
                                    (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                               (real_mult (real_inv_pos beta beta_pos) (reward s)))))
    by exact (real_log_pi_star s).
  (* Inner cancellation: (log pi_ref + r/beta) + opp(log pi_ref) == r/beta. *)
  assert (Hcancel : real_eq (real_plus (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                  (real_mult (real_inv_pos beta beta_pos) (reward s)))
                                       (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
                            (real_mult (real_inv_pos beta beta_pos) (reward s))).
  {
    apply (real_eq_trans _ (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                      (real_plus (real_mult (real_inv_pos beta beta_pos) (reward s))
                                                 (real_opp (real_log (pi_ref s) (pi_ref_pos s))))) _).
    - apply (real_eq_sym _ _
               (real_plus_assoc (real_log (pi_ref s) (pi_ref_pos s))
                                (real_mult (real_inv_pos beta beta_pos) (reward s))
                                (real_opp (real_log (pi_ref s) (pi_ref_pos s))))).
    - apply (real_eq_trans _ (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                        (real_plus (real_opp (real_log (pi_ref s) (pi_ref_pos s)))
                                                   (real_mult (real_inv_pos beta beta_pos) (reward s)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_log (pi_ref s) (pi_ref_pos s))
                                              (real_plus (real_mult (real_inv_pos beta beta_pos) (reward s))
                                                         (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
                                              (real_log (pi_ref s) (pi_ref_pos s))
                                              (real_plus (real_opp (real_log (pi_ref s) (pi_ref_pos s)))
                                                         (real_mult (real_inv_pos beta beta_pos) (reward s)))
                                              (real_eq_refl _)
                                              (real_plus_comm (real_mult (real_inv_pos beta beta_pos) (reward s))
                                                              (real_opp (real_log (pi_ref s) (pi_ref_pos s))))).
      + apply (real_eq_trans _ (real_plus (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                     (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
                                          (real_mult (real_inv_pos beta beta_pos) (reward s))) _).
        * apply (real_plus_assoc (real_log (pi_ref s) (pi_ref_pos s))
                                 (real_opp (real_log (pi_ref s) (pi_ref_pos s)))
                                 (real_mult (real_inv_pos beta beta_pos) (reward s))).
        * apply (real_eq_trans _ (real_plus real_zero (real_mult (real_inv_pos beta beta_pos) (reward s))) _).
          -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                             (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
                                                  (real_mult (real_inv_pos beta beta_pos) (reward s))
                                                  real_zero
                                                  (real_mult (real_inv_pos beta beta_pos) (reward s))
                                                  (real_plus_opp (real_log (pi_ref s) (pi_ref_pos s)))
                                                  (real_eq_refl _)).
          -- apply (real_eq_trans _ (real_mult (real_inv_pos beta beta_pos) (reward s)) _).
             ** apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos beta beta_pos) (reward s)) real_zero) _).
                --- apply (real_plus_comm real_zero (real_mult (real_inv_pos beta beta_pos) (reward s))).
                --- apply (real_plus_zero (real_mult (real_inv_pos beta beta_pos) (reward s))).
             ** apply (real_eq_refl _).
  }
  (* beta*(opp logZ) == opp(beta*logZ). *)
  assert (Hopp : real_eq (real_mult beta (real_opp (real_log Z_align Z_align_pos)))
                         (real_opp (real_mult beta (real_log Z_align Z_align_pos)))).
  {
    apply (real_eq_trans _ (real_mult (real_opp (real_log Z_align Z_align_pos)) beta) _).
    - apply (real_mult_comm beta (real_opp (real_log Z_align Z_align_pos))).
    - apply (real_eq_trans _ (real_opp (real_mult (real_log Z_align Z_align_pos) beta)) _).
      + apply (real_eq_sym _ _
                 (real_opp_mult_r (real_log Z_align Z_align_pos) beta)).
      + apply (RealSetoid.real_eq_opp_compat (real_mult (real_log Z_align Z_align_pos) beta)
                                             (real_mult beta (real_log Z_align Z_align_pos))
                                             (real_mult_comm (real_log Z_align Z_align_pos) beta)).
  }
  (* beta·((1/beta)·r) == r. *)
  assert (Habsorb : real_eq (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s)))
                            (reward s)).
  {
    apply (real_eq_trans _ (real_mult (real_mult beta (real_inv_pos beta beta_pos)) (reward s)) _).
    - apply (real_mult_assoc beta (real_inv_pos beta beta_pos) (reward s)).
    - apply (real_eq_trans _ (real_mult real_one (reward s)) _).
      + apply (RealSetoid.real_eq_mult_compat (real_mult beta (real_inv_pos beta beta_pos))
                                              (reward s)
                                              real_one
                                              (reward s)
                                              (real_inv_pos_correct beta beta_pos)
                                              (real_eq_refl _)).
      + apply (real_eq_trans _ (real_mult (reward s) real_one) _).
        * apply (real_mult_comm real_one (reward s)).
        * apply (real_mult_one (reward s)).
  }
  (* Main chain: beta*(log pi* + opp log pi_ref)
     == beta*((-logZ + (log pi_ref + r/beta)) + opp log pi_ref)
     == beta·(-logZ + r/beta) == beta·(-logZ) + beta·((1/beta)·r)
     == -(beta*logZ) + r == r + -(beta*logZ). *)
  apply (real_eq_trans _ (real_mult beta
                          (real_plus (real_plus (real_opp (real_log Z_align Z_align_pos))
                                                (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                           (real_mult (real_inv_pos beta beta_pos) (reward s))))
                                     (real_opp (real_log (pi_ref s) (pi_ref_pos s))))) _).
  - (* Substitute the closed form for log pi*. *)
    apply (RealSetoid.real_eq_mult_compat beta
             (real_plus (real_log (real_pi_star s) (real_pi_star_pos s))
                        (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
             beta
             (real_plus (real_plus (real_opp (real_log Z_align Z_align_pos))
                                   (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                              (real_mult (real_inv_pos beta beta_pos) (reward s))))
                        (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
             (real_eq_refl beta)
             (RealSetoid.real_eq_plus_compat
                (real_log (real_pi_star s) (real_pi_star_pos s))
                (real_opp (real_log (pi_ref s) (pi_ref_pos s)))
                (real_plus (real_opp (real_log Z_align Z_align_pos))
                           (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                      (real_mult (real_inv_pos beta beta_pos) (reward s))))
                (real_opp (real_log (pi_ref s) (pi_ref_pos s)))
                Hlog (real_eq_refl _))).
  - (* Algebraic simplification. *)
    apply (real_eq_trans _ (real_mult beta
                          (real_plus (real_opp (real_log Z_align Z_align_pos))
                                     (real_mult (real_inv_pos beta beta_pos) (reward s)))) _).
    + (* Inner cancellation: (plus A (plus B C)) + D == A + C. *)
      apply (RealSetoid.real_eq_mult_compat beta
               (real_plus (real_plus (real_opp (real_log Z_align Z_align_pos))
                                     (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                (real_mult (real_inv_pos beta beta_pos) (reward s))))
                          (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
               beta
               (real_plus (real_opp (real_log Z_align Z_align_pos))
                          (real_mult (real_inv_pos beta beta_pos) (reward s)))
               (real_eq_refl beta)
               (real_eq_trans _ _ _
                  (real_eq_sym _ _
                     (real_plus_assoc (real_opp (real_log Z_align Z_align_pos))
                                      (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                 (real_mult (real_inv_pos beta beta_pos) (reward s)))
                                      (real_opp (real_log (pi_ref s) (pi_ref_pos s)))))
                  (RealSetoid.real_eq_plus_compat
                     (real_opp (real_log Z_align Z_align_pos))
                     (real_plus (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                           (real_mult (real_inv_pos beta beta_pos) (reward s)))
                                (real_opp (real_log (pi_ref s) (pi_ref_pos s))))
                     (real_opp (real_log Z_align Z_align_pos))
                     (real_mult (real_inv_pos beta beta_pos) (reward s))
                     (real_eq_refl _) Hcancel))).
    + (* beta*(A + C) == beta*A + beta*C == -(beta*logZ) + r == r + -(beta*logZ). *)
      apply (real_eq_trans _ (real_plus (real_mult beta (real_opp (real_log Z_align Z_align_pos)))
                                        (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s)))) _).
      * apply (real_distrib beta (real_opp (real_log Z_align Z_align_pos))
                             (real_mult (real_inv_pos beta beta_pos) (reward s))).
      * apply (real_eq_trans _ (real_plus (real_opp (real_mult beta (real_log Z_align Z_align_pos)))
                                          (reward s)) _).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_mult beta (real_opp (real_log Z_align Z_align_pos)))
                    (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s)))
                    (real_opp (real_mult beta (real_log Z_align Z_align_pos)))
                    (reward s)
                    Hopp Habsorb).
        -- apply (real_plus_comm (real_opp (real_mult beta (real_log Z_align Z_align_pos)))
                                 (reward s)).
Qed.

End DpoPairMain.

(* ============================================================ *)
(* B-8-2: GRPO group-relative advantage has zero mean            *)
(*   (Real-layer replica).                                       *)
(*   Real version of the abstract-level grpo_advantage_zero_mean: *)
(*   sum_i (r_i - mu)·c == 0 for any scaling factor c.            *)
(*   Infrastructure: real_of_nat (embedding of nat into Real) +   *)
(*   the real_list_sum_g family (ext/add/linear/opp/minus/const,  *)
(*   list-fold summation).                                        *)
(*   Assembly: commutativity of mult, then scalar linearity, then *)
(*   the cancellation chain sum A_i == 0                          *)
(*   (sum r - G*mu == sum r - sum r == 0, absorbing G*(1/G)).     *)
(* ============================================================ *)

Section RealGrpoMain.

(* Embedding of nat into Real (0 maps to real_zero, S n maps to real_one + of_nat n). *)
Fixpoint real_of_nat (n : nat) : Real :=
  match n with
  | O => real_zero
  | Datatypes.S n' => real_plus real_one (real_of_nat n')
  end.

(* Honest interface: a finite group, an enumerating cover, and positivity
   of the group size (instantiable in the Real layer with a concrete finite type). *)
Variable Group : Set.
Variable group_enum : list Group.
Variable group_cover : forall i : Group, InT i group_enum.
Definition real_group_size : nat := length group_enum.
Variable real_group_size_pos : real_lt real_zero (real_of_nat real_group_size).
Variable reward_group : Group -> Real.

(* Group sum (list fold, Real layer). *)
Fixpoint real_list_sum_g (f : Group -> Real) (l : list Group) : Real :=
  match l with
  | nil => real_zero
  | i :: rest => real_plus (f i) (real_list_sum_g f rest)
  end.

(* Pointwise extensionality: f == g pointwise implies sum == sum. *)
Lemma real_list_sum_g_ext : forall (f g : Group -> Real) (l : list Group),
  (forall i : Group, real_eq (f i) (g i)) -> real_eq (real_list_sum_g f l) (real_list_sum_g g l).
Proof.
  intros f g l Hfg.
  induction l as [| i rest IH]; simpl.
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat (f i) (real_list_sum_g f rest)
                                          (g i) (real_list_sum_g g rest)).
    + exact (Hfg i).
    + exact IH.
Qed.

(* Scalar linearity: sum(a*f) == a*sum(f). *)
Lemma real_list_sum_g_linear : forall a : Real, forall f : Group -> Real, forall l : list Group,
  real_eq (real_list_sum_g (fun i => real_mult a (f i)) l) (real_mult a (real_list_sum_g f l)).
Proof.
  intros a f l.
  induction l as [| i rest IH]; simpl.
  - apply (real_eq_sym _ _ (real_mult_zero a)).
  - apply (real_eq_trans _ (real_plus (real_mult a (f i)) (real_mult a (real_list_sum_g f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult a (f i))
                                            (real_list_sum_g (fun i => real_mult a (f i)) rest)
                                            (real_mult a (f i))
                                            (real_mult a (real_list_sum_g f rest))
                                            (real_eq_refl _) IH).
    + apply (real_eq_sym _ _ (real_distrib a (f i) (real_list_sum_g f rest))).
Qed.

(* Additivity of the sum: sum(f+g) == sum(f) + sum(g). *)
Lemma real_list_sum_g_add : forall (f g : Group -> Real) (l : list Group),
  real_eq (real_list_sum_g (fun i => real_plus (f i) (g i)) l)
          (real_plus (real_list_sum_g f l) (real_list_sum_g g l)).
Proof.
  intros f g l.
  induction l as [| i rest IH]; simpl.
  - apply (real_eq_sym _ _ (real_plus_zero real_zero)).
  - (* cons: f i + g i + sum(f+g) rest == (f i + sum f rest) + (g i + sum g rest). *)
    apply (real_eq_trans _ (real_plus (f i) (real_plus (g i) (real_plus (real_list_sum_g f rest) (real_list_sum_g g rest)))) _).
    + apply (real_eq_trans _ (real_plus (f i) (real_plus (g i) (real_list_sum_g (fun i => real_plus (f i) (g i)) rest))) _).
      * apply (real_eq_sym _ _ (real_plus_assoc (f i) (g i) (real_list_sum_g (fun i => real_plus (f i) (g i)) rest))).
      * apply (RealSetoid.real_eq_plus_compat (f i)
                                              (real_plus (g i) (real_list_sum_g (fun i => real_plus (f i) (g i)) rest))
                                              (f i)
                                              (real_plus (g i) (real_plus (real_list_sum_g f rest) (real_list_sum_g g rest)))
                                              (real_eq_refl _)
                                              (RealSetoid.real_eq_plus_compat (g i)
                                                                              (real_list_sum_g (fun i => real_plus (f i) (g i)) rest)
                                                                              (g i)
                                                                              (real_plus (real_list_sum_g f rest) (real_list_sum_g g rest))
                                                                              (real_eq_refl _) IH)).
    + apply (real_eq_trans _ (real_plus (real_plus (f i) (g i)) (real_plus (real_list_sum_g f rest) (real_list_sum_g g rest))) _).
      * apply (real_plus_assoc (f i) (g i) (real_plus (real_list_sum_g f rest) (real_list_sum_g g rest))).
      * apply (real_plus_swap_mid (f i) (g i) (real_list_sum_g f rest) (real_list_sum_g g rest)).
Qed.

(* Right distributivity (proved directly in the Real layer by composing
   commutativity with [real_distrib]; avoids a forward reference). *)
Lemma real_distrib_r_local : forall x y z : Real,
  real_eq (real_plus (real_mult x z) (real_mult y z)) (real_mult (real_plus x y) z).
Proof.
  intros x y z.
  apply (real_eq_trans _ (real_plus (real_mult z x) (real_mult z y)) _).
  - apply (RealSetoid.real_eq_plus_compat (real_mult x z) (real_mult y z)
                                          (real_mult z x) (real_mult z y)
                                          (real_mult_comm x z) (real_mult_comm y z)).
  - apply (real_eq_trans _ (real_mult z (real_plus x y)) _).
    + apply (real_eq_sym _ _ (real_distrib z x y)).
    + apply (real_mult_comm z (real_plus x y)).
Qed.

(* Constant sum: sum (const c) == real_of_nat (length l) * c. *)
Lemma real_list_sum_g_const : forall (c : Real) (l : list Group),
  real_eq (real_list_sum_g (fun _ : Group => c) l)
          (real_mult (real_of_nat (length l)) c).
Proof.
  intros c l.
  induction l as [| i rest IH]; simpl.
  - (* nil: zero == of_nat 0 * c == 0 * c (of_nat 0 is definitionally
       real_zero; real_zero == c*0 == 0*c). *)
    apply (real_eq_trans _ _ _ (real_eq_sym _ _ (real_mult_zero c)) (real_mult_comm c real_zero)).
  - (* cons: c + of_nat(len)·c == (1 + of_nat(len))·c == of_nat(S len)·c. *)
    apply (real_eq_trans _ (real_plus c (real_mult (real_of_nat (length rest)) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c (real_list_sum_g (fun _ : Group => c) rest)
                                            c (real_mult (real_of_nat (length rest)) c)
                                            (real_eq_refl _) IH).
    + apply (real_eq_trans _ (real_plus (real_mult real_one c) (real_mult (real_of_nat (length rest)) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c (real_mult (real_of_nat (length rest)) c)
                                              (real_mult real_one c) (real_mult (real_of_nat (length rest)) c)
                                              (real_eq_sym _ _ (real_eq_trans _ _ _ (real_mult_comm real_one c) (real_mult_one c)))
                                              (real_eq_refl _)).
      * apply (real_eq_trans _ (real_mult (real_plus real_one (real_of_nat (length rest))) c) _).
        -- apply (real_distrib_r_local real_one (real_of_nat (length rest)) c).
        -- apply real_eq_refl.
Qed.

(* Negation of the sum: sum(opp f) == opp(sum f). *)
Lemma real_list_sum_g_opp : forall (f : Group -> Real) (l : list Group),
  real_eq (real_list_sum_g (fun i => real_opp (f i)) l) (real_opp (real_list_sum_g f l)).
Proof.
  intros f l.
  induction l as [| i rest IH]; simpl.
  - apply (real_eq_sym _ _ (real_opp_zero)).
  - (* opp(f i) + opp(sum rest) == opp(f i + sum rest). *)
    apply (real_eq_trans _ (real_plus (real_opp (f i)) (real_opp (real_list_sum_g f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp (f i))
                                            (real_list_sum_g (fun i => real_opp (f i)) rest)
                                            (real_opp (f i))
                                            (real_opp (real_list_sum_g f rest))
                                            (real_eq_refl _) IH).
    + apply (real_eq_sym _ _ (real_opp_plus (f i) (real_list_sum_g f rest))).
Qed.

(* Difference of sums: sum(f - g) == sum(f) - sum(g). *)
Lemma real_list_sum_g_minus : forall (f g : Group -> Real) (l : list Group),
  real_eq (real_list_sum_g (fun i => real_plus (f i) (real_opp (g i))) l)
          (real_plus (real_list_sum_g f l) (real_opp (real_list_sum_g g l))).
Proof.
  intros f g l.
  apply (real_eq_trans _ (real_plus (real_list_sum_g f l) (real_list_sum_g (fun i => real_opp (g i)) l)) _).
  - apply (real_list_sum_g_add f (fun i => real_opp (g i)) l).
  - apply (RealSetoid.real_eq_plus_compat (real_list_sum_g f l)
                                          (real_list_sum_g (fun i => real_opp (g i)) l)
                                          (real_list_sum_g f l)
                                          (real_opp (real_list_sum_g g l))
                                          (real_eq_refl _) (real_list_sum_g_opp g l)).
Qed.

(* Group mean: mu = (1/G) * sum r_i. *)
Definition real_group_mean : Real :=
  real_mult (real_inv_pos (real_of_nat real_group_size) real_group_size_pos)
            (real_list_sum_g reward_group group_enum).

(* Group-relative advantage: A_i = r_i - mu. *)
Definition real_grpo_advantage (i : Group) : Real :=
  real_plus (reward_group i) (real_opp real_group_mean).

(* Constant sum == G*c with G := length group_enum, so sum mu == sum r
   (mu := (1/G)·sum r, absorbing the inverse). *)
Lemma real_group_mean_sum : forall (l : list Group),
  real_eq (real_list_sum_g (fun _ : Group => real_group_mean) l)
          (real_mult (real_of_nat (length l)) real_group_mean).
Proof.
  intro l.
  apply (real_list_sum_g_const real_group_mean l).
Qed.

(* Zero mean (B-8-2 main theorem): sum_i (r_i - mu)·c == 0 for any scaling c. *)
Theorem real_grpo_advantage_zero_mean : forall c : Real,
  real_eq (real_list_sum_g (fun i => real_mult (real_grpo_advantage i) c) group_enum) real_zero.
Proof.
  intros c.
  (* Cancellation core: sum A_i == 0. *)
  assert (Hcancel : real_eq (real_list_sum_g real_grpo_advantage group_enum) real_zero).
  {
    unfold real_grpo_advantage.
    (* sum (r_i - mu) == sum r - sum mu. *)
    apply (real_eq_trans _ (real_plus (real_list_sum_g reward_group group_enum)
                                      (real_opp (real_list_sum_g (fun _ : Group => real_group_mean) group_enum))) _).
    - apply (real_list_sum_g_minus reward_group (fun _ : Group => real_group_mean) group_enum).
    - (* sum mu == sum r (G*mu == sum r, absorbing G*(1/G)). *)
      assert (Hmu : real_eq (real_list_sum_g (fun _ : Group => real_group_mean) group_enum)
                            (real_list_sum_g reward_group group_enum)).
      {
        (* sum mu == of_nat G * mu (const lemma, G := length group_enum). *)
        apply (real_eq_trans _ (real_mult (real_of_nat real_group_size) real_group_mean) _).
        - apply (real_list_sum_g_const real_group_mean group_enum).
        - (* G·mu == sum r: G·((1/G)·sum r) == (G·(1/G))·sum r == 1·sum r == sum r. *)
          unfold real_group_mean.
          apply (real_eq_trans _ (real_mult (real_mult (real_of_nat real_group_size)
                                                       (real_inv_pos (real_of_nat real_group_size) real_group_size_pos))
                                            (real_list_sum_g reward_group group_enum)) _).
          + apply (real_mult_assoc (real_of_nat real_group_size)
                                   (real_inv_pos (real_of_nat real_group_size) real_group_size_pos)
                                   (real_list_sum_g reward_group group_enum)).
          + apply (real_eq_trans _ (real_mult real_one (real_list_sum_g reward_group group_enum)) _).
            * apply (RealSetoid.real_eq_mult_compat (real_mult (real_of_nat real_group_size)
                                                               (real_inv_pos (real_of_nat real_group_size) real_group_size_pos))
                                                    (real_list_sum_g reward_group group_enum)
                                                    real_one
                                                    (real_list_sum_g reward_group group_enum)
                                                    (real_inv_pos_correct (real_of_nat real_group_size) real_group_size_pos)
                                                    (real_eq_refl _)).
            * apply (real_eq_trans _ (real_mult (real_list_sum_g reward_group group_enum) real_one) _).
              -- apply (real_mult_comm real_one (real_list_sum_g reward_group group_enum)).
              -- apply (real_mult_one (real_list_sum_g reward_group group_enum)).
      }
      (* sum r - sum mu == sum r - sum r == 0. *)
      apply (real_eq_trans _ (real_plus (real_list_sum_g reward_group group_enum)
                                        (real_opp (real_list_sum_g reward_group group_enum))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum_g reward_group group_enum)
                                              (real_opp (real_list_sum_g (fun _ : Group => real_group_mean) group_enum))
                                              (real_list_sum_g reward_group group_enum)
                                              (real_opp (real_list_sum_g reward_group group_enum))
                                              (real_eq_refl _)
                                              (RealSetoid.real_eq_opp_compat
                                                 (real_list_sum_g (fun _ : Group => real_group_mean) group_enum)
                                                 (real_list_sum_g reward_group group_enum)
                                                 Hmu)).
      + apply (real_plus_opp (real_list_sum_g reward_group group_enum)).
  }
  (* sum (A_i*c) == sum (c*A_i) == c*sum A_i == c*0 == 0. *)
  apply (real_eq_trans _ (real_list_sum_g (fun i => real_mult c (real_grpo_advantage i)) group_enum) _).
  - apply (real_list_sum_g_ext (fun i => real_mult (real_grpo_advantage i) c)
                                (fun i => real_mult c (real_grpo_advantage i)) group_enum).
    intro i. apply (real_mult_comm (real_grpo_advantage i) c).
  - apply (real_eq_trans _ (real_mult c (real_list_sum_g real_grpo_advantage group_enum)) _).
    + apply (real_list_sum_g_linear c real_grpo_advantage group_enum).
    + apply (real_eq_trans _ (real_mult c real_zero) _).
      * apply (RealSetoid.real_eq_mult_compat c (real_list_sum_g real_grpo_advantage group_enum)
                                              c real_zero
                                              (real_eq_refl c) Hcancel).
      * apply (real_mult_zero c).
Qed.

End RealGrpoMain.

(* ============================================================ *)
(* B-8-3: softmax = Boltzmann (Real-layer replica).              *)
(*   Real version of the abstract-level attention_is_gibbs:       *)
(*   unit temperature (inv D == 1), energy == -logits, and equal  *)
(*   partition sums imply softmax(z,s) == boltzmann_dist_attn(s)  *)
(*   pointwise.                                                   *)
(*   Honest interface: real_sum_over_S (summation over the        *)
(*   abstract S, supplied at Real-layer instantiation — the       *)
(*   Real-layer form of S without an enumeration-bounds premise).   *)
(*   Assembly: reduce mult (inv D) (energy s) to energy s         *)
(*   (HD + comm + mult_one), substitute energy == -logits,        *)
(*   transport the equality via cauchy_real_exp_wd, unify the     *)
(*   inverses by real_inv_pos_ext, finish by mult_comm.           *)
(* ============================================================ *)

Section RealAttnMain.

(* Abstract state space (declared by this Real-layer Section, as in DpoPairMain). *)
Variable S : Type.

(* Honest interface: summation over the abstract S (instantiable in the Real layer; axiom-free). *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real), (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).

(* Temperature / energy / logits environment (Real layer). *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable z_logits : S -> Real.

(* Real-layer exp_pos_fn: e^{x} (the softmax numerator). *)
Definition real_exp_pos_fn (x : Real) : Real := real_exp_neg (real_opp x).

(* Partition function (Real layer): sum_s e^{z_logits s}. *)
Definition real_partition_function (z_logits : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (z_logits s)).

Lemma real_partition_function_pos : forall z_logits : S -> Real, real_lt real_zero (real_partition_function z_logits).
Proof.
  intros zz. unfold real_partition_function, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* Softmax (Real layer): e^{z_logits s} * inv(sum e^{z_logits}). *)
Definition real_softmax (z_logits : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (z_logits s)) (real_inv_pos (real_partition_function z_logits) (real_partition_function_pos z_logits)).

(* Boltzmann factor (Real layer): e^{-e(s)/D}. *)
Definition real_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

(* Thermodynamic partition (Real layer): sum_s boltzmann_factor. *)
Definition real_Z_thermo : Real := real_sum_over_S real_boltzmann_factor.

Variable real_Z_thermo_pos : real_lt real_zero real_Z_thermo.

(* Boltzmann distribution (Real layer): inv(Z_thermo) * factor. *)
Definition real_boltzmann_dist_attn (s : S) : Real :=
  real_mult (real_inv_pos real_Z_thermo real_Z_thermo_pos) (real_boltzmann_factor s).

(* softmax = Boltzmann at unit temperature (B-8-3 main theorem):
   inv D == 1, energy == -logits, and Z_thermo == partition_function z_logits
   imply, for every state s, softmax(z_logits,s) == boltzmann_dist_attn(s). *)
Theorem real_attention_is_gibbs :
  (real_eq (real_inv_pos D D_pos) real_one) ->
  (forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
  real_eq real_Z_thermo (real_partition_function z_logits) ->
  forall s : S, real_eq (real_softmax z_logits s) (real_boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  unfold real_softmax, real_boltzmann_dist_attn, real_boltzmann_factor, real_exp_pos_fn.
  (* 1. Reduce the Boltzmann-side exponent: e^{-e(s)/D} == e^{z_logits s}
     (since mult (inv D) (energy s) == energy s == opp (z_logits s)). *)
  assert (Hbf : real_eq (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))
                        (real_exp_neg (real_opp (z_logits s)))).
  {
    assert (Hm : real_eq (real_mult (real_inv_pos D D_pos) (energy s)) (real_opp (z_logits s))).
    {
      apply (real_eq_trans _ (energy s) _).
      - apply (real_eq_trans _ (real_mult real_one (energy s)) _).
        + apply (RealSetoid.real_eq_mult_compat (real_inv_pos D D_pos) (energy s) real_one (energy s) HD (real_eq_refl _)).
        + apply (real_eq_trans _ _ _ (real_mult_comm real_one (energy s)) (real_mult_one (energy s))).
      - exact (Henergy s).
    }
    apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos D D_pos) (energy s)) (real_opp (z_logits s)) Hm).
  }
  (* 2. Unify the inverses: inv(Z_thermo) == inv(partition_function z_logits)
     (by HZ and [real_inv_pos_ext]). *)
  assert (Hinv : real_eq (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                         (real_inv_pos (real_partition_function z_logits) (real_partition_function_pos z_logits))).
  { apply (real_inv_pos_ext real_Z_thermo (real_partition_function z_logits) real_Z_thermo_pos (real_partition_function_pos z_logits)). exact HZ. }
  (* 3. Assembly: mult (e^{z_logits s}) (inv Pf) == mult (inv Z) (e^{-e/D}):
     the LHS is definitional; unify the inverses (sym Hinv), commute,
     then substitute the exponent (sym Hbf). *)
  apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (z_logits s)))
                                    (real_inv_pos (real_partition_function z_logits) (real_partition_function_pos z_logits))) _).
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (z_logits s))) (real_inv_pos real_Z_thermo real_Z_thermo_pos)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_exp_neg (real_opp (z_logits s)))
                                            (real_inv_pos (real_partition_function z_logits) (real_partition_function_pos z_logits))
                                            (real_exp_neg (real_opp (z_logits s)))
                                            (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                                            (real_eq_refl _) (real_eq_sym _ _ Hinv)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos real_Z_thermo real_Z_thermo_pos) (real_exp_neg (real_opp (z_logits s)))) _).
      * apply (real_mult_comm (real_exp_neg (real_opp (z_logits s))) (real_inv_pos real_Z_thermo real_Z_thermo_pos)).
      * apply (RealSetoid.real_eq_mult_compat (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                                              (real_exp_neg (real_opp (z_logits s)))
                                              (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                                              (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))
                                              (real_eq_refl _) (real_eq_sym _ _ Hbf)).
Qed.

End RealAttnMain.

(* ============================================================ *)
(* B-8-4: Boltzmann attention steady-state equation              *)
(*   (Real-layer replica).                                       *)
(*   Real version of the abstract-level steady_state_boltzmann_attn: *)
(*   sum_s' p(s')·T(s',s) == p(s) (steady state, assembled from  *)
(*   detailed balance and kernel normalization).                 *)
(*   Honest interface (axiom-free): real_sum_over_S_ext/linear   *)
(*   (extensionality/linearity of summation) +                   *)
(*   real_detailed_balance + real_transition_normalization       *)
(*   (instantiable in the Real layer).                           *)
(* ============================================================ *)

Section RealAttnSteady.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable Z_thermo : Real.
Variable Z_thermo_pos : real_lt real_zero Z_thermo.

(* Boltzmann attention distribution (Real layer): p(s) := inv(Z)·e^{-e(s)/D}. *)
Definition real_boltzmann_dist_attn_s (s : S) : Real :=
  real_mult (real_inv_pos Z_thermo Z_thermo_pos) (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s))).

(* Transition kernel (Real layer). *)
Variable real_transition : S -> S -> Real.

(* Honest interface: detailed balance (reversible kernel, instantiable in the Real layer). *)
Variable real_detailed_balance : forall (s s' : S),
  real_eq (real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s))
          (real_mult (real_boltzmann_dist_attn_s s) (real_transition s s')).

(* Honest interface: row normalization sum_s' T(s,s') == 1 (the standard Markov-kernel property). *)
Variable real_transition_normalization : forall s : S,
  real_eq (real_sum_over_S (fun s' => real_transition s s')) real_one.

(* Steady-state equation (B-8-4 main theorem): sum_s' p(s')·T(s',s) == p(s).
   Assembly: substitute detailed balance pointwise, apply extensionality
   of the sum, extract p(s) by linearity, use kernel normalization,
   finish by mult_one. *)
Theorem real_steady_state_boltzmann_attn : forall s : S,
  real_eq (real_sum_over_S (fun s' => real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s)))
          (real_boltzmann_dist_attn_s s).
Proof.
  intro s.
  (* 1. Substitute detailed balance pointwise: sum (p s' * T s' s) == sum (p s * T s s'). *)
  apply (real_eq_trans _ (real_sum_over_S (fun s' => real_mult (real_boltzmann_dist_attn_s s) (real_transition s s'))) _).
  - apply (real_sum_over_S_ext (fun s' => real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s))
                               (fun s' => real_mult (real_boltzmann_dist_attn_s s) (real_transition s s'))).
    intro s'. apply (real_detailed_balance s s').
  - (* 2. Extract by linearity: sum (p s * T s s') == p s * sum (T s s'). *)
    apply (real_eq_trans _ (real_mult (real_boltzmann_dist_attn_s s) (real_sum_over_S (fun s' => real_transition s s'))) _).
    + apply (real_sum_over_S_linear (real_boltzmann_dist_attn_s s) (fun s' => real_transition s s')).
    + (* 3. Kernel normalization: sum T == 1, so p s * 1 == p s. *)
      apply (real_eq_trans _ (real_mult (real_boltzmann_dist_attn_s s) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat (real_boltzmann_dist_attn_s s)
                                              (real_sum_over_S (fun s' => real_transition s s'))
                                              (real_boltzmann_dist_attn_s s) real_one
                                              (real_eq_refl _) (real_transition_normalization s)).
      * apply (real_mult_one (real_boltzmann_dist_attn_s s)).
Qed.

End RealAttnSteady.

(* ============================================================ *)
(* B-8-5: Min-P truncated kernel normalization (Real-layer replica). *)
(*   Real version of the abstract-level                          *)
(*   minp_markov_kernel_normalized:                              *)
(*   sum_w minp_kernel(prefix,w) == 1 (conservation of probability). *)
(*   Assembly: swap branches pointwise (keep branch by mult_comm, *)
(*   drop branch by mult_zero backwards), extract inv(temp_sum)   *)
(*   by scalar linearity, finish with                             *)
(*   inv(temp_sum)·temp_sum == 1 (by inv_pos_correct).            *)
(*   Honest interface (axiom-free): real_minp_keep_dec (decidable, *)
(*   Set-layer Or) + real_minp_temp_sum_pos (kept set nonempty    *)
(*   and factors positive).                                       *)
(* ============================================================ *)

Section RealMinPMain.

Variable Token : Type.
Variable vocab : list Token.

(* Temperature factor (Real layer): e^{-loss/T}. *)
Variable real_temp_factor : Token -> Real.

(* Decidable interface: the Real-layer form of minp_keep_dec (Set-layer Or, instantiable). *)
Variable real_minp_keep : list Token -> Token -> Set.
Variable real_minp_keep_dec : forall (prefix : list Token) (w : Token),
  Or (real_minp_keep prefix w) (Not (real_minp_keep prefix w)).

(* Truncated mass: the temp_factor of kept branches (matched on the decidability). *)
Definition real_minp_temp_sum (prefix : list Token) : Real :=
  real_list_sum Token (fun w => match real_minp_keep_dec prefix w with
                          | inl _ => real_temp_factor w
                          | inr _ => real_zero
                          end) vocab.

(* Positivity interface (instantiable in the Real layer: kept set nonempty and factors positive). *)
Variable real_minp_temp_sum_pos : forall prefix : list Token,
  real_lt real_zero (real_minp_temp_sum prefix).

(* Min-P truncated kernel (Real layer): keep maps to temp_factor*inv(sum), drop maps to zero. *)
Definition real_minp_markov_kernel (prefix : list Token) (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ => real_mult (real_temp_factor w)
                       (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
  | inr _ => real_zero
  end.

(* Normalization (B-8-5 main theorem): sum_w minp_kernel(prefix,w) == 1.
   Assembly: swap branches (ext), extract inv(temp_sum) by linearity,
   restate temp_sum definitionally, then inv(temp_sum)·temp_sum == 1
   (comm + inv_pos_correct). *)
Theorem real_minp_markov_kernel_normalized : forall prefix : list Token,
  real_eq (real_list_sum Token (fun w => real_minp_markov_kernel prefix w) vocab) real_one.
Proof.
  intro prefix.
  unfold real_minp_markov_kernel.
  (* 1. Swap branches pointwise: keep branch temp*inv == inv*temp (comm);
     drop branch zero == inv*zero (mult_zero backwards). *)
  apply (real_eq_trans _ (real_list_sum Token (fun w => real_mult (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                                         (match real_minp_keep_dec prefix w with
                                                          | inl _ => real_temp_factor w
                                                          | inr _ => real_zero
                                                          end)) vocab) _).
  - apply (real_list_sum_ext Token
             (fun w => match real_minp_keep_dec prefix w with
                       | inl _ => real_mult (real_temp_factor w) (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                       | inr _ => real_zero
                       end)
             (fun w => real_mult (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                 (match real_minp_keep_dec prefix w with
                                  | inl _ => real_temp_factor w
                                  | inr _ => real_zero
                                  end))
             vocab).
    intro w. destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    + apply (real_mult_comm (real_temp_factor w) (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))).
    + apply (real_eq_sym _ _ (real_mult_zero (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix)))).
  - (* 2. Extract inv(temp_sum) by linearity: sum (inv*match) == inv*sum (match). *)
    apply (real_eq_trans _ (real_mult (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                      (real_list_sum Token (fun w => match real_minp_keep_dec prefix w with
                                                               | inl _ => real_temp_factor w
                                                               | inr _ => real_zero
                                                               end) vocab)) _).
    + apply (real_list_sum_linear Token (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                  (fun w => match real_minp_keep_dec prefix w with
                                            | inl _ => real_temp_factor w
                                            | inr _ => real_zero
                                            end)
                                  vocab).
    + (* 3. Restate temp_sum definitionally, then inv(temp_sum)·temp_sum == 1
         (comm + inv_pos_correct). *)
      apply (real_eq_trans _ (real_mult (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                        (real_minp_temp_sum prefix)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                              (real_list_sum Token (fun w => match real_minp_keep_dec prefix w with
                                                                       | inl _ => real_temp_factor w
                                                                       | inr _ => real_zero
                                                                       end) vocab)
                                              (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                              (real_minp_temp_sum prefix)
                                              (real_eq_refl _) (real_eq_refl _)).
      * apply (real_eq_trans _ (real_mult (real_minp_temp_sum prefix)
                                          (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))) _).
        -- apply (real_mult_comm (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
                                 (real_minp_temp_sum prefix)).
        -- apply (real_inv_pos_correct (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix)).
Qed.

End RealMinPMain.

(* ============================================================ *)
(* B-8-6: Top-K majorization (Real-layer replica).               *)
(*   Real version of the abstract-level top_k_majorization:       *)
(*   keep_top_k s1 and not keep_top_k s2 imply f s2 <= f s1       *)
(*   (kept tokens carry weight at least that of evicted tokens —  *)
(*   an order characterization of the K heaviest).                *)
(*   Assembly: branch on real_le_dec; by contradiction (not_le_lt  *)
(*   gives lt (f s1) (f s2)), then count monotonicity             *)
(*   (count_heavier_succ_le), then a keep/drop counting           *)
(*   contradiction (NatLt both ways + Nat.ltb conversion + lia).  *)
(*   Honest interface (axiom-free): real_le_dec (decidable linear  *)
(*   order) + real_not_le_lt (linear order: Not(le) implies lt;    *)
(*   real_weak_trich is unavailable here — a strong order decision *)
(*   is required) + counting interfaces (count/monotone/keep iff). *)
(* ============================================================ *)

Section RealTopKMain.

Variable S : Type.
Variable K : nat.
Variable real_boltzmann_factor_ : S -> Real.

(* Honest interface: decidable linear order (Real layer, instantiable). *)
(* Decidable total order on the whole Real layer is equivalent to LPO and
   is therefore not instantiable constructively in this development (see
   the rLPO equivalence records, paper-7 §8); decidability holds pointwise
   at the Q layer but does not lift to this position.  The Top-K consumer
   chain takes this Variable as its linear-order source; concrete
   instances may supply it only from a computable model. *)
Variable real_le_dec : forall a b : Real, Or (real_le a b) (Not (real_le a b)).
(* Honest interface: linear order — Not (le a b) implies lt b a
   (linearity of the Cauchy reals, instantiable). *)
(* With real_le defined as Or(lt,eq) (S02_CauchyComplete), deriving
   b < a from the negative statement not (a <= b) requires extracting a
   positive separation witness from a negative statement, in the
   neighborhood of Markov/LPO principles; no proved instance exists in
   this development (the like-shaped rnot_le_lt elsewhere also sits at a
   premise position).  Locatedness of the Cauchy construction is a
   candidate supplier at the concrete layer. *)
Variable real_not_le_lt : forall a b : Real, Not (real_le a b) -> real_lt b a.
(* Honest interface: counting states heavier than f s (an enumerative count; its semantics is guaranteed by the real_le_dec instantiation). *)
Variable real_count_heavier : S -> nat.
Variable real_count_heavier_succ_le : forall (s1 s2 : S),
  real_lt (real_boltzmann_factor_ s1) (real_boltzmann_factor_ s2) ->
  (Datatypes.S (real_count_heavier s2) <= real_count_heavier s1)%nat.
(* Honest interface: the Top-K decision (a two-way Set-layer characterization of count < K, via NatLt). *)
Variable real_keep_top_k : S -> Set.
Variable real_keep_top_k_iff : forall s : S,
  And (real_keep_top_k s -> NatLt (real_count_heavier s) K)
      (NatLt (real_count_heavier s) K -> real_keep_top_k s).

(* Top-K majorization (B-8-6 main theorem): kept tokens carry weight at
   least that of evicted tokens.
   Assembly: branch on le_dec; by contradiction, not_le_lt gives
   lt (f s1) (f s2), which makes the counts contradict (lia). *)
Theorem real_top_k_majorization : forall s1 s2 : S,
  real_keep_top_k s1 -> Not (real_keep_top_k s2) ->
  real_le (real_boltzmann_factor_ s2) (real_boltzmann_factor_ s1).
Proof.
  intros s1 s2 Hk1 Hnk2.
  destruct (real_le_dec (real_boltzmann_factor_ s2) (real_boltzmann_factor_ s1)) as [Hle | Hnle].
  - exact Hle.
  - (* By contradiction: Hnle gives lt (f s1) (f s2), hence
       S(count s2) <= count s1; the keep/drop counts then contradict. *)
    assert (Hlt : real_lt (real_boltzmann_factor_ s1) (real_boltzmann_factor_ s2))
      by exact (real_not_le_lt (real_boltzmann_factor_ s2) (real_boltzmann_factor_ s1) Hnle).
    assert (Hsucc : (Datatypes.S (real_count_heavier s2) <= real_count_heavier s1)%nat)
      by exact (real_count_heavier_succ_le s1 s2 Hlt).
    assert (Hlt1 : (real_count_heavier s1 < K)%nat).
    { apply (proj1 (Nat.ltb_lt (real_count_heavier s1) K)).
      exact (match (fst (real_keep_top_k_iff s1) Hk1) in (Id _ y) return (Nat.ltb (real_count_heavier s1) K = y) with id_refl => eq_refl end). }
    assert (Hge2 : (K <= real_count_heavier s2)%nat).
    {
      apply Nat.nlt_ge. intro Hlt2.
      exact (match (Hnk2 (snd (real_keep_top_k_iff s2)
                             (match (proj2 (Nat.ltb_lt (real_count_heavier s2) K) Hlt2) in (_ = y) return (Id (Nat.ltb (real_count_heavier s2) K) y) with eq_refl => id_refl end))) with end).
    }
    exfalso. lia.
Qed.

End RealTopKMain.

(* ============================================================ *)
(* B-8-7: PPO conservativity (Real-layer replica, eps-ified).     *)
(*   Real version of the abstract-level ppo_conservative:         *)
(*   min(r, clip(r))·adv <= r·adv (min_le_l), giving ppo <= is +   *)
(*   an eps residual.  In the Real layer min only admits an eps    *)
(*   bound (real_min_le_l_eps), so the main theorem takes the      *)
(*   eps-weighted residual form (the honest-interface boundary):   *)
(*   ppo_objective <= is_objective + sum pi_old*(eps*adv).         *)
(*   Assembly: min <= rho+eps (eps bound), multiply by adv (strict *)
(*   positivity), right-distribute, multiply by pi_old (strict     *)
(*   positivity + comm restatement), lift pointwise bounds to the  *)
(*   sum (sum_le interface), finish by splitting with sum_add.     *)
(*   Honest interface (axiom-free): real_sum_over_S_le/add +       *)
(*   real_advantage_pos / real_pi_old_pos (strict positivity;      *)
(*   real_le_mult_compat requires the lt premise) + environment.   *)
(* ============================================================ *)

Section RealPPOMain.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).

Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.

(* Importance sampling ratio: r(s) := pi*(s)/pi_old(s). *)
Definition real_importance_ratio_ (s : S) : Real :=
  real_mult (real_pi_star_ s) (real_inv_pos (real_pi_old s) (real_pi_old_pos s)).

(* Clip: clip(r) := max(min(r, 1+eps), 1-eps) (the Real layer has no
   real_minus, so 1-eps is written 1+(-eps)). *)
Definition real_ppo_clip_ (r : Real) : Real :=
  real_max (real_min r (real_plus real_one epsilon)) (real_plus real_one (real_opp epsilon)).

(* PPO conservativity (B-8-7 main theorem, eps-ified):
   ppo_objective <= is_objective + sum pi_old*(eps*adv).
   Assembly: min <= rho+eps, multiply by adv, right-distribute,
   multiply by pi_old, lift to the sum by order preservation,
   split by sum_add. *)
Theorem real_ppo_conservative_eps : forall eps : Real,
  real_lt real_zero eps ->
  real_le (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                     (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))))
          (real_plus (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s))))
                     (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))).
Proof.
  intros eps Hepspos.
  (* Pointwise: min*adv <= (rho+eps)·adv == rho*adv + eps*adv, hence
     pi_old*min*adv <= pi_old*(rho*adv + eps*adv). *)
  assert (Hpt : forall s : S,
    real_le (real_mult (real_pi_old s) (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s)))
            (real_mult (real_pi_old s) (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                  (real_mult eps (real_advantage_fn s))))).
  {
    intro s.
    (* min*adv <= (rho+eps)·adv: [real_min_le_l_eps] plus multiplication
       by a strictly positive factor. *)
    assert (H1 : real_le (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))
                          (real_mult (real_plus (real_importance_ratio_ s) eps) (real_advantage_fn s))).
    {
      apply (real_le_mult_compat (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s)))
                                 (real_plus (real_importance_ratio_ s) eps)
                                 (real_advantage_fn s)).
      - exact (real_advantage_pos s).
      - exact (real_min_le_l_eps (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s)) eps Hepspos).
    }
    (* (rho+eps)·adv == rho*adv + eps*adv (chain of comm + distrib + comm). *)
    assert (Hd : real_eq (real_mult (real_plus (real_importance_ratio_ s) eps) (real_advantage_fn s))
                         (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                    (real_mult eps (real_advantage_fn s)))).
    {
      apply (real_eq_trans _ (real_mult (real_advantage_fn s) (real_plus (real_importance_ratio_ s) eps)) _).
      - apply (real_mult_comm (real_plus (real_importance_ratio_ s) eps) (real_advantage_fn s)).
      - apply (real_eq_trans _ (real_plus (real_mult (real_advantage_fn s) (real_importance_ratio_ s))
                                          (real_mult (real_advantage_fn s) eps)) _).
        + apply (real_distrib (real_advantage_fn s) (real_importance_ratio_ s) eps).
        + apply (RealSetoid.real_eq_plus_compat (real_mult (real_advantage_fn s) (real_importance_ratio_ s))
                                                (real_mult (real_advantage_fn s) eps)
                                                (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                (real_mult eps (real_advantage_fn s))
                                                (real_mult_comm (real_advantage_fn s) (real_importance_ratio_ s))
                                                (real_mult_comm (real_advantage_fn s) eps)).
    }
    (* min*adv <= rho*adv + eps*adv (restated by [real_le_id_r]). *)
    assert (H2 : real_le (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))
                         (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                    (real_mult eps (real_advantage_fn s)))).
    {
      apply (RealSetoid.real_le_id_r (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))
                                     (real_mult (real_plus (real_importance_ratio_ s) eps) (real_advantage_fn s))
                                     (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                (real_mult eps (real_advantage_fn s)))
                                     Hd H1).
    }
    (* pi_old*min*adv <= pi_old*(rho*adv + eps*adv): comm restatement
       plus multiplication by a strictly positive factor. *)
    apply (RealSetoid.real_le_id_l (real_mult (real_pi_old s) (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s)))
                        (real_mult (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s)) (real_pi_old s))
                        (real_mult (real_pi_old s) (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                              (real_mult eps (real_advantage_fn s))))).
    - apply (real_mult_comm (real_pi_old s) (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))).
    - apply (RealSetoid.real_le_id_r _ (real_mult (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                  (real_mult eps (real_advantage_fn s))) (real_pi_old s)) _).
      + apply (real_mult_comm (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                         (real_mult eps (real_advantage_fn s))) (real_pi_old s)).
      + apply (real_le_mult_compat (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))
                                   (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                              (real_mult eps (real_advantage_fn s)))
                                   (real_pi_old s)).
        * exact (real_pi_old_pos s).
        * exact H2.
  }
  (* Order preservation: lift the pointwise bound to the sum. *)
  assert (Hsum : real_le (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                                 (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))))
                         (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                                 (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                            (real_mult eps (real_advantage_fn s)))))).
  { apply real_sum_over_S_le. intro s. exact (Hpt s). }
  (* Algebra: sum pi_old*(rho*adv + eps*adv) == sum pi_old*rho*adv +
     sum pi_old*(eps*adv) (pointwise distributivity via ext + sum_add). *)
  apply (RealSetoid.real_le_id_r _ (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                                 (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                            (real_mult eps (real_advantage_fn s))))) _).
  - (* RHS restatement: sum pi_old*(rho*adv + eps*adv)
       == sum (pi_old*rho*adv + pi_old*eps*adv) == sum + sum. *)
    apply (real_eq_trans _ (real_sum_over_S (fun s => real_plus (real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s)))
                                                               (real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))) _).
    + apply (real_sum_over_S_ext
              (fun s => real_mult (real_pi_old s) (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                              (real_mult eps (real_advantage_fn s))))
              (fun s => real_plus (real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s)))
                                  (real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))).
      intro s. apply (real_distrib (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                    (real_mult eps (real_advantage_fn s))).
    + apply (real_sum_over_S_add (fun s => real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s)))
                                 (fun s => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s)))).
  - exact Hsum.
Qed.

End RealPPOMain.

(* ============================================================ *)
(* B-8-8: RLHF optimality (Real-layer replica, eps-ified).        *)
(*   Real version of the abstract-level rlhf_optimal:             *)
(*   J(pi) := -F(pi) <= J(pi_star) + D·eps (eps-weighted residual *)
(*   form — in the Real layer, KL >= 0 only admits the eps form). *)
(*   Core proof: real_kl_sum_decomp (sum p·log p == sum p·log p_b *)
(*   + sum p·kl_term: pointwise distrib + cancellation chain +    *)
(*   the kl_term_equiv interface).                                *)
(*   Assembly: the KL decomposition interface → gibbs eps         *)
(*   (0 <= sum kl + eps) → multiplication by positive D →         *)
(*   le_plus_compat (F(p_b) <= F(pi) + D·eps) → negation via opp  *)
(*   + ring identity.                                             *)
(*   Honest interface (axiom-free): real_boltzmann_log_decomp/    *)
(*   normalized (Boltzmann log decomposition/normalization) +     *)
(*   real_kl_term_equiv (log division decomposition) +            *)
(*   real_pi_star_align (pi_star == p_b) +                        *)
(*   real_gibbs_sum_eps (the sum-form KL >= 0) +                  *)
(*   real_kl_decomp_full (the constant-elimination bridge:        *)
(*   F(p) == F(p_b) + D·sum kl).                                  *)
(* ============================================================ *)

Section RealRLHFMain.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_align_r : Real.
Variable Z_align_r_pos : real_lt real_zero Z_align_r.

(* Boltzmann distribution (Real layer, aligned energy base_loss): p_b(s) := inv(Z)·e^{-e(s)/D}. *)
Definition real_boltzmann_dist_r (s : S) : Real :=
  real_mult (real_inv_pos Z_align_r Z_align_r_pos)
            (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s))).

(* Boltzmann positivity (provable: positive inverse times positive exponential). *)
Lemma real_boltzmann_dist_r_pos : forall s : S, real_lt real_zero (real_boltzmann_dist_r s).
Proof.
  intro s. unfold real_boltzmann_dist_r.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_exp_neg_pos.
Qed.

(* KL term wrapper (shortens long bracket chains). *)
Definition real_kl_sum_term (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) (s : S) : Real :=
  real_kl_term (p s) (real_boltzmann_dist_r s) (Hp s) (real_boltzmann_dist_r_pos s).

(* Honest interface: Boltzmann log decomposition log p_b == -(e/D + log Z) (instantiable in the Real layer). *)
Variable real_boltzmann_log_decomp : forall (s : S) (Hpb : real_lt real_zero (real_boltzmann_dist_r s)),
  real_eq (real_log (real_boltzmann_dist_r s) Hpb)
          (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) (real_log Z_align_r Z_align_r_pos))).
(* Honest interface: Boltzmann normalization sum p_b == 1 (instantiable in the Real layer). *)
Variable real_boltzmann_normalized :
  real_eq (real_sum_over_S real_boltzmann_dist_r) real_one.
(* Honest interface: KL term equivalence p·(log p − log p_b) == real_kl_term p p_b (log division decomposition). *)
Variable real_kl_term_equiv : forall (p : S -> Real) (Hp : forall s, real_lt real_zero (p s)) (s : S),
  real_eq (real_mult (p s) (real_plus (real_log (p s) (Hp s))
                                      (real_opp (real_log (real_boltzmann_dist_r s) (real_boltzmann_dist_r_pos s)))))
          (real_kl_sum_term p Hp s).
(* Honest interface: the pi_star closed form (declared in this Real-layer Section, in the shape of DpoPairMain's real_pi_star). *)
Variable real_pi_star_r : S -> Real.
(* Honest interface: pi_star == p_b pointwise (the aligned closed form agrees with the Boltzmann distribution). *)
Definition real_free_energy (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_plus (real_sum_over_S (fun s => real_mult (p s) (real_base_loss s)))
            (real_mult D (real_sum_over_S (fun s => real_mult (p s) (real_log (p s) (Hp s))))).

Variable real_pi_star_align : forall (s : S),
  real_eq (real_pi_star_r s) (real_boltzmann_dist_r s).
(* Honest interface: sum-form KL >= 0 + eps (the abstract-S form of real_gibbs_inequality_eps). *)
Variable real_gibbs_sum_eps : forall (p : S -> Real) (Hp : forall s, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one) (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_sum_over_S (fun s => real_kl_term (p s) (real_boltzmann_dist_r s) (Hp s) (real_boltzmann_dist_r_pos s))) eps).
(* Honest interface: free-energy KL decomposition (the constant-elimination bridge: F(p) == F(p_b) + D·sum kl). *)
Variable real_kl_decomp_full : forall (p : S -> Real) (Hp : forall s, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one),
  real_eq (real_free_energy p Hp)
          (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                     (real_mult D (real_sum_over_S (fun s => real_kl_term (p s) (real_boltzmann_dist_r s) (Hp s) (real_boltzmann_dist_r_pos s))))).

(* Entropy-side KL decomposition (B-8-8 core proof): sum p·log p == sum p·log p_b + sum p·kl_term
(* Entropy-side KL decomposition (B-8-8 core proof): sum p·log p == sum p·log p_b + sum p·kl_term
   Assembly: pointwise (log p == log p_b + (log p − log p_b) cancellation chain + distrib) →
   sum ext → sum_add → kl_term_equiv substitution *)
Theorem real_kl_sum_decomp :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S (fun s => real_mult (p s) (real_log (p s) (Hp s))))
            (real_plus (real_sum_over_S (fun s => real_mult (p s) (real_log (real_boltzmann_dist_r s) (real_boltzmann_dist_r_pos s))))
                       (real_sum_over_S (fun s => real_kl_sum_term p Hp s))).
Proof.
  intros p Hp.
  set (B := real_boltzmann_dist_r).
  set (Bpos := real_boltzmann_dist_r_pos).
  set (Lp := fun s : S => real_log (p s) (Hp s)).
  set (Lb := fun s : S => real_log (B s) (Bpos s)).
  (* 1. Pointwise: p·Lp == p·Lb + p·(Lp − Lb) (inner cancellation + distrib) *)
  assert (Hpt : forall s : S,
    real_eq (real_mult (p s) (Lp s))
            (real_plus (real_mult (p s) (Lb s))
                       (real_mult (p s) (real_plus (Lp s) (real_opp (Lb s))))))).
  {
    intro s.
    (* Inner cancellation: Lb + (Lp + (−Lb)) == Lp *)
    assert (Hin : real_eq (real_plus (Lb s) (real_plus (Lp s) (real_opp (Lb s)))) (Lp s)).
    {
      apply (real_eq_trans _ (real_plus (Lb s) (real_plus (real_opp (Lb s)) (Lp s))) _).
      - apply (RealSetoid.real_eq_plus_compat (Lb s) (real_plus (Lp s) (real_opp (Lb s)))
                                              (Lb s) (real_plus (real_opp (Lb s)) (Lp s))
                                              (real_eq_refl _) (real_plus_comm (Lp s) (real_opp (Lb s)))).
      - apply (real_eq_trans _ (real_plus (real_plus (Lb s) (real_opp (Lb s))) (Lp s)) _).
        + apply (real_plus_assoc (Lb s) (real_opp (Lb s)) (Lp s)).
        + apply (real_eq_trans _ (real_plus real_zero (Lp s)) _).
          * apply (RealSetoid.real_eq_plus_compat (real_plus (Lb s) (real_opp (Lb s))) real_zero (Lp s) (Lp s)
                                                  (real_plus_opp (Lb s)) (real_eq_refl _)).
          * apply (real_eq_trans _ _ _ (real_plus_comm real_zero (Lp s)) (real_plus_zero (Lp s))).
    }
    (* p·Lp == p·(Lb + (Lp − Lb)) == p·Lb + p·(Lp − Lb) *)
    apply (real_eq_trans _ (real_mult (p s) (real_plus (Lb s) (real_plus (Lp s) (real_opp (Lb s))))) _).
    - apply (RealSetoid.real_eq_mult_compat (p s) (Lp s) (p s) (real_plus (Lb s) (real_plus (Lp s) (real_opp (Lb s))))
                                            (real_eq_refl _) (real_eq_sym _ _ Hin)).
    - apply (real_distrib (p s) (Lb s) (real_plus (Lp s) (real_opp (Lb s)))).
  }
  (* 2. Sum side: pointwise replacement by ext → sum_add → kl_term_equiv substitution *)
  apply (real_eq_trans _ (real_sum_over_S (fun s => real_plus (real_mult (p s) (Lb s))
                                                              (real_mult (p s) (real_plus (Lp s) (real_opp (Lb s)))))) _).
  - apply (real_sum_over_S_ext (fun s => real_mult (p s) (Lp s))
                               (fun s => real_plus (real_mult (p s) (Lb s))
                                                   (real_mult (p s) (real_plus (Lp s) (real_opp (Lb s)))))).
    intro s. exact (Hpt s).
  - apply (real_eq_trans _ (real_plus (real_sum_over_S (fun s => real_mult (p s) (Lb s)))
                                      (real_sum_over_S (fun s => real_mult (p s) (real_plus (Lp s) (real_opp (Lb s)))))) _).
    + apply (real_sum_over_S_add (fun s => real_mult (p s) (Lb s))
                                 (fun s => real_mult (p s) (real_plus (Lp s) (real_opp (Lb s))))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_sum_over_S (fun s => real_mult (p s) (Lb s)))
               (real_sum_over_S (fun s => real_mult (p s) (real_plus (Lp s) (real_opp (Lb s)))))
               (real_sum_over_S (fun s => real_mult (p s) (Lb s)))
               (real_sum_over_S (fun s => real_kl_sum_term p Hp s))
               (real_eq_refl _)
               (real_sum_over_S_ext (fun s => real_mult (p s) (real_plus (Lp s) (real_opp (Lb s))))
                                    (fun s => real_kl_sum_term p Hp s))).
      intro s. exact (real_kl_term_equiv p Hp s).
Qed.
(* RLHF optimality (B-8-8 main theorem, eps-ified):
   J(pi) := -F(pi) <= J(pi_star) + D·eps (pi_star == p_b pointwise, supplied by real_pi_star_align) *)
   Assembly: KL decomposition (kl_decomp_full) → gibbs eps (0 <= sum kl + eps) → multiplication by positive D →
   le_plus_compat (F(p_b) <= F(pi) + D·eps) → negation via opp (opp_le_compat +
   ring identity: A + X <= B implies A <= B + opp(X), with X := opp(D·eps)) *)
Theorem real_rlhf_optimal_eps :
  forall (pi : S -> Real) (Hpi : forall s : S, real_lt real_zero (pi s))
    (Hnormpi : real_eq (real_sum_over_S pi) real_one) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_opp (real_free_energy pi Hpi))
            (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)) (real_mult D eps)).
Proof.
  intros pi Hpi Hnormpi eps Hepspos.
  (* 1. F(pi) == F(p_b) + D·sum kl (the decomposition). *)
  assert (Hkl : real_eq (real_free_energy pi Hpi)
                        (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                   (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))))
    by exact (real_kl_decomp_full pi Hpi Hnormpi).
  (* 2. 0 <= sum kl + eps (gibbs) implies 0 <= D·sum kl + D·eps (multiplication by positive D + distrib). *)
  assert (Hg : real_le real_zero (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps))
    by exact (real_gibbs_sum_eps pi Hpi Hnormpi eps Hepspos).
  assert (Hd : real_le real_zero (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                             (real_mult D eps))).
  {
    apply (real_le_trans real_zero
                         (real_mult D (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps))
                         (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                    (real_mult D eps))).
    - apply (real_le_trans _ (real_mult D real_zero) _).
      + apply (RealSetoid.real_eq_le real_zero (real_mult D real_zero)).
        apply (real_eq_sym _ _ (real_mult_zero D)).
      + apply (RealSetoid.real_le_id_l (real_mult D real_zero) (real_mult real_zero D)
                                       (real_mult D (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps))).
        * apply (real_mult_comm D real_zero).
        * apply (RealSetoid.real_le_id_r (real_mult real_zero D)
                                         (real_mult (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps) D)
                                         (real_mult D (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps))).
          -- apply (real_mult_comm (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps) D).
          -- apply (real_le_mult_compat real_zero (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps) D D_pos Hg).
    - apply (RealSetoid.real_eq_le (real_mult D (real_plus (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps))
                                   (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                              (real_mult D eps))).
      apply (real_distrib D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))) eps).
  }
  (* 3. F(p_b) <= F(pi) + D·eps ([real_le_plus_compat] on Hd, restated via Hkl). *)
  assert (Hf : real_le (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                       (real_plus (real_free_energy pi Hpi) (real_mult D eps))).
  {
    apply (real_le_trans _ (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                      (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                                 (real_mult D eps))) _).
    - (* F(p_b) == F(p_b) + 0 ≤ F(p_b) + (D·Σkl + D·eps) (0 ≤ D·Σkl + D·eps) *)
      apply (real_le_trans _ (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos) real_zero) _).
      + apply (RealSetoid.real_eq_le (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                          (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos) real_zero)).
        apply (real_eq_sym _ _ (real_plus_zero (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))).
      + apply (real_le_plus_compat (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                   (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                   real_zero
                                   (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                              (real_mult D eps))
                                   (real_le_refl (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))
                                   Hd).
    - (* F(p_b) + (D·sum kl + D·eps) == F(pi) + D·eps (associativity + Hkl backwards). *)
      apply (RealSetoid.real_eq_le (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                   (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                              (real_mult D eps)))
                        (real_plus (real_free_energy pi Hpi) (real_mult D eps))).
      apply (real_eq_trans _ (real_plus (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                                   (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s)))))
                                        (real_mult D eps)) _).
      + apply (real_plus_assoc (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                               (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                               (real_mult D eps)).
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                                         (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s)))))
                                              (real_mult D eps)
                                              (real_free_energy pi Hpi)
                                              (real_mult D eps)
                                              (real_eq_sym _ _ Hkl) (real_eq_refl _)).
  }
  (* 4. Negation via opp: J(pi) <= J(pi_star) + D·eps.
     A := opp(F pi), B := opp(F p_b), C := D·eps.
     Given Hf : F(p_b) <= F(pi) + C, opp(F(pi) + C) <= B (opp_le_compat).
     opp(F(pi) + C) == A + opp(C) (real_opp_plus), so A + opp(C) <= B.
     Ring identity: A == (A + opp(C)) + C, so (A + opp(C)) + C <= B + C,
     hence A <= B + C. *)
  assert (Hopp' : real_le (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps)))
                          (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))).
  {
    apply (RealSetoid.real_le_id_l (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps)))
                                   (real_opp (real_plus (real_free_energy pi Hpi) (real_mult D eps)))
                                   (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))).
    - apply (real_eq_sym _ _ (real_opp_plus (real_free_energy pi Hpi) (real_mult D eps))).
    - apply (real_opp_le_compat (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                (real_plus (real_free_energy pi Hpi) (real_mult D eps))
                                Hf).
  }
  apply (real_le_trans (real_opp (real_free_energy pi Hpi))
                       (real_plus (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps)))
                                  (real_mult D eps))
                       (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)) (real_mult D eps))).
  - (* A == (A + opp C) + C: ring identity (assoc backwards + inner comm +
       plus_opp + plus_zero). *)
    assert (Hring : real_eq (real_plus (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps))) (real_mult D eps))
                            (real_opp (real_free_energy pi Hpi))).
    {
      apply (real_eq_trans _ (real_plus (real_opp (real_free_energy pi Hpi))
                                        (real_plus (real_opp (real_mult D eps)) (real_mult D eps))) _).
      - apply (real_eq_sym _ _ (real_plus_assoc (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps)) (real_mult D eps))).
      - apply (real_eq_trans _ (real_plus (real_opp (real_free_energy pi Hpi))
                                          (real_plus (real_mult D eps) (real_opp (real_mult D eps)))) _).
        + apply (RealSetoid.real_eq_plus_compat (real_opp (real_free_energy pi Hpi))
                                                (real_plus (real_opp (real_mult D eps)) (real_mult D eps))
                                                (real_opp (real_free_energy pi Hpi))
                                                (real_plus (real_mult D eps) (real_opp (real_mult D eps)))
                                                (real_eq_refl _)
                                                (real_plus_comm (real_opp (real_mult D eps)) (real_mult D eps))).
        + apply (real_eq_trans _ (real_plus (real_opp (real_free_energy pi Hpi)) real_zero) _).
          * apply (RealSetoid.real_eq_plus_compat (real_opp (real_free_energy pi Hpi))
                                                  (real_plus (real_mult D eps) (real_opp (real_mult D eps)))
                                                  (real_opp (real_free_energy pi Hpi))
                                                  real_zero
                                                  (real_eq_refl _)
                                                  (real_plus_opp (real_mult D eps))).
          * apply (real_plus_zero (real_opp (real_free_energy pi Hpi))).
    }
    apply (RealSetoid.real_eq_le (real_opp (real_free_energy pi Hpi))
                                 (real_plus (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps))) (real_mult D eps))).
    apply (real_eq_sym _ _ Hring).
  - (* (A + opp C) + C ≤ B + C: le_plus_compat (Hopp' + refl C) *)
    apply (real_le_plus_compat (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps)))
                               (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))
                               (real_mult D eps) (real_mult D eps)
                               Hopp' (real_le_refl (real_mult D eps))).
Qed.

End RealRLHFMain.

(* ============================================================ *)

(* Real-layer differentiability argument for log: a Bishop-style per-eps replica. *)
Section LogDiffPhase4.
Section LogDiffPhase2.

(* Q layer: 0 ≤ t ≤ 1/2 implies t/(1+t) ≥ t − t² (field reasoning on Q atoms). *)
(* Q layer: 0 ≤ t ≤ 1/2 implies t−t² ≤ t/(1+t) (field reasoning, [Qle_shift_div_l]). *)
Lemma q_div_linear_ge_quad : forall t : Q, QleT' 0 t -> QleT' t (1 / 2) ->
  QleT' (t - t * t) (t / (1 + t)).
Proof.
  intros t Ht0 Ht12.
  apply Qle_to_QleT'.
  apply (Qle_shift_div_l (t - t * t) t (1 + t)).
  - (* 0 < 1+t *)
    apply (Qlt_le_trans _ 1 _).
    + unfold Qlt; simpl; lia.
    + apply (Qplus_le_compat 1 1 0 t); [apply Qle_refl | apply QleT'_to_Qle; exact Ht0].
  - (* (t−t²)(1+t) ≤ t: = t − t³ ≤ t ⟺ t³ ≥ 0 *)
    assert (Ht3 : Qle 0 (t * t * t)).
    { apply Qmult_le_0_compat; [apply Qmult_le_0_compat; apply QleT'_to_Qle; exact Ht0 | apply QleT'_to_Qle; exact Ht0]. }
    apply (Qle_trans _ (t - t * t * t) _).
    + (* (t−t²)(1+t) == t − t³ *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + (* t − t³ ≤ t − 0 *)
      apply (Qle_trans _ (t - 0) _).
      * apply (Qplus_le_compat t t (Qopp (t * t * t)) (Qopp 0)).
        -- apply Qle_refl.
        -- apply (Qopp_le_compat 0 (t * t * t)). exact Ht3.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============ 2. Real-layer log lower bound: 0 < t ≤ 1/2 implies t−t² ≤ log(1+t) ============ *)
(* Sub-lemma A: log(1+t) + log(1/(1+t)) == 0 (real_log_mult + inv_correct + log_one). *)
Lemma real_log_plus_inv_log : forall (t : Real) (Ht : real_lt real_zero t),
  let s := real_plus real_one t in
  forall (Hs : real_lt real_zero s),
  real_eq (real_plus (real_log s Hs)
                     (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs)))
          real_zero.
Proof.
  intros t Ht s Hs.
  (* log s + log (inv s) == log (s·inv s) == log 1 == 0 *)
  apply (real_eq_trans _ (real_log (real_mult s (real_inv_pos s Hs))
                                   (real_mult_positive s (real_inv_pos s Hs) Hs (real_inv_pos_pos s Hs))) _).
  - apply real_eq_sym.
    apply (real_log_mult s (real_inv_pos s Hs) Hs (real_inv_pos_pos s Hs)).
  - apply (real_eq_trans _ (real_log real_one (real_lt_zero_one)) _).
    + apply real_log_wd.
      apply (real_inv_pos_correct s Hs).
    + apply real_log_one.
Qed.

(* Sub-lemma B0: 1 − (1+t) == −t (projection-level identity, modeled on real_opp_plus). *)
Lemma real_one_minus_succ : forall (t : Real),
  real_eq (real_plus real_one (real_opp (real_plus real_one t))) (real_opp t).
Proof.
  intros t.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_opp (real_plus real_one t)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus real_one t) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one t n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj t n)).
  ring.
Qed.

(* Sub-lemma B1a: s + (−1) == t (s == 1+t; projection-level identity, modeled on
   real_one_minus_succ: real_eq_of_zero_diff + real_plus_proj/real_opp_proj + ring —
   no inv involved, so projections compute). *)
Lemma real_succ_minus_one : forall (t : Real),
  real_eq (real_plus (real_plus real_one t) (real_opp real_one)) t.
Proof.
  intros t.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus real_one t) (real_opp real_one) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one t n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
  ring.
Qed.

(* Sub-lemma B1: −t·(inv s) == inv s − 1 (s == 1+t; inv_correct: s·inv s == 1).
   Algebra-level chain (the Real layer is not a setoid here, so everything is
   assembled from explicit real_eq_trans + RealSetoid.compat steps, modeled on
   real_hpq1; real_inv_pos embeds a Qinv, so projection-level ring is
   unavailable here):
     −t·inv == −(s−1)·inv          [t == s+(−1), real_succ_minus_one]
            == −(inv·(s−1))         [mult_comm]
            == −(inv·s + inv·(−1))  [distrib]
            == −(1 + −(inv·1))      [inv·s == 1 (inv_correct+comm); inv·(−1) == −(inv·1) (opp_mult)]
            == −(1 + −inv)          [mult_one]
            == −1 + −−inv           [opp_plus]
            == −1 + inv             [opp_opp]
            == inv − 1              [plus_comm] *)
Lemma real_inv_minus_one_opp : forall (t : Real) (Ht : real_lt real_zero t),
  let s := real_plus real_one t in
  forall (Hs : real_lt real_zero s),
  real_eq (real_opp (real_mult t (real_inv_pos s Hs)))
          (real_plus (real_inv_pos s Hs) (real_opp real_one)).
Proof.
  intros t Ht s Hs.
  apply (real_eq_trans _ (real_opp (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))) _).
  { (* −t·inv == −(s−1)·inv: t == s+(−1), via mult_compat + opp_compat *)
    apply (RealSetoid.real_eq_opp_compat (real_mult t (real_inv_pos s Hs))
                                         (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))).
    apply (RealSetoid.real_eq_mult_compat t (real_inv_pos s Hs)
                                          (real_plus s (real_opp real_one)) (real_inv_pos s Hs)).
    - apply real_eq_sym. exact (real_succ_minus_one t).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_opp (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))) _).
  { (* −(s−1)·inv == −(inv·(s−1)): mult_comm *)
    apply (RealSetoid.real_eq_opp_compat (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))
                                         (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))).
    apply (real_mult_comm (real_plus s (real_opp real_one)) (real_inv_pos s Hs)). }
  apply (real_eq_trans _ (real_opp (real_plus (real_mult (real_inv_pos s Hs) s)
                                              (real_mult (real_inv_pos s Hs) (real_opp real_one)))) _).
  { (* −(inv·(s−1)) == −(inv·s + inv·(−1)): distrib *)
    apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))
                                         (real_plus (real_mult (real_inv_pos s Hs) s)
                                                    (real_mult (real_inv_pos s Hs) (real_opp real_one)))).
    apply (real_distrib (real_inv_pos s Hs) s (real_opp real_one)). }
  apply (real_eq_trans _ (real_opp (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))) _).
  { (* −(inv·s + inv·(−1)) == −(1 + −(inv·1)): inv·s == 1 (inv_correct+comm),
       inv·(−1) == −(inv·1) (opp_mult backwards). *)
    apply (RealSetoid.real_eq_opp_compat (real_plus (real_mult (real_inv_pos s Hs) s)
                                                    (real_mult (real_inv_pos s Hs) (real_opp real_one)))
                                         (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))).
    apply (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos s Hs) s)
                                          (real_mult (real_inv_pos s Hs) (real_opp real_one))
                                          real_one (real_opp (real_mult (real_inv_pos s Hs) real_one))).
    - (* inv·s == 1: comm + inv_correct *)
      apply (real_eq_trans _ (real_mult s (real_inv_pos s Hs)) _).
      + apply (real_mult_comm (real_inv_pos s Hs) s).
      + apply (real_inv_pos_correct s Hs).
    - (* inv·(−1) == −(inv·1): opp_mult backwards. *)
      apply (real_eq_sym (real_opp (real_mult (real_inv_pos s Hs) real_one))
                         (real_mult (real_inv_pos s Hs) (real_opp real_one))).
      apply (real_opp_mult (real_inv_pos s Hs) real_one). }
  apply (real_eq_trans _ (real_opp (real_plus real_one (real_opp (real_inv_pos s Hs)))) _).
  { (* −(1 + −(inv·1)) == −(1 + −inv): mult_one *)
    apply (RealSetoid.real_eq_opp_compat (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))
                                         (real_plus real_one (real_opp (real_inv_pos s Hs)))).
    apply (RealSetoid.real_eq_plus_compat real_one (real_opp (real_mult (real_inv_pos s Hs) real_one))
                                          real_one (real_opp (real_inv_pos s Hs))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos s Hs) real_one) (real_inv_pos s Hs)).
      apply (real_mult_one (real_inv_pos s Hs)). }
  apply (real_eq_trans _ (real_plus (real_opp real_one) (real_opp (real_opp (real_inv_pos s Hs)))) _).
  { (* −(1 + −inv) == −1 + −−inv: opp_plus *)
    apply (real_opp_plus real_one (real_opp (real_inv_pos s Hs))). }
  apply (real_eq_trans _ (real_plus (real_opp real_one) (real_inv_pos s Hs)) _).
  { (* −1 + −−inv == −1 + inv: opp_opp *)
    apply (RealSetoid.real_eq_plus_compat (real_opp real_one) (real_opp (real_opp (real_inv_pos s Hs)))
                                          (real_opp real_one) (real_inv_pos s Hs)).
    - apply real_eq_refl.
    - apply (real_opp_opp (real_inv_pos s Hs)). }
  { (* −1 + inv == inv − 1: plus_comm *)
    apply (real_plus_comm (real_opp real_one) (real_inv_pos s Hs)). }
Qed.

End LogDiffPhase2.

(* ============ Phase 2b: Real-layer linear bounds for log (Bishop, per eps) ============
   The Set-layer (RealInterfaceEnhanced Id form) linear bounds cannot be
   instantiated at the Real layer (the Id form is not instantiable; the Real
   layer uses the req-form RealInterfaceEnhancedSetoid), so the Real-layer
   linear bounds must be re-proved here.
   Targets: real_log_one_plus_le_eps (log(1+t) ≤ t+eps) and
   real_log_one_plus_ge_eps (t−t² ≤ log(1+t)+eps).
   Mathematics: the upper bound is real_log_le_linear_eps applied to (1+t);
   the lower bound is log(1+t) == −log(1/(1+t)) (real_log_inv_one_inv,
   backwards) + real_log_le_linear_eps on inv s + real_inv_minus_one_opp +
   t−t² ≤ t·inv s (already available at the Q layer as q_div). *)

Section LogDiffPhase2b.

(* Algebra 1: (t−t²)(1+t) == t−t³ (projection level, no inv; expand projections layer by layer + ring). *)
Lemma real_quad_prod : forall (t : Real),
  real_eq (real_mult (real_plus t (real_opp (real_mult t t)))
                     (real_plus real_one t))
          (real_plus t (real_opp (real_mult t (real_mult t t)))).
Proof.
  intros t.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus t (real_opp (real_mult t t))) (real_plus real_one t) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj t (real_opp (real_mult t t)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult t t) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one t n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj t (real_opp (real_mult t (real_mult t t))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult t (real_mult t t)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj t (real_mult t t) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
  ring.
Qed.

(* Algebra 2: 0 < t implies t³ ≥ 0 (le_mult_compat, twice). *)
Lemma real_cube_nonneg : forall (t : Real),
  real_lt real_zero t -> real_le real_zero (real_mult t (real_mult t t)).
Proof.
  intros t Ht.
  (* First 0 ≤ t·t: 0·t ≤ t·t (le_mult_compat on 0≤t with t>0). *)
  assert (Hsq : real_le real_zero (real_mult t t)).
  {
    apply (real_le_trans real_zero (real_mult real_zero t) (real_mult t t)).
    - apply RealSetoid.real_eq_le.
      apply (real_eq_trans real_zero (real_mult t real_zero) (real_mult real_zero t)).
      + apply real_eq_sym. apply (real_mult_zero t).
      + apply real_mult_comm.
    - apply (real_le_mult_compat real_zero t t Ht).
      apply (RealSetoid.real_lt_le_iff_req real_zero t). left. exact Ht.
  }
  (* Then 0 ≤ t·(t·t): 0·t ≤ (t·t)·t (le_mult_compat on 0≤t·t with t>0). *)
  apply (real_le_trans real_zero (real_mult real_zero t) (real_mult t (real_mult t t))).
  - apply RealSetoid.real_eq_le.
    apply (real_eq_trans real_zero (real_mult t real_zero) (real_mult real_zero t)).
    + apply real_eq_sym. apply (real_mult_zero t).
    + apply real_mult_comm.
  - apply (real_le_trans (real_mult real_zero t) (real_mult (real_mult t t) t) (real_mult t (real_mult t t))).
    + apply (real_le_mult_compat real_zero (real_mult t t) t Ht). exact Hsq.
    + apply RealSetoid.real_eq_le.
      apply (real_eq_trans (real_mult (real_mult t t) t) (real_mult t (real_mult t t)) (real_mult t (real_mult t t))).
      * apply real_mult_comm.
      * apply real_eq_refl.
Qed.

(* Algebra 3: 0 < t implies t−t³ ≤ t (t³≥0 gives −t³≤0, hence t+(−t³) ≤ t+0). *)
Lemma real_minus_cube_le : forall (t : Real),
  real_lt real_zero t ->
  real_le (real_plus t (real_opp (real_mult t (real_mult t t)))) t.
Proof.
  intros t Ht.
  apply (real_le_trans (real_plus t (real_opp (real_mult t (real_mult t t))))
                       (real_plus t real_zero) t).
  - apply (real_le_plus_compat t t (real_opp (real_mult t (real_mult t t))) real_zero).
    + apply real_le_refl.
    + (* −t³ ≤ 0: 0 ≤ t³ gives −t³ ≤ −0 == 0. *)
      apply (real_le_trans (real_opp (real_mult t (real_mult t t))) (real_opp real_zero) real_zero).
      * apply (real_opp_le_compat real_zero (real_mult t (real_mult t t))).
        exact (real_cube_nonneg t Ht).
      * apply RealSetoid.real_eq_le. apply real_opp_zero.
  - apply RealSetoid.real_eq_le. apply real_plus_zero.
Qed.

(* Algebra 4: 0 < t and 0 < 1+t imply t−t² ≤ t·inv(1+t).
   (t−t²)(1+t) == t−t³ ≤ t [real_quad_prod + real_minus_cube_le];
   le_mult_compat by the positive inv s gives (t−t²)·s·inv s ≤ t·inv s;
   the left side restates as (t−t²)·(s·inv s) == t−t²
   [assoc backwards + inv_correct + mult_one]. *)
Lemma real_quad_div_ge : forall (t : Real),
  real_lt real_zero t ->
  forall (Hs : real_lt real_zero (real_plus real_one t)),
  real_le (real_plus t (real_opp (real_mult t t)))
          (real_mult t (real_inv_pos (real_plus real_one t) Hs)).
Proof.
  intros t Ht Hs.
  set (s := real_plus real_one t).
  (* Core: (t−t²)·s ≤ t. *)
  assert (Hcore : real_le (real_mult (real_plus t (real_opp (real_mult t t))) s) t).
  {
    apply (real_le_trans (real_mult (real_plus t (real_opp (real_mult t t))) s)
                         (real_plus t (real_opp (real_mult t (real_mult t t)))) t).
    - apply RealSetoid.real_eq_le. apply (real_quad_prod t).
    - apply (real_minus_cube_le t). exact Ht.
  }
  (* Multiply Hcore by the positive inv s: le_mult_compat. *)
  pose proof (real_le_mult_compat (real_mult (real_plus t (real_opp (real_mult t t))) s) t
                                  (real_inv_pos s Hs)
                                  (real_inv_pos_pos s Hs) Hcore) as Hstep.
  (* Left side restated: (A·s)·inv s == A. *)
  apply (real_le_trans (real_plus t (real_opp (real_mult t t)))
                       (real_mult (real_mult (real_plus t (real_opp (real_mult t t))) s)
                                  (real_inv_pos s Hs))
                       (real_mult t (real_inv_pos s Hs))).
  - apply RealSetoid.real_eq_le.
    (* A == A·(s·inv s) == (A·s)·inv s. *)
    apply (real_eq_trans (real_plus t (real_opp (real_mult t t)))
                         (real_mult (real_plus t (real_opp (real_mult t t)))
                                    (real_mult s (real_inv_pos s Hs)))
                         (real_mult (real_mult (real_plus t (real_opp (real_mult t t))) s)
                                    (real_inv_pos s Hs))).
    + apply (real_eq_trans (real_plus t (real_opp (real_mult t t)))
                           (real_mult (real_plus t (real_opp (real_mult t t))) real_one)
                           (real_mult (real_plus t (real_opp (real_mult t t)))
                                      (real_mult s (real_inv_pos s Hs)))).
      * apply real_eq_sym. apply (real_mult_one (real_plus t (real_opp (real_mult t t)))).
      * apply (RealSetoid.real_eq_mult_compat (real_plus t (real_opp (real_mult t t))) real_one
                                              (real_plus t (real_opp (real_mult t t)))
                                              (real_mult s (real_inv_pos s Hs))).
        -- apply real_eq_refl.
        -- apply real_eq_sym. apply (real_inv_pos_correct s Hs).
    + exact (real_mult_assoc (real_plus t (real_opp (real_mult t t))) s
                             (real_inv_pos s Hs)).
  - exact Hstep.
Qed.

(* ============ 5. Real-layer linear bounds for log (Bishop, per eps) ============ *)
(* Upper bound: 0 < 1+t and 0 < eps imply log(1+t) ≤ t + eps.
   real_log_le_linear_eps applied to (1+t): log(1+t) ≤ ((1+t)+(−1)) + eps == t + eps
   (real_succ_minus_one: (1+t)+(−1) == t). *)
Lemma real_log_one_plus_le_eps : forall (t eps : Real),
  forall (Hs : real_lt real_zero (real_plus real_one t)),
  real_lt real_zero eps ->
  real_le (real_log (real_plus real_one t) Hs)
          (real_plus t eps).
Proof.
  intros t eps Hs Heps.
  apply (real_le_trans (real_log (real_plus real_one t) Hs)
                       (real_plus (real_plus (real_plus real_one t) (real_opp real_one)) eps)
                       (real_plus t eps)).
  - exact (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_plus real_one t) eps Hs Heps).
  - apply RealSetoid.real_eq_le.
    apply (RealSetoid.real_eq_plus_compat (real_plus (real_plus real_one t) (real_opp real_one))
                                          eps
                                          t eps).
    + exact (real_succ_minus_one t).
    + apply real_eq_refl.
Qed.

(* Lower bound: 0 < t, 0 < 1+t, 0 < eps imply t−t² ≤ log(1+t) + eps.
   Chain: t−t² ≤ t·inv s                [real_quad_div_ge]
       t·inv s == opp (minus (inv s) one)   [real_inv_minus_one_opp backwards + opp_opp]
       opp (minus (inv s) one) ≤ opp (log (inv s)) + eps'   [real_log_le_linear_eps on inv s + opp_le_compat]
       opp (log (inv s)) == log s    [real_log_inv_one_inv backwards + opp_opp]
       hence t−t² ≤ log s + eps          [assembled; eps' := eps]. *)
Lemma real_log_one_plus_ge_eps : forall (t eps : Real),
  forall (Ht : real_lt real_zero t),
  forall (Hs : real_lt real_zero (real_plus real_one t)),
  real_lt real_zero eps ->
  real_le (real_plus t (real_opp (real_mult t t)))
          (real_plus (real_log (real_plus real_one t) Hs) eps).
Proof.
  intros t eps Ht Hs Heps.
  (* Throughout, use the delta-equality form of s := real_plus real_one t
     (matching the lemma's let-bound unfolding); avoid set variables to keep
     the statement shapes from splitting. *)
  (* Segment 1: t−t² ≤ t·inv s. *)
  pose proof (real_quad_div_ge t Ht Hs) as Hseg1.
  (* Segment 2a: t·inv s == opp (minus (inv s) one).
       real_inv_minus_one_opp t Ht Hs : opp (t·inv s) == inv s + (−1)
       negate both sides and apply opp_opp, giving t·inv s == opp (inv s + (−1)). *)
  pose proof (real_inv_minus_one_opp t Ht Hs) as Himpo.
  (* t·inv s == opp (opp (t·inv s)) [real_opp_opp backwards]
             == opp (inv s + (−1)) [real_eq_opp_compat on Himpo]. *)
  pose proof (real_eq_trans (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                            (real_opp (real_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs))))
                            (real_opp (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)))
                            (real_eq_sym (real_opp (real_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs))))
                                         (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                         (real_opp_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs))))
                            (RealSetoid.real_eq_opp_compat (real_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs)))
                                                           (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one))
                                                           Himpo)) as Hio.
  (* Segment 2b: log (inv s) ≤ (inv s + (−1)) + eps (real_log_le_linear_eps on inv s). *)
  pose proof (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_inv_pos (real_plus real_one t) Hs) eps
                                     (real_inv_pos_pos (real_plus real_one t) Hs) Heps) as Hlin.
  (* Segment 2c: opp ((inv s + (−1)) + eps) ≤ opp (log (inv s)) (opp_le_compat). *)
  pose proof (real_opp_le_compat (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs))
                                 (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps)
                                 Hlin) as Hoc.
  (* Segment 2d: opp (log (inv s)) == log s (real_log_inv_one_inv backwards + opp_opp). *)
  pose proof (real_log_inv_one_inv (real_plus real_one t) Hs (real_inv_pos_pos (real_plus real_one t) Hs)) as Hli.
  pose proof (real_eq_trans (real_opp (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs)))
                            (real_opp (real_opp (real_log (real_plus real_one t) Hs)))
                            (real_log (real_plus real_one t) Hs)
                            (RealSetoid.real_eq_opp_compat (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs))
                                                           (real_opp (real_log (real_plus real_one t) Hs))
                                                           Hli)
                            (real_opp_opp (real_log (real_plus real_one t) Hs))) as Hol.
  (* Segment 2e: le (t·inv s) (log s + eps).
       t·inv s == opp (inv s + (−1)) == opp ((inv s + (−1)) + eps) + eps;
       opp ((inv s + (−1)) + eps) ≤ opp (log (inv s)) == log s;
       hence assemble. *)
  (* First: opp ((inv s + (−1)) + eps) == opp (inv s + (−1)) + opp eps (opp_plus). *)
  pose proof (real_opp_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps) as Hop.
  (* Assembly: real_le (plus (mult t (inv s)) (opp eps)) (log s) by restating via Hoc + Hio + Hop. *)
  assert (Hmid : real_le (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps))
                         (real_log (real_plus real_one t) Hs)).
  {
    (* Goal: t·inv s + (−eps) ≤ log s.
       Chain: t·inv s + (−eps) == opp(inv s + (−1)) + (−eps)   [Hio]
           == opp((inv s + (−1)) + eps)                     [Hop backwards + eq]
           ≤ opp (log (inv s)) == log s                      [Hoc + Hol]. *)
    apply (real_le_trans (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps))
                         (real_opp (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps))
                         (real_log (real_plus real_one t) Hs)).
    - apply RealSetoid.real_eq_le.
      (* t·inv s + (−eps) == opp ((inv s + (−1)) + eps). *)
      apply (real_eq_trans (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps))
                           (real_plus (real_opp (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)))
                                      (real_opp eps))
                           (real_opp (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps))).
      + apply (RealSetoid.real_eq_plus_compat (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                              (real_opp eps)
                                              (real_opp (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)))
                                              (real_opp eps)).
        * exact (real_eq_sym (real_opp (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)))
                             (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                             (real_eq_sym (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                          (real_opp (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)))
                                          Hio)).
        * apply real_eq_refl.
      + apply real_eq_sym. apply (real_opp_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps).
    - (* opp ((inv s + (−1)) + eps) ≤ opp (log (inv s)) == log s. *)
      apply (real_le_trans (real_opp (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps))
                           (real_opp (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs)))
                           (real_log (real_plus real_one t) Hs)).
      + exact Hoc.
      + apply RealSetoid.real_eq_le. exact Hol.
  }
  (* Final: t−t² ≤ t·inv s ≤ log s + eps (add eps to both sides of Hmid). *)
  apply (real_le_trans (real_plus t (real_opp (real_mult t t)))
                       (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                       (real_plus (real_log (real_plus real_one t) Hs) eps)).
  - exact Hseg1.
  - (* t·inv s ≤ log s + eps: add eps to both sides of Hmid (t·inv s + (−eps) ≤ log s). *)
    apply (real_le_trans (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                         (real_plus (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps)) eps)
                         (real_plus (real_log (real_plus real_one t) Hs) eps)).
    + apply RealSetoid.real_eq_le.
      (* t·inv s == (t·inv s + (−eps)) + eps. *)
      apply (real_eq_trans (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                           (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) real_zero)
                           (real_plus (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps)) eps)).
      * apply real_eq_sym. apply (real_plus_zero (real_mult t (real_inv_pos (real_plus real_one t) Hs))).
      * apply real_eq_sym.
        apply (real_eq_trans (real_plus (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps)) eps)
                             (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                        (real_plus (real_opp eps) eps))
                             (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) real_zero)).
        -- apply real_eq_sym.
           apply (real_plus_assoc (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps) eps).
        -- apply (RealSetoid.real_eq_plus_compat (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                                 (real_plus (real_opp eps) eps)
                                                 (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                                 real_zero).
           ++ apply real_eq_refl.
           ++ apply (real_eq_trans (real_plus (real_opp eps) eps)
                                   (real_plus eps (real_opp eps))
                                   real_zero).
              ** apply real_plus_comm.
              ** apply (real_plus_opp eps).
    + apply (real_le_plus_compat (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps))
                                  (real_log (real_plus real_one t) Hs) eps eps).
      * exact Hmid.
      * apply real_le_refl.
Qed.

(* ============ 6. Real-layer log_div: log(a/b) == log a − log b ============
   Chain: log(a·inv b) == log a + log(inv b) [real_log_mult]
                     == log a + opp (log b) [real_log_inv_one_inv]. *)
Lemma real_log_div : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_log (real_mult a (real_inv_pos b Hb))
                    (real_mult_positive a (real_inv_pos b Hb) Ha (real_inv_pos_pos b Hb)))
          (real_plus (real_log a Ha) (real_opp (real_log b Hb))).
Proof.
  intros a b Ha Hb.
  apply (real_eq_trans (real_log (real_mult a (real_inv_pos b Hb))
                                 (real_mult_positive a (real_inv_pos b Hb) Ha (real_inv_pos_pos b Hb)))
                       (real_plus (real_log a Ha)
                                  (real_log (real_inv_pos b Hb) (real_inv_pos_pos b Hb)))
                       (real_plus (real_log a Ha) (real_opp (real_log b Hb)))).
  - exact (real_log_mult a (real_inv_pos b Hb) Ha (real_inv_pos_pos b Hb)).
  - apply (RealSetoid.real_eq_plus_compat (real_log a Ha)
                                          (real_log (real_inv_pos b Hb) (real_inv_pos_pos b Hb))
                                          (real_log a Ha)
                                          (real_opp (real_log b Hb))).
    + apply real_eq_refl.
    + exact (real_log_inv_one_inv b Hb (real_inv_pos_pos b Hb)).
Qed.

(* ============ 7. Algebraic identity: (x+h)·inv x == 1 + h·inv x ============
   Chain: (x+h)·inv x == x·inv x + h·inv x [distrib]
                   == 1 + h·inv x      [inv_correct]. *)
Lemma real_succ_mult_inv : forall (x h : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult (real_plus x h) (real_inv_pos x Hx))
          (real_plus real_one (real_mult h (real_inv_pos x Hx))).
Proof.
  intros x h Hx.
  (* (x+h)·inv == inv·(x+h) [mult_comm]
               == inv·x + inv·h [real_distrib]
               == x·inv + h·inv [mult_comm ×2]
               == 1 + h·inv [inv_correct + plus_compat] *)
  apply (real_eq_trans (real_mult (real_plus x h) (real_inv_pos x Hx))
                       (real_plus (real_mult (real_inv_pos x Hx) x)
                                  (real_mult (real_inv_pos x Hx) h))
                       (real_plus real_one (real_mult h (real_inv_pos x Hx)))).
  - (* (x+h)·inv == inv·x + inv·h: mult_comm + distrib *)
    apply (real_eq_trans (real_mult (real_plus x h) (real_inv_pos x Hx))
                         (real_mult (real_inv_pos x Hx) (real_plus x h))
                         (real_plus (real_mult (real_inv_pos x Hx) x)
                                    (real_mult (real_inv_pos x Hx) h))).
    + apply (real_mult_comm (real_plus x h) (real_inv_pos x Hx)).
    + apply (real_distrib (real_inv_pos x Hx) x h).
  - (* inv·x + inv·h == x·inv + h·inv == 1 + h·inv *)
    apply (real_eq_trans (real_plus (real_mult (real_inv_pos x Hx) x)
                                    (real_mult (real_inv_pos x Hx) h))
                         (real_plus (real_mult x (real_inv_pos x Hx))
                                    (real_mult h (real_inv_pos x Hx)))
                         (real_plus real_one (real_mult h (real_inv_pos x Hx)))).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos x Hx) x)
                                            (real_mult (real_inv_pos x Hx) h)
                                            (real_mult x (real_inv_pos x Hx))
                                            (real_mult h (real_inv_pos x Hx))).
      * apply (real_mult_comm (real_inv_pos x Hx) x).
      * apply (real_mult_comm (real_inv_pos x Hx) h).
    + apply (RealSetoid.real_eq_plus_compat (real_mult x (real_inv_pos x Hx))
                                            (real_mult h (real_inv_pos x Hx))
                                            real_one
                                            (real_mult h (real_inv_pos x Hx))).
      * exact (real_inv_pos_correct x Hx).
      * apply real_eq_refl.
Qed.

(* ============ 8. Real-layer differentiability record (Bishop per-eps, with a positivity premise) ============
   Unlike the Set-layer Differentiable (whose df_correct is universally
   quantified over x), the Real-layer log carries a positivity premise, so
   differentiability is only required at positive x (the universally
   quantified form is not provable at the abstract interface; this Real
   layer takes the per-eps Bishop replica route).
   Bishop form (since real_le = Or lt eq cannot express "non-strict and not
   approaching"): the error is ≤ eps·|h| + eps' for any eps' > 0 (a Bishop
   margin eps' on top of the main bound eps).  This lets the main-theorem
   assembly use the Bishop linear bounds; the precise-form argument would
   additionally require the deep non-Bishop route, which the Bishop form
   avoids. *)
Record RealDifferentiable (f : forall x : Real, real_lt real_zero x -> Real) : Set := {
  rdf : forall x : Real, real_lt real_zero x -> Real;
  rdf_correct : forall (x : Real) (Hx : real_lt real_zero x),
    forall (eps : Real), real_lt real_zero eps ->
    sigT (fun delta : Real =>
      And (real_lt real_zero delta)
          (forall h : Real, real_lt (real_abs h) delta ->
            forall (Hxh : real_lt real_zero (real_plus x h)),
            forall (eps' : Real), real_lt real_zero eps' ->
            real_le (real_abs (real_plus (f (real_plus x h) Hxh)
                                         (real_opp (real_plus (f x Hx) (real_mult (rdf x Hx) h)))))
                    (real_plus (real_mult eps (real_abs h)) eps')))
}.

End LogDiffPhase2b.

(* ============ 9. Main-theorem core identity: log(x+h) − log x == log(1 + h·inv x) ============
   Chain: log(x+h) − log x == log((x+h)·inv x)  [real_log_div]
                     == log(1 + h·inv x)     [real_succ_mult_inv restatement + real_log_wd].
   Positivity proofs (Ht : 0 < 1+h/x, Hxh : 0 < x+h) are supplied by the
   caller (derived in the main theorem from |h| < x/2). *)
Lemma real_log_plus_diff : forall (x h : Real) (Hx : real_lt real_zero x)
  (Hxh : real_lt real_zero (real_plus x h))
  (Ht : real_lt real_zero (real_plus real_one (real_mult h (real_inv_pos x Hx)))),
  real_eq (real_plus (real_log (real_plus x h) Hxh)
                     (real_opp (real_log x Hx)))
          (real_log (real_plus real_one (real_mult h (real_inv_pos x Hx))) Ht).
Proof.
  intros x h Hx Hxh Ht.
  apply (real_eq_trans (real_plus (real_log (real_plus x h) Hxh)
                                  (real_opp (real_log x Hx)))
                       (real_log (real_mult (real_plus x h) (real_inv_pos x Hx))
                                 (real_mult_positive (real_plus x h) (real_inv_pos x Hx) Hxh (real_inv_pos_pos x Hx)))
                       (real_log (real_plus real_one (real_mult h (real_inv_pos x Hx))) Ht)).
  - exact (real_eq_sym (real_log (real_mult (real_plus x h) (real_inv_pos x Hx))
                                 (real_mult_positive (real_plus x h) (real_inv_pos x Hx) Hxh (real_inv_pos_pos x Hx)))
                       (real_plus (real_log (real_plus x h) Hxh)
                                  (real_opp (real_log x Hx)))
                       (real_log_div (real_plus x h) x Hxh Hx)).
  - apply (real_log_wd (real_mult (real_plus x h) (real_inv_pos x Hx))
                       (real_plus real_one (real_mult h (real_inv_pos x Hx)))
                       (real_mult_positive (real_plus x h) (real_inv_pos x Hx) Hxh (real_inv_pos_pos x Hx))
                       Ht).
    exact (real_succ_mult_inv x h Hx).
Qed.

(* ============ 10. Positivity lemma family (the main theorem's delta argument) ============ *)
(* Q-layer auxiliary: −x ≤ |x| (q_neg_le_abs is not visible from the main file, proved here). *)
Lemma q_neg_le_abs_local : forall x : Q, QleT' (- x) (Qabs x).
Proof.
  intros x.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (- x)) _).
  - apply Qle_Qabs.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
Qed.

(* 10a. |h| < e implies −e < h (lower bound of abs, pointwise q_neg_le_abs: −|h_n| ≤ h_n).
   Mathematics: h ≥ −|h| > −e gives −e < h. *)
Lemma real_abs_lt_lower : forall (h e : Real),
  real_lt (real_abs h) e ->
  real_lt (real_opp e) h.
Proof.
  intros h e Hhe.
  destruct Hhe as [e0 [He0 [N0 HN0]]].
  exists e0.
  split.
  - exact He0.
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hpt_abs : projT1 (real_abs h) n == Qabs (projT1 h n)).
    { apply qeqT_imp_qeq; apply real_abs_proj. }
    assert (Hpt_opp : projT1 (real_opp e) n == - projT1 e n).
    { apply qeqT_imp_qeq; apply real_opp_proj. }
    assert (Hq : Qlt e0 (projT1 e n - projT1 (real_abs h) n)).
    { apply QltT_to_Qlt. exact (HN0 n Hn). }
    assert (Hle : Qle (projT1 e n - projT1 (real_abs h) n) (projT1 e n + projT1 h n)).
    {
      apply (Qplus_le_compat (projT1 e n) (projT1 e n) (Qopp (projT1 (real_abs h) n)) (projT1 h n)).
      - apply Qle_refl.
      - (* −|h_n| ≤ h_n: q_neg_le_abs_local at h_n, restated via
           projT1 (real_abs h) n == Qabs (h_n). *)
        apply (Qle_trans (Qopp (projT1 (real_abs h) n)) (Qopp (Qabs (projT1 h n))) (projT1 h n)).
        + (* −(real_abs h)_n == −Qabs (h_n): Qeq restatement. *)
          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qopp_comp (projT1 (real_abs h) n) (Qabs (projT1 h n))).
          exact (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        + (* −Qabs (h_n) ≤ h_n: Qopp_le_compat on q_neg_le_abs_local + opp_opp. *)
          apply (Qle_trans (Qopp (Qabs (projT1 h n))) (Qopp (Qopp (projT1 h n))) (projT1 h n)).
          * apply (Qopp_le_compat (Qopp (projT1 h n)) (Qabs (projT1 h n))).
            apply (Qle_trans (Qopp (projT1 h n)) (Qabs (Qopp (projT1 h n))) (Qabs (projT1 h n))).
            -- apply Qle_Qabs.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qopp_involutive.
    }
    (* Goal: e0 < h_n − (opp e)_n. Chain: e0 < e_n − |h_n| ≤ e_n + h_n ≤ h_n − (opp e)_n
       (Hq + Hle + restatement: h_n + e_n == h_n − (opp e)_n, since (opp e)_n == −e_n). *)
    apply (Qlt_le_trans e0 (projT1 e n + projT1 h n) (projT1 h n - projT1 (real_opp e) n)).
    + apply (Qlt_le_trans e0 (projT1 e n - projT1 (real_abs h) n) (projT1 e n + projT1 h n)).
      * exact Hq.
      * exact Hle.
    + (* e_n + h_n ≤ h_n − (opp e)_n: h_n + e_n == h_n + (−(opp e)_n) (Hpt_opp) and comm. *)
      apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      apply (Qeq_trans (projT1 e n + projT1 h n) (projT1 h n + projT1 e n)
                       (projT1 h n - projT1 (real_opp e) n)).
      * apply Qplus_comm.
      * (* h_n + e_n == h_n − (opp e)_n: (opp e)_n == −e_n (Hpt_opp), setoid restatement + ring. *)
        setoid_rewrite Hpt_opp. ring.
Qed.

(* 10b. 0 < x and |h| < x/2 imply 0 < x+h.
   Chain: |h| < x·inv2 < x (inv2 < 1, 0 < x) gives |h| < x (real_lt_trans)
       gives −x < h (real_abs_lt_lower) gives x+(−x) < x+h (real_lt_plus_compat_le_lt)
       gives 0 < x+h (real_eq_lt_lt: x+(−x) == 0). *)
(* Auxiliary: inv 1 == 1 (inv_correct: 1·inv 1 == 1 gives inv 1 == 1·inv 1 == 1). *)
Lemma real_inv_one : real_eq (real_inv_pos real_one (real_lt_zero_one)) real_one.
Proof.
  apply (real_eq_trans (real_inv_pos real_one (real_lt_zero_one))
                       (real_mult real_one (real_inv_pos real_one (real_lt_zero_one)))
                       real_one).
  - apply (real_eq_trans (real_inv_pos real_one (real_lt_zero_one))
                         (real_mult (real_inv_pos real_one (real_lt_zero_one)) real_one)
                         (real_mult real_one (real_inv_pos real_one (real_lt_zero_one)))).
    + apply real_eq_sym. apply (real_mult_one (real_inv_pos real_one (real_lt_zero_one))).
    + apply (real_mult_comm (real_inv_pos real_one (real_lt_zero_one)) real_one).
  - apply (real_inv_pos_correct real_one (real_lt_zero_one)).
Qed.

(* Auxiliary: inv 2 < 1 (real_inv_pos_lt_contra on 1 < 2 + inv 1 == 1). *)
Lemma real_two_pos_local : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus real_one real_one)).
  - apply real_eq_sym. apply (real_plus_zero real_zero).
  - apply (real_lt_plus_compat real_zero real_one real_zero real_one
                               (real_lt_zero_one) (real_lt_zero_one)).
Qed.

Lemma real_inv_two_lt_one : real_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one.
Proof.
  (* real_lt_eq_lt (inv2) (inv1) one: lt (inv2) (inv1) (inv_lt_contra on 1<2) + eq (inv1) one. *)
  apply (real_lt_eq_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                       (real_inv_pos real_one (real_lt_zero_one))
                       real_one).
  - apply (real_inv_pos_lt_contra real_one (real_plus real_one real_one)
                                  (real_lt_zero_one) (real_two_pos_local)).
    (* 1 < 2: 1+0 < 1+1 (lt_plus_compat_le_lt: le 1 1 + lt 0 1), then bridge 1+0 == 1. *)
    apply (real_eq_lt_lt real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    + apply real_eq_sym. apply (real_plus_zero real_one).
    + apply (real_lt_plus_compat_le_lt real_one real_one real_zero real_one
                                       (real_le_refl real_one) (real_lt_zero_one)).
  - apply real_inv_one.
Qed.

(* Auxiliary: 0 < x implies x·inv2 < x (mult_lt_compat_l: inv2 < 1, 0 < x). *)
Lemma real_half_lt_self : forall (x : Real) (Hx : real_lt real_zero x),
  real_lt (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x) x.
Proof.
  intros x Hx.
  (* Chain: inv2·x == x·inv2 (comm) < x·1 == x (mult_lt_compat_l: inv2<1, 0<x). *)
  apply (real_eq_lt_lt (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                       (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                       x).
  - apply (real_mult_comm (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x).
  - (* x·inv2 < x: real_lt_eq_lt (x·inv2) (x·1) x: lt (mult_lt_compat_l)+ eq (mult_one) *)
    apply (real_lt_eq_lt (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                         (real_mult x real_one)
                         x).
    + (* x·inv2 < x·1: mult_lt_compat_l (c:=x, a:=inv2, b:=1) *)
      apply (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                   real_one x).
      * exact real_inv_two_lt_one.
      * exact Hx.
    + apply (real_mult_one x).
Qed.

Lemma real_plus_pos_half : forall (x h : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h) (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x) ->
  real_lt real_zero (real_plus x h).
Proof.
  intros x h Hx Hh.
  (* Segment 1: |h| < x (via |h| < x·inv2 < x). *)
  assert (Hhx : real_lt (real_abs h) x).
  { apply (real_lt_trans (real_abs h)
                         (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                         x).
    - exact Hh.
    - exact (real_half_lt_self x Hx). }
  (* Segment 2: −x < h (real_abs_lt_lower). *)
  pose proof (real_abs_lt_lower h x Hhx) as Hlower.
  (* Segment 3: x+(−x) < x+h (lt_plus_compat_le_lt: le x x + lt (−x) h). *)
  apply (real_eq_lt_lt real_zero (real_plus x (real_opp x)) (real_plus x h)).
  - apply real_eq_sym. apply (real_plus_opp x).
  - apply (real_lt_plus_compat_le_lt x x (real_opp x) h).
    + apply real_le_refl.
    + exact Hlower.
Qed.

(* ============ 11. Main-theorem auxiliary lemmas ============ *)
(* 11a. 0 < x implies |h·inv x| == |h|·inv x (abs_mult + abs_pos on inv x). *)
Lemma real_abs_mult_inv : forall (x h : Real) (Hx : real_lt real_zero x),
  real_eq (real_abs (real_mult h (real_inv_pos x Hx)))
          (real_mult (real_abs h) (real_inv_pos x Hx)).
Proof.
  intros x h Hx.
  apply (real_eq_trans (real_abs (real_mult h (real_inv_pos x Hx)))
                       (real_mult (real_abs h) (real_abs (real_inv_pos x Hx)))
                       (real_mult (real_abs h) (real_inv_pos x Hx))).
  - apply (real_abs_mult_req h (real_inv_pos x Hx)).
  - apply (RealSetoid.real_eq_mult_compat (real_abs h) (real_abs (real_inv_pos x Hx))
                                          (real_abs h) (real_inv_pos x Hx)).
    + apply real_eq_refl.
    + apply (real_abs_pos_req (real_inv_pos x Hx)). apply (real_inv_pos_pos x Hx).
Qed.

(* ============ 12. |h| < x implies x+h > 0 (a direct variant of real_plus_pos_half, for the delta argument) ============
   Chain: |h| < x gives −x < h (real_abs_lt_lower), gives x+(−x) < x+h (lt_plus_compat_le_lt)
       gives 0 < x+h (real_eq_lt_lt: x+(−x) == 0). *)
Lemma real_plus_pos : forall (x h : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h) x ->
  real_lt real_zero (real_plus x h).
Proof.
  intros x h Hx Hh.
  pose proof (real_abs_lt_lower h x Hh) as Hlower.
  apply (real_eq_lt_lt real_zero (real_plus x (real_opp x)) (real_plus x h)).
  - apply real_eq_sym. apply (real_plus_opp x).
  - apply (real_lt_plus_compat_le_lt x x (real_opp x) h).
    + apply real_le_refl.
    + exact Hlower.
Qed.

(* ============ 13. 1 + h·inv x > 0 (for |h| < x; the 1+t > 1−1 == 0 side argument) ============
   Mathematics: t := h·inv x with |t| < 1 (|h| < x gives |h|·inv x < x·inv x == 1)
        gives 1+t > 1−|t| > 0.  Apply real_abs_lt_lower with e := 1: −1 < t gives 1+(−1) < 1+t. *)
Lemma real_one_plus_t_pos : forall (x h : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h) x ->
  real_lt real_zero (real_plus real_one (real_mult h (real_inv_pos x Hx))).
Proof.
  intros x h Hx Hh.
  (* Segment 1: |h·inv x| < 1: |h| < x with inv x > 0 gives |h|·inv x < x·inv x == 1
     (|h·inv x| == |h|·inv x by real_abs_mult_inv). *)
  assert (Ht1 : real_lt (real_abs (real_mult h (real_inv_pos x Hx))) real_one).
  {
    (* |h·inv x| == |h|·inv x < x·inv x == 1 *)
    apply (real_eq_lt_lt (real_abs (real_mult h (real_inv_pos x Hx)))
                         (real_mult (real_abs h) (real_inv_pos x Hx))
                         real_one).
    - apply (real_abs_mult_inv x h Hx).
    - (* |h|·inv x < x·inv x == 1: mult_lt_compat_l on (|h|, x, inv x) + commuting the factors. *)
      apply (real_lt_eq_lt (real_mult (real_abs h) (real_inv_pos x Hx))
                           (real_mult x (real_inv_pos x Hx))
                           real_one).
      + (* |h|·inv x < x·inv x: |h|·inv x == inv x·|h| < inv x·x == x·inv x *)
        apply (real_eq_lt_lt (real_mult (real_abs h) (real_inv_pos x Hx))
                             (real_mult (real_inv_pos x Hx) (real_abs h))
                             (real_mult x (real_inv_pos x Hx))).
        * apply (real_mult_comm (real_abs h) (real_inv_pos x Hx)).
        * apply (real_lt_eq_lt (real_mult (real_inv_pos x Hx) (real_abs h))
                               (real_mult (real_inv_pos x Hx) x)
                               (real_mult x (real_inv_pos x Hx))).
          -- apply (real_mult_lt_compat_l (real_abs h) x (real_inv_pos x Hx)).
             ++ exact Hh.
             ++ apply (real_inv_pos_pos x Hx).
          -- apply real_mult_comm.
      + apply (real_inv_pos_correct x Hx).
  }
  (* Segment 2: −1 < h·inv x (real_abs_lt_lower with e := 1). *)
  pose proof (real_abs_lt_lower (real_mult h (real_inv_pos x Hx)) real_one Ht1) as Hlower.
  (* Segment 3: 1+(−1) < 1+t (lt_plus_compat_le_lt: le 1 1 + lt (−1) t), hence 0 < 1+t. *)
  apply (real_eq_lt_lt real_zero (real_plus real_one (real_opp real_one))
                       (real_plus real_one (real_mult h (real_inv_pos x Hx)))).
  - apply (real_plus_opp real_one).
  - apply (real_lt_plus_compat_le_lt real_one real_one (real_opp real_one)
                                     (real_mult h (real_inv_pos x Hx))).
    + apply real_le_refl.
    + exact Hlower.
Qed.

(* ============ 14. Main-theorem delta-argument auxiliaries ============ *)
(* 14a. |h| < min A B implies |h| < A + eps (min_le_l_eps on eps + lt_le_trans). *)
Lemma real_min_abs_lt_l : forall (h A B eps : Real),
  real_lt real_zero eps ->
  real_lt (real_abs h) (real_min A B) ->
  real_lt (real_abs h) (real_plus A eps).
Proof.
  intros h A B eps Heps Hh.
  apply (real_lt_le_trans (real_abs h) (real_min A B) (real_plus A eps)).
  - exact Hh.
  - exact (real_min_le_l_eps A B eps Heps).
Qed.

(* 14b. Symmetric: |h| < min A B implies |h| < B + eps. *)
Lemma real_min_abs_lt_r : forall (h A B eps : Real),
  real_lt real_zero eps ->
  real_lt (real_abs h) (real_min A B) ->
  real_lt (real_abs h) (real_plus B eps).
Proof.
  intros h A B eps Heps Hh.
  apply (real_lt_le_trans (real_abs h) (real_min A B) (real_plus B eps)).
  - exact Hh.
  - exact (real_min_le_r_eps A B eps Heps).
Qed.

(* 14c. 0 < x implies 3x/4 < x (x·(3/4) < x·1 with 3/4 < 1; the route 3/4 :=
   1/2+1/4 simplifies: 3x/4 == x/2 + x/4, and x/2 + x/4 < x follows from
   x/2 < x and x/4 < x/2 — real_half_lt_self applied twice.
   The main theorem only needs x/2 + x/4 < x: x/2 < x (half_lt_self) and
   x/4 ≤ x/2 needs 1/4 ≤ 1/2 (inv2 composed with itself). *)

(* ============ 15. Delta-argument core identity: inv2·x + inv2·x == x ============
   Chain: inv2·x + inv2·x == (inv2+inv2)·x [distrib backwards]
                      == 1·x == x        [2·inv2 == 1: inv2+inv2 == 1 (2 by definition)]
   2·inv2 == 1 is inv_pos_correct (1+1); inv2+inv2 == 2·inv2 needs 2 == 1+1
   (definition) + mult_one. *)
Lemma real_half_plus_half : forall (x : Real),
  real_eq (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                     (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x))
          x.
Proof.
  intros x.
  (* inv2·x + inv2·x == (inv2+inv2)·x [distrib backwards: a·x + b·x == (a+b)·x]
                  == (2·inv2)·x == 1·x == x [inv_correct: (1+1)·inv2 == 1]. *)
  apply (real_eq_trans (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                                  (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x))
                       (real_mult (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                             (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) x)
                       x).
  - (* inv2·x + inv2·x == (inv2+inv2)·x: right distributivity via comm + distrib:
        inv2·x == x·inv2 (comm); (inv2+inv2)·x == x·(inv2+inv2) (comm)
        == x·inv2 + x·inv2 (distrib) == inv2·x + inv2·x (comm twice). *)
    apply (real_eq_trans (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                                    (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x))
                         (real_plus (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                                    (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))))
                         (real_mult (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                               (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) x)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                                            (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                                            (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                                            (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))).
      * apply (real_mult_comm (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x).
      * apply (real_mult_comm (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x).
    + apply (real_eq_trans (real_plus (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                                      (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))))
                           (real_mult x (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                   (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))))
                           (real_mult (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                 (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) x)).
      * apply real_eq_sym.
        apply (real_distrib x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                             (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))).
      * apply (real_mult_comm x (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                           (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))).
  - (* (inv2+inv2)·x == 1·x == x: inv2+inv2 == 1 from inv_pos_correct (2·inv2 == 1)
        with 2 == 1+1.
        inv_pos_correct (plus one one) : (1+1)·inv2 == 1; a comm step is needed:
        no — inv_pos_correct directly gives mult (plus one one)
        (inv_pos (plus one one) ...) == one.
        (inv2+inv2)·x == 1·x needs inv2+inv2 == 1: from 2·inv2 == 1, 2 == 1+1,
        and comm: (1+1)·inv2 == 1, so inv2·(1+1) == 1 (comm), and
        inv2+inv2 == inv2·(1+1) (distrib backwards: inv2·1+inv2·1 == inv2·(1+1),
        with inv2+inv2 == inv2·1+inv2·1 by mult_one twice), hence inv2+inv2 == 1. *)
    apply (real_eq_trans (real_mult (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) x)
                         (real_mult real_one x)
                         x).
    + apply (RealSetoid.real_eq_mult_compat (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                        (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                                            x real_one x).
      * (* inv2 + inv2 == 1: inv2·1 + inv2·1 == inv2·(1+1) == 2·inv2 == 1 *)
        apply (real_eq_trans (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                        (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                             (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one)
                                        (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one))
                             real_one).
        -- apply (RealSetoid.real_eq_plus_compat (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                 (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                 (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one)
                                                 (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one)).
           ++ apply real_eq_sym. apply (real_mult_one (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))).
           ++ apply real_eq_sym. apply (real_mult_one (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))).
        -- apply (real_eq_trans (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one)
                                           (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one))
                                (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                           (real_plus real_one real_one))
                                real_one).
           ++ apply real_eq_sym. apply (real_distrib (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one real_one).
           ++ (* inv2·(1+1) == 1: comm + inv_pos_correct *)
              apply (real_eq_trans (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                              (real_plus real_one real_one))
                                   (real_mult (real_plus real_one real_one)
                                              (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                                   real_one).
              ** apply (real_mult_comm (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                       (real_plus real_one real_one)).
              ** apply (real_inv_pos_correct (real_plus real_one real_one) (real_two_pos_local)).
      * apply real_eq_refl.
    + apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
      * apply (real_mult_comm real_one x).
      * apply (real_mult_one x).
Qed.

(* ============ 16. t² ≥ 0 (pointwise Qmult_le_0_compat; needed by the main theorem's quad_bound etc.) ============ *)

(* Bishop form: 0 ≤ t² + eps (any eps > 0; non-strict-but-approaching becomes the Bishop margin). *)
Lemma real_square_nonneg_eps : forall (t eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_mult t t) eps).
Proof.
  intros t eps Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req real_zero (real_plus (real_mult t t) eps)). left.
  unfold real_lt.
  exists eps0.
  split.
  - exact Heps0.
  - exists N0.
    intros n Hn.
    (* Pointwise: t_n² + eps_n > eps0 (eps_n > eps0 and t_n² ≥ 0). *)
    assert (Hpt : projT1 (real_mult t t) n == projT1 t n * projT1 t n) by (apply qeqT_imp_qeq; apply real_mult_proj).
    assert (Hpt_eps : projT1 (real_plus (real_mult t t) eps) n == projT1 (real_mult t t) n + projT1 eps n)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    (* Q-layer square nonnegativity (Qsquare_nonneg, from the development's Q layer). *)
    assert (Hs : Qle 0 (projT1 t n * projT1 t n)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg (projT1 t n))).
    (* eps_n > eps0 (HN0 is in difference form: QltT eps0 (eps_n − 0)). *)
    assert (Hn0 : Qlt eps0 (projT1 eps n)).
    { apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n Hn).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hz. ring. }
    (* Goal: QltT eps0 (P − 0) with P := projT1 (real_plus (real_mult t t) eps) n; a pure Qeq chain. *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (projT1 (real_mult t t) n + projT1 eps n) _).
    { (* eps0 < projT1(real_mult t t) n + eps_n *)
      apply (Qlt_le_trans _ (projT1 eps n) _).
      { exact Hn0. }
      { (* eps_n <= projT1(real_mult t t) n + eps_n *)
        apply (Qle_trans _ (0 + projT1 eps n) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qplus_le_compat 0 (projT1 (real_mult t t) n) (projT1 eps n) (projT1 eps n)).
          { (* 0 <= projT1(real_mult t t) n (via t_n²). *)
            apply (Qle_trans _ (projT1 t n * projT1 t n) _).
            { exact Hs. }
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hpt. } }
          { apply Qle_refl. } } } }
    { (* projT1(real_mult t t) n + eps_n <= P − projT1 real_zero n *)
      apply (Qle_trans _ (projT1 (real_plus (real_mult t t) eps) n) _).
      { (* projT1(real_mult t t) n + eps_n <= P *)
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        apply (Qeq_trans _ (projT1 (real_mult t t) n + projT1 eps n) _).
        { reflexivity. }
        { apply Qeq_sym. exact Hpt_eps. } }
      { (* P <= P − 0 *)
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hz. ring. } }
Qed.

(* ============ 17. Main-theorem lower-bound chain (t<0 side route, sign-free: t − log(1+t) ≤ t²/(1+t) + eps) ============ *)

(* 17a: real_inv_minus_one_opp without the Ht premise (the original carries 0 < t
   but never uses it in its proof; the t<0 side needs the Ht-free form). *)
Lemma real_inv_minus_one_opp_noHt : forall (t : Real),
  let s := real_plus real_one t in
  forall (Hs : real_lt real_zero s),
  real_eq (real_opp (real_mult t (real_inv_pos s Hs)))
          (real_plus (real_inv_pos s Hs) (real_opp real_one)).
Proof.
  intros t s Hs.
  apply (real_eq_trans _ (real_opp (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))) _).
  { apply (RealSetoid.real_eq_opp_compat (real_mult t (real_inv_pos s Hs))
                                         (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))).
    apply (RealSetoid.real_eq_mult_compat t (real_inv_pos s Hs)
                                          (real_plus s (real_opp real_one)) (real_inv_pos s Hs)).
    - apply real_eq_sym. exact (real_succ_minus_one t).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_opp (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))) _).
  { apply (RealSetoid.real_eq_opp_compat (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))
                                         (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))).
    apply (real_mult_comm (real_plus s (real_opp real_one)) (real_inv_pos s Hs)). }
  apply (real_eq_trans _ (real_opp (real_plus (real_mult (real_inv_pos s Hs) s)
                                              (real_mult (real_inv_pos s Hs) (real_opp real_one)))) _).
  { apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))
                                         (real_plus (real_mult (real_inv_pos s Hs) s)
                                                    (real_mult (real_inv_pos s Hs) (real_opp real_one)))).
    apply (real_distrib (real_inv_pos s Hs) s (real_opp real_one)). }
  apply (real_eq_trans _ (real_opp (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))) _).
  { apply (RealSetoid.real_eq_opp_compat (real_plus (real_mult (real_inv_pos s Hs) s)
                                                    (real_mult (real_inv_pos s Hs) (real_opp real_one)))
                                         (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))).
    apply (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos s Hs) s)
                                          (real_mult (real_inv_pos s Hs) (real_opp real_one))
                                          real_one (real_opp (real_mult (real_inv_pos s Hs) real_one))).
    - apply (real_eq_trans _ (real_mult s (real_inv_pos s Hs)) _).
      + apply (real_mult_comm (real_inv_pos s Hs) s).
      + apply (real_inv_pos_correct s Hs).
    - apply (real_eq_sym (real_opp (real_mult (real_inv_pos s Hs) real_one))
                         (real_mult (real_inv_pos s Hs) (real_opp real_one))).
      apply (real_opp_mult (real_inv_pos s Hs) real_one). }
  apply (real_eq_trans _ (real_opp (real_plus real_one (real_opp (real_inv_pos s Hs)))) _).
  { apply (RealSetoid.real_eq_opp_compat (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))
                                         (real_plus real_one (real_opp (real_inv_pos s Hs)))).
    apply (RealSetoid.real_eq_plus_compat real_one (real_opp (real_mult (real_inv_pos s Hs) real_one))
                                          real_one (real_opp (real_inv_pos s Hs))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos s Hs) real_one) (real_inv_pos s Hs)).
      apply (real_mult_one (real_inv_pos s Hs)). }
  apply (real_eq_trans _ (real_plus (real_opp real_one) (real_opp (real_opp (real_inv_pos s Hs)))) _).
  { apply (real_opp_plus real_one (real_opp (real_inv_pos s Hs))). }
  apply (real_eq_trans _ (real_plus (real_opp real_one) (real_inv_pos s Hs)) _).
  { apply (RealSetoid.real_eq_plus_compat (real_opp real_one) (real_opp (real_opp (real_inv_pos s Hs)))
                                          (real_opp real_one) (real_inv_pos s Hs)).
    - apply real_eq_refl.
    - apply (real_opp_opp (real_inv_pos s Hs)). }
  { apply (real_plus_comm (real_opp real_one) (real_inv_pos s Hs)). }
Qed.

(* 17b: algebraic identity t + (inv s − 1) == t²·inv s (no Ht; explicit Real-layer chain). *)
Lemma real_t_plus_inv_minus_one : forall (t : Real),
  let s := real_plus real_one t in
  forall (Hs : real_lt real_zero s),
  real_eq (real_plus t (real_plus (real_inv_pos s Hs) (real_opp real_one)))
          (real_mult (real_mult t t) (real_inv_pos s Hs)).
Proof.
  intros t s Hs.
  (* Segment 1: t + (inv s − 1) == t + opp(t·inv s) (real_inv_minus_one_opp_noHt backwards). *)
  apply (real_eq_trans _ (real_plus t (real_opp (real_mult t (real_inv_pos s Hs)))) _).
  - apply (RealSetoid.real_eq_plus_compat t (real_plus (real_inv_pos s Hs) (real_opp real_one))
                                        t (real_opp (real_mult t (real_inv_pos s Hs)))).
    + apply real_eq_refl.
    + apply real_eq_sym. exact (real_inv_minus_one_opp_noHt t Hs).
  - (* Segment 2: t + opp(t·inv s) == t²·inv s. *)
    apply (real_eq_trans _ (real_plus (real_mult t real_one) (real_mult t (real_opp (real_inv_pos s Hs)))) _).
    + (* t + opp(t·inv s) == t·1 + t·opp(inv s) *)
      apply (RealSetoid.real_eq_plus_compat t (real_opp (real_mult t (real_inv_pos s Hs)))
                                            (real_mult t real_one) (real_mult t (real_opp (real_inv_pos s Hs)))).
      * apply real_eq_sym. exact (real_mult_one t).
      * exact (real_opp_mult t (real_inv_pos s Hs)).
    + (* t·1 + t·opp(inv s) == t²·inv s *)
      apply (real_eq_trans _ (real_mult t (real_plus real_one (real_opp (real_inv_pos s Hs)))) _).
      * apply real_eq_sym. exact (real_distrib t real_one (real_opp (real_inv_pos s Hs))).
      * (* t·(1 − inv s) == t²·inv s *)
        apply (real_eq_trans _ (real_mult t (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))) _).
        { (* t·(1 − inv) == t·((s−1)·inv): the inner identity 1 − inv == (s−1)·inv. *)
          apply (RealSetoid.real_eq_mult_compat t (real_plus real_one (real_opp (real_inv_pos s Hs)))
                                                t (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))).
          { apply real_eq_refl. }
          { (* 1 + opp(inv s) == (s + (−1))·inv s *)
            apply (real_eq_trans _ (real_plus (real_mult s (real_inv_pos s Hs))
                                              (real_opp (real_mult (real_inv_pos s Hs) real_one))) _).
            { (* 1 + opp(inv) == s·inv s + opp(inv·1) *)
              apply (RealSetoid.real_eq_plus_compat real_one (real_opp (real_inv_pos s Hs))
                                                    (real_mult s (real_inv_pos s Hs))
                                                    (real_opp (real_mult (real_inv_pos s Hs) real_one))).
              { apply real_eq_sym. exact (real_inv_pos_correct s Hs). }
              { apply (RealSetoid.real_eq_opp_compat (real_inv_pos s Hs)
                                                     (real_mult (real_inv_pos s Hs) real_one)).
                apply real_eq_sym. exact (real_mult_one (real_inv_pos s Hs)). } }
            { (* s·inv s + opp(inv·1) == (s + (−1))·inv s *)
              apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos s Hs) s)
                                                (real_mult (real_inv_pos s Hs) (real_opp real_one))) _).
              { (* s·inv + opp(inv·1) == inv·s + inv·(−1) *)
                apply (RealSetoid.real_eq_plus_compat (real_mult s (real_inv_pos s Hs))
                                                      (real_opp (real_mult (real_inv_pos s Hs) real_one))
                                                      (real_mult (real_inv_pos s Hs) s)
                                                      (real_mult (real_inv_pos s Hs) (real_opp real_one))).
                { apply (real_mult_comm s (real_inv_pos s Hs)). }
                { exact (real_opp_mult (real_inv_pos s Hs) real_one). } }
              { (* inv·s + inv·(−1) == (s + (−1))·inv s *)
                apply (real_eq_trans _ (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one))) _).
                { apply real_eq_sym. exact (real_distrib (real_inv_pos s Hs) s (real_opp real_one)). }
                { apply (real_mult_comm (real_inv_pos s Hs) (real_plus s (real_opp real_one))). } } } } }
        { (* t·((s−1)·inv s) == (t·t)·inv s *)
          apply (real_eq_trans _ (real_mult t (real_mult t (real_inv_pos s Hs))) _).
          { (* t·((s−1)·inv s) == t·(t·inv s) *)
            apply (RealSetoid.real_eq_mult_compat t (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))
                                                  t (real_mult t (real_inv_pos s Hs))).
            { apply real_eq_refl. }
            { apply (RealSetoid.real_eq_mult_compat (real_plus s (real_opp real_one)) (real_inv_pos s Hs)
                                                    t (real_inv_pos s Hs)).
              { exact (real_succ_minus_one t). }
              { apply real_eq_refl. } } }
          { (* t·(t·inv s) == (t·t)·inv s *)
            apply (real_mult_assoc t t (real_inv_pos s Hs)). } }
Qed.

(* 17c: t − log(1+t) ≤ t²·inv(1+t) + eps (sign-free; s := 1+t, requiring 0 < s).
   Chain: t − log s == t + log(inv s)                    [real_log_inv_one_inv backwards + eq_le]
        ≤ t + ((inv s − 1) + eps)                     [le_linear on inv s + le_plus_compat]
        == t²·inv s + eps                             [real_t_plus_inv_minus_one + assoc] *)
Lemma real_t_minus_log_bound : forall (t eps : Real)
  (Hs : real_lt real_zero (real_plus real_one t)),
  real_lt real_zero eps ->
  real_le (real_plus t (real_opp (real_log (real_plus real_one t) Hs)))
          (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Hs)) eps).
Proof.
  intros t eps Hs Heps.
  set (s := real_plus real_one t).
  apply (real_le_trans _ (real_plus t (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs))) _).
  - (* t − log s ≤ t + log(inv s): eq_le (log(inv s) == opp(log s), backwards). *)
    apply (RealSetoid.real_eq_le (real_plus t (real_opp (real_log s Hs)))
                                 (real_plus t (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs)))).
    apply (RealSetoid.real_eq_plus_compat t (real_opp (real_log s Hs))
                                          t (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs))).
    + apply real_eq_refl.
    + apply real_eq_sym. exact (real_log_inv_one_inv s Hs (real_inv_pos_pos s Hs)).
  - apply (real_le_trans _ (real_plus t (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps)) _).
    + (* t + log(inv s) ≤ t + ((inv s − 1) + eps): le_plus_compat. *)
      apply (real_le_plus_compat t t
                                 (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs))
                                 (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps)).
      * apply real_le_refl.
      * exact (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_inv_pos s Hs) eps
                                                (real_inv_pos_pos s Hs) Heps).
    + (* t + ((inv s − 1) + eps) ≤ t²·inv s + eps: eq_le (assoc + real_t_plus_inv_minus_one). *)
      apply (RealSetoid.real_eq_le (real_plus t (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps))
                                   (real_plus (real_mult (real_mult t t) (real_inv_pos s Hs)) eps)).
      apply (real_eq_trans (real_plus t (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps))
                           (real_plus (real_plus t (real_plus (real_inv_pos s Hs) (real_opp real_one))) eps)
                           (real_plus (real_mult (real_mult t t) (real_inv_pos s Hs)) eps)).
      * (* assoc: t + (X + eps) == (t + X) + eps (real_plus_assoc, X := inv s + (−1)). *)
        apply (real_plus_assoc t (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps).
      * (* (t + X) + eps == t²·inv s + eps. *)
        apply (RealSetoid.real_eq_plus_compat (real_plus t (real_plus (real_inv_pos s Hs) (real_opp real_one)))
                                              eps
                                              (real_mult (real_mult t t) (real_inv_pos s Hs))
                                              eps).
        -- exact (real_t_plus_inv_minus_one t Hs).
        -- apply real_eq_refl.
Qed.

(* ============ 18. Scaling: t²·inv s ≤ t²·2 + eps (needs 1/2 < s; pointwise Q layer) ============
   Closes the main theorem's lower-bound chain: t²/(1+t) ≤ 2t².
   Real layer: real_inv_pos (real_plus real_one real_one) (real_two_pos_local) < s
   gives inv s < inv real_inv_pos (real_plus real_one real_one) (real_two_pos_local) == 2
   (strictly, avoiding a pointwise stall in the real_le eq branch).
   Pointwise: t²·inv s ≤ t²·2 + eps (invs ≤ 2 pointwise + t² ≥ 0 by Qsquare_nonneg + witness eps0). *)
Lemma real_quad_div_le_two_eps : forall (t s eps : Real)
  (Hs : real_lt real_zero s)
  (Hs12 : real_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) s)
  (Heps : real_lt real_zero eps),
  real_le (real_mult (real_mult t t) (real_inv_pos s Hs))
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps).
Proof.
  intros t s eps Hs Hs12 Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  (* inv s < 2: real_inv_pos (real_plus real_one real_one) (real_two_pos_local) < s gives inv s < inv real_inv_pos (real_plus real_one real_one) (real_two_pos_local) == 2 (strict, Real layer). *)
  assert (Hinv2lt : real_lt (real_inv_pos s Hs) (real_plus real_one real_one)).
  { apply (real_lt_eq_lt (real_inv_pos s Hs)
                         (real_inv_pos (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                       (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)))
                         (real_plus real_one real_one)).
    - apply (real_inv_pos_lt_contra (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) s
                                    (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)) Hs
                                    Hs12).
    - apply (real_inv_inv (real_plus real_one real_one) (real_two_pos_local)). }
  destruct Hinv2lt as [e2 [He2 [N2b HN2b]]].
  destruct Hs12 as [e [He [N12 HN12]]].
  destruct s as [us Hus].
  destruct Hs as [eps1 [Heps1 [Ns HNs]]].
  apply (RealSetoid.real_lt_le_iff_req _ _). left.
  unfold real_lt.
  exists eps0.
  split.
  - exact Heps0.
  - exists (Nat.max N0 (Nat.max Ns (Nat.max N12 N2b))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hns : (Ns <= n)%nat) by lia.
    assert (Hn12 : (N12 <= n)%nat) by lia.
    assert (Hn2b : (N2b <= n)%nat) by lia.
    set (tn := projT1 t n).
    set (p2 := projT1 (real_plus real_one real_one) n).
    set (en := projT1 eps n).
    set (I := real_inv_pos (existT (fun u : Qseq => cauchy u) us Hus)
         (existT (fun eps0 : Q => And (QltT 0 eps0) {N0 : nat & forall n0 : nat, NatLe N0 n0 -> QltT eps0 (projT1 (existT (fun u : Qseq => cauchy u) us Hus) n0 - projT1 real_zero n0)})
                 eps1 (Heps1, existT (fun N0 : nat => forall n0 : nat, NatLe N0 n0 -> QltT eps1 (projT1 (existT (fun u : Qseq => cauchy u) us Hus) n0 - projT1 real_zero n0)) Ns HNs))).
    set (qn := projT1 (real_mult (real_mult t t) I) n).
    set (pn := projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps) n).
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    (* eps0 < en (the HN0 difference bridge). *)
    assert (Hepsn : Qlt eps0 en).
    { unfold en. apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    (* invs projection reduction (n ≥ Ns): projT1 I n == Qinv (us n). *)
    assert (Hinvs : projT1 I n == Qinv (us n)).
    { unfold I. cbn [real_inv_pos projT1].
      assert (Hl : Nat.leb Ns n = true) by (apply Nat.leb_le; exact Hns).
      rewrite Hl. reflexivity. }
    (* 0 ≤ p2 − invs (HN2b: e2 < p2 − invs) *)
    assert (Hpnz : Qle 0 (p2 - projT1 I n)).
    { unfold p2. apply (Qle_trans _ e2 _).
      - apply Qlt_le_weak. apply QltT_to_Qlt. exact He2.
      - apply Qlt_le_weak. apply QltT_to_Qlt.
        unfold I. exact (HN2b n (NatLe_lift _ _ Hn2b)). }
    (* tn² ≥ 0 *)
    assert (Hsq : Qle 0 (tn * tn)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg tn)).
    (* Projection unfolding: qn == (tn·tn)·projT1 I n and pn == (tn·tn)·p2 + en. *)
    assert (Hqn : qn == (tn * tn) * projT1 I n).
    { unfold qn, tn.
      apply (Qeq_trans _ (projT1 (real_mult t t) n * projT1 I n) _).
      - exact (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) I n)).
      - apply (Qmult_comp (projT1 (real_mult t t) n) (tn * tn) (qeqT_imp_qeq _ _ (real_mult_proj t t n))
                          (projT1 I n) (projT1 I n) (Qeq_refl _)). }
    assert (Hpn : pn == (tn * tn) * p2 + en).
    { unfold pn, tn, p2, en.
      apply (Qeq_trans _ (projT1 (real_mult (real_mult t t) (real_plus real_one real_one)) n + projT1 eps n) _).
      - exact (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) eps n)).
      - apply (Qplus_comp (projT1 (real_mult (real_mult t t) (real_plus real_one real_one)) n)
                          ((tn * tn) * p2)
                          (Qeq_trans (projT1 (real_mult (real_mult t t) (real_plus real_one real_one)) n)
                                     (projT1 (real_mult t t) n * projT1 (real_plus real_one real_one) n)
                                     ((tn * tn) * p2)
                                     (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n))
                                     (Qmult_comp (projT1 (real_mult t t) n) (tn * tn) (qeqT_imp_qeq _ _ (real_mult_proj t t n))
                                                 (projT1 (real_plus real_one real_one) n) p2 (Qeq_refl _)))
                          (projT1 eps n) en (Qeq_refl (projT1 eps n))). }
    (* Main chain: QltT eps0 (pn − qn): eps0 < en ≤ tn·tn·(p2−invs) + en == pn − qn. *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ en _).
    { exact Hepsn. }
    { (* en ≤ pn − qn *)
      apply (Qle_trans _ (tn * tn * (p2 - projT1 I n) + en) _).
      { (* en ≤ tn·tn·(p2−invs) + en: the nonnegative term (via commuting en + y). *)
        apply (Qle_trans _ (en + tn * tn * (p2 - projT1 I n)) _).
        { apply (Qle_plus_nonneg_r en (tn * tn * (p2 - projT1 I n))).
          apply (Qmult_le_0_compat (tn * tn) (p2 - projT1 I n)).
          { exact Hsq. }
          { exact Hpnz. } }
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. } }
      { (* tn·tn·(p2−invs) + en ≤ pn − qn: Qeq bridge. *)
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        apply (Qeq_trans _ ((tn * tn) * p2 + en - (tn * tn) * projT1 I n) _).
        { (* Subgoal 1: tn·tn·(p2−invs) + en == (tn·tn·p2+en) − tn·tn·invs: ring. *)
          unfold Qminus. ring. }
        { (* Subgoal 2: (tn·tn·p2+en) − tn·tn·invs == pn − qn (Qplus_comp backwards). *)
          apply Qeq_sym.
          apply (Qplus_comp pn ((tn * tn) * p2 + en) Hpn
                            (Qopp qn) (Qopp ((tn * tn) * projT1 I n))).
          apply (Qopp_comp qn ((tn * tn) * projT1 I n)). exact Hqn. } } }
Qed.

(* ============ 19. Main-theorem assembly components: strict min splitting + the |t|<1/2 chain + algebra ============ *)

(* 19a: |h| < min A B implies |h| < A (strictly; pointwise: e < min_n − |h|_n ≤ A_n − |h|_n). *)
Lemma real_min_lt_l : forall (h A B : Real),
  real_lt (real_abs h) (real_min A B) ->
  real_lt (real_abs h) A.
Proof.
  intros h A B Hhmin.
  destruct Hhmin as [e [He [N HN]]].
  unfold real_lt.
  exists e.
  split.
  - exact He.
  - exists N.
    intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (projT1 (real_min A B) n - projT1 (real_abs h) n) _).
    + apply QltT_to_Qlt. exact (HN n Hn).
    + apply (Qle_trans _ (Qmin (projT1 A n) (projT1 B n) - projT1 (real_abs h) n) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qplus_comp (projT1 (real_min A B) n) (Qmin (projT1 A n) (projT1 B n))
                          (qeqT_imp_qeq _ _ (real_min_proj A B n))
                          (Qopp (projT1 (real_abs h) n)) (Qopp (projT1 (real_abs h) n))
                          (Qeq_refl _)).
      * apply (Qplus_le_compat (Qmin (projT1 A n) (projT1 B n)) (projT1 A n)
                               (Qopp (projT1 (real_abs h) n)) (Qopp (projT1 (real_abs h) n))).
        -- apply Q.le_min_l.
        -- apply Qle_refl.
Qed.

(* 19b: |h| < min A B implies |h| < B (strictly, by symmetry). *)
Lemma real_min_lt_r : forall (h A B : Real),
  real_lt (real_abs h) (real_min A B) ->
  real_lt (real_abs h) B.
Proof.
  intros h A B Hhmin.
  destruct Hhmin as [e [He [N HN]]].
  unfold real_lt.
  exists e.
  split.
  - exact He.
  - exists N.
    intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (projT1 (real_min A B) n - projT1 (real_abs h) n) _).
    + apply QltT_to_Qlt. exact (HN n Hn).
    + apply (Qle_trans _ (Qmin (projT1 A n) (projT1 B n) - projT1 (real_abs h) n) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qplus_comp (projT1 (real_min A B) n) (Qmin (projT1 A n) (projT1 B n))
                          (qeqT_imp_qeq _ _ (real_min_proj A B n))
                          (Qopp (projT1 (real_abs h) n)) (Qopp (projT1 (real_abs h) n))
                          (Qeq_refl _)).
      * apply (Qplus_le_compat (Qmin (projT1 A n) (projT1 B n)) (projT1 B n)
                               (Qopp (projT1 (real_abs h) n)) (Qopp (projT1 (real_abs h) n))).
        -- apply Q.le_min_r.
        -- apply Qle_refl.
Qed.

(* 19c: algebraic identity (inv2·x)·inv x == inv2 (x > 0). *)
Lemma real_half_x_mult_inv : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                     (real_inv_pos x Hx))
          (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
Proof.
  intros x Hx.
  apply (real_eq_trans (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                                  (real_inv_pos x Hx))
                       (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                  (real_mult x (real_inv_pos x Hx)))
                       (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))).
  - apply real_eq_sym.
    apply (real_mult_assoc (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x (real_inv_pos x Hx)).
  - apply (real_eq_trans (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                    (real_mult x (real_inv_pos x Hx)))
                         (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one)
                         (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))).
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                            (real_mult x (real_inv_pos x Hx))
                                            (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                            real_one).
      * apply real_eq_refl.
      * exact (real_inv_pos_correct x Hx).
    + apply (real_mult_one (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))).
Qed.

(* 19d: −inv2 < t implies inv2 < 1+t (assembling half+half == 1: 1+t == half+(half+t)). *)
Lemma real_half_lt_one_plus_t : forall (t : Real),
  real_lt (real_opp (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) t ->
  real_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) (real_plus real_one t).
Proof.
  intros t Ht.
  set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  (* Segment 1: 0 < half + t (−half < t plus half on both sides: (−half)+half < t+half, bridged by zero == (−half)+half). *)
  assert (Hhalf_t : real_lt real_zero (real_plus half t)).
  { apply (real_eq_lt_lt real_zero (real_plus (real_opp half) half) (real_plus half t)).
    - apply real_eq_sym.
      apply (real_eq_trans (real_plus (real_opp half) half) (real_plus half (real_opp half)) real_zero).
      + apply (real_plus_comm (real_opp half) half).
      + apply (real_plus_opp half).
    - apply (real_lt_eq_lt (real_plus (real_opp half) half) (real_plus t half) (real_plus half t)).
      + apply (real_lt_plus_compat_lt_le (real_opp half) t half half).
        * exact Ht.
        * apply real_le_refl.
      + apply (real_plus_comm t half). }
  (* Segment 2: half < half + (half + t) (half+0 < half+(half+t), with 0 < half+t). *)
  assert (Hmid : real_lt half (real_plus half (real_plus half t))).
  { apply (real_eq_lt_lt half (real_plus half real_zero) (real_plus half (real_plus half t))).
    - apply real_eq_sym. apply (real_plus_zero half).
    - apply (real_lt_plus_compat_le_lt half half real_zero (real_plus half t)).
      + apply real_le_refl.
      + exact Hhalf_t. }
  (* Segment 3: half + (half + t) == 1 + t (assoc + half+half == 1). *)
  apply (real_lt_eq_lt half (real_plus half (real_plus half t)) (real_plus real_one t)).
  - exact Hmid.
  - apply (real_eq_trans (real_plus half (real_plus half t))
                         (real_plus (real_plus half half) t)
                         (real_plus real_one t)).
    + apply (real_plus_assoc half half t).
    + apply (RealSetoid.real_eq_plus_compat (real_plus half half) t real_one t).
      * (* half + half == 1: real_half_plus_half at 1. *)
        apply (real_eq_trans (real_plus half half)
                             (real_plus (real_mult half real_one) (real_mult half real_one))
                             real_one).
        -- apply (RealSetoid.real_eq_plus_compat half half
                                                  (real_mult half real_one) (real_mult half real_one)).
           ++ apply real_eq_sym. apply (real_mult_one half).
           ++ apply real_eq_sym. apply (real_mult_one half).
        -- apply (real_eq_trans (real_plus (real_mult half real_one) (real_mult half real_one))
                                (real_mult half (real_plus real_one real_one))
                                real_one).
           ++ apply real_eq_sym. apply (real_distrib half real_one real_one).
           ++ apply (real_eq_trans (real_mult half (real_plus real_one real_one))
                                   (real_mult (real_plus real_one real_one) half)
                                   real_one).
              ** apply (real_mult_comm half (real_plus real_one real_one)).
              ** apply (real_inv_pos_correct (real_plus real_one real_one) (real_two_pos_local)).
      * apply real_eq_refl.
Qed.

(* 19e: |h| < inv2·x ⟹ |h·inv x| < inv2 (|h·inv x| == |h|·inv x < (inv2·x)·inv x == inv2) *)
Lemma real_t_abs_lt_half : forall (x h : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h) (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x) ->
  real_lt (real_abs (real_mult h (real_inv_pos x Hx)))
          (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
Proof.
  intros x h Hx Hhx.
  set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  (* Segment 1: |h·inv x| == |h|·inv x. *)
  assert (Habs : real_eq (real_abs (real_mult h (real_inv_pos x Hx)))
                         (real_mult (real_abs h) (real_inv_pos x Hx))).
  { apply (real_eq_trans (real_abs (real_mult h (real_inv_pos x Hx)))
                         (real_mult (real_abs h) (real_abs (real_inv_pos x Hx)))
                         (real_mult (real_abs h) (real_inv_pos x Hx))).
    - exact (real_abs_mult_req h (real_inv_pos x Hx)).
    - apply (RealSetoid.real_eq_mult_compat (real_abs h) (real_abs (real_inv_pos x Hx))
                                            (real_abs h) (real_inv_pos x Hx)).
      + apply real_eq_refl.
      + apply (real_abs_pos_req (real_inv_pos x Hx) (real_inv_pos_pos x Hx)). }
  (* Segment 2: |h|·inv x < (half·x)·inv x. *)
  assert (Hmid : real_lt (real_mult (real_abs h) (real_inv_pos x Hx))
                         (real_mult (real_mult half x) (real_inv_pos x Hx))).
  { unfold half.
    apply (real_mult_lt_compat (real_abs h) (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                               (real_inv_pos x Hx)).
    - exact Hhx.
    - apply (real_inv_pos_pos x Hx). }
  (* Segment 3: (half·x)·inv x == half. *)
  assert (Heq : real_eq (real_mult (real_mult half x) (real_inv_pos x Hx)) half).
  { unfold half. exact (real_half_x_mult_inv x Hx). }
  (* Assembly: |h·inv x| == |h|·inv x < (half·x)·inv x == half. *)
  apply (real_eq_lt_lt (real_abs (real_mult h (real_inv_pos x Hx)))
                       (real_mult (real_abs h) (real_inv_pos x Hx))
                       half).
  - exact Habs.
  - apply (real_lt_eq_lt (real_mult (real_abs h) (real_inv_pos x Hx))
                         (real_mult (real_mult half x) (real_inv_pos x Hx))
                         half).
    + exact Hmid.
    + exact Heq.
Qed.

(* ============ 20. abs two-way bridges (main-theorem assembly): |X| ≤ 2t² + eps1 + eps2 + eps ============ *)

(* 20a: Q layer |x| ≤ a + b (from x ≤ a, −x ≤ b, 0 ≤ a, 0 ≤ b; trichotomy via Qlt_le_dec). *)
Lemma q_abs_le_plus : forall (x a b : Q),
  QleT' x a -> QleT' (- x) b -> QleT' 0 a -> QleT' 0 b -> QleT' (Qabs x) (a + b).
Proof.
  intros x a b Hxa Hxb Ha Hb.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec x 0) as [Hxlt | Hxge].
  - (* x < 0: Qabs x == −x ≤ b ≤ a + b *)
    apply (Qle_trans _ (- x) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_neg x). apply Qlt_le_weak. exact Hxlt.
    + apply (Qle_trans _ b _).
      * apply QleT'_to_Qle; exact Hxb.
      * apply (Qle_trans _ (b + a) _).
        -- apply (Qle_plus_nonneg_r b a). apply QleT'_to_Qle; exact Ha.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - (* x ≥ 0: Qabs x == x ≤ a ≤ a + b *)
    apply (Qle_trans _ x _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_pos x). exact Hxge.
    + apply (Qle_trans _ a _).
      * apply QleT'_to_Qle; exact Hxa.
      * apply (Qle_plus_nonneg_r a b). apply QleT'_to_Qle; exact Hb.
Qed.

(* 20b: Q layer x ≤ |x| (trichotomy via Qlt_le_dec). *)
Lemma q_le_abs : forall x : Q, QleT' x (Qabs x).
Proof.
  intro x.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec x 0) as [Hxlt | Hxge].
  - apply (Qle_trans _ 0 _).
    + apply Qlt_le_weak. exact Hxlt.
    + apply (Qle_trans _ (- x) _).
      * apply (Qopp_le_compat x 0). apply Qlt_le_weak. exact Hxlt.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_neg x). apply Qlt_le_weak. exact Hxlt.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos x). exact Hxge.
Qed.

(* 20c: Q layer |x−y| < c implies x ≤ y + c. *)
Lemma q_abs_lt_le : forall (x y c : Q), QltT (Qabs (x - y)) c -> QleT' x (y + c).
Proof.
  intros x y c Hc.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (x - y) + y) _).
  - apply (Qle_trans _ ((x - y) + y) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
    + apply (Qplus_le_compat (x - y) (Qabs (x - y)) y y).
      * apply QleT'_to_Qle. apply (q_le_abs (x - y)).
      * apply Qle_refl.
  - apply (Qle_trans _ (c + y) _).
    + apply (Qplus_le_compat (Qabs (x - y)) c y y).
      * apply Qlt_le_weak. apply QltT_to_Qlt. exact Hc.
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 20d: Q layer 0 < a and a < y−x imply x ≤ y (strict difference gives non-strict). *)
Lemma q_lt_diff_le : forall (a x y : Q), QltT 0 a -> QltT a (y - x) -> QleT' x y.
Proof.
  intros a x y Ha Hd.
  apply Qle_to_QleT'.
  assert (Hyx : Qlt 0 (y - x)) by (apply (Qlt_trans 0 a (y - x)); [apply QltT_to_Qlt; exact Ha | apply QltT_to_Qlt; exact Hd]).
  apply Qlt_le_weak.
  apply (Qlt_le_trans _ (x + (y - x)) _).
  - apply (Qle_lt_trans _ (x + 0) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_lt_trans _ (0 + x) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qlt_le_trans _ ((y - x) + x) _).
        -- apply (Qplus_lt_le_compat 0 (y - x) x x); [exact Hyx | apply Qle_refl].
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
Qed.

(* ============ 21. abs two-way bridges (4-branch lemmas + main lemma): X ≤ eps1 and −X ≤ 2t²+eps2 imply |X| ≤ 2t²+eps1+eps2+eps ============ *)

(* 21a: the lt/lt branch (X < eps1, −X < 2t²+eps2). *)
Lemma real_abs_le_quad_ll : forall (X t eps1 eps2 eps : Real)
  (HXA_lt : real_lt X eps1)
  (HXB_lt : real_lt (real_opp X) (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2))
  (HA : real_lt real_zero eps1)
  (Heps2 : real_lt real_zero eps2)
  (Heps : real_lt real_zero eps),
  real_le (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps).
Proof.
  intros X t eps1 eps2 eps HXA_lt HXB_lt HA Heps2 Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  destruct HA as [a1 [Ha1 [Na1 HNa1]]].
  destruct Heps2 as [e2 [He2 [Ne2 HNe2]]].
  destruct HXA_lt as [a [Ha [Na HNa]]].
  destruct HXB_lt as [b [Hb [Nb HNb]]].
  apply (RealSetoid.real_lt_le_iff_req (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps)). left.
  unfold real_lt.
  exists eps0.
  split.
  - exact Heps0.
  - exists (Nat.max N0 (Nat.max Na (Nat.max Nb (Nat.max Na1 Ne2)))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hna : (Na <= n)%nat) by lia.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hna1 : (Na1 <= n)%nat) by lia.
    assert (Hne2 : (Ne2 <= n)%nat) by lia.
    set (xn := projT1 X n).
    set (tn := projT1 t n).
    set (p2 := projT1 (real_plus real_one real_one) n).
    set (e1n := projT1 eps1 n).
    set (e2n := projT1 eps2 n).
    set (en := projT1 eps n).
    set (qn := projT1 (real_abs X) n).
    set (pn := projT1 (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps) n).
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hepsn : Qlt eps0 en).
    { unfold en. apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He1n_pos : Qle 0 e1n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e1n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 a1 (e1n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact Ha1.
        + apply QltT_to_Qlt. exact (HNa1 n (NatLe_lift _ _ Hna1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He2n_pos : Qle 0 e2n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e2n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 e2 (e2n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact He2.
        + apply QltT_to_Qlt. exact (HNe2 n (NatLe_lift _ _ Hne2)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (Hp2 : p2 == 2).
    { unfold p2. setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)). cbn [projT1]. ring. }
    assert (Hp2_pos : Qle 0 p2).
    { apply (Qle_trans _ 2 _).
      - apply Qlt_le_weak. vm_compute; reflexivity.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hp2. }
    assert (Hsq : Qle 0 (tn * tn)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg tn)).
    assert (Hqpos : Qle 0 ((tn * tn) * p2 + e2n)).
    { apply (Qle_trans _ e2n _).
      - exact He2n_pos.
      - apply (Qle_trans _ (e2n + (tn * tn) * p2) _).
        + apply (Qle_plus_nonneg_r e2n ((tn * tn) * p2)).
          apply (Qmult_le_0_compat (tn * tn) p2).
          * exact Hsq.
          * exact Hp2_pos.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hqn_eq : qn == Qabs xn).
    { unfold qn, xn. setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj X n)). reflexivity. }
    assert (Hpn_eq : pn == (tn * tn) * p2 + e1n + e2n + en).
    { unfold pn, tn, p2, e1n, e2n, en.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj eps1 eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    (* B_n == (tn·tn)·p2 + e2n (the 2t²+eps2 projection unfolding). *)
    assert (HBeq : projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n == (tn * tn) * p2 + e2n).
    { unfold tn, p2, e2n.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    (* xn ≤ e1n (strict difference). *)
    assert (Hxa_n : Qle xn e1n).
    { unfold xn, e1n. apply QleT'_to_Qle. apply (q_lt_diff_le a (projT1 X n) (projT1 eps1 n)).
      - exact Ha.
      - exact (HNa n (NatLe_lift _ _ Hna)). }
    (* −xn ≤ (tn·tn)·p2 + e2n (strict difference; Qeq chain unfolding B_n and oppX_n). *)
    assert (Hxb_n : Qle (Qopp xn) ((tn * tn) * p2 + e2n)).
    { unfold xn, tn, p2, e2n.
      apply QleT'_to_Qle. apply (q_lt_diff_le b (Qopp (projT1 X n)) ((tn * tn) * p2 + e2n)).
      - exact Hb.
      - apply Qlt_to_QltT. apply (Qlt_le_trans _ (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n - projT1 (real_opp X) n) _).
        + apply QltT_to_Qlt. exact (HNb n (NatLe_lift _ _ Hnb)).
        + apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
          apply (Qplus_comp (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n)
                            ((tn * tn) * p2 + e2n)
                            HBeq
                            (Qopp (projT1 (real_opp X) n)) (Qopp (Qopp (projT1 X n)))
                            (Qopp_comp (projT1 (real_opp X) n) (Qopp (projT1 X n)) (qeqT_imp_qeq _ _ (real_opp_proj X n)))). }
    (* Qabs xn ≤ (tn·tn)·p2 + e1n + e2n (q_abs_le_plus) *)
    assert (Habsn : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n)).
    { apply (Qle_trans _ (e1n + ((tn * tn) * p2 + e2n)) _).
      - apply QleT'_to_Qle. apply (q_abs_le_plus xn e1n ((tn * tn) * p2 + e2n)).
        + apply Qle_to_QleT'. exact Hxa_n.
        + apply Qle_to_QleT'. exact Hxb_n.
        + apply Qle_to_QleT'. exact He1n_pos.
        + apply Qle_to_QleT'. exact Hqpos.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* Main chain: eps0 < en ≤ pn − qn. *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ en _).
    { exact Hepsn. }
    { apply (Qle_trans _ (en + ((tn * tn) * p2 + e1n + e2n - Qabs xn)) _).
      { apply (Qle_plus_nonneg_r en ((tn * tn) * p2 + e1n + e2n - Qabs xn)).
        apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + Qopp (Qabs xn)) _).
        { apply (Qle_trans _ (Qabs xn + Qopp (Qabs xn)) _).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qplus_opp_r (Qabs xn)).
          - apply (Qplus_le_compat (Qabs xn) ((tn * tn) * p2 + e1n + e2n)
                                   (Qopp (Qabs xn)) (Qopp (Qabs xn))).
            + exact Habsn.
            + apply Qle_refl. }
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. } }
      { apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_trans _ ((tn * tn) * p2 + e1n + e2n + en - Qabs xn) _).
        { unfold Qminus. ring. }
        { apply (Qplus_comp ((tn * tn) * p2 + e1n + e2n + en) pn
                            (Qeq_sym _ _ Hpn_eq)
                            (Qopp (Qabs xn)) (Qopp qn)).
          apply (Qopp_comp (Qabs xn) qn). apply Qeq_sym. exact Hqn_eq. } } }
Qed.

(* 21b: Q layer 0 < q implies q/2 < q (the Cauchy-margin bridge on the eq branch). *)
Lemma q_half_pos : forall q : Q, QltT 0 q -> QltT 0 (q / 2).
Proof.
  intros q Hq.
  apply Qlt_to_QltT.
  apply (Qlt_shift_div_l 0 q 2).
  - reflexivity.
  - simpl. apply QltT_to_Qlt. exact Hq.
Qed.

(* 21c: the lt/eq branch (X < eps1, −X == 2t²+eps2 in the Cauchy sense). *)
Lemma real_abs_le_quad_le : forall (X t eps1 eps2 eps : Real)
  (HXA_lt : real_lt X eps1)
  (HXB_eq : real_eq (real_opp X) (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2))
  (HA : real_lt real_zero eps1)
  (Heps2 : real_lt real_zero eps2)
  (Heps : real_lt real_zero eps),
  real_le (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps).
Proof.
  intros X t eps1 eps2 eps HXA_lt HXB_eq HA Heps2 Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  destruct HA as [a1 [Ha1 [Na1 HNa1]]].
  destruct Heps2 as [e2 [He2 [Ne2 HNe2]]].
  destruct HXA_lt as [a [Ha [Na HNa]]].
  assert (Heps0h : QltT 0 (eps0 / 2)).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0]. }
  destruct (HXB_eq (eps0 / 2) Heps0h) as [Nxb HXBeq_n].
  apply (RealSetoid.real_lt_le_iff_req (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps)). left.
  unfold real_lt.
  exists (eps0 / 2).
  split.
  - apply (q_half_pos eps0). exact Heps0.
  - exists (Nat.max N0 (Nat.max Na (Nat.max Nxb (Nat.max Na1 Ne2)))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hna : (Na <= n)%nat) by lia.
    assert (Hnxb : (Nxb <= n)%nat) by lia.
    assert (Hna1 : (Na1 <= n)%nat) by lia.
    assert (Hne2 : (Ne2 <= n)%nat) by lia.
    set (xn := projT1 X n).
    set (tn := projT1 t n).
    set (p2 := projT1 (real_plus real_one real_one) n).
    set (e1n := projT1 eps1 n).
    set (e2n := projT1 eps2 n).
    set (en := projT1 eps n).
    set (qn := projT1 (real_abs X) n).
    set (pn := projT1 (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps) n).
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hepsn : Qlt eps0 en).
    { unfold en. apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He1n_pos : Qle 0 e1n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e1n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 a1 (e1n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact Ha1.
        + apply QltT_to_Qlt. exact (HNa1 n (NatLe_lift _ _ Hna1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He2n_pos : Qle 0 e2n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e2n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 e2 (e2n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact He2.
        + apply QltT_to_Qlt. exact (HNe2 n (NatLe_lift _ _ Hne2)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (Hp2 : p2 == 2).
    { unfold p2. setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)). cbn [projT1]. ring. }
    assert (Hp2_pos : Qle 0 p2).
    { apply (Qle_trans _ 2 _).
      - apply Qlt_le_weak. vm_compute; reflexivity.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hp2. }
    assert (Hsq : Qle 0 (tn * tn)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg tn)).
    assert (Hqpos : Qle 0 ((tn * tn) * p2 + e2n)).
    { apply (Qle_trans _ e2n _).
      - exact He2n_pos.
      - apply (Qle_trans _ (e2n + (tn * tn) * p2) _).
        + apply (Qle_plus_nonneg_r e2n ((tn * tn) * p2)).
          apply (Qmult_le_0_compat (tn * tn) p2).
          * exact Hsq.
          * exact Hp2_pos.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hqn_eq : qn == Qabs xn).
    { unfold qn, xn. setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj X n)). reflexivity. }
    assert (Hpn_eq : pn == (tn * tn) * p2 + e1n + e2n + en).
    { unfold pn, tn, p2, e1n, e2n, en.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj eps1 eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (HBeq : projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n == (tn * tn) * p2 + e2n).
    { unfold tn, p2, e2n.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (Heps0h_le : Qle (eps0 / 2) en).
    { apply (Qle_trans _ eps0 _).
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
      - apply Qlt_le_weak. exact Hepsn. }
    assert (Hxa_n : Qle xn e1n).
    { unfold xn, e1n. apply QleT'_to_Qle. apply (q_lt_diff_le a (projT1 X n) (projT1 eps1 n)).
      - exact Ha.
      - exact (HNa n (NatLe_lift _ _ Hna)). }
    assert (Hxb_n : Qle (Qopp xn) ((tn * tn) * p2 + e2n + eps0 / 2)).
    { unfold xn, tn, p2, e2n.
      apply (Qle_trans _ (projT1 (real_opp X) n) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (qeqT_imp_qeq _ _ (real_opp_proj X n)).
      - apply (Qle_trans _ (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n + eps0 / 2) _).
        + apply QleT'_to_Qle. apply (q_abs_lt_le (projT1 (real_opp X) n)
                             (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n)
                             (eps0 / 2)).
          exact (HXBeq_n n (NatLe_lift _ _ Hnxb)).
        + apply (Qplus_le_compat (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n)
                                 ((tn * tn) * p2 + e2n)
                                 (eps0 / 2) (eps0 / 2)).
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact HBeq.
          * apply Qle_refl. }
    assert (Habsn : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n + eps0 / 2)).
    { apply (Qle_trans _ (e1n + ((tn * tn) * p2 + e2n + eps0 / 2)) _).
      - apply QleT'_to_Qle. apply (q_abs_le_plus xn e1n ((tn * tn) * p2 + e2n + eps0 / 2)).
        + apply Qle_to_QleT'. exact Hxa_n.
        + apply Qle_to_QleT'. exact Hxb_n.
        + apply Qle_to_QleT'. exact He1n_pos.
        + apply Qle_to_QleT'. apply (Qle_trans _ e2n _).
          * exact He2n_pos.
          * apply (Qle_trans _ (e2n + ((tn * tn) * p2 + eps0 / 2)) _).
            -- apply (Qle_plus_nonneg_r e2n ((tn * tn) * p2 + eps0 / 2)).
               apply (Qle_trans _ 0 _).
               ++ apply Qle_refl.
               ++ apply (Qplus_le_compat 0 ((tn * tn) * p2) 0 (eps0 / 2)).
                  ** apply (Qmult_le_0_compat (tn * tn) p2).
                     --- exact Hsq.
                     --- exact Hp2_pos.
                  ** apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_pos eps0). exact Heps0.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    assert (Habsn' : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n + en)).
    { apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2) _).
      - exact Habsn.
      - apply (Qplus_le_compat ((tn * tn) * p2 + e1n + e2n) ((tn * tn) * p2 + e1n + e2n)
                               (eps0 / 2) en).
        + apply Qle_refl.
        + exact Heps0h_le. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (en - eps0 / 2) _).
    { (* eps0/2 < en − eps0/2: 0 < en − eps0 (Hepsn)⟹ (en−eps0) + eps0/2 > 0 + eps0/2 *)
      apply (Qlt_le_trans _ ((en - eps0) + eps0 / 2) _).
      - apply (Qle_lt_trans _ (0 + eps0 / 2) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        + apply (Qplus_lt_le_compat 0 (en - eps0) (eps0 / 2) (eps0 / 2)).
          * apply (proj1 (Qlt_minus_iff eps0 en)). exact Hepsn.
          * apply Qle_refl.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    { (* en − eps0/2 ≤ pn − qn *)
      apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + en - Qabs xn) _).
      - apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn + (en - eps0 / 2)) _).
        + apply (Qle_trans _ ((en - eps0 / 2) + ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn)) _).
          * apply (Qle_plus_nonneg_r (en - eps0 / 2) ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn)).
            apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2 + Qopp (Qabs xn)) _).
            -- apply (Qle_trans _ (Qabs xn + Qopp (Qabs xn)) _).
               ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qplus_opp_r (Qabs xn)).
               ++ apply (Qplus_le_compat (Qabs xn) ((tn * tn) * p2 + e1n + e2n + eps0 / 2)
                                      (Qopp (Qabs xn)) (Qopp (Qabs xn))).
                  ** exact Habsn.
                  ** apply Qle_refl.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_trans _ (pn - qn) _).
        * apply (Qplus_comp ((tn * tn) * p2 + e1n + e2n + en) pn
                            (Qeq_sym _ _ Hpn_eq)
                            (Qopp (Qabs xn)) (Qopp qn)).
          apply (Qopp_comp (Qabs xn) qn). apply Qeq_sym. exact Hqn_eq.
        * reflexivity. }
Qed.

(* 21b'': Q layer 0 < q implies 0 < q/4 (the ee-branch two-sided Cauchy margin). *)
Lemma q_quarter_pos : forall q : Q, QltT 0 q -> QltT 0 (q / 4).
Proof.
  intros q Hq.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (q / 2 / 2) _).
  - apply QltT_to_Qlt. apply (q_half_pos (q / 2)). apply (q_half_pos q). exact Hq.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* 21e: the eq/eq branch (X == eps1 and −X == 2t²+eps2, both Cauchy; margins eps0/4). *)
Lemma real_abs_le_quad_ee : forall (X t eps1 eps2 eps : Real)
  (HXA_eq : real_eq X eps1)
  (HXB_eq : real_eq (real_opp X) (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2))
  (HA : real_lt real_zero eps1)
  (Heps2 : real_lt real_zero eps2)
  (Heps : real_lt real_zero eps),
  real_le (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps).
Proof.
  intros X t eps1 eps2 eps HXA_eq HXB_eq HA Heps2 Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  destruct HA as [a1 [Ha1 [Na1 HNa1]]].
  destruct Heps2 as [e2 [He2 [Ne2 HNe2]]].
  assert (Heps0q : QltT 0 (eps0 / 4)).
  { apply (q_quarter_pos eps0). exact Heps0. }
  destruct (HXA_eq (eps0 / 4) Heps0q) as [Nxa HXAeq_n].
  destruct (HXB_eq (eps0 / 4) Heps0q) as [Nxb HXBeq_n].
  apply (RealSetoid.real_lt_le_iff_req (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps)). left.
  unfold real_lt.
  exists (eps0 / 2).
  split.
  - apply (q_half_pos eps0). exact Heps0.
  - exists (Nat.max N0 (Nat.max Nxa (Nat.max Nxb (Nat.max Na1 Ne2)))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hnxa : (Nxa <= n)%nat) by lia.
    assert (Hnxb : (Nxb <= n)%nat) by lia.
    assert (Hna1 : (Na1 <= n)%nat) by lia.
    assert (Hne2 : (Ne2 <= n)%nat) by lia.
    set (xn := projT1 X n).
    set (tn := projT1 t n).
    set (p2 := projT1 (real_plus real_one real_one) n).
    set (e1n := projT1 eps1 n).
    set (e2n := projT1 eps2 n).
    set (en := projT1 eps n).
    set (qn := projT1 (real_abs X) n).
    set (pn := projT1 (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps) n).
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hepsn : Qlt eps0 en).
    { unfold en. apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He1n_pos : Qle 0 e1n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e1n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 a1 (e1n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact Ha1.
        + apply QltT_to_Qlt. exact (HNa1 n (NatLe_lift _ _ Hna1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He2n_pos : Qle 0 e2n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e2n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 e2 (e2n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact He2.
        + apply QltT_to_Qlt. exact (HNe2 n (NatLe_lift _ _ Hne2)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (Hp2 : p2 == 2).
    { unfold p2. setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)). cbn [projT1]. ring. }
    assert (Hp2_pos : Qle 0 p2).
    { apply (Qle_trans _ 2 _).
      - apply Qlt_le_weak. vm_compute; reflexivity.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hp2. }
    assert (Hsq : Qle 0 (tn * tn)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg tn)).
    assert (Hqpos : Qle 0 ((tn * tn) * p2 + e2n)).
    { apply (Qle_trans _ e2n _).
      - exact He2n_pos.
      - apply (Qle_trans _ (e2n + (tn * tn) * p2) _).
        + apply (Qle_plus_nonneg_r e2n ((tn * tn) * p2)).
          apply (Qmult_le_0_compat (tn * tn) p2).
          * exact Hsq.
          * exact Hp2_pos.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hqn_eq : qn == Qabs xn).
    { unfold qn, xn. setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj X n)). reflexivity. }
    assert (Hpn_eq : pn == (tn * tn) * p2 + e1n + e2n + en).
    { unfold pn, tn, p2, e1n, e2n, en.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj eps1 eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (HBeq : projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n == (tn * tn) * p2 + e2n).
    { unfold tn, p2, e2n.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (Heps0h_le : Qle (eps0 / 2) en).
    { apply (Qle_trans _ eps0 _).
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
      - apply Qlt_le_weak. exact Hepsn. }
    assert (Hxa_n : Qle xn (e1n + eps0 / 4)).
    { unfold xn, e1n.
      apply QleT'_to_Qle. apply (q_abs_lt_le (projT1 X n) (projT1 eps1 n) (eps0 / 4)).
      exact (HXAeq_n n (NatLe_lift _ _ Hnxa)). }
    assert (Hxb_n : Qle (Qopp xn) ((tn * tn) * p2 + e2n + eps0 / 4)).
    { unfold xn, tn, p2, e2n.
      apply (Qle_trans _ (projT1 (real_opp X) n) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (qeqT_imp_qeq _ _ (real_opp_proj X n)).
      - apply (Qle_trans _ (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n + eps0 / 4) _).
        + apply QleT'_to_Qle. apply (q_abs_lt_le (projT1 (real_opp X) n)
                             (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n)
                             (eps0 / 4)).
          exact (HXBeq_n n (NatLe_lift _ _ Hnxb)).
        + apply (Qplus_le_compat (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n)
                                 ((tn * tn) * p2 + e2n)
                                 (eps0 / 4) (eps0 / 4)).
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact HBeq.
          * apply Qle_refl. }
    assert (Habsn : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n + eps0 / 2)).
    { apply (Qle_trans _ ((e1n + eps0 / 4) + ((tn * tn) * p2 + e2n + eps0 / 4)) _).
      - apply QleT'_to_Qle. apply (q_abs_le_plus xn (e1n + eps0 / 4) ((tn * tn) * p2 + e2n + eps0 / 4)).
        + apply Qle_to_QleT'. exact Hxa_n.
        + apply Qle_to_QleT'. exact Hxb_n.
        + apply Qle_to_QleT'. apply (Qplus_le_compat 0 e1n 0 (eps0 / 4)).
          * exact He1n_pos.
          * apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_quarter_pos eps0). exact Heps0.
        + apply Qle_to_QleT'. apply (Qle_trans _ e2n _).
          * exact He2n_pos.
          * apply (Qle_trans _ (e2n + ((tn * tn) * p2 + eps0 / 4)) _).
            -- apply (Qle_plus_nonneg_r e2n ((tn * tn) * p2 + eps0 / 4)).
               apply (Qle_trans _ 0 _).
               ++ apply Qle_refl.
               ++ apply (Qplus_le_compat 0 ((tn * tn) * p2) 0 (eps0 / 4)).
                  ** apply (Qmult_le_0_compat (tn * tn) p2).
                     --- exact Hsq.
                     --- exact Hp2_pos.
                  ** apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_quarter_pos eps0). exact Heps0.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    assert (Habsn' : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n + en)).
    { apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2) _).
      - exact Habsn.
      - apply (Qplus_le_compat ((tn * tn) * p2 + e1n + e2n) ((tn * tn) * p2 + e1n + e2n)
                               (eps0 / 2) en).
        + apply Qle_refl.
        + exact Heps0h_le. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (en - eps0 / 2) _).
    { apply (Qlt_le_trans _ ((en - eps0) + eps0 / 2) _).
      - apply (Qle_lt_trans _ (0 + eps0 / 2) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        + apply (Qplus_lt_le_compat 0 (en - eps0) (eps0 / 2) (eps0 / 2)).
          * apply (proj1 (Qlt_minus_iff eps0 en)). exact Hepsn.
          * apply Qle_refl.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    { apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + en - Qabs xn) _).
      - apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn + (en - eps0 / 2)) _).
        + apply (Qle_trans _ ((en - eps0 / 2) + ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn)) _).
          * apply (Qle_plus_nonneg_r (en - eps0 / 2) ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn)).
            apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2 + Qopp (Qabs xn)) _).
            -- apply (Qle_trans _ (Qabs xn + Qopp (Qabs xn)) _).
               ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qplus_opp_r (Qabs xn)).
               ++ apply (Qplus_le_compat (Qabs xn) ((tn * tn) * p2 + e1n + e2n + eps0 / 2)
                                      (Qopp (Qabs xn)) (Qopp (Qabs xn))).
                  ** exact Habsn.
                  ** apply Qle_refl.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_trans _ (pn - qn) _).
        * apply (Qplus_comp ((tn * tn) * p2 + e1n + e2n + en) pn
                            (Qeq_sym _ _ Hpn_eq)
                            (Qopp (Qabs xn)) (Qopp qn)).
          apply (Qopp_comp (Qabs xn) qn). apply Qeq_sym. exact Hqn_eq.
        * reflexivity. }
Qed.

(* 21d: the eq/lt branch (X == eps1 Cauchy, −X < 2t²+eps2). *)
Lemma real_abs_le_quad_el : forall (X t eps1 eps2 eps : Real)
  (HXA_eq : real_eq X eps1)
  (HXB_lt : real_lt (real_opp X) (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2))
  (HA : real_lt real_zero eps1)
  (Heps2 : real_lt real_zero eps2)
  (Heps : real_lt real_zero eps),
  real_le (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps).
Proof.
  intros X t eps1 eps2 eps HXA_eq HXB_lt HA Heps2 Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  destruct HA as [a1 [Ha1 [Na1 HNa1]]].
  destruct Heps2 as [e2 [He2 [Ne2 HNe2]]].
  destruct HXB_lt as [b [Hb [Nb HNb]]].
  assert (Heps0h : QltT 0 (eps0 / 2)).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0]. }
  destruct (HXA_eq (eps0 / 2) Heps0h) as [Nxa HXAeq_n].
  apply (RealSetoid.real_lt_le_iff_req (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps)). left.
  unfold real_lt.
  exists (eps0 / 2).
  split.
  - apply (q_half_pos eps0). exact Heps0.
  - exists (Nat.max N0 (Nat.max Nxa (Nat.max Nb (Nat.max Na1 Ne2)))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hnxa : (Nxa <= n)%nat) by lia.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hna1 : (Na1 <= n)%nat) by lia.
    assert (Hne2 : (Ne2 <= n)%nat) by lia.
    set (xn := projT1 X n).
    set (tn := projT1 t n).
    set (p2 := projT1 (real_plus real_one real_one) n).
    set (e1n := projT1 eps1 n).
    set (e2n := projT1 eps2 n).
    set (en := projT1 eps n).
    set (qn := projT1 (real_abs X) n).
    set (pn := projT1 (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps) n).
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hepsn : Qlt eps0 en).
    { unfold en. apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He1n_pos : Qle 0 e1n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e1n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 a1 (e1n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact Ha1.
        + apply QltT_to_Qlt. exact (HNa1 n (NatLe_lift _ _ Hna1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (He2n_pos : Qle 0 e2n).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans _ (e2n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 e2 (e2n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact He2.
        + apply QltT_to_Qlt. exact (HNe2 n (NatLe_lift _ _ Hne2)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (Hp2 : p2 == 2).
    { unfold p2. setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)). cbn [projT1]. ring. }
    assert (Hp2_pos : Qle 0 p2).
    { apply (Qle_trans _ 2 _).
      - apply Qlt_le_weak. vm_compute; reflexivity.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hp2. }
    assert (Hsq : Qle 0 (tn * tn)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg tn)).
    assert (Hqpos : Qle 0 ((tn * tn) * p2 + e2n)).
    { apply (Qle_trans _ e2n _).
      - exact He2n_pos.
      - apply (Qle_trans _ (e2n + (tn * tn) * p2) _).
        + apply (Qle_plus_nonneg_r e2n ((tn * tn) * p2)).
          apply (Qmult_le_0_compat (tn * tn) p2).
          * exact Hsq.
          * exact Hp2_pos.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hqn_eq : qn == Qabs xn).
    { unfold qn, xn. setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj X n)). reflexivity. }
    assert (Hpn_eq : pn == (tn * tn) * p2 + e1n + e2n + en).
    { unfold pn, tn, p2, e1n, e2n, en.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj eps1 eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (HBeq : projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n == (tn * tn) * p2 + e2n).
    { unfold tn, p2, e2n.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (Heps0h_le : Qle (eps0 / 2) en).
    { apply (Qle_trans _ eps0 _).
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
      - apply Qlt_le_weak. exact Hepsn. }
    (* xn ≤ e1n + eps0/2 (the eq Cauchy margin). *)
    assert (Hxa_n : Qle xn (e1n + eps0 / 2)).
    { unfold xn, e1n.
      apply QleT'_to_Qle. apply (q_abs_lt_le (projT1 X n) (projT1 eps1 n) (eps0 / 2)).
      exact (HXAeq_n n (NatLe_lift _ _ Hnxa)). }
    (* −xn ≤ (tn·tn)·p2 + e2n (strict difference). *)
    assert (Hxb_n : Qle (Qopp xn) ((tn * tn) * p2 + e2n)).
    { unfold xn, tn, p2, e2n.
      apply QleT'_to_Qle. apply (q_lt_diff_le b (Qopp (projT1 X n)) ((tn * tn) * p2 + e2n)).
      - exact Hb.
      - apply Qlt_to_QltT. apply (Qlt_le_trans _ (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n - projT1 (real_opp X) n) _).
        + apply QltT_to_Qlt. exact (HNb n (NatLe_lift _ _ Hnb)).
        + apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
          apply (Qplus_comp (projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n)
                            ((tn * tn) * p2 + e2n)
                            HBeq
                            (Qopp (projT1 (real_opp X) n)) (Qopp (Qopp (projT1 X n)))
                            (Qopp_comp (projT1 (real_opp X) n) (Qopp (projT1 X n)) (qeqT_imp_qeq _ _ (real_opp_proj X n)))). }
    assert (Habsn : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n + eps0 / 2)).
    { apply (Qle_trans _ ((e1n + eps0 / 2) + ((tn * tn) * p2 + e2n)) _).
      - apply QleT'_to_Qle. apply (q_abs_le_plus xn (e1n + eps0 / 2) ((tn * tn) * p2 + e2n)).
        + apply Qle_to_QleT'. exact Hxa_n.
        + apply Qle_to_QleT'. exact Hxb_n.
        + apply Qle_to_QleT'. apply (Qplus_le_compat 0 e1n 0 (eps0 / 2)).
          * exact He1n_pos.
          * apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_pos eps0). exact Heps0.
        + apply Qle_to_QleT'. exact Hqpos.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    assert (Habsn' : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n + en)).
    { apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2) _).
      - exact Habsn.
      - apply (Qplus_le_compat ((tn * tn) * p2 + e1n + e2n) ((tn * tn) * p2 + e1n + e2n)
                               (eps0 / 2) en).
        + apply Qle_refl.
        + exact Heps0h_le. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (en - eps0 / 2) _).
    { apply (Qlt_le_trans _ ((en - eps0) + eps0 / 2) _).
      - apply (Qle_lt_trans _ (0 + eps0 / 2) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        + apply (Qplus_lt_le_compat 0 (en - eps0) (eps0 / 2) (eps0 / 2)).
          * apply (proj1 (Qlt_minus_iff eps0 en)). exact Hepsn.
          * apply Qle_refl.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    { apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + en - Qabs xn) _).
      - apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn + (en - eps0 / 2)) _).
        + apply (Qle_trans _ ((en - eps0 / 2) + ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn)) _).
          * apply (Qle_plus_nonneg_r (en - eps0 / 2) ((tn * tn) * p2 + e1n + e2n + eps0 / 2 - Qabs xn)).
            apply (Qle_trans _ ((tn * tn) * p2 + e1n + e2n + eps0 / 2 + Qopp (Qabs xn)) _).
            -- apply (Qle_trans _ (Qabs xn + Qopp (Qabs xn)) _).
               ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qplus_opp_r (Qabs xn)).
               ++ apply (Qplus_le_compat (Qabs xn) ((tn * tn) * p2 + e1n + e2n + eps0 / 2)
                                      (Qopp (Qabs xn)) (Qopp (Qabs xn))).
                  ** exact Habsn.
                  ** apply Qle_refl.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_trans _ (pn - qn) _).
        * apply (Qplus_comp ((tn * tn) * p2 + e1n + e2n + en) pn
                            (Qeq_sym _ _ Hpn_eq)
                            (Qopp (Qabs xn)) (Qopp qn)).
          apply (Qopp_comp (Qabs xn) qn). apply Qeq_sym. exact Hqn_eq.
        * reflexivity. }
Qed.
(* 21f: the abs-bridge main lemma (dispatching over the 4 branches). *)
Lemma real_abs_le_quad_eps : forall (X t eps1 eps2 eps : Real)
  (HXA : real_le X eps1)
  (HXB : real_le (real_opp X) (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2))
  (HA : real_lt real_zero eps1)
  (Heps2 : real_lt real_zero eps2)
  (Heps : real_lt real_zero eps),
  real_le (real_abs X)
          (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus eps1 eps2)) eps).
Proof.
  intros X t eps1 eps2 eps HXA HXB HA Heps2 Heps.
  unfold real_le in HXA, HXB.
  destruct HXA as [HXA_lt | HXA_eq].
  { destruct HXB as [HXB_lt | HXB_eq].
    - exact (real_abs_le_quad_ll X t eps1 eps2 eps HXA_lt HXB_lt HA Heps2 Heps).
    - exact (real_abs_le_quad_le X t eps1 eps2 eps HXA_lt HXB_eq HA Heps2 Heps). }
  { destruct HXB as [HXB_lt | HXB_eq].
    - exact (real_abs_le_quad_el X t eps1 eps2 eps HXA_eq HXB_lt HA Heps2 Heps).
    - exact (real_abs_le_quad_ee X t eps1 eps2 eps HXA_eq HXB_eq HA Heps2 Heps). }
Qed.

(* ============ 22. Final scaling: 2·(h·inv x)² ≤ (eps/2)·|h| + eps' ============ *)

(* 22a: Q layer q² == |q|² (trichotomy via Qlt_le_dec). *)
Lemma q_sq_abs : forall q : Q, QeqT (q * q) (Qabs q * Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  destruct (Qlt_le_dec q 0) as [Hqlt | Hqge].
  - apply (Qeq_trans _ (- q * - q) _).
    + ring.
    + apply (Qmult_comp (- q) (Qabs q) (Qeq_sym _ _ (Qabs_neg q (Qlt_le_weak q 0 Hqlt)))
                       (- q) (Qabs q) (Qeq_sym _ _ (Qabs_neg q (Qlt_le_weak q 0 Hqlt)))).
  - apply (Qmult_comp q (Qabs q) (Qeq_sym _ _ (Qabs_pos q Hqge))
                     q (Qabs q) (Qeq_sym _ _ (Qabs_pos q Hqge))).
Qed.

(* 22b: Q layer 2a²·iv² ≤ (e/2)·a (from a ≥ 0, a ≤ e·x²/4, and x·iv == 1). *)
Lemma q_quad_le_h_inv : forall (a x e iv : Q),
  QleT' 0 a -> QleT' a (e * (x * x) / 4) -> QleT' 0 iv -> QeqT (x * iv) 1 ->
  QleT' (2 * (a * a) * (iv * iv)) (e / 2 * a).
Proof.
  intros a x e iv Ha Hae Hiv Hxi.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (2 * (a * (e * (x * x) / 4)) * (iv * iv)) _).
  - apply (Qmult_le_compat_r (2 * (a * a)) (2 * (a * (e * (x * x) / 4))) (iv * iv)).
    + apply (Qmult_le_compat_nonneg 2 2 (a * a) (a * (e * (x * x) / 4))).
      * split; [apply Qlt_le_weak; vm_compute; reflexivity | apply Qle_refl].
      * split.
        -- apply (Qmult_le_0_compat a a (QleT'_to_Qle _ _ Ha) (QleT'_to_Qle _ _ Ha)).
        -- apply (Qle_trans _ ((e * (x * x) / 4) * a) _).
           ++ apply (Qmult_le_compat_r a (e * (x * x) / 4) a).
              ** apply QleT'_to_Qle; exact Hae.
              ** apply QleT'_to_Qle; exact Ha.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qmult_le_0_compat iv iv (QleT'_to_Qle _ _ Hiv) (QleT'_to_Qle _ _ Hiv)).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    apply (Qeq_trans _ (e / 2 * a * ((x * iv) * (x * iv))) _).
    + unfold Qdiv. field.
    + apply (Qeq_trans _ ((e / 2 * a) * 1) _).
      * apply (Qmult_comp (e / 2 * a) (e / 2 * a) (Qeq_refl _)
                          ((x * iv) * (x * iv)) 1
                          (Qmult_comp (x * iv) 1 (qeqT_imp_qeq _ _ Hxi) (x * iv) 1 (qeqT_imp_qeq _ _ Hxi))).
      * apply (Qmult_1_r (e / 2 * a)).
Qed.

(* 22c: the main theorem's final scaling (pointwise Q layer, witness eps0'). *)
Lemma real_quad_t_le_h_eps : forall (x h eps eps' : Real)
  (Hx : real_lt real_zero x)
  (Hh : real_lt (real_abs h)
        (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                              (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                   (real_mult eps (real_mult x x))))
  (Heps : real_lt real_zero eps)
  (Heps' : real_lt real_zero eps'),
  real_le (real_mult (real_mult (real_mult h (real_inv_pos x Hx)) (real_mult h (real_inv_pos x Hx)))
                     (real_plus real_one real_one))
          (real_plus (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) eps)
                                (real_abs h)) eps').
Proof.
  intros x h eps eps' Hx Hh Heps Heps'.
  destruct Heps' as [eps0 [Heps0 [N0 HN0]]].
  destruct Hh as [d [Hd [Nd HNd]]].
  destruct x as [ux Hux].
  destruct Hx as [e1 [He1 [N1 HN1]]].
  apply (RealSetoid.real_lt_le_iff_req _ _). left.
  unfold real_lt.
  destruct (real_two_pos_local) as [e2 [He2 [N2 HN2]]].
  set (half := real_inv_pos (real_plus real_one real_one) (existT _ e2 (He2, existT _ N2 HN2))).
  exists eps0.
  split.
  - exact Heps0.
  - exists (Nat.max N0 (Nat.max Nd (Nat.max N1 N2))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hnd : (Nd <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    set (hn := projT1 h n).
    set (xn := ux n).
    set (en := projT1 eps n).
    set (en' := projT1 eps' n).
    set (p2 := projT1 (real_plus real_one real_one) n).
    set (halfn := projT1 half n).
    set (I := real_inv_pos (existT (fun u : Qseq => cauchy u) ux Hux)
         (existT (fun eps0 : Q => And (QltT 0 eps0) {N0 : nat & forall n0 : nat, NatLe N0 n0 -> QltT eps0 (projT1 (existT (fun u : Qseq => cauchy u) ux Hux) n0 - projT1 real_zero n0)})
                 e1 (He1, existT (fun N0 : nat => forall n0 : nat, NatLe N0 n0 -> QltT e1 (projT1 (existT (fun u : Qseq => cauchy u) ux Hux) n0 - projT1 real_zero n0)) N1 HN1))).
    set (qn := projT1 (real_mult (real_mult (real_mult h I) (real_mult h I)) (real_plus real_one real_one)) n).
    set (pn := projT1 (real_plus (real_mult (real_mult half eps) (real_abs h)) eps') n).
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hepsn' : Qlt eps0 en').
    { unfold en'. apply (Qlt_le_trans _ (projT1 eps' n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (Hinvn : projT1 I n == Qinv xn).
    { unfold I, xn. cbn [real_inv_pos projT1].
      assert (Hl : Nat.leb N1 n = true) by (apply Nat.leb_le; exact Hn1).
      rewrite Hl. reflexivity. }
    assert (Hxn_pos : Qlt 0 xn).
    { unfold xn. apply (Qlt_le_trans _ (ux n - projT1 real_zero n) _).
      - apply (Qlt_trans 0 e1 (ux n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact He1.
        + apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    assert (Hxn_inv : xn * Qinv xn == 1).
    { apply (Qmult_inv_r xn).
      intro Hz. apply (Qlt_not_eq 0 xn Hxn_pos). apply Qeq_sym. exact Hz. }
    (* Unfolded assertion. *)
    assert (Hqn : qn == (hn * projT1 I n) * (hn * projT1 I n) * p2).
    { unfold qn, hn, p2.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult (real_mult h (I)) (real_mult h (I))) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult h (I)) (real_mult h (I)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj h (I) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    assert (Hp2 : p2 == 2).
    { unfold p2. setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)). cbn [projT1]. ring. }
    assert (Heps4 : projT1 (real_mult (real_mult half
                                                 half)
                            (real_mult eps (real_mult (existT (fun u : Qseq => cauchy u) ux Hux) (existT (fun u : Qseq => cauchy u) ux Hux)))) n == en * (xn * xn) / 4).
    { unfold en, xn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult half
                                                half)
                                     (real_mult eps (real_mult (existT (fun u : Qseq => cauchy u) ux Hux) (existT (fun u : Qseq => cauchy u) ux Hux))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj half
                                     half n)).
      unfold half. cbn [real_inv_pos real_plus real_one projT1].
      assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
      rewrite Hl.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_mult (existT (fun u : Qseq => cauchy u) ux Hux) (existT (fun u : Qseq => cauchy u) ux Hux)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (existT (fun u : Qseq => cauchy u) ux Hux) (existT (fun u : Qseq => cauchy u) ux Hux) n)).
      cbn [projT1]. unfold Qdiv. field. }
    (* |hn| ≤ en·xn²/4 (the HNd difference + d > 0). *)
    assert (Habs_le : Qle (Qabs hn) (en * (xn * xn) / 4)).
    { unfold hn, en, xn.
      set (aq := Qabs (projT1 h n)).
      apply Qlt_le_weak.
      apply (Qlt_le_trans _ ((en * (xn * xn) / 4) - aq + aq) _).
      - apply (Qle_lt_trans _ (0 + aq) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qplus_lt_le_compat 0 ((en * (xn * xn) / 4) - aq)
                                    (aq) (aq)).
          * apply (Qlt_trans 0 d ((en * (xn * xn) / 4) - aq)).
            -- apply QltT_to_Qlt. exact Hd.
            -- apply (Qlt_le_trans _ (projT1 (real_mult (real_mult half half) (real_mult eps (real_mult (existT (fun u : Qseq => cauchy u) ux Hux) (existT (fun u : Qseq => cauchy u) ux Hux)))) n - projT1 (real_abs h) n) _).
               ++ apply QltT_to_Qlt. exact (HNd n (NatLe_lift _ _ Hnd)).
               ++ apply QleT'_to_Qle. apply qeq_le.
               apply qeq_imp_qeqT.
                  setoid_rewrite Heps4.
                  setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
                  cbn [projT1]. reflexivity.
          * apply Qle_refl.
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_trans _ (en * (xn * xn) / 4 + 0) _).
        + apply (Qeq_trans _ (en * (xn * xn) / 4 + (Qopp aq + aq)) _).
          * apply Qeq_sym. apply (Qplus_assoc (en * (xn * xn) / 4) (Qopp aq) aq).
          * apply (Qplus_comp (en * (xn * xn) / 4) (en * (xn * xn) / 4) (Qeq_refl _)
                              (Qopp aq + aq) 0
                              (Qeq_trans (Qopp aq + aq) (aq + Qopp aq) 0
                                         (Qplus_comm (Qopp aq) aq) (Qplus_opp_r aq))).
        + apply (Qplus_0_r (en * (xn * xn) / 4)). }
    (* qn ≤ (en/2)·Qabs hn *)
    assert (Hqn_le : Qle qn ((en / 2) * Qabs hn)).
    { apply (Qle_trans _ (2 * (Qabs hn * Qabs hn) * (Qinv xn * Qinv xn)) _).
      - apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_trans _ ((hn * Qinv xn) * (hn * Qinv xn) * 2) _).
        + apply (Qeq_trans _ ((hn * projT1 I n) * (hn * projT1 I n) * p2) _).
          * exact Hqn.
          * setoid_rewrite <- Hinvn. setoid_rewrite <- Hp2. reflexivity.
        + apply (Qeq_trans _ (2 * (hn * hn) * (Qinv xn * Qinv xn)) _).
          * ring.
          * setoid_rewrite (qeqT_imp_qeq _ _ (q_sq_abs hn)). reflexivity.
      - apply QleT'_to_Qle. apply (q_quad_le_h_inv (Qabs hn) xn en (Qinv xn)).
        + apply Qle_to_QleT'. apply Qabs_nonneg.
        + apply Qle_to_QleT'. exact Habs_le.
        + apply Qle_to_QleT'. apply (Qinv_le_0_compat xn). apply Qlt_le_weak. exact Hxn_pos.
        + apply qeq_imp_qeqT. exact Hxn_inv. }
    (* pn == (en/2)·|hn| + en' (the inv2_n == /2 bridge). *)
    assert (Hpn_eq : pn == (en / 2) * Qabs hn + en').
    { unfold pn, hn, en, en'.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult half eps) (real_abs h)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult half eps) (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj half eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      unfold half. cbn [real_inv_pos real_plus real_one projT1].
      assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
      rewrite Hl.
      cbn [projT1]. unfold Qdiv. field. }
    (* Main chain: eps0 < en' ≤ pn − qn. *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ en' _).
    { exact Hepsn'. }
    { apply (Qle_trans _ (((en / 2) * Qabs hn + en') - (en / 2) * Qabs hn) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
      - apply (Qle_trans _ (pn - qn) _).
        { apply (Qplus_le_compat ((en / 2) * Qabs hn + en') pn
                                 (Qopp ((en / 2) * Qabs hn)) (Qopp qn)).
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hpn_eq. }
          { apply (Qopp_le_compat qn ((en / 2) * Qabs hn)). exact Hqn_le. } }
        { apply Qle_refl. } }
Qed.

(* ============ 23. Main-theorem auxiliary: abs compatibility of real_eq (D == X gives |D| == |X|) ============
   Pointwise: |Qabs(x_n) − Qabs(y_n)| ≤ Qabs(x_n − y_n) (Qabs_triangle_reverse on both sides + Qabs_Qle_condition).
   Qabs_Qle_condition : Qabs x ≤ y <-> −y ≤ x ≤ y. *)
Lemma real_abs_eq_compat : forall (x y : Real), real_eq x y -> real_eq (real_abs x) (real_abs y).
Proof.
  intros x y Hxy.
  unfold real_eq in *.
  intros eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 (real_abs x) n - projT1 (real_abs y) n))
                      (Qabs (projT1 x n - projT1 y n))
                      eps).
  - (* |Qabs(x_n) − Qabs(y_n)| ≤ Qabs(x_n − y_n) *)
    apply (Qle_trans (Qabs (projT1 (real_abs x) n - projT1 (real_abs y) n))
                     (Qabs (Qabs (projT1 x n) - Qabs (projT1 y n)))
                     (Qabs (projT1 x n - projT1 y n))).
    + (* Restatement: projT1 (real_abs x) n == Qabs (projT1 x n) (real_abs_proj). *)
      apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (real_abs x) n - projT1 (real_abs y) n)
                     (Qabs (projT1 x n) - Qabs (projT1 y n))).
      apply (Qplus_comp (projT1 (real_abs x) n) (Qabs (projT1 x n)) (qeqT_imp_qeq _ _ (real_abs_proj x n))
                        (Qopp (projT1 (real_abs y) n)) (Qopp (Qabs (projT1 y n)))
                        (Qopp_comp (projT1 (real_abs y) n) (Qabs (projT1 y n)) (qeqT_imp_qeq _ _ (real_abs_proj y n)))).
    + (* |Qabs x_n − Qabs y_n| ≤ Qabs(x_n − y_n): the two branches of Qabs_Qle_condition. *)
      apply (proj2 (Qabs_Qle_condition (Qabs (projT1 x n) - Qabs (projT1 y n)) (Qabs (projT1 x n - projT1 y n)))).
      split.
      { (* −|x−y| ≤ |x|−|y|: |y|−|x| ≤ |y−x| (triangle_reverse y x) + negating both sides + |y−x| == |x−y|. *)
        apply (Qle_trans _ (Qopp (Qabs (projT1 y n - projT1 x n))) _).
        { apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
          apply (Qopp_comp (Qabs (projT1 x n - projT1 y n)) (Qabs (projT1 y n - projT1 x n))).
          apply (Qeq_trans (Qabs (projT1 x n - projT1 y n))
                           (Qabs (Qopp (projT1 y n - projT1 x n)))
                           (Qabs (projT1 y n - projT1 x n))).
          - apply (Qabs_wd (projT1 x n - projT1 y n) (Qopp (projT1 y n - projT1 x n))).
            unfold Qminus. ring.
          - apply (Qabs_opp (projT1 y n - projT1 x n)). }
        { apply (Qle_trans (Qopp (Qabs (projT1 y n - projT1 x n)))
                           (Qopp (Qabs (projT1 y n) - Qabs (projT1 x n)))
                           (Qabs (projT1 x n) - Qabs (projT1 y n))).
          - apply (Qopp_le_compat (Qabs (projT1 y n) - Qabs (projT1 x n)) (Qabs (projT1 y n - projT1 x n))).
            apply (Qabs_triangle_reverse (projT1 y n) (projT1 x n)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. } }
      { (* |x|−|y| ≤ |x−y|: triangle_reverse x y. *)
        apply (Qabs_triangle_reverse (projT1 x n) (projT1 y n)). }
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.

(* ============ 24. Main theorem real_log_differentiable (Bishop per-eps) ============
   rdf x Hx := inv_pos x Hx.
   δ := min (x/2) (eps·x²/4).  Budget: 5×inv8·eps' (totalling 5eps'/8 ≤ eps').
   Structure:
     premise chain: |h|<δ gives |h|<x/2 (min_lt_l) gives |t|<1/2 (t_abs_lt_half)
              gives −1/2<t (abs_lt_lower) gives 1/2<1+t (half_lt_one_plus_t) gives 0<1+t (trans)
             |h|<eps4 (min_lt_r) gives the 22c premise
     D == X (log(x+h)−log x−inv x·h == log(1+t)−t, via opp_plus + assoc + real_log_plus_diff + mult_comm)
     upper bound X ≤ share (le_eps)
     lower bound −X ≤ 2t²+2share (chaining t_minus_log_bound + quad_div_le_two_eps)
     abs bridge: |X| ≤ 2t² + (share+2share) + share == 2t² + 4share
     22c: 2t² ≤ (eps/2)|h| + share
     summary: |D| ≤ |X| ≤ (eps/2)|h| + 5share ≤ eps|h| + eps' (5share ≤ eps' pointwise in the Q layer). *)
Lemma real_log_differentiable : forall (x : Real) (Hx : real_lt real_zero x),
  RealDifferentiable real_log.
Proof.
  intros x Hx.
  exists (fun y Hy => real_inv_pos y Hy).
  intros x0 Hx0 eps Heps.
  (* Constants. *)
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (four_inv := real_mult two_inv two_inv).
  set (eight_inv := real_mult four_inv two_inv).
  set (half_x := real_mult two_inv x0).
  set (eps_x2 := real_mult eps (real_mult x0 x0)).
  set (eps4 := real_mult four_inv eps_x2).      (* eps·x²/4 *)
  set (delta := real_min half_x eps4).
  exists delta.
  split.
  - (* 0 < delta: min_pos *)
    unfold delta, half_x, eps4, eps_x2, four_inv, two_inv.
    apply real_min_pos.
    + apply real_mult_positive.
      * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      * exact Hx0.
    + apply real_mult_positive.
      * apply real_mult_positive.
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      * apply real_mult_positive.
        -- exact Heps.
        -- apply real_mult_positive.
           ++ exact Hx0.
           ++ exact Hx0.
  - intros h Hh Hxh eps' Heps'.
    (* Budget share := inv8·eps' (shared across the five uses). *)
    set (share := real_mult eight_inv eps').
    assert (Hshare : real_lt real_zero share).
    { unfold share. apply real_mult_positive.
      - unfold eight_inv, four_inv, two_inv.
        apply real_mult_positive.
        + apply real_mult_positive.
          * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
          * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
        + apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      - exact Heps'. }
    (* t := h·inv x0 *)
    set (t := real_mult h (real_inv_pos x0 Hx0)).
    (* Premise chain. *)
    assert (Hh_half : real_lt (real_abs h) half_x).
    { apply (real_min_lt_l h half_x eps4). unfold delta. exact Hh. }
    assert (Ht_half : real_lt (real_abs t) two_inv).
    { unfold t. apply (real_t_abs_lt_half x0 h Hx0). exact Hh_half. }
    assert (Ht_lower : real_lt (real_opp two_inv) t).
    { apply (real_abs_lt_lower t two_inv). exact Ht_half. }
    assert (Hhalf_t : real_lt two_inv (real_plus real_one t)).
    { apply (real_half_lt_one_plus_t t). exact Ht_lower. }
    assert (Htpos : real_lt real_zero (real_plus real_one t)).
    { apply (real_lt_trans real_zero two_inv (real_plus real_one t)).
      - apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      - exact Hhalf_t. }
    assert (Hh_eps4 : real_lt (real_abs h) eps4).
    { apply (real_min_lt_r h half_x eps4). unfold delta. exact Hh. }
    (* X := log(1+t) − t *)
    set (X := real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
    (* Assert D == X. *)
    assert (HDX : real_eq
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
      X).
    {
      (* D == log(x0+h) + (opp(log x0) + opp(inv·h)): split by opp_plus. *)
      apply (real_eq_trans
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_plus (real_opp (real_log x0 Hx0))
                              (real_opp (real_mult (real_inv_pos x0 Hx0) h))))
        X).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))
                 (real_log (real_plus x0 h) Hxh)
                 (real_plus (real_opp (real_log x0 Hx0))
                            (real_opp (real_mult (real_inv_pos x0 Hx0) h)))).
        + apply real_eq_refl.
        + apply (real_opp_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)).
      - (* (log(x0+h) + (opplog + oppinv)) == (log(x0+h) − log x0) + (−inv·h): assoc *)
        apply (real_eq_trans
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_plus (real_opp (real_log x0 Hx0))
                                (real_opp (real_mult (real_inv_pos x0 Hx0) h))))
          (real_plus (real_plus (real_log (real_plus x0 h) Hxh) (real_opp (real_log x0 Hx0)))
                     (real_opp (real_mult (real_inv_pos x0 Hx0) h)))
          X).
        + apply (real_plus_assoc (real_log (real_plus x0 h) Hxh)
                                 (real_opp (real_log x0 Hx0))
                                 (real_opp (real_mult (real_inv_pos x0 Hx0) h))).
        + (* (log(x0+h) − log x0) + (−inv·h) == log(1+t) − t *)
          apply (RealSetoid.real_eq_plus_compat
                   (real_plus (real_log (real_plus x0 h) Hxh) (real_opp (real_log x0 Hx0)))
                   (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                   (real_log (real_plus real_one t) Htpos)
                   (real_opp t)).
          * (* log(x0+h) − log x0 == log(1+t): real_log_plus_diff *)
            apply (real_log_plus_diff x0 h Hx0 Hxh Htpos).
          * (* −inv·h == −t: mult_comm restatement + the definition of t. *)
            apply (real_eq_trans (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                                 (real_opp (real_mult h (real_inv_pos x0 Hx0)))
                                 (real_opp t)).
            -- apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_inv_pos x0 Hx0) h)
                       (real_mult h (real_inv_pos x0 Hx0))).
               apply (real_mult_comm (real_inv_pos x0 Hx0) h).
            -- apply real_eq_refl.
    }
    (* Upper bound: X ≤ share. *)
    assert (HXup : real_le X share).
    {
      apply (real_le_trans X (real_plus (real_plus t share) (real_opp t)) share).
      - (* X ≤ (t+share) − t: le_eps + plus_le_compat *)
        unfold X.
        apply (real_le_plus_compat (real_log (real_plus real_one t) Htpos) (real_plus t share)
                                   (real_opp t) (real_opp t)).
        + exact (real_log_one_plus_le_eps t share Htpos Hshare).
        + apply real_le_refl.
      - (* (t+share) − t ≤ share: eq_le, a ring identity. *)
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_plus (real_plus t share) (real_opp t))
                             (real_plus t (real_plus share (real_opp t)))
                             share).
        + apply real_eq_sym. apply (real_plus_assoc t share (real_opp t)).
        + apply (real_eq_trans (real_plus t (real_plus share (real_opp t)))
                               (real_plus (real_plus t (real_opp t)) share)
                               share).
          * apply (real_eq_trans (real_plus t (real_plus share (real_opp t)))
                                 (real_plus t (real_plus (real_opp t) share))
                                 (real_plus (real_plus t (real_opp t)) share)).
            -- apply (RealSetoid.real_eq_plus_compat t (real_plus share (real_opp t))
                                                       t (real_plus (real_opp t) share)).
               ++ apply real_eq_refl.
               ++ apply (real_plus_comm share (real_opp t)).
            -- apply (real_plus_assoc t (real_opp t) share).
          * apply (real_eq_trans (real_plus (real_plus t (real_opp t)) share)
                                 (real_plus real_zero share)
                                 share).
            -- apply (RealSetoid.real_eq_plus_compat (real_plus t (real_opp t)) share real_zero share).
               ++ apply (real_plus_opp t).
               ++ apply real_eq_refl.
            -- apply (real_eq_trans (real_plus real_zero share) (real_plus share real_zero) share).
               ** apply (real_plus_comm real_zero share).
               ** apply (real_plus_zero share).
    }
    (* Lower bound: −X ≤ 2t² + (share+share). *)
    assert (HXdown : real_le (real_opp X)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                 (real_plus share share))).
    {
      apply (real_le_trans (real_opp X)
                           (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                           (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
      - (* −X == t − log s: eq_le, restated by opp_plus. *)
        unfold X.
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_opp (real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)))
                             (real_plus (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t)))
                             (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))).
        + apply (real_opp_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
        + apply (real_eq_trans (real_plus (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t)))
                               (real_plus (real_opp (real_opp t)) (real_opp (real_log (real_plus real_one t) Htpos)))
                               (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))).
          * apply (real_plus_comm (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t))).
          * apply (RealSetoid.real_eq_plus_compat (real_opp (real_opp t))
                                                  (real_opp (real_log (real_plus real_one t) Htpos))
                                                  t
                                                  (real_opp (real_log (real_plus real_one t) Htpos))).
            -- apply (real_opp_opp t).
            -- apply real_eq_refl.
      - (* t − log s ≤ 2t² + share + share *)
        apply (real_le_trans (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                             (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos)) share)
                             (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
        + exact (real_t_minus_log_bound t share Htpos Hshare).
        + apply (real_le_trans (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos)) share)
                               (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) share) share)
                               (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
          * apply (real_le_plus_compat (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos))
                                       (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) share)
                                       share share).
            -- exact (real_quad_div_le_two_eps t (real_plus real_one t) share Htpos Hhalf_t Hshare).
            -- apply real_le_refl.
          * apply RealSetoid.real_eq_le.
            apply real_eq_sym. apply (real_plus_assoc (real_mult (real_mult t t) (real_plus real_one real_one)) share share).
    }
    (* abs bridge: |X| ≤ 2t² + (share + (share+share)) + share. *)
    assert (Habs : real_le (real_abs X)
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)).
    { apply (real_abs_le_quad_eps X t share (real_plus share share) share).
      - exact HXup.
      - exact HXdown.
      - exact Hshare.
      - (* 0 < share + share *)
        apply real_plus_positive; exact Hshare.
      - exact Hshare. }
    (* 22c: 2t² ≤ (eps/2)|h| + share *)
    assert (Hquad : real_le
      (real_mult (real_mult (real_mult h (real_inv_pos x0 Hx0)) (real_mult h (real_inv_pos x0 Hx0)))
                 (real_plus real_one real_one))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)).
    { apply (real_quad_t_le_h_eps x0 h eps share Hx0 Hh_eps4 Heps Hshare). }
    (* Summary 1: |D| == |X| (HDX + real_abs_eq_compat). *)
    assert (HabsD : real_le (real_abs
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)).
    {
      apply (real_le_trans (real_abs
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
                           (real_abs X)
                           (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                 (real_plus share (real_plus share share)))
                                      share)).
      - (* |D| == |X| ⟹ |D| ≤ |X|: real_abs_eq_compat + eq_le *)
        apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
          X).
        exact HDX.
      - exact Habs.
    }
    (* Summary 2: 2t² + C ≤ ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C). *)
    assert (Hmid : real_le
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                 (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
    {
      apply (real_le_trans
        (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                              (real_plus share (real_plus share share)))
                   share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_plus share (real_plus share share)) share))
        (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                   (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
      - (* (2t² + C') + share == 2t² + C (assoc backwards, C := C'+share). *)
        apply RealSetoid.real_eq_le.
        apply real_eq_sym.
        apply (real_plus_assoc (real_mult (real_mult t t) (real_plus real_one real_one))
                               (real_plus share (real_plus share share))
                               share).
      - (* 2t² + C ≤ ((eps/2)|h| + share) + C ≤ (eps/2)|h| + (share + C) *)
        apply (real_le_trans
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                     (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                     (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                     (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
        + (* 2t² + C ≤ ((eps/2)|h| + share) + C: plus_le_compat (Hquad + refl) *)
          apply (real_le_plus_compat
                   (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                   (real_plus (real_plus share (real_plus share share)) share)
                   (real_plus (real_plus share (real_plus share share)) share)).
          * exact Hquad.
          * apply real_le_refl.
        + (* ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C): assoc backwards. *)
          apply RealSetoid.real_eq_le.
          apply real_eq_sym.
          apply (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
                                 share
                                 (real_plus (real_plus share (real_plus share share)) share)).
    }
    (* Summary 3: finally (eps/2)|h| + 5share ≤ eps|h| + eps' — pointwise in the Bishop
       sense (the Or encoding cannot express a general non-strict ≤).
       The pointwise difference is (eps_n/2)|h_n| + (3/8)eps'_n ≥ (3/8)eps'_n > (3/8)e0' > 0,
       witnessed by (3/8)·e0'. *)
    assert (Hfinal : real_le
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                 (real_plus share (real_plus (real_plus share (real_plus share share)) share)))
      (real_plus (real_mult eps (real_abs h)) eps')).
    {
      destruct real_two_pos_local as [e2 [He2 [N2 HN2]]].
      destruct Heps as [e0 [He0 [N0 HN0]]].
      destruct Heps' as [e0' [He0' [N0' HN0']]].
      set (eps0q := Qmult (Qmake 3 8) e0').
      assert (Heps0q : QltT 0 eps0q).
      { apply Qlt_to_QltT. unfold eps0q.
        apply (Qmult_lt_0_compat (Qmake 3 8) e0').
        - (* 0 < 3/8: 0·8 < 3·1 *)
          simpl. reflexivity.
        - apply QltT_to_Qlt. exact He0'. }
      apply (RealSetoid.real_lt_le_iff_req _ _). left.
      unfold real_lt.
      exists eps0q.
      split.
      - exact Heps0q.
      - exists (Nat.max N0' (Nat.max N2 N0)).
        intros n Hn.
        apply NatLe_drop in Hn.
        assert (Hn0' : (N0' <= n)%nat) by lia.
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn0 : (N0 <= n)%nat) by lia.
        set (hn := projT1 h n).
        set (en := projT1 eps n).
        set (en' := projT1 eps' n).
        set (inv2n := projT1 two_inv n).
        set (inv8n := projT1 eight_inv n).
        (* Unfolded assertion. *)
        assert (Hinv2 : inv2n == Qinv 2).
        { unfold inv2n, two_inv.
          cbn [real_inv_pos real_plus real_one projT1].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl. reflexivity. }
        assert (Hinv8 : inv8n == Qinv 8).
        { unfold inv8n, eight_inv, four_inv, two_inv.
          cbn [real_inv_pos real_plus real_one projT1 real_mult].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl. unfold Qdiv. field. }
        assert (Heps0'n : Qlt e0' en').
        { apply (Qlt_le_trans _ (en' - projT1 real_zero n) _).
          - apply QltT_to_Qlt. exact (HN0' n (NatLe_lift _ _ Hn0')).
          - apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
            assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
            rewrite Hz. ring. }
        assert (Heps0n : Qlt e0 en).
        { apply (Qlt_le_trans _ (en - projT1 real_zero n) _).
          - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
          - apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
            assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
            rewrite Hz. ring. }
        (* A_n, B_n projection unfolding. *)
        assert (HA : projT1
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                     (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n
          == (inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))).
        { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult two_inv eps) (real_abs h))
                                         (real_plus share (real_plus (real_plus share (real_plus share share)) share)) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult two_inv eps) (real_abs h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj two_inv eps n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj share (real_plus (real_plus share (real_plus share share)) share) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus share (real_plus share share)) share n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj share (real_plus share share) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj share share n)).
          unfold share.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eight_inv eps' n)).
          unfold eight_inv.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj four_inv two_inv n)).
          unfold four_inv.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj two_inv two_inv n)).
          unfold hn, en, en', inv2n, inv8n.
          unfold share, eight_inv, four_inv, two_inv.
          cbn [projT1 real_inv_pos real_plus real_one real_mult real_abs].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl.
          set (aq := Qabs (projT1 h n)). unfold Qdiv. field. }
        (* Main chain: eps0q < B_n − A_n. *)
        apply Qlt_to_QltT.
        apply (Qlt_le_trans _ ((en / 2) * Qabs hn + (Qmake 3 8) * en') _).
        { (* eps0q < (en/2)|hn| + (3/8)en' *)
          apply (Qlt_le_trans _ ((Qmake 3 8) * en') _).
          { (* (3/8)e0' < (3/8)en': en' > e0', by mult_lt_l. *)
            unfold eps0q.
            assert (H38 : Qlt 0 (Qmake 3 8)) by (simpl; reflexivity).
            apply (proj2 (Qmult_lt_l e0' en' (Qmake 3 8) H38)).
            exact Heps0'n. }
          { (* (3/8)en' ≤ (en/2)|hn| + (3/8)en': 0 ≤ (en/2)|hn| *)
            apply (Qle_trans ((Qmake 3 8) * en')
                             ((Qmake 3 8) * en' + (en / 2) * Qabs hn)
                             ((en / 2) * Qabs hn + (Qmake 3 8) * en')).
            { apply (Qle_plus_nonneg_r ((Qmake 3 8) * en') ((en / 2) * Qabs hn)).
              apply (Qmult_le_compat_nonneg 0 (en / 2) 0 (Qabs hn)).
              { split. apply Qle_refl.
                apply (Qmult_le_compat_nonneg 0 en 0 (Qinv 2)).
                { split. apply Qle_refl. apply Qlt_le_weak. apply (Qlt_trans 0 e0 en). apply QltT_to_Qlt. exact He0. exact Heps0n. }
                { split. apply Qle_refl. apply Qlt_le_weak. simpl. reflexivity. } }
              { split. apply Qle_refl. apply Qabs_nonneg. } }
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qplus_comm ((Qmake 3 8) * en') ((en / 2) * Qabs hn)). } }
          }
        { (* (en/2)|hn| + (3/8)en' ≤ B_n − A_n: unfolding + field. *)
          apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
          (* B_n unfolded. *)
          assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
          { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            cbn [projT1]. unfold hn, en, en'. ring. }
          (* Main chain: M == B_n − A_n. *)
          apply (Qeq_trans ((en / 2) * Qabs hn + (Qmake 3 8) * en')
                           ((en * Qabs hn + en') - ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                           (projT1 (real_plus (real_mult eps (real_abs h)) eps') n - projT1
                             (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                        (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)).
          - (* M == the unfolded form: rewrite Hinv2/Hinv8 + field. *)
            rewrite Hinv2. rewrite Hinv8.
            unfold Qdiv. field.
          - (* the unfolded form == B_n − A_n: plus_comp (HB + HA backwards). *)
            apply (Qplus_comp (en * Qabs hn + en') (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                              (Qeq_sym _ _ HB)
                              (Qopp ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                              (Qopp (projT1 (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                                       (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n))
                              (Qopp_comp ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en')))))
                                         (projT1 (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                                            (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)
                                         (Qeq_sym _ _ HA))).
        }
    }
    (* Assembly. *)
    apply (real_le_trans _ (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                      (real_plus share (real_plus (real_plus share (real_plus share share)) share))) _).
    { apply (real_le_trans _ (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                   (real_plus share (real_plus share share)))
                                        share) _).
      - exact HabsD.
      - exact Hmid. }
    { exact Hfinal. }
Qed.

End LogDiffPhase4.

(* ============================================================ *)
(* Real-layer entropy: the RealDifferentiable composition lemma family.       *)
(* Includes the mult-budget lemma (real_differentiable_mult).                 *)
(* Dependencies: the RealDifferentiable record of LogDiffPhase4 above.        *)
(* ============================================================ *)

Open Scope Q_scope.

Opaque Qred.

