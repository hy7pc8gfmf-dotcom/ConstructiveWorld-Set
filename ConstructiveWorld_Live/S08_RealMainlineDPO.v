(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* S08_RealMainlineDPO.v                                       *)
(*                                                             *)
(* 目的：Real 层 DPO/RLHF 主线：奖励恢复、注意力稳态、Top-K、    *)
(*       PPO 保守性与 eps 化最优性（构造性 Set 层）。            *)
(* 主件：real_steady_state_boltzmann_attn（Boltzmann 注意力稳态  *)
(*       方程）；real_rlhf_optimal_eps（J(π) := −F(π) ≤          *)
(*       J(π⋆) + D·eps，eps 加权残差形态）。                     *)
(* 依赖：S01–S07；Stdlib（QArith、List、Bool、Arith、Setoid、    *)
(*       Morphisms、Lia）。                                      *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 拆分模块之一，原文区间 *)
(*       L41233-L46820，去头正文与原文区间逐字节同源；抽象求和   *)
(*       以显式接口变量呈现（求和外延/线性，可实例化）。         *)
(* ============================================================ *)
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
(* ============ 1. real_opp_mult：opp (mult a b) == mult a (opp b) ============
   逐点：−(a_n·b_n) == a_n·(−b_n)（Q ring）。
   E143 #76：real_eq_of_zero_diff + destruct + simpl + ring。 *)
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

(* ============ 2. real_opp_mult_r：opp (mult a b) == mult (opp a) b ============ *)
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

(* ============ 3. real_mult_opp_l：mult a (opp b) == opp (mult a b)（反向） ============ *)
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
(* ============ Gibbs 逐点核心并入（，来自检验 _dbg_gibbs4.v 5 Qed 全部通过） ============
   real_mult_div（p·(q/p) == q，inv_correct 抽象链）、real_opp_opp（opp 对合）、
   real_hpq1（p−q == p·(−(q/p−1))）、real_hpq2（p·(−X) == p·(−(X+eps)) + p·eps）、
   real_gibbs_core_eps（p−q ≤ p·(−log(q/p)) + p·eps——Gibbs 逐点核心）。
   paper-2 §9.2/§10.2 Gibbs 不等式 Real 层逐 eps 版的核心块（判例组）。 *)
Section GibbsCoreMain.
(* ============ 1. p·(q/p) == q（inv_correct 抽象链） ============ *)
Lemma real_mult_div : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  (* p·(q·(1/p)) == (p·q)·(1/p) == (q·p)·(1/p) == q·(p·(1/p)) == q·1 == q *)
  apply (real_eq_trans _ (real_mult (real_mult p q) (real_inv_pos p Hp)) _).
  - (* p·(q·(1/p)) == (p·q)·(1/p)：assoc 直接（p·(q·inv)==(p·q)·inv） *)
    exact (real_mult_assoc p q (real_inv_pos p Hp)).
  - (* (p·q)·(1/p) == q：链 *)
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

(* ============ 2. real_opp_opp：opp (opp x) == x（逐点 ring） ============ *)
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

(* ============ 3. Hpq1：p−q == p·(−(q/p−1)) ============
   抽象层链：p·(−X) == −(p·X) == −(q−p) == p−q，X := q/p−1。
   中间：p·X == q−p（distrib + mult_div + opp_mult + mult_one）。 *)
Lemma real_hpq1 : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_plus p (real_opp q))
          (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))).
Proof.
  intros p q Hp.
  apply real_eq_sym.
  (* ① 中间：p·(q/p−1) == q−p *)
  assert (Hmid : real_eq (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))
                         (real_plus q (real_opp p))).
  { (* p·(q/p−1) == p·(q/p) + p·(−1) == q + −p *)
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
  (* ② 目标：p·(−X) == p−q。p·(−X) == −(p·X)（opp_mult 反向）== −(q−p) == p−q *)
  apply (real_eq_trans _ (real_opp (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))) _).
  - apply (real_eq_sym (real_opp (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))
                       (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))).
    apply (real_opp_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))).
  - (* −(p·X) == p−q：经 Hmid（p·X == q−p）+ −(q−p)==p−q *)
    apply (real_eq_trans _ (real_opp (real_plus q (real_opp p))) _).
    + apply (RealSetoid.real_eq_opp_compat (real_mult p (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)))
                                           (real_plus q (real_opp p))).
      exact Hmid.
    + (* −(q−p) == p−q：opp_plus + opp_opp + comm *)
      apply (real_eq_trans _ (real_plus (real_opp q) (real_opp (real_opp p))) _).
      * apply (real_opp_plus q (real_opp p)).
      * apply (real_eq_trans _ (real_plus (real_opp q) p) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_opp q) (real_opp (real_opp p))
                                                 (real_opp q) p).
           ++ apply real_eq_refl.
           ++ apply (real_opp_opp p).
        -- apply (real_plus_comm (real_opp q) p).
Qed.

(* ============ 4. Hpq2（E179）：p·(−X) == p·(−(X+eps)) + p·eps，X := q/p−1 ============ *)
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

(* ============ 5. 组装：real_gibbs_core_eps（p−q ≤ p·(−log(q/p)) + p·eps） ============ *)
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
  (* 3. le_mult_compat：A·p ≤ B·p（A := −(q/p−1+eps)，B := −log(q/p)） *)
  assert (Hmult : real_le (real_mult (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)) p)
                          (real_mult (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                         (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))) p)).
  { apply (real_le_mult_compat (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps))
                               (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                   (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
                               p).
    - exact Hp.
    - exact Hopp. }
  (* 4. 组装：p−q == p·(−(q/p−1))（real_hpq1）
        == p·(−(q/p−1+eps)) + p·eps（real_hpq2）
        ≤ p·(−log(q/p)) + p·eps（Hmult comm 桥 + le_plus_compat）
     链：p−q ≤ p·B + p·eps，其中 p·B = B·p（comm） *)
  apply (real_le_trans (real_plus p (real_opp q))
                       (real_plus (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                                  (real_mult p eps))
                       (real_plus (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                   (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
                                  (real_mult p eps))).
  - (* p−q ≤ p·(−(q/p−1+eps)) + p·eps：p−q == p·(−(q/p−1)) == p·(−(q/p−1+eps)) + p·eps（hpq1+hpq2） *)
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (real_plus p (real_opp q))
                         (real_mult p (real_opp (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))))
                         (real_plus (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                                    (real_mult p eps))).
    + apply (real_hpq1 p q Hp).
    + apply (real_hpq2 p q eps Hp).
  - (* p·(−(q/p−1+eps)) + p·eps ≤ p·(−log(q/p)) + p·eps：le_plus_compat（Hmult comm 桥） *)
    apply (real_le_plus_compat (real_mult p (real_opp (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one)) eps)))
                               (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                                (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))))
                               (real_mult p eps) (real_mult p eps)).
    + (* p·A ≤ p·B：Hmult 给 A·p ≤ B·p，comm 桥 *)
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

(* ============ 0. real_list_sum：Fixpoint fold real_plus（nil → real_zero） ============ *)
Fixpoint real_list_sum (f : X -> Real) (l : list X) : Real :=
  match l with
  | nil => real_zero
  | w :: rest => real_plus (f w) (real_list_sum f rest)
  end.

(* ============ 1. real_list_sum_ext：逐点 real_eq ⟹ 求和 real_eq ============ *)
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

(* ============ 2. real_plus_swap_mid：(a+b)+(c+d) == (a+c)+(b+d) ============ *)
Lemma real_plus_swap_mid : forall (a b c d : Real),
  real_eq (real_plus (real_plus a b) (real_plus c d))
          (real_plus (real_plus a c) (real_plus b d)).
Proof.
  intros a b c d.
  (* (a+b)+(c+d) == a+(b+(c+d)) [assoc 反向] == a+((c+d)+b) [comm]
     == a+(c+(d+b)) [assoc 反向] == a+(c+(b+d)) [comm] == (a+c)+(b+d) [assoc] *)
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

(* ============ 3. real_list_sum_add：Σ(f+g) == Σf + Σg ============ *)
Lemma real_list_sum_add : forall (f g : X -> Real) (l : list X),
  real_eq (real_list_sum (fun w => real_plus (f w) (g w)) l)
          (real_plus (real_list_sum f l) (real_list_sum g l)).
Proof.
  intros f g l.
  induction l as [| w rest IH]; simpl.
  - (* zero == zero + zero *)
    apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - (* (f w + g w) + (Σf_rest + Σg_rest) == (f w + Σf_rest) + (g w + Σg_rest) *)
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

(* ============ 4. real_list_sum_linear：Σ(a·f w) == a·Σf ============ *)
Lemma real_list_sum_linear : forall (a : Real) (f : X -> Real) (l : list X),
  real_eq (real_list_sum (fun w => real_mult a (f w)) l)
          (real_mult a (real_list_sum f l)).
Proof.
  intros a f l.
  induction l as [| w rest IH]; simpl.
  - (* zero == a·zero *)
    apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - (* a·f w + a·Σf_rest == a·(f w + Σf_rest)：distrib 反向 *)
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

(* ============ 5. real_list_sum_linear_r：Σ(f w·a) == a·Σf（常数在右） ============ *)
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

(* ============ 6. real_opp_zero + real_list_sum_opp：Σ(opp f) == opp(Σf) ============ *)
Lemma real_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  (* opp zero == (opp zero)+zero [plus_zero 反向] == zero+(opp zero) [comm 反向]
     == zero [plus_opp] *)
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
  - (* (opp f w) + (opp Σf_rest) == opp (f w + Σf_rest) *)
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

(* ============ 7. real_list_sum_le：逐点 real_le ⟹ 求和 real_le ============ *)
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

(* ============ 8. real_list_sum_nonneg：逐点 0 ≤ f w ⟹ 0 ≤ Σf ============ *)
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
(* ============ 8b. real_list_sum_pos：逐点 0 < f w 且 l 非空 ⟹ 0 < Σf ============
   （strict 版。Real 层有限列表和的正性真定理——L21132/L17000 注释
   「Real 层有限和可实例化」的文件内背书：一旦以具体有限状态表
   （list X + real_list_sum）实例化 Section Alignment，sum_over_S_pos /
   Z_align_pos 的 Real 层佐证即此形态。sTB3 论证 C1， 并入） *)
Lemma real_list_sum_pos : forall (f : X -> Real) (l : list X),
  (forall w : X, real_lt real_zero (f w)) ->
  l <> nil ->
  real_lt real_zero (real_list_sum f l).
Proof.
  intros f l Hf Hnn.
  induction l as [| w rest IH].
  - (* nil：和 == real_zero；由非空假设 l <> nil 矛盾（eq_refl） *)
    simpl. exfalso. exact (Hnn eq_refl).
  - (* w :: rest：按 rest 是否为空分情形 *)
    destruct rest as [| w' rest'].
    + (* 单元素：和 == f w + real_zero == f w（real_lt_id_r + real_plus_zero） *)
      simpl.
      apply (RealSetoid.real_lt_id_r real_zero (f w) (real_plus (f w) real_zero)).
      * apply (real_eq_sym (real_plus (f w) real_zero) (f w)).
        apply (real_plus_zero (f w)).
      * exact (Hf w).
    + (* 多元素：f w 与（尾和）皆正（real_lt_id_l：0 == 0+0 + real_lt_plus_compat） *)
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

(* ============ 9. real_kl_term：p·(−log(q/p))（与 real_gibbs_core_eps RHS 定义等价） ============ *)
Definition real_kl_term (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q) : Real :=
  real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                  (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))).

(* ============ 10. real_gibbs_inequality_eps：0 ≤ Σ_s p s·(−log(q s/p s)) + eps
   （KL ≥ 0 Real 层逐 eps，具体 list 状态空间）
   逐点 core（real_gibbs_core_eps）+ 求和保序（real_list_sum_le）
   + 归一化（Σp==1、Σq==1 ⟹ Σ(p−q)==0）+ 误差累积（Σ(p·eps)==eps） *)
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
  (* 1. 逐点求和：Σ(p−q) ≤ Σ(KL) + Σ(p·eps)（real_list_sum_le + real_gibbs_core_eps） *)
  assert (Hsum : real_le (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                         (real_list_sum (fun s => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                                           (real_mult (p s) eps)) l)).
  { apply real_list_sum_le.
    intro s.
    exact (real_gibbs_core_eps (p s) (q s) (Hp s) (Hq s) eps Hepspos). }
  (* 2. Σ(p−q) == 0：add + opp + 归一化 + plus_opp *)
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
  (* 3. Σ(p·eps) == eps：linear_r + 归一化 + mult_one *)
  assert (Heps : real_eq (real_list_sum (fun s => real_mult (p s) eps) l) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum p l)) _).
    - apply (real_list_sum_linear_r eps p l).
    - apply (real_eq_trans _ (real_mult eps real_one) _).
      + apply (RealSetoid.real_eq_mult_compat eps (real_list_sum p l) eps real_one).
        * apply real_eq_refl.
        * exact Hnormp.
      + apply (real_mult_one eps).
  }
  (* 4a. Σ(KL+per) == KLsum + SumPE（add） *)
  assert (Hadd : real_eq (real_list_sum (fun s => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                                           (real_mult (p s) eps)) l)
                         (real_plus KLsum SumPE)).
  { unfold KLsum, SumPE.
    apply (real_list_sum_add (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                             (fun s => real_mult (p s) eps) l). }
  (* 4b. Σ(p−q) ≤ KLsum + SumPE（id_r 替换 Hsum 的 RHS） *)
  assert (Hsum2 : real_le (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                          (real_plus KLsum SumPE)).
  { apply (RealSetoid.real_le_id_r (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                                   (real_list_sum (fun s => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                                                     (real_mult (p s) eps)) l)
                                   (real_plus KLsum SumPE) Hadd Hsum). }
  (* 4c. KLsum + SumPE == KLsum + eps（Heps） *)
  assert (Hplus : real_eq (real_plus KLsum SumPE) (real_plus KLsum eps)).
  { apply (RealSetoid.real_eq_plus_compat KLsum SumPE KLsum eps).
    - apply real_eq_refl.
    - unfold SumPE. exact Heps. }
  (* 4d. Σ(p−q) ≤ KLsum + eps *)
  assert (Hsum' : real_le (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                          (real_plus KLsum eps)).
  { apply (RealSetoid.real_le_id_r (real_list_sum (fun s => real_plus (p s) (real_opp (q s))) l)
                                   (real_plus KLsum SumPE) (real_plus KLsum eps) Hplus Hsum2). }
  (* 5. 0 ≤ Σ(p−q) ≤ KLsum + eps（trans + eq_le） *)
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

(* ============ 1. 分母正性：0 < 1 + e^{-x} ============ *)
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

(* ============ 2. real_sigmoid：σ(x) = 1/(1+e^{-x}) ============ *)
Definition real_sigmoid (x : Real) : Real :=
  real_inv_pos (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x).

(* ============ 3. 0 < 1+1（σ(0) 分母） ============ *)
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

(* ============ 4. sigmoid 正性：0 < σ(x) ============ *)
Lemma real_sigmoid_pos : forall x : Real,
  real_lt real_zero (real_sigmoid x).
Proof.
  intro x. unfold real_sigmoid. apply real_inv_pos_pos.
Qed.

(* ============ 5. sigmoid 严格递增：x < y ⟹ σ x < σ y ============ *)
Lemma real_sigmoid_strict_inc : forall x y : Real,
  real_lt x y -> real_lt (real_sigmoid x) (real_sigmoid y).
Proof.
  intros x y Hxy.
  unfold real_sigmoid.
  (* exp_neg_decr：x < y ⟹ e^{-y} < e^{-x} *)
  assert (Hexp : real_lt (real_exp_neg y) (real_exp_neg x))
    by exact (real_exp_neg_decr x y Hxy).
  (* 分母：1 + e^{-y} < 1 + e^{-x}（le one one + Hexp 混合保序） *)
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

(* ============ 6. σ(0) = 1/(1+1)（inv_pos_ext 折叠） ============ *)
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

(* ============ 1. real_eq_plus_cancel_l：a+b == a+c ⟹ b == c（抽象链） ============ *)
Lemma real_eq_plus_cancel_l : forall (a b c : Real),
  real_eq (real_plus a b) (real_plus a c) -> real_eq b c.
Proof.
  intros a b c Habc.
  (* b == (a+b)+(−a) == (a+c)+(−a) == c *)
  apply (real_eq_trans _ (real_plus (real_plus a b) (real_opp a)) _).
  - (* b == (a+b)+(−a) *)
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
           ++ (* zero+b == b *)
              apply (real_eq_sym b (real_plus real_zero b)).
              apply (real_eq_trans _ (real_plus b real_zero) _).
              ** apply (real_eq_sym (real_plus b real_zero) b).
                 apply (real_plus_zero b).
              ** apply (real_plus_comm b real_zero).
  - (* (a+b)+(−a) == (a+c)+(−a) == c *)
    apply (real_eq_trans _ (real_plus (real_plus a c) (real_opp a)) _).
    + apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                                            (real_plus a c) (real_opp a)).
      * exact Habc.
      * apply real_eq_refl.
    + (* (a+c)+(−a) == c，对称链 *)
      apply (real_eq_sym c (real_plus (real_plus a c) (real_opp a))).
      apply (real_eq_trans _ (real_plus a (real_plus c (real_opp a))) _).
      * (* c == a+(c+−a)：c == zero+c == (a+−a)+c == a+(−a+c) == a+(c+−a) *)
        apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) c)) _).
        -- (* c == a+(−a+c) *)
           apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) c) _).
           ++ (* c == (a+−a)+c *)
              apply (real_eq_trans _ (real_plus real_zero c) _).
              ** (* c == zero+c *)
                  apply (real_eq_sym (real_plus real_zero c) c).
                  apply (real_eq_trans _ (real_plus c real_zero) _).
                  --- apply (real_eq_sym (real_plus c real_zero) (real_plus real_zero c)).
                      apply (real_plus_comm c real_zero).
                  --- apply (real_plus_zero c).
              ** (* zero+c == (a+−a)+c *)
                 apply (RealSetoid.real_eq_plus_compat real_zero c (real_plus a (real_opp a)) c).
                 --- apply (real_eq_sym (real_plus a (real_opp a)) real_zero).
                     apply (real_plus_opp a).
                 --- apply real_eq_refl.
           ++ (* (a+−a)+c == a+(−a+c) *)
               apply (real_eq_sym (real_plus a (real_plus (real_opp a) c)) (real_plus (real_plus a (real_opp a)) c)).
               apply (real_plus_assoc a (real_opp a) c).
         -- (* a+(−a+c) == a+(c+−a) *)
           apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp a) c)
                                                 a (real_plus c (real_opp a))).
           ++ apply real_eq_refl.
           ++ apply (real_plus_comm (real_opp a) c).
      * (* a+(c+−a) == (a+c)+−a：assoc 正向 *)
        apply (real_plus_assoc a c (real_opp a)).
Qed.

(* ============ 2. real_eq_mult_cancel_r：a·c == b·c，c>0 ⟹ a == b（抽象链） ============ *)
Lemma real_eq_mult_cancel_r : forall (a b c : Real) (Hc : real_lt real_zero c),
  real_eq (real_mult a c) (real_mult b c) -> real_eq a b.
Proof.
  intros a b c Hc Habc.
  (* a == (a·c)·(inv c) == (b·c)·(inv c) == b *)
  apply (real_eq_trans _ (real_mult (real_mult a c) (real_inv_pos c Hc)) _).
  - (* a == (a·c)·(inv c) *)
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
  - (* (a·c)·(inv c) == (b·c)·(inv c) == b *)
    apply (real_eq_trans _ (real_mult (real_mult b c) (real_inv_pos c Hc)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult a c) (real_inv_pos c Hc)
                                            (real_mult b c) (real_inv_pos c Hc)).
      * exact Habc.
      * apply real_eq_refl.
    + (* (b·c)·(inv c) == b，对称 *)
      apply (real_eq_sym b (real_mult (real_mult b c) (real_inv_pos c Hc))).
      apply (real_eq_trans _ (real_mult b (real_mult c (real_inv_pos c Hc))) _).
      * (* b == b·(c·inv c)：b == b·1 == b·(c·inv c) *)
        apply (real_eq_trans _ (real_mult b real_one) _).
        -- apply (real_eq_sym (real_mult b real_one) b).
           apply (real_mult_one b).
        -- apply (RealSetoid.real_eq_mult_compat b real_one b (real_mult c (real_inv_pos c Hc))).
           ++ apply real_eq_refl.
           ++ apply (real_eq_sym (real_mult c (real_inv_pos c Hc)) real_one).
              apply (real_inv_pos_correct c Hc).
      * (* b·(c·inv c) == (b·c)·inv c：assoc 正向 *)
        apply (real_mult_assoc b c (real_inv_pos c Hc)).
Qed.

(* ============ 3. real_inv_inv：inv (inv x) == x（mult_cancel_r） ============ *)
Lemma real_inv_inv : forall (x : Real) (Hx : real_lt real_zero x)
  (Hx' : real_lt real_zero (real_inv_pos x Hx)),
  real_eq (real_inv_pos (real_inv_pos x Hx) Hx') x.
Proof.
  intros x Hx Hx'.
  apply (real_eq_mult_cancel_r (real_inv_pos (real_inv_pos x Hx) Hx') x
                               (real_inv_pos x Hx) Hx').
  apply (real_eq_trans _ real_one _).
  - (* inv(inv x)·inv x == 1 *)
    apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) (real_inv_pos (real_inv_pos x Hx) Hx')) _).
    + apply (real_mult_comm (real_inv_pos (real_inv_pos x Hx) Hx') (real_inv_pos x Hx)).
    + apply (real_inv_pos_correct (real_inv_pos x Hx) Hx').
  - (* x·inv x == 1（反向） *)
    apply (real_eq_sym (real_mult x (real_inv_pos x Hx)) real_one).
    apply (real_inv_pos_correct x Hx).
Qed.

(* ============ 4. real_exp_neg_opp_log：e^{−log x} == inv x（x>0）
   锚点：e^{−log x}·x == e^{−log x}·e^{log x} == e^{−log x + log x} == e^0 == 1
   == inv x·x，mult_cancel_r ⟹ e^{−log x} == inv x。 *)
Lemma real_exp_neg_opp_log : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (cauchy_real_exp (real_opp (real_log x Hx))) (real_inv_pos x Hx).
Proof.
  intros x Hx.
  apply (real_eq_mult_cancel_r (cauchy_real_exp (real_opp (real_log x Hx)))
                               (real_inv_pos x Hx) x Hx).
  apply (real_eq_trans _ real_one _).
  - (* e^{−log x}·x == 1 *)
    apply (real_eq_trans _ (real_mult (cauchy_real_exp (real_opp (real_log x Hx)))
                                      (cauchy_real_exp (real_log x Hx))) _).
    + (* x == e^{log x} 替换 *)
      apply (RealSetoid.real_eq_mult_compat (cauchy_real_exp (real_opp (real_log x Hx))) x
                                            (cauchy_real_exp (real_opp (real_log x Hx)))
                                            (cauchy_real_exp (real_log x Hx))).
      * apply real_eq_refl.
      * apply (real_eq_sym (cauchy_real_exp (real_log x Hx)) x).
        apply (cw_log_exp_right x Hx).
    + (* e^{−log x}·e^{log x} == e^{−log x+log x} == e^0 == 1 *)
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
  - (* inv x·x == 1 *)
    apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx)) _).
    + (* 1 == x·inv x *)
      apply (real_eq_sym (real_mult x (real_inv_pos x Hx)) real_one).
      apply (real_inv_pos_correct x Hx).
    + (* x·inv x == inv x·x *)
      apply (real_mult_comm x (real_inv_pos x Hx)).
Qed.

(* ============ 5. real_log_sigmoid_zero_neg：−log σ(0) == log 2（锚点法）
   e^{−log σ0} == inv σ0 == inv(inv 2) == 2 == e^{log 2}，弱三分 ⟹ 相等。 *)
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
    + (* e^L == inv σ0 == inv(inv 2) == 2 == e^R *)
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
    + (* e^R == 2 == inv(inv 2) == inv σ0 == e^L *)
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

(* ============ 6. real_dpo_sigmoid_loss_bounded：r_l < r_w ⟹ −log σ(r_w−r_l) < log 2
   = dpo_loss_at_pi_star 化简后 DPO 有界性的数学核心。 *)
Lemma real_dpo_sigmoid_loss_bounded :
  forall (r_w r_l : Real),
    real_lt r_l r_w ->
    real_lt (real_opp (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                (real_sigmoid_pos (real_plus r_w (real_opp r_l)))))
            (real_log (real_plus real_one real_one) real_two_pos).
Proof.
  intros r_w r_l Hrw.
  (* 1. 0 < r_w − r_l（r_l < r_w ⟹ r_l+(−r_l) < r_w+(−r_l)，0 == r_l+(−r_l)） *)
  assert (Hpos : real_lt real_zero (real_plus r_w (real_opp r_l))).
  { apply (RealSetoid.real_lt_id_l real_zero (real_plus r_l (real_opp r_l))
                                  (real_plus r_w (real_opp r_l))).
    - apply (real_eq_sym (real_plus r_l (real_opp r_l)) real_zero).
      apply (real_plus_opp r_l).
    - apply (real_lt_plus_compat_lt_le r_l r_w (real_opp r_l) (real_opp r_l)).
      + exact Hrw.
      + apply real_le_refl.
  }
  (* 2. σ 0 < σ(r_w−r_l)（sigmoid_strict_inc） *)
  assert (Hsig : real_lt (real_sigmoid real_zero)
                         (real_sigmoid (real_plus r_w (real_opp r_l))))
    by exact (real_sigmoid_strict_inc real_zero (real_plus r_w (real_opp r_l)) Hpos).
  (* 3. log σ0 < log σ(r_w−r_l)（real_log_lt_mono） *)
  assert (Hlog : real_lt (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero))
                         (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                   (real_sigmoid_pos (real_plus r_w (real_opp r_l))))).
  { apply (real_log_lt_mono (real_sigmoid real_zero)
                            (real_sigmoid (real_plus r_w (real_opp r_l)))
                            (real_sigmoid_pos real_zero)
                            (real_sigmoid_pos (real_plus r_w (real_opp r_l)))
                            Hsig). }
  (* 4. −log σ(r_w−r_l) < −log σ0（opp_lt_compat） *)
  assert (Hopp : real_lt (real_opp (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                              (real_sigmoid_pos (real_plus r_w (real_opp r_l)))))
                         (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))).
  { apply (real_opp_lt_compat (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero))
                              (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                        (real_sigmoid_pos (real_plus r_w (real_opp r_l))))
                              Hlog). }
  (* 5. −log σ0 == log 2 *)
  assert (Hval : real_eq (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
                         (real_log (real_plus real_one real_one) real_two_pos))
    by exact (real_log_sigmoid_zero_neg).
  (* 6. 组装：−log σ(r_w−r_l) < log 2（lt_id_r 替换） *)
  apply (RealSetoid.real_lt_id_r (real_opp (real_log (real_sigmoid (real_plus r_w (real_opp r_l)))
                                                      (real_sigmoid_pos (real_plus r_w (real_opp r_l)))))
                                 (real_opp (real_log (real_sigmoid real_zero) (real_sigmoid_pos real_zero)))
                                 (real_log (real_plus real_one real_one) real_two_pos) Hval Hopp).
Qed.

End DpoBoundMain.

Section DpoPairMain.

(* ============ Part 0a. real_eq_plus_opp_swap：(a+x)+(−a) == x ============ *)
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

(* ============ Part 0b. real_eq_plus_opp_common：(A+X)+(−(A+Y)) == X+(−Y) ============ *)
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

(* ============ Part 0c. real_log_inv_one_inv：log(inv x) == −log x（锚点法） ============ *)
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

(* ============ Part 0d. real_log_exp_neg：log(e^{−x}) == −x（锚点法） ============ *)
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

(* ============ Part 0e. real_log_proof_irrel：log 的正性证明参数无关（锚点法） ============ *)
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

(* ============ Part 0f. real_log_wd：log 参数 real_eq 兼容（锚点法） ============ *)
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

(* ============ Part 1a. Real 层 Alignment 结构（Z_align 作 Variable，抽象状态空间 S） ============ *)
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

(* 对数几率比：log_ratio(pi,s) := log(pi s) − log(pi_ref s) *)
Definition real_log_ratio (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s : S) : Real :=
  real_plus (real_log (pi s) (Hpi s)) (real_opp (real_log (pi_ref s) (pi_ref_pos s))).

(* 成对 DPO 损失：−log σ( β·log_ratio(pi,s_w) − β·log_ratio(pi,s_l) ) *)
Definition real_dpo_loss_pair (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S) : Real :=
  real_opp (real_log (real_sigmoid (real_plus (real_mult beta (real_log_ratio pi Hpi s_w))
                                              (real_opp (real_mult beta (real_log_ratio pi Hpi s_l)))))
                     (real_sigmoid_pos (real_plus (real_mult beta (real_log_ratio pi Hpi s_w))
                                                  (real_opp (real_mult beta (real_log_ratio pi Hpi s_l)))))).

(* ============ Part 1b. real_log_pi_star：log π*(s) == −log Z + log π_ref(s) + r(s)/β ============ *)
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

(* ============ Part 2a. real_sigmoid_wd：sigmoid 参数 real_eq 兼容（链） ============ *)
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

(* ============ Part 2b. real_dpo_loss_at_pi_star：L_DPO(π*, s_w, s_l) == −log σ(r_w − r_l) ============ *)
Lemma real_dpo_loss_at_pi_star : forall (s_w s_l : S),
  real_eq (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
          (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                              (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l)))))).
Proof.
  intros s_w s_l.
  unfold real_dpo_loss_pair, real_log_ratio.
  set (A := real_opp (real_log Z_align Z_align_pos)).
  (* Hdiff_w：log(pi_star s_w) − log(pi_ref s_w) == A + u_w *)
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
    - (* (A+(L+u))+(−L) == A+((L+u)+(−L)) == A+u *)
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
  (* Hdiff_l 对称 *)
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
  (* Hmain：β·(log_ratio_w) − β·(log_ratio_l) == r_w − r_l *)
  assert (Hmain : real_eq
        (real_plus (real_mult beta (real_plus (real_log (real_pi_star s_w) (real_pi_star_pos s_w))
                                              (real_opp (real_log (pi_ref s_w) (pi_ref_pos s_w)))))
                   (real_opp (real_mult beta (real_plus (real_log (real_pi_star s_l) (real_pi_star_pos s_l))
                                                        (real_opp (real_log (pi_ref s_l) (pi_ref_pos s_l)))))))
        (real_plus (reward s_w) (real_opp (reward s_l)))).
  {
    (* 1. β·LR_w == β·(A+u_w)（Hdiff_w）、β·LR_l == β·(A+u_l)（Hdiff_l） *)
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
    - (* 2-4. β·(A+u_w) − β·(A+u_l) == r_w − r_l *)
      apply (real_eq_trans _ (real_plus (real_plus (real_mult beta A)
                                                   (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w))))
                                        (real_opp (real_plus (real_mult beta A)
                                                             (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l)))))) _).
      + (* β·(A+u_w) == βA+βu_w（distrib 两次） *)
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
      + (* 3. common 消 A：plus (plus BA X) (opp (plus BA Y)) == X+(−Y) *)
        apply (real_eq_trans _ (real_plus (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                                          (real_opp (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l))))) _).
        * apply (real_eq_plus_opp_common (real_mult beta A)
                                         (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                                         (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l)))).
        * (* 4. β·(invβ·r_w) == r_w、β·(invβ·r_l) == r_l *)
          apply (RealSetoid.real_eq_plus_compat (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_w)))
                                                (real_opp (real_mult beta (real_mult (real_inv_pos beta beta_pos) (reward s_l))))
                                                (reward s_w)
                                                (real_opp (reward s_l))).
          -- (* β·(invβ·r_w) == r_w *)
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
  (* 组装：opp (log (sigmoid P)) == opp (log (sigmoid Q))，P := β·LR_w−β·LR_l，Q := r_w−r_l *)
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

(* ============ Part 3. real_dpo_loss_pi_star_bounded_eps：r_l < r_w ⟹ L_DPO(π*,s_w,s_l) < log 2 ============ *)
Lemma real_dpo_loss_pi_star_bounded_eps :
  forall (s_w s_l : S),
    real_lt (reward s_l) (reward s_w) ->
    real_lt (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
            (real_log (real_plus real_one real_one) real_two_pos).
Proof.
  intros s_w s_l Hrw.
  (* 核心：−log σ(r_w−r_l) < log 2（判例 real_dpo_sigmoid_loss_bounded） *)
  assert (Hcore : real_lt
        (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                            (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
        (real_log (real_plus real_one real_one) real_two_pos))
    by exact (real_dpo_sigmoid_loss_bounded (reward s_w) (reward s_l) Hrw).
  (* at_pi_star：L_DPO(π*,s_w,s_l) == −log σ(r_w−r_l) *)
  apply (RealSetoid.real_lt_id_l (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
          (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                              (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
          (real_log (real_plus real_one real_one) real_two_pos)).
  - exact (real_dpo_loss_at_pi_star s_w s_l).
  - exact Hcore.
Qed.

(* ============================================================ *)
(* T1.4（）：π* 处 DPO 损失双侧定量界（论文1 P2 项 10）*)
(*   r_l < r_w ⟹ 0 < L_DPO(π*,s_w,s_l) < log 2                 *)
(*   链①（下界）：1 < 1+e^{−x}（e^{−x} > 0 平移）→ σ(x) < 1    *)
(*     （inv 反序 + inv one == one）→ log σ < log 1 == 0        *)
(*     → 0 < −log σ（real_opp_lt_compat + real_opp_zero）       *)
(*     → 换形 at_pi_star；链②（上界）：bounded_eps。            *)
(* ============================================================ *)

(* 辅助：0 < x ⟹ 1 < 1 + x（Real 层平移） *)
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

(* 辅助：inv 1 == 1（real_inv_unique 于 correct 与 mult_one；real_inv_one 定义在
   Section 之后，防前向引用） *)
Lemma real_inv_one_local : real_eq (real_inv_pos real_one real_lt_zero_one) real_one.
Proof.
  apply (real_inv_unique real_one (real_inv_pos real_one real_lt_zero_one) real_one).
  - apply (real_inv_pos_correct real_one real_lt_zero_one).
  - apply (real_mult_one real_one).
Qed.

(* 辅助：σ(x) < 1（1 < 1+e^{−x} + inv 反序 + inv one == one） *)
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

(* 辅助：log σ(x) < 0（σ < 1 + log 严格递增 + log 1 == 0） *)
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

(* T1.4 主定理：r_l < r_w ⟹ 0 < L_DPO(π*,s_w,s_l) < log 2（双侧定量界） *)
Theorem real_dpo_loss_pi_star_bounded_both :
  forall (s_w s_l : S),
    real_lt (reward s_l) (reward s_w) ->
    And (real_lt real_zero (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l))
        (real_lt (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
                 (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  intros s_w s_l Hrw.
  split.
  - (* 0 < L：L == −log σ(r_w−r_l)（at_pi_star）+ 0 < −log σ *)
    apply (RealSetoid.real_lt_id_r real_zero
             (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                                 (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
             (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)).
    + apply (real_eq_sym (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
                         (real_opp (real_log (real_sigmoid (real_plus (reward s_w) (real_opp (reward s_l))))
                                             (real_sigmoid_pos (real_plus (reward s_w) (real_opp (reward s_l))))))
                         (real_dpo_loss_at_pi_star s_w s_l)).
    + (* 0 < −log σ：real_opp_lt_compat 于 log σ < 0，opp zero == zero 换形 *)
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
(* B-8-1：DPO 奖励恢复（Real 层复刻）                          *)
(*   抽象层 dpo_reward_recovers_up_to_baseline（L18858）的 Real 版：*)
(*   β·(log π*(s) − log π_ref(s)) == r(s) − β·log Z_align         *)
(*   （π* 处 DPO 隐式奖励精确恢复真实奖励，差配分基线偏移）     *)
(*   组装：real_log_pi_star（闭式解）+ Real 层代数链            *)
(*   （消去 log π_ref + β 分配 + β·(1/β) 吸收 + opp 换形证毕）  *)
(* ============================================================ *)

(* Real 层 DPO 显式奖励：β·(log π(s) − log π_ref(s)) *)
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
  (* log π* == −log Z + (log π_ref + r/β)（闭式解） *)
  assert (Hlog : real_eq (real_log (real_pi_star s) (real_pi_star_pos s))
                         (real_plus (real_opp (real_log Z_align Z_align_pos))
                                    (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                               (real_mult (real_inv_pos beta beta_pos) (reward s)))))
    by exact (real_log_pi_star s).
  (* 内层抵消：(log π_ref + r/β) + opp(log π_ref) == r/β *)
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
  (* β·(opp logZ) == opp(β·logZ) *)
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
  (* β·((1/β)·r) == r *)
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
  (* 主链：β·(log π* + opp log π_ref) == β·((−logZ + (log π_ref + r/β)) + opp log π_ref)
     == β·(−logZ + r/β) == β·(−logZ) + β·((1/β)r) == −(β·logZ) + r == r + −(β·logZ) *)
  apply (real_eq_trans _ (real_mult beta
                          (real_plus (real_plus (real_opp (real_log Z_align Z_align_pos))
                                                (real_plus (real_log (pi_ref s) (pi_ref_pos s))
                                                           (real_mult (real_inv_pos beta beta_pos) (reward s))))
                                     (real_opp (real_log (pi_ref s) (pi_ref_pos s))))) _).
  - (* 替换 log π* *)
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
  - (* 代数化简 *)
    apply (real_eq_trans _ (real_mult beta
                          (real_plus (real_opp (real_log Z_align Z_align_pos))
                                     (real_mult (real_inv_pos beta beta_pos) (reward s)))) _).
    + (* 内层抵消：(plus A (plus B C)) + D == A + C *)
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
    + (* β·(A + C) == β·A + β·C == −(β·logZ) + r == r + −(β·logZ) *)
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
(* B-8-2：GRPO 组相对优势零均值（Real 层复刻）                 *)
(*   抽象层 grpo_advantage_zero_mean（L22573）的 Real 版：       *)
(*   Σ_i (r_i − μ)·c == 0（对任意缩放 c）                        *)
(*   基础设施：real_of_nat（nat→Real 嵌入）+ real_list_sum_g 族  *)
(*   （ext/add/linear/opp/minus/const，列表 fold 求和）          *)
(*   组装：mult 交换 → 标量线性 → ΣA_i == 0 抵消链              *)
(*   （Σr − G·μ == Σr − Σr == 0，G·(1/G) 吸收）                 *)
(* ============================================================ *)

Section RealGrpoMain.

(* nat 到 Real 的嵌入（0 ⟼ real_zero，S n ⟼ real_one + of_nat n） *)
Fixpoint real_of_nat (n : nat) : Real :=
  match n with
  | O => real_zero
  | Datatypes.S n' => real_plus real_one (real_of_nat n')
  end.

(* 诚实接口：有限组 + 枚举覆盖 + 组大小正性（Real 层可实例化：具体有限类型） *)
Variable Group : Set.
Variable group_enum : list Group.
Variable group_cover : forall i : Group, InT i group_enum.
Definition real_group_size : nat := length group_enum.
Variable real_group_size_pos : real_lt real_zero (real_of_nat real_group_size).
Variable reward_group : Group -> Real.

(* 组求和（列表 fold，Real 层） *)
Fixpoint real_list_sum_g (f : Group -> Real) (l : list Group) : Real :=
  match l with
  | nil => real_zero
  | i :: rest => real_plus (f i) (real_list_sum_g f rest)
  end.

(* 逐点 ext：f ≈ g 逐点 ⟹ Σ ≈ Σ *)
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

(* 标量线性：Σ(a·f) == a·Σf *)
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

(* 和的可加性：Σ(f+g) == Σf + Σg *)
Lemma real_list_sum_g_add : forall (f g : Group -> Real) (l : list Group),
  real_eq (real_list_sum_g (fun i => real_plus (f i) (g i)) l)
          (real_plus (real_list_sum_g f l) (real_list_sum_g g l)).
Proof.
  intros f g l.
  induction l as [| i rest IH]; simpl.
  - apply (real_eq_sym _ _ (real_plus_zero real_zero)).
  - (* cons：f i + g i + Σ(f+g)rest == (f i + Σf rest) + (g i + Σg rest) *)
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

(* 右分配（Real 层自证：comm + real_distrib 组装，避免前向引用 L44250） *)
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

(* 常数和：Σ const c == real_of_nat (length l)·c *)
Lemma real_list_sum_g_const : forall (c : Real) (l : list Group),
  real_eq (real_list_sum_g (fun _ : Group => c) l)
          (real_mult (real_of_nat (length l)) c).
Proof.
  intros c l.
  induction l as [| i rest IH]; simpl.
  - (* nil：zero == of_nat 0·c == 0·c（of_nat 0 ≡ real_zero 定义性；
       real_zero == c·0 == 0·c） *)
    apply (real_eq_trans _ _ _ (real_eq_sym _ _ (real_mult_zero c)) (real_mult_comm c real_zero)).
  - (* cons：c + of_nat(len)·c == (1 + of_nat(len))·c == of_nat(S len)·c *)
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

(* 和的负：Σ(opp f) == opp(Σf) *)
Lemma real_list_sum_g_opp : forall (f : Group -> Real) (l : list Group),
  real_eq (real_list_sum_g (fun i => real_opp (f i)) l) (real_opp (real_list_sum_g f l)).
Proof.
  intros f l.
  induction l as [| i rest IH]; simpl.
  - apply (real_eq_sym _ _ (real_opp_zero)).
  - (* opp(f i) + opp(Σrest) == opp(f i + Σrest) *)
    apply (real_eq_trans _ (real_plus (real_opp (f i)) (real_opp (real_list_sum_g f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp (f i))
                                            (real_list_sum_g (fun i => real_opp (f i)) rest)
                                            (real_opp (f i))
                                            (real_opp (real_list_sum_g f rest))
                                            (real_eq_refl _) IH).
    + apply (real_eq_sym _ _ (real_opp_plus (f i) (real_list_sum_g f rest))).
Qed.

(* 和的差：Σ(f − g) == Σf − Σg *)
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

(* 组均值：μ = (1/G)·Σ r_i *)
Definition real_group_mean : Real :=
  real_mult (real_inv_pos (real_of_nat real_group_size) real_group_size_pos)
            (real_list_sum_g reward_group group_enum).

(* 组相对优势：A_i = r_i − μ *)
Definition real_grpo_advantage (i : Group) : Real :=
  real_plus (reward_group i) (real_opp real_group_mean).

(* 常数和 == G·c，G := length group_enum ⟹ Σμ == Σr（μ := (1/G)·Σr，inv 吸收） *)
Lemma real_group_mean_sum : forall (l : list Group),
  real_eq (real_list_sum_g (fun _ : Group => real_group_mean) l)
          (real_mult (real_of_nat (length l)) real_group_mean).
Proof.
  intro l.
  apply (real_list_sum_g_const real_group_mean l).
Qed.

(* 零均值（B-8-2 主定理）：Σ_i (r_i − μ)·c == 0（对任意缩放 c） *)
Theorem real_grpo_advantage_zero_mean : forall c : Real,
  real_eq (real_list_sum_g (fun i => real_mult (real_grpo_advantage i) c) group_enum) real_zero.
Proof.
  intros c.
  (* 抵消核心：ΣA_i == 0 *)
  assert (Hcancel : real_eq (real_list_sum_g real_grpo_advantage group_enum) real_zero).
  {
    unfold real_grpo_advantage.
    (* Σ(r_i − μ) == Σr − Σμ *)
    apply (real_eq_trans _ (real_plus (real_list_sum_g reward_group group_enum)
                                      (real_opp (real_list_sum_g (fun _ : Group => real_group_mean) group_enum))) _).
    - apply (real_list_sum_g_minus reward_group (fun _ : Group => real_group_mean) group_enum).
    - (* Σμ == Σr（G·μ == Σr：G·(1/G) 吸收） *)
      assert (Hmu : real_eq (real_list_sum_g (fun _ : Group => real_group_mean) group_enum)
                            (real_list_sum_g reward_group group_enum)).
      {
        (* Σμ == of_nat G·μ（const，G := length group_enum） *)
        apply (real_eq_trans _ (real_mult (real_of_nat real_group_size) real_group_mean) _).
        - apply (real_list_sum_g_const real_group_mean group_enum).
        - (* G·μ == Σr：G·((1/G)·Σr) == (G·(1/G))·Σr == 1·Σr == Σr *)
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
      (* Σr − Σμ == Σr − Σr == 0 *)
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
  (* Σ(A_i·c) == Σ(c·A_i) == c·ΣA_i == c·0 == 0 *)
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
(* B-8-3：softmax = Boltzmann（Real 层复刻）                   *)
(*   抽象层 attention_is_gibbs（L27104）的 Real 版：             *)
(*   单位温度（inv D == 1）且 energy = −logits 且配分相等 ⟹      *)
(*   softmax(z,s) == boltzmann_dist_attn(s)（逐点）              *)
(*   诚实接口：real_sum_over_S（抽象 S 求和，Real 层实例化时     *)
(*   提供——S 无枚举边界假设的 Real 层形态）                     *)
(*   组装：mult invD·energy 归约（HD + comm + mult_one）→        *)
(*   energy == −logits 替换 → cauchy_real_exp_wd 保 eq →         *)
(*   real_inv_pos_ext 逆元统一 → mult_comm 证毕                  *)
(* ============================================================ *)

Section RealAttnMain.

(* 抽象状态空间（Real 层 Section 自声明，同 DpoPairMain 先例） *)
Variable S : Type.

(* 诚实接口：抽象 S 上的求和（Real 层可实例化；零公理面） *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real), (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).

(* 温度 / 能量 / logits 环境（Real 层） *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable z_logits : S -> Real.

(* exp_pos_fn Real 版：e^{x}（softmax 分子） *)
Definition real_exp_pos_fn (x : Real) : Real := real_exp_neg (real_opp x).

(* 配分函数（Real 层）：Σ_s e^{z_logits s} *)
Definition real_partition_function (z_logits : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (z_logits s)).

Lemma real_partition_function_pos : forall z_logits : S -> Real, real_lt real_zero (real_partition_function z_logits).
Proof.
  intros zz. unfold real_partition_function, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* softmax（Real 层）：e^{z_logits s}·inv(Σ e^{z_logits·}) *)
Definition real_softmax (z_logits : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (z_logits s)) (real_inv_pos (real_partition_function z_logits) (real_partition_function_pos z_logits)).

(* Boltzmann 因子（Real 层）：e^{−e(s)/D} *)
Definition real_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

(* 热力学配分（Real 层）：Σ_s boltzmann_factor *)
Definition real_Z_thermo : Real := real_sum_over_S real_boltzmann_factor.

Variable real_Z_thermo_pos : real_lt real_zero real_Z_thermo.

(* Boltzmann 分布（Real 层）：inv(z_logits)·factor *)
Definition real_boltzmann_dist_attn (s : S) : Real :=
  real_mult (real_inv_pos real_Z_thermo real_Z_thermo_pos) (real_boltzmann_factor s).

(* 单位温度下 softmax = Boltzmann（B-8-3 主定理）：
   inv D == 1 且 energy == −logits 且 Z_thermo == partition_function z_logits
   ⟹ 对任意状态 s：softmax(z_logits,s) == boltzmann_dist_attn(s) *)
Theorem real_attention_is_gibbs :
  (real_eq (real_inv_pos D D_pos) real_one) ->
  (forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
  real_eq real_Z_thermo (real_partition_function z_logits) ->
  forall s : S, real_eq (real_softmax z_logits s) (real_boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  unfold real_softmax, real_boltzmann_dist_attn, real_boltzmann_factor, real_exp_pos_fn.
  (* 1. Boltzmann 侧指数归约：e^{−e(s)/D} == e^{z_logits s}（mult (inv D) (energy s) == energy s == opp (z_logits s)） *)
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
  (* 2. 逆元统一：inv(Z_thermo) == inv(partition_function z_logits)（HZ + real_inv_pos_ext） *)
  assert (Hinv : real_eq (real_inv_pos real_Z_thermo real_Z_thermo_pos)
                         (real_inv_pos (real_partition_function z_logits) (real_partition_function_pos z_logits))).
  { apply (real_inv_pos_ext real_Z_thermo (real_partition_function z_logits) real_Z_thermo_pos (real_partition_function_pos z_logits)). exact HZ. }
  (* 3. 组装：mult (e^{z_logits s}) (inv Pf) == mult (inv z_logits) (e^{−e/D})
     （LHS 定义性 = M；inv 统一（sym Hinv）→ comm → 指数替换（sym Hbf）） *)
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
(* B-8-4：Boltzmann 注意力稳态方程（Real 层复刻）              *)
(*   抽象层 steady_state_boltzmann_attn（L27180）的 Real 版：    *)
(*   Σ_s' p(s')·T(s',s) == p(s)（稳态：detailed balance + 核归   *)
(*   一化组装）                                                  *)
(*   诚实接口（零公理面）：real_sum_over_S_ext/linear *)
(*   （求和外延/线性）+ real_detailed_balance +                   *)
(*   real_transition_normalization（Real 层可实例化）            *)
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

(* Boltzmann 注意力分布（Real 层）：p(s) := inv(Z)·e^{−e(s)/D} *)
Definition real_boltzmann_dist_attn_s (s : S) : Real :=
  real_mult (real_inv_pos Z_thermo Z_thermo_pos) (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s))).

(* 转移核（Real 层） *)
Variable real_transition : S -> S -> Real.

(* 诚实接口：detailed balance（可逆核，Real 层可实例化） *)
Variable real_detailed_balance : forall (s s' : S),
  real_eq (real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s))
          (real_mult (real_boltzmann_dist_attn_s s) (real_transition s s')).

(* 诚实接口：行归一化 Σ_s' T(s,s') == 1（马尔可夫核标准性质） *)
Variable real_transition_normalization : forall s : S,
  real_eq (real_sum_over_S (fun s' => real_transition s s')) real_one.

(* 稳态方程（B-8-4 主定理）：Σ_s' p(s')·T(s',s) == p(s)
   组装：detailed balance 逐点替换 → 求和外延 → 线性提取 p(s) → 核归一化 → mult_one 证毕 *)
Theorem real_steady_state_boltzmann_attn : forall s : S,
  real_eq (real_sum_over_S (fun s' => real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s)))
          (real_boltzmann_dist_attn_s s).
Proof.
  intro s.
  (* 1. 逐点 detailed balance 替换：Σ (p s'·T s' s) == Σ (p s·T s s') *)
  apply (real_eq_trans _ (real_sum_over_S (fun s' => real_mult (real_boltzmann_dist_attn_s s) (real_transition s s'))) _).
  - apply (real_sum_over_S_ext (fun s' => real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s))
                               (fun s' => real_mult (real_boltzmann_dist_attn_s s) (real_transition s s'))).
    intro s'. apply (real_detailed_balance s s').
  - (* 2. 线性提取：Σ (p s·T s s') == p s·Σ (T s s') *)
    apply (real_eq_trans _ (real_mult (real_boltzmann_dist_attn_s s) (real_sum_over_S (fun s' => real_transition s s'))) _).
    + apply (real_sum_over_S_linear (real_boltzmann_dist_attn_s s) (fun s' => real_transition s s')).
    + (* 3. 核归一化：Σ T == 1 ⟹ p s·1 == p s *)
      apply (real_eq_trans _ (real_mult (real_boltzmann_dist_attn_s s) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat (real_boltzmann_dist_attn_s s)
                                              (real_sum_over_S (fun s' => real_transition s s'))
                                              (real_boltzmann_dist_attn_s s) real_one
                                              (real_eq_refl _) (real_transition_normalization s)).
      * apply (real_mult_one (real_boltzmann_dist_attn_s s)).
Qed.

End RealAttnSteady.

(* ============================================================ *)
(* B-8-5：Min-P 截断核归一化（Real 层复刻）                    *)
(*   抽象层 minp_markov_kernel_normalized（L29492）的 Real 版：  *)
(*   Σ_w minp_kernel(prefix,w) == 1（概率守恒）                  *)
(*   组装：逐点分支交换（keep 分支 mult_comm / drop 分支         *)
(*   mult_zero 反向）→ 标量线性提取 inv(temp_sum) →              *)
(*   inv(temp_sum)·temp_sum == 1（inv_pos_correct）证毕          *)
(*   诚实接口（零公理面）：real_minp_keep_dec（判定，*)
(*   Set 层 Or）+ real_minp_temp_sum_pos（保留集非空 + 因子正）  *)
(* ============================================================ *)

Section RealMinPMain.

Variable Token : Type.
Variable vocab : list Token.

(* 温度因子（Real 层）：e^{−loss/T} *)
Variable real_temp_factor : Token -> Real.

(* 判定接口：minp_keep_dec 的 Real 版（Set 层 Or，可实例化） *)
Variable real_minp_keep : list Token -> Token -> Set.
Variable real_minp_keep_dec : forall (prefix : list Token) (w : Token),
  Or (real_minp_keep prefix w) (Not (real_minp_keep prefix w)).

(* 截断质量：Σ 保留分支的 temp_factor（match 判定） *)
Definition real_minp_temp_sum (prefix : list Token) : Real :=
  real_list_sum Token (fun w => match real_minp_keep_dec prefix w with
                          | inl _ => real_temp_factor w
                          | inr _ => real_zero
                          end) vocab.

(* 正性接口（Real 层可实例化：保留集非空 + 因子正） *)
Variable real_minp_temp_sum_pos : forall prefix : list Token,
  real_lt real_zero (real_minp_temp_sum prefix).

(* Min-P 截断核（Real 层）：keep ⟹ temp_factor·inv(sum)，drop ⟹ zero *)
Definition real_minp_markov_kernel (prefix : list Token) (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ => real_mult (real_temp_factor w)
                       (real_inv_pos (real_minp_temp_sum prefix) (real_minp_temp_sum_pos prefix))
  | inr _ => real_zero
  end.

(* 归一化（B-8-5 主定理）：Σ_w minp_kernel(prefix,w) == 1
   组装：分支交换（ext）→ 线性提取 inv(temp_sum) → temp_sum 定义性换形 →
   inv(temp_sum)·temp_sum == 1（comm + inv_pos_correct） *)
Theorem real_minp_markov_kernel_normalized : forall prefix : list Token,
  real_eq (real_list_sum Token (fun w => real_minp_markov_kernel prefix w) vocab) real_one.
Proof.
  intro prefix.
  unfold real_minp_markov_kernel.
  (* 1. 逐点分支交换：keep 分支 temp·inv == inv·temp（comm），drop 分支 zero == inv·zero（mult_zero 反向） *)
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
  - (* 2. 线性提取 inv(temp_sum)：Σ (inv·match) == inv·Σ(match) *)
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
    + (* 3. temp_sum 定义性换形 + inv(temp_sum)·temp_sum == 1（comm + inv_pos_correct） *)
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
(* B-8-6：Top-K 支配性（Real 层复刻）                          *)
(*   抽象层 top_k_majorization（L28489）的 Real 版：             *)
(*   keep_top_k s1 ∧ ¬keep_top_k s2 ⟹ f s2 ≤ f s1               *)
(*   （Top-K 保留者权重 ≥ 逐出者权重——最重 K 个的序刻画）       *)
(*   组装：real_le_dec 分叉 → 反证（not_le_lt ⟹ lt (f s1)(f s2)）*)
(*   → 计数单调（count_heavier_succ_le）→ keep/drop 计数矛盾    *)
(*   （NatLt 双向 + Nat.ltb 转换 + lia）                         *)
(*   诚实接口（零公理面）：real_le_dec（线序判定）+  *)
(*   real_not_le_lt（线序：Not(le) ⟹ lt 反向；real_weak_trich   *)
(*   在此不可用——需强序判定）+ 计数接口（count/单调/keep 双向）*)
(* ============================================================ *)

Section RealTopKMain.

Variable S : Type.
Variable K : nat.
Variable real_boltzmann_factor_ : S -> Real.

(* 诚实接口：线序判定（Real 层可实例化） *)
(* [墙族登记·RW-LPO 线序判定] 整体实序可判定=LPO 不可实例化（判例；SqWall⟺rLPO 双向类=UpReqLpoEquiv.v:258/351/438 lpn_equivalence；论文7§8）——基座墙密度最高单点，禁硬证禁纯删；Q 层逐点可判定（Qlt_le_dec，判例下半）不升级本位；Top-K 使用链（:2266-）以本位为线序判定源，实例层仅可计算模型可供给。 *)
Variable real_le_dec : forall a b : Real, Or (real_le a b) (Not (real_le a b)).
(* 诚实接口：线序——Not (le a b) ⟹ lt b a（柯西实数线序，可实例化） *)
(* [墙族登记·RW-NOTLT 线序负转正] real_le=Or(lt,eq)（S02_CauchyComplete.v:471）定义形下，¬(a≤b)→b<a 需从负陈述提取正分离见证——Markov/LPO 族邻域（判例组；PA_UpAblD2_AbsLeId_RI_DO.v:49 在案）；库内零已证实例（G09_MiscSmall.v:635 rnot_le_lt 同形亦假设位）——禁硬证；locatedness 供给候选（UpReqCauchy 系具体层，核）。 *)
Variable real_not_le_lt : forall a b : Real, Not (real_le a b) -> real_lt b a.
(* 诚实接口：比 f s 更重的计数（枚举计数，语义由 real_le_dec 实例化保证） *)
Variable real_count_heavier : S -> nat.
Variable real_count_heavier_succ_le : forall (s1 s2 : S),
  real_lt (real_boltzmann_factor_ s1) (real_boltzmann_factor_ s2) ->
  (Datatypes.S (real_count_heavier s2) <= real_count_heavier s1)%nat.
(* 诚实接口：Top-K 判定（count < K 的 Set 层双向刻画，NatLt） *)
Variable real_keep_top_k : S -> Set.
Variable real_keep_top_k_iff : forall s : S,
  And (real_keep_top_k s -> NatLt (real_count_heavier s) K)
      (NatLt (real_count_heavier s) K -> real_keep_top_k s).

(* Top-K 支配性（B-8-6 主定理）：保留者权重 ≥ 逐出者权重
   组装：le_dec 分叉 → 反证（not_le_lt ⟹ lt (f s1) (f s2) ⟹ 计数矛盾 lia） *)
Theorem real_top_k_majorization : forall s1 s2 : S,
  real_keep_top_k s1 -> Not (real_keep_top_k s2) ->
  real_le (real_boltzmann_factor_ s2) (real_boltzmann_factor_ s1).
Proof.
  intros s1 s2 Hk1 Hnk2.
  destruct (real_le_dec (real_boltzmann_factor_ s2) (real_boltzmann_factor_ s1)) as [Hle | Hnle].
  - exact Hle.
  - (* 反证：Hnle ⟹ lt (f s1) (f s2) ⟹ S(count s2) ≤ count s1；keep/drop 计数矛盾 *)
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
(* B-8-7：PPO 保守性（Real 层复刻，eps 化）                    *)
(*   抽象层 ppo_conservative（L18795）的 Real 版：               *)
(*   min(r, clip(r))·adv ≤ r·adv（min_le_l）⟹ ppo ≤ is + eps 残差 *)
(*   Real 层 min 只有 eps 界（real_min_le_l_eps），主定理取       *)
(*   eps 加权残差形态（诚实接口边界）：                          *)
(*   ppo_objective ≤ is_objective + Σ π_old·(eps·adv)            *)
(*   组装：min ≤ ρ+eps（eps 界）→ ×adv（strict 正乘）→ 右分配   *)
(*   → ×π_old（strict 正乘 + comm 换形）→ Σ 保序（sum_le 接口） *)
(*   → sum_add 拆项证毕                                          *)
(*   诚实接口（零公理面）：real_sum_over_S_le/add +  *)
(*   real_advantage_pos / real_pi_old_pos（strict 正性，          *)
(*   real_le_mult_compat 需 lt 前提）+ 环境                       *)
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

(* 重要性采样比率：r(s) := π*(s)/π_old(s) *)
Definition real_importance_ratio_ (s : S) : Real :=
  real_mult (real_pi_star_ s) (real_inv_pos (real_pi_old s) (real_pi_old_pos s)).

(* 裁剪：clip(r) := max(min(r, 1+eps), 1−eps)（Real 层无 real_minus，1−eps := 1+(−eps)） *)
Definition real_ppo_clip_ (r : Real) : Real :=
  real_max (real_min r (real_plus real_one epsilon)) (real_plus real_one (real_opp epsilon)).

(* PPO 保守性（B-8-7 主定理，eps 化）：
   ppo_objective ≤ is_objective + Σ π_old·(eps·adv)
   组装：min ≤ ρ+eps → ×adv → 右分配 → ×π_old → Σ 保序 → sum_add 拆项 *)
Theorem real_ppo_conservative_eps : forall eps : Real,
  real_lt real_zero eps ->
  real_le (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                     (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))))
          (real_plus (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s))))
                     (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))).
Proof.
  intros eps Hepspos.
  (* 逐点：min·adv ≤ (ρ+eps)·adv == ρ·adv + eps·adv ⟹ π_old·min·adv ≤ π_old·(ρ·adv + eps·adv) *)
  assert (Hpt : forall s : S,
    real_le (real_mult (real_pi_old s) (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s)))
            (real_mult (real_pi_old s) (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                  (real_mult eps (real_advantage_fn s))))).
  {
    intro s.
    (* min·adv ≤ (ρ+eps)·adv：real_min_le_l_eps + strict 正乘 *)
    assert (H1 : real_le (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))
                          (real_mult (real_plus (real_importance_ratio_ s) eps) (real_advantage_fn s))).
    {
      apply (real_le_mult_compat (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s)))
                                 (real_plus (real_importance_ratio_ s) eps)
                                 (real_advantage_fn s)).
      - exact (real_advantage_pos s).
      - exact (real_min_le_l_eps (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s)) eps Hepspos).
    }
    (* (ρ+eps)·adv == ρ·adv + eps·adv（comm + distrib + comm 链） *)
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
    (* min·adv ≤ ρ·adv + eps·adv（le_id_r 换形） *)
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
    (* π_old·min·adv ≤ π_old·(ρ·adv + eps·adv)：comm 换形 + strict 正乘 *)
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
  (* Σ 保序：逐点界提升到和 *)
  assert (Hsum : real_le (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                                 (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))))
                         (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                                 (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                            (real_mult eps (real_advantage_fn s)))))).
  { apply real_sum_over_S_le. intro s. exact (Hpt s). }
  (* 代数：Σ π_old·(ρ·adv + eps·adv) == Σ π_old·ρ·adv + Σ π_old·(eps·adv)（ext distrib + sum_add） *)
  apply (RealSetoid.real_le_id_r _ (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                                 (real_plus (real_mult (real_importance_ratio_ s) (real_advantage_fn s))
                                                            (real_mult eps (real_advantage_fn s))))) _).
  - (* RHS 换形：Σ π_old·(ρ·adv + eps·adv) == Σ (π_old·ρ·adv + π_old·eps·adv) == Σ + Σ *)
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
(* B-8-8：RLHF 最优性（Real 层复刻，eps 化）                   *)
(*   抽象层 rlhf_optimal（L18318）的 Real 版：                   *)
(*   J(pi) := −F(pi) ≤ J(pi_star) + D·eps（eps 加权残差形态——    *)
(*   Real 层 KL ≥ 0 只有 eps 版）                                *)
(*   核心证明：real_kl_sum_decomp（Σ p·log p == Σ p·log p_b     *)
(*   + Σ p·kl_term：逐点 distrib + 抵消链 + kl_term_equiv 接口）*)
(*   组装：KL 分解接口 → gibbs eps（0 ≤ Σkl + eps）→ D 正乘 →   *)
(*   le_plus_compat（F(p_b) ≤ F(π) + D·eps）→ opp 取负 + 环恒等  *)
(*   诚实接口（零公理面）：real_boltzmann_log_decomp/ *)
(*   normalized（Boltzmann 对数分解/归一化）+ real_kl_term_equiv *)
(*   （log 除法分解）+ real_pi_star_align（π* == p_b）+          *)
(*   real_gibbs_sum_eps（Σ 版 KL ≥ 0）+ real_kl_decomp_full      *)
(*   （常数消去桥：F(p) == F(p_b) + D·Σ kl）                     *)
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

(* Boltzmann 分布（Real 层，对齐能量 base_loss）：p_b(s) := inv(Z)·e^{−e(s)/D} *)
Definition real_boltzmann_dist_r (s : S) : Real :=
  real_mult (real_inv_pos Z_align_r Z_align_r_pos)
            (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s))).

(* Boltzmann 正性（可证：inv 正 × exp 正） *)
Lemma real_boltzmann_dist_r_pos : forall s : S, real_lt real_zero (real_boltzmann_dist_r s).
Proof.
  intro s. unfold real_boltzmann_dist_r.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_exp_neg_pos.
Qed.

(* KL 项封装（缩短长括号链） *)
Definition real_kl_sum_term (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) (s : S) : Real :=
  real_kl_term (p s) (real_boltzmann_dist_r s) (Hp s) (real_boltzmann_dist_r_pos s).

(* 诚实接口：Boltzmann 对数分解 log p_b == −(e/D + log Z)（Real 层可实例化） *)
Variable real_boltzmann_log_decomp : forall (s : S) (Hpb : real_lt real_zero (real_boltzmann_dist_r s)),
  real_eq (real_log (real_boltzmann_dist_r s) Hpb)
          (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) (real_log Z_align_r Z_align_r_pos))).
(* 诚实接口：Boltzmann 归一化 Σ p_b == 1（Real 层可实例化） *)
Variable real_boltzmann_normalized :
  real_eq (real_sum_over_S real_boltzmann_dist_r) real_one.
(* 诚实接口：KL 项等价 p·(log p − log p_b) == real_kl_term p p_b（log 除法分解） *)
Variable real_kl_term_equiv : forall (p : S -> Real) (Hp : forall s, real_lt real_zero (p s)) (s : S),
  real_eq (real_mult (p s) (real_plus (real_log (p s) (Hp s))
                                      (real_opp (real_log (real_boltzmann_dist_r s) (real_boltzmann_dist_r_pos s)))))
          (real_kl_sum_term p Hp s).
(* 诚实接口：π* 闭式解（Real 层自声明，同 DpoPairMain real_pi_star 形态） *)
Variable real_pi_star_r : S -> Real.
(* 诚实接口：π* == p_b 逐点（对齐闭式解与 Boltzmann 分布一致） *)
Definition real_free_energy (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_plus (real_sum_over_S (fun s => real_mult (p s) (real_base_loss s)))
            (real_mult D (real_sum_over_S (fun s => real_mult (p s) (real_log (p s) (Hp s))))).

Variable real_pi_star_align : forall (s : S),
  real_eq (real_pi_star_r s) (real_boltzmann_dist_r s).
(* 诚实接口：Σ 版 KL ≥ 0 + eps（real_gibbs_inequality_eps 的抽象 S 形态） *)
Variable real_gibbs_sum_eps : forall (p : S -> Real) (Hp : forall s, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one) (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_sum_over_S (fun s => real_kl_term (p s) (real_boltzmann_dist_r s) (Hp s) (real_boltzmann_dist_r_pos s))) eps).
(* 诚实接口：自由能 KL 分解（常数消去桥：F(p) == F(p_b) + D·Σ kl） *)
Variable real_kl_decomp_full : forall (p : S -> Real) (Hp : forall s, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one),
  real_eq (real_free_energy p Hp)
          (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                     (real_mult D (real_sum_over_S (fun s => real_kl_term (p s) (real_boltzmann_dist_r s) (Hp s) (real_boltzmann_dist_r_pos s))))).

(* 熵侧 KL 分解（B-8-8 核心证明）：Σ p·log p == Σ p·log p_b + Σ p·kl_term
(* 熵侧 KL 分解（B-8-8 核心证明）：Σ p·log p == Σ p·log p_b + Σ p·kl_term
   组装：逐点（log p == log p_b + (log p − log p_b) 抵消链 + distrib）→
   Σ ext → sum_add → kl_term_equiv 替换 *)
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
  (* 1. 逐点：p·Lp == p·Lb + p·(Lp − Lb)（内层抵消 + distrib） *)
  assert (Hpt : forall s : S,
    real_eq (real_mult (p s) (Lp s))
            (real_plus (real_mult (p s) (Lb s))
                       (real_mult (p s) (real_plus (Lp s) (real_opp (Lb s))))))).
  {
    intro s.
    (* 内层抵消：Lb + (Lp + (−Lb)) == Lp *)
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
  (* 2. Σ 侧：ext 逐点替换 → sum_add → kl_term_equiv 替换 *)
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
(* RLHF 最优性（B-8-8 主定理，eps 化）：
   J(π) := −F(π) ≤ J(π⋆) + D·eps（π⋆ == p_b 逐点由 real_pi_star_align 提供） *)
   组装：KL 分解（kl_decomp_full）→ gibbs eps（0 ≤ Σkl + eps）→ D 正乘 →
   le_plus_compat（F(p_b) ≤ F(π) + D·eps）→ opp 取负（opp_le_compat +
   环恒等：A + X ≤ B ⟹ A ≤ B + opp(X)，X := opp(D·eps)） *)
Theorem real_rlhf_optimal_eps :
  forall (pi : S -> Real) (Hpi : forall s : S, real_lt real_zero (pi s))
    (Hnormpi : real_eq (real_sum_over_S pi) real_one) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_opp (real_free_energy pi Hpi))
            (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)) (real_mult D eps)).
Proof.
  intros pi Hpi Hnormpi eps Hepspos.
  (* 1. F(π) == F(p_b) + D·Σkl（分解） *)
  assert (Hkl : real_eq (real_free_energy pi Hpi)
                        (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                   (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))))
    by exact (real_kl_decomp_full pi Hpi Hnormpi).
  (* 2. 0 ≤ Σkl + eps（gibbs）⟹ 0 ≤ D·Σkl + D·eps（D 正乘 + distrib） *)
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
  (* 3. F(p_b) ≤ F(π) + D·eps（le_plus_compat 于 Hd + Hkl 换形） *)
  assert (Hf : real_le (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                       (real_plus (real_free_energy pi Hpi) (real_mult D eps))).
  {
    apply (real_le_trans _ (real_plus (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)
                                      (real_plus (real_mult D (real_sum_over_S (fun s => real_kl_term (pi s) (real_boltzmann_dist_r s) (Hpi s) (real_boltzmann_dist_r_pos s))))
                                                 (real_mult D eps))) _).
    - (* F(p_b) == F(p_b) + 0 ≤ F(p_b) + (D·Σkl + D·eps)（0 ≤ D·Σkl + D·eps） *)
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
    - (* F(p_b) + (D·Σkl + D·eps) == F(π) + D·eps（结合 + Hkl 反向） *)
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
  (* 4. opp 取负：J(pi) ≤ J(pi_star) + D·eps
     A := opp(F pi)、B := opp(F p_b)、C := D·eps。
     已知 Hf : F(p_b) ≤ F(pi) + C ⟹ opp(F(pi) + C) ≤ B（opp_le_compat）。
     opp(F(pi) + C) == A + opp(C)（real_opp_plus）⟹ A + opp(C) ≤ B。
     环恒等：A == (A + opp(C)) + C ⟹ (A + opp(C)) + C ≤ B + C ⟹ A ≤ B + C。 *)
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
  - (* A == (A + opp C) + C：环恒等（assoc 反向 + comm 内层 + plus_opp + plus_zero） *)
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
  - (* (A + opp C) + C ≤ B + C：le_plus_compat（Hopp' + refl C） *)
    apply (real_le_plus_compat (real_plus (real_opp (real_free_energy pi Hpi)) (real_opp (real_mult D eps)))
                               (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))
                               (real_mult D eps) (real_mult D eps)
                               Hopp' (real_le_refl (real_mult D eps))).
Qed.

End RealRLHFMain.

(* ============================================================ *)

(* Real 层 log 可微性论证：Bishop 逐 eps 复刻（检验 54 Qed 全部通过，） *)
Section LogDiffPhase4.
Section LogDiffPhase2.

(* Q 层：0 ≤ t ≤ 1/2 ⟹ t/(1+t) ≥ t − t²（field 于 Q 原子） *)
(* Q 层：0 ≤ t ≤ 1/2 ⟹ t−t² ≤ t/(1+t)（判例 field/Qle_shift_div_l） *)
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
  - (* (t−t²)(1+t) ≤ t：= t − t³ ≤ t ⟺ t³ ≥ 0 *)
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

(* ============ 2. Real 层 log 下界：0 < t ≤ 1/2 ⟹ t−t² ≤ log(1+t) ============ *)
(* 子引理 A：log(1+t) + log(1/(1+t)) == 0（real_log_mult + inv_correct + log_one） *)
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

(* 子引理 B0：1 − (1+t) == −t（投影级恒等，仿 real_opp_plus） *)
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

(* 子引理 B1a：s + (−1) == t（s == 1+t；投影级恒等，仿 real_one_minus_succ：
   real_eq_of_zero_diff + real_plus_proj/real_opp_proj + ring——不含 inv，投影可算） *)
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

(* 子引理 B1：−t·(inv s) == inv s − 1（s == 1+t；inv_correct：s·inv s == 1）
   代数级链（Real 层非 setoid，全部显式 real_eq_trans + RealSetoid.compat 组装，
   仿 real_hpq1；real_inv_pos 含 Qinv，投影级 ring 不可用——判例）：
     −t·inv == −(s−1)·inv          [t == s+(−1)，real_succ_minus_one]
            == −(inv·(s−1))         [mult_comm]
            == −(inv·s + inv·(−1))  [distrib]
            == −(1 + −(inv·1))      [inv·s == 1（inv_correct+comm）；inv·(−1) == −(inv·1)（opp_mult）]
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
  { (* −t·inv == −(s−1)·inv：t == s+(−1) 经 mult_compat + opp_compat *)
    apply (RealSetoid.real_eq_opp_compat (real_mult t (real_inv_pos s Hs))
                                         (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))).
    apply (RealSetoid.real_eq_mult_compat t (real_inv_pos s Hs)
                                          (real_plus s (real_opp real_one)) (real_inv_pos s Hs)).
    - apply real_eq_sym. exact (real_succ_minus_one t).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_opp (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))) _).
  { (* −(s−1)·inv == −(inv·(s−1))：mult_comm *)
    apply (RealSetoid.real_eq_opp_compat (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s Hs))
                                         (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))).
    apply (real_mult_comm (real_plus s (real_opp real_one)) (real_inv_pos s Hs)). }
  apply (real_eq_trans _ (real_opp (real_plus (real_mult (real_inv_pos s Hs) s)
                                              (real_mult (real_inv_pos s Hs) (real_opp real_one)))) _).
  { (* −(inv·(s−1)) == −(inv·s + inv·(−1))：distrib *)
    apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos s Hs) (real_plus s (real_opp real_one)))
                                         (real_plus (real_mult (real_inv_pos s Hs) s)
                                                    (real_mult (real_inv_pos s Hs) (real_opp real_one)))).
    apply (real_distrib (real_inv_pos s Hs) s (real_opp real_one)). }
  apply (real_eq_trans _ (real_opp (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))) _).
  { (* −(inv·s + inv·(−1)) == −(1 + −(inv·1))：inv·s == 1（inv_correct+comm）、
       inv·(−1) == −(inv·1)（opp_mult 反向） *)
    apply (RealSetoid.real_eq_opp_compat (real_plus (real_mult (real_inv_pos s Hs) s)
                                                    (real_mult (real_inv_pos s Hs) (real_opp real_one)))
                                         (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))).
    apply (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos s Hs) s)
                                          (real_mult (real_inv_pos s Hs) (real_opp real_one))
                                          real_one (real_opp (real_mult (real_inv_pos s Hs) real_one))).
    - (* inv·s == 1：comm + inv_correct *)
      apply (real_eq_trans _ (real_mult s (real_inv_pos s Hs)) _).
      + apply (real_mult_comm (real_inv_pos s Hs) s).
      + apply (real_inv_pos_correct s Hs).
    - (* inv·(−1) == −(inv·1)：opp_mult 反向 *)
      apply (real_eq_sym (real_opp (real_mult (real_inv_pos s Hs) real_one))
                         (real_mult (real_inv_pos s Hs) (real_opp real_one))).
      apply (real_opp_mult (real_inv_pos s Hs) real_one). }
  apply (real_eq_trans _ (real_opp (real_plus real_one (real_opp (real_inv_pos s Hs)))) _).
  { (* −(1 + −(inv·1)) == −(1 + −inv)：mult_one *)
    apply (RealSetoid.real_eq_opp_compat (real_plus real_one (real_opp (real_mult (real_inv_pos s Hs) real_one)))
                                         (real_plus real_one (real_opp (real_inv_pos s Hs)))).
    apply (RealSetoid.real_eq_plus_compat real_one (real_opp (real_mult (real_inv_pos s Hs) real_one))
                                          real_one (real_opp (real_inv_pos s Hs))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos s Hs) real_one) (real_inv_pos s Hs)).
      apply (real_mult_one (real_inv_pos s Hs)). }
  apply (real_eq_trans _ (real_plus (real_opp real_one) (real_opp (real_opp (real_inv_pos s Hs)))) _).
  { (* −(1 + −inv) == −1 + −−inv：opp_plus *)
    apply (real_opp_plus real_one (real_opp (real_inv_pos s Hs))). }
  apply (real_eq_trans _ (real_plus (real_opp real_one) (real_inv_pos s Hs)) _).
  { (* −1 + −−inv == −1 + inv：opp_opp *)
    apply (RealSetoid.real_eq_plus_compat (real_opp real_one) (real_opp (real_opp (real_inv_pos s Hs)))
                                          (real_opp real_one) (real_inv_pos s Hs)).
    - apply real_eq_refl.
    - apply (real_opp_opp (real_inv_pos s Hs)). }
  { (* −1 + inv == inv − 1：plus_comm *)
    apply (real_plus_comm (real_opp real_one) (real_inv_pos s Hs)). }
Qed.

End LogDiffPhase2.

(* ============ Phase 2b：Real 层 log 线性界（Bishop 逐 eps） ============
   Set 层（RealInterfaceEnhanced Id 版）线性界不可实例化到 Real 层（判例：Id 版不可实例化，
   Real 层是 req 版 RealInterfaceEnhancedSetoid）——Real 层线性界必须重证（判例论证延续）。
   目标：real_log_one_plus_le_eps（log(1+t) ≤ t+eps）+ real_log_one_plus_ge_eps（t−t² ≤ log(1+t)+eps）。
   数学：上界 = real_log_le_linear_eps 于 (1+t)；下界 = log(1+t)==−log(1/(1+t))（real_log_inv_one_inv
   反向）+ real_log_le_linear_eps 于 inv s + real_inv_minus_one_opp + t−t²≤t·inv s（Q 层已有 q_div）。 *)

Section LogDiffPhase2b.

(* 代数 1：(t−t²)(1+t) == t−t³（投影级，不含 inv；逐层展开投影 + ring） *)
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

(* 代数 2：0 < t ⟹ t³ ≥ 0（le_mult_compat 两次） *)
Lemma real_cube_nonneg : forall (t : Real),
  real_lt real_zero t -> real_le real_zero (real_mult t (real_mult t t)).
Proof.
  intros t Ht.
  (* 先 0 ≤ t·t：0·t ≤ t·t（le_mult_compat 于 0≤t、t>0） *)
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
  (* 再 0 ≤ t·(t·t)：0·t ≤ (t·t)·t（le_mult_compat 于 0≤t·t、t>0） *)
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

(* 代数 3：0 < t ⟹ t−t³ ≤ t（t³≥0 ⟹ −t³≤0 ⟹ t+(−t³) ≤ t+0） *)
Lemma real_minus_cube_le : forall (t : Real),
  real_lt real_zero t ->
  real_le (real_plus t (real_opp (real_mult t (real_mult t t)))) t.
Proof.
  intros t Ht.
  apply (real_le_trans (real_plus t (real_opp (real_mult t (real_mult t t))))
                       (real_plus t real_zero) t).
  - apply (real_le_plus_compat t t (real_opp (real_mult t (real_mult t t))) real_zero).
    + apply real_le_refl.
    + (* −t³ ≤ 0：0 ≤ t³ ⟹ −t³ ≤ −0 == 0 *)
      apply (real_le_trans (real_opp (real_mult t (real_mult t t))) (real_opp real_zero) real_zero).
      * apply (real_opp_le_compat real_zero (real_mult t (real_mult t t))).
        exact (real_cube_nonneg t Ht).
      * apply RealSetoid.real_eq_le. apply real_opp_zero.
  - apply RealSetoid.real_eq_le. apply real_plus_zero.
Qed.

(* 代数 4：0 < t、0 < 1+t ⟹ t−t² ≤ t·inv(1+t)
   (t−t²)(1+t) == t−t³ ≤ t [real_quad_prod + real_minus_cube_le]
   ⟹ le_mult_compat 于 inv s（正）：(t−t²)·s·inv s ≤ t·inv s
   ⟸ 左边换形 (t−t²)·(s·inv s) == t−t² [assoc 反向 + inv_correct + mult_one] *)
Lemma real_quad_div_ge : forall (t : Real),
  real_lt real_zero t ->
  forall (Hs : real_lt real_zero (real_plus real_one t)),
  real_le (real_plus t (real_opp (real_mult t t)))
          (real_mult t (real_inv_pos (real_plus real_one t) Hs)).
Proof.
  intros t Ht Hs.
  set (s := real_plus real_one t).
  (* 核心：(t−t²)·s ≤ t *)
  assert (Hcore : real_le (real_mult (real_plus t (real_opp (real_mult t t))) s) t).
  {
    apply (real_le_trans (real_mult (real_plus t (real_opp (real_mult t t))) s)
                         (real_plus t (real_opp (real_mult t (real_mult t t)))) t).
    - apply RealSetoid.real_eq_le. apply (real_quad_prod t).
    - apply (real_minus_cube_le t). exact Ht.
  }
  (* 由 Hcore 乘 inv s 正：le_mult_compat *)
  pose proof (real_le_mult_compat (real_mult (real_plus t (real_opp (real_mult t t))) s) t
                                  (real_inv_pos s Hs)
                                  (real_inv_pos_pos s Hs) Hcore) as Hstep.
  (* 左边换形：(A·s)·inv s == A *)
  apply (real_le_trans (real_plus t (real_opp (real_mult t t)))
                       (real_mult (real_mult (real_plus t (real_opp (real_mult t t))) s)
                                  (real_inv_pos s Hs))
                       (real_mult t (real_inv_pos s Hs))).
  - apply RealSetoid.real_eq_le.
    (* A == A·(s·inv s) == (A·s)·inv s *)
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

(* ============ 5. Real 层 log 线性界（Bishop 逐 eps） ============ *)
(* 上界：0 < 1+t、0 < eps ⟹ log(1+t) ≤ t + eps
   real_log_le_linear_eps 于 (1+t)：log(1+t) ≤ ((1+t)+(−1)) + eps == t + eps
   （real_succ_minus_one：(1+t)+(−1) == t） *)
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

(* 下界：0 < t、0 < 1+t、0 < eps ⟹ t−t² ≤ log(1+t) + eps
   链：t−t² ≤ t·inv s                [real_quad_div_ge]
       t·inv s == opp (minus (inv s) one)   [real_inv_minus_one_opp 反向 + opp_opp]
       opp (minus (inv s) one) ≤ opp (log (inv s)) + eps'   [real_log_le_linear_eps 于 inv s + opp_le_compat]
       opp (log (inv s)) == log s    [real_log_inv_one_inv 反向 + opp_opp]
       ⟹ t−t² ≤ log s + eps          [组装；eps' := eps] *)
Lemma real_log_one_plus_ge_eps : forall (t eps : Real),
  forall (Ht : real_lt real_zero t),
  forall (Hs : real_lt real_zero (real_plus real_one t)),
  real_lt real_zero eps ->
  real_le (real_plus t (real_opp (real_mult t t)))
          (real_plus (real_log (real_plus real_one t) Hs) eps).
Proof.
  intros t eps Ht Hs Heps.
  (* 全程用 s := real_plus real_one t 的 δ 等价（引理 let 绑定展开一致）；不 set 变量避免形态分裂 *)
  (* 段 1：t−t² ≤ t·inv s *)
  pose proof (real_quad_div_ge t Ht Hs) as Hseg1.
  (* 段 2a：t·inv s == opp (minus (inv s) one)
        real_inv_minus_one_opp t Ht Hs : opp (t·inv s) == inv s + (−1)
        opp 两边 + opp_opp ⟹ t·inv s == opp (inv s + (−1)) *)
  pose proof (real_inv_minus_one_opp t Ht Hs) as Himpo.
  (* t·inv s == opp (opp (t·inv s)) [real_opp_opp 反向]
             == opp (inv s + (−1)) [real_eq_opp_compat 于 Himpo] *)
  pose proof (real_eq_trans (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                            (real_opp (real_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs))))
                            (real_opp (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)))
                            (real_eq_sym (real_opp (real_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs))))
                                         (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                                         (real_opp_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs))))
                            (RealSetoid.real_eq_opp_compat (real_opp (real_mult t (real_inv_pos (real_plus real_one t) Hs)))
                                                           (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one))
                                                           Himpo)) as Hio.
  (* 段 2b：log (inv s) ≤ (inv s + (−1)) + eps（real_log_le_linear_eps 于 inv s） *)
  pose proof (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_inv_pos (real_plus real_one t) Hs) eps
                                     (real_inv_pos_pos (real_plus real_one t) Hs) Heps) as Hlin.
  (* 段 2c：opp ((inv s + (−1)) + eps) ≤ opp (log (inv s))（opp_le_compat） *)
  pose proof (real_opp_le_compat (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs))
                                 (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps)
                                 Hlin) as Hoc.
  (* 段 2d：opp (log (inv s)) == log s（real_log_inv_one_inv 反向 + opp_opp） *)
  pose proof (real_log_inv_one_inv (real_plus real_one t) Hs (real_inv_pos_pos (real_plus real_one t) Hs)) as Hli.
  pose proof (real_eq_trans (real_opp (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs)))
                            (real_opp (real_opp (real_log (real_plus real_one t) Hs)))
                            (real_log (real_plus real_one t) Hs)
                            (RealSetoid.real_eq_opp_compat (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs))
                                                           (real_opp (real_log (real_plus real_one t) Hs))
                                                           Hli)
                            (real_opp_opp (real_log (real_plus real_one t) Hs))) as Hol.
  (* 段 2e：le (t·inv s) (log s + eps)
        t·inv s == opp (inv s + (−1)) == opp ((inv s + (−1)) + eps) + eps
        opp ((inv s + (−1)) + eps) ≤ opp (log (inv s)) == log s
        ⟹ 组装 *)
  (* 先：opp ((inv s + (−1)) + eps) == opp (inv s + (−1)) + opp eps（opp_plus） *)
  pose proof (real_opp_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps) as Hop.
  (* 组装：real_le (plus (mult t (inv s)) (opp eps)) (log s) 由 Hoc + Hio + Hop 换形 *)
  assert (Hmid : real_le (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps))
                         (real_log (real_plus real_one t) Hs)).
  {
    (* 目标：t·inv s + (−eps) ≤ log s
       链：t·inv s + (−eps) == opp(inv s + (−1)) + (−eps)   [Hio]
           == opp((inv s + (−1)) + eps)                     [Hop 反向 + eq]
           ≤ opp (log (inv s)) == log s                      [Hoc + Hol] *)
    apply (real_le_trans (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps))
                         (real_opp (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps))
                         (real_log (real_plus real_one t) Hs)).
    - apply RealSetoid.real_eq_le.
      (* t·inv s + (−eps) == opp ((inv s + (−1)) + eps) *)
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
    - (* opp ((inv s + (−1)) + eps) ≤ opp (log (inv s)) == log s *)
      apply (real_le_trans (real_opp (real_plus (real_plus (real_inv_pos (real_plus real_one t) Hs) (real_opp real_one)) eps))
                           (real_opp (real_log (real_inv_pos (real_plus real_one t) Hs) (real_inv_pos_pos (real_plus real_one t) Hs)))
                           (real_log (real_plus real_one t) Hs)).
      + exact Hoc.
      + apply RealSetoid.real_eq_le. exact Hol.
  }
  (* 最终：t−t² ≤ t·inv s ≤ log s + eps（Hmid 两边加 eps） *)
  apply (real_le_trans (real_plus t (real_opp (real_mult t t)))
                       (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                       (real_plus (real_log (real_plus real_one t) Hs) eps)).
  - exact Hseg1.
  - (* t·inv s ≤ log s + eps：由 Hmid（t·inv s + (−eps) ≤ log s）两边加 eps *)
    apply (real_le_trans (real_mult t (real_inv_pos (real_plus real_one t) Hs))
                         (real_plus (real_plus (real_mult t (real_inv_pos (real_plus real_one t) Hs)) (real_opp eps)) eps)
                         (real_plus (real_log (real_plus real_one t) Hs) eps)).
    + apply RealSetoid.real_eq_le.
      (* t·inv s == (t·inv s + (−eps)) + eps *)
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

(* ============ 6. Real 层 log_div：log(a/b) == log a − log b ============
   链：log(a·inv b) == log a + log(inv b) [real_log_mult]
                     == log a + opp (log b) [real_log_inv_one_inv] *)
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

(* ============ 7. 代数恒等：(x+h)·inv x == 1 + h·inv x ============
   链：(x+h)·inv x == x·inv x + h·inv x [distrib]
                   == 1 + h·inv x      [inv_correct] *)
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
  - (* (x+h)·inv == inv·x + inv·h：mult_comm + distrib *)
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

(* ============ 8. Real 层可微性记录（Bishop 逐 eps，rdf 带正性前提） ============
   与 Set 层 Differentiable（L1369，df_correct 全称 x）不同——Real 层 log 带正性前提，
   可微性只对正 x 要求（判例判定：全称 x 在抽象接口不可证；Real 层逐 eps 复刻判例路线 c）。
   Bishop 形式（先例：real_le = Or lt eq 无法表达"非严格且不趋近"）：误差 ≤ eps·|h| + eps'
   对任意 eps' > 0（主界 eps 之外再留 Bishop 余量 eps'）。这使主定理组装可用 Bishop 线性界
   （判例判定的"非 Bishop 必要性"针对精确形式；Bishop 化后不再需要深水区非 Bishop 论证）。 *)
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

(* ============ 9. 主定理核心恒等：log(x+h) − log x == log(1 + h·inv x) ============
   链：log(x+h) − log x == log((x+h)·inv x)  [real_log_div]
                     == log(1 + h·inv x)     [real_succ_mult_inv 换形 + real_log_wd]
   正性证明（Ht : 0 < 1+h/x、Hxh : 0 < x+h）由调用方提供（主定理内从 |h| < x/2 推出）。 *)
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

(* ============ 10. 正性引理族（主定理 δ 论证） ============ *)
(* Q 层辅助：−x ≤ |x|（q_neg_le_abs 主文件不可见，自证） *)
Lemma q_neg_le_abs_local : forall x : Q, QleT' (- x) (Qabs x).
Proof.
  intros x.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (- x)) _).
  - apply Qle_Qabs.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
Qed.

(* 10a. |h| < e ⟹ −e < h（abs 下界，逐点 q_neg_le_abs：−|h_n| ≤ h_n）
   数学：h ≥ −|h| > −e ⟹ −e < h。 *)
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
      - (* −|h_n| ≤ h_n：q_neg_le_abs_local 于 h_n，换形 projT1 (real_abs h) n == Qabs (h_n) *)
        apply (Qle_trans (Qopp (projT1 (real_abs h) n)) (Qopp (Qabs (projT1 h n))) (projT1 h n)).
        + (* −(real_abs h)_n == −Qabs (h_n)：Qeq 换形 *)
          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qopp_comp (projT1 (real_abs h) n) (Qabs (projT1 h n))).
          exact (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        + (* −Qabs (h_n) ≤ h_n：Qopp_le_compat 于 q_neg_le_abs_local + opp_opp *)
          apply (Qle_trans (Qopp (Qabs (projT1 h n))) (Qopp (Qopp (projT1 h n))) (projT1 h n)).
          * apply (Qopp_le_compat (Qopp (projT1 h n)) (Qabs (projT1 h n))).
            apply (Qle_trans (Qopp (projT1 h n)) (Qabs (Qopp (projT1 h n))) (Qabs (projT1 h n))).
            -- apply Qle_Qabs.
            -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qopp_involutive.
    }
    (* 目标：e0 < h_n − (opp e)_n。链：e0 < e_n − |h_n| ≤ e_n + h_n ≤ h_n − (opp e)_n
       （Hq + Hle + 换形：h_n + e_n == h_n − (opp e)_n，因 (opp e)_n == −e_n） *)
    apply (Qlt_le_trans e0 (projT1 e n + projT1 h n) (projT1 h n - projT1 (real_opp e) n)).
    + apply (Qlt_le_trans e0 (projT1 e n - projT1 (real_abs h) n) (projT1 e n + projT1 h n)).
      * exact Hq.
      * exact Hle.
    + (* e_n + h_n ≤ h_n − (opp e)_n：h_n + e_n == h_n + (−(opp e)_n)（Hpt_opp）且 comm *)
      apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      apply (Qeq_trans (projT1 e n + projT1 h n) (projT1 h n + projT1 e n)
                       (projT1 h n - projT1 (real_opp e) n)).
      * apply Qplus_comm.
      * (* h_n + e_n == h_n − (opp e)_n：(opp e)_n == −e_n（Hpt_opp）setoid 换形 + ring *)
        setoid_rewrite Hpt_opp. ring.
Qed.

(* 10b. 0 < x、|h| < x/2 ⟹ 0 < x+h
   链：|h| < x·inv2 < x（inv2 < 1、0 < x）⟹ |h| < x（real_lt_trans）
       ⟹ −x < h（real_abs_lt_lower）⟹ x+(−x) < x+h（real_lt_plus_compat_le_lt）
       ⟹ 0 < x+h（real_eq_lt_lt：x+(−x) == 0）。 *)
(* 辅助：inv 1 == 1（inv_correct：1·inv 1 == 1 ⟹ inv 1 == 1·inv 1 == 1） *)
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

(* 辅助：inv 2 < 1（real_inv_pos_lt_contra 于 1 < 2 + inv 1 == 1） *)
Lemma real_two_pos_local : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus real_one real_one)).
  - apply real_eq_sym. apply (real_plus_zero real_zero).
  - apply (real_lt_plus_compat real_zero real_one real_zero real_one
                               (real_lt_zero_one) (real_lt_zero_one)).
Qed.

Lemma real_inv_two_lt_one : real_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) real_one.
Proof.
  (* real_lt_eq_lt (inv2) (inv1) one：lt (inv2) (inv1)（inv_lt_contra 于 1<2）+ eq (inv1) one *)
  apply (real_lt_eq_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                       (real_inv_pos real_one (real_lt_zero_one))
                       real_one).
  - apply (real_inv_pos_lt_contra real_one (real_plus real_one real_one)
                                  (real_lt_zero_one) (real_two_pos_local)).
    (* 1 < 2：1+0 < 1+1（lt_plus_compat_le_lt：le 1 1 + lt 0 1）再桥 1+0==1 *)
    apply (real_eq_lt_lt real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    + apply real_eq_sym. apply (real_plus_zero real_one).
    + apply (real_lt_plus_compat_le_lt real_one real_one real_zero real_one
                                       (real_le_refl real_one) (real_lt_zero_one)).
  - apply real_inv_one.
Qed.

(* 辅助：0 < x ⟹ x·inv2 < x（mult_lt_compat_l：inv2 < 1、0 < x） *)
Lemma real_half_lt_self : forall (x : Real) (Hx : real_lt real_zero x),
  real_lt (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x) x.
Proof.
  intros x Hx.
  (* 链：inv2·x == x·inv2（comm）< x·1 == x（mult_lt_compat_l：inv2<1、0<x） *)
  apply (real_eq_lt_lt (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                       (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                       x).
  - apply (real_mult_comm (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x).
  - (* x·inv2 < x：real_lt_eq_lt (x·inv2) (x·1) x：lt（mult_lt_compat_l）+ eq（mult_one） *)
    apply (real_lt_eq_lt (real_mult x (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                         (real_mult x real_one)
                         x).
    + (* x·inv2 < x·1：mult_lt_compat_l（c:=x, a:=inv2, b:=1） *)
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
  (* 段 1：|h| < x（|h| < x·inv2 < x） *)
  assert (Hhx : real_lt (real_abs h) x).
  { apply (real_lt_trans (real_abs h)
                         (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                         x).
    - exact Hh.
    - exact (real_half_lt_self x Hx). }
  (* 段 2：−x < h（real_abs_lt_lower） *)
  pose proof (real_abs_lt_lower h x Hhx) as Hlower.
  (* 段 3：x+(−x) < x+h（lt_plus_compat_le_lt：le x x + lt (−x) h） *)
  apply (real_eq_lt_lt real_zero (real_plus x (real_opp x)) (real_plus x h)).
  - apply real_eq_sym. apply (real_plus_opp x).
  - apply (real_lt_plus_compat_le_lt x x (real_opp x) h).
    + apply real_le_refl.
    + exact Hlower.
Qed.

(* ============ 11. 主定理辅助引理 ============ *)
(* 11a. 0 < x ⟹ |h·inv x| == |h|·inv x（abs_mult + abs_pos 于 inv x） *)
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

(* ============ 12. |h| < x ⟹ x+h > 0（real_plus_pos_half 的直接变体，δ 论证用） ============
   链：|h| < x ⟹ −x < h（real_abs_lt_lower）⟹ x+(−x) < x+h（lt_plus_compat_le_lt）
       ⟹ 0 < x+h（real_eq_lt_lt：x+(−x) == 0）。 *)
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

(* ============ 13. 1 + h·inv x > 0（|h| < x 时；1+t > 1−1 == 0 侧论证） ============
   数学：t := h·inv x，|t| < 1（|h| < x ⟹ |h|·inv x < x·inv x == 1）
        ⟹ 1+t > 1−|t| > 0。用 real_abs_lt_lower 于 e := 1：−1 < t ⟹ 1+(−1) < 1+t。 *)
Lemma real_one_plus_t_pos : forall (x h : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h) x ->
  real_lt real_zero (real_plus real_one (real_mult h (real_inv_pos x Hx))).
Proof.
  intros x h Hx Hh.
  (* 段 1：|h·inv x| < 1：|h| < x 且 inv x > 0 ⟹ |h|·inv x < x·inv x == 1
     |h·inv x| == |h|·inv x（real_abs_mult_inv） *)
  assert (Ht1 : real_lt (real_abs (real_mult h (real_inv_pos x Hx))) real_one).
  {
    (* |h·inv x| == |h|·inv x < x·inv x == 1 *)
    apply (real_eq_lt_lt (real_abs (real_mult h (real_inv_pos x Hx)))
                         (real_mult (real_abs h) (real_inv_pos x Hx))
                         real_one).
    - apply (real_abs_mult_inv x h Hx).
    - (* |h|·inv x < x·inv x == 1：mult_lt_compat_l 于 (|h|, x, inv x) + comm 换位 *)
      apply (real_lt_eq_lt (real_mult (real_abs h) (real_inv_pos x Hx))
                           (real_mult x (real_inv_pos x Hx))
                           real_one).
      + (* |h|·inv x < x·inv x：|h|·inv x == inv x·|h| < inv x·x == x·inv x *)
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
  (* 段 2：−1 < h·inv x（real_abs_lt_lower 于 e := 1） *)
  pose proof (real_abs_lt_lower (real_mult h (real_inv_pos x Hx)) real_one Ht1) as Hlower.
  (* 段 3：1+(−1) < 1+t（lt_plus_compat_le_lt：le 1 1 + lt (−1) t）⟹ 0 < 1+t *)
  apply (real_eq_lt_lt real_zero (real_plus real_one (real_opp real_one))
                       (real_plus real_one (real_mult h (real_inv_pos x Hx)))).
  - apply (real_plus_opp real_one).
  - apply (real_lt_plus_compat_le_lt real_one real_one (real_opp real_one)
                                     (real_mult h (real_inv_pos x Hx))).
    + apply real_le_refl.
    + exact Hlower.
Qed.

(* ============ 14. 主定理 δ 论证辅助 ============ *)
(* 14a. |h| < min A B ⟹ |h| < A + eps（min_le_l_eps 于 eps + lt_le_trans） *)
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

(* 14b. 对称：|h| < min A B ⟹ |h| < B + eps *)
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

(* 14c. 0 < x ⟹ 3x/4 < x（x·(3/4) < x·1，3/4 < 1；3/4 := inv4·3 用 inv2 组合：3/4 == 1/2+1/4？
   简化：3x/4 == x/2 + x/4，x/2 + x/4 < x ⟸ x/2 < x 且 x/4 < x/2 —— 走 real_half_lt_self 两次。
   实际主定理只需 x/2 + x/4 < x：x/2 < x（half_lt_self）且 x/4 ≤ x/2 需要 1/4 ≤ 1/2（inv2 自乘）。 *)

(* ============ 15. δ 论证核心恒等：inv2·x + inv2·x == x ============
   链：inv2·x + inv2·x == (inv2+inv2)·x [distrib 反向]
                      == 1·x == x        [2·inv2 == 1：inv2+inv2 == 1（2 定义）]
   2·inv2 == 1 即 inv_pos_correct (1+1)；inv2+inv2 == 2·inv2 需 2 == 1+1（定义）+ mult_one。 *)
Lemma real_half_plus_half : forall (x : Real),
  real_eq (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                     (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x))
          x.
Proof.
  intros x.
  (* inv2·x + inv2·x == (inv2+inv2)·x [distrib 反向：a·x + b·x == (a+b)·x]
                  == (2·inv2)·x == 1·x == x [inv_correct：(1+1)·inv2 == 1] *)
  apply (real_eq_trans (real_plus (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                                  (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x))
                       (real_mult (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                             (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) x)
                       x).
  - (* inv2·x + inv2·x == (inv2+inv2)·x：右分配经 comm + distrib：
        inv2·x == x·inv2（comm）；(inv2+inv2)·x == x·(inv2+inv2)（comm）
        == x·inv2 + x·inv2（distrib）== inv2·x + inv2·x（comm ×2） *)
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
  - (* (inv2+inv2)·x == 1·x == x：(inv2+inv2) == 1 由 inv_pos_correct（2·inv2==1）且 2==1+1。
        inv_pos_correct (plus one one) : (1+1)·inv2 == 1；需 comm：(1+1)·inv2 == inv2·(1+1)？
        不——inv_pos_correct 给 mult (plus one one) (inv_pos (plus one one) ...) == one。
        (inv2+inv2)·x == 1·x 需 inv2+inv2 == 1：由 2·inv2 == 1 且 2 == 1+1 且 comm：
        (1+1)·inv2 == 1，inv2·(1+1) == 1（comm），(inv2+inv2) == inv2·(1+1)（distrib 反向：inv2·1+inv2·1 == inv2·(1+1)，
        但 inv2+inv2 == inv2·1+inv2·1（mult_one ×2））⟹ inv2+inv2 == 1。 *)
    apply (real_eq_trans (real_mult (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) x)
                         (real_mult real_one x)
                         x).
    + apply (RealSetoid.real_eq_mult_compat (real_plus (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))
                                                        (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)))
                                            x real_one x).
      * (* inv2 + inv2 == 1：inv2·1 + inv2·1 == inv2·(1+1) == 2·inv2 == 1 *)
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
           ++ (* inv2·(1+1) == 1：comm + inv_pos_correct *)
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

(* ============ 16. t² ≥ 0（逐点 Qmult_le_0_compat；主定理 quad_bound 等需要） ============ *)

(* Bishop 版：0 ≤ t² + eps（任意 eps > 0；判例：非严格不趋近 → Bishop） *)
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
    (* 逐点：t_n² + eps_n > eps0（eps_n > eps0 且 t_n² ≥ 0） *)
    assert (Hpt : projT1 (real_mult t t) n == projT1 t n * projT1 t n) by (apply qeqT_imp_qeq; apply real_mult_proj).
    assert (Hpt_eps : projT1 (real_plus (real_mult t t) eps) n == projT1 (real_mult t t) n + projT1 eps n)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    (* Q 层平方非负（Qsquare_nonneg，项目已有，L3383） *)
    assert (Hs : Qle 0 (projT1 t n * projT1 t n)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg (projT1 t n))).
    (* eps_n > eps0（HN0 是差分形式：QltT eps0 (eps_n − 0)） *)
    assert (Hn0 : Qlt eps0 (projT1 eps n)).
    { apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n Hn).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hz. ring. }
    (* 目标：QltT eps0 (P − 0)，P := projT1 (real_plus (real_mult t t) eps) n；纯 Qeq 链（判例） *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (projT1 (real_mult t t) n + projT1 eps n) _).
    { (* eps0 < projT1(real_mult t t) n + eps_n *)
      apply (Qlt_le_trans _ (projT1 eps n) _).
      { exact Hn0. }
      { (* eps_n <= projT1(real_mult t t) n + eps_n *)
        apply (Qle_trans _ (0 + projT1 eps n) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qplus_le_compat 0 (projT1 (real_mult t t) n) (projT1 eps n) (projT1 eps n)).
          { (* 0 <= projT1(real_mult t t) n（经 t_n²） *)
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

(* ============ 17. 主定理下界链（t<0 侧路线，无符号统一：t − log(1+t) ≤ t²/(1+t) + eps） ============ *)

(* 17a：real_inv_minus_one_opp 去 Ht 版（原 L104 带 0<t 前提，证明未用 Ht；t<0 侧需要无 Ht） *)
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

(* 17b：代数 t + (inv s − 1) == t²·inv s（无 Ht；Real 层显式链） *)
Lemma real_t_plus_inv_minus_one : forall (t : Real),
  let s := real_plus real_one t in
  forall (Hs : real_lt real_zero s),
  real_eq (real_plus t (real_plus (real_inv_pos s Hs) (real_opp real_one)))
          (real_mult (real_mult t t) (real_inv_pos s Hs)).
Proof.
  intros t s Hs.
  (* 段 1：t + (inv s − 1) == t + opp(t·inv s)（real_inv_minus_one_opp_noHt 反向） *)
  apply (real_eq_trans _ (real_plus t (real_opp (real_mult t (real_inv_pos s Hs)))) _).
  - apply (RealSetoid.real_eq_plus_compat t (real_plus (real_inv_pos s Hs) (real_opp real_one))
                                        t (real_opp (real_mult t (real_inv_pos s Hs)))).
    + apply real_eq_refl.
    + apply real_eq_sym. exact (real_inv_minus_one_opp_noHt t Hs).
  - (* 段 2：t + opp(t·inv s) == t²·inv s *)
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
        { (* t·(1 − inv) == t·((s−1)·inv)：内层 1 − inv == (s−1)·inv *)
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

(* 17c：t − log(1+t) ≤ t²·inv(1+t) + eps（无符号统一；s := 1+t，需 0<s）
   链：t − log s == t + log(inv s)                    [real_log_inv_one_inv 反向 + eq_le]
        ≤ t + ((inv s − 1) + eps)                     [le_linear 于 inv s + le_plus_compat]
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
  - (* t − log s ≤ t + log(inv s)：eq_le（log(inv s) == opp(log s) 反向） *)
    apply (RealSetoid.real_eq_le (real_plus t (real_opp (real_log s Hs)))
                                 (real_plus t (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs)))).
    apply (RealSetoid.real_eq_plus_compat t (real_opp (real_log s Hs))
                                          t (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs))).
    + apply real_eq_refl.
    + apply real_eq_sym. exact (real_log_inv_one_inv s Hs (real_inv_pos_pos s Hs)).
  - apply (real_le_trans _ (real_plus t (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps)) _).
    + (* t + log(inv s) ≤ t + ((inv s − 1) + eps)：le_plus_compat *)
      apply (real_le_plus_compat t t
                                 (real_log (real_inv_pos s Hs) (real_inv_pos_pos s Hs))
                                 (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps)).
      * apply real_le_refl.
      * exact (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_inv_pos s Hs) eps
                                                (real_inv_pos_pos s Hs) Heps).
    + (* t + ((inv s − 1) + eps) ≤ t²·inv s + eps：eq_le（assoc + real_t_plus_inv_minus_one） *)
      apply (RealSetoid.real_eq_le (real_plus t (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps))
                                   (real_plus (real_mult (real_mult t t) (real_inv_pos s Hs)) eps)).
      apply (real_eq_trans (real_plus t (real_plus (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps))
                           (real_plus (real_plus t (real_plus (real_inv_pos s Hs) (real_opp real_one))) eps)
                           (real_plus (real_mult (real_mult t t) (real_inv_pos s Hs)) eps)).
      * (* assoc：t + (X + eps) == (t + X) + eps（real_plus_assoc，X := inv s + (−1)） *)
        apply (real_plus_assoc t (real_plus (real_inv_pos s Hs) (real_opp real_one)) eps).
      * (* (t + X) + eps == t²·inv s + eps *)
        apply (RealSetoid.real_eq_plus_compat (real_plus t (real_plus (real_inv_pos s Hs) (real_opp real_one)))
                                              eps
                                              (real_mult (real_mult t t) (real_inv_pos s Hs))
                                              eps).
        -- exact (real_t_plus_inv_minus_one t Hs).
        -- apply real_eq_refl.
Qed.

(* ============ 18. 放缩：t²·inv s ≤ t²·2 + eps（需 1/2 < s；逐点 Q 层） ============
   主定理下界链收尾：t²/(1+t) ≤ 2t²。
   Real 层：real_inv_pos (real_plus real_one real_one) (real_two_pos_local) < s ⟹ inv s < inv real_inv_pos (real_plus real_one real_one) (real_two_pos_local) == 2（strict，避开 real_le eq 分支逐点停滞（判例）
   逐点：t²·inv s ≤ t²·2 + eps（invs ≤ 2 逐点 + t² ≥ 0 Qsquare_nonneg + 见证 eps0） *)
Lemma real_quad_div_le_two_eps : forall (t s eps : Real)
  (Hs : real_lt real_zero s)
  (Hs12 : real_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) s)
  (Heps : real_lt real_zero eps),
  real_le (real_mult (real_mult t t) (real_inv_pos s Hs))
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps).
Proof.
  intros t s eps Hs Hs12 Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  (* inv s < 2：real_inv_pos (real_plus real_one real_one) (real_two_pos_local) < s ⟹ inv s < inv real_inv_pos (real_plus real_one real_one) (real_two_pos_local) == 2（strict，Real 层） *)
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
    (* eps0 < en（HN0 差分桥） *)
    assert (Hepsn : Qlt eps0 en).
    { unfold en. apply (Qlt_le_trans _ (projT1 eps n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hzero. ring. }
    (* invs 投影归约（n ≥ Ns）：projT1 I n == Qinv (us n) *)
    assert (Hinvs : projT1 I n == Qinv (us n)).
    { unfold I. cbn [real_inv_pos projT1].
      assert (Hl : Nat.leb Ns n = true) by (apply Nat.leb_le; exact Hns).
      rewrite Hl. reflexivity. }
    (* 0 ≤ p2 − invs（HN2b：e2 < p2 − invs） *)
    assert (Hpnz : Qle 0 (p2 - projT1 I n)).
    { unfold p2. apply (Qle_trans _ e2 _).
      - apply Qlt_le_weak. apply QltT_to_Qlt. exact He2.
      - apply Qlt_le_weak. apply QltT_to_Qlt.
        unfold I. exact (HN2b n (NatLe_lift _ _ Hn2b)). }
    (* tn² ≥ 0 *)
    assert (Hsq : Qle 0 (tn * tn)) by (apply QleT'_to_Qle; apply (Qsquare_nonneg tn)).
    (* 投影展开：qn == (tn·tn)·projT1 I n、pn == (tn·tn)·p2 + en *)
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
    (* 主链：QltT eps0 (pn − qn)：eps0 < en ≤ tn·tn·(p2−invs) + en == pn − qn *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ en _).
    { exact Hepsn. }
    { (* en ≤ pn − qn *)
      apply (Qle_trans _ (tn * tn * (p2 - projT1 I n) + en) _).
      { (* en ≤ tn·tn·(p2−invs) + en：非负项（经 en + y 换位） *)
        apply (Qle_trans _ (en + tn * tn * (p2 - projT1 I n)) _).
        { apply (Qle_plus_nonneg_r en (tn * tn * (p2 - projT1 I n))).
          apply (Qmult_le_0_compat (tn * tn) (p2 - projT1 I n)).
          { exact Hsq. }
          { exact Hpnz. } }
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. } }
      { (* tn·tn·(p2−invs) + en ≤ pn − qn：Qeq 桥 *)
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        apply (Qeq_trans _ ((tn * tn) * p2 + en - (tn * tn) * projT1 I n) _).
        { (* 子目标1：tn·tn·(p2−invs) + en == (tn·tn·p2+en) − tn·tn·invs：ring *)
          unfold Qminus. ring. }
        { (* 子目标2：(tn·tn·p2+en) − tn·tn·invs == pn − qn（Qplus_comp 反向） *)
          apply Qeq_sym.
          apply (Qplus_comp pn ((tn * tn) * p2 + en) Hpn
                            (Qopp qn) (Qopp ((tn * tn) * projT1 I n))).
          apply (Qopp_comp qn ((tn * tn) * projT1 I n)). exact Hqn. } } }
Qed.

(* ============ 19. 主定理组装组件：严格 min 拆分 + |t|<1/2 链 + 代数 ============ *)

(* 19a：|h| < min A B ⟹ |h| < A（严格；逐点：e < min_n − |h|_n ≤ A_n − |h|_n） *)
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

(* 19b：|h| < min A B ⟹ |h| < B（严格，对称） *)
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

(* 19c：代数 (inv2·x)·inv x == inv2（x > 0） *)
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

(* 19d：−inv2 < t ⟹ inv2 < 1+t（half+half == 1 组装：1+t == half+(half+t)） *)
Lemma real_half_lt_one_plus_t : forall (t : Real),
  real_lt (real_opp (real_inv_pos (real_plus real_one real_one) (real_two_pos_local))) t ->
  real_lt (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) (real_plus real_one t).
Proof.
  intros t Ht.
  set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  (* 段 1：0 < half + t（−half < t 加 half：(−half)+half < t+half，桥 zero == (−half)+half） *)
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
  (* 段 2：half < half + (half + t)（half+0 < half+(half+t)，0 < half+t） *)
  assert (Hmid : real_lt half (real_plus half (real_plus half t))).
  { apply (real_eq_lt_lt half (real_plus half real_zero) (real_plus half (real_plus half t))).
    - apply real_eq_sym. apply (real_plus_zero half).
    - apply (real_lt_plus_compat_le_lt half half real_zero (real_plus half t)).
      + apply real_le_refl.
      + exact Hhalf_t. }
  (* 段 3：half + (half + t) == 1 + t（assoc + half+half == 1） *)
  apply (real_lt_eq_lt half (real_plus half (real_plus half t)) (real_plus real_one t)).
  - exact Hmid.
  - apply (real_eq_trans (real_plus half (real_plus half t))
                         (real_plus (real_plus half half) t)
                         (real_plus real_one t)).
    + apply (real_plus_assoc half half t).
    + apply (RealSetoid.real_eq_plus_compat (real_plus half half) t real_one t).
      * (* half + half == 1：real_half_plus_half 于 1 *)
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

(* 19e：|h| < inv2·x ⟹ |h·inv x| < inv2（|h·inv x| == |h|·inv x < (inv2·x)·inv x == inv2） *)
Lemma real_t_abs_lt_half : forall (x h : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h) (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x) ->
  real_lt (real_abs (real_mult h (real_inv_pos x Hx)))
          (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
Proof.
  intros x h Hx Hhx.
  set (half := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  (* 段 1：|h·inv x| == |h|·inv x *)
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
  (* 段 2：|h|·inv x < (half·x)·inv x *)
  assert (Hmid : real_lt (real_mult (real_abs h) (real_inv_pos x Hx))
                         (real_mult (real_mult half x) (real_inv_pos x Hx))).
  { unfold half.
    apply (real_mult_lt_compat (real_abs h) (real_mult (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) x)
                               (real_inv_pos x Hx)).
    - exact Hhx.
    - apply (real_inv_pos_pos x Hx). }
  (* 段 3：(half·x)·inv x == half *)
  assert (Heq : real_eq (real_mult (real_mult half x) (real_inv_pos x Hx)) half).
  { unfold half. exact (real_half_x_mult_inv x Hx). }
  (* 组装：|h·inv x| == |h|·inv x < (half·x)·inv x == half *)
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

(* ============ 20. abs 双向桥（主定理组装）：|X| ≤ 2t² + eps1 + eps2 + eps ============ *)

(* 20a：Q 层 |x| ≤ a + b（x ≤ a、−x ≤ b、0 ≤ a、0 ≤ b；三分 Qlt_le_dec） *)
Lemma q_abs_le_plus : forall (x a b : Q),
  QleT' x a -> QleT' (- x) b -> QleT' 0 a -> QleT' 0 b -> QleT' (Qabs x) (a + b).
Proof.
  intros x a b Hxa Hxb Ha Hb.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec x 0) as [Hxlt | Hxge].
  - (* x < 0：Qabs x == −x ≤ b ≤ a + b *)
    apply (Qle_trans _ (- x) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_neg x). apply Qlt_le_weak. exact Hxlt.
    + apply (Qle_trans _ b _).
      * apply QleT'_to_Qle; exact Hxb.
      * apply (Qle_trans _ (b + a) _).
        -- apply (Qle_plus_nonneg_r b a). apply QleT'_to_Qle; exact Ha.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - (* x ≥ 0：Qabs x == x ≤ a ≤ a + b *)
    apply (Qle_trans _ x _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_pos x). exact Hxge.
    + apply (Qle_trans _ a _).
      * apply QleT'_to_Qle; exact Hxa.
      * apply (Qle_plus_nonneg_r a b). apply QleT'_to_Qle; exact Hb.
Qed.

(* 20b：Q 层 x ≤ |x|（三分 Qlt_le_dec） *)
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

(* 20c：Q 层 |x−y| < c ⟹ x ≤ y + c *)
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

(* 20d：Q 层 0 < a、a < y−x ⟹ x ≤ y（lt 差分 ⟹ 非严格） *)
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

(* ============ 21. abs 双向桥（4 分支引理 + 主引理）：X ≤ eps1、−X ≤ 2t²+eps2 ⟹ |X| ≤ 2t²+eps1+eps2+eps ============ *)

(* 21a：lt/lt 分支（X < eps1、−X < 2t²+eps2） *)
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
    (* B_n == (tn·tn)·p2 + e2n（2t²+eps2 投影展开） *)
    assert (HBeq : projT1 (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) n == (tn * tn) * p2 + e2n).
    { unfold tn, p2, e2n.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult t t) (real_plus real_one real_one)) eps2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult t t) (real_plus real_one real_one) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
      cbn [projT1]. ring. }
    (* xn ≤ e1n（lt 差分） *)
    assert (Hxa_n : Qle xn e1n).
    { unfold xn, e1n. apply QleT'_to_Qle. apply (q_lt_diff_le a (projT1 X n) (projT1 eps1 n)).
      - exact Ha.
      - exact (HNa n (NatLe_lift _ _ Hna)). }
    (* −xn ≤ (tn·tn)·p2 + e2n（lt 差分；Qeq 链展开 B_n、oppX_n） *)
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
    (* Qabs xn ≤ (tn·tn)·p2 + e1n + e2n（q_abs_le_plus） *)
    assert (Habsn : Qle (Qabs xn) ((tn * tn) * p2 + e1n + e2n)).
    { apply (Qle_trans _ (e1n + ((tn * tn) * p2 + e2n)) _).
      - apply QleT'_to_Qle. apply (q_abs_le_plus xn e1n ((tn * tn) * p2 + e2n)).
        + apply Qle_to_QleT'. exact Hxa_n.
        + apply Qle_to_QleT'. exact Hxb_n.
        + apply Qle_to_QleT'. exact He1n_pos.
        + apply Qle_to_QleT'. exact Hqpos.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* 主链：eps0 < en ≤ pn − qn *)
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

(* 21b：Q 层 0 < q ⟹ q/2 < q（eq 分支柯西余量桥） *)
Lemma q_half_pos : forall q : Q, QltT 0 q -> QltT 0 (q / 2).
Proof.
  intros q Hq.
  apply Qlt_to_QltT.
  apply (Qlt_shift_div_l 0 q 2).
  - reflexivity.
  - simpl. apply QltT_to_Qlt. exact Hq.
Qed.

(* 21c：lt/eq 分支（X < eps1、−X == 2t²+eps2 柯西） *)
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
    { (* eps0/2 < en − eps0/2：0 < en − eps0（Hepsn）⟹ (en−eps0) + eps0/2 > 0 + eps0/2 *)
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

(* 21b''：Q 层 0 < q ⟹ 0 < q/4（ee 分支双侧柯西） *)
Lemma q_quarter_pos : forall q : Q, QltT 0 q -> QltT 0 (q / 4).
Proof.
  intros q Hq.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (q / 2 / 2) _).
  - apply QltT_to_Qlt. apply (q_half_pos (q / 2)). apply (q_half_pos q). exact Hq.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* 21e：eq/eq 分支（X == eps1、−X == 2t²+eps2，双侧柯西 eps0/4） *)
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

(* 21d：eq/lt 分支（X == eps1 柯西、−X < 2t²+eps2） *)
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
    (* xn ≤ e1n + eps0/2（eq 柯西） *)
    assert (Hxa_n : Qle xn (e1n + eps0 / 2)).
    { unfold xn, e1n.
      apply QleT'_to_Qle. apply (q_abs_lt_le (projT1 X n) (projT1 eps1 n) (eps0 / 2)).
      exact (HXAeq_n n (NatLe_lift _ _ Hnxa)). }
    (* −xn ≤ (tn·tn)·p2 + e2n（lt 差分） *)
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
(* 21f：abs 桥主引理（4 分支分发） *)
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

(* ============ 22. 最终放缩：2·(h·inv x)² ≤ (eps/2)·|h| + eps' ============ *)

(* 22a：Q 层 q² == |q|²（三分 Qlt_le_dec） *)
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

(* 22b：Q 层 2a²·iv² ≤ (e/2)·a（a ≥ 0、a ≤ e·x²/4、x·iv == 1） *)
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

(* 22c：主定理最终放缩（逐点 Q 层，见证 eps0'） *)
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
    (* 展开断言 *)
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
    (* |hn| ≤ en·xn²/4（HNd 差分 + d > 0） *)
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
    (* pn == (en/2)·|hn| + en'（inv2_n == /2 桥） *)
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
    (* 主链：eps0 < en' ≤ pn − qn *)
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

(* ============ 23. 主定理辅助：real_eq 的 abs 兼容（D==X ⟹ |D|==|X|） ============
   逐点：|Qabs(x_n) − Qabs(y_n)| ≤ Qabs(x_n − y_n)（Qabs_triangle_reverse 两侧 + Qabs_Qle_condition）
   Qabs_Qle_condition : Qabs x ≤ y <-> −y ≤ x ≤ y *)
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
    + (* 换形：projT1 (real_abs x) n == Qabs (projT1 x n)（real_abs_proj） *)
      apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (real_abs x) n - projT1 (real_abs y) n)
                     (Qabs (projT1 x n) - Qabs (projT1 y n))).
      apply (Qplus_comp (projT1 (real_abs x) n) (Qabs (projT1 x n)) (qeqT_imp_qeq _ _ (real_abs_proj x n))
                        (Qopp (projT1 (real_abs y) n)) (Qopp (Qabs (projT1 y n)))
                        (Qopp_comp (projT1 (real_abs y) n) (Qabs (projT1 y n)) (qeqT_imp_qeq _ _ (real_abs_proj y n)))).
    + (* |Qabs x_n − Qabs y_n| ≤ Qabs(x_n − y_n)：Qabs_Qle_condition 双分支 *)
      apply (proj2 (Qabs_Qle_condition (Qabs (projT1 x n) - Qabs (projT1 y n)) (Qabs (projT1 x n - projT1 y n)))).
      split.
      { (* −|x−y| ≤ |x|−|y|：|y|−|x| ≤ |y−x|（triangle_reverse y x）+ opp 两侧 + |y−x|==|x−y| *)
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
      { (* |x|−|y| ≤ |x−y|：triangle_reverse x y *)
        apply (Qabs_triangle_reverse (projT1 x n) (projT1 y n)). }
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.

(* ============ 24. 主定理 real_log_differentiable（Bishop 逐 eps，判例组新路线） ============
   rdf x Hx := inv_pos x Hx。
   δ := min (x/2) (eps·x²/4)。份额 5×inv8·eps'（合计 5eps'/8 ≤ eps'）。
   结构：
     前提链：|h|<δ ⟹ |h|<x/2（min_lt_l）⟹ |t|<1/2（t_abs_lt_half）⟹ −1/2<t（abs_lt_lower）
              ⟹ 1/2<1+t（half_lt_one_plus_t）⟹ 0<1+t（trans）
             |h|<eps4（min_lt_r）⟹ 22c 前提
     D == X（log(x+h)−log x−inv x·h == log(1+t)−t，opp_plus + assoc + real_log_plus_diff + mult_comm）
     上界 X ≤ share（le_eps）
     下界 −X ≤ 2t²+2share（t_minus_log_bound + quad_div_le_two_eps 串联）
     abs 桥：|X| ≤ 2t² + (share+2share) + share == 2t² + 4share
     22c：2t² ≤ (eps/2)|h| + share
     汇总：|D| ≤ |X| ≤ (eps/2)|h| + 5share ≤ eps|h| + eps'（5share ≤ eps' 逐点 Q 层） *)
Lemma real_log_differentiable : forall (x : Real) (Hx : real_lt real_zero x),
  RealDifferentiable real_log.
Proof.
  intros x Hx.
  exists (fun y Hy => real_inv_pos y Hy).
  intros x0 Hx0 eps Heps.
  (* 常量 *)
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (four_inv := real_mult two_inv two_inv).
  set (eight_inv := real_mult four_inv two_inv).
  set (half_x := real_mult two_inv x0).
  set (eps_x2 := real_mult eps (real_mult x0 x0)).
  set (eps4 := real_mult four_inv eps_x2).      (* eps·x²/4 *)
  set (delta := real_min half_x eps4).
  exists delta.
  split.
  - (* 0 < delta：min_pos *)
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
    (* 份额 share := inv8·eps'（5 份共用） *)
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
    (* 前提链 *)
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
    (* 断言 D == X *)
    assert (HDX : real_eq
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
      X).
    {
      (* D == log(x0+h) + (opp(log x0) + opp(inv·h))：opp_plus 拆开 *)
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
      - (* (log(x0+h) + (opplog + oppinv)) == (log(x0+h) − log x0) + (−inv·h)：assoc *)
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
          * (* log(x0+h) − log x0 == log(1+t)：real_log_plus_diff *)
            apply (real_log_plus_diff x0 h Hx0 Hxh Htpos).
          * (* −inv·h == −t：mult_comm 换形 + t 定义 *)
            apply (real_eq_trans (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                                 (real_opp (real_mult h (real_inv_pos x0 Hx0)))
                                 (real_opp t)).
            -- apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_inv_pos x0 Hx0) h)
                       (real_mult h (real_inv_pos x0 Hx0))).
               apply (real_mult_comm (real_inv_pos x0 Hx0) h).
            -- apply real_eq_refl.
    }
    (* 上界：X ≤ share *)
    assert (HXup : real_le X share).
    {
      apply (real_le_trans X (real_plus (real_plus t share) (real_opp t)) share).
      - (* X ≤ (t+share) − t：le_eps + plus_le_compat *)
        unfold X.
        apply (real_le_plus_compat (real_log (real_plus real_one t) Htpos) (real_plus t share)
                                   (real_opp t) (real_opp t)).
        + exact (real_log_one_plus_le_eps t share Htpos Hshare).
        + apply real_le_refl.
      - (* (t+share) − t ≤ share：eq_le，环 *)
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
    (* 下界：−X ≤ 2t² + (share+share) *)
    assert (HXdown : real_le (real_opp X)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                 (real_plus share share))).
    {
      apply (real_le_trans (real_opp X)
                           (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                           (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
      - (* −X == t − log s：eq_le，opp_plus 换形 *)
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
    (* abs 桥：|X| ≤ 2t² + (share + (share+share)) + share *)
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
    (* 22c：2t² ≤ (eps/2)|h| + share *)
    assert (Hquad : real_le
      (real_mult (real_mult (real_mult h (real_inv_pos x0 Hx0)) (real_mult h (real_inv_pos x0 Hx0)))
                 (real_plus real_one real_one))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)).
    { apply (real_quad_t_le_h_eps x0 h eps share Hx0 Hh_eps4 Heps Hshare). }
    (* 汇总 1：|D| == |X|（HDX + real_abs_eq_compat） *)
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
      - (* |D| == |X| ⟹ |D| ≤ |X|：real_abs_eq_compat + eq_le *)
        apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
          X).
        exact HDX.
      - exact Habs.
    }
    (* 汇总 2：2t² + C ≤ ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C) *)
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
      - (* (2t² + C') + share == 2t² + C（assoc 反向，C := C'+share） *)
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
        + (* 2t² + C ≤ ((eps/2)|h| + share) + C：plus_le_compat（Hquad + refl） *)
          apply (real_le_plus_compat
                   (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                   (real_plus (real_plus share (real_plus share share)) share)
                   (real_plus (real_plus share (real_plus share share)) share)).
          * exact Hquad.
          * apply real_le_refl.
        + (* ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C)：assoc 反向 *)
          apply RealSetoid.real_eq_le.
          apply real_eq_sym.
          apply (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
                                 share
                                 (real_plus (real_plus share (real_plus share share)) share)).
    }
    (* 汇总 3：最终 (eps/2)|h| + 5share ≤ eps|h| + eps'——Bishop 逐点（Or 编码无法表达通用非严格 ≤）。
       逐点差分 = (eps_n/2)|h_n| + (3/8)eps'_n ≥ (3/8)eps'_n > (3/8)e0' > 0（见证 (3/8)·e0'） *)
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
        - (* 0 < 3/8：0·8 < 3·1 *)
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
        (* 展开断言 *)
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
        (* A_n、B_n 投影展开 *)
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
        (* 主链：eps0q < B_n − A_n *)
        apply Qlt_to_QltT.
        apply (Qlt_le_trans _ ((en / 2) * Qabs hn + (Qmake 3 8) * en') _).
        { (* eps0q < (en/2)|hn| + (3/8)en' *)
          apply (Qlt_le_trans _ ((Qmake 3 8) * en') _).
          { (* (3/8)e0' < (3/8)en'：en' > e0'，mult_lt_l *)
            unfold eps0q.
            assert (H38 : Qlt 0 (Qmake 3 8)) by (simpl; reflexivity).
            apply (proj2 (Qmult_lt_l e0' en' (Qmake 3 8) H38)).
            exact Heps0'n. }
          { (* (3/8)en' ≤ (en/2)|hn| + (3/8)en'：0 ≤ (en/2)|hn| *)
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
        { (* (en/2)|hn| + (3/8)en' ≤ B_n − A_n：展开 + field *)
          apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
          (* B_n 展开 *)
          assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
          { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            cbn [projT1]. unfold hn, en, en'. ring. }
          (* 主链：M == B_n − A_n *)
          apply (Qeq_trans ((en / 2) * Qabs hn + (Qmake 3 8) * en')
                           ((en * Qabs hn + en') - ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                           (projT1 (real_plus (real_mult eps (real_abs h)) eps') n - projT1
                             (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                        (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)).
          - (* M == 展开形态：rewrite Hinv2/Hinv8 + field *)
            rewrite Hinv2. rewrite Hinv8.
            unfold Qdiv. field.
          - (* 展开形态 == B_n − A_n：plus_comp（HB + HA 反向） *)
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
    (* 组装 *)
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
(* entropy Real 层：RealDifferentiable 组合引理族（判例后续）  *)
(* + mult 份额（real_differentiable_mult）检验并入    *)
(* 依赖：上面 LogDiffPhase4 的 RealDifferentiable 记录          *)
(* ============================================================ *)

Open Scope Q_scope.

Opaque Qred.

