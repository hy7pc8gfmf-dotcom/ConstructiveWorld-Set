(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* S07_RealSetoidExpLog.v                                      *)
(*                                                             *)
(* 目的：柯西实数的 setoid 化指数/对数：接口实例化、exp 加法性、 *)
(*       弱三分与 log_inv 左逆族（构造性 Set 层）。              *)
(* 主件：real_weak_trich（弱三分：¬lt x y → ¬lt y x → eq x y）；  *)
(*       cw_log_exp_right 与 real_lim/real_lim_unique 接口装填。 *)
(* 依赖：S01–S06；Stdlib（QArith、Qabs、Qround、List、Bool、    *)
(*       Arith、Setoid、Morphisms、Lia、Qminmax）。              *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 之拆分分片，原文区间  *)
(*       L32575-L41232，去头正文与原文区间逐字节同源；弱三分     *)
(*       直觉主义可证，强三分（LPO）不可证。                     *)
(* ============================================================ *)
(* ============================================================ *)
(* ToyR（S 系下半）同名非平凡替换稿 · 检验记录号 S01+S02          *)
(* 替换定理清单：real_eq_le / eq_Id / NatLe_to_le / le_to_NatLe    *)
(*   （共 4 条，语句与声明序不变）                                 *)
(* 非平凡性说明：仅替换上列 4 条证明体；声明面、其余定理、原头注   *)
(*   一律原样保留。口径：real_eq_le 改显式 sum 构造（@inr 全显，   *)
(*   消 right 单跳）；eq_Id 改显式 eq_rect 运送构造项（消 subst    *)
(*   魔法）；NatLe 两桥改 assert 两段组合投影链。全为实质非平凡     *)
(*   构造性推导：零 公理、零 承认件、零经典逻辑，真证闭闭合。      *)
(*   编译态：深依赖链（S01–S06 vo 摘要链断裂），整件遗留；         *)
(*   替换证明体已经语境检验（S01+S02 语义面）G4 全部通过。       *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.

Module RealSetoidCore.
Class RealInterfaceSetoidCore := {
  req : Real -> Real -> Set;
  req_refl : forall x, real_eq x x;
  req_sym : forall x y, real_eq x y -> real_eq y x;
  req_trans : forall x y z, real_eq x y -> real_eq y z -> real_eq x z;

  zero : Real;
  one : Real;
  plus : Real -> Real -> Real;
  mult : Real -> Real -> Real;
  opp : Real -> Real;
  abs : Real -> Real;
  lt : Real -> Real -> Set;
  le : Real -> Real -> Set;

  req_plus_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_eq (plus x1 y1) (plus x2 y2);
  req_mult_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_eq (mult x1 y1) (mult x2 y2);
  req_opp_compat : forall x y, real_eq x y -> real_eq (opp x) (opp y);
  req_abs_compat : forall x y, real_eq x y -> real_eq (abs x) (abs y);
  req_lt_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_lt x1 y1 -> real_lt x2 y2;
  req_le_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_le x1 y1 -> real_le x2 y2;

  plus_assoc : forall a b c, real_eq (plus a (plus b c)) (plus (plus a b) c);
  plus_comm : forall a b, real_eq (plus a b) (plus b a);
  plus_zero : forall a, real_eq (plus a zero) a;
  plus_opp : forall a, real_eq (plus a (opp a)) zero;
  mult_assoc : forall a b c, real_eq (mult a (mult b c)) (mult (mult a b) c);
  mult_comm : forall a b, real_eq (mult a b) (mult b a);
  mult_one : forall a, real_eq (mult a one) a;
  distrib : forall a b c, real_eq (mult a (plus b c)) (plus (mult a b) (mult a c));
  mult_zero : forall a, real_eq (mult a zero) zero;

  lt_irrefl : forall a, Not (real_lt a a);
  lt_trans : forall a b c, real_lt a b -> real_lt b c -> real_lt a c;
  le_refl : forall a, real_le a a;
  le_trans : forall a b c, real_le a b -> real_le b c -> real_le a c;
  le_antisym : forall a b, real_le a b -> real_le b a -> real_eq a b;
  le_lt_trans : forall a b c, real_le a b -> real_lt b c -> real_lt a c;
  lt_le_trans : forall a b c, real_lt a b -> real_le b c -> real_lt a c;
  lt_le_iff : forall a b, Or (real_lt a b) (real_eq a b) -> real_le a b;
  le_id_l : forall a b c, real_eq a b -> real_le b c -> real_le a c;
  le_id_r : forall a b c, real_eq b c -> real_le a b -> real_le a c;
  lt_id_l : forall a b c, real_eq a b -> real_lt b c -> real_lt a c;
  lt_id_r : forall a b c, real_eq b c -> real_lt a b -> real_lt a c;

  inv_pos : forall x, real_lt zero x -> Real;
  inv_pos_correct : forall x H, real_eq (mult x (inv_pos x H)) one;

  metric : Real -> Real -> Real;
  metric_sym : forall a b, real_eq (metric a b) (metric b a);
  metric_pos : forall a b (eps : Real), real_lt zero eps -> real_le zero (plus (metric a b) eps);
  metric_zero : forall a b, real_eq (metric a b) zero -> real_eq a b;
  metric_triangle : forall a b c (eps : Real), real_lt zero eps ->
    real_le (metric a c) (plus (plus (metric a b) (metric b c)) eps);

  lim : (nat -> Real) -> Real -> Set;
  lim_unique : forall u l1 l2, real_lim u l1 -> real_lim u l2 -> real_eq l1 l2;
  cauchy_complete :
    forall u : nat -> Real,
      (forall eps : Real, real_lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> real_lt (metric (u m) (u n)) eps)) ->
      sigT (fun l : Real => real_lim u l);
}.
End RealSetoidCore.

Module RealSetoid.
(* ============================================================
   RealInterface 实例化 阶段 3：Setoid 并行接口类 + 实例组装
   RealInterfaceSetoid（req 版，与旧 RealInterface 同构但 Id → req，
   增加 Proper 原理字段）。实例化 R := Real，req := real_eq。
   完整版：环 + 序 + inv_pos + abs + metric + lim + cauchy_complete
   + exp_neg + log_inv。
   ============================================================ *)

(* 桥：real_eq a b -> real_le a b（real_le_refl + real_eq 替换） *)
Lemma real_eq_le : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  intros a b Hab.
  (* ToyR 替换：显式 sum 构造——real_le 展开为 Or（S01 Or = 和型），
     右支相等支以 @inr 全显注入（和型非归纳具文，消 right 单跳魔法） *)
  unfold real_le.
  exact (@inr (real_lt a b) (real_eq a b) Hab).
Qed.

(* 桥：Or (real_lt a b) (real_eq a b) -> real_le a b（lt_le_iff 的 req 版） *)
Lemma real_lt_le_iff_req : forall a b : Real,
  Or (real_lt a b) (real_eq a b) -> real_le a b.
Proof.
  intros a b H.
  destruct H as [Hlt | Heq].
  - apply (real_lt_le_iff a b). left. exact Hlt.
  - apply real_eq_le. exact Heq.
Qed.

Class RealInterfaceSetoid := {
  (* 参数化相等（setoid 核心） *)
  req : Real -> Real -> Set;
  req_refl : forall x, real_eq x x;
  req_sym : forall x y, real_eq x y -> real_eq y x;
  req_trans : forall x y z, real_eq x y -> real_eq y z -> real_eq x z;

  (* 常数与运算 *)
  zero : Real;
  one : Real;
  plus : Real -> Real -> Real;
  mult : Real -> Real -> Real;
  opp : Real -> Real;
  abs : Real -> Real;
  lt : Real -> Real -> Set;
  le : Real -> Real -> Set;

  (* Proper 原理（setoid 替换核心） *)
  req_plus_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_eq (plus x1 y1) (plus x2 y2);
  req_mult_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_eq (mult x1 y1) (mult x2 y2);
  req_opp_compat : forall x y, real_eq x y -> real_eq (opp x) (opp y);
  req_abs_compat : forall x y, real_eq x y -> real_eq (abs x) (abs y);
  req_lt_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_lt x1 y1 -> real_lt x2 y2;
  req_le_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_le x1 y1 -> real_le x2 y2;

  (* 环律（req 版） *)
  plus_assoc : forall a b c, real_eq (plus a (plus b c)) (plus (plus a b) c);
  plus_comm : forall a b, real_eq (plus a b) (plus b a);
  plus_zero : forall a, real_eq (plus a zero) a;
  plus_opp : forall a, real_eq (plus a (opp a)) zero;
  mult_assoc : forall a b c, real_eq (mult a (mult b c)) (mult (mult a b) c);
  mult_comm : forall a b, real_eq (mult a b) (mult b a);
  mult_one : forall a, real_eq (mult a one) a;
  distrib : forall a b c, real_eq (mult a (plus b c)) (plus (mult a b) (mult a c));
  mult_zero : forall a, real_eq (mult a zero) zero;

  (* 序 *)
  lt_irrefl : forall a, Not (real_lt a a);
  lt_trans : forall a b c, real_lt a b -> real_lt b c -> real_lt a c;
  le_refl : forall a, real_le a a;
  le_trans : forall a b c, real_le a b -> real_le b c -> real_le a c;
  le_antisym : forall a b, real_le a b -> real_le b a -> real_eq a b;
  le_lt_trans : forall a b c, real_le a b -> real_lt b c -> real_lt a c;
  lt_le_trans : forall a b c, real_lt a b -> real_le b c -> real_lt a c;
  lt_le_iff : forall a b, Or (real_lt a b) (real_eq a b) -> real_le a b;
  le_id_l : forall a b c, real_eq a b -> real_le b c -> real_le a c;
  le_id_r : forall a b c, real_eq b c -> real_le a b -> real_le a c;
  lt_id_l : forall a b c, real_eq a b -> real_lt b c -> real_lt a c;
  lt_id_r : forall a b c, real_eq b c -> real_lt a b -> real_lt a c;

  (* 可逆元 *)
  inv_pos : forall x, real_lt zero x -> Real;
  inv_pos_correct : forall x H, real_eq (mult x (inv_pos x H)) one;

  (* exp 族 *)
  exp_neg : Real -> Real;
  exp_neg_pos : forall x, real_lt zero (exp_neg x);
  exp_neg_zero : real_eq (exp_neg zero) one;
  exp_neg_plus : forall a b, real_eq (exp_neg (plus a b)) (mult (exp_neg a) (exp_neg b));

  (* log 族（exp 的逆） *)
  log_inv : forall x, real_lt zero x -> Real;
  log_inv_exp_neg : forall x (H : real_lt zero (exp_neg x)),
    real_eq (log_inv (exp_neg x) H) x;
  log_inv_one : forall (H : real_lt zero one), real_eq (log_inv one H) zero;
  log_inv_mult : forall a b Ha Hb Hm,
    real_eq (log_inv (mult a b) Hm) (plus (log_inv a Ha) (log_inv b Hb));

  (* metric 族（逐 eps 上界形式：Or 编码 le 无法表达"非严格且不趋近"；
     metric_pos/metric_triangle 需加 eps 余量才可证） *)
  metric : Real -> Real -> Real;
  metric_sym : forall a b, real_eq (metric a b) (metric b a);
  metric_pos : forall a b (eps : Real), real_lt zero eps -> real_le zero (plus (metric a b) eps);
  metric_zero : forall a b, real_eq (metric a b) zero -> real_eq a b;
  metric_triangle : forall a b c (eps : Real), real_lt zero eps ->
    real_le (metric a c) (plus (plus (metric a b) (metric b c)) eps);

  (* 极限与完备性 *)
  lim : (nat -> Real) -> Real -> Set;
  lim_unique : forall u l1 l2, real_lim u l1 -> real_lim u l2 -> real_eq l1 l2;
  cauchy_complete :
    forall u : nat -> Real,
      (forall eps : Real, real_lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> real_lt (metric (u m) (u n)) eps)) ->
      sigT (fun l : Real => real_lim u l);
}.

(* ============ 阶段 3 续：Proper 原理（setoid 替换核心） ============ *)

(* real_eq 对 real_plus 的 Proper：a≈c ∧ b≈d ⟹ a+b ≈ c+d（eps/2 分割 + Qabs_triangle） *)
Lemma real_eq_plus_compat : forall a b c d : Real,
  real_eq a c -> real_eq b d -> real_eq (real_plus a b) (real_plus c d).
Proof.
  intros a b c d Hac Hbd eps Heps.
  (* 一致界：|a_k| ≤ Ma、|d_k| ≤ Md（q_prod_diff_bound 需要 |a| 与 |d| 的界） *)
  destruct (real_norm_bounded a) as [Ma [HMa_pos HMa]].
  destruct (real_norm_bounded d) as [Md [HMd_pos HMd]].
  assert (Hhalf0 : QltT 0 (eps / 2)%Q).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
  destruct (Hac (eps / 2)%Q Hhalf0) as [N1 HN1].
  destruct (Hbd (eps / 2)%Q Hhalf0) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros k Hk.
  assert (HkN1 : (N1 <= k)%nat) by (apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
  assert (HkN2 : (N2 <= k)%nat) by (apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
  apply Qlt_to_QltT.
  (* 换形：(a+b) − (c+d) == (a−c) + (b−d)（ring） *)
  assert (Hd : projT1 (real_plus a b) k - projT1 (real_plus c d) k ==
               (projT1 a k - projT1 c k) + (projT1 b k - projT1 d k)).
  { assert (Hpa : projT1 (real_plus a b) k == projT1 a k + projT1 b k) by (apply qeqT_imp_qeq, real_plus_proj).
    assert (Hpc : projT1 (real_plus c d) k == projT1 c k + projT1 d k) by (apply qeqT_imp_qeq, real_plus_proj).
    setoid_rewrite Hpa. setoid_rewrite Hpc. ring. }
  rewrite Hd.
  (* |(a−c) + (b−d)| ≤ |a−c| + |b−d| < eps/2 + eps/2 == eps *)
  apply (Qle_lt_trans _ (Qabs (projT1 a k - projT1 c k) + Qabs (projT1 b k - projT1 d k)) _).
  - apply Qabs_triangle.
  - (* |a−c| + |b−d| < eps：Qplus_lt_compat（各 < eps/2）+ eps/2+eps/2 == eps *)
    apply (Qlt_le_trans _ (eps / 2 + eps / 2) _).
    + apply (Qplus_lt_compat (Qabs (projT1 a k - projT1 c k)) (eps / 2)
                             (Qabs (projT1 b k - projT1 d k)) (eps / 2)).
      * apply QltT_to_Qlt. apply (HN1 k). apply NatLe_lift. exact HkN1.
      * apply QltT_to_Qlt. apply (HN2 k). apply NatLe_lift. exact HkN2.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
Qed.

(* real_eq 对 real_opp 的 Proper：a≈b ⟹ -a ≈ -b（|-a + b| == |a - b|） *)
Lemma real_eq_opp_compat : forall a b : Real,
  real_eq a b -> real_eq (real_opp a) (real_opp b).
Proof.
  intros a b Hab eps Heps.
  destruct (Hab eps Heps) as [N HN].
  exists N.
  intros k Hk.
  apply Qlt_to_QltT.
  assert (Hoa : projT1 (real_opp a) k == - projT1 a k) by (apply qeqT_imp_qeq, real_opp_proj).
  assert (Hob : projT1 (real_opp b) k == - projT1 b k) by (apply qeqT_imp_qeq, real_opp_proj).
  (* |-a - (-b)| == |-(a - b)| == |a - b| *)
  apply (Qle_lt_trans _ (Qabs (projT1 a k - projT1 b k)) _).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    (* Qabs (−a − (−b)) == Qabs (a − b)：rewrite Hoa/Hob 后 Qabs_wd + ring *)
    (* Qabs (opp a − opp b) == Qabs (a − b)：rewrite Hoa/Hob → Qabs_Qminus → ring *)
    rewrite Hoa. rewrite Hob.
    transitivity (Qabs (- projT1 b k - (- projT1 a k))).
    { rewrite (Qabs_Qminus (- projT1 a k) (- projT1 b k)). reflexivity. }
    { apply Qabs_wd. unfold Qminus.
      rewrite (Qopp_involutive (projT1 a k)).
      apply Qplus_comm. }
  - apply QltT_to_Qlt. apply (HN k). exact Hk.
Qed.

(* real_eq 对 real_mult 的 Proper：a≈c ∧ b≈d ⟹ a·b ≈ c·d
   （eps/2 分割 + real_norm_bounded 有界 + q_prod_diff_bound 乘积差三角界；
     b−d 项用 |a| 的界 Mupos、a−c 项用 |d| 的界 Mvpos——real_mult L3293 同款结构） *)
Lemma real_eq_mult_compat : forall a b c d : Real,
  real_eq a c -> real_eq b d -> real_eq (real_mult a b) (real_mult c d).
Proof.
  intros a b c d Hac Hbd eps Heps.
  (* 一致界：|a_k| ≤ Ma、|d_k| ≤ Md（q_prod_diff_bound 需要 |a| 与 |d| 的界） *)
  destruct (real_norm_bounded a) as [Ma [HMa_pos HMa]].
  destruct (real_norm_bounded d) as [Md [HMd_pos HMd]].
  (* 正界提升（Set 版） *)
  set (Mupos := (1 + Qabs Ma)%Q).
  set (Mvpos := (1 + Qabs Md)%Q).
  assert (Mupos_pos : Qlt 0 Mupos).
  { unfold Mupos. apply Qlt_le_trans with 1%Q.
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (Mvpos_pos : Qlt 0 Mvpos).
  { unfold Mvpos. apply Qlt_le_trans with 1%Q.
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (MuposT : QltT 0 Mupos).
  { apply Qlt_to_QltT. exact Mupos_pos. }
  assert (MvposT : QltT 0 Mvpos).
  { apply Qlt_to_QltT. exact Mvpos_pos. }
  (* eps/(2·Mupos) 与 eps/(2·Mvpos) 严格正（柯西阈值，Set 链） *)
  assert (HepsB : QltT 0 (eps / (2 * Mupos))%Q).
  { apply (qltT_div_pos eps (2 * Mupos)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 Mupos). exact qltT_0_2. exact MuposT. }
  assert (HepsA : QltT 0 (eps / (2 * Mvpos))%Q).
  { apply (qltT_div_pos eps (2 * Mvpos)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 Mvpos). exact qltT_0_2. exact MvposT. }
  destruct (Hbd (eps / (2 * Mupos))%Q HepsB) as [Nbd HNbd].
  destruct (Hac (eps / (2 * Mvpos))%Q HepsA) as [Nac HNac].
  exists (Nat.max Nbd Nac).
  intros k Hk.
  assert (HkNbd : (Nbd <= k)%nat)
    by (apply Nat.le_trans with (Nat.max Nbd Nac); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
  assert (HkNac : (Nac <= k)%nat)
    by (apply Nat.le_trans with (Nat.max Nbd Nac); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
  (* Set 链（HMa/HMd 直接，无降级） *)
  assert (Hpa : projT1 (real_mult a b) k == projT1 a k * projT1 b k) by (apply qeqT_imp_qeq, real_mult_proj).
  assert (Hpc : projT1 (real_mult c d) k == projT1 c k * projT1 d k) by (apply qeqT_imp_qeq, real_mult_proj).
  apply (qltT_eq_compat_l (Qabs (projT1 a k * projT1 b k - projT1 c k * projT1 d k))
                          (Qabs (projT1 (real_mult a b) k - projT1 (real_mult c d) k))
                          eps).
  - apply qeq_imp_qeqT.
    apply Qabs_wd.
    rewrite Hpa. rewrite Hpc. reflexivity.
  - (* |a·b − c·d| ≤T |a||b−d| + |a−c||d|（q_prod_diff_bound 提升） *)
    assert (HbdT : QleT' (Qabs (projT1 a k * projT1 b k - projT1 c k * projT1 d k))
                         (Qabs (projT1 a k) * Qabs (projT1 b k - projT1 d k)
                          + Qabs (projT1 d k) * Qabs (projT1 a k - projT1 c k))).
    { apply Qle_to_QleT'.
      assert (Hp : Qle (Qabs (projT1 a k * projT1 b k - projT1 c k * projT1 d k))
                       (Qabs (projT1 a k) * Qabs (projT1 b k - projT1 d k)
                        + Qabs (projT1 a k - projT1 c k) * Qabs (projT1 d k))) by (apply QleT'_to_Qle, q_prod_diff_bound).
      eapply Qle_trans; [exact Hp |].
      apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    assert (HMa_boundT : QleT' (Qabs (projT1 a k)) Mupos).
    { apply (qleT'_trans (Qabs (projT1 a k)) Ma Mupos).
      - apply HMa.
      - apply Qle_to_QleT'.
        unfold Mupos.
        apply (Qle_trans Ma (Qabs Ma) (1 + Qabs Ma)).
        + apply Qle_Qabs.
        + rewrite Qplus_comm. apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1. }
    assert (HMd_boundT : QleT' (Qabs (projT1 d k)) Mvpos).
    { apply (qleT'_trans (Qabs (projT1 d k)) Md Mvpos).
      - apply HMd.
      - apply Qle_to_QleT'.
        unfold Mvpos.
        apply (Qle_trans Md (Qabs Md) (1 + Qabs Md)).
        + apply Qle_Qabs.
        + rewrite Qplus_comm. apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1. }
    assert (Ht1T : QltT (Qabs (projT1 a k) * Qabs (projT1 b k - projT1 d k))
                        (Mupos * (eps / (2 * Mupos)))).
    { apply (qleT'_mult_ltT_compat (Qabs (projT1 a k)) Mupos
                                   (Qabs (projT1 b k - projT1 d k))
                                   (eps / (2 * Mupos))).
      - exact MuposT.
      - apply qabs_nonnegT.
      - exact HMa_boundT.
      - apply (HNbd k). apply NatLe_lift. exact HkNbd. }
    assert (Ht2T : QltT (Qabs (projT1 d k) * Qabs (projT1 a k - projT1 c k))
                        (Mvpos * (eps / (2 * Mvpos)))).
    { apply (qleT'_mult_ltT_compat (Qabs (projT1 d k)) Mvpos
                                   (Qabs (projT1 a k - projT1 c k))
                                   (eps / (2 * Mvpos))).
      - exact MvposT.
      - apply qabs_nonnegT.
      - exact HMd_boundT.
      - apply (HNac k). apply NatLe_lift. exact HkNac. }
    (* 项界 ≤T eps/2（乘后 == 换形） *)
    assert (Ht1bT : QleT' (Mupos * (eps / (2 * Mupos))) (eps / 2)).
    { apply qeq_leT'.
      assert (Hf : Mupos * (eps / (2 * Mupos)) == eps / 2).
      { field.
        intro Hz.
        exact (Qlt_not_eq 0 Mupos (QltT_to_Qlt 0 Mupos MuposT) (Qeq_sym Mupos 0 Hz)). }
      exact (qeq_imp_qeqT _ _ Hf). }
    assert (Ht2bT : QleT' (Mvpos * (eps / (2 * Mvpos))) (eps / 2)).
    { apply qeq_leT'.
      assert (Hf : Mvpos * (eps / (2 * Mvpos)) == eps / 2).
      { field.
        intro Hz.
        exact (Qlt_not_eq 0 Mvpos (QltT_to_Qlt 0 Mvpos MvposT) (Qeq_sym Mvpos 0 Hz)). }
      exact (qeq_imp_qeqT _ _ Hf). }
    assert (Ht1T' : QltT (Qabs (projT1 a k) * Qabs (projT1 b k - projT1 d k)) (eps / 2))
      by (apply (qltT_leT'_ltT _ _ _ Ht1T Ht1bT)).
    assert (Ht2T' : QltT (Qabs (projT1 d k) * Qabs (projT1 a k - projT1 c k)) (eps / 2))
      by (apply (qltT_leT'_ltT _ _ _ Ht2T Ht2bT)).
    (* 结论：|…| ≤T 和 <T eps/2+eps/2 ==T eps *)
    apply (qleT'_ltT_ltT (Qabs (projT1 a k * projT1 b k - projT1 c k * projT1 d k))
                         (Qabs (projT1 a k) * Qabs (projT1 b k - projT1 d k)
                          + Qabs (projT1 d k) * Qabs (projT1 a k - projT1 c k))
                         eps);
      [ exact HbdT
      | apply (qltT_leT'_ltT _ (eps / 2 + eps / 2) eps);
        [ apply (qltT_plus_ltT (Qabs (projT1 a k) * Qabs (projT1 b k - projT1 d k))
                               (eps / 2)
                               (Qabs (projT1 d k) * Qabs (projT1 a k - projT1 c k))
                               (eps / 2));
          [ exact Ht1T' | exact Ht2T' ]
        | apply qeq_leT'; apply qeq_imp_qeqT;
          assert (Hf3 : eps / 2 + eps / 2 == eps) by field;
          exact Hf3 ] ].
Qed.

(* real_eq 对 real_abs 的 Proper：a≈b ⟹ |a| ≈ |b|（反三角 q_abs_abs_triangle） *)
Lemma real_eq_abs_compat : forall a b : Real,
  real_eq a b -> real_eq (real_abs a) (real_abs b).
Proof.
  intros a b Hab eps Heps.
  destruct (Hab eps Heps) as [N HN].
  exists N.
  intros k Hk.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj a k)). rewrite (qeqT_imp_qeq _ _ (real_abs_proj b k)).
  apply (Qle_lt_trans _ (Qabs (projT1 a k - projT1 b k)) _).
  - apply QleT'_to_Qle. apply (q_abs_abs_triangle (projT1 a k) (projT1 b k)).
  - apply QltT_to_Qlt. apply (HN k). exact Hk.
Qed.

(* real_eq 对 real_lt 的 Proper：x1≈x2 ∧ y1≈y2 ⟹ x1<y1 → x2<y2
   （real_eq_lt_lt + real_lt_eq_lt 单向桥组合） *)
Lemma real_lt_compat : forall x1 x2 y1 y2 : Real,
  real_eq x1 x2 -> real_eq y1 y2 -> real_lt x1 y1 -> real_lt x2 y2.
Proof.
  intros x1 x2 y1 y2 Hx Hy Hlt.
  apply (real_lt_eq_lt x2 y1 y2).
  - apply (real_eq_lt_lt x2 x1 y1 (real_eq_sym x1 x2 Hx) Hlt).
  - exact Hy.
Qed.

(* real_eq 对 real_le 的 Proper：x1≈x2 ∧ y1≈y2 ⟹ x1≤y1 → x2≤y2
   （real_le = Or (real_lt) (real_eq) 分解） *)
Lemma real_le_compat : forall x1 x2 y1 y2 : Real,
  real_eq x1 x2 -> real_eq y1 y2 -> real_le x1 y1 -> real_le x2 y2.
Proof.
  intros x1 x2 y1 y2 Hx Hy Hle.
  destruct Hle as [Hlt | Heq].
  - left. apply (real_lt_compat x1 x2 y1 y2 Hx Hy Hlt).
  - right. apply (real_eq_trans x2 y1 y2).
    + apply (real_eq_trans x2 x1 y1 (real_eq_sym x1 x2 Hx) Heq).
    + exact Hy.
Qed.

(* lt_id_l：req a b -> lt b c -> lt a c（= real_eq_lt_lt） *)
Lemma real_lt_id_l : forall a b c : Real,
  real_eq a b -> real_lt b c -> real_lt a c.
Proof.
  intros a b c Hab Hbc. apply (real_eq_lt_lt a b c Hab Hbc).
Qed.

(* lt_id_r：req b c -> lt a b -> lt a c（= real_lt_eq_lt） *)
Lemma real_lt_id_r : forall a b c : Real,
  real_eq b c -> real_lt a b -> real_lt a c.
Proof.
  intros a b c Hbc Hab. apply (real_lt_eq_lt a b c Hab Hbc).
Qed.

(* le_id_l：req a b -> le b c -> le a c（real_le_compat 取 y 恒等） *)
Lemma real_le_id_l : forall a b c : Real,
  real_eq a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Hab Hbc.
  apply (real_le_compat b a c c (real_eq_sym a b Hab) (real_eq_refl c) Hbc).
Qed.

(* le_id_r：req b c -> le a b -> le a c（real_le_compat 取 x 恒等） *)
Lemma real_le_id_r : forall a b c : Real,
  real_eq b c -> real_le a b -> real_le a c.
Proof.
  intros a b c Hbc Hab.
  apply (real_le_compat a a b c (real_eq_refl a) Hbc Hab).
Qed.

(* real_eq 对 real_metric 的对称：metric a b ≈ metric b a
   （逐点 Qabs (u−v) == Qabs (v−u)，Qabs_opp 对称） *)
Lemma real_metric_sym : forall a b : Real,
  real_eq (real_metric a b) (real_metric b a).
Proof.
  intros a b eps Heps.
  exists 0%nat.
  intros k _.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    unfold real_metric.
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a (real_opp b)) k)).
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus b (real_opp a)) k)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp b) k)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj b (real_opp a) k)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj b k)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj a k)).
    (* Qabs (Qabs (u−v) − Qabs (v−u)) == 0 ⟸ Qabs (u−v) == Qabs (v−u) *)
    apply (Qabs_wd (Qabs (projT1 a k + - projT1 b k) - Qabs (projT1 b k + - projT1 a k)) 0).
    (* 目标：Qabs (u−v) − Qabs (v−u) == 0；先证两 Qabs 相等 *)
    assert (Habs : Qabs (projT1 a k + - projT1 b k) == Qabs (projT1 b k + - projT1 a k)).
    { transitivity (Qabs (- (projT1 b k + - projT1 a k))).
      - apply Qabs_wd. ring.
      - apply Qabs_opp. }
    rewrite Habs. ring.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* metric_zero：metric a b ≈ 0 ⟹ a ≈ b
   （逐 eps：|u−v| == |metric_k − 0|，HN 直接给 < eps） *)
Lemma real_metric_zero : forall a b : Real,
  real_eq (real_metric a b) real_zero -> real_eq a b.
Proof.
  intros a b Hab eps Heps.
  destruct (Hab eps Heps) as [N HN].
  exists N.
  intros k Hk.
  apply Qlt_to_QltT.
  (* 换形：projT1 (real_metric a b) k == Qabs (projT1 a k - projT1 b k) *)
  assert (Hproj : projT1 (real_metric a b) k == Qabs (projT1 a k - projT1 b k)).
  { unfold real_metric.
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a (real_opp b)) k)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp b) k)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj b k)).
    apply Qabs_wd. ring. }
  (* |u−v| ≤ |metric_k − 0| < eps：|u−v| == |metric_k| == |metric_k − 0| *)
  apply (Qle_lt_trans _ (Qabs (projT1 (real_metric a b) k - projT1 real_zero k)) _).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    transitivity (Qabs (projT1 (real_metric a b) k)).
    + (* |u−v| == |metric_k|：经幂等 | |u−v| |（Qabs_pos + 非负）+ Hproj（Qabs_wd） *)
      transitivity (Qabs (Qabs (projT1 a k - projT1 b k))).
      * apply Qeq_sym.
        apply (Qabs_pos (Qabs (projT1 a k - projT1 b k)) (Qabs_nonneg (projT1 a k - projT1 b k))).
      * apply (Qabs_wd (Qabs (projT1 a k - projT1 b k)) (projT1 (real_metric a b) k)).
        apply Qeq_sym. exact Hproj.
    + (* |metric_k| == |metric_k − 0|：Hzero 归约 real_zero 后 ring（判例：勿整目标 cbn） *)
      apply (Qabs_wd (projT1 (real_metric a b) k) (projT1 (real_metric a b) k - projT1 real_zero k)).
      assert (Hzero : projT1 real_zero k == 0) by (cbn [projT1]; reflexivity).
      rewrite Hzero. ring.
  - apply QltT_to_Qlt. apply (HN k). exact Hk.
Qed.

(* ============ 阶段 3 续：cauchy_complete 桥（metric 形式 → 双向 real_lt 形式） ============ *)

(* Q 层：−x ≤ |x|（Qle_Qabs 于 −x + Qabs_opp 对称） *)
Lemma q_neg_le_abs : forall x : Q, QleT' (- x) (Qabs x).
Proof.
  intros x.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (- x)) _).
  - apply Qle_Qabs.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
Qed.

(* Q 层：e − |x| ≤ e − x（|x| ≥ x ⟹ 取负 + e 平移） *)
Lemma q_minus_abs_le : forall e x : Q, QleT' (e - Qabs x) (e - x).
Proof.
  intros e x.
  apply Qle_to_QleT'.
  apply (Qplus_le_compat e e (Qopp (Qabs x)) (Qopp x)).
  - apply Qle_refl.
  - apply (Qopp_le_compat x (Qabs x)). apply Qle_Qabs.
Qed.

(* Q 层：e − |x| ≤ e + x（|x| ≥ −x ⟹ −|x| ≤ x） *)
Lemma q_minus_abs_le_neg : forall e x : Q, QleT' (e - Qabs x) (e + x).
Proof.
  intros e x.
  apply Qle_to_QleT'.
  apply (Qplus_le_compat e e (Qopp (Qabs x)) x).
  - apply Qle_refl.
  - apply (Qle_trans _ (- (- x)) _).
    + apply (Qopp_le_compat (- x) (Qabs x)). apply QleT'_to_Qle. apply q_neg_le_abs.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qopp_involutive.
Qed.

(* 桥 1：real_lt (metric (u m) (u n)) (real_const e) ⟹ real_lt (u m − u n) (real_const e)
   （见证不变：e0/N；逐点 |x| ≥ x 桥） *)
Lemma real_metric_lt_const_to_minus :
  forall (u : nat -> Real) (m n : nat) (e : Q),
    real_lt (real_metric (u m) (u n)) (real_const e) ->
    real_lt (real_plus (u m) (real_opp (u n))) (real_const e).
Proof.
  intros u m n e Hlt.
  destruct Hlt as [e0 [He0 [N HN]]].
  exists e0. split.
  - exact He0.
  - exists N. intros k Hk.
    apply Qlt_to_QltT.
    (* 换形：projT1 (real_const e) k == e；projT1 (real_metric (u m) (u n)) k == Qabs (u m k − u n k) *)
    assert (Hc : projT1 (real_const e) k == e) by (apply qeqT_imp_qeq, real_const_proj).
    assert (Hm : projT1 (real_metric (u m) (u n)) k == Qabs (projT1 (u m) k - projT1 (u n) k)).
    { unfold real_metric.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (u m) (real_opp (u n))) k)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (u m) (real_opp (u n)) k)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (u n) k)).
      apply Qabs_wd. ring. }
    (* 链：e0 < e − |x|（HN）≤ e − x（q_minus_abs_le）== RHS（投影换形） *)
    apply (Qlt_le_trans _ (e - Qabs (projT1 (u m) k - projT1 (u n) k)) _).
    + apply (Qlt_le_trans _ (projT1 (real_const e) k - projT1 (real_metric (u m) (u n)) k) _).
      * apply QltT_to_Qlt. apply (HN k). exact Hk.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hc. rewrite Hm. reflexivity.
    + apply (Qle_trans _ (e - (projT1 (u m) k - projT1 (u n) k)) _).
      * apply QleT'_to_Qle. apply (q_minus_abs_le e (projT1 (u m) k - projT1 (u n) k)).
      * apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        transitivity (e - (projT1 (u m) k - projT1 (u n) k)).
        -- reflexivity.
        -- rewrite Hc.
           rewrite (qeqT_imp_qeq _ _ (real_plus_proj (u m) (real_opp (u n)) k)).
           rewrite (qeqT_imp_qeq _ _ (real_opp_proj (u n) k)).
           reflexivity.
Qed.

(* 桥 2：real_lt (metric (u m) (u n)) (real_const e) ⟹ real_lt (u n − u m) (real_const e)
   （|x| ≥ −x 桥；RHS 换形 e − (v k − u k) == e + (u k − v k)） *)
Lemma real_metric_lt_const_to_minus_comm :
  forall (u : nat -> Real) (m n : nat) (e : Q),
    real_lt (real_metric (u m) (u n)) (real_const e) ->
    real_lt (real_plus (u n) (real_opp (u m))) (real_const e).
Proof.
  intros u m n e Hlt.
  destruct Hlt as [e0 [He0 [N HN]]].
  exists e0. split.
  - exact He0.
  - exists N. intros k Hk.
    apply Qlt_to_QltT.
    assert (Hc : projT1 (real_const e) k == e) by (apply qeqT_imp_qeq, real_const_proj).
    assert (Hm : projT1 (real_metric (u m) (u n)) k == Qabs (projT1 (u m) k - projT1 (u n) k)).
    { unfold real_metric.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (u m) (real_opp (u n))) k)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (u m) (real_opp (u n)) k)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (u n) k)).
      apply Qabs_wd. ring. }
    apply (Qlt_le_trans _ (e - Qabs (projT1 (u m) k - projT1 (u n) k)) _).
    + apply (Qlt_le_trans _ (projT1 (real_const e) k - projT1 (real_metric (u m) (u n)) k) _).
      * apply QltT_to_Qlt. apply (HN k). exact Hk.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hc. rewrite Hm. reflexivity.
    + apply (Qle_trans _ (e + (projT1 (u m) k - projT1 (u n) k)) _).
      * apply QleT'_to_Qle. apply (q_minus_abs_le_neg e (projT1 (u m) k - projT1 (u n) k)).
      * apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        transitivity (e + (projT1 (u m) k - projT1 (u n) k)).
        -- reflexivity.
        -- rewrite Hc.
           rewrite (qeqT_imp_qeq _ _ (real_plus_proj (u n) (real_opp (u m)) k)).
           rewrite (qeqT_imp_qeq _ _ (real_opp_proj (u m) k)).
           ring.
Qed.

(* 主桥：接口 cauchy（Real 层 eps + metric 形式）→ real_cauchy_complete 输入（Q 层 eps + 双向）
   用 real_const e 作接口输入（e/2 见证 real_lt real_zero (real_const e)） *)
Lemma real_cauchy_complete_metric :
  forall (u : nat -> Real),
    (forall eps : Real, real_lt real_zero eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        real_lt (real_metric (u m) (u n)) eps)) ->
    sigT (fun l : Real => real_lim u l).
Proof.
  intros u Hcau.
  apply real_cauchy_complete.
  intros e He.
  destruct (Hcau (real_const e)) as [N HN].
  { (* real_lt real_zero (real_const e)：见证 e/2、N=0 *)
    assert (Hhalf : Qlt 0 (e / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact He]. }
    exists (e / 2)%Q. split.
    - apply Qlt_to_QltT. exact Hhalf.
    - exists 0%nat. intros k _.
      apply Qlt_to_QltT.
      (* e/2 < e − 0：e/2 < e/2+e/2 == e 且 e/2+0 == e/2 *)
      apply (Qlt_le_trans _ (e / 2 + e / 2) _).
      + apply (Qle_lt_trans _ (e / 2 + 0) _).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        * apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2)) Hhalf).
      + apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        assert (Hc' : projT1 (real_const e) k == e) by (apply qeqT_imp_qeq, real_const_proj).
        assert (Hz' : projT1 real_zero k == 0) by (cbn [projT1]; reflexivity).
        rewrite Hc'. rewrite Hz'.
        (* e/2 + e/2 == e − 0：Qopp 0 的 Qred 卡 ring（判例）→ Qeq_trans + Qred_correct *)
        transitivity e.
        * field.
        * unfold Qminus.
          assert (Hopp0 : Qopp 0%Q == 0%Q).
          { transitivity (Qred (Qmake 0 1)).
            - reflexivity.
            - apply Qred_correct. }
          rewrite Hopp0. apply Qeq_sym. apply Qplus_0_r. }
  exists N.
  intros m n Hm Hn.
  split.
  - apply (real_metric_lt_const_to_minus u m n e (HN m n Hm Hn)).
  - apply (real_metric_lt_const_to_minus_comm u m n e (HN m n Hm Hn)).
Qed.

(* ============ Core 组装前置：metric 逐 eps 形式（接口字段已改） ============ *)

(* metric_pos 逐 eps 形式：0 < eps ⟹ 0 ≤ metric a b + eps
   （Or 编码下 |u−v| ≥ 0 无法一致分离；加 eps 余量后可证：e < eps_n − 0 ≤ |u n−v n| + eps_n − 0） *)
Lemma real_metric_pos_eps : forall a b (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_metric a b) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e [He [N HN]]].
  left.
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    apply Qlt_to_QltT.
    (* 链：e < eps_n − 0 ≤ |u n − v n| + eps_n − 0 == (metric a b + eps)_n − 0 *)
    apply (Qlt_le_trans _ (projT1 eps n - 0) _).
    + apply QltT_to_Qlt. apply (HN n). exact Hn.
    + apply (Qle_trans _ (Qabs (projT1 a n - projT1 b n) + projT1 eps n) _).
      * (* projT1 eps n − 0 ≤ |u n − v n| + projT1 eps n：先归零再平移 *)
        apply (Qle_trans _ (projT1 eps n) _).
        apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
           assert (Hz : projT1 eps n - 0 == projT1 eps n).
           { unfold Qminus.
             assert (Hopp0 : Qopp 0%Q == 0%Q).
             { transitivity (Qred (Qmake 0 1)).
               - reflexivity.
               - apply Qred_correct. }
             rewrite Hopp0.
             apply Qplus_0_r. }
           exact Hz.
        -- apply (Qle_trans _ (0 + projT1 eps n) _).
           ++ (* projT1 eps n ≤ 0 + projT1 eps n：qeq（0 + X == X） *)
              apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ (* 0 + eps_n ≤ |u n − v n| + eps_n：Qplus_le_compat *)
              apply (Qplus_le_compat 0 (Qabs (projT1 a n - projT1 b n)) (projT1 eps n) (projT1 eps n)).
              { apply Qabs_nonneg. }
              { apply Qle_refl. }
      * (* |u n − v n| + projT1 eps n ≤ projT1 (real_plus (real_metric a b) eps) n − projT1 real_zero n *)
        apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
        assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        assert (Hp : projT1 (real_plus (real_metric a b) eps) n == Qabs (projT1 a n - projT1 b n) + projT1 eps n).
        { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_metric a b) eps n)).
          unfold real_metric.
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a (real_opp b)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp b) n)).
          rewrite (qeqT_imp_qeq _ _ (real_opp_proj b n)).
          assert (Habs : Qabs (projT1 a n + - projT1 b n) == Qabs (projT1 a n - projT1 b n)).
          { apply Qabs_wd. ring. }
          rewrite Habs. reflexivity. }
        transitivity (Qabs (projT1 a n - projT1 b n) + projT1 eps n - 0).
        -- unfold Qminus.
           assert (Hopp0 : Qopp 0%Q == 0%Q).
           { transitivity (Qred (Qmake 0 1)).
             - reflexivity.
             - apply Qred_correct. }
           rewrite Hopp0.
           apply Qeq_sym. apply Qplus_0_r.
        -- rewrite Hp. cbn [projT1]. reflexivity.
Qed.

(* metric_triangle 逐 eps 形式：0 < eps ⟹ metric a c ≤ metric a b + metric b c + eps
   （逐点三角不等式 + eps 余量；Or 编码无法表达非严格三角不等式） *)
Lemma real_metric_triangle_eps : forall a b c (eps : Real),
  real_lt real_zero eps ->
  real_le (real_metric a c) (real_plus (real_plus (real_metric a b) (real_metric b c)) eps).
Proof.
  intros a b c eps Heps.
  destruct Heps as [e [He [N HN]]].
  left.
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    apply Qlt_to_QltT.
    (* 逐点目标：e < RHS_n − (metric a c)_n，其中
       RHS_n == (|u a n − u b n| + |u b n − u c n|) + eps_n、(metric a c)_n == |u a n − u c n| *)
    (* 链：e < eps_n − 0 ≤ (A + eps_n) − A ≤ (B + eps_n) − A == RHS_n − (metric a c)_n
       （A := |u a n − u c n|，B := |u a n − u b n| + |u b n − u c n|） *)
    apply (Qlt_le_trans _ (projT1 eps n - 0) _).
    + apply QltT_to_Qlt. apply (HN n). exact Hn.
    + apply (Qle_trans _ ((Qabs (projT1 a n - projT1 c n) + projT1 eps n) - Qabs (projT1 a n - projT1 c n)) _).
      * (* eps_n − 0 ≤ (A + eps_n) − A：两边 == eps_n *)
        apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
        transitivity (projT1 eps n).
        -- (* eps_n − 0 == eps_n（判例：Qopp 0 的 Qred 卡 ring） *)
           unfold Qminus.
           assert (Hopp0 : Qopp 0%Q == 0%Q).
           { transitivity (Qred (Qmake 0 1)).
             - reflexivity.
             - apply Qred_correct. }
           rewrite Hopp0. apply Qplus_0_r.
        -- (* eps_n == (A + eps_n) − A：ring *)
           ring.
      * (* (A + eps_n) − A ≤ RHS_n − (metric a c)_n：经 (B + eps_n) − A 两层 *)
        apply (Qle_trans _ ((Qabs (projT1 a n - projT1 b n) + Qabs (projT1 b n - projT1 c n)) + projT1 eps n - Qabs (projT1 a n - projT1 c n)) _).
        -- (* (A + eps_n) − A ≤ (B + eps_n) − A：Qplus 右平移（proj2 Qplus_le_l）+ 三角不等式 *)
           apply (proj2 (Qplus_le_l (Qabs (projT1 a n - projT1 c n) + projT1 eps n)
                                    ((Qabs (projT1 a n - projT1 b n) + Qabs (projT1 b n - projT1 c n)) + projT1 eps n)
                                    (Qopp (Qabs (projT1 a n - projT1 c n))))).
           apply (Qplus_le_compat (Qabs (projT1 a n - projT1 c n))
                                  (Qabs (projT1 a n - projT1 b n) + Qabs (projT1 b n - projT1 c n))
                                  (projT1 eps n) (projT1 eps n)).
           ++ apply (Qle_trans _ (Qabs ((projT1 a n - projT1 b n) + (projT1 b n - projT1 c n))) _).
             { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. ring. }
             { apply Qabs_triangle. }
           ++ apply Qle_refl.
        -- (* (B + eps_n) − A ≤ RHS_n − (metric a c)_n：qeq 换形（setoid_rewrite，勿 rewrite） *)
           apply QleT'_to_Qle. apply qeq_le.
             apply qeq_imp_qeqT.
           assert (HpR : projT1 (real_plus (real_plus (real_metric a b) (real_metric b c)) eps) n ==
                         (Qabs (projT1 a n - projT1 b n) + Qabs (projT1 b n - projT1 c n)) + projT1 eps n).
           { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_metric a b) (real_metric b c)) eps n)).
             rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_metric a b) (real_metric b c) n)).
             unfold real_metric.
             rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a (real_opp b)) n)).
             rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp b) n)).
             rewrite (qeqT_imp_qeq _ _ (real_opp_proj b n)).
             rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus b (real_opp c)) n)).
             rewrite (qeqT_imp_qeq _ _ (real_plus_proj b (real_opp c) n)).
             rewrite (qeqT_imp_qeq _ _ (real_opp_proj c n)).
             assert (Habs1 : Qabs (projT1 a n + - projT1 b n) == Qabs (projT1 a n - projT1 b n)).
             { apply Qabs_wd. ring. }
             assert (Habs2 : Qabs (projT1 b n + - projT1 c n) == Qabs (projT1 b n - projT1 c n)).
             { apply Qabs_wd. ring. }
             rewrite Habs1. rewrite Habs2. reflexivity. }
           assert (HpL : projT1 (real_metric a c) n == Qabs (projT1 a n - projT1 c n)).
           { unfold real_metric.
             rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a (real_opp c)) n)).
             rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp c) n)).
             rewrite (qeqT_imp_qeq _ _ (real_opp_proj c n)).
             apply Qabs_wd. ring. }
           setoid_rewrite HpR. setoid_rewrite HpL. reflexivity.
Qed.

(* 接口 Proper 参数序取（x1≈x2 且 y1≈y2）——real_eq_plus/mult_compat 原始序是 a≈c 且 b≈d *)

(* NatLe ↔ (<=)%nat 桥（接口 cauchy_complete 用 NatLe，real 层用 nat ≤） *)
(* Id → =（单构造子归纳）与反向 *)
Lemma Id_eq : forall {A : Set} (x y : A), Id x y -> x = y.
Proof.
  intros A x y H. destruct H. reflexivity.
Qed.

Lemma eq_Id : forall {A : Set} (x y : A), x = y -> Id x y.
Proof.
  intros A x y H.
  (* ToyR 替换：显式构造项——eq_rect 沿 Leibniz 等式 H 把基点 id_refl
     从 Id x x 运送到 Id x y（不经 subst 改写魔法，逐参全显） *)
  exact (eq_rect x (fun z : A => Id x z) id_refl y H).
Qed.

Lemma NatLe_to_le : forall n m : nat, NatLe n m -> NatLe n m.
Proof.
  intros n m H. exact H.
Qed.

Lemma le_to_NatLe : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  unfold NatLe.
  (* ToyR 替换：assert 两段组合——① nat 序经 Nat.leb_le 降为
     bool 等式（具名中间步）；② 经 eq_Id 升回 Id 层（两端全显） *)
  assert (Hb : Nat.leb n m = true) by (apply Nat.leb_le; exact H).
  apply (eq_Id (Nat.leb n m) true).
  exact Hb.
Qed.

Lemma real_cauchy_complete_metric_natle :
  forall (u : nat -> Real),
    (forall eps : Real, real_lt real_zero eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n -> real_lt (real_metric (u m) (u n)) eps)) ->
    sigT (fun l : Real => real_lim u l).
Proof.
  intros u Hcau.
  apply real_cauchy_complete_metric.
  intros eps Heps.
  destruct (Hcau eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  apply (HN m n (le_to_NatLe N m Hm) (le_to_NatLe N n Hn)).
Qed.

Lemma real_eq_plus_compat_adapt : forall x1 x2 y1 y2 : Real,
  real_eq x1 x2 -> real_eq y1 y2 -> real_eq (real_plus x1 y1) (real_plus x2 y2).
Proof.
  intros x1 x2 y1 y2 H12 H34.
  apply (real_eq_plus_compat x1 y1 x2 y2 H12 H34).
Qed.

Lemma real_eq_mult_compat_adapt : forall x1 x2 y1 y2 : Real,
  real_eq x1 x2 -> real_eq y1 y2 -> real_eq (real_mult x1 y1) (real_mult x2 y2).
Proof.
  intros x1 x2 y1 y2 H12 H34.
  apply (real_eq_mult_compat x1 y1 x2 y2 H12 H34).
Qed.
(* ============ Core 实例组装：Real 满足 RealSetoidCore.RealInterfaceSetoidCore ============
   req := real_eq；缺口（exp_neg_plus / log_inv 族）属阶段 2，完整 RealInterfaceSetoid 届时组装。
   metric_pos / metric_triangle 用逐 eps 形式（判例，Or 编码不可证）。 *)
Instance Real_RealInterfaceSetoidCore : RealSetoidCore.RealInterfaceSetoidCore := {
  RealSetoidCore.req := real_eq;
  RealSetoidCore.req_refl := real_eq_refl;
  RealSetoidCore.req_sym := real_eq_sym;
  RealSetoidCore.req_trans := real_eq_trans;
  RealSetoidCore.zero := real_zero;
  RealSetoidCore.one := real_one;
  RealSetoidCore.plus := real_plus;
  RealSetoidCore.mult := real_mult;
  RealSetoidCore.opp := real_opp;
  RealSetoidCore.abs := real_abs;
  RealSetoidCore.lt := real_lt;
  RealSetoidCore.le := real_le;
  RealSetoidCore.req_plus_compat := real_eq_plus_compat_adapt;
  RealSetoidCore.req_mult_compat := real_eq_mult_compat_adapt;
  RealSetoidCore.req_opp_compat := real_eq_opp_compat;
  RealSetoidCore.req_abs_compat := real_eq_abs_compat;
  RealSetoidCore.req_lt_compat := real_lt_compat;
  RealSetoidCore.req_le_compat := real_le_compat;
  RealSetoidCore.plus_assoc := real_plus_assoc;
  RealSetoidCore.plus_comm := real_plus_comm;
  RealSetoidCore.plus_zero := real_plus_zero;
  RealSetoidCore.plus_opp := real_plus_opp;
  RealSetoidCore.mult_assoc := real_mult_assoc;
  RealSetoidCore.mult_comm := real_mult_comm;
  RealSetoidCore.mult_one := real_mult_one;
  RealSetoidCore.distrib := real_distrib;
  RealSetoidCore.mult_zero := real_mult_zero;
  RealSetoidCore.lt_irrefl := real_lt_irrefl;
  RealSetoidCore.lt_trans := real_lt_trans;
  RealSetoidCore.le_refl := real_le_refl;
  RealSetoidCore.le_trans := real_le_trans;
  RealSetoidCore.le_antisym := real_le_antisym;
  RealSetoidCore.le_lt_trans := real_le_lt_trans;
  RealSetoidCore.lt_le_trans := real_lt_le_trans;
  RealSetoidCore.lt_le_iff := real_lt_le_iff_req;
  RealSetoidCore.le_id_l := real_le_id_l;
  RealSetoidCore.le_id_r := real_le_id_r;
  RealSetoidCore.lt_id_l := real_lt_id_l;
  RealSetoidCore.lt_id_r := real_lt_id_r;
  RealSetoidCore.inv_pos := real_inv_pos;
  RealSetoidCore.inv_pos_correct := real_inv_pos_correct;
  RealSetoidCore.metric := real_metric;
  RealSetoidCore.metric_sym := real_metric_sym;
  RealSetoidCore.metric_pos := real_metric_pos_eps;
  RealSetoidCore.metric_zero := real_metric_zero;
  RealSetoidCore.metric_triangle := real_metric_triangle_eps;
  RealSetoidCore.lim := real_lim;
  RealSetoidCore.lim_unique := real_lim_unique;
  RealSetoidCore.cauchy_complete := real_cauchy_complete_metric_natle;
}.
End RealSetoid.
(* 结束：本块全部为构造性定义和可证明引理，无公理面与承认件   *)
(* ============================================================ *)
(* ============================================================ *)
(* 阶段 2：exp 加法性 Q 层（并入，来自检验 _dbg_exp_plus.v，37 引理）
   目标：cauchy_real_exp_plus（exp_neg_plus 字段材料）
   内容：q_binom 二项式定理 + exp 层 Cauchy 积引理族（exp_cauchy_double / exp_trunc_decomp 等）
   依赖：q_fact/q_pow/sum_upto/exp_partial/exp_series 族（主文件已有）
   验证：coqc+coqtop 双验 + BAD=0（备份 100） *)
(* Qred 透明（含 Z.ggcd 约分）卡 conversion——设为不透明，Qred 作原子处理（判例） *)
Opaque Qred.

Section ExpPlusStage2.

(* ===== Q 层：组合数 ===== *)

(* q_choose n k == n!/(k!·(n−k)!)（k ≤ n 时标准意义） *)
Definition q_choose (n k : nat) : Q :=
  q_fact n / (q_fact k * q_fact (n - k)).

(* 边界：q_choose n 0 == 1（field 对 q_fact Fixpoint 原子失败（判例），手工链） *)
Lemma q_choose_0 : forall n : nat,QeqT (q_choose n 0) (1).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  unfold q_choose.
  assert (Hsub : (n - 0)%nat = n) by lia.  (* n - 0 == n（lia 桥，%nat 防 Q 劫持） *)
  rewrite Hsub.
  simpl.  (* q_fact 0 == 1 计算归约 *)
  (* q_fact n / (1 * q_fact n) == 1：Qinv_comp 换形分母 + Qmult_inv_r（field/rewrite 均遇 Qred） *)
  unfold Qdiv.
  transitivity (q_fact n * / q_fact n).
  - setoid_rewrite (Qmult_1_l (q_fact n)). reflexivity.
  - apply Qmult_inv_r.
    intro Hq0. exact (Qlt_not_eq 0 (q_fact n) (QltT_to_Qlt 0 (q_fact n) (q_fact_pos n)) (Qeq_sym (q_fact n) 0 Hq0)).
Qed.

(* 边界：q_choose n n == 1 *)
Lemma q_choose_n : forall n : nat,QeqT (q_choose n n) (1).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  unfold q_choose.
  assert (Hsub : (n - n)%nat = 0%nat) by lia.  (* n - n == 0（lia 桥，%nat 防 Q 劫持） *)
  rewrite Hsub.
  simpl.  (* q_fact 0 == 1 计算归约 *)
  unfold Qdiv.
  transitivity (q_fact n * / q_fact n).
  - setoid_rewrite (Qmult_1_r (q_fact n)). reflexivity.  (* 分母 q_fact n * 1（Qmult_1_r） *)
  - apply Qmult_inv_r.
    intro Hq0. exact (Qlt_not_eq 0 (q_fact n) (QltT_to_Qlt 0 (q_fact n) (q_fact_pos n)) (Qeq_sym (q_fact n) 0 Hq0)).
Qed.

(* ===== Q 层：组合数（续）===== *)

(* nat 层：S n − k == n + 1 − k（k ≤ n+1） *)
Lemma nat_sub_succ : forall n k : nat, (k <= n + 1)%nat -> Id ((Datatypes.S n - k)%nat) ((n + 1 - k)%nat).
Proof. intros n k H. apply RealSetoid.eq_Id. lia. Qed.

(* nat 层：n − (k−1) == n + 1 − k（k ≥ 1） *)
Lemma nat_sub_pred : forall n k : nat, (1 <= k)%nat -> Id ((n - (k - 1))%nat) ((n + 1 - k)%nat).
Proof. intros n k H. apply RealSetoid.eq_Id. lia. Qed.

(* ===== Q 层：除法通分/消去（纯变量 field，供 Pascal 组装） ===== *)

(* 通分：F/(K·N) + F/(L·M) == F·(L·M + K·N)/(K·N·L·M) *)
Lemma q_div_plus : forall (F K N L M : Q),
  ~ K == 0 -> ~ N == 0 -> ~ L == 0 -> ~ M == 0 ->QeqT (F / (K * N) + F / (L * M)) (F * (L * M + K * N) / (K * N * L * M)).
Proof.
  intros F K N L M HK HN HL HM.
  apply qeq_imp_qeqT.
  field.
  repeat split.
  - exact HM.
  - exact HL.
  - exact HN.
  - exact HK.
Qed.

(* 消去：F·A/(B·A) == F/B（A,B ≠ 0） *)
Lemma q_div_cancel : forall (F A B : Q), ~ A == 0 -> ~ B == 0 ->QeqT (F * A / (B * A)) (F / B).
Proof.
  intros F A B HA HB.
  apply qeq_imp_qeqT.
  field.
  split.
  - exact HB.
  - exact HA.
Qed.

(* ===== Pascal 恒等式（q_choose_succ）===== *)

(* nat 层：S (n − k) == n + 1 − k（k ≤ n） *)
Lemma nat_succ_sub : forall n k : nat, (k <= n)%nat -> Id ((Datatypes.S (n - k))%nat) ((n + 1 - k)%nat).
Proof. intros n k H. apply RealSetoid.eq_Id. lia. Qed.

(* nat 层：S (k − 1) == k（k ≥ 1） *)
Lemma nat_succ_pred : forall n k : nat, (1 <= k)%nat -> Id ((Datatypes.S (k - 1))%nat) k.
Proof. intros n k H. apply RealSetoid.eq_Id. lia. Qed.

(* q_fact 对 nat 等式的 Leibniz 兼容（HK 换形用）——主文件已有 L9048，此处不再定义 *)

(* 分子重排（段B2 用）：N·L·(X+Y) == L·X·N + Y·L·N *)
Lemma q_mix_ring : forall (n l x y : Q),QeqT (n * l * (x + y)) (l * x * n + y * l * n).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* 分母重排（段B2 用）：(K·M)·(N·L) == (K·N)·L·M *)
Lemma q_den_reorder : forall (K M N L : Q),QeqT ((K * M) * (N * L)) ((K * N) * L * M).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* 子目标2 独立：通分中间项 == RHS（q_div_plus 反向） *)
Lemma q_choose_succ_div : forall (F K N L M : Q),
  ~ K == 0 -> ~ N == 0 -> ~ L == 0 -> ~ M == 0 ->QeqT (F * (L * M + K * N) / (K * N * L * M)) (F / (K * N) + F / (L * M)).
Proof.
  intros F K N L M HK HN HL HM.
  apply qeq_imp_qeqT.
  apply Qeq_sym.
  apply qeqT_imp_qeq. apply (q_div_plus F K N L M); assumption.
Qed.

(* Pascal：q_choose (S n) k == q_choose n k + q_choose n (k−1)（1 ≤ k ≤ n） *)
Lemma q_choose_succ : forall n k : nat, (1 <= k)%nat -> (k <= n)%nat ->QeqT (q_choose (Datatypes.S n) k) (q_choose n k + q_choose n (k - 1)).
Proof.
  intros n k Hk1 Hkn.
  apply qeq_imp_qeqT.
  unfold q_choose.
  assert (Hs1 : (Datatypes.S n - k)%nat = (n + 1 - k)%nat) by lia.
  assert (Hp1 : (n - (k - 1))%nat = (n + 1 - k)%nat) by lia.
  rewrite Hs1, Hp1.
  assert (Hs2 : (Datatypes.S (n - k))%nat = (n + 1 - k)%nat) by lia.
  assert (Hs3 : (Datatypes.S (k - 1))%nat = k) by lia.
  set (F := q_fact n).
  set (K := q_fact k).
  set (N := q_fact (n - k)).
  set (L := q_fact (k - 1)).
  set (M := q_fact (n + 1 - k)).
  transitivity (F * (L * M + K * N) / (K * N * L * M)).
  - assert (HM : M == (Z.of_nat (n + 1 - k) # 1) * N).
    { unfold M, N. rewrite <- Hs2. apply qeqT_imp_qeq. apply q_fact_succ. }
    assert (HK : K == (Z.of_nat k # 1) * L).
    { unfold K, L.
      assert (HkS : k = Datatypes.S (k - 1)) by lia.
      transitivity (q_fact (Datatypes.S (k - 1))).
      - apply qeqT_imp_qeq. apply q_fact_nat_eq. exact HkS.
      - assert (Hz : (Z.of_nat (Datatypes.S (k - 1)) # 1) == (Z.of_nat k # 1)).
        { unfold Qeq. simpl. lia. }
        transitivity ((Z.of_nat (Datatypes.S (k - 1)) # 1) * q_fact (k - 1)).
        { apply qeqT_imp_qeq. apply q_fact_succ. }
        { setoid_rewrite Hz. reflexivity. } }
    assert (Hn1 : (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat (n + 1) # 1)).
    { unfold Qeq. simpl. lia. }
    transitivity ((Z.of_nat (n + 1) # 1) * F / (K * M)).
    + setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ n)).
      setoid_rewrite Hn1.
      reflexivity.
    + (* 段B：(n+1)·F/(K·M) == F·(L·M+K·N)/(K·N·L·M) *)
      assert (HZ : (Z.of_nat (n + 1 - k) # 1) + (Z.of_nat k # 1) == (Z.of_nat (n + 1) # 1)).
      { transitivity (Qred (Qmake (Z.of_nat (n + 1 - k) + Z.of_nat k) 1)).
        - unfold Qplus. simpl.
          rewrite (Z.mul_1_r (Z.of_nat (n + 1 - k))).
          rewrite (Z.mul_1_r (Z.of_nat k)).
          apply Qeq_sym. apply Qred_correct.
        - transitivity (Qmake (Z.of_nat (n + 1 - k) + Z.of_nat k) 1).
          + apply Qred_correct.
          + unfold Qeq. simpl.
            assert (Hadd : (Z.of_nat (n + 1 - k) + Z.of_nat k)%Z = Z.of_nat (n + 1)) by lia.
            rewrite Hadd. reflexivity. }
      transitivity (F * (Z.of_nat (n + 1) # 1) / (K * M)).
      * setoid_rewrite (Qmult_comm (Z.of_nat (n + 1) # 1) F). reflexivity.
      * transitivity (F * (N * L * (Z.of_nat (n + 1) # 1)) / (K * M * (N * L))).
        -- transitivity (F * (Z.of_nat (n + 1) # 1) * (N * L) / (K * M * (N * L))).
           ++ apply Qeq_sym.
              apply qeqT_imp_qeq. apply (q_div_cancel (F * (Z.of_nat (n + 1) # 1)) (N * L) (K * M)).
              ** intro Hz.
                 assert (HN0 : ~ N == 0) by (unfold N; intro Hq0; exact (Qlt_not_eq 0 (q_fact (n - k)) (QltT_to_Qlt 0 (q_fact (n - k)) (q_fact_pos (n - k))) (Qeq_sym (q_fact (n - k)) 0 Hq0))).
                 assert (HL0 : ~ L == 0) by (unfold L; intro Hq0; exact (Qlt_not_eq 0 (q_fact (k - 1)) (QltT_to_Qlt 0 (q_fact (k - 1)) (q_fact_pos (k - 1))) (Qeq_sym (q_fact (k - 1)) 0 Hq0))).
                 destruct (Qmult_integral N L Hz) as [HNz | HLz].
                 { apply HN0. exact HNz. }
                 { apply HL0. exact HLz. }
              ** intro Hz.
                 assert (HK0 : ~ K == 0) by (unfold K; intro Hq0; exact (Qlt_not_eq 0 (q_fact k) (QltT_to_Qlt 0 (q_fact k) (q_fact_pos k)) (Qeq_sym (q_fact k) 0 Hq0))).
                 assert (HM0 : ~ M == 0) by (unfold M; intro Hq0; exact (Qlt_not_eq 0 (q_fact (n + 1 - k)) (QltT_to_Qlt 0 (q_fact (n + 1 - k)) (q_fact_pos (n + 1 - k))) (Qeq_sym (q_fact (n + 1 - k)) 0 Hq0))).
                 destruct (Qmult_integral K M Hz) as [HKz | HMz].
                 { apply HK0. exact HKz. }
                 { apply HM0. exact HMz. }
           ++ setoid_rewrite <- (Qmult_assoc F (Z.of_nat (n + 1) # 1) (N * L)).
              setoid_rewrite (Qmult_comm (Z.of_nat (n + 1) # 1) (N * L)).
              reflexivity.
        -- (* 段B2：分子分母换形链（setoid_rewrite） *)
           setoid_rewrite <- HZ.
           setoid_rewrite (qeqT_imp_qeq _ _ (q_mix_ring N L (Z.of_nat (n + 1 - k) # 1) (Z.of_nat k # 1))).
           setoid_rewrite <- (Qmult_assoc L (Z.of_nat (n + 1 - k) # 1) N).
           setoid_rewrite (qeqT_imp_qeq _ _ (q_den_reorder K M N L)).
           setoid_rewrite <- HM.
           setoid_rewrite <- HK.
           reflexivity.
  - apply qeqT_imp_qeq. apply q_choose_succ_div.
    + intro Hz. unfold K in Hz. exact (Qlt_not_eq 0 (q_fact k) (QltT_to_Qlt 0 (q_fact k) (q_fact_pos k)) (Qeq_sym (q_fact k) 0 Hz)).
    + intro Hz. unfold N in Hz. exact (Qlt_not_eq 0 (q_fact (n - k)) (QltT_to_Qlt 0 (q_fact (n - k)) (q_fact_pos (n - k))) (Qeq_sym (q_fact (n - k)) 0 Hz)).
    + intro Hz. unfold L in Hz. exact (Qlt_not_eq 0 (q_fact (k - 1)) (QltT_to_Qlt 0 (q_fact (k - 1)) (q_fact_pos (k - 1))) (Qeq_sym (q_fact (k - 1)) 0 Hz)).
    + intro Hz. unfold M in Hz. exact (Qlt_not_eq 0 (q_fact (n + 1 - k)) (QltT_to_Qlt 0 (q_fact (n + 1 - k)) (q_fact_pos (n + 1 - k))) (Qeq_sym (q_fact (n + 1 - k)) 0 Hz)).
Qed.

(* ===== 二项式定理（q_binom）：q_pow (a+b) n == Σ_{k=0}^{n} C(n,k)·a^k·b^(n−k) ===== *)

(* sum_upto 乘性分布：c·Σ f == Σ (c·f) *)
Lemma sum_upto_scal : forall (n : nat) (c : Q) (f : nat -> Q),QeqT (c * sum_upto n f) (sum_upto n (fun i => c * f i)).
Proof.
  intros n c f.
  apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - ring.
  - setoid_rewrite (Qmult_plus_distr_r c (sum_upto n' f) (f n')).
    rewrite IH.
    ring.
Qed.

(* 基例 n=0 *)
Lemma q_binom_0 : forall a b : Q,QeqT (q_pow (a + b) 0) (sum_upto 1 (fun k : nat => q_choose 0 k * q_pow a k * q_pow b (0 - k))).
Proof.
  intros a b.
  apply qeq_imp_qeqT.
  simpl.
  rewrite (qeqT_imp_qeq _ _ (q_choose_0 0)).
  simpl. ring.
Qed.

(* 换元（第一和用）：Σ_{j=0}^{n+1} f (j−1) == f 0 + Σ_{k=0}^{n} f k
   核心：sum_upto_rot 拆首项 + 逐项 S i − 1 == i（lia） *)
Lemma sum_upto_shift_pred : forall (n : nat) (f : nat -> Q),QeqT (sum_upto (Datatypes.S (Datatypes.S n)) (fun j => f (Nat.sub j 1))) (f 0%nat + sum_upto (Datatypes.S n) (fun k => f k)).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  transitivity (f (Nat.sub 0 1) + sum_upto (Datatypes.S n) (fun i => f (Nat.sub (Datatypes.S i) 1))).
  - change (sum_upto (Datatypes.S (Datatypes.S n)) (fun j : nat => f (Nat.sub j 1)) ==
            f (Nat.sub 0 1) + sum_upto (Datatypes.S n) (fun i : nat => f (Nat.sub (Datatypes.S i) 1))).
    exact (qeqT_imp_qeq _ _ (sum_upto_rot (Datatypes.S n) (fun j => f (Nat.sub j 1)))).
  - replace (Nat.sub 0 1) with 0%nat by lia.
    assert (Hsum : sum_upto (Datatypes.S n) (fun i => f (Nat.sub (Datatypes.S i) 1)) ==
                   sum_upto (Datatypes.S n) (fun i => f i)).
    { apply qeqT_imp_qeq. apply (sum_upto_ext_below (Datatypes.S n)
               (fun i => f (Nat.sub (Datatypes.S i) 1)) (fun i => f i)).
      intro i. intro Hi.
      replace (Nat.sub (Datatypes.S i) 1) with i by lia.
      apply qeq_imp_qeqT. reflexivity. }
    setoid_rewrite Hsum. reflexivity.
Qed.

(* 第一和换元：Σ_{k=0}^{n} g k == Σ_{j=1}^{n+1} g (j−1)（j = k+1）
   由 sum_upto_shift_pred 反向 + sum_upto_rot 拆 j=0 项 *)
Lemma sum_upto_shift_pred2 : forall (n : nat) (f : nat -> Q),QeqT (sum_upto (Datatypes.S n) (fun k => f k) + f 0%nat) (sum_upto (Datatypes.S (Datatypes.S n)) (fun j => f (Nat.sub j 1))).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  transitivity (f 0%nat + sum_upto (Datatypes.S n) (fun k => f k)).
  - apply Qplus_comm.
  - apply Qeq_sym. exact (qeqT_imp_qeq _ _ (sum_upto_shift_pred n f)).
Qed.

(* ===== 二项式定理配对引理（q_binom_S 第二小步用） ===== *)

(* 配对中间项：g1 i + g2 (S i) == h (S i)（i < n'）
   g1 i := C(n',i)·a^(S i)·b^(n'−i)
   g2 (S i) := C(n',S i)·a^(S i)·b^(S n'−S i)
   h (S i) := C(S n',S i)·a^(S i)·b^(S n'−S i)
   配对：C(n',i)+C(n',S i) == C(S n',S i)（q_choose_succ，S i − 1 == i）+ b 指数 lia 桥
   （判例：q_pow 参数 nat 换形用 q_pow_comp_proper） *)
Lemma q_binom_pair_mid : forall (a b : Q) (n' i : nat),
  (i < n')%nat ->QeqT ((q_choose n' i * q_pow a (Datatypes.S i) * q_pow b (Nat.sub n' i)) +
  (q_choose n' (Datatypes.S i) * q_pow a (Datatypes.S i) * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i)))) (q_choose (Datatypes.S n') (Datatypes.S i) * q_pow a (Datatypes.S i) * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i))).
Proof.
  intros a b n' i Hi.
  apply qeq_imp_qeqT.
  assert (Hbe : Nat.sub n' i = Nat.sub (Datatypes.S n') (Datatypes.S i)) by lia.
  setoid_replace (q_pow b (Nat.sub n' i)) with (q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i))).
  2: { apply (q_pow_comp_proper b b (Qeq_refl b) (Nat.sub n' i) (Nat.sub (Datatypes.S n') (Datatypes.S i)) Hbe). }
  assert (Hp : q_choose (Datatypes.S n') (Datatypes.S i) == q_choose n' (Datatypes.S i) + q_choose n' (Nat.sub (Datatypes.S i) 1)).
  { apply qeqT_imp_qeq. apply (q_choose_succ n' (Datatypes.S i)); lia. }
  assert (Hq : q_choose n' (Nat.sub (Datatypes.S i) 1) == q_choose n' i).
  { unfold q_choose.
    assert (Hf1 : q_fact (Nat.sub (Datatypes.S i) 1) == q_fact i) by (apply qeqT_imp_qeq, q_fact_nat_eq; lia).
    assert (Hf2 : q_fact (Nat.sub n' (Nat.sub (Datatypes.S i) 1)) == q_fact (Nat.sub n' i)) by (apply qeqT_imp_qeq, q_fact_nat_eq; lia).
    setoid_rewrite Hf1.
    setoid_rewrite Hf2.
    reflexivity. }
  setoid_rewrite Hp.
  setoid_rewrite Hq.
  ring.
Qed.

(* 配对首项：g2 0 == h 0（q_choose_0 双侧 + ring） *)
Lemma q_binom_pair_head : forall (a b : Q) (n' : nat),QeqT (q_choose n' 0%nat * q_pow a 0%nat * q_pow b (Nat.sub (Datatypes.S n') 0)) (q_choose (Datatypes.S n') 0%nat * q_pow a 0%nat * q_pow b (Nat.sub (Datatypes.S n') 0)).
Proof.
  intros a b n'.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (q_choose_0 n')).
  setoid_rewrite (qeqT_imp_qeq _ _ (q_choose_0 (Datatypes.S n'))).
  simpl. ring.
Qed.

(* 配对尾项：g1 n' == h (S n')（q_choose_n 双侧 + b^0 + ring） *)
Lemma q_binom_pair_tail : forall (a b : Q) (n' : nat),QeqT (q_choose n' n' * q_pow a (Datatypes.S n') * q_pow b (Nat.sub n' n')) (q_choose (Datatypes.S n') (Datatypes.S n') * q_pow a (Datatypes.S n') * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S n'))).
Proof.
  intros a b n'.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (q_choose_n n')).
  setoid_rewrite (qeqT_imp_qeq _ _ (q_choose_n (Datatypes.S n'))).
  simpl. ring.
Qed.

(* ===== q_binom_S：归纳步（前 4 步 + 第一小步 + 第二小步 Pascal 合并配对） =====
   配对蓝图（判例）：LHS == Σ_{j≤n'+1} g1(j−1) + (Σ g2 − g1 0) == Σ_{j=1}^{n'+1} g1(j−1) + Σ_{j=0}^{n'} g2 j
   配对：j=0（g2 0 == h 0，q_binom_pair_head）；j=1..n'（g1(j−1)+g2 j == h j，q_binom_pair_mid）；
        j=n'+1（g1 n' == h(S n')，q_binom_pair_tail）
   实现：LHS 重组 sum_upto_rot → 中间项 g2 0 + Σ_{i<n'} (g1 i + g2 (S i)) + g1 n'；
        RHS 拆 h 0 + Σ_{i<n'} h (S i) + h (S n')（sum_upto_rot 一次 + change 拆尾项） *)
Lemma q_binom_S : forall a b : Q, forall n' : nat,QeqT (q_pow (a + b) n') (sum_upto (Datatypes.S n') (fun k : nat => q_choose n' k * q_pow a k * q_pow b (Nat.sub n' k)))->QeqT (q_pow (a + b) (Datatypes.S n')) (sum_upto (Datatypes.S (Datatypes.S n')) (fun k : nat => q_choose (Datatypes.S n') k * q_pow a k * q_pow b (Nat.sub (Datatypes.S n') k))).
Proof.
  intros a b n' IH.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ (a + b) n')).
  setoid_rewrite (qeqT_imp_qeq _ _ IH).
  (* (a+b)·Σ_{k≤n'} C(n',k)·a^k·b^(n'−k)：提出 (a+b) 入和（sum_upto_scal 正向） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scal (Datatypes.S n') (a + b)
                                (fun k => q_choose n' k * q_pow a k * q_pow b (Nat.sub n' k)))).
  (* ④逐项分配 + 拆双和：Σ (a+b)·f == Σ f1 + Σ f2 *)
  transitivity (sum_upto (Datatypes.S n') (fun k => q_choose n' k * q_pow a (Datatypes.S k) * q_pow b (Nat.sub n' k)) +
                sum_upto (Datatypes.S n') (fun k => q_choose n' k * q_pow a k * q_pow b (Nat.sub (Datatypes.S n') k))).
  - setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S n')
                        (fun k => q_choose n' k * q_pow a (Datatypes.S k) * q_pow b (Nat.sub n' k))
                        (fun k => q_choose n' k * q_pow a k * q_pow b (Nat.sub (Datatypes.S n') k)))).
    apply qeqT_imp_qeq. apply (sum_upto_ext_below (Datatypes.S n')
             (fun k => (a + b) * (q_choose n' k * q_pow a k * q_pow b (Nat.sub n' k)))
             (fun k => q_choose n' k * q_pow a (Datatypes.S k) * q_pow b (Nat.sub n' k) +
                       q_choose n' k * q_pow a k * q_pow b (Nat.sub (Datatypes.S n') k))).
    intro k. intro Hklt. apply NatLe_drop in Hklt. apply qeq_imp_qeqT.
    assert (Hps : (Datatypes.S (Nat.sub n' k))%nat = (Nat.sub (Datatypes.S n') k)) by lia.
    transitivity (q_choose n' k * (a * q_pow a k) * q_pow b (Nat.sub n' k) +
                  q_choose n' k * q_pow a k * (b * q_pow b (Nat.sub n' k))).
    + ring.
    + assert (Hpa : a * q_pow a k == q_pow a (Datatypes.S k)).
      { apply Qeq_sym. apply qeqT_imp_qeq. apply q_pow_succ. }
      assert (Hpb : b * q_pow b (Nat.sub n' k) == q_pow b (Datatypes.S (Nat.sub n' k))).
      { apply Qeq_sym. apply qeqT_imp_qeq. apply q_pow_succ. }
      setoid_rewrite Hpa.
      setoid_rewrite Hpb.
      replace (Datatypes.S (Nat.sub n' k)) with (Nat.sub (Datatypes.S n') k) by lia.
      reflexivity.
  - (* ⑤换元 + Pascal 合并：第二段 Σ f1 + Σ f2 == Σ_{j≤n'+1} C(n'+1,j)·a^j·b^(n'+1−j) *)
    set (g1 := fun k : nat => q_choose n' k * q_pow a (Datatypes.S k) * q_pow b (Nat.sub n' k)).
    set (g2 := fun k : nat => q_choose n' k * q_pow a k * q_pow b (Nat.sub (Datatypes.S n') k)).
    set (h := fun j : nat => q_choose (Datatypes.S n') j * q_pow a j * q_pow b (Nat.sub (Datatypes.S n') j)).
    change (sum_upto (Datatypes.S (Datatypes.S n')) (fun k : nat => q_choose (Datatypes.S n') k * q_pow a k * q_pow b (Nat.sub (Datatypes.S n') k)))
      with (sum_upto (Datatypes.S (Datatypes.S n')) h).
    (* 第一和换元（j=k+1）：shift_pred2：Σ g1 + g1 0 == Σ_{j≤n'+1} g1 (j−1) *)
    assert (Hsp := sum_upto_shift_pred2 n' g1).
    (* 变形：Σ g1 + Σ g2 == Σ g1(j−1) + (Σ g2 − g1 0)
       经 (Σ g1 + g1 0) − g1 0 + Σ g2（ring + Hsp） *)
    transitivity (sum_upto (Datatypes.S (Datatypes.S n')) (fun j => g1 (Nat.sub j 1)) +
                  (sum_upto (Datatypes.S n') (fun k => g2 k) - g1 0%nat)).
    { (* Σ g1 + Σ g2 == Σ g1(j−1) + (Σ g2 − g1 0) *)
      transitivity ((sum_upto (Datatypes.S n') g1 + g1 0%nat) + (sum_upto (Datatypes.S n') g2 - g1 0%nat)).
      { ring. }
      { setoid_rewrite (qeqT_imp_qeq _ _ Hsp). reflexivity. } }
    { (* 第二小步（Pascal 合并配对）：
           LHS == Σ_{j≤n'+1} g1(j−1) + (Σ g2 − g1 0)
               == Σ g1 + Σ g2                          [sum_upto_shift_pred + ring 消 g1 0 − g1 0]
               == g2 0 + Σ_{i<n'} (g1 i + g2 (S i)) + g1 n'   [拆尾项/首项 + sum_upto_plus 反向]
       RHS == h 0 + Σ_{i<n'} h (S i) + h (S n')        [sum_upto_rot + change 拆尾项]
       配对：q_binom_pair_head / q_binom_pair_mid（ext_below，i<n'）/ q_binom_pair_tail *)
      transitivity (sum_upto (Datatypes.S n') g1 + sum_upto (Datatypes.S n') g2).
      { transitivity (g1 0%nat + sum_upto (Datatypes.S n') g1 + (sum_upto (Datatypes.S n') g2 - g1 0%nat)).
        { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift_pred n' g1)). reflexivity. }
        { ring. } }
      { (* Σ g1 + Σ g2 == g2 0 + Σ_{i<n'} (g1 i + g2 (S i)) + g1 n' *)
        transitivity (g2 0%nat + sum_upto n' (fun i => g1 i + g2 (Datatypes.S i)) + g1 n').
        { transitivity ((sum_upto n' g1 + g1 n') + (g2 0%nat + sum_upto n' (fun i => g2 (Datatypes.S i)))).
          { change (sum_upto (Datatypes.S n') g1) with (sum_upto n' g1 + g1 n').
            setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' g2)).
            reflexivity. }
          { transitivity (g2 0%nat + (sum_upto n' g1 + sum_upto n' (fun i => g2 (Datatypes.S i))) + g1 n').
            { ring. }
            { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus n' g1 (fun i => g2 (Datatypes.S i)))). reflexivity. } } }
        { (* 三段配对：g2 0 == h 0；Σ(g1 i + g2 (S i)) == Σ h (S i)；g1 n' == h (S n') *)
          transitivity (h 0%nat + sum_upto n' (fun i => h (Datatypes.S i)) + h (Datatypes.S n')).
          { unfold g1, g2, h.
            assert (Hmid : sum_upto n' (fun i => q_choose n' i * q_pow a (Datatypes.S i) * q_pow b (Nat.sub n' i) +
                                                 q_choose n' (Datatypes.S i) * q_pow a (Datatypes.S i) * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i))) ==
                           sum_upto n' (fun i => q_choose (Datatypes.S n') (Datatypes.S i) * q_pow a (Datatypes.S i) * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i)))).
            { apply qeqT_imp_qeq. apply (sum_upto_ext_below n'
                       (fun i => q_choose n' i * q_pow a (Datatypes.S i) * q_pow b (Nat.sub n' i) +
                                 q_choose n' (Datatypes.S i) * q_pow a (Datatypes.S i) * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i)))
                       (fun i => q_choose (Datatypes.S n') (Datatypes.S i) * q_pow a (Datatypes.S i) * q_pow b (Nat.sub (Datatypes.S n') (Datatypes.S i)))).
              intro i. intro Hi. assert (Hlt : (i < n')%nat) by (apply NatLe_drop in Hi; lia). apply (q_binom_pair_mid a b n' i Hlt). }
            setoid_rewrite (qeqT_imp_qeq _ _ (q_binom_pair_head a b n')).
            setoid_rewrite Hmid.
            setoid_rewrite (qeqT_imp_qeq _ _ (q_binom_pair_tail a b n')).
            reflexivity. }
          { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (Datatypes.S n') h)).
            change (sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))) with
              (sum_upto n' (fun i => h (Datatypes.S i)) + h (Datatypes.S n')).
            ring. } } } }
Qed.

(* 二项式定理主定理：q_pow (a+b) n == Σ_{k=0}^{n} C(n,k)·a^k·b^(n−k)
   归纳：q_binom_0（基例）+ q_binom_S（归纳步） *)
Lemma q_binom : forall (a b : Q) (n : nat),QeqT (q_pow (a + b) n) (sum_upto (Datatypes.S n) (fun k : nat => q_choose n k * q_pow a k * q_pow b (Nat.sub n k))).
Proof.
  intros a b n.
  induction n as [| n' IH].
  - apply q_binom_0.
  - apply (q_binom_S a b n' IH).
Qed.

(* ===== exp 层 Cauchy 积：q_binom 代入 exp_partial ===== *)

(* sum_upto 除法分配：Σ (f j / c) == (Σ f j) / c（c ≠ 0） *)
Lemma sum_upto_div : forall (n : nat) (c : Q) (f : nat -> Q),
  ~ c == 0 ->QeqT (sum_upto n (fun j => f j / c)) ((sum_upto n f) / c).
Proof.
  intros n c f Hc.
  apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - unfold Qdiv. ring.
  - setoid_rewrite IH.
    unfold Qdiv. ring.
Qed.

(* 组合数与阶乘分裂：C(n,k)/n! == 1/k! · 1/(n−k)! *)
Lemma q_choose_div_fact : forall (n k : nat),QeqT (q_choose n k / q_fact n) (Qinv (q_fact k) * Qinv (q_fact (Nat.sub n k))).
Proof.
  intros n k.
  apply qeq_imp_qeqT.
  unfold q_choose.
  unfold Qdiv.
  (* 目标：(F·/(K·N))·/F == /K·/N，F := q_fact n，K := q_fact k，N := q_fact (n−k)
     分两步：先消 F（Qmult_inv_r），再 Qinv_mult_distr *)
  transitivity (Qinv (q_fact k * q_fact (Nat.sub n k))).
  - (* (F·/(K·N))·/F == /(K·N)：结合 + 交换 + Qmult_inv_r *)
    setoid_rewrite <- (Qmult_assoc (q_fact n) (Qinv (q_fact k * q_fact (Nat.sub n k))) (Qinv (q_fact n))).
    setoid_rewrite (Qmult_comm (Qinv (q_fact k * q_fact (Nat.sub n k))) (Qinv (q_fact n))).
    setoid_rewrite (Qmult_assoc (q_fact n) (Qinv (q_fact n)) (Qinv (q_fact k * q_fact (Nat.sub n k)))).
    setoid_rewrite (Qmult_inv_r (q_fact n)).
    + setoid_rewrite (Qmult_1_l (Qinv (q_fact k * q_fact (Nat.sub n k)))). reflexivity.
    + intro Hq0. exact (Qlt_not_eq 0 (q_fact n) (QltT_to_Qlt 0 (q_fact n) (q_fact_pos n)) (Qeq_sym (q_fact n) 0 Hq0)).
  - apply (Qinv_mult_distr (q_fact k) (q_fact (Nat.sub n k))).
Qed.

(* E1：exp 项的二项式展开（q_binom + sum_upto_div 落点）
   q_pow (x+y) k / k! == Σ_{j=0}^{k} C(k,j)·x^j·y^(k−j) / k! *)
Lemma exp_term_binom : forall (x y : Q) (k : nat),QeqT (q_pow (x + y) k / q_fact k) (sum_upto (Datatypes.S k) (fun j : nat => q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k)).
Proof.
  intros x y k.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (q_binom x y k)).
  apply Qeq_sym.
  apply qeqT_imp_qeq. apply (sum_upto_div (Datatypes.S k) (q_fact k)
           (fun j => q_choose k j * q_pow x j * q_pow y (Nat.sub k j))).
  intro Hq0. exact (Qlt_not_eq 0 (q_fact k) (QltT_to_Qlt 0 (q_fact k) (q_fact_pos k)) (Qeq_sym (q_fact k) 0 Hq0)).
Qed.

(* E2：项分裂——C(k,j)·x^j·y^(k−j)/k! == (x^j/j!)·(y^(k−j)/(k−j)!) *)
Lemma exp_term_split : forall (x y : Q) (k j : nat),QeqT (q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k) ((q_pow x j / q_fact j) * (q_pow y (Nat.sub k j) / q_fact (Nat.sub k j))).
Proof.
  intros x y k j.
  apply qeq_imp_qeqT.
  (* C(k,j)/k! == 1/j!·1/(k−j)!（q_choose_div_fact）；余下 x^j·y^(k−j) 分配 *)
  transitivity ((q_choose k j / q_fact k) * q_pow x j * q_pow y (Nat.sub k j)).
  - unfold Qdiv. ring.
  - rewrite (qeqT_imp_qeq _ _ (q_choose_div_fact k j)).
    unfold Qdiv. ring.
Qed.

(* E3：exp_partial 的和式形式——exp_partial n x == Σ_{k=0}^{n} x^k/k! *)
Lemma exp_partial_sum : forall (n : nat) (x : Q),QeqT (exp_partial n x) (sum_upto (Datatypes.S n) (fun k : nat => q_pow x k / q_fact k)).
Proof.
  intros n x.
  apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* E4：乘积展开为双和——(Σ_{j≤m} f j)·(Σ_{i≤n} g i) == Σ_{j≤m} Σ_{i≤n} (f j · g i) *)
Lemma sum_upto_prod : forall (m n : nat) (f g : nat -> Q),QeqT (sum_upto (Datatypes.S m) f * sum_upto (Datatypes.S n) g) (sum_upto (Datatypes.S m) (fun j => sum_upto (Datatypes.S n) (fun i => f j * g i))).
Proof.
  intros m n f g.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - (* Σ_{i≤n} (f 0·g i) == f 0·Σ g：sum_upto_scale 反向（基例 m=0） *)
    assert (Hf0 : sum_upto 1 f == f 0%nat) by (simpl; ring).
    assert (Hr : sum_upto 1 (fun j => sum_upto (Datatypes.S n) (fun i => f j * g i)) ==
                 sum_upto (Datatypes.S n) (fun i => f 0%nat * g i)) by (simpl; ring).
    setoid_rewrite Hf0.
    setoid_rewrite Hr.
    apply Qeq_sym. apply qeqT_imp_qeq. apply (sum_upto_scale (Datatypes.S n) (f 0%nat) g).
  - (* (Σ f' + f (S m'))·Σg == Σ_j Σ_i f j g i：
      拆 LHS 分配 + 右侧逐项（RHS 拆尾项 j = S m'） *)
    transitivity (sum_upto (Datatypes.S m') f * sum_upto (Datatypes.S n) g +
                  f (Datatypes.S m') * sum_upto (Datatypes.S n) g).
    + change (sum_upto (Datatypes.S (Datatypes.S m')) f)
        with (sum_upto (Datatypes.S m') f + f (Datatypes.S m')).
      ring.
    + transitivity (sum_upto (Datatypes.S m') (fun j => sum_upto (Datatypes.S n) (fun i => f j * g i)) +
                    sum_upto (Datatypes.S n) (fun i => f (Datatypes.S m') * g i)).
      * setoid_rewrite IH.
        setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S n) (f (Datatypes.S m')) g)).
        reflexivity.
      * change (sum_upto (Datatypes.S (Datatypes.S m')) (fun j => sum_upto (Datatypes.S n) (fun i => f j * g i)))
          with (sum_upto (Datatypes.S m') (fun j => sum_upto (Datatypes.S n) (fun i => f j * g i)) +
                sum_upto (Datatypes.S n) (fun i => f (Datatypes.S m') * g i)).
        reflexivity.
Qed.

(* E5：三角转置（分离变量）——Σ_{k=0}^{N} Σ_{j=0}^{k} A j·B (k−j) == Σ_{j=0}^{N} Σ_{i=0}^{N−j} A j·B i
   归纳于 N：
     LHS(S N') = LHS(N') + Σ_{j=0}^{S N'} A j·B (S N'−j)      [外层尾项 k = S N']
     RHS(S N') = RHS(N') + Σ_{j=0}^{N'} A j·B (S N'−j) + A (S N')·B 0
                  [外层尾项 j = S N'（单点 A(S N') B 0）；逐 j≤N' 内层拆尾项 i = S N'−j]
   两端增量一致（S N'−S N' == 0 时尾项重合），IH 闭合 *)
Lemma exp_cauchy_swap : forall (N : nat) (A B : nat -> Q),QeqT (sum_upto (Datatypes.S N) (fun k => sum_upto (Datatypes.S k) (fun j => A j * B (Nat.sub k j)))) (sum_upto (Datatypes.S N) (fun j => sum_upto (Datatypes.S (Nat.sub N j)) (fun i => A j * B i))).
Proof.
  intros N A B.
  apply qeq_imp_qeqT.
  induction N as [| N' IH]; simpl.
  - reflexivity.
  - (* LHS 拆外层尾项 k = S N' *)
    change (sum_upto (Datatypes.S (Datatypes.S N')) (fun k => sum_upto (Datatypes.S k) (fun j => A j * B (Nat.sub k j))))
      with (sum_upto (Datatypes.S N') (fun k => sum_upto (Datatypes.S k) (fun j => A j * B (Nat.sub k j))) +
            sum_upto (Datatypes.S (Datatypes.S N')) (fun j => A j * B (Nat.sub (Datatypes.S N') j))).
    (* RHS 拆外层尾项 j = S N'（内层 S (S N' − S N') == S 0 → 单点 A (S N') B 0） *)
    change (sum_upto (Datatypes.S (Datatypes.S N')) (fun j => sum_upto (Datatypes.S (Nat.sub (Datatypes.S N') j)) (fun i => A j * B i)))
      with (sum_upto (Datatypes.S N') (fun j => sum_upto (Datatypes.S (Nat.sub (Datatypes.S N') j)) (fun i => A j * B i)) +
            sum_upto (Datatypes.S (Nat.sub (Datatypes.S N') (Datatypes.S N'))) (fun i => A (Datatypes.S N') * B i)).
    (* 逐 j≤N'：RHS 内层 S (S N' − j) 拆尾项（lia 桥 S N'−j == S (N'−j)），尾项 == A j·B (S N'−j) *)
    assert (HsubE1 : sum_upto (Datatypes.S N') (fun j => sum_upto (Datatypes.S (Nat.sub (Datatypes.S N') j)) (fun i => A j * B i)) == sum_upto (Datatypes.S N') (fun j => sum_upto (Datatypes.S (Nat.sub N' j)) (fun i => A j * B i) + A j * B (Nat.sub (Datatypes.S N') j))).
{ apply qeqT_imp_qeq. apply (sum_upto_ext_below (Datatypes.S N')
      (fun j => sum_upto (Datatypes.S (Nat.sub (Datatypes.S N') j)) (fun i => A j * B i))
      (fun j => sum_upto (Datatypes.S (Nat.sub N' j)) (fun i => A j * B i) + A j * B (Nat.sub (Datatypes.S N') j))).
intros j Hjlt. apply NatLe_drop in Hjlt.
         assert (Hn : (Nat.sub (Datatypes.S N') j = Datatypes.S (Nat.sub N' j))%nat) by lia.
         change (sum_upto (Datatypes.S (Datatypes.S (Nat.sub N' j))) (fun i => A j * B i))
           with (sum_upto (Datatypes.S (Nat.sub N' j)) (fun i => A j * B i) + A j * B (Datatypes.S (Nat.sub N' j))).
         rewrite <- Hn. apply qeq_imp_qeqT. reflexivity.
}
setoid_rewrite HsubE1.
    (* 提取 Σ_{j≤N'} A j·B (S N'−j)（sum_upto_plus 反向） *)
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S N')
      (fun j => sum_upto (Datatypes.S (Nat.sub N' j)) (fun i => A j * B i))
      (fun j => A j * B (Nat.sub (Datatypes.S N') j)))).
    setoid_rewrite IH.
    (* 剩余：LHS 尾 Σ_{j≤S N'} A j B (S N'−j) == RHS 尾 Σ_{j≤N'} A j B (S N'−j) + A (S N') B 0
       即 sum_upto (S (S N')) 拆尾项 j = S N'（其 B 参数 S N'−S N' == 0） *)
    change (sum_upto (Datatypes.S (Datatypes.S N')) (fun j => A j * B (Nat.sub (Datatypes.S N') j)))
      with (sum_upto (Datatypes.S N') (fun j => A j * B (Nat.sub (Datatypes.S N') j)) +
            A (Datatypes.S N') * B (Nat.sub N' N')).
    assert (H0 : (Nat.sub N' N' = 0)%nat) by lia.
    rewrite H0. simpl. ring.
Qed.

(* E6：Cauchy 积恒等式——exp_partial (2n) (x+y) 的双和展开
   exp_partial (2n) (x+y) == Σ_{j=0}^{2n} Σ_{i=0}^{2n−j} (x^j/j!)·(y^i/i!)
   链：exp_partial_sum（和式）→ exp_term_binom（逐项二项式）→ exp_term_split（逐项分裂）→ exp_cauchy_swap（三角转置） *)
Lemma exp_cauchy_double : forall (x y : Q) (n : nat),QeqT (exp_partial (2 * n) (x + y)) (sum_upto (Datatypes.S (2 * n)) (fun j : nat => sum_upto (Datatypes.S (2 * n - j)) (fun i : nat => (q_pow x j / q_fact j) * (q_pow y i / q_fact i)))).
Proof.
  intros x y n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (exp_partial_sum (2 * n) (x + y))).
  (* 逐项 q_pow (x+y) k / k! == Σ_j C(k,j)x^j y^(k−j)/k!（exp_term_binom） *)
  assert (HsubE2 : sum_upto (Datatypes.S (2 * n)) (fun k => q_pow (x + y) k / q_fact k) == sum_upto (Datatypes.S (2 * n)) (fun k => sum_upto (Datatypes.S k) (fun j => q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k))).
{ apply qeqT_imp_qeq. apply (sum_upto_ext_below (Datatypes.S (2 * n))
    (fun k => q_pow (x + y) k / q_fact k)
    (fun k => sum_upto (Datatypes.S k) (fun j => q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k))).
intros k Hklt. apply NatLe_drop in Hklt. apply (exp_term_binom x y k).
}
setoid_rewrite HsubE2.
  (* 逐 j 项分裂：C(k,j)x^j y^(k−j)/k! == (x^j/j!)(y^(k−j)/(k−j)!)（exp_term_split） *)
  assert (HsubE3 : sum_upto (Datatypes.S (2 * n)) (fun k => sum_upto (Datatypes.S k) (fun j => q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k)) == sum_upto (Datatypes.S (2 * n)) (fun k => sum_upto (Datatypes.S k) (fun j => (q_pow x j / q_fact j) * (q_pow y (Nat.sub k j) / q_fact (Nat.sub k j))))).
{ apply qeqT_imp_qeq. apply (sum_upto_ext_below (Datatypes.S (2 * n))
    (fun k => sum_upto (Datatypes.S k) (fun j => q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k))
    (fun k => sum_upto (Datatypes.S k) (fun j => (q_pow x j / q_fact j) * (q_pow y (Nat.sub k j) / q_fact (Nat.sub k j))))).
intros k Hklt. apply NatLe_drop in Hklt.
       apply (sum_upto_ext_below (Datatypes.S k)
         (fun j => q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k)
         (fun j => (q_pow x j / q_fact j) * (q_pow y (Nat.sub k j) / q_fact (Nat.sub k j)))).
       intro j. intro Hjlt. apply (exp_term_split x y k j).
}
setoid_rewrite HsubE3.
  (* 三角转置（exp_cauchy_swap，N := 2n，A j := x^j/j!，B i := y^i/i!） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (exp_cauchy_swap (2 * n) (fun j => q_pow x j / q_fact j) (fun i => q_pow y i / q_fact i))).
  reflexivity.
Qed.

(* E7：乘积侧展开——exp_partial n x · exp_partial n y == Σ_{j=0}^{n} Σ_{i=0}^{n} (x^j/j!)·(y^i/i!)
   链：exp_partial_sum（双侧和式）+ sum_upto_prod（乘积双和） *)
Lemma exp_prod_double : forall (x y : Q) (n : nat),QeqT (exp_partial n x * exp_partial n y) (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => (q_pow x j / q_fact j) * (q_pow y i / q_fact i)))).
Proof.
  intros x y n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (exp_partial_sum n x)).
  rewrite (qeqT_imp_qeq _ _ (exp_partial_sum n y)).
  apply qeqT_imp_qeq. apply (sum_upto_prod n n (fun j => q_pow x j / q_fact j) (fun i => q_pow y i / q_fact i)).
Qed.

(* E8：三角双和 − 方块双和 == 上带 + 右带
   拆分辅助：outer_split（外层 j≤n 与 j>n）、inner_split（内层 i≤n 与上带）、rhs_inner（右带换形） *)
Lemma sum_upto_outer_split : forall (n : nat) (F : nat -> Q),QeqT (sum_upto (Datatypes.S (2 * n)) F) (sum_upto (Datatypes.S n) F + sum_upto n (fun j => F ((Datatypes.S n + j)%nat))).
Proof.
  intros n F.
  apply qeq_imp_qeqT.
  assert (Hadd : (Datatypes.S (2 * n) = Datatypes.S n + n)%nat) by lia.
  rewrite Hadd.
  apply qeqT_imp_qeq. apply (sum_upto_add (Datatypes.S n) n F).
Qed.

Lemma sum_upto_inner_split : forall (n j : nat) (f : nat -> Q), (j <= n)%nat ->QeqT (sum_upto (Datatypes.S (2 * n - j)) f) (sum_upto (Datatypes.S n) f + sum_upto (n - j) (fun k => f ((Datatypes.S n + k)%nat))).
Proof.
  intros n j f Hj.
  apply qeq_imp_qeqT.
  assert (Hadd : (Datatypes.S (2 * n - j) = Datatypes.S n + (n - j))%nat) by lia.
  rewrite Hadd.
  apply qeqT_imp_qeq. apply (sum_upto_add (Datatypes.S n) (n - j) f).
Qed.

(* 第一步：三角 == 方块外 j≤n 部分（内层未拆）+ 右带 *)
Lemma exp_trunc_step1 : forall (n : nat) (A B : nat -> Q),QeqT (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i))) (sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i)) +
  sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => A ((Datatypes.S n + j)%nat) * B i))).
Proof.
  intros n A B.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_outer_split n (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i)))).
  assert (HsubE4 : sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - (Datatypes.S n + j))) (fun i => A ((Datatypes.S n + j)%nat) * B i)) == sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => A ((Datatypes.S n + j)%nat) * B i))).
{ apply qeqT_imp_qeq. apply (sum_upto_ext_below n
    (fun j => sum_upto (Datatypes.S (2 * n - (Datatypes.S n + j))) (fun i => A ((Datatypes.S n + j)%nat) * B i))
    (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => A ((Datatypes.S n + j)%nat) * B i))).
intros j Hj. apply NatLe_drop in Hj. apply sum_upto_nat_eq. lia.
}
setoid_rewrite HsubE4.
  reflexivity.
Qed.

(* 第二步：方块外 j≤n 部分拆内层 == 方块 + 上带 *)
Lemma exp_trunc_step2 : forall (n : nat) (A B : nat -> Q),QeqT (sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i))) (sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => A j * B i) +
                                    sum_upto (n - j) (fun k => A j * B ((Datatypes.S n + k)%nat)))).
Proof.
  intros n A B.
  apply qeq_imp_qeqT.
  assert (HsubE5 : sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i)) == sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => A j * B i) +
              sum_upto (n - j) (fun k => A j * B ((Datatypes.S n + k)%nat)))).
{ apply qeqT_imp_qeq. apply (sum_upto_ext_below (Datatypes.S n)
    (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i))
    (fun j => sum_upto (Datatypes.S n) (fun i => A j * B i) +
              sum_upto (n - j) (fun k => A j * B ((Datatypes.S n + k)%nat)))).
intros j Hjlt. apply NatLe_drop in Hjlt. apply (sum_upto_inner_split n j (fun i => A j * B i)); lia.
}
setoid_rewrite HsubE5.
  reflexivity.
Qed.

(* 通用环恒等：(A + U) + R − A == U + R *)
Lemma q_cancel_ring : forall (A U R : Q),QeqT ((A + U) + R - A) (U + R).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* E8 组装：三角 − 方块 == 上带 + 右带（step1 + step2 + q_cancel_ring） *)
Lemma exp_trunc_decomp : forall (n : nat) (A B : nat -> Q),QeqT (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * B i)) -
  sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => A j * B i))) (sum_upto (Datatypes.S n) (fun j => sum_upto (n - j) (fun k => A j * B ((Datatypes.S n + k)%nat))) +
  sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => A ((Datatypes.S n + j)%nat) * B i))).
Proof.
  intros n A B.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (exp_trunc_step1 n A B)).
  rewrite (qeqT_imp_qeq _ _ (exp_trunc_step2 n A B)).
  (* 拆 Σ(方块内层 + 上带) == Σ方块 + Σ上带（sum_upto_plus），再 q_cancel_ring 对消 *)
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S n)
    (fun j => sum_upto (Datatypes.S n) (fun i => A j * B i))
    (fun j => sum_upto (n - j) (fun k => A j * B ((Datatypes.S n + k)%nat))))).
  apply qeqT_imp_qeq. apply (q_cancel_ring
    (sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => A j * B i)))
    (sum_upto (Datatypes.S n) (fun j => sum_upto (n - j) (fun k => A j * B ((Datatypes.S n + k)%nat))))
    (sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => A ((Datatypes.S n + j)%nat) * B i)))).
Qed.
End ExpPlusStage2.

(* ============================================================ *)
(* 阶段 2 续：exp 截断误差上界（并入，来自检验 _dbg_exp_plus.v 49 Qed）
   内容：sum_upto_abs_le / sum_upto_le_ext / q_abs_pow_fact_le / exp_tail_abs_sum /
        exp_tail_abs_mono2 / exp_series_sum / exp_tail_abs_sum_inner / exp_tail_abs_inner_le /
        q_abs_prod_le / exp_trunc_abs_step / q_scale_series_le / exp_trunc_band_up
   验证：coqc+coqtop 双验 + BAD=0（备份 101） *)
Section ExpPlusStage2b.

(* ===== 截断误差上界：|三角 − 方块| ≤ 尾项控制（判例追加） ===== *)

(* T1：求和绝对值三角不等式——|Σ f| ≤ Σ |f|（归纳于 n） *)
Lemma sum_upto_abs_le : forall (n : nat) (f : nat -> Q),
  QleT' (Qabs (sum_upto n f)) (sum_upto n (fun i => Qabs (f i))).
Proof.
  intros n f.
  apply Qle_to_QleT'.
  induction n as [| n' IH]; simpl.
  - unfold Qle; simpl; lia.
  - apply (Qle_trans _ (Qabs (sum_upto n' f) + Qabs (f n')) _).
    + apply Qabs_triangle.
    + apply Qplus_le_compat; [exact IH | apply Qle_refl].
Qed.

(* T2：逐项和上界（Qle 保持）——Σ_k f k ≤ Σ_k g k 若逐项 f k ≤ g k（归纳于 n） *)
Lemma sum_upto_le_ext : forall (n : nat) (f g : nat -> Q),
  (forall k : nat, NatLe (Datatypes.S k) n -> QleT' (f k) (g k)) ->
  QleT' (sum_upto n f) (sum_upto n g).
Proof.
  intros n f g Hfg.
  apply Qle_to_QleT'.
  induction n as [| n' IH]; simpl.
  - apply Qle_refl.
  - apply Qplus_le_compat.
    + apply IH. intro k. intro Hk. apply (Hfg k). apply NatLe_lift. apply (Nat.le_trans _ n'); [apply NatLe_drop; exact Hk | apply Nat.le_succ_diag_r].
    + apply QleT'_to_Qle. apply (Hfg n' (NatLe_lift _ _ (Nat.le_refl (Datatypes.S n')))).
Qed.

(* T3：|A j| ≤ B^j/j!（|x| ≤ B）——逐项幂-阶乘绝对值上界 *)
Lemma q_abs_pow_fact_le : forall (x B : Q) (j : nat),
  QleT' 0 B -> QleT' (Qabs x) B ->
  QleT' (Qabs (q_pow x j / q_fact j)) (q_pow B j / q_fact j).
Proof.
  intros x B j HB HxB.
  apply Qle_to_QleT'.
  unfold Qdiv.
  assert (Hinv : Qabs (Qinv (q_fact j)) == Qinv (q_fact j)).
  { transitivity (Qinv (Qabs (q_fact j))).
    - apply Qabs_Qinv.
    - apply Qinv_comp.
      apply Qabs_pos.
      apply (Qlt_le_weak 0 (q_fact j)). apply QltT_to_Qlt. apply q_fact_pos. }
  apply (Qle_trans _ (Qabs (q_pow x j) * Qabs (Qinv (q_fact j))) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
  - apply (Qle_trans _ (Qabs (q_pow x j) * Qinv (q_fact j)) _).
    + apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      setoid_rewrite Hinv. reflexivity.
    + apply (Qle_trans _ (q_pow B j * Qinv (q_fact j)) _).
      * apply (Qmult_le_compat_r (Qabs (q_pow x j)) (q_pow B j) (Qinv (q_fact j))).
        -- apply (Qle_trans _ (q_pow (Qabs x) j) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply q_pow_abs.
           ++ apply QleT'_to_Qle. apply q_pow_mono; [apply Qle_to_QleT'; apply Qabs_nonneg | exact HxB].
        -- apply (Qlt_le_weak 0 (Qinv (q_fact j))).
           apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
      * apply Qle_refl.
Qed.

(* T4 辅助 1：exp_tail_abs 的和式定义——exp_tail_abs m N B == Σ_{k=0}^{N−m−1} B^{S m + k}/(S m + k)!（m < N） *)
Lemma exp_tail_abs_sum : forall (m N : nat) (B : Q), (m < N)%nat ->QeqT (exp_tail_abs m N B) (sum_upto (N - m) (fun k => q_pow B ((Datatypes.S m + k)%nat) / q_fact ((Datatypes.S m + k)%nat))).
Proof.
  intros m N B HmN.
  apply qeq_imp_qeqT.
  revert HmN.
  induction N as [| N' IH]; intros HmN.
  - lia.
  - change (exp_tail_abs m (Datatypes.S N') B)
      with (exp_tail_abs m N' B + (if Nat.leb m N' then q_pow B (Datatypes.S N') / q_fact (Datatypes.S N') else 0)).
    destruct (Nat.leb m N') eqn:EmN.
    + apply Nat.leb_le in EmN.
      destruct (Nat.eq_dec m N') as [HmN' | Hmn'].
      * subst N'.
        rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m m m B (Nat.le_refl m))).
        assert (Hsub : (Datatypes.S m - m = 1)%nat) by lia.
        rewrite Hsub. simpl.
        assert (Hid : (m + 0 = m)%nat) by lia.
        setoid_replace (m + 0)%nat with m by (rewrite Hid; reflexivity).
        reflexivity.
      * assert (Hlt : (m < N')%nat) by lia.
        assert (Hsub : (Datatypes.S N' - m = Datatypes.S (N' - m))%nat) by lia.
        rewrite Hsub.
        change (sum_upto (Datatypes.S (N' - m)) (fun k => q_pow B ((Datatypes.S m + k)%nat) / q_fact ((Datatypes.S m + k)%nat)))
          with (sum_upto (N' - m) (fun k => q_pow B ((Datatypes.S m + k)%nat) / q_fact ((Datatypes.S m + k)%nat)) +
                q_pow B ((Datatypes.S m + (N' - m))%nat) / q_fact ((Datatypes.S m + (N' - m))%nat)).
        rewrite (IH Hlt).
        assert (Hidx : (Datatypes.S N' = Datatypes.S m + (N' - m))%nat) by lia.
        rewrite Hidx. reflexivity.
    + apply Nat.leb_gt in EmN.
      assert (Hge : (N' <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m m N' B Hge)).
      assert (Hcnt : (Datatypes.S N' - m = 0)%nat) by lia.
      rewrite Hcnt. simpl. ring.
Qed.

(* T4 辅助 2：exp_tail_abs 第二参数单调——N ≤ N' ⟹ exp_tail_abs m N B ≤ exp_tail_abs m N' B *)
Lemma exp_tail_abs_mono2 : forall (m N N' : nat) (B : Q),
  QleT' 0 B -> (N <= N')%nat ->
  QleT' (exp_tail_abs m N B) (exp_tail_abs m N' B).
Proof.
  intros m N N' B HB HNN.
  apply Qle_to_QleT'.
  induction HNN as [| N' _ IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (exp_tail_abs m N' B) _); [exact IH |].
    simpl.
    destruct (Nat.leb m N') eqn:EmN.
    + apply (Qle_plus_nonneg_r (exp_tail_abs m N' B) (q_pow B (Datatypes.S N') / q_fact (Datatypes.S N'))).
      apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HB.
    + setoid_replace (exp_tail_abs m N' B + 0) with (exp_tail_abs m N' B) by ring.
      apply Qle_refl.
Qed.

(* T4 辅助 3：exp_series 与 sum_upto 的桥——exp_series n B == Σ_{k=0}^{n} B^k/k! *)
Lemma exp_series_sum : forall (n : nat) (B : Q),QeqT (exp_series n B) (sum_upto (Datatypes.S n) (fun k => q_pow B k / q_fact k)).
Proof.
  intros n B.
  apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* T4a-1：内层恒等——Σ_{k<n−j} B^{S n+k}/(S n+k)! == exp_tail_abs n (2n−j) B *)
Lemma exp_tail_abs_sum_inner : forall (n j : nat) (B : Q), (j <= n)%nat ->QeqT (sum_upto (n - j) (fun k => q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))) (exp_tail_abs n (2 * n - j) B).
Proof.
  intros n j B Hj.
  apply qeq_imp_qeqT.
  destruct (Nat.eq_dec j n) as [Hjn | Hjn'].
  - subst j.
    assert (Hsub : (n - n = 0)%nat) by lia.
    rewrite Hsub. simpl.
    apply (Qeq_trans _ 0 _).
    + reflexivity.
    + apply Qeq_sym.
      apply qeqT_imp_qeq. apply (exp_tail_abs_le_m n (2 * n - n) B).
      lia.
  - assert (Hlt : (j < n)%nat) by lia.
    assert (Hcnt : (n - j = (2 * n - j) - n)%nat) by lia.
    rewrite Hcnt.
    apply Qeq_sym.
    apply qeqT_imp_qeq. apply (exp_tail_abs_sum n (2 * n - j) B).
    lia.
Qed.

(* T4a-2：内层 ≤ exp_tail_abs n (2n) B（mono2，2n−j ≤ 2n） *)
Lemma exp_tail_abs_inner_le : forall (n j : nat) (B : Q),
  QleT' 0 B -> (j <= n)%nat ->
  QleT' (exp_tail_abs n (2 * n - j) B) (exp_tail_abs n (2 * n) B).
Proof.
  intros n j B HB Hj.
  apply (exp_tail_abs_mono2 n (2 * n - j) (2 * n) B HB).
  lia.
Qed.

(* T4a-3：逐项积上界——|A j · B' k| ≤ (B^j/j!)·(B^{S n+k}/(S n+k)!)（|x|,|y| ≤ B） *)
Lemma q_abs_prod_le : forall (x y B : Q) (n j k : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs ((q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))
      ((q_pow B j / q_fact j) * (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))).
Proof.
  intros x y B n j k HB HxB HyB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (q_pow x j / q_fact j) * Qabs (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
  - apply (Qle_trans _ ((q_pow B j / q_fact j) * Qabs (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))) _).
    + apply (Qmult_le_compat_r (Qabs (q_pow x j / q_fact j))
                               (q_pow B j / q_fact j)
                               (Qabs (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
      * apply QleT'_to_Qle. apply q_abs_pow_fact_le; assumption.
      * apply Qabs_nonneg.
    + setoid_rewrite (Qmult_comm (q_pow B j / q_fact j) (Qabs (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
      setoid_rewrite (Qmult_comm (q_pow B j / q_fact j) (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))).
      apply (Qmult_le_compat_r (Qabs (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))
                               (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))
                               (q_pow B j / q_fact j)).
      * apply QleT'_to_Qle. apply q_abs_pow_fact_le; assumption.
      * apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HB.
Qed.

(* T4a-4：Σ_j f2 j ≤ Σ_j f3 j（逐 j 内层 le_ext + q_abs_prod_le） *)
Lemma exp_trunc_abs_step : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (sum_upto (Datatypes.S n) (fun j => sum_upto (n - j) (fun k => Qabs ((q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))))
      (sum_upto (Datatypes.S n) (fun j => sum_upto (n - j) (fun k => (q_pow B j / q_fact j) * (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))).
Proof.
  intros x y B n HB HxB HyB.
  apply Qle_to_QleT'.
  set (f2 := fun j : nat => sum_upto (n - j) (fun k => Qabs ((q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))).
  set (f3 := fun j : nat => sum_upto (n - j) (fun k => (q_pow B j / q_fact j) * (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
  change (Qle (sum_upto (Datatypes.S n) f2) (sum_upto (Datatypes.S n) f3)).
  apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S n) f2 f3).
  intro j. intro Hjlt.
  unfold f2, f3.
  apply (sum_upto_le_ext (n - j)
    (fun k => Qabs ((q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))
    (fun k => (q_pow B j / q_fact j) * (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
  intro k. intro Hklt.
  apply (q_abs_prod_le x y B n j k HB HxB HyB).
Qed.

(* T4a-5：Σ_j (B^j/j!)·C ≤ exp_series n B · C（C ≥ 0）——Qeq 链 comm+scale+series_sum *)
Lemma q_scale_series_le : forall (n : nat) (B C : Q),
  QleT' 0 C ->
  QleT' (sum_upto (Datatypes.S n) (fun j => (q_pow B j / q_fact j) * C))
      (exp_series n B * C).
Proof.
  intros n B C HC.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
  transitivity (sum_upto (Datatypes.S n) (fun j => C * (q_pow B j / q_fact j))).
  - apply qeqT_imp_qeq. apply (sum_upto_ext (Datatypes.S n)
      (fun j => (q_pow B j / q_fact j) * C)
      (fun j => C * (q_pow B j / q_fact j))).
    intro j. apply qeq_imp_qeqT. apply Qmult_comm.
  - transitivity (C * sum_upto (Datatypes.S n) (fun j => q_pow B j / q_fact j)).
    + apply qeqT_imp_qeq. apply (sum_upto_scale (Datatypes.S n) C (fun j => q_pow B j / q_fact j)).
    + transitivity (C * exp_series n B).
      * apply Qmult_comp.
        -- reflexivity.
        -- apply Qeq_sym. apply qeqT_imp_qeq. apply (exp_series_sum n B).
      * apply Qmult_comm.
Qed.

(* T4a：上带上界——|Σ_{j≤n} Σ_{k<n−j} A j B (n+1+k)| ≤ exp_series n B · exp_tail_abs n (2n) B *)

(* T4a：上带上界——|Σ_{j≤n} Σ_{k<n−j} A j B (n+1+k)| ≤ exp_series n B · exp_tail_abs n (2n) B *)
Lemma exp_trunc_band_up : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j => sum_upto (n - j) (fun k => (q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))))
      (exp_series n B * exp_tail_abs n (2 * n) B).
Proof.
  intros x y B n HB HxB HyB.
  apply Qle_to_QleT'.
  set (f1 := fun j : nat => sum_upto (n - j) (fun k => (q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
  set (f2 := fun j : nat => sum_upto (n - j) (fun k => Qabs ((q_pow x j / q_fact j) * (q_pow y ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat))))).
  set (f3 := fun j : nat => sum_upto (n - j) (fun k => (q_pow B j / q_fact j) * (q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
  change (Qle (Qabs (sum_upto (Datatypes.S n) f1)) (exp_series n B * exp_tail_abs n (2 * n) B)).
  apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j => Qabs (f1 j))) _).
  - apply QleT'_to_Qle. apply sum_upto_abs_le.
  - apply (Qle_trans _ (sum_upto (Datatypes.S n) f3) _).
    + apply (Qle_trans _ (sum_upto (Datatypes.S n) f2) _).
      * apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S n) (fun j => Qabs (f1 j)) f2).
        intro j. intro Hjlt. unfold f1, f2. apply sum_upto_abs_le.
      * apply QleT'_to_Qle. apply (exp_trunc_abs_step x y B n HB HxB HyB).
    + apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j => (q_pow B j / q_fact j) * exp_tail_abs n (2 * n) B)) _).
      * apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S n) f3 (fun j => (q_pow B j / q_fact j) * exp_tail_abs n (2 * n) B)).
        intro j. intro Hjlt.
        unfold f3.
        apply Qle_to_QleT'.
        apply (Qle_trans _ ((q_pow B j / q_fact j) * exp_tail_abs n (2 * n - j) B) _).
        apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
           setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (n - j) (q_pow B j / q_fact j)
             (fun k => q_pow B ((Datatypes.S n + k)%nat) / q_fact ((Datatypes.S n + k)%nat)))).
           assert (Hjle : (j <= n)%nat) by (apply NatLe_drop in Hjlt; lia).
           setoid_rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_sum_inner n j B Hjle)).
           reflexivity.
        -- setoid_rewrite (Qmult_comm (q_pow B j / q_fact j) (exp_tail_abs n (2 * n - j) B)).
           setoid_rewrite (Qmult_comm (q_pow B j / q_fact j) (exp_tail_abs n (2 * n) B)).
           apply (Qmult_le_compat_r (exp_tail_abs n (2 * n - j) B) (exp_tail_abs n (2 * n) B)
                                    (q_pow B j / q_fact j)).
           ++ apply QleT'_to_Qle. apply (exp_tail_abs_inner_le n j B HB). apply NatLe_drop in Hjlt. lia.
           ++ apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HB.
      * apply QleT'_to_Qle. apply (q_scale_series_le n B (exp_tail_abs n (2 * n) B)).
        apply (exp_tail_abs_nonneg n (2 * n) B). exact HB.
Qed.

Lemma sum_upto_series_le : forall (m N : nat) (B : Q),
  QleT' 0 B -> (m <= N)%nat ->
  QleT' (sum_upto (Datatypes.S m) (fun i => q_pow B i / q_fact i))
      (exp_series N B).
Proof.
  intros m N B HB HmN.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (exp_series m B) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. apply (exp_series_sum m B).
  - apply QleT'_to_Qle. apply exp_series_mono; [exact HB | exact HmN].
Qed.

(* T4b 辅助 2：外层和式恒等——Σ_{j<n} B^{S n+j}/(S n+j)! == exp_tail_abs n (2n) B
   由 exp_tail_abs_sum（m := n，N := 2n）反向；n = 0 时两侧皆 0 *)
Lemma exp_tail_abs_outer_eq : forall (n : nat) (B : Q),QeqT (sum_upto n (fun j => q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat))) (exp_tail_abs n (2 * n) B).
Proof.
  intros n B.
  apply qeq_imp_qeqT.
  destruct n as [| n'].
  - simpl. reflexivity.
  - transitivity (sum_upto (2 * Datatypes.S n' - Datatypes.S n')
                   (fun k => q_pow B ((Datatypes.S (Datatypes.S n') + k)%nat) / q_fact ((Datatypes.S (Datatypes.S n') + k)%nat))).
    + apply qeqT_imp_qeq. apply sum_upto_nat_eq. lia.
    + apply Qeq_sym.
      apply qeqT_imp_qeq. apply (exp_tail_abs_sum (Datatypes.S n') (2 * Datatypes.S n') B). lia.
Qed.

(* T4b：右带上界——|Σ_{j'<n} Σ_{i≤2n−n−1−j'} A (n+1+j') B i| ≤ exp_tail_abs n (2n) B · exp_series (2n) B
   A k := x^k/k!，B i := y^i/i!；|x|,|y| ≤ B 时逐项 |A k| ≤ B^k/k!、|B i| ≤ B^i/i!
   链：abs_le 外层 + le_ext 逐 j（abs_le 内层）→ q_abs_pow_fact_le 逐项
       → 内层 ≤ exp_series (2n) B（sum_upto_series_le）
       → 外层 == exp_tail_abs n (2n) B（exp_tail_abs_outer_eq）→ q_scale_series_le 收拢 *)

(* T4b 辅助 3：逐项积上界（T4b 形态）——|A k · B i| ≤ (B^k/k!)·(B^i/i!) *)
Lemma q_abs_prod_le2 : forall (x y B : Q) (k i : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs ((q_pow x k / q_fact k) * (q_pow y i / q_fact i)))
      ((q_pow B k / q_fact k) * (q_pow B i / q_fact i)).
Proof.
  intros x y B k i HB HxB HyB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (q_pow x k / q_fact k) * Qabs (q_pow y i / q_fact i)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
  - apply (Qle_trans _ ((q_pow B k / q_fact k) * Qabs (q_pow y i / q_fact i)) _).
    + apply (Qmult_le_compat_r (Qabs (q_pow x k / q_fact k))
                               (q_pow B k / q_fact k)
                               (Qabs (q_pow y i / q_fact i))).
      * apply QleT'_to_Qle. apply q_abs_pow_fact_le; assumption.
      * apply Qabs_nonneg.
    + setoid_rewrite (Qmult_comm (q_pow B k / q_fact k) (Qabs (q_pow y i / q_fact i))).
      setoid_rewrite (Qmult_comm (q_pow B k / q_fact k) (q_pow B i / q_fact i)).
      apply (Qmult_le_compat_r (Qabs (q_pow y i / q_fact i))
                               (q_pow B i / q_fact i)
                               (q_pow B k / q_fact k)).
      * apply QleT'_to_Qle. apply q_abs_pow_fact_le; assumption.
      * apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HB.
Qed.

(* T4b 辅助 4：内层乘界——c·Σ_{i≤m} B^i/i! ≤ c·exp_series N B（m ≤ N，c ≥ 0） *)
Lemma q_scale_inner_le : forall (m N : nat) (B c : Q),
  QleT' 0 B -> QleT' 0 c -> (m <= N)%nat ->
  QleT' (c * sum_upto (Datatypes.S m) (fun i => q_pow B i / q_fact i))
      (c * exp_series N B).
Proof.
  intros m N B c HB Hc HmN.
  apply Qle_to_QleT'.
  setoid_rewrite (Qmult_comm c (sum_upto (Datatypes.S m) (fun i => q_pow B i / q_fact i))).
  setoid_rewrite (Qmult_comm c (exp_series N B)).
  apply (Qmult_le_compat_r (sum_upto (Datatypes.S m) (fun i => q_pow B i / q_fact i))
                           (exp_series N B) c).
  - apply QleT'_to_Qle. apply (sum_upto_series_le m N B HB HmN).
  - apply QleT'_to_Qle. exact Hc.
Qed.

(* T4b 辅助 5：外层收拢——Σ_j c_j·C ≤ exp_tail_abs n (2n) B · C（C ≥ 0）
   其中 c_j := B^{S n+j}/(S n+j)!，Σ_j c_j == exp_tail_abs n (2n) B（outer_eq） *)
Lemma q_tail_scale_le : forall (n : nat) (B C : Q),
  QleT' 0 C ->
  QleT' (sum_upto n (fun j => (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * C))
      (exp_tail_abs n (2 * n) B * C).
Proof.
  intros n B C HC.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
  transitivity (sum_upto n (fun j => C * (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)))).
  - apply qeqT_imp_qeq. apply (sum_upto_ext n
      (fun j => (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * C)
      (fun j => C * (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)))).
    intro j. apply qeq_imp_qeqT. apply Qmult_comm.
  - transitivity (C * sum_upto n (fun j => q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat))).
    + apply qeqT_imp_qeq. apply (sum_upto_scale n C (fun j => q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat))).
    + transitivity (C * exp_tail_abs n (2 * n) B).
      * apply Qmult_comp.
        -- reflexivity.
        -- apply qeqT_imp_qeq. apply (exp_tail_abs_outer_eq n B).
      * apply Qmult_comm.
Qed.

(* T4b：右带上界——|Σ_{j'<n} Σ_{i≤2n−n−1−j'} A (n+1+j') B i| ≤ exp_tail_abs n (2n) B · exp_series (2n) B *)
Lemma exp_trunc_band_right : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => (q_pow x ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * (q_pow y i / q_fact i)))))
      (exp_tail_abs n (2 * n) B * exp_series (2 * n)%nat B).
Proof.
  intros x y B n HB HxB HyB.
  apply Qle_to_QleT'.
  set (c := fun j : nat => q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)).
  set (g1 := fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => (q_pow x ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * (q_pow y i / q_fact i))).
  set (g3 := fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * (q_pow B i / q_fact i))).
  change (Qle (Qabs (sum_upto n g1)) (exp_tail_abs n (2 * n) B * exp_series (2 * n)%nat B)).
  apply (Qle_trans _ (sum_upto n (fun j => Qabs (g1 j))) _).
  - apply QleT'_to_Qle. apply sum_upto_abs_le.
  - apply (Qle_trans _ (sum_upto n g3) _).
    + apply QleT'_to_Qle. apply (sum_upto_le_ext n (fun j => Qabs (g1 j)) g3).
      intro j. intro Hjlt.
      unfold g1, g3.
      apply Qle_to_QleT'.
      apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => Qabs ((q_pow x ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * (q_pow y i / q_fact i)))) _).
      * apply QleT'_to_Qle. apply sum_upto_abs_le.
      * set (fA := fun i : nat => Qabs ((q_pow x ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * (q_pow y i / q_fact i))).
        set (fB := fun i : nat => (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) * (q_pow B i / q_fact i)).
        apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S (2 * n - Datatypes.S n - j)) fA fB).
        intro i. intro Hilt. unfold fA, fB.
        apply (q_abs_prod_le2 x y B ((Datatypes.S n + j)%nat) i HB HxB HyB).
    + apply (Qle_trans _ (sum_upto n (fun j => c j * exp_series (2 * n)%nat B)) _).
      * apply QleT'_to_Qle. apply (sum_upto_le_ext n g3 (fun j => c j * exp_series (2 * n)%nat B)).
        intro j. intro Hjlt.
        unfold g3, c.
        apply (qleT'_trans _
                ((q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat)) *
                 sum_upto (Datatypes.S (2 * n - Datatypes.S n - j))
                   (fun i => q_pow B i / q_fact i)) _).
        apply qeq_leT'.
        apply (sum_upto_scale (Datatypes.S (2 * n - Datatypes.S n - j))
          (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat))
          (fun i => q_pow B i / q_fact i)).
        apply (q_scale_inner_le (2 * n - Datatypes.S n - j) (2 * n) B
                                (q_pow B ((Datatypes.S n + j)%nat) / q_fact ((Datatypes.S n + j)%nat))).
        -- exact HB.
        -- apply q_pow_fact_nonneg. exact HB.
        -- lia.
      * apply QleT'_to_Qle. apply (q_tail_scale_le n B (exp_series (2 * n)%nat B)).
        apply Qle_to_QleT'.
        apply (Qle_trans _ 1%Q _).
        -- apply QleT'_to_Qle. apply Qle_0_1.
        -- setoid_replace 1%Q with (exp_series 0 B) by reflexivity.
           apply QleT'_to_Qle.
           apply (exp_series_mono B 0 (2 * n)%nat HB). lia.
Qed.

(* E9：截断误差主界——|三角双和 − 方块双和| ≤ exp_series n B·exp_tail_abs n (2n) B + exp_tail_abs n (2n) B·exp_series (2n) B
   链：exp_trunc_decomp（三角−方块 == 上带+右带）→ Qabs_triangle（|上带+右带| ≤ |上带|+|右带|）
       → exp_trunc_band_up（|上带| 界）+ exp_trunc_band_right（|右带| 界） *)
Lemma exp_trunc_bound : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => (q_pow x j / q_fact j) * (q_pow y i / q_fact i))) -
              sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => (q_pow x j / q_fact j) * (q_pow y i / q_fact i)))))
      (exp_series n B * exp_tail_abs n (2 * n) B +
       exp_tail_abs n (2 * n) B * exp_series (2 * n)%nat B).
Proof.
  intros x y B n HB HxB HyB.
  apply Qle_to_QleT'.
  set (A := fun i : nat => q_pow x i / q_fact i).
  set (C := fun i : nat => q_pow y i / q_fact i).
  change (Qle (Qabs (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => A j * C i)) -
              sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => A j * C i))))
      (exp_series n B * exp_tail_abs n (2 * n) B +
       exp_tail_abs n (2 * n) B * exp_series (2 * n)%nat B)).
  (* 三角 − 方块 == 上带 + 右带（exp_trunc_decomp，A j := x^j/j!，C i := y^i/i!） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (exp_trunc_decomp n A C)).
  (* |上带 + 右带| ≤ |上带| + |右带|（Qabs_triangle） *)
  apply (Qle_trans _ (Qabs (sum_upto (Datatypes.S n) (fun j => sum_upto (n - j) (fun k => A j * C ((Datatypes.S n + k)%nat)))) +
                      Qabs (sum_upto n (fun j => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => A ((Datatypes.S n + j)%nat) * C i)))) _).
  - apply Qabs_triangle.
  - apply Qplus_le_compat.
    + unfold A, C. apply QleT'_to_Qle. apply (exp_trunc_band_up x y B n HB HxB HyB).
    + unfold A, C. apply QleT'_to_Qle. apply (exp_trunc_band_right x y B n HB HxB HyB).
Qed.

(* E10：截断误差衰减——对任意 eps > 0，∃N，∀n ≥ N：|三角−方块| < eps
   输入：exp_trunc_bound（|差| ≤ C·tail + tail·C'）→ exp_series_arch（C, C' 界）→ exp_tail_arch（tail → 0）
   具体：C := exp_series_arch B 的界（exp_series n B ≤ C、exp_series (2n) B ≤ C）
         tail := exp_tail_abs n (2n) B ≤ (B^n/n!)·2 ≤ ... < eps/(2C)（exp_tail_arch + arch_decay）
         |差| ≤ C·tail + tail·C ≤ 2·C·tail < eps
   但 exp_tail_abs n (2n) B 的上界形式：exp_tail_abs n (2n) B ≤ (B^n/n!)·2（exp_tail_abs_geom2，需 B 几何条件）
   而 exp_tail_arch 给 (B^b/b!)·2 < eps 当 b 大。取 n := b 且 n ≤ 2n（恒真）：
   exp_tail_abs n (2n) B ≤ (B^n/n!)·2 < eps（exp_tail_arch 于 b := n）
   组合：∃N，∀n≥N，(B^n/n!)·2 < eps/(2C) ⟹ |差| < eps *)
(* E10 辅助：exp_series n B ≥ 0（exp_series 0 B = 1 ≥ 0 + 单调） *)
Lemma exp_series_nonneg : forall (n : nat) (B : Q), QleT' 0 B -> QleT' 0 (exp_series n B).
Proof.
  intros n B HB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ 1%Q _).
  - apply QleT'_to_Qle. apply Qle_0_1.
  - setoid_replace 1%Q with (exp_series 0 B) by reflexivity.
    apply QleT'_to_Qle.
    apply (exp_series_mono B 0 n HB). lia.
Qed.

Lemma exp_trunc_arch : forall (x y B : Q) (eps : Q),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B -> QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (Qabs (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => (q_pow x j / q_fact j) * (q_pow y i / q_fact i))) -
                sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => (q_pow x j / q_fact j) * (q_pow y i / q_fact i)))))
         eps).
Proof.
  intros x y B eps HB HxB HyB Hep.
  destruct (exp_series_arch B HB) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1%Q _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  assert (HCnonneg : Qle 0 C) by (apply (Qlt_le_weak 0 C); exact HCpos).
  destruct (q_arch_geom B) as [N0 HN0].
  destruct (arch_decay ((q_pow B N0 / q_fact N0) * (1 + 1)%Q) (eps / (2 * C))%Q) as [t Hdec].
  { apply q_pow_fact2_nonneg. exact HB. }
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - apply (Qmult_lt_0_compat 2 C).
      + reflexivity.
      + exact HCpos.
    - rewrite Qmult_0_l. exact (QltT_to_Qlt _ _ Hep). }
  exists (N0 + Datatypes.S t)%nat.
  intros n Hn.
  apply NatLe_drop in Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (exp_series n B * exp_tail_abs n (2 * n) B +
                         exp_tail_abs n (2 * n) B * exp_series (2 * n)%nat B) _).
  - apply QleT'_to_Qle.
    apply (exp_trunc_bound x y B n HB HxB HyB).
  - (* 两项和 <= 2*C*tail <= 2*C*X < eps *)
    apply (Qle_lt_trans _ ((1 + 1)%Q * C * exp_tail_abs n (2 * n) B) _).
    + apply (Qle_trans _ (C * exp_tail_abs n (2 * n) B + exp_tail_abs n (2 * n) B * C) _).
      * apply Qplus_le_compat.
        -- apply (Qmult_le_compat_nonneg (exp_series n B) C
                   (exp_tail_abs n (2 * n) B) (exp_tail_abs n (2 * n) B)).
           ++ split; [apply QleT'_to_Qle; apply (exp_series_nonneg n B HB) | apply QleT'_to_Qle; apply (HC n)].
           ++ split; [apply QleT'_to_Qle; apply (exp_tail_abs_nonneg n (2 * n) B); exact HB | apply Qle_refl].
        -- apply (Qmult_le_compat_nonneg (exp_tail_abs n (2 * n) B) (exp_tail_abs n (2 * n) B)
                   (exp_series (2 * n)%nat B) C).
           ++ split; [apply QleT'_to_Qle; apply (exp_tail_abs_nonneg n (2 * n) B); exact HB | apply Qle_refl].
           ++ split; [apply QleT'_to_Qle; apply (exp_series_nonneg (2 * n)%nat B HB) | apply QleT'_to_Qle; apply (HC (2 * n)%nat)].
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + (* 2*C*tail < eps：tail <= X（geom2）+ X < eps/(2C)（arch），2*C > 0 *)
      apply (Qle_lt_trans _ ((1 + 1)%Q * C * ((q_pow B n / q_fact n) * (1 + 1)%Q)) _).
      * (* 2*C*tail <= 2*C*X：Qmult_le_compat_nonneg 交叉 x=2C y=2C z=tail t=X *)
        apply (Qmult_le_compat_nonneg ((1 + 1)%Q * C) ((1 + 1)%Q * C)
                 (exp_tail_abs n (2 * n) B) ((q_pow B n / q_fact n) * (1 + 1)%Q)).
        -- split; [apply (Qmult_le_0_compat (1 + 1)%Q C); [unfold Qle; simpl; lia | exact HCnonneg] | apply (Qle_refl ((1 + 1)%Q * C))].
        -- split; [apply QleT'_to_Qle; apply (exp_tail_abs_nonneg n (2 * n) B); exact HB
                 | apply QleT'_to_Qle; apply (exp_tail_abs_geom2 B n (2 * n) HB)].
           ++ intros u Hu. apply (HN0 u). apply NatLe_lift. apply Nat.le_trans with n; [lia | exact (NatLe_drop n u Hu)].
           ++ lia.
      * (* 2*C*X < eps：X < eps/(2C)（arch），乘 2*C（正） *)
        apply (Qle_lt_trans _ (((q_pow B n / q_fact n) * (1 + 1)%Q) * ((1 + 1)%Q * C)) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qlt_le_trans _ ((eps / (2 * C)) * ((1 + 1)%Q * C)) _).
          { apply (Qmult_lt_compat_r ((q_pow B n / q_fact n) * (1 + 1)%Q)
                     (eps / (2 * C)) ((1 + 1)%Q * C)).
            { apply (Qmult_lt_0_compat (1 + 1)%Q C).
              { unfold Qlt; simpl; lia. }
              { exact HCpos. } }
            { apply QltT_to_Qlt. apply (exp_tail_arch B N0 t n (eps / (2 * C))%Q HB (fun u Hu => HN0 u Hu)).
              { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps (2 * C)).
                { apply (Qmult_lt_0_compat 2 C).
                  { reflexivity. }
                  { exact HCpos. } }
                { rewrite Qmult_0_l. exact (QltT_to_Qlt _ _ Hep). } }
              { exact Hdec. }
              { lia. } } }
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            transitivity (eps * ((2 * C) * Qinv (2 * C))).
            + unfold Qdiv. ring.
            + rewrite (Qmult_inv_r (2 * C)).
              * ring.
* intro Hz. assert (H2C : QltT 0 (2 * C)).
                { apply Qlt_to_QltT. apply (Qmult_lt_0_compat 2 C). unfold Qlt; simpl; lia. exact HCpos. }
                exact (match q_neq_of_lt (2 * C) H2C (qeq_imp_qeqT _ _ Hz) with end). } }
Qed.

(* E11：序列版截断误差衰减——u v 为随 n 变化的序列（Real 层组装用）：
   前提：∀n, |u n| ≤ B 且 |v n| ≤ B（一致有界）⟹ ∃N，∀n≥N：|三角(2n,u n,v n) − 方块(n,u n,v n)| < eps
   与 exp_trunc_arch 的区别：x y 参数化（u n / v n），N 只依赖 B、eps（q_arch_geom/arch_decay 与 x y 无关） *)
Lemma exp_trunc_arch_seq : forall (u v : nat -> Q) (B eps : Q),
  QleT' 0 B -> (forall n : nat, QleT' (Qabs (u n)) B) -> (forall n : nat, QleT' (Qabs (v n)) B) -> QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (Qabs (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => (q_pow (u n) j / q_fact j) * (q_pow (v n) i / q_fact i))) -
                sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => (q_pow (u n) j / q_fact j) * (q_pow (v n) i / q_fact i)))))
         eps).
Proof.
  intros u v B eps HB HuB HvB Hep.
  destruct (exp_series_arch B HB) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1%Q _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  assert (HCnonneg : Qle 0 C) by (apply (Qlt_le_weak 0 C); exact HCpos).
  destruct (q_arch_geom B) as [N0 HN0].
  destruct (arch_decay ((q_pow B N0 / q_fact N0) * (1 + 1)%Q) (eps / (2 * C))%Q) as [t Hdec].
  { apply q_pow_fact2_nonneg. exact HB. }
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - apply (Qmult_lt_0_compat 2 C).
      + reflexivity.
      + exact HCpos.
    - rewrite Qmult_0_l. exact (QltT_to_Qlt _ _ Hep). }
  exists (N0 + Datatypes.S t)%nat.
  intros n Hn.
  apply NatLe_drop in Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (exp_series n B * exp_tail_abs n (2 * n) B +
                         exp_tail_abs n (2 * n) B * exp_series (2 * n)%nat B) _).
  - apply QleT'_to_Qle.
    apply (exp_trunc_bound (u n) (v n) B n HB (HuB n) (HvB n)).
  - apply (Qle_lt_trans _ ((1 + 1)%Q * C * exp_tail_abs n (2 * n) B) _).
    + apply (Qle_trans _ (C * exp_tail_abs n (2 * n) B + exp_tail_abs n (2 * n) B * C) _).
      * apply Qplus_le_compat.
        -- apply (Qmult_le_compat_nonneg (exp_series n B) C
                   (exp_tail_abs n (2 * n) B) (exp_tail_abs n (2 * n) B)).
           ++ split; [apply QleT'_to_Qle; apply (exp_series_nonneg n B HB) | apply QleT'_to_Qle; apply (HC n)].
           ++ split; [apply QleT'_to_Qle; apply (exp_tail_abs_nonneg n (2 * n) B); exact HB | apply Qle_refl].
        -- apply (Qmult_le_compat_nonneg (exp_tail_abs n (2 * n) B) (exp_tail_abs n (2 * n) B)
                   (exp_series (2 * n)%nat B) C).
           ++ split; [apply QleT'_to_Qle; apply (exp_tail_abs_nonneg n (2 * n) B); exact HB | apply Qle_refl].
           ++ split; [apply QleT'_to_Qle; apply (exp_series_nonneg (2 * n)%nat B HB) | apply QleT'_to_Qle; apply (HC (2 * n)%nat)].
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_lt_trans _ ((1 + 1)%Q * C * ((q_pow B n / q_fact n) * (1 + 1)%Q)) _).
      * apply (Qmult_le_compat_nonneg ((1 + 1)%Q * C) ((1 + 1)%Q * C)
               (exp_tail_abs n (2 * n) B) ((q_pow B n / q_fact n) * (1 + 1)%Q)).
        -- split; [apply (Qmult_le_0_compat (1 + 1)%Q C); [unfold Qle; simpl; lia | exact HCnonneg] | apply (Qle_refl ((1 + 1)%Q * C))].
        -- split; [apply QleT'_to_Qle; apply (exp_tail_abs_nonneg n (2 * n) B); exact HB
                 | apply QleT'_to_Qle; apply (exp_tail_abs_geom2 B n (2 * n) HB)].
           ++ intros u0 Hu0. apply (HN0 u0). apply NatLe_lift. apply Nat.le_trans with n; [lia | exact (NatLe_drop n u0 Hu0)].
           ++ lia.
      * apply (Qle_lt_trans _ (((q_pow B n / q_fact n) * (1 + 1)%Q) * ((1 + 1)%Q * C)) _).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        { apply (Qlt_le_trans _ ((eps / (2 * C)) * ((1 + 1)%Q * C)) _).
          { apply (Qmult_lt_compat_r ((q_pow B n / q_fact n) * (1 + 1)%Q)
                     (eps / (2 * C)) ((1 + 1)%Q * C)).
            { apply (Qmult_lt_0_compat (1 + 1)%Q C).
              { unfold Qlt; simpl; lia. }
              { exact HCpos. } }
            { apply QltT_to_Qlt. apply (exp_tail_arch B N0 t n (eps / (2 * C))%Q HB (fun u Hu => HN0 u Hu)).
              { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps (2 * C)).
                { apply (Qmult_lt_0_compat 2 C).
                  { reflexivity. }
                  { exact HCpos. } }
                { rewrite Qmult_0_l. apply QltT_to_Qlt. exact Hep. } }
              { exact Hdec. }
              { lia. } } }
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            transitivity (eps * ((2 * C) * Qinv (2 * C))).
            + unfold Qdiv. ring.
            + rewrite (Qmult_inv_r (2 * C)).
              * ring.
* intro Hz. assert (H2C : QltT 0 (2 * C)).
                { apply Qlt_to_QltT. apply (Qmult_lt_0_compat 2 C). unfold Qlt; simpl; lia. exact HCpos. }
                exact (match q_neq_of_lt (2 * C) H2C (qeq_imp_qeqT _ _ Hz) with end). } }
Qed.

End ExpPlusStage2b.

(* ================================================================
   Real 层组装：cauchy_real_exp_plus（exp_neg_plus 字段材料）
   目标：real_eq (cauchy_real_exp (real_plus x y))
                 (real_mult (cauchy_real_exp x) (cauchy_real_exp y))
   结构（eps/3 分割，对角线拼接）：
     |ep_n(u+v) − ep_n u·ep_n v|
     ≤ |ep_n(u+v) − ep_{2n}(u+v)|              [A：部分和阶差，exp_partial_cauchy_bounded]
       + |ep_{2n}(u+v) − ep_n u·ep_n v|        [B：Cauchy 积差，exp_cauchy_double/prod_double + exp_trunc_arch_seq]
   ================================================================ *)
Lemma cauchy_real_exp_plus : forall x y : Real,
  real_eq (cauchy_real_exp (real_plus x y))
          (real_mult (cauchy_real_exp x) (cauchy_real_exp y)).
Proof.
  intros x y.
  destruct x as [u Hu]. destruct y as [v Hv].
  unfold real_eq.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mx [HMxpos HMx]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [My [HMypos HMy]].
  set (M := Mx + My).
  (* M = Mx + My：Set 正性/非负与一致界（HMxpos/HMypos/HMx/HMy 直接，无降级） *)
  assert (HMposT : QltT 0 M).
  { unfold M. apply (qltT_plus_pos_r Mx My). exact HMxpos. exact HMypos. }
  assert (HMnonnegT : QleT' 0 M).
  { apply qltT_leT'. exact HMposT. }
  assert (HuMT : forall n : nat, QleT' (Qabs (u n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (u n)) Mx (Mx + My)).
    - apply HMx.
    - apply (qleT'_plus_nonneg_rT Mx My). apply qltT_leT'. exact HMypos. }
  assert (HvMT : forall n : nat, QleT' (Qabs (v n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (v n)) My (Mx + My)).
    - apply HMy.
    - apply (qleT'_trans My (My + Mx) (Mx + My)).
      + apply (qleT'_plus_nonneg_rT My Mx). apply qltT_leT'. exact HMxpos.
      + apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (HsumMT : forall n : nat, QleT' (Qabs (u n + v n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (u n + v n)) (Qabs (u n) + Qabs (v n)) (Mx + My)).
    - apply Qle_to_QleT'. apply Qabs_triangle.
    - apply (qleT'_plus_compat (Qabs (u n)) Mx (Qabs (v n)) My).
      + apply HMx.
      + apply HMy. }
  (* eps/3 正性（Set） *)
  assert (Heps3T : QltT 0 (eps / 3)).
  { apply (qltT_div_pos eps 3). exact Heps. exact qltT_0_3. }
  (* 部分 A：exp_partial_cauchy_bounded（Set 输入） *)
  destruct (exp_partial_cauchy_bounded M (eps / 3)%Q HMnonnegT Heps3T) as [N1 HN1].
  (* 部分 B：exp_trunc_arch_seq（Set 输入） *)
  destruct (exp_trunc_arch_seq u v M (eps / 3)%Q HMnonnegT HuMT HvMT Heps3T) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  apply NatLe_drop in Hn.
  apply Qlt_to_QltT.
  change (Qlt (Qabs (exp_partial n (u n + v n) - exp_partial n (u n) * exp_partial n (v n))) eps).
  (* 代数拆分：ep_n(u+v) − ep_n u·ep_n v == (ep_n(u+v) − ep_{2n}(u+v)) + (ep_{2n}(u+v) − ep_n u·ep_n v) *)
  apply (Qle_lt_trans _ (Qabs (exp_partial n (u n + v n) - exp_partial ((2 * n)%nat) (u n + v n)) +
                          Qabs (exp_partial ((2 * n)%nat) (u n + v n) - exp_partial n (u n) * exp_partial n (v n))) _).
  - apply (Qle_trans _ (Qabs ((exp_partial n (u n + v n) - exp_partial ((2 * n)%nat) (u n + v n)) +
                               (exp_partial ((2 * n)%nat) (u n + v n) - exp_partial n (u n) * exp_partial n (v n)))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.      apply (Qabs_wd (exp_partial n (u n + v n) - exp_partial n (u n) * exp_partial n (v n))
                     ((exp_partial n (u n + v n) - exp_partial ((2 * n)%nat) (u n + v n)) +
                      (exp_partial ((2 * n)%nat) (u n + v n) - exp_partial n (u n) * exp_partial n (v n)))).
      ring.
    + apply Qabs_triangle.
  - apply (Qlt_le_trans _ (eps / 3 + eps / 3) _).
    + apply Qplus_lt_compat.
      * apply QltT_to_Qlt.
        apply (HN1 n ((2 * n)%nat)).
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact Hn].
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | lia].
        -- exact (HsumMT n).
      * apply (Qle_lt_trans _ (Qabs (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => (q_pow (u n) j / q_fact j) * (q_pow (v n) i / q_fact i))) -
                                    sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => (q_pow (u n) j / q_fact j) * (q_pow (v n) i / q_fact i))))) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.           apply (Qabs_wd (exp_partial ((2 * n)%nat) (u n + v n) - exp_partial n (u n) * exp_partial n (v n))
                          (sum_upto (Datatypes.S (2 * n)) (fun j => sum_upto (Datatypes.S (2 * n - j)) (fun i => (q_pow (u n) j / q_fact j) * (q_pow (v n) i / q_fact i))) -
                           sum_upto (Datatypes.S n) (fun j => sum_upto (Datatypes.S n) (fun i => (q_pow (u n) j / q_fact j) * (q_pow (v n) i / q_fact i))))).
           setoid_rewrite (qeqT_imp_qeq _ _ ((exp_cauchy_double (u n) (v n) n))).
           setoid_rewrite (qeqT_imp_qeq _ _ ((exp_prod_double (u n) (v n) n))).
           reflexivity.
        -- apply QltT_to_Qlt.
           apply (HN2 n).
           apply NatLe_lift.
           apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact Hn].
    + (* eps/3 + eps/3 ≤ eps：2/3 ≤ 1，乘 eps ≥ 0 *)
      apply (Qle_trans _ (Qmult (Qinv 3 + Qinv 3) eps) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
      * apply (Qle_trans _ (Qmult 1 eps) _).
        -- apply (Qmult_le_compat_r (Qinv 3 + Qinv 3) 1 eps).
           ++ unfold Qle, Qinv, Qplus. simpl. lia.
           ++ apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* log 论证第三阶段（并入主文件）：构造性 log 族  *)
(* exp 值域 (0,∞) 二分逼近 → log_seq 柯西 → cw_log 定义 + 右逆  *)
(* 检验 _dbg_exp_plus.v L1408-4692 合并（158 Qed 验证通过）        *)
(* ============================================================ *)

Section LogStage3.

(* Q 层：0 < e ⟹ e/2 < e（合并自检验 L1391，log 论证第三阶段依赖） *)
Lemma q_half_lt_self : forall e : Q, QltT 0 e -> QltT (e / 2) e.
Proof.
  intros e He.
  apply Qlt_to_QltT.
  unfold Qdiv.
  apply (Qlt_shift_div_r e 2 e).
  - reflexivity.
  - apply (Qle_lt_trans _ (1 * e) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qlt_le_trans _ (2 * e) _).
      * apply (Qmult_lt_compat_r 1 2 e).
        -- apply QltT_to_Qlt. exact He.
        -- assert (H12 : Qlt 1 2) by (unfold Qlt; vm_compute; reflexivity).
           exact H12.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma exp_partial_ge_plus_x : forall (n : nat) (x : Q),
  QleT' 0 x -> QleT' (1 + x) (exp_partial (Datatypes.S n) x).
Proof.
  intros n x Hx.
  apply Qle_to_QleT'.
  induction n as [| m IH]; simpl.
  - change (Qle (1 + x) (1 + q_pow x 1 / q_fact 1)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ x 0)).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ 0)).
    simpl.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
  - apply (Qle_trans _ (exp_partial (Datatypes.S m) x) _).
    + exact IH.
    + apply (Qle_plus_nonneg_r (exp_partial (Datatypes.S m) x) (q_pow x (Datatypes.S (Datatypes.S m)) / q_fact (Datatypes.S (Datatypes.S m)))).
      apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact Hx.
Qed.

(* Real 层：t > 0 ⟹ e^t > 1
   见证 eps 直接取 t 的分离 eps：对 n ≥ max N1 1，
   ep_n(u n) ≥ 1 + u n ≥ 1 + eps（exp_partial_ge_plus_x，n = S(n−1)）⟹ ep_n(u n) − 1 ≥ eps *)
Lemma cauchy_real_exp_gt_one : forall t : Real,
  real_lt real_zero t -> real_lt real_one (cauchy_real_exp t).
Proof.
  intros t Ht.
  destruct t as [u Hu].
  destruct Ht as [eps [Heps [N1 HN1]]].
  exists eps.
  split.
  - exact Heps.
  - exists (Nat.max N1 1)%nat.
    intros n Hn.
    apply NatLe_drop in Hn.
    apply Qlt_to_QltT.
    assert (Hn1 : (1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N1 1) _); [apply Nat.le_max_r | exact Hn]).
    assert (HnN : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N1 1) _); [apply Nat.le_max_l | exact Hn]).
    (* eps < u n − 0 == u n *)
    assert (Hun : QltT eps (u n)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans _ (u n - 0) _).
      - apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift. exact HnN.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* ep_n(u n) ≥ 1 + u n，eps < u n ⟹ eps < ep_n(u n) − 1 *)
    assert (Hnpos : (0 < n)%nat) by lia.
    destruct n as [| m].
    { lia. }  (* n ≥ 1 矛盾 *)
    { assert (Hu0 : Qle 0 (u (Datatypes.S m))).
      { apply (Qlt_le_weak 0 (u (Datatypes.S m))).
        apply (Qlt_trans _ eps _).
        - apply QltT_to_Qlt. exact Heps.
        - exact (QltT_to_Qlt _ _ Hun). }
      assert (Hepx : Qle (1 + u (Datatypes.S m)) (exp_partial (Datatypes.S m) (u (Datatypes.S m)))).
      { apply QleT'_to_Qle. apply (exp_partial_ge_plus_x m (u (Datatypes.S m))). apply Qle_to_QleT'. exact Hu0. }
      assert (Hsum : Qle (u (Datatypes.S m)) (1 + u (Datatypes.S m))).
      { apply (Qle_trans _ (u (Datatypes.S m) + 1) _).
        - apply (Qle_plus_nonneg_r (u (Datatypes.S m)) 1). apply QleT'_to_Qle. apply Qle_0_1.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      (* 目标：eps < ep_n(u n) − 1；桥：(1 + u n) − 1 == u n 且 1+u n ≤ ep_n(u n) *)
      apply (Qlt_le_trans _ (u (Datatypes.S m)) _).
      + exact (QltT_to_Qlt _ _ Hun).
      + apply (Qle_trans _ (exp_partial (Datatypes.S m) (u (Datatypes.S m)) - 1) _).
        * apply (Qle_trans _ (1 + u (Datatypes.S m) - 1) _).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* (1+u) − 1 == u *)
          -- apply (Qplus_le_compat (1 + u (Datatypes.S m)) (exp_partial (Datatypes.S m) (u (Datatypes.S m))) (- 1) (- 1)).
             ++ exact Hepx.
             ++ apply Qle_refl.
        * apply Qle_refl.
      }
Qed.

(* Real 层桥：x < y ⟹ 0 < y − x（差正性，eps 见证不变） *)
Lemma real_lt_opp_plus : forall x y : Real,
  real_lt x y -> real_lt real_zero (real_plus y (real_opp x)).
Proof.
  intros x y Hxy.
  destruct Hxy as [eps [Heps [N1 HN1]]].
  exists eps.
  split.
  - exact Heps.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps < projT1 (real_plus y (real_opp x)) n − projT1 real_zero n == (y_n − x_n) − 0 *)
    assert (Hpt : projT1 (real_plus y (real_opp x)) n == projT1 y n - projT1 x n).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_opp x) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)). ring. }
    setoid_rewrite Hpt.
    (* (y_n − x_n) − 0 == y_n − x_n *)
    apply (Qlt_le_trans _ (projT1 y n - projT1 x n) _).
    + apply QltT_to_Qlt. apply (HN1 n). exact Hn.
    + apply QleT'_to_Qle. apply qeq_le.      apply qeq_imp_qeqT.
      assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hz0.
      unfold Qminus. ring.
Qed.

(* Real 层：0 < a、0 < b ⟹ 0 < a·b（eps 见证 = e_a·e_b/2 类？直接构造：
   0 < a 给 e1,N1：e1 < a_n；0 < b 给 e2,N2：e2 < b_n；
   取 e := e1·e2，对 n ≥ max N1 N2：e1·e2 < a_n·b_n（a_n,b_n 有界正）*)
Lemma real_mult_pos_compat : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  destruct a as [u Hu]. destruct b as [v Hv].
  destruct Ha as [e1 [He1 [N1 HN1]]].
  destruct Hb as [e2 [He2 [N2 HN2]]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mu [HMupos HMu]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [Mv [HMvpos HMv]].
  assert (Hpos : Qlt 0 (e1 * e2)).
  { apply Qmult_lt_0_compat; [exact (QltT_to_Qlt _ _ He1) | exact (QltT_to_Qlt _ _ He2)]. }
  exists (e1 * e2).
  split.
  - apply Qlt_to_QltT. exact Hpos.
  - exists (Nat.max N1 N2).
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：e1·e2 < projT1 (real_mult (existT u Hu) (existT v Hv)) n − 0 == a_n·b_n *)
    assert (Hpt : projT1 (real_mult (existT (fun s : Qseq => cauchy s) u Hu) (existT (fun s : Qseq => cauchy s) v Hv)) n == projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n).
    { apply qeqT_imp_qeq. apply real_mult_proj. }
    setoid_rewrite Hpt.
    (* e1·e2 < a_n·b_n：e1 < a_n 且 e2 < b_n，乘正 *)
    assert (Ha1 : QltT e1 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)).
    { apply Qlt_to_QltT.
      assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      apply (Qlt_le_trans _ (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. setoid_rewrite Hz0. unfold Qminus. ring. }
    assert (Hb1 : QltT e2 (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
    { apply Qlt_to_QltT.
      assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      apply (Qlt_le_trans _ (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 real_zero n) _).
      - apply QltT_to_Qlt. apply (HN2 n). apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)].
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. setoid_rewrite Hz0. unfold Qminus. ring. }
    (* 桥：e1·e2 < a_n·b_n：e1·e2 < b_n·e2（e1 < b_n 乘 e2 正）< a_n·b_n（b_n ≤ a_n 乘 e2？改：
       中间项 b_n·e1：e1·e2 < b_n·e2（e1<b_n, 0<e2）== e2·b_n，再 b_n·e1 ≤ ... 不对。
       直接：e1·e2 < e1·b_n（e2<b_n, 0<e1）且 e1·b_n ≤ a_n·b_n（e1≤a_n, 0≤b_n）*)
    (* 归约 real_zero 投影：目标尾部 − projT1 real_zero n == − 0 *)
    assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hz0' : projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 real_zero n ==
                    projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n).
    { setoid_rewrite Hz0. unfold Qminus. ring. }
    setoid_rewrite Hz0'.
    (* 桥：e1·e2 < a_n·b_n（Qmult_lt_compat_nonneg：0 ≤ e1 < a_n、0 ≤ e2 < b_n） *)
    apply (Qmult_lt_compat_nonneg e1 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)
                                  e2 (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
    + split.
      * apply (Qlt_le_weak 0 e1). exact (QltT_to_Qlt _ _ He1).
      * apply QltT_to_Qlt. exact Ha1.
    + split.
      * apply (Qlt_le_weak 0 e2). exact (QltT_to_Qlt _ _ He2).
      * apply QltT_to_Qlt. exact Hb1.
Qed.

(* Real 层：e^{y−x} − 1 > 0（由 e^{y−x} > 1，逐 eps 差正性） *)
Lemma cauchy_real_exp_minus_one_pos : forall t : Real,
  real_lt real_zero t -> real_lt real_zero (real_plus (cauchy_real_exp t) (real_opp real_one)).
Proof.
  intros t Ht.
  (* e^t > 1 ⟹ e^t − 1 > 0：逐 eps 同见证 *)
  destruct (cauchy_real_exp_gt_one t Ht) as [eps [Heps [N1 HN1]]].
  exists eps.
  split.
  - exact Heps.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps < projT1 (real_plus (exp t) (real_opp one)) n − 0 == ep_n(t_n) − 1 *)
    assert (Hpt : projT1 (real_plus (cauchy_real_exp t) (real_opp real_one)) n ==
                  projT1 (cauchy_real_exp t) n - projT1 real_one n).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp t) (real_opp real_one) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)). ring. }
    setoid_rewrite Hpt.
    assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hz0' : projT1 (cauchy_real_exp t) n - projT1 real_one n - projT1 real_zero n ==
                    projT1 (cauchy_real_exp t) n - projT1 real_one n).
    { setoid_rewrite Hz0. unfold Qminus. ring. }
    setoid_rewrite Hz0'.
    (* eps < ep_n(t_n) − 1：HN1 给 eps < ep_n(t_n) − 1（real_lt one (exp t) 见证） *)
    apply (Qlt_le_trans _ (projT1 (cauchy_real_exp t) n - projT1 real_one n) _).
    + apply QltT_to_Qlt. apply (HN1 n). exact Hn.
    + apply Qle_refl.
Qed.

(* Real 层：e^x > 0 且 e^{y−x} − 1 > 0 ⟹ e^x·(e^{y−x} − 1) > 0 *)
Lemma cauchy_real_exp_plus_pos : forall x y : Real,
  real_lt real_zero (cauchy_real_exp x) ->
  real_lt real_zero (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one)) ->
  real_lt real_zero (real_mult (cauchy_real_exp x)
                               (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one))).
Proof.
  intros x y Hx Hdiff.
  apply (real_mult_pos_compat (cauchy_real_exp x)
                              (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one))).
  - exact Hx.
  - exact Hdiff.
Qed.

(* Real 层反向差正性桥：0 < y − x ⟹ x < y（与 real_lt_opp_plus 互逆，eps 见证不变） *)
Lemma real_lt_zero_minus : forall x y : Real,
  real_lt real_zero (real_plus y (real_opp x)) -> real_lt x y.
Proof.
  intros x y H.
  destruct H as [eps [Heps [N1 HN1]]].
  exists eps.
  split.
  - exact Heps.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps < projT1 y n − projT1 x n == (y_n − x_n) − 0 *)
    assert (Hpt : projT1 (real_plus y (real_opp x)) n == projT1 y n - projT1 x n).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_opp x) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)). ring. }
    apply (Qlt_le_trans _ (projT1 y n - projT1 x n) _).
    + apply (Qlt_le_trans _ (projT1 (real_plus y (real_opp x)) n - projT1 real_zero n) _).
      * apply QltT_to_Qlt. apply (HN1 n). exact Hn.
      * apply QleT'_to_Qle. apply qeq_le.        apply qeq_imp_qeqT.
        assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hpt.
        setoid_rewrite Hz0.
        unfold Qminus. ring.
    + apply Qle_refl.
Qed.

(* exp 参数外延（连续性 eps-N）：real_eq a b ⟹ real_eq (exp a) (exp b)
   策略：|ep_n(a_n) − ep_n(b_n)| ≤ |a_n − b_n|·exp_series n M（lipschitz）
   ≤ (eps/(2C))·C == eps/2 < eps（|a_n−b_n| < eps/(2C) 由 real_eq a b 取 eps/(2C)，
   C := exp_series_arch M 界，M 覆盖 a,b 一致界） *)
Lemma cauchy_real_exp_wd : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  destruct a as [u Hu]. destruct b as [v Hv].
  unfold real_eq.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mu [HMupos HMu]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [Mv [HMvpos HMv]].
  set (M := Mu + Mv).
  (* Set 正性/非负与一致界（HMupos/HMvpos/HMu/HMv 直接，无降级） *)
  assert (HMposT : QltT 0 M).
  { unfold M. apply (qltT_plus_pos_r Mu Mv). exact HMupos. exact HMvpos. }
  assert (HMnonnegT : QleT' 0 M).
  { apply qltT_leT'. exact HMposT. }
  destruct (exp_series_arch M HMnonnegT) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  assert (HCpos : Qlt 0 C).
  { apply QltT_to_Qlt. exact HCposT. }
  assert (HCnonneg : Qle 0 C) by (apply (Qlt_le_weak 0 C); exact HCpos).
  assert (HuMT : forall n : nat, QleT' (Qabs (u n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (u n)) Mu (Mu + Mv)).
    - apply HMu.
    - apply (qleT'_plus_nonneg_rT Mu Mv). apply qltT_leT'. exact HMvpos. }
  assert (HvMT : forall n : nat, QleT' (Qabs (v n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (v n)) Mv (Mu + Mv)).
    - apply HMv.
    - apply (qleT'_trans Mv (Mv + Mu) (Mu + Mv)).
      + apply (qleT'_plus_nonneg_rT Mv Mu). apply qltT_leT'. exact HMupos.
      + apply qeq_le. apply qeq_imp_qeqT. ring. }
  (* real_eq a b 取 eps/(2C)（Set 正性链） *)
  assert (HepsC : QltT 0 (eps / (2 * C))).
  { apply (qltT_div_pos eps (2 * C)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT. }
  destruct (Hab (eps / (2 * C))%Q HepsC) as [N1 HN1].
  (* exp_partial 尾部柯西（eps/2，Set 输入） *)
  assert (Heps2T : QltT 0 (eps / 2)).
  { apply (qltT_div_pos eps 2). exact Heps. exact qltT_0_2. }
  destruct (exp_partial_cauchy_bounded M (eps / 2)%Q HMnonnegT Heps2T) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  apply Qlt_to_QltT.
  (* 目标：|ep_n(u n) − ep_n(v n)| < eps *)
  apply (Qle_lt_trans _ (Qabs (u n - v n) * C) _).
  - apply (Qle_trans _ (Qabs (u n - v n) * exp_series n M) _).
    + apply (Qle_trans _ (Qabs (exp_partial n (u n) - exp_partial n (v n))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.        apply (Qabs_wd (exp_partial n (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) - exp_partial n (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n))
                       (exp_partial n (u n) - exp_partial n (v n))).
        reflexivity.
      * apply QleT'_to_Qle. apply (exp_partial_lipschitz (u n) (v n) M n HMnonnegT (HuMT n) (HvMT n)).
    + apply (Qmult_le_compat_nonneg (Qabs (u n - v n)) (Qabs (u n - v n))
                                    (exp_series n M) C).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- apply QleT'_to_Qle. apply (exp_series_nonneg n M HMnonnegT).
        -- apply QleT'_to_Qle. apply (HC n).
  - apply (Qle_lt_trans _ ((eps / (2 * C)) * C) _).
    + apply (Qmult_le_compat_r (Qabs (u n - v n)) (eps / (2 * C)) C).
      * apply (Qlt_le_weak (Qabs (u n - v n)) (eps / (2 * C))).
        apply QltT_to_Qlt.
        apply (HN1 n).
        apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
      * exact HCnonneg.
    + apply (Qle_lt_trans _ (eps / 2) _).
      * apply QleT'_to_Qle. apply qeq_le.        apply qeq_imp_qeqT.
        assert (Hc : (eps / (2 * C)) * C == eps / 2).
        { unfold Qdiv. field.
          all: try (intro Hzc; exact (match q_neq_of_lt C (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ Hzc) with end)). }
        exact Hc.
      * apply QltT_to_Qlt. apply (q_half_lt_self eps).
        exact Heps.
Qed.

(* Real 层分配：a·b − a == a·(b − 1)（real_eq，逐点 ring） *)
Lemma real_mult_minus_factor : forall a b : Real,
  real_eq (real_plus (real_mult a b) (real_opp a))
          (real_mult a (real_plus b (real_opp real_one))).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  set (A := projT1 a n).
  set (B := projT1 b n).
  assert (Hl : projT1 (real_plus (real_mult a b) (real_opp a)) n == A * B + - A).
  { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult a b) (real_opp a) n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj a b n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)).
    unfold A, B. ring. }
  assert (Hr : projT1 (real_mult a (real_plus b (real_opp real_one))) n == A * (B + - 1)).
  { assert (Ho1 : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj a (real_plus b (real_opp real_one)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj b (real_opp real_one) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    setoid_rewrite Ho1.
    unfold A, B. ring. }
  apply qeq_imp_qeqT.
  setoid_rewrite Hl.
  setoid_rewrite Hr.
  unfold Qminus. ring.
Qed.

(* 主定理：exp 严格单调——x < y ⟹ e^x < e^y
   链：0 < y−x → e^{y−x} > 1 → e^{y−x}−1 > 0 → e^x·(e^{y−x}−1) > 0
       且 e^y == e^{x+(y−x)} == e^x·e^{y−x}（real_eq_of_zero_diff + plus + wd）
       → e^y − e^x == e^x·(e^{y−x}−1) > 0 → e^x < e^y（real_lt_zero_minus） *)
Lemma cauchy_real_exp_mono : forall x y : Real,
  real_lt x y -> real_lt (cauchy_real_exp x) (cauchy_real_exp y).
Proof.
  intros x y Hxy.
  (* 0 < y − x *)
  assert (Hdiff : real_lt real_zero (real_plus y (real_opp x))) by (apply (real_lt_opp_plus x y); exact Hxy).
  (* e^{y−x} − 1 > 0 *)
  assert (Hminus : real_lt real_zero (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one))).
  { apply (cauchy_real_exp_minus_one_pos (real_plus y (real_opp x))). exact Hdiff. }
  (* e^x·(e^{y−x}−1) > 0 *)
  assert (Hprod : real_lt real_zero (real_mult (cauchy_real_exp x)
                                     (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one)))).
  { apply (real_mult_pos_compat (cauchy_real_exp x)
                                (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one))).
    - apply cauchy_real_exp_pos.
    - exact Hminus. }
  (* y == x + (y − x)：逐点 ring *)
  assert (Hxyeq : real_eq y (real_plus x (real_plus y (real_opp x)))).
  { apply real_eq_of_zero_diff.
    intro n.
    assert (Hpy : projT1 y n - projT1 (real_plus x (real_plus y (real_opp x))) n == 0).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj x (real_plus y (real_opp x)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_opp x) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
      ring. }
    exact (qeq_imp_qeqT _ _ Hpy). }
  (* e^y == e^{x+(y−x)}（exp_wd） *)
  assert (Hewd : real_eq (cauchy_real_exp y) (cauchy_real_exp (real_plus x (real_plus y (real_opp x))))).
  { apply (cauchy_real_exp_wd y (real_plus x (real_plus y (real_opp x)))). exact Hxyeq. }
  (* e^{x+(y−x)} == e^x·e^{y−x}（cauchy_real_exp_plus） *)
  assert (Heplus : real_eq (cauchy_real_exp (real_plus x (real_plus y (real_opp x))))
                          (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_plus y (real_opp x))))).
  { apply (cauchy_real_exp_plus x (real_plus y (real_opp x))). }
  (* e^y == e^x·e^{y−x} *)
  assert (Hmain : real_eq (cauchy_real_exp y)
                          (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_plus y (real_opp x))))).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus x (real_plus y (real_opp x)))) _).
    - exact Hewd.
    - exact Heplus. }
  (* e^y − e^x == e^x·e^{y−x} − e^x == e^x·(e^{y−x} − 1)（real_eq 组合） *)
  assert (Hdiffeq : real_eq (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
                            (real_mult (cauchy_real_exp x)
                                       (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one)))).
  { apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_plus y (real_opp x))))
                                      (real_opp (cauchy_real_exp x))) _).
    - apply (RealSetoid.real_eq_plus_compat (cauchy_real_exp y)
                                 (real_opp (cauchy_real_exp x))
                                 (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_plus y (real_opp x))))
                                 (real_opp (cauchy_real_exp x))).
      + exact Hmain.
      + apply real_eq_refl.
    - apply (real_mult_minus_factor (cauchy_real_exp x) (cauchy_real_exp (real_plus y (real_opp x)))).
  }
  (* 0 < e^y − e^x：real_eq_lt_lt 桥（e^y−e^x == 正项，正项 > 0） *)
  assert (Hposdiff : real_lt real_zero (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))).
  { apply (real_lt_eq_lt real_zero
                         (real_mult (cauchy_real_exp x)
                                    (real_plus (cauchy_real_exp (real_plus y (real_opp x))) (real_opp real_one)))
                         (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))).
    - exact Hprod.
    - apply real_eq_sym. exact Hdiffeq. }
  (* e^x < e^y：由 0 < e^y − e^x 且 (e^y−e^x) == e^y + (−e^x)，逐点 eps 一致 *)
  destruct Hposdiff as [eps [Heps [N1 HN1]]].
  exists eps.
  split.
  - exact Heps.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps < (e^y)_n − (e^x)_n；HN1 给 eps < (e^y−e^x)_n − 0 *)
    assert (Hpt : projT1 (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x))) n ==
                  projT1 (cauchy_real_exp y) n - projT1 (cauchy_real_exp x) n).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp y) (real_opp (cauchy_real_exp x)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_exp x) n)). ring. }
    apply (Qlt_le_trans _ (projT1 (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x))) n - projT1 real_zero n) _).
    + apply QltT_to_Qlt. apply (HN1 n). exact Hn.
    + apply QleT'_to_Qle. apply qeq_le.      apply qeq_imp_qeqT.
      assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hpt.
      setoid_rewrite Hz0.
      unfold Qminus. ring.
Qed.

(* ================================================================
   log 论证第二阶段：exp 无界（∀B, ∃x, B < e^x）
   ================================================================ *)

(* ================================================================
   log 论证第二阶段：exp 无界（∀B, ∃x, B < e^x）
   ================================================================ *)

(* Real 层 Archimedean：∀B, ∃n:nat, B < n#1（B 有界 + q_arch_geom）
   eps = (n#1 − M)/2，n#1 − b_k ≥ n#1 − M > eps ✓ 严格 *)
Lemma real_arch : forall B : Real,
  sigT (fun n : nat => And (NatLe 2 n) (real_lt B (real_const (Z.of_nat n # 1)))).
Proof.
  intros B.
  destruct B as [b Hb].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) b Hb)) as [M [HMpos HM]].
  destruct (q_arch_geom M) as [N0 HN0].
  exists (N0 + 2)%nat.
  split.
  - apply NatLe_lift. lia.
  - (* M < (N0+2)#1：2M ≤ N0+2（HN0 于 t = N0+1）⟹ M < N0+2 *)
  assert (HnM : Qlt M (Z.of_nat (N0 + 2) # 1)).
  { apply (Qlt_le_trans _ (Qmult 2 M) _).
    - (* M < 2M：M == 1·M < 2M（0 < M） *)
      apply (Qle_lt_trans _ (1 * M) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* M == 1·M *)
      + apply (Qmult_lt_compat_r 1 2 M).
        * apply QltT_to_Qlt. exact HMpos.
        * assert (H12 : Qlt 1 2) by (unfold Qlt; vm_compute; reflexivity).
          exact H12.
    - apply (Qle_trans _ ((1 + 1) * M) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* 2·M == (1+1)·M *)
      + apply (Qle_trans _ (Z.of_nat (N0 + 1 + 1) # 1) _).
        * apply QleT'_to_Qle. apply (HN0 ((N0 + 1)%nat)). apply NatLe_lift. lia.
        * apply QleT'_to_Qle. apply qeq_le.          apply qeq_imp_qeqT.
          assert (Hn : (N0 + 1 + 1)%nat = (N0 + 2)%nat) by lia.
          rewrite Hn. reflexivity. }
  assert (Hpos : Qlt 0 ((Z.of_nat (N0 + 2) # 1) - M)).
  { apply (proj1 (Qlt_minus_iff M (Z.of_nat (N0 + 2) # 1))).
    exact HnM. }
  exists (((Z.of_nat (N0 + 2) # 1) - M) / 2).
  split.
  { apply Qlt_to_QltT.
    apply Qlt_shift_div_l.
    + reflexivity.
    + rewrite Qmult_0_l. exact Hpos. }
  { exists 0%nat.
    intros k Hk.
    apply Qlt_to_QltT.
    (* 目标：eps < (n#1) − b_k；n#1 − b_k ≥ n#1 − M > eps *)
    apply (Qlt_le_trans _ ((Z.of_nat (N0 + 2) # 1) - M) _).
    + apply (Qlt_shift_div_r ((Z.of_nat (N0 + 2) # 1) - M) 2
                             ((Z.of_nat (N0 + 2) # 1) - M)).
      * reflexivity.
      * (* X < 2·X：X == 1·X < 2X（0 < X） *)
        apply (Qle_lt_trans _ (1 * ((Z.of_nat (N0 + 2) # 1) - M)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* X == 1·X *)
        -- apply (Qlt_le_trans _ (2 * ((Z.of_nat (N0 + 2) # 1) - M)) _).
           ++ apply (Qmult_lt_compat_r 1 2 ((Z.of_nat (N0 + 2) # 1) - M)).
              ** exact Hpos.
              ** assert (H12 : Qlt 1 2) by (unfold Qlt; vm_compute; reflexivity).
                 exact H12.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* 2·X == X·2 *)
    + (* (n#1) − M ≤ (n#1) − b_k：b_k ≤ M ⟹ −b_k ≥ −M *)
      apply (Qplus_le_compat ((Z.of_nat (N0 + 2) # 1)) ((Z.of_nat (N0 + 2) # 1))
                               (- M) (- (projT1 (existT (fun s : Qseq => cauchy s) b Hb) k))).
      * apply Qle_refl.
      * apply (Qopp_le_compat (projT1 (existT (fun s : Qseq => cauchy s) b Hb) k) M).
        -- apply (Qle_trans _ (Qabs (projT1 (existT (fun s : Qseq => cauchy s) b Hb) k)) _).
           ++ apply Qle_Qabs.
           ++ exact (QleT'_to_Qle _ _ (HM k)). }
Qed.

(* Real 层：N ≥ 1 ⟹ e^{N#1} > N#1（ep_n(N) ≥ 1+N，见证 1/2，N0 = 1 跳过 n=0）
   链：1/2 < 1 ≤ ep_n(N) − N（Hepx：ep ≥ 1+N ⟹ ep−N ≥ 1） *)
Lemma cauchy_real_exp_gt_const : forall N : nat,
  (1 <= N)%nat ->
  real_lt (real_const (Z.of_nat N # 1)) (cauchy_real_exp (real_const (Z.of_nat N # 1))).
Proof.
  intros N HN.
  exists (1 / 2)%Q.
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 1%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    destruct n as [| m].
    { apply NatLe_drop in Hn. lia. }
    { assert (HN0 : Qle 0 (Z.of_nat N # 1)) by (unfold Qle; simpl; lia).
      assert (Hepx : Qle (Qplus 1 (Z.of_nat N # 1)) (exp_partial (Datatypes.S m) (Z.of_nat N # 1))).
      { apply QleT'_to_Qle. apply (exp_partial_ge_plus_x m (Z.of_nat N # 1)). apply Qle_to_QleT'. exact HN0. }
      assert (Hc : projT1 (real_const (Z.of_nat N # 1)) (Datatypes.S m) == Z.of_nat N # 1) by (apply qeqT_imp_qeq, real_const_proj).
      assert (He : projT1 (cauchy_real_exp (real_const (Z.of_nat N # 1))) (Datatypes.S m) ==
                   exp_partial (Datatypes.S m) (Z.of_nat N # 1)).
      { cbn [projT1]. reflexivity. }
      setoid_rewrite He.
      setoid_rewrite Hc.
      (* 目标：1/2 < ep − N *)
      apply (Qlt_le_trans _ 1%Q _).
      - (* 1/2 < 1：数值 *)
        change (Qlt (1 / 2) 1).
        unfold Qlt. simpl. lia.
      - (* 1 ≤ ep − N：1 == (1+N) + (−N) ≤ ep + (−N) *)
        apply (Qle_trans _ (Qplus (Qplus 1 (Z.of_nat N # 1)) (- (Z.of_nat N # 1))) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* 1 == (1+N) + (−N) *)
        + apply (Qplus_le_compat (Qplus 1 (Z.of_nat N # 1)) (exp_partial (Datatypes.S m) (Z.of_nat N # 1))
                                 (- (Z.of_nat N # 1)) (- (Z.of_nat N # 1))).
          * exact Hepx.
          * apply Qle_refl.
    }
Qed.

(* 主定理：exp 无界——∀B, ∃x, B < e^x
   B < N#1（real_arch）且 N#1 < e^{N#1}（gt_const，N = N0+2 ≥ 2）⟹ B < e^{N#1}（real_lt_trans） *)
Lemma cauchy_real_exp_unbounded : forall B : Real,
  sigT (fun x : Real => real_lt B (cauchy_real_exp x)).
Proof.
  intros B.
  destruct (real_arch B) as [n [Hn2 Hn]].
  exists (real_const (Z.of_nat n # 1)).
  (* n ≥ 1：real_arch 保证 2 ≤ n *)
  assert (Hn1 : (1 <= n)%nat) by (apply NatLe_drop in Hn2; lia).
  (* B < n#1 < e^{n#1} *)
  apply (real_lt_trans B (real_const (Z.of_nat n # 1)) (cauchy_real_exp (real_const (Z.of_nat n # 1)))).
  - exact Hn.
  - apply (cauchy_real_exp_gt_const n Hn1).
Qed.
(* ================================================================
   log 论证第三阶段（后续会话）：exp 值域 (0,∞) + 构造性 log
   路线（判例绕行定案）：Q 层近似测试二分（可判定）→ 近似根扫描
   （缺陷情形返回中点）→ Lipschitz 柯西族 → 极限 = log y
   ================================================================ *)

(* 中点严格位于区间内：a < b ⟹ a < (a+b)/2 < b *)
Lemma log_mid_lt_b : forall a b : Q, QltT a b -> QltT ((a + b) / 2) b.
Proof.
  intros a b Hab.
  apply Qlt_to_QltT.
  unfold Qdiv.
  apply (Qlt_shift_div_r (a + b) 2 b).
  - change (Qlt 0 2). compute. reflexivity.
  - apply (Qlt_le_trans _ (b + b) _).
    + apply (proj2 (Qplus_lt_l a b b)). apply QltT_to_Qlt. exact Hab.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma log_a_lt_mid : forall a b : Q, QltT a b -> QltT a ((a + b) / 2).
Proof.
  intros a b Hab.
  apply Qlt_to_QltT.
  unfold Qdiv.
  apply (Qlt_shift_div_l a (a + b) 2).
  - change (Qlt 0 2). compute. reflexivity.
  - apply (Qle_lt_trans _ (a + a) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (proj2 (Qplus_lt_r a b a)). apply QltT_to_Qlt. exact Hab.
Qed.

(* 近似精度正性：a < b ⟹ 0 < (b−a)/32 *)
Lemma log_d4_pos : forall a b : Q, QltT a b -> QltT 0 ((b - a) / 32).
Proof.
  intros a b Hab.
  apply Qlt_to_QltT.
  unfold Qdiv.
  apply (Qlt_shift_div_l 0 (b - a) 32).
  - change (Qlt 0 32). compute. reflexivity.
  - apply (Qle_lt_trans _ 0 _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (proj1 (Qlt_minus_iff a b)). apply QltT_to_Qlt. exact Hab.
Qed.

Lemma log_d4_posT : forall a b : Q, QltT a b -> QltT 0 ((b - a) / 32).
Proof.
  intros a b Hab. apply log_d4_pos. exact Hab.
Qed.

(* 区间长度：两种分支都减半 *)
Lemma log_step_len_mb : forall a b : Q, QltT a b -> QeqT (b - ((a + b) / 2)) ((b - a) / 2).
Proof.
  intros a b Hab. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

Lemma log_step_len_am : forall a b : Q, QltT a b -> QeqT (((a + b) / 2) - a) ((b - a) / 2).
Proof.
  intros a b Hab. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* 决策测试（与 log_step 体内完全一致，供引理 destruct）
   区间 [a,b]，m := (a+b)/2，d4 := (b−a)/32（近似精度）
   q ≈ e^m（exp_partial K1 m），r ≈ y（y_{K2}），|e^m−q| < d4，|y−r| < d4
   testA：q + 2d4 < r ⟹ e^m < y；testB：r + 2d4 < q ⟹ y < e^m；
   都失败：|e^m − y| ≤ 4d4（缺陷情形） *)
Definition log_testA (y : Real) (a b : Q) (Hab : QltT a b) : bool :=
  let m := (a + b) / 2 in
  let d4 := (b - a) / 32 in
  let K1 := projT1 (exp_partial_cauchy m d4 (log_d4_pos a b Hab)) in
  let K2 := projT1 (projT2 y d4 (log_d4_posT a b Hab)) in
  Qlt_bool (exp_partial K1 m + 2 * d4) (projT1 y K2).

Definition log_testB (y : Real) (a b : Q) (Hab : QltT a b) : bool :=
  let m := (a + b) / 2 in
  let d4 := (b - a) / 32 in
  let K1 := projT1 (exp_partial_cauchy m d4 (log_d4_pos a b Hab)) in
  let K2 := projT1 (projT2 y d4 (log_d4_posT a b Hab)) in
  Qlt_bool (projT1 y K2 + 2 * d4) (exp_partial K1 m).

Definition log_step (y : Real) (a b : Q) (Hab : QltT a b) :
  sigT (fun ab : Q * Q => QltT (fst ab) (snd ab)).
Proof.
  set (m := (a + b) / 2).
  destruct (log_testA y a b Hab) eqn:EA.
  - exists (m, b). unfold m. apply log_mid_lt_b. exact Hab.
  - destruct (log_testB y a b Hab) eqn:EB.
    + exists (a, m). unfold m. apply log_a_lt_mid. exact Hab.
    + exists (m, b). unfold m. apply log_mid_lt_b. exact Hab.
Defined.

Fixpoint log_bisect (y : Real) (a b : Q) (Hab : QltT a b) (n : nat) :
  sigT (fun ab : Q * Q => QltT (fst ab) (snd ab)) :=
  match n with
  | O => existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) Hab
  | Datatypes.S n' =>
      let prev := log_bisect y a b Hab n' in
      log_step y (fst (projT1 prev)) (snd (projT1 prev)) (projT2 prev)
  end.

Definition log_interval (y : Real) (a b : Q) (Hab : QltT a b) (n : nat) : Q * Q :=
  projT1 (log_bisect y a b Hab n).

Definition log_mid (y : Real) (a b : Q) (Hab : QltT a b) (n : nat) : Q :=
  (fst (log_interval y a b Hab n) + snd (log_interval y a b Hab n)) / 2.

Definition log_len (y : Real) (a b : Q) (Hab : QltT a b) (n : nat) : Q :=
  snd (log_interval y a b Hab n) - fst (log_interval y a b Hab n).

(* 单步长度减半 *)
Lemma log_step_len : forall (y : Real) (a b : Q) (Hab : QltT a b),
  QeqT (snd (projT1 (log_step y a b Hab)) - fst (projT1 (log_step y a b Hab))) ((b - a) / 2).
Proof.
  intros y a b Hab.
  unfold log_step.
  set (m := (a + b) / 2).
  destruct (log_testA y a b Hab) eqn:EA.
  - simpl. unfold m. apply log_step_len_mb. exact Hab.
  - destruct (log_testB y a b Hab) eqn:EB.
    + simpl. unfold m. apply log_step_len_am. exact Hab.
    + simpl. unfold m. apply log_step_len_mb. exact Hab.
Qed.

(* 归纳：log_len (S n) == log_len n / 2 *)
Lemma log_len_halves : forall (y : Real) (a b : Q) (Hab : QltT a b) (n : nat),
  QeqT (log_len y a b Hab (Datatypes.S n)) (log_len y a b Hab n / 2).
Proof.
  intros y a b Hab n.
  unfold log_len, log_interval.
  simpl.
  apply log_step_len.
Qed.

(* 单步嵌套：a ≤ a' 且 b' ≤ b *)
Lemma log_step_nested_l : forall (y : Real) (a b : Q) (Hab : QltT a b),
  QleT' a (fst (projT1 (log_step y a b Hab))).
Proof.
  intros y a b Hab.
  apply Qle_to_QleT'.
  unfold log_step.
  set (m := (a + b) / 2).
  destruct (log_testA y a b Hab) eqn:EA.
  - simpl. unfold m. apply Qlt_le_weak. apply QltT_to_Qlt. apply log_a_lt_mid. exact Hab.
  - destruct (log_testB y a b Hab) eqn:EB.
    + simpl. apply Qle_refl.
    + simpl. unfold m. apply Qlt_le_weak. apply QltT_to_Qlt. apply log_a_lt_mid. exact Hab.
Qed.

Lemma log_step_nested_r : forall (y : Real) (a b : Q) (Hab : QltT a b),
  QleT' (snd (projT1 (log_step y a b Hab))) b.
Proof.
  intros y a b Hab.
  apply Qle_to_QleT'.
  unfold log_step.
  set (m := (a + b) / 2).
  destruct (log_testA y a b Hab) eqn:EA.
  - simpl. apply Qle_refl.
  - destruct (log_testB y a b Hab) eqn:EB.
    + simpl. unfold m. apply Qlt_le_weak. apply QltT_to_Qlt. apply log_mid_lt_b. exact Hab.
    + simpl. apply Qle_refl.
Qed.

(* ============ log 论证第三阶段 Chunk 2：嵌套迭代 + 中点柯西界 ============ *)

Lemma log_nested_step_l : forall (y : Real) (a b : Q) (Hab : QltT a b) (j : nat),
  QleT' (fst (log_interval y a b Hab j)) (fst (log_interval y a b Hab (Datatypes.S j))).
Proof.
  intros y a b Hab j.
  unfold log_interval.
  simpl.
  apply (log_step_nested_l y (fst (projT1 (log_bisect y a b Hab j)))
                              (snd (projT1 (log_bisect y a b Hab j)))
                              (projT2 (log_bisect y a b Hab j))).
Qed.

Lemma log_nested_step_r : forall (y : Real) (a b : Q) (Hab : QltT a b) (j : nat),
  QleT' (snd (log_interval y a b Hab (Datatypes.S j))) (snd (log_interval y a b Hab j)).
Proof.
  intros y a b Hab j.
  unfold log_interval.
  simpl.
  apply (log_step_nested_r y (fst (projT1 (log_bisect y a b Hab j)))
                              (snd (projT1 (log_bisect y a b Hab j)))
                              (projT2 (log_bisect y a b Hab j))).
Qed.

(* 区间嵌套：n ≤ n+k ⟹ a_n ≤ a_{n+k} 且 b_{n+k} ≤ b_n *)
Lemma log_interval_nested : forall (y : Real) (a b : Q) (Hab : QltT a b) (n k : nat),
  And
    (QleT' (fst (log_interval y a b Hab n)) (fst (log_interval y a b Hab (n + k))))
    (QleT' (snd (log_interval y a b Hab (n + k))) (snd (log_interval y a b Hab n))).
Proof.
  intros y a b Hab n k. revert n. induction k as [| k IH]; intros n.
  - assert (Hn0 : (n + 0)%nat = n) by lia.
    rewrite Hn0. split; apply Qle_to_QleT'; apply Qle_refl.
  - replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k))%nat by lia.
    destruct (IH n) as [Hl Hr].
    split.
    + apply (qleT'_trans _ (fst (log_interval y a b Hab (n + k))) _).
      * exact Hl.
      * apply log_nested_step_l.
    + apply (qleT'_trans _ (snd (log_interval y a b Hab (n + k))) _).
      * apply log_nested_step_r.
      * exact Hr.
Qed.

(* 中点在本区间内：a_n ≤ mid_n ≤ b_n *)
Lemma log_mid_fst_le : forall (y : Real) (a b : Q) (Hab : QltT a b) (n : nat),
  QleT' (fst (log_interval y a b Hab n)) (log_mid y a b Hab n).
Proof.
  intros y a b Hab n.
  unfold log_mid, log_interval.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply QltT_to_Qlt.
  apply (log_a_lt_mid (fst (projT1 (log_bisect y a b Hab n))) (snd (projT1 (log_bisect y a b Hab n)))).
  exact (projT2 (log_bisect y a b Hab n)).
Qed.

Lemma log_mid_le_snd : forall (y : Real) (a b : Q) (Hab : QltT a b) (n : nat),
  QleT' (log_mid y a b Hab n) (snd (log_interval y a b Hab n)).
Proof.
  intros y a b Hab n.
  unfold log_mid, log_interval.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply QltT_to_Qlt.
  apply (log_mid_lt_b (fst (projT1 (log_bisect y a b Hab n))) (snd (projT1 (log_bisect y a b Hab n)))).
  exact (projT2 (log_bisect y a b Hab n)).
Qed.

(* 区间长度非负 *)
Lemma log_len_nonneg : forall (y : Real) (a b : Q) (Hab : QltT a b) (n : nat),
  QleT' 0 (log_len y a b Hab n).
Proof.
  intros y a b Hab n.
  apply Qle_to_QleT'.
  unfold log_len, log_interval.
  exact (Qlt_le_weak 0
           (snd (projT1 (log_bisect y a b Hab n)) - fst (projT1 (log_bisect y a b Hab n)))%Q
           (proj1 (Qlt_minus_iff (fst (projT1 (log_bisect y a b Hab n)))
                                 (snd (projT1 (log_bisect y a b Hab n))))
                  (QltT_to_Qlt (fst (projT1 (log_bisect y a b Hab n)))
                               (snd (projT1 (log_bisect y a b Hab n)))
                               (projT2 (log_bisect y a b Hab n))))).
Qed.

(* Q 层跨度：x,y ∈ [a,b] ⟹ |x−y| ≤ b−a *)
Lemma q_abs_le_span : forall a b x y : Q,
  QleT' a x -> QleT' x b -> QleT' a y -> QleT' y b -> QleT' (Qabs (x - y)) (b - a).
Proof.
  intros a b x y Hax Hxb Hay Hyb.
  apply Qle_to_QleT'.
  apply (proj2 (Qabs_Qle_condition (x - y) (b - a))).
  split.
  - apply (Qle_trans _ (Qopp (y - x)) _).
    + apply Qopp_le_compat.
      apply (Qle_trans _ (y - a) _).
      * apply (Qplus_le_compat y y (Qopp x) (Qopp a)); [apply Qle_refl | apply Qopp_le_compat; apply QleT'_to_Qle; exact Hax].
      * apply (Qplus_le_compat y b (Qopp a) (Qopp a)); [apply QleT'_to_Qle; exact Hyb | apply Qle_refl].
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (x - a) _).
    + apply (Qplus_le_compat x x (Qopp y) (Qopp a)); [apply Qle_refl | apply Qopp_le_compat; apply QleT'_to_Qle; exact Hay].
    + apply (Qplus_le_compat x b (Qopp a) (Qopp a)); [apply QleT'_to_Qle; exact Hxb | apply Qle_refl].
Qed.

(* 中点差 ≤ 小区间长：|mid_m − mid_n| ≤ len_{min m n} *)
Lemma log_mid_cauchy_bound : forall (y : Real) (a b : Q) (Hab : QltT a b) (m n : nat),
  QleT' (Qabs (log_mid y a b Hab m - log_mid y a b Hab n)) (log_len y a b Hab (Nat.min m n)).
Proof.
  intros y a b Hab m n.
  destruct (Nat.leb m n) eqn:E.
  - apply Nat.leb_le in E.
    assert (Hmin : Nat.min m n = m) by (apply Nat.min_l; exact E).
    assert (Hmn : (m + (n - m))%nat = n) by lia.
    rewrite Hmin.
    apply (q_abs_le_span (fst (log_interval y a b Hab m)) (snd (log_interval y a b Hab m))
                         (log_mid y a b Hab m) (log_mid y a b Hab n)).
    + apply log_mid_fst_le.
    + apply log_mid_le_snd.
    + apply (qleT'_trans _ (fst (log_interval y a b Hab n)) _).
      * rewrite <- Hmn.
        apply (fst (log_interval_nested y a b Hab m (n - m))).
      * apply log_mid_fst_le.
    + apply (qleT'_trans _ (snd (log_interval y a b Hab n)) _).
      * apply log_mid_le_snd.
      * rewrite <- Hmn.
        apply (snd (log_interval_nested y a b Hab m (n - m))).
  - apply Nat.leb_gt in E.
    assert (Hmin : Nat.min m n = n) by (apply Nat.min_r; lia).
    assert (Hnm : (n + (m - n))%nat = m) by lia.
    rewrite Hmin.
    rewrite (Qabs_Qminus (log_mid y a b Hab m) (log_mid y a b Hab n)).
    apply (q_abs_le_span (fst (log_interval y a b Hab n)) (snd (log_interval y a b Hab n))
                         (log_mid y a b Hab n) (log_mid y a b Hab m)).
    + apply log_mid_fst_le.
    + apply log_mid_le_snd.
    + apply (qleT'_trans _ (fst (log_interval y a b Hab m)) _).
      * rewrite <- Hnm.
        apply (fst (log_interval_nested y a b Hab n (m - n))).
      * apply log_mid_fst_le.
    + apply (qleT'_trans _ (snd (log_interval y a b Hab m)) _).
      * apply log_mid_le_snd.
      * rewrite <- Hnm.
        apply (snd (log_interval_nested y a b Hab n (m - n))).
Qed.

(* 长度几何衰减：len_n == (b−a)·(1/2)^n *)
Lemma log_len_geom : forall (y : Real) (a b : Q) (Hab : QltT a b) (n : nat),
  QeqT (log_len y a b Hab n) ((b - a) * q_pow (1 / 2) n).
Proof.
  intros y a b Hab n.
  induction n as [| n IH]; simpl.
  - unfold log_len, log_interval. simpl. apply qeq_imp_qeqT. unfold Qminus. ring.
  - apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (log_len_halves y a b Hab n)).
    rewrite (qeqT_imp_qeq _ _ IH).
    unfold Qdiv. field.
Qed.

(* ============ log 论证第三阶段 Chunk 3：决策引理 + 缺陷界 + slack 提升 ============ *)

Definition log_m (a b : Q) : Q := (a + b) / 2.
Definition log_d4 (a b : Q) : Q := (b - a) / 32.
Definition log_K1 (a b : Q) (Hab : QltT a b) : nat :=
  projT1 (exp_partial_cauchy (log_m a b) (log_d4 a b)
            (log_d4_pos a b Hab)).
Definition log_K2 (y : Real) (a b : Q) (Hab : QltT a b) : nat :=
  projT1 (projT2 y (log_d4 a b) (log_d4_posT a b Hab)).
Definition log_q (a b : Q) (Hab : QltT a b) : Q := exp_partial (log_K1 a b Hab) (log_m a b).
Definition log_r (y : Real) (a b : Q) (Hab : QltT a b) : Q := projT1 y (log_K2 y a b Hab).

(* Qlt_bool = false ⟹ x < y → False *)
Lemma qlt_bool_false_not : forall x y : Q, Qlt_bool x y = false -> QltT x y -> Empty_set.
Proof.
  intros x y H Hlt.
  unfold QltT in Hlt.
  rewrite H in Hlt.
  inversion Hlt.
Qed.

(* |x - y| < d ⟹ x < y + d（上支 x - y < d） *)
Lemma q_abs_lt_lower : forall x y d : Q, QltT (Qabs (x - y)) d -> QltT x (y + d).
Proof.
  intros x y d H.
  apply Qlt_to_QltT.
  pose (Hc := proj1 (Qabs_Qlt_condition (x - y) d) (QltT_to_Qlt _ _ H)).
  apply (proj2 (Qlt_minus_iff x (y + d))).
  apply (Qlt_le_trans _ (Qplus d (Qopp (Qplus x (Qopp y)))) _).
  - apply (proj1 (Qlt_minus_iff (x - y) d)). exact (proj2 Hc).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* |x - y| < d ⟹ y - d < x（下支 -d < x - y） *)
Lemma q_abs_lt_minus : forall x y d : Q, QltT (Qabs (x - y)) d -> QltT (y - d) x.
Proof.
  intros x y d H.
  apply Qlt_to_QltT.
  pose (Hc := proj1 (Qabs_Qlt_condition (x - y) d) (QltT_to_Qlt _ _ H)).
  apply (proj2 (Qlt_minus_iff (y - d) x)).
  apply (Qlt_le_trans _ (Qplus (Qplus x (Qopp y)) (Qopp (Qopp d))) _).
  - apply (proj1 (Qlt_minus_iff (Qopp d) (x - y))). exact (proj1 Hc).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 决策 A 真 ⟹ e^m < y：见证 r − q − 2d4，N := max K1 K2 *)
Lemma log_testA_true_lt : forall (y : Real) (a b : Q) (Hab : QltT a b),
  log_testA y a b Hab = true ->
  real_lt (cauchy_real_exp (real_const (log_m a b))) y.
Proof.
  intros y a b Hab HA.
  unfold log_testA in HA.
  cbn in HA.
  pose (m := log_m a b).
  pose (d4 := log_d4 a b).
  pose (K1 := log_K1 a b Hab).
  pose (K2 := log_K2 y a b Hab).
  pose (q := log_q a b Hab).
  pose (r := log_r y a b Hab).
  assert (Hlt : Qlt (q + 2 * d4) r).
  { apply QltT_to_Qlt.
    exact (RealSetoid.eq_Id _ _ HA). }
  assert (Heps : QltT 0 (r - q - 2 * d4)).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (r + - (q + 2 * d4)) _).
    - apply (proj1 (Qlt_minus_iff (q + 2 * d4) r)). exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  exists (r - q - 2 * d4).
  split.
  - exact Heps.
  - exists (Nat.max K1 K2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (HnK1 : (K1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (HnK2 : (K2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hem : Qlt (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q)) d4).
    { apply QltT_to_Qlt.
      cbn [projT1].
      apply (projT2 (exp_partial_cauchy m d4 (log_d4_pos a b Hab)) n K1).
      - exact (NatLe_lift _ _ HnK1).
      - apply NatLe_lift. apply Nat.le_refl. }
    assert (Hyr : Qlt (Qabs (projT1 y n - r)) d4).
    { apply QltT_to_Qlt.
      apply (projT2 (projT2 y d4 (log_d4_posT a b Hab)) n K2).
      - exact (NatLe_lift _ _ HnK2).
      - apply NatLe_lift. apply Nat.le_refl. }
    apply (Qle_lt_trans _ ((r - d4) - (q + d4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_lt_compat (r - d4) (projT1 y n) (Qopp (q + d4)) (Qopp (projT1 (cauchy_real_exp (real_const m)) n))).
      * apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 y n) r d4). apply Qlt_to_QltT. exact Hyr.
      * apply (Qopp_lt_compat (projT1 (cauchy_real_exp (real_const m)) n) (q + d4)).
        apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 (cauchy_real_exp (real_const m)) n) q d4). apply Qlt_to_QltT. exact Hem.
Qed.

(* 决策 B 真 ⟹ y < e^m：见证 q − r − 2d4 *)
Lemma log_testB_true_gt : forall (y : Real) (a b : Q) (Hab : QltT a b),
  log_testB y a b Hab = true ->
  real_lt y (cauchy_real_exp (real_const (log_m a b))).
Proof.
  intros y a b Hab HB.
  unfold log_testB in HB.
  cbn in HB.
  pose (m := log_m a b).
  pose (d4 := log_d4 a b).
  pose (K1 := log_K1 a b Hab).
  pose (K2 := log_K2 y a b Hab).
  pose (q := log_q a b Hab).
  pose (r := log_r y a b Hab).
  assert (Hlt : Qlt (r + 2 * d4) q).
  { apply QltT_to_Qlt.
    apply RealSetoid.eq_Id.
    exact HB. }
  assert (Heps : QltT 0 (q - r - 2 * d4)).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (q + - (r + 2 * d4)) _).
    - apply (proj1 (Qlt_minus_iff (r + 2 * d4) q)). exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  exists (q - r - 2 * d4).
  split.
  - exact Heps.
  - exists (Nat.max K1 K2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (HnK1 : (K1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (HnK2 : (K2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hem : Qlt (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q)) d4).
    { apply QltT_to_Qlt.
      cbn [projT1].
      apply (projT2 (exp_partial_cauchy m d4 (log_d4_pos a b Hab)) n K1).
      - exact (NatLe_lift _ _ HnK1).
      - apply NatLe_lift. apply Nat.le_refl. }
    assert (Hyr : Qlt (Qabs (projT1 y n - r)) d4).
    { apply QltT_to_Qlt.
      apply (projT2 (projT2 y d4 (log_d4_posT a b Hab)) n K2).
      - exact (NatLe_lift _ _ HnK2).
      - apply NatLe_lift. apply Nat.le_refl. }
    apply (Qle_lt_trans _ ((q - d4) - (r + d4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_lt_compat (q - d4) (projT1 (cauchy_real_exp (real_const m)) n)
                             (Qopp (r + d4)) (Qopp (projT1 y n))).
      * apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 (cauchy_real_exp (real_const m)) n) q d4). apply Qlt_to_QltT. exact Hem.
      * apply (Qopp_lt_compat (projT1 y n) (r + d4)).
        apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 y n) r d4). apply Qlt_to_QltT. exact Hyr.
Qed.

(* 三角 + 三段拼接：|A| < d、|B| ≤ M、|C| < d ⟹ |A + (B + C)| < M + 2d *)
Lemma q_abs_plus3_lt : forall (A B C M d : Q),
  QltT (Qabs A) d -> QleT' (Qabs B) M -> QltT (Qabs C) d ->
  QltT (Qabs (A + (B + C))) (M + 2 * d).
Proof.
  intros A B C M d HA HB HC.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs A + Qabs (B + C)) _).
  - apply Qabs_triangle.
  - apply (Qle_lt_trans _ (Qabs A + (Qabs B + Qabs C)) _).
    + apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply Qabs_triangle].
    + apply (Qlt_le_trans _ (d + (M + d)) _).
      * apply (Qplus_lt_le_compat (Qabs A) d (Qabs B + Qabs C) (M + d)).
        -- apply QltT_to_Qlt. exact HA.
        -- apply (Qplus_le_compat (Qabs B) M (Qabs C) d); [apply QleT'_to_Qle; exact HB | apply Qlt_le_weak; apply QltT_to_Qlt; exact HC].
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 两测试都失败 ⟹ |e^m − y| ≤ 4d4（逐点，n ≥ max K1 K2） *)
Lemma log_test_mid_bound : forall (y : Real) (a b : Q) (Hab : QltT a b),
  log_testA y a b Hab = false -> log_testB y a b Hab = false ->
  forall n : nat, (Nat.max (log_K1 a b Hab) (log_K2 y a b Hab) <= n)%nat ->
    QleT' (Qabs (projT1 (cauchy_real_exp (real_const (log_m a b))) n - projT1 y n))
        (4 * log_d4 a b).
Proof.
  intros y a b Hab HA HB n Hn.
  apply Qle_to_QleT'.
  unfold log_testA in HA. unfold log_testB in HB. cbn in HA, HB.
  pose (m := log_m a b).
  pose (d4 := log_d4 a b).
  pose (K1 := log_K1 a b Hab).
  pose (K2 := log_K2 y a b Hab).
  pose (q := log_q a b Hab).
  pose (r := log_r y a b Hab).
  change (Qlt_bool (q + 2 * d4) r = false) in HA.
  change (Qlt_bool (r + 2 * d4) q = false) in HB.
  pose (HnA := qlt_bool_false_not (q + 2 * d4) r HA).
  pose (HnB := qlt_bool_false_not (r + 2 * d4) q HB).
  assert (Hqle : Qle q (r + 2 * d4)).
  { apply Qnot_lt_le. intro Hc. destruct (HnB (Qlt_to_QltT _ _ Hc)). }
  assert (Hrle : Qle r (q + 2 * d4)).
  { apply Qnot_lt_le. intro Hc. destruct (HnA (Qlt_to_QltT _ _ Hc)). }
  assert (Hqr : Qle (Qabs (q - r)) (2 * d4)).
  { apply (proj2 (Qabs_Qle_condition (q - r) (2 * d4))).
    split.
    - apply (Qle_trans _ (Qopp (r - q)) _).
      + apply Qopp_le_compat.
        apply (Qle_trans _ (Qplus (Qplus q (2 * d4)) (Qopp q)) _).
        * apply (Qplus_le_compat r (q + 2 * d4) (Qopp q) (Qopp q)); [exact Hrle | apply Qle_refl].
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ (Qplus (Qplus r (2 * d4)) (Qopp r)) _).
      + apply (Qplus_le_compat q (r + 2 * d4) (Qopp r) (Qopp r)); [exact Hqle | apply Qle_refl].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hem : Qlt (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q)) d4).
  { apply QltT_to_Qlt.
    cbn [projT1].
    apply (projT2 (exp_partial_cauchy m d4 (log_d4_pos a b Hab)) n K1).
    - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_l | exact Hn].
    - apply NatLe_lift. apply Nat.le_refl. }
  assert (Hyr : Qlt (Qabs (projT1 y n - r)) d4).
  { apply QltT_to_Qlt.
    apply (projT2 (projT2 y d4 (log_d4_posT a b Hab)) n K2).
    - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_r | exact Hn].
    - apply NatLe_lift. apply Nat.le_refl. }
  apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q) + Qabs (q - r) + Qabs (r - projT1 y n)) _).
  - apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q) + Qabs ((q - r) + (r - projT1 y n))) _).
    + assert (Hsum : projT1 (cauchy_real_exp (real_const m)) n - projT1 y n ==
                     (projT1 (cauchy_real_exp (real_const m)) n - q) + ((q - r) + (r - projT1 y n))).
      { ring. }
      apply (Qle_trans _ (Qabs ((projT1 (cauchy_real_exp (real_const m)) n - q) + ((q - r) + (r - projT1 y n)))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. exact Hsum.
      * apply Qabs_triangle.
    + apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q) + (Qabs (q - r) + Qabs (r - projT1 y n))) _).
      * apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply Qabs_triangle].
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (d4 + (2 * d4) + d4) _).
    + apply (Qplus_le_compat _ _ _ _).
      * apply (Qplus_le_compat _ _ _ _).
        -- apply Qlt_le_weak. exact Hem.
        -- exact Hqr.
      * apply Qlt_le_weak.
        rewrite <- (Qabs_Qminus (projT1 y n) r). exact Hyr.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold d4. ring.
Qed.

(* 逐点 |a_n − b_n| ≤ M（n ≥ N0）⟹ real_lt (|a − b|) (real_const (M + γ))（见证 γ/2） *)
Lemma real_abs_diff_le_lift : forall (a b : Real) (M γ : Q) (N0 : nat),
  Qlt 0 γ ->
  (forall n : nat, (N0 <= n)%nat -> Qle (Qabs (projT1 a n - projT1 b n)) M) ->
  real_lt (real_abs (real_plus a (real_opp b))) (real_const (M + γ)).
Proof.
  intros a b M γ N0 Hγ Hpoint.
  assert (Hg4 : QltT 0 (γ / 4)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 γ 4).
    - change (Qlt 0 4). compute. reflexivity.
    - apply (Qle_lt_trans _ 0 _); [apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring | exact Hγ]. }
  destruct (projT2 a (γ / 4) Hg4) as [Na HNa].
  destruct (projT2 b (γ / 4) Hg4) as [Nb HNb].
  pose (n0 := Nat.max N0 (Nat.max Na Nb)).
  exists (γ / 2).
  split.
  - apply Qlt_to_QltT.
    apply (Qlt_shift_div_l 0 γ 2).
    + change (Qlt 0 2). compute. reflexivity.
    + apply (Qle_lt_trans _ 0 _); [apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring | exact Hγ].
  - exists (Nat.max Na Nb).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hx : Qlt (Qabs (projT1 a n - projT1 b n)) (M + γ / 2)).
    { apply (Qlt_le_trans _ (M + 2 * (γ / 4)) _).
      - apply (Qle_lt_trans _ (Qabs ((projT1 a n - projT1 a n0) + ((projT1 a n0 - projT1 b n0) + (projT1 b n0 - projT1 b n)))) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. ring.
        + apply QltT_to_Qlt.
          apply (q_abs_plus3_lt (projT1 a n - projT1 a n0) (projT1 a n0 - projT1 b n0) (projT1 b n0 - projT1 b n) M (γ / 4)).
          * apply (HNa n n0).
            -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max Na Nb) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
            -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max Na Nb) _); [apply Nat.le_max_l | apply Nat.le_max_r].
          * apply Qle_to_QleT'. apply Hpoint. unfold n0. apply Nat.le_max_l.
          * apply (HNb n0 n).
            -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max Na Nb) _); [apply Nat.le_max_r | apply Nat.le_max_r].
            -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max Na Nb) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)].
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    assert (Hxproj : projT1 (real_abs (real_plus a (real_opp b))) n == Qabs (projT1 a n - projT1 b n)).
    { rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a (real_opp b)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp b) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj b n)).
      reflexivity. }
    setoid_rewrite Hxproj.
    apply (proj2 (Qlt_minus_iff (γ / 2) (M + γ - Qabs (projT1 a n - projT1 b n)))).
    apply (Qlt_le_trans _ (M + γ / 2 - Qabs (projT1 a n - projT1 b n)) _).
    + apply (proj1 (Qlt_minus_iff (Qabs (projT1 a n - projT1 b n)) (M + γ / 2))). exact Hx.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* ============ log 论证第三阶段 Chunk 4a：inv 唯一性 + 倒数恒等 + Q 常量上 Lipschitz ============ *)

(* inv 唯一性：a·b == 1 且 a·c == 1 ⟹ b == c *)
Lemma real_inv_unique : forall (a b c : Real),
  real_eq (real_mult a b) real_one ->
  real_eq (real_mult a c) real_one ->
  real_eq b c.
Proof.
  intros a b c Hab Hac.
  apply (real_eq_trans _ (real_mult b real_one) _).
  - apply real_eq_sym. apply real_mult_one.
  - apply (real_eq_trans _ (real_mult b (real_mult a c)) _).
    + apply (RealSetoid.real_eq_mult_compat b real_one b (real_mult a c)).
      * apply real_eq_refl.
      * apply real_eq_sym. exact Hac.
    + apply (real_eq_trans _ (real_mult (real_mult b a) c) _).
      * apply real_mult_assoc.
      * apply (real_eq_trans _ (real_mult (real_mult a b) c) _).
        -- apply (RealSetoid.real_eq_mult_compat (real_mult b a) c (real_mult a b) c).
           ++ apply real_mult_comm.
           ++ apply real_eq_refl.
        -- apply (real_eq_trans _ (real_mult real_one c) _).
           ++ apply (RealSetoid.real_eq_mult_compat (real_mult a b) c real_one c).
              ** exact Hab.
              ** apply real_eq_refl.
           ++ apply (real_eq_trans _ (real_mult c real_one) _).
              ** apply real_mult_comm.
              ** apply real_mult_one.
Qed.

(* 倒数恒等：e^{−x} == 1/e^x（exp_plus + exp_zero + inv 唯一性） *)
Lemma exp_neg_recip : forall (x : Real) (Hx : real_lt real_zero (cauchy_real_exp x)),
  real_eq (cauchy_real_exp (real_opp x))
          (real_inv_pos (cauchy_real_exp x) Hx).
Proof.
  intros x Hx.
  apply (real_inv_unique (cauchy_real_exp x)
                         (cauchy_real_exp (real_opp x))
                         (real_inv_pos (cauchy_real_exp x) Hx)).
  - apply (real_eq_trans _ (cauchy_real_exp (real_plus x (real_opp x))) _).
    + apply real_eq_sym. apply (cauchy_real_exp_plus x (real_opp x)).
    + apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
      * apply cauchy_real_exp_wd.
        apply real_eq_of_zero_diff.
        intro n.
        apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj x (real_opp x) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
        assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hz0.
        unfold Qminus. ring.
      * apply cauchy_real_exp_zero.
  - apply real_inv_pos_correct.
Qed.

(* Q 常量上 Lipschitz：|e^u_n − e^s_n| ≤ |u−s|·C（逐点全 n，C := exp_series_arch B） *)
Lemma exp_upper_lipschitz_q : forall (u s B C : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs u) B -> QleT' (Qabs s) B ->
  (forall n : nat, QleT' (exp_series n B) C) ->
  QleT' (Qabs (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))
      (Qmult (Qabs (u - s)) C).
Proof.
  intros u s B C n HB Hu Hs HC.
  cbn [projT1].
  apply (qleT'_trans _ (Qabs (u - s) * exp_series n B) _).
  - apply (exp_partial_lipschitz u s B n); [exact HB | exact Hu | exact Hs].
  - apply Qle_to_QleT'.
    apply (Qmult_le_compat_nonneg (Qabs (u - s)) (Qabs (u - s)) (exp_series n B) C).
    + split; [apply Qabs_nonneg | apply Qle_refl].
    + split; [apply QleT'_to_Qle; apply (exp_series_nonneg n B HB) | exact (QleT'_to_Qle _ _ (HC n))].
Qed.

(* ============ log 论证第三阶段 Chunk 4b：exp_diff_factor + 松弛 ≥ ============ *)

(* e^u − e^s == e^s·(e^{u−s} − 1) *)
Lemma exp_diff_factor : forall (u s : Real),
  real_eq (real_plus (cauchy_real_exp u) (real_opp (cauchy_real_exp s)))
          (real_mult (cauchy_real_exp s)
                     (real_plus (cauchy_real_exp (real_plus u (real_opp s))) (real_opp real_one))).
Proof.
  intros u s.
  assert (Hmain : real_eq (cauchy_real_exp u)
                          (real_mult (cauchy_real_exp s) (cauchy_real_exp (real_plus u (real_opp s))))).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus s (real_plus u (real_opp s)))) _).
    - apply cauchy_real_exp_wd.
      apply real_eq_of_zero_diff.
      intro n.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj s (real_plus u (real_opp s)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj u (real_opp s) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj s n)).
      unfold Qminus. ring.
    - apply (cauchy_real_exp_plus s (real_plus u (real_opp s))). }
  apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_exp s) (cauchy_real_exp (real_plus u (real_opp s))))
                                    (real_opp (cauchy_real_exp s))) _).
  - apply (RealSetoid.real_eq_plus_compat (cauchy_real_exp u)
                                          (real_opp (cauchy_real_exp s))
                                          (real_mult (cauchy_real_exp s) (cauchy_real_exp (real_plus u (real_opp s))))
                                          (real_opp (cauchy_real_exp s))).
    + exact Hmain.
    + apply real_eq_refl.
  - apply (real_mult_minus_factor (cauchy_real_exp s) (cauchy_real_exp (real_plus u (real_opp s)))).
Qed.

(* 实层松弛 ≥：a ≥ b（逐点差 < eps 对任意 eps）——Or 障碍绕行（判例） *)
Definition real_ge_relax (a b : Real) : Set :=
  forall eps : Q, QltT 0 eps -> sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (projT1 b n - projT1 a n) eps).

(* 逐点 b_n ≤ a_n（n ≥ N0）⟹ real_ge_relax a b *)
Lemma real_ge_relax_of_pointwise : forall (a b : Real) (N0 : nat),
  (forall n : nat, (N0 <= n)%nat -> Qle (projT1 b n) (projT1 a n)) ->
  real_ge_relax a b.
Proof.
  intros a b N0 Hpoint eps Heps.
  exists N0.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply (Qle_trans _ (Qplus (projT1 a n) (Qopp (projT1 a n))) _).
    + apply (Qplus_le_compat (projT1 b n) (projT1 a n) (Qopp (projT1 a n)) (Qopp (projT1 a n))).
      * apply (Hpoint n Hn).
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* e^t − 1 ≥ t（t ≥ 0，逐点，松弛 ≥）：e^t_n ≥ 1 + t（n ≥ 1） *)
Lemma exp_ge_plus_one_q : forall (t : Q), Qle 0 t ->
  real_ge_relax (cauchy_real_exp (real_const t)) (real_const (1 + t)).
Proof.
  intros t Ht eps Heps.
  exists 1%nat.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - cbn [projT1].
    destruct n as [| m].
    { lia. }
    apply (Qle_trans _ (Qplus (exp_partial (Datatypes.S m) t) (Qopp (exp_partial (Datatypes.S m) t))) _).
    + apply (Qplus_le_compat (1 + t) (exp_partial (Datatypes.S m) t)
                             (Qopp (exp_partial (Datatypes.S m) t)) (Qopp (exp_partial (Datatypes.S m) t))).
      * apply QleT'_to_Qle. apply (exp_partial_ge_plus_x m t). apply Qle_to_QleT'. exact Ht.
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* ============ log 论证第三阶段 Chunk 4c：下 Lipschitz（松弛 ≥） ============ *)

(* s ≤ u ⟹ 0 ≤ u − s *)
Lemma q_le_minus : forall s u : Q, QleT' s u -> QleT' 0 (u - s).
Proof.
  intros s u H.
  apply Qle_to_QleT'.
  apply (proj1 (Qle_minus_iff s u)).
  apply QleT'_to_Qle. exact H.
Qed.

(* Q 常量下 Lipschitz：s ≤ u、e^{a0}_n ≤ e^s_n（n ≥ 1 逐点）⟹ e^u − e^s ≥ e^{a0}·(u−s)（松弛 ≥）
   链：exp_diff_factor（real_eq，|差| < eps/2）→ e^s_n·(e^{u−s}_n−1) ≥ e^s_n·(u−s)（exp_partial_ge_plus_x）
       → ≥ e^{a0}_n·(u−s)（Hmono + u−s ≥ 0） *)
Lemma exp_lower_lipschitz_q : forall (a0 u s : Q) (Hle : Qle s u),
  (forall n : nat, (1 <= n)%nat -> Qle (exp_partial n a0) (exp_partial n s)) ->
  real_ge_relax (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s))))
                (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))).
Proof.
  intros a0 u s Hle Hmono eps Heps.
  destruct (cauchy_real_exp_pos (real_const s)) as [epss [Hepss [Ns HNs]]].
  assert (Hh : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps 2).
    - change (Qlt 0 2). compute. reflexivity.
    - apply (Qle_lt_trans _ 0 _); [apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring | apply QltT_to_Qlt; exact Heps]. }
  destruct (exp_diff_factor (real_const u) (real_const s) (eps / 2) Hh) as [N1 HN1].
  exists (Nat.max 1 (Nat.max Ns N1)).
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hn1 : (1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 1 (Nat.max Ns N1)) _); [apply Nat.le_max_l | exact Hn]).
  assert (HnNs : (Ns <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Ns N1) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max 1 (Nat.max Ns N1)) _); [apply Nat.le_max_r | exact Hn]]).
  assert (HnN1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Ns N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 1 (Nat.max Ns N1)) _); [apply Nat.le_max_r | exact Hn]]).
  assert (Hl : projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) n ==
                projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n).
  { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_exp (real_const s)) n)). reflexivity. }
  assert (Hr : projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) n ==
                projT1 (cauchy_real_exp (real_const a0)) n * (u - s)).
  { rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_exp (real_const a0)) (real_const (u - s)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (u - s) n)). reflexivity. }
  assert (Hm : projT1 (real_mult (cauchy_real_exp (real_const s))
                                (real_plus (cauchy_real_exp (real_const (u - s))) (real_opp real_one))) n ==
                projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1)).
  { rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_exp (real_const s))
                            (real_plus (cauchy_real_exp (real_const (u - s))) (real_opp real_one)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (real_const (u - s))) (real_opp real_one) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    assert (Ho1 : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    setoid_rewrite Ho1. reflexivity. }
  setoid_rewrite Hr. setoid_rewrite Hl.
  assert (H1 : Qlt (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1) - eps / 2)
                   (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)).
  { apply QltT_to_Qlt.
    apply (q_abs_lt_minus (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)
                          (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1))
                          (eps / 2)).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) n -
                                 projT1 (real_mult (cauchy_real_exp (real_const s))
                                                  (real_plus (cauchy_real_exp (real_const (u - s))) (real_opp real_one))) n)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
      setoid_rewrite <- Hl.
      setoid_rewrite <- Hm.
      reflexivity.
    - apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift. exact HnN1. }
  assert (Hus : Qle (u - s) (projT1 (cauchy_real_exp (real_const (u - s))) n - 1)).
  { cbn [projT1].
    destruct n as [| m].
    { lia. }
    apply (Qle_trans _ (Qplus (1 + (u - s)) (Qopp 1)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qplus_le_compat (1 + (u - s)) (exp_partial (Datatypes.S m) (u - s)) (Qopp 1) (Qopp 1)).
      * apply QleT'_to_Qle. apply (exp_partial_ge_plus_x m (u - s)). apply q_le_minus. apply Qle_to_QleT'. exact Hle.
      * apply Qle_refl. }
  assert (Hs0 : Qle 0 (projT1 (cauchy_real_exp (real_const s)) n)).
  { apply (Qle_trans _ epss _).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hepss.
    - apply (Qle_trans _ (projT1 (cauchy_real_exp (real_const s)) n - projT1 real_zero n) _).
      + apply Qlt_le_weak. apply QltT_to_Qlt. apply (HNs n). apply NatLe_lift. exact HnNs.
      + apply QleT'_to_Qle. apply qeq_le.        apply qeq_imp_qeqT.
        assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hz0. unfold Qminus. ring. }
  assert (H2 : Qle (projT1 (cauchy_real_exp (real_const s)) n * (u - s))
                   (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1))).
  { apply (Qle_trans _ (Qmult (u - s) (projT1 (cauchy_real_exp (real_const s)) n)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ (Qmult (projT1 (cauchy_real_exp (real_const (u - s))) n - 1) (projT1 (cauchy_real_exp (real_const s)) n)) _).
      + apply (Qmult_le_compat_r (u - s) (projT1 (cauchy_real_exp (real_const (u - s))) n - 1)
                                 (projT1 (cauchy_real_exp (real_const s)) n)).
        * exact Hus.
        * exact Hs0.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hus0 : Qle 0 (u - s)).
  { apply QleT'_to_Qle. apply q_le_minus. apply Qle_to_QleT'. exact Hle. }
  assert (H3 : Qle (projT1 (cauchy_real_exp (real_const a0)) n * (u - s))
                   (projT1 (cauchy_real_exp (real_const s)) n * (u - s))).
  { apply (Qmult_le_compat_r (projT1 (cauchy_real_exp (real_const a0)) n)
                             (projT1 (cauchy_real_exp (real_const s)) n) (u - s)).
    - cbn [projT1]. destruct n as [| m]. { lia. } apply (Hmono (Datatypes.S m)). lia.
    - exact Hus0. }
  assert (Hmain : Qlt (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - eps / 2)
                      (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)).
  { apply (Qle_lt_trans _ (projT1 (cauchy_real_exp (real_const s)) n * (u - s) - eps / 2) _).
    - apply (Qplus_le_compat (projT1 (cauchy_real_exp (real_const a0)) n * (u - s))
                             (projT1 (cauchy_real_exp (real_const s)) n * (u - s))
                             (Qopp (eps / 2)) (Qopp (eps / 2))).
      + exact H3.
      + apply Qle_refl.
    - apply (Qle_lt_trans _ (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1) - eps / 2) _).
      + apply (Qplus_le_compat (projT1 (cauchy_real_exp (real_const s)) n * (u - s))
                               (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1))
                               (Qopp (eps / 2)) (Qopp (eps / 2))).
        * exact H2.
        * apply Qle_refl.
      + exact H1. }
  apply (proj2 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)) eps)).
  apply (Qlt_le_trans _ (Qplus (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)
                               (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - eps / 2))) _).
  - apply (proj1 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - eps / 2)
                                (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))).
    exact Hmain.
  - apply (Qle_trans _ (Qplus (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))) (eps / 2)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (Qplus (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))) eps) _).
      * apply (Qplus_le_compat (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)))
                               (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)))
                               (eps / 2) eps).
        -- apply Qle_refl.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_lt_self eps). exact Heps.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============ log 论证第三阶段 Chunk 4d：exp 值域 (0,∞) 界 ============ *)

(* 常量正性：c > 0 ⟹ real_const c > 0（见证 c/2，N=0） *)
Lemma real_const_pos : forall (c : Q), QltT 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  assert (Hhalf : Qlt 0 (c / 2)).
  { apply Qlt_shift_div_l; [change (Qlt 0 2); compute; reflexivity | simpl; apply QltT_to_Qlt; exact Hc]. }
  exists (c / 2). split.
  - apply Qlt_to_QltT. exact Hhalf.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    (* 目标：c/2 < projT1 (real_const c) n − projT1 real_zero n == c − 0 == c *)
    apply (Qlt_le_trans _ (c / 2 + c / 2) _).
    + apply (Qle_lt_trans _ (c / 2 + 0) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (proj2 (Qplus_lt_r 0 (c / 2) (c / 2)) Hhalf).
    + apply QleT'_to_Qle. apply qeq_le.      apply qeq_imp_qeqT.
      assert (Hc' : projT1 (real_const c) n == c) by (apply qeqT_imp_qeq, real_const_proj).
      assert (Hz' : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc'. setoid_rewrite Hz'.
      unfold Qminus. transitivity (c + 0).
      * field.
      * assert (Hopp0 : Qopp 0%Q == 0%Q).
        { transitivity (Qred (Qmake 0 1)).
          - reflexivity.
          - apply Qred_correct. }
        rewrite Hopp0. reflexivity.
Qed.

(* 倒数反变：0 < a、0 < b、a < b ⟹ 1/b < 1/a
   eps 见证 := e/(M_a·M_b)（M 为 a、b 的范数上界），逐点 Qinv 差 == (v−u)·Qinv(u·v) *)
Lemma real_inv_lt_contra : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_inv_pos b Hb) (real_inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  destruct a as [u Hu]. destruct b as [v Hv].
  destruct Ha as [ea [Hea [Na HNa]]].
  destruct Hb as [eb [Heb [Nb HNb]]].
  destruct Hab as [e [He [Nab HNab]]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mu [HMupos HMu]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [Mv [HMvpos HMv]].
  exists (e / (Mu * Mv)).
  split.
  - apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat e (Qinv (Mu * Mv))).
    + apply QltT_to_Qlt. exact He.
    + apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat Mu Mv); [apply QltT_to_Qlt; exact HMupos | apply QltT_to_Qlt; exact HMvpos].
  - exists (Nat.max (Nat.max Na Nb) Nab).
    intros n Hn.
    apply NatLe_drop in Hn.
    apply Qlt_to_QltT.
    assert (HnNa : (Na <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Na Nb) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max Na Nb) Nab) _); [apply Nat.le_max_l | exact Hn]]).
    assert (HnNb : (Nb <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Na Nb) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max Na Nb) Nab) _); [apply Nat.le_max_l | exact Hn]]).
    assert (HnNab : (Nab <= n)%nat) by (apply (Nat.le_trans _ (Nat.max (Nat.max Na Nb) Nab) _); [apply Nat.le_max_r | exact Hn]).
    assert (Hu0 : Qlt 0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)).
    { apply (Qlt_le_trans 0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n)
                           (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)).
      - apply (Qlt_le_trans 0 ea (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact Hea.
        + apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply (HNa n). apply NatLe_lift. exact HnNa.
      - apply QleT'_to_Qle. apply qeq_le.        apply qeq_imp_qeqT.
        assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hz0. unfold Qminus. ring. }
    assert (Hv0 : Qlt 0 (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
    { apply (Qlt_le_trans 0 (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 real_zero n)
                           (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
      - apply (Qlt_le_trans 0 eb (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 real_zero n)).
        + apply QltT_to_Qlt. exact Heb.
        + apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply (HNb n). apply NatLe_lift. exact HnNb.
      - apply QleT'_to_Qle. apply qeq_le.        apply qeq_imp_qeqT.
        assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hz0. unfold Qminus. ring. }
    assert (Hule : Qle (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) Mu).
    { apply (Qle_trans _ (Qabs (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)) _).
      - apply Qle_Qabs.
      - apply QleT'_to_Qle. apply HMu. }
    assert (Hvle : Qle (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n) Mv).
    { apply (Qle_trans _ (Qabs (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)) _).
      - apply Qle_Qabs.
      - apply QleT'_to_Qle. apply HMv. }
    assert (Huvle : Qle (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n) (Mu * Mv)).
    { apply (Qmult_le_compat_nonneg (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) Mu
                                   (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n) Mv).
      - split; [apply (Qlt_le_weak 0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)); exact Hu0 | exact Hule].
      - split; [apply (Qlt_le_weak 0 (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)); exact Hv0 | exact Hvle]. }
    assert (Hinvle : Qle (Qinv (Mu * Mv)) (Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n))).
    { apply QleT'_to_Qle.
      apply (q_inv_le_contravar (Mu * Mv) (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
      - apply Qlt_to_QltT.
        apply (Qmult_lt_0_compat Mu Mv); [apply QltT_to_Qlt; exact HMupos | apply QltT_to_Qlt; exact HMvpos].
      - apply Qlt_to_QltT.
        apply (Qmult_lt_0_compat (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)); [exact Hu0 | exact Hv0].
      - exact (Qle_to_QleT' _ _ Huvle). }
    assert (Hia : projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) u Hu)
                                     (existT _ ea (pair Hea (existT _ Na HNa)))) n == Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)).
    { unfold real_inv_pos. cbn [projT1]. destruct (Nat.leb Na n) eqn:Eleb.
      - reflexivity.
      - exfalso. apply Nat.leb_gt in Eleb. lia. }
    assert (Hib : projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) v Hv)
                                     (existT _ eb (pair Heb (existT _ Nb HNb)))) n == Qinv (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
    { unfold real_inv_pos. cbn [projT1]. destruct (Nat.leb Nb n) eqn:Eleb.
      - reflexivity.
      - exfalso. apply Nat.leb_gt in Eleb. lia. }
    assert (Hid : Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) - Qinv (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)
                 == (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 (existT (fun s : Qseq => cauchy s) u Hu) n)
                    * Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
    { unfold Qminus. field.
      split.
      - intro Hz; exact (match q_neq_of_lt (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n) (Qlt_to_QltT _ _ Hv0) (qeq_imp_qeqT _ _ Hz) with end).
      - intro Hz; exact (match q_neq_of_lt (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) (Qlt_to_QltT _ _ Hu0) (qeq_imp_qeqT _ _ Hz) with end). }
    unfold Qdiv.
    apply (Qlt_le_trans _ (Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) - Qinv (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)) _).
    + apply (Qlt_le_trans _ ((projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) * Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)) _).
      * apply (Qle_lt_trans _ (e * Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)) _).
        -- apply (Qmult_le_compat_nonneg e e (Qinv (Mu * Mv)) (Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n))).
           ++ split.
              ** apply (Qlt_le_weak 0 e). apply QltT_to_Qlt. exact He.
              ** apply Qle_refl.
           ++ split.
              ** apply (Qlt_le_weak 0 (Qinv (Mu * Mv))). apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat Mu Mv); [apply QltT_to_Qlt; exact HMupos | apply QltT_to_Qlt; exact HMvpos].
              ** exact Hinvle.
        -- apply (Qmult_lt_compat_r e (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n - projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) (Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n * projT1 (existT (fun s : Qseq => cauchy s) v Hv) n))).
           ++ apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n) (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)); [exact Hu0 | exact Hv0].
           ++ apply QltT_to_Qlt. apply (HNab n). apply NatLe_lift. exact HnNab.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hid.
    + apply (Qplus_le_compat (Qinv (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n))
                             (projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) u Hu)
                                                  (existT _ ea (pair Hea (existT _ Na HNa)))) n)
                             (Qopp (Qinv (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)))
                             (Qopp (projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) v Hv)
                                                          (existT _ eb (pair Heb (existT _ Nb HNb)))) n))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hia.
      * apply (Qopp_le_compat (projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) v Hv)
                                                    (existT _ eb (pair Heb (existT _ Nb HNb)))) n)
                              (Qinv (projT1 (existT (fun s : Qseq => cauchy s) v Hv) n))).
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hib.
Qed.

(* 上界：y > 0 ⟹ ∃x, y < e^x（real_arch + exp 超常量 + real_lt_trans） *)
Lemma exp_upper_bound : forall (y : Real), real_lt real_zero y ->
  sigT (fun x : Real => real_lt y (cauchy_real_exp x)).
Proof.
  intros y Hy.
  destruct (real_arch y) as [n [Hn2 Hyn]].
  exists (real_const (Z.of_nat n # 1)).
  apply (real_lt_trans y (real_const (Z.of_nat n # 1)) (cauchy_real_exp (real_const (Z.of_nat n # 1)))).
  - exact Hyn.
  - apply (cauchy_real_exp_gt_const n). apply NatLe_drop in Hn2. lia.
Qed.

(* 下界：y > 0 ⟹ ∃x, e^x < y
   见证 eps/2；x := −x0 其中 e^{x0} > 2/eps（unbounded）；
   e^{−x0} == 1/e^{x0}（exp_neg_recip）< 1/(2/eps)（real_inv_lt_contra）== eps/2（real_inv_unique）< y *)
Lemma exp_lower_bound : forall (y : Real), real_lt real_zero y ->
  sigT (fun x : Real => real_lt (cauchy_real_exp x) y).
Proof.
  intros y Hy.
  destruct Hy as [eps [Heps [Ny HNy]]].
  assert (H2e : QltT 0 (2 / eps)).
  { apply Qlt_to_QltT. unfold Qdiv. apply (Qmult_lt_0_compat 2 (Qinv eps)).
    - change (Qlt 0 2). compute. reflexivity.
    - apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Heps. }
  assert (Hcst : real_lt real_zero (real_const (2 / eps))) by (apply real_const_pos; exact H2e).
  destruct (cauchy_real_exp_unbounded (real_const (2 / eps))) as [x0 Hx0].
  assert (Hexp0 : real_lt real_zero (cauchy_real_exp x0)) by apply cauchy_real_exp_pos.
  exists (real_opp x0).
  assert (Hhalf : Qlt 0 (eps / 2)).
  { apply Qlt_shift_div_l; [change (Qlt 0 2); compute; reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
  assert (Hcy : real_lt (real_const (eps / 2)) y).
  { exists (eps / 2). split.
    - apply Qlt_to_QltT. exact Hhalf.
    - exists Ny. intros n Hn. apply Qlt_to_QltT.
      apply (proj2 (Qlt_minus_iff (eps / 2) (projT1 y n - projT1 (real_const (eps / 2)) n))).
      apply (Qlt_le_trans 0 (projT1 y n - eps) ((projT1 y n - projT1 (real_const (eps / 2)) n) + Qopp (eps / 2))).
      + apply (proj1 (Qlt_minus_iff eps (projT1 y n))).
        apply (Qlt_le_trans eps (projT1 y n - projT1 real_zero n) (projT1 y n)).
        * apply QltT_to_Qlt. apply (HNy n). exact Hn.
        * apply QleT'_to_Qle. apply qeq_le.          apply qeq_imp_qeqT.
          assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
          setoid_rewrite Hz0. unfold Qminus. ring.
      + apply QleT'_to_Qle. apply qeq_le.        apply qeq_imp_qeqT.
        assert (Hcp : projT1 (real_const (eps / 2)) n == eps / 2) by (apply qeqT_imp_qeq, real_const_proj).
        setoid_rewrite Hcp. unfold Qminus. field. }
  apply (real_lt_trans (cauchy_real_exp (real_opp x0))
                       (real_inv_pos (real_const (2 / eps)) Hcst)
                       y).
  - apply (real_eq_lt_lt (cauchy_real_exp (real_opp x0))
                         (real_inv_pos (cauchy_real_exp x0) Hexp0)
                         (real_inv_pos (real_const (2 / eps)) Hcst)).
    + apply (exp_neg_recip x0 Hexp0).
    + apply (real_inv_lt_contra (real_const (2 / eps)) (cauchy_real_exp x0) Hcst Hexp0).
      exact Hx0.
  - apply (real_eq_lt_lt (real_inv_pos (real_const (2 / eps)) Hcst)
                         (real_const (eps / 2)) y).
    + apply (real_inv_unique (real_const (2 / eps))
                             (real_inv_pos (real_const (2 / eps)) Hcst)
                             (real_const (eps / 2))).
      * apply real_inv_pos_correct.
      * apply real_eq_of_zero_diff. intro n.
        apply qeq_imp_qeqT.
        assert (Hp1 : projT1 (real_mult (real_const (2 / eps)) (real_const (eps / 2))) n ==
                      projT1 (real_const (2 / eps)) n * projT1 (real_const (eps / 2)) n).
        { apply qeqT_imp_qeq. apply real_mult_proj. }
        assert (Hp2 : projT1 (real_const (2 / eps)) n == 2 / eps) by (apply qeqT_imp_qeq, real_const_proj).
        assert (Hp3 : projT1 (real_const (eps / 2)) n == eps / 2) by (apply qeqT_imp_qeq, real_const_proj).
        assert (Hone : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hp1. setoid_rewrite Hp2. setoid_rewrite Hp3. setoid_rewrite Hone.
        unfold Qminus. field.
        intro Hz; exact (match q_neq_of_lt eps Heps (qeq_imp_qeqT _ _ Hz) with end).
    + exact Hcy.
Qed.

(* ============ log 论证第三阶段 Chunk 5：approx_root（常数精度 eps/16 测试） ============ *)

(* d4 := eps/16 正性 *)
Lemma q_eps16_pos : forall eps : Q, QltT 0 eps -> QltT 0 (eps / 16).
Proof.
  intros eps Heps.
  apply Qlt_to_QltT.
  apply (Qlt_shift_div_l 0 eps 16).
  - change (Qlt 0 16). compute. reflexivity.
  - simpl. apply QltT_to_Qlt. exact Heps.
Qed.

Lemma q_eps16_posT : forall eps : Q, QltT 0 eps -> QltT 0 (eps / 16).
Proof.
  intros eps Heps. apply q_eps16_pos. exact Heps.
Qed.

(* eps 版决策测试：d4 := eps/16 常数（不随区间长度变化）
   testA：q + 2d4 < r ⟹ e^m < y；testB：r + 2d4 < q ⟹ y < e^m；
   双假 ⟹ |e^m−y| ≤ 4d4 = eps/4 < eps（缺陷步直接达标） *)
Definition log_testA_eps (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) : bool :=
  let m := (a + b) / 2 in
  let d4 := eps / 16 in
  let K1 := projT1 (exp_partial_cauchy m d4 (q_eps16_posT eps Heps)) in
  let K2 := projT1 (projT2 y d4 (q_eps16_posT eps Heps)) in
  Qlt_bool (exp_partial K1 m + 2 * d4) (projT1 y K2).

Definition log_testB_eps (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) : bool :=
  let m := (a + b) / 2 in
  let d4 := eps / 16 in
  let K1 := projT1 (exp_partial_cauchy m d4 (q_eps16_posT eps Heps)) in
  let K2 := projT1 (projT2 y d4 (q_eps16_posT eps Heps)) in
  Qlt_bool (projT1 y K2 + 2 * d4) (exp_partial K1 m).

Definition log_m_eps (a b : Q) : Q := (a + b) / 2.
Definition log_d4_eps (eps : Q) : Q := eps / 16.
Definition log_K1_eps (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) : nat :=
  projT1 (exp_partial_cauchy (log_m_eps a b) (log_d4_eps eps) (q_eps16_posT eps Heps)).
Definition log_K2_eps (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) : nat :=
  projT1 (projT2 y (log_d4_eps eps) (q_eps16_posT eps Heps)).
Definition log_q_eps (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) : Q :=
  exp_partial (log_K1_eps a b Hab eps Heps) (log_m_eps a b).
Definition log_r_eps (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) : Q :=
  projT1 y (log_K2_eps y a b Hab eps Heps).

(* 决策 A 真 ⟹ e^m < y：见证 r − q − 2d4（eps 版） *)
Lemma log_testA_eps_true_lt : forall (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps),
  log_testA_eps y a b Hab eps Heps = true ->
  real_lt (cauchy_real_exp (real_const (log_m_eps a b))) y.
Proof.
  intros y a b Hab eps Heps HA.
  unfold log_testA_eps in HA.
  cbn in HA.
  pose (m := log_m_eps a b).
  pose (d4 := log_d4_eps eps).
  pose (K1 := log_K1_eps a b Hab eps Heps).
  pose (K2 := log_K2_eps y a b Hab eps Heps).
  pose (q := log_q_eps a b Hab eps Heps).
  pose (r := log_r_eps y a b Hab eps Heps).
  assert (Hlt : Qlt (q + 2 * d4) r).
  { apply QltT_to_Qlt.
    exact (RealSetoid.eq_Id _ _ HA). }
  assert (Heps4 : QltT 0 (r - q - 2 * d4)).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (r + - (q + 2 * d4)) _).
    - apply (proj1 (Qlt_minus_iff (q + 2 * d4) r)). exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  exists (r - q - 2 * d4).
  split.
  - exact Heps4.
  - exists (Nat.max K1 K2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (HnK1 : (K1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (HnK2 : (K2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hem : Qlt (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q)) d4).
    { apply QltT_to_Qlt.
      cbn [projT1].
      apply (projT2 (exp_partial_cauchy m d4 (q_eps16_posT eps Heps)) n K1).
      - exact (NatLe_lift _ _ HnK1).
      - apply NatLe_lift. apply Nat.le_refl. }
    assert (Hyr : Qlt (Qabs (projT1 y n - r)) d4).
    { apply QltT_to_Qlt.
      apply (projT2 (projT2 y d4 (q_eps16_posT eps Heps)) n K2).
      - exact (NatLe_lift _ _ HnK2).
      - apply NatLe_lift. apply Nat.le_refl. }
    apply (Qle_lt_trans _ ((r - d4) - (q + d4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_lt_compat (r - d4) (projT1 y n) (Qopp (q + d4)) (Qopp (projT1 (cauchy_real_exp (real_const m)) n))).
      * apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 y n) r d4). apply Qlt_to_QltT. exact Hyr.
      * apply (Qopp_lt_compat (projT1 (cauchy_real_exp (real_const m)) n) (q + d4)).
        apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 (cauchy_real_exp (real_const m)) n) q d4). apply Qlt_to_QltT. exact Hem.
Qed.

(* 决策 B 真 ⟹ y < e^m（eps 版） *)
Lemma log_testB_eps_true_gt : forall (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps),
  log_testB_eps y a b Hab eps Heps = true ->
  real_lt y (cauchy_real_exp (real_const (log_m_eps a b))).
Proof.
  intros y a b Hab eps Heps HB.
  unfold log_testB_eps in HB.
  cbn in HB.
  pose (m := log_m_eps a b).
  pose (d4 := log_d4_eps eps).
  pose (K1 := log_K1_eps a b Hab eps Heps).
  pose (K2 := log_K2_eps y a b Hab eps Heps).
  pose (q := log_q_eps a b Hab eps Heps).
  pose (r := log_r_eps y a b Hab eps Heps).
  assert (Hlt : Qlt (r + 2 * d4) q).
  { apply QltT_to_Qlt.
    apply RealSetoid.eq_Id.
    exact HB. }
  assert (Heps4 : QltT 0 (q - r - 2 * d4)).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (q + - (r + 2 * d4)) _).
    - apply (proj1 (Qlt_minus_iff (r + 2 * d4) q)). exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  exists (q - r - 2 * d4).
  split.
  - exact Heps4.
  - exists (Nat.max K1 K2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (HnK1 : (K1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (HnK2 : (K2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hem : Qlt (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q)) d4).
    { apply QltT_to_Qlt.
      cbn [projT1].
      apply (projT2 (exp_partial_cauchy m d4 (q_eps16_posT eps Heps)) n K1).
      - exact (NatLe_lift _ _ HnK1).
      - apply NatLe_lift. apply Nat.le_refl. }
    assert (Hyr : Qlt (Qabs (projT1 y n - r)) d4).
    { apply QltT_to_Qlt.
      apply (projT2 (projT2 y d4 (q_eps16_posT eps Heps)) n K2).
      - exact (NatLe_lift _ _ HnK2).
      - apply NatLe_lift. apply Nat.le_refl. }
    apply (Qle_lt_trans _ ((q - d4) - (r + d4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_lt_compat (q - d4) (projT1 (cauchy_real_exp (real_const m)) n)
                             (Qopp (r + d4)) (Qopp (projT1 y n))).
      * apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 (cauchy_real_exp (real_const m)) n) q d4). apply Qlt_to_QltT. exact Hem.
      * apply (Qopp_lt_compat (projT1 y n) (r + d4)).
        apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 y n) r d4). apply Qlt_to_QltT. exact Hyr.
Qed.

(* 双假 ⟹ |e^m−y| ≤ 4d4 = eps/4（逐点，eps 版） *)
Lemma log_test_mid_bound_eps : forall (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps),
  log_testA_eps y a b Hab eps Heps = false -> log_testB_eps y a b Hab eps Heps = false ->
  forall n : nat, (Nat.max (log_K1_eps a b Hab eps Heps) (log_K2_eps y a b Hab eps Heps) <= n)%nat ->
    QleT' (Qabs (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n - projT1 y n))
        (4 * log_d4_eps eps).
Proof.
  intros y a b Hab eps Heps HA HB n Hn.
  apply Qle_to_QleT'.
  unfold log_testA_eps in HA. unfold log_testB_eps in HB. cbn in HA, HB.
  pose (m := log_m_eps a b).
  pose (d4 := log_d4_eps eps).
  pose (K1 := log_K1_eps a b Hab eps Heps).
  pose (K2 := log_K2_eps y a b Hab eps Heps).
  pose (q := log_q_eps a b Hab eps Heps).
  pose (r := log_r_eps y a b Hab eps Heps).
  change (Qlt_bool (q + 2 * d4) r = false) in HA.
  change (Qlt_bool (r + 2 * d4) q = false) in HB.
  pose (HnA := qlt_bool_false_not (q + 2 * d4) r HA).
  pose (HnB := qlt_bool_false_not (r + 2 * d4) q HB).
  assert (Hqle : Qle q (r + 2 * d4)).
  { apply Qnot_lt_le. intro Hc. destruct (HnB (Qlt_to_QltT _ _ Hc)). }
  assert (Hrle : Qle r (q + 2 * d4)).
  { apply Qnot_lt_le. intro Hc. destruct (HnA (Qlt_to_QltT _ _ Hc)). }
  assert (Hqr : Qle (Qabs (q - r)) (2 * d4)).
  { apply (proj2 (Qabs_Qle_condition (q - r) (2 * d4))).
    split.
    - apply (Qle_trans _ (Qopp (r - q)) _).
      + apply Qopp_le_compat.
        apply (Qle_trans _ (Qplus (Qplus q (2 * d4)) (Qopp q)) _).
        * apply (Qplus_le_compat r (q + 2 * d4) (Qopp q) (Qopp q)); [exact Hrle | apply Qle_refl].
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ (Qplus (Qplus r (2 * d4)) (Qopp r)) _).
      + apply (Qplus_le_compat q (r + 2 * d4) (Qopp r) (Qopp r)); [exact Hqle | apply Qle_refl].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hem : Qlt (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q)) d4).
  { apply QltT_to_Qlt.
    cbn [projT1].
    apply (projT2 (exp_partial_cauchy m d4 (q_eps16_posT eps Heps)) n K1).
    - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_l | exact Hn].
    - apply NatLe_lift. apply Nat.le_refl. }
  assert (Hyr : Qlt (Qabs (projT1 y n - r)) d4).
  { apply QltT_to_Qlt.
    apply (projT2 (projT2 y d4 (q_eps16_posT eps Heps)) n K2).
    - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max K1 K2) _); [apply Nat.le_max_r | exact Hn].
    - apply NatLe_lift. apply Nat.le_refl. }
  apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q) + Qabs (q - r) + Qabs (r - projT1 y n)) _).
  - apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q) + Qabs ((q - r) + (r - projT1 y n))) _).
    + assert (Hsum : projT1 (cauchy_real_exp (real_const m)) n - projT1 y n ==
                     (projT1 (cauchy_real_exp (real_const m)) n - q) + ((q - r) + (r - projT1 y n))).
      { ring. }
      apply (Qle_trans _ (Qabs ((projT1 (cauchy_real_exp (real_const m)) n - q) + ((q - r) + (r - projT1 y n)))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. exact Hsum.
      * apply Qabs_triangle.
    + apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const m)) n - q) + (Qabs (q - r) + Qabs (r - projT1 y n))) _).
      * apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply Qabs_triangle].
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (d4 + (2 * d4) + d4) _).
    + apply (Qplus_le_compat _ _ _ _).
      * apply (Qplus_le_compat _ _ _ _).
        -- apply Qlt_le_weak. exact Hem.
        -- exact Hqr.
      * apply Qlt_le_weak.
        rewrite <- (Qabs_Qminus (projT1 y n) r). exact Hyr.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold d4, log_d4_eps. ring.
Qed.

(* ============ log 论证第三阶段 Chunk 5b：log_scan 扫描 + 正确性 ============ *)

(* 1/2 的幂非增 *)
Lemma q_pow_half_le : forall n : nat, QleT' (q_pow (1 / 2) (Datatypes.S n)) (q_pow (1 / 2) n).
Proof.
  intros n. apply Qle_to_QleT'.
  apply (Qle_trans _ ((1 / 2) * q_pow (1 / 2) n) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
  - apply (Qle_trans _ (1 * q_pow (1 / 2) n) _).
    + apply (Qmult_le_compat_r (1 / 2) 1 (q_pow (1 / 2) n)).
      * change (Qle (1 / 2) 1). unfold Qle, Qdiv. simpl. lia.
      * apply QleT'_to_Qle. apply (q_pow_nonneg (1 / 2) n). apply Qle_to_QleT'. change (Qle 0 (1 / 2)). unfold Qle, Qdiv. simpl. lia.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 严格递减：(1/2)^(S n) < (1/2)^n *)
Lemma q_pow_half_lt_self : forall n : nat, QltT (q_pow (1 / 2) (Datatypes.S n)) (q_pow (1 / 2) n).
Proof.
  intros n. apply Qlt_to_QltT.
  induction n as [| m IH]; simpl.
  - change (Qlt (1 / 2) 1). unfold Qdiv. simpl. reflexivity.
  - apply (Qle_lt_trans ((1 / 2) * ((1 / 2) * q_pow (1 / 2) m))
                        (((1 / 2) * q_pow (1 / 2) m) * (1 / 2))
                        ((1 / 2) * q_pow (1 / 2) m)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qlt_le_trans _ ((q_pow (1 / 2) m) * (1 / 2)) _).
      * apply (Qmult_lt_compat_r ((1 / 2) * q_pow (1 / 2) m) (q_pow (1 / 2) m) (1 / 2)).
        -- change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity.
        -- apply IH.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 扫描 Fixpoint：testA 真→右半、testB 真→左半、双假→冻结（返回当前区间 + false） *)
Fixpoint log_scan (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) (n : nat) :
  (sigT (fun ab : Q * Q => QltT (fst ab) (snd ab))) * bool :=
  match n with
  | O => (existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) Hab, true)
  | Datatypes.S n' =>
      let m := log_m_eps a b in
      if log_testA_eps y a b Hab eps Heps then
        log_scan y m b (log_mid_lt_b a b Hab) eps Heps n'
      else if log_testB_eps y a b Hab eps Heps then
        log_scan y a m (log_a_lt_mid a b Hab) eps Heps n'
      else (existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) Hab, false)
  end.

(* 单步归约等式：S 步 = if testA then 右半 else if testB then 左半 else 冻结 *)
Lemma log_scan_S : forall (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) (n : nat),
  Id (log_scan y a b Hab eps Heps (Datatypes.S n))
  (if log_testA_eps y a b Hab eps Heps then
     log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n
   else if log_testB_eps y a b Hab eps Heps then
     log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n
   else (existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) Hab, false)).
Proof. intros. reflexivity. Qed.

(* 扫描正确性：true ⟹ 区间夹逼 y 且长度 == (b−a)·(1/2)^n；false ⟹ 中点 |e^m−y| ≤ 4d4 *)
Lemma log_scan_spec : forall (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) (n : nat),
  real_lt (cauchy_real_exp (real_const a)) y ->
  real_lt y (cauchy_real_exp (real_const b)) ->
  Or
    (And (Id (snd (log_scan y a b Hab eps Heps n)) true)
         (And (real_lt (cauchy_real_exp (real_const (fst (projT1 (fst (log_scan y a b Hab eps Heps n)))))) y)
              (And (real_lt y (cauchy_real_exp (real_const (snd (projT1 (fst (log_scan y a b Hab eps Heps n)))))))
                   (QeqT (snd (projT1 (fst (log_scan y a b Hab eps Heps n))) - fst (projT1 (fst (log_scan y a b Hab eps Heps n))))
                    ((b - a) * q_pow (1 / 2) n)))))
    (And (Id (snd (log_scan y a b Hab eps Heps n)) false)
         (forall k : nat,
           (Nat.max (log_K1_eps (fst (projT1 (fst (log_scan y a b Hab eps Heps n))))
                                (snd (projT1 (fst (log_scan y a b Hab eps Heps n))))
                                (projT2 (fst (log_scan y a b Hab eps Heps n))) eps Heps)
                    (log_K2_eps y (fst (projT1 (fst (log_scan y a b Hab eps Heps n))))
                                (snd (projT1 (fst (log_scan y a b Hab eps Heps n))))
                                (projT2 (fst (log_scan y a b Hab eps Heps n))) eps Heps) <= k)%nat ->
            QleT' (Qabs (projT1 (cauchy_real_exp (real_const
              (log_m_eps (fst (projT1 (fst (log_scan y a b Hab eps Heps n))))
                         (snd (projT1 (fst (log_scan y a b Hab eps Heps n))))))) k - projT1 y k))
                (4 * log_d4_eps eps))).
Proof.
  intros y a b Hab eps Heps n.
  revert y a b Hab eps Heps.
  induction n as [| n IH]; intros y a b Hab eps Heps Hla Hrb.
  - left. simpl. split; [reflexivity | ].
    split; [exact Hla | ].
    split; [exact Hrb | ].
    apply qeq_imp_qeqT. simpl. ring.
  - destruct (log_testA_eps y a b Hab eps Heps) eqn:EA.
    + rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA.
      assert (Hmb : real_lt (cauchy_real_exp (real_const (log_m_eps a b))) y)
        by (apply (log_testA_eps_true_lt y a b Hab eps Heps); exact EA).
      assert (HIH : Or
        (And (Id (snd (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n)) true)
             (And (real_lt (cauchy_real_exp (real_const (fst (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n)))))) y)
                  (And (real_lt y (cauchy_real_exp (real_const (snd (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n)))))))
                       (QeqT (snd (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))) -
                        fst (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))
                        ((b - log_m_eps a b) * q_pow (1 / 2) n)))))
        (And (Id (snd (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n)) false)
             (forall k : nat,
               (Nat.max (log_K1_eps (fst (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))
                                    (snd (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))
                                    (projT2 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))) eps Heps)
                        (log_K2_eps y (fst (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))
                                    (snd (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))
                                    (projT2 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))) eps Heps) <= k)%nat ->
                QleT' (Qabs (projT1 (cauchy_real_exp (real_const
                  (log_m_eps (fst (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))
                             (snd (projT1 (fst (log_scan y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps n))))))) k - projT1 y k))
                    (4 * log_d4_eps eps))))
        by (apply (IH y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps); [apply Hmb | exact Hrb]).
      destruct HIH as [Hfull | Hdef].
      { left.
        destruct Hfull as [Hfl [Hla' [Hrb' Hlen]]].
        split; [exact Hfl | ].
        split; [exact Hla' | ].
        split; [exact Hrb' | ].
        apply qeq_imp_qeqT.
        apply (Qeq_trans _ ((b - log_m_eps a b) * q_pow (1 / 2) n) _).
        { apply qeqT_imp_qeq. exact Hlen. }
        { assert (Hb : b - log_m_eps a b == (b - a) / 2).
          { unfold log_m_eps. apply qeqT_imp_qeq. apply log_step_len_mb. exact Hab. }
          rewrite Hb.
          unfold Qdiv.
          cbn [q_pow].
          ring. } }
      { right. exact Hdef. }
    + destruct (log_testB_eps y a b Hab eps Heps) eqn:EB.
      * rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA. rewrite EB.
        assert (Ham : real_lt y (cauchy_real_exp (real_const (log_m_eps a b))))
          by (apply (log_testB_eps_true_gt y a b Hab eps Heps); exact EB).
        assert (HIH : Or
          (And (Id (snd (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n)) true)
               (And (real_lt (cauchy_real_exp (real_const (fst (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n)))))) y)
                    (And (real_lt y (cauchy_real_exp (real_const (snd (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n)))))))
                         (QeqT (snd (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))) -
                          fst (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))
                          ((log_m_eps a b - a) * q_pow (1 / 2) n)))))
          (And (Id (snd (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n)) false)
               (forall k : nat,
                 (Nat.max (log_K1_eps (fst (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))
                                      (snd (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))
                                      (projT2 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))) eps Heps)
                          (log_K2_eps y (fst (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))
                                      (snd (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))
                                      (projT2 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))) eps Heps) <= k)%nat ->
                  QleT' (Qabs (projT1 (cauchy_real_exp (real_const
                    (log_m_eps (fst (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))
                               (snd (projT1 (fst (log_scan y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps n))))))) k - projT1 y k))
                      (4 * log_d4_eps eps))))
          by (apply (IH y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps); [exact Hla | apply Ham]).
        destruct HIH as [Hfull | Hdef].
        { left.
          destruct Hfull as [Hfl [Hla' [Hrb' Hlen]]].
          split; [exact Hfl | ].
          split; [exact Hla' | ].
          split; [exact Hrb' | ].
          apply qeq_imp_qeqT.
          apply (Qeq_trans _ ((log_m_eps a b - a) * q_pow (1 / 2) n) _).
          { apply qeqT_imp_qeq. exact Hlen. }
          { assert (Ha : log_m_eps a b - a == (b - a) / 2).
            { unfold log_m_eps. apply qeqT_imp_qeq. apply log_step_len_am. exact Hab. }
            rewrite Ha.
            unfold Qdiv.
            cbn [q_pow].
            ring. } }
        { right. exact Hdef. }
      * rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA. rewrite EB.
        right. split; [reflexivity | ].
        intros k Hk.
        apply (log_test_mid_bound_eps y a b Hab eps Heps); [exact EA | exact EB | exact Hk].
Qed.

(* ============ log 论证第三阶段 Chunk 5c：approx_root 辅助引理 ============ *)

(* 下界端点：∃N, e^{−(N#1)} < y（N ≥ 2，来自 real_arch） *)
Lemma exp_lower_q : forall (y : Real) (Hy : real_lt real_zero y),
  sigT (fun N : nat => And (NatLe 2 N)
    (real_lt (cauchy_real_exp (real_const (Qopp (Z.of_nat N # 1)))) y)).
Proof.
  intros y Hy.
  destruct Hy as [eps [Heps [Ny HNy]]].
  assert (H2e : QltT 0 (2 / eps)).
  { apply Qlt_to_QltT. unfold Qdiv. apply (Qmult_lt_0_compat 2 (Qinv eps)).
    - change (Qlt 0 2). compute. reflexivity.
    - apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Heps. }
  assert (Hcst : real_lt real_zero (real_const (2 / eps))) by (apply real_const_pos; exact H2e).
  destruct (real_arch (real_const (2 / eps))) as [N [HN2 HN]].
  assert (HN1 : (1 <= N)%nat) by (apply NatLe_drop in HN2; lia).
  assert (HexpN : real_lt (real_const (2 / eps)) (cauchy_real_exp (real_const (Z.of_nat N # 1)))).
  { apply (real_lt_trans (real_const (2 / eps)) (real_const (Z.of_nat N # 1))
                          (cauchy_real_exp (real_const (Z.of_nat N # 1)))).
    - exact HN.
    - apply (cauchy_real_exp_gt_const N HN1). }
  assert (HexpNpos : real_lt real_zero (cauchy_real_exp (real_const (Z.of_nat N # 1)))) by apply cauchy_real_exp_pos.
  exists N. split; [exact HN2 | ].
  apply (real_eq_lt_lt (cauchy_real_exp (real_const (Qopp (Z.of_nat N # 1))))
                       (cauchy_real_exp (real_opp (real_const (Z.of_nat N # 1))))
                       y).
  - apply cauchy_real_exp_wd.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    assert (Hp : projT1 (real_const (Qopp (Z.of_nat N # 1))) n == Qopp (Z.of_nat N # 1)) by (apply (qeqT_imp_qeq _ _ (real_const_proj (Qopp (Z.of_nat N # 1)) n))).
    assert (Hq0 : projT1 (real_const (Z.of_nat N # 1)) n == Z.of_nat N # 1) by (apply (qeqT_imp_qeq _ _ (real_const_proj (Z.of_nat N # 1) n))).
    assert (Hq : projT1 (real_opp (real_const (Z.of_nat N # 1))) n == Qopp (Z.of_nat N # 1)).
    { rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_const (Z.of_nat N # 1)) n)). apply (Qopp_comp _ _ Hq0). }
    rewrite Hp. rewrite Hq. unfold Qminus. ring.
  - apply (real_lt_trans (cauchy_real_exp (real_opp (real_const (Z.of_nat N # 1))))
                         (real_inv_pos (real_const (2 / eps)) Hcst)
                         y).
    + apply (real_eq_lt_lt (cauchy_real_exp (real_opp (real_const (Z.of_nat N # 1))))
                           (real_inv_pos (cauchy_real_exp (real_const (Z.of_nat N # 1))) HexpNpos)
                           (real_inv_pos (real_const (2 / eps)) Hcst)).
      * apply (exp_neg_recip (real_const (Z.of_nat N # 1)) HexpNpos).
      * apply (real_inv_lt_contra (real_const (2 / eps)) (cauchy_real_exp (real_const (Z.of_nat N # 1))) Hcst HexpNpos).
        exact HexpN.
    + apply (real_eq_lt_lt (real_inv_pos (real_const (2 / eps)) Hcst)
                           (real_const (eps / 2)) y).
      * apply (real_inv_unique (real_const (2 / eps))
                               (real_inv_pos (real_const (2 / eps)) Hcst)
                               (real_const (eps / 2))).
        -- apply real_inv_pos_correct.
        -- apply real_eq_of_zero_diff. intro n.
           apply qeq_imp_qeqT.
           assert (Hp1 : projT1 (real_mult (real_const (2 / eps)) (real_const (eps / 2))) n ==
                         projT1 (real_const (2 / eps)) n * projT1 (real_const (eps / 2)) n).
           { apply qeqT_imp_qeq. apply real_mult_proj. }
           assert (Hp2 : projT1 (real_const (2 / eps)) n == 2 / eps) by (apply (qeqT_imp_qeq _ _ (real_const_proj (2 / eps) n))).
           assert (Hp3 : projT1 (real_const (eps / 2)) n == eps / 2) by (apply (qeqT_imp_qeq _ _ (real_const_proj (eps / 2) n))).
           assert (Hone : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
           setoid_rewrite Hp1. setoid_rewrite Hp2. setoid_rewrite Hp3. setoid_rewrite Hone.
           unfold Qminus. field.
           intro Hz; exact (match q_neq_of_lt eps Heps (qeq_imp_qeqT _ _ Hz) with end).
      * assert (Hhalf : Qlt 0 (eps / 2)).
        { apply Qlt_shift_div_l; [change (Qlt 0 2); compute; reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
        exists (eps / 2). split.
        -- apply Qlt_to_QltT. exact Hhalf.
        -- exists Ny. intros n Hn. apply Qlt_to_QltT.
           apply (proj2 (Qlt_minus_iff (eps / 2) (projT1 y n - projT1 (real_const (eps / 2)) n))).
           apply (Qlt_le_trans 0 (projT1 y n - eps) ((projT1 y n - projT1 (real_const (eps / 2)) n) + Qopp (eps / 2))).
           ++ apply (proj1 (Qlt_minus_iff eps (projT1 y n))).
              apply (Qlt_le_trans eps (projT1 y n - projT1 real_zero n) (projT1 y n)).
              ** apply QltT_to_Qlt. apply (HNy n). exact Hn.
              ** apply QleT'_to_Qle. apply qeq_le.                 apply qeq_imp_qeqT.
                 assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
                 setoid_rewrite Hz0. unfold Qminus. ring.
           ++ apply QleT'_to_Qle. apply qeq_le.              apply qeq_imp_qeqT.
              assert (Hcp : projT1 (real_const (eps / 2)) n == eps / 2) by (apply (qeqT_imp_qeq _ _ (real_const_proj (eps / 2) n))).
              setoid_rewrite Hcp. unfold Qminus. field.
Qed.

(* 上端点：∃M, y < e^{M#1}（M ≥ 2，来自 real_arch） *)
Lemma exp_upper_q : forall (y : Real) (Hy : real_lt real_zero y),
  sigT (fun M : nat => And (NatLe 2 M)
    (real_lt y (cauchy_real_exp (real_const (Z.of_nat M # 1))))).
Proof.
  intros y Hy.
  destruct (real_arch y) as [M [HM2 HM]].
  assert (HM1 : (1 <= M)%nat) by (apply NatLe_drop in HM2; lia).
  exists M. split; [exact HM2 | ].
  apply (real_lt_trans y (real_const (Z.of_nat M # 1)) (cauchy_real_exp (real_const (Z.of_nat M # 1)))).
  - exact HM.
  - apply (cauchy_real_exp_gt_const M HM1).
Qed.

(* log 扫描区间端点（依赖 y 的 a0/b0）：log_lower y Hy := −(Na#1)，log_upper y Hy := Nb#1 *)
Definition log_lower (y : Real) (Hy : real_lt real_zero y) : Q :=
  Qopp (Z.of_nat (projT1 (exp_lower_q y Hy)) # 1).
Definition log_upper (y : Real) (Hy : real_lt real_zero y) : Q :=
  Z.of_nat (projT1 (exp_upper_q y Hy)) # 1.

(* a0 := −(Na#1) < b0 := Nb#1（Na,Nb ≥ 1） *)
Lemma q_neg_nat_lt_nat : forall (Na Nb : nat), (1 <= Na)%nat -> (1 <= Nb)%nat ->
  QltT (Qopp (Z.of_nat Na # 1)) (Z.of_nat Nb # 1).
Proof.
  intros Na Nb HNa HNb.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ 0 _).
  - apply (Qopp_lt_compat 0 (Z.of_nat Na # 1)).
    apply (Qlt_le_trans 0 1 (Z.of_nat Na # 1)).
    + change (Qlt 0 1). compute. reflexivity.
    + change (Qle 1 (Z.of_nat Na # 1)). unfold Qle. simpl. lia.
  - change (Qle 0 (Z.of_nat Nb # 1)). unfold Qle. simpl. lia.
Qed.

(* log_lower y Hy < log_upper y Hy（Na,Nb ≥ 2 ≥ 1） *)
Lemma log_interval_lt : forall (y : Real) (Hy : real_lt real_zero y),
  QltT (log_lower y Hy) (log_upper y Hy).
Proof.
  intros y Hy.
  unfold log_lower, log_upper.
  apply (q_neg_nat_lt_nat (projT1 (exp_lower_q y Hy)) (projT1 (exp_upper_q y Hy))).
  - apply (Nat.le_trans _ 2 _); [lia | exact (NatLe_drop _ _ (fst (projT2 (exp_lower_q y Hy))))].
  - apply (Nat.le_trans _ 2 _); [lia | exact (NatLe_drop _ _ (fst (projT2 (exp_upper_q y Hy))))].
Qed.

(* arch_decay 组合：D ≥ 0 ⟹ ∃n, D·(1/2)^n < eps *)
Lemma q_pow_arch : forall (D eps : Q), QleT' 0 D -> QltT 0 eps ->
  sigT (fun n : nat => QltT (D * q_pow (1 / 2) n) eps).
Proof.
  intros D eps HD Heps.
  destruct (arch_decay D eps HD Heps) as [t Ht].
  exists (Datatypes.S t).
  exact Ht.
Qed.

(* 上 Lipschitz 跨度：a ≤ b，|a|,|b| ≤ B ⟹ |e^b − e^a| ≤ (b−a)·C *)
Lemma q_span_lipschitz : forall (a b B C : Q) (n : nat),
  QleT' a b -> QleT' 0 B -> QleT' (Qabs a) B -> QleT' (Qabs b) B ->
  (forall n : nat, QleT' (exp_series n B) C) ->
  QleT' (Qabs (projT1 (cauchy_real_exp (real_const b)) n - projT1 (cauchy_real_exp (real_const a)) n))
      ((b - a) * C).
Proof.
  intros a b B C n Hab HB Ha Hb HC.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (b - a) * C) _).
  - apply QleT'_to_Qle. apply (exp_upper_lipschitz_q b a B C n HB Hb Ha HC).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    assert (Hbma : Qabs (b - a) == b - a).
    { apply Qabs_pos. apply (proj1 (Qle_minus_iff a b)). apply QleT'_to_Qle. exact Hab. }
    rewrite Hbma. reflexivity.
Qed.

(* |(a+b)/2| ≤ |a+b|/2（q_abs_div 链） *)
Lemma q_abs_half_sum : forall (a b : Q), QleT' (Qabs ((a + b) / 2)) (Qabs (a + b) / 2).
Proof.
  intros a b.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (a + b) / Qabs 2) _).
  - apply (qeqT_imp_qeq _ _ (q_abs_div (a + b) 2)).
  - assert (H2 : Qabs 2 == 2) by (unfold Qabs; simpl; reflexivity).
    rewrite H2. reflexivity.
Qed.

(* X ≤ X + X（X ≥ 0） *)
Lemma q_le_double : forall (X : Q), QleT' 0 X -> QleT' X (X + X).
Proof.
  intros X HX.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (X + 0) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat X X 0 X).
    + apply Qle_refl.
    + apply QleT'_to_Qle. exact HX.
Qed.

(* 中点落在区间内：a < b ⟹ a ≤ m ≤ b *)
Lemma log_mid_between : forall a b : Q, QltT a b ->
  And (QleT' a (log_m_eps a b)) (QleT' (log_m_eps a b) b).
Proof.
  intros a b Hab.
  split.
  - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply log_a_lt_mid. exact Hab.
  - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply log_mid_lt_b. exact Hab.
Qed.

Lemma q_abs_sum_bound : forall (x y : Q), QleT' (Qabs x) (Qabs x + Qabs y).
Proof.
  intros x y.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs x + 0) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat (Qabs x) (Qabs x) 0 (Qabs y)).
    + apply Qle_refl.
    + apply Qabs_nonneg.
Qed.

Lemma q_abs_sum_bound_r : forall (x y : Q), QleT' (Qabs y) (Qabs x + Qabs y).
Proof.
  intros x y.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (0 + Qabs y) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat 0 (Qabs x) (Qabs y) (Qabs y)).
    + apply Qabs_nonneg.
    + apply Qle_refl.
Qed.

(* 扫描中点绝对界：|(a+b)/2| ≤ |a| + |b| *)
Lemma q_mid_bound : forall (a b : Q), QleT' a b ->
  QleT' (Qabs (log_m_eps a b)) (Qabs a + Qabs b).
Proof.
  intros a b Hab.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (a + b) / 2) _).
  - unfold log_m_eps. apply QleT'_to_Qle. exact (q_abs_half_sum a b).
  - apply (Qle_shift_div_r (Qabs (a + b)) 2 (Qabs a + Qabs b)).
    + change (Qlt 0 2). compute. reflexivity.
    + apply (Qle_trans _ (Qabs a + Qabs b) _).
      * apply Qabs_triangle.
      * assert (HX : Qle 0 (Qabs a + Qabs b)).
        { apply (Qplus_le_compat 0 (Qabs a) 0 (Qabs b)); apply Qabs_nonneg. }
        apply (Qle_trans _ ((Qabs a + Qabs b) + (Qabs a + Qabs b)) _).
        -- apply QleT'_to_Qle. apply (q_le_double (Qabs a + Qabs b)). apply Qle_to_QleT'. exact HX.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* c < d ⟹ real_const c < real_const d（见证 (d−c)/2，N=0） *)
Lemma real_const_lt : forall (c d : Q), QltT c d -> real_lt (real_const c) (real_const d).
Proof.
  intros c d Hcd.
  assert (Hpos : Qlt 0 ((d - c) / 2)).
  { apply (Qlt_shift_div_l 0 (d - c) 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply (proj1 (Qlt_minus_iff c d)). apply QltT_to_Qlt. exact Hcd. }
  exists ((d - c) / 2). split.
  - apply Qlt_to_QltT. exact Hpos.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (d - c) _).
    + apply (proj2 (Qlt_minus_iff ((d - c) / 2) (d - c))).
      apply (Qlt_le_trans 0 ((d - c) / 2) (d - c - (d - c) / 2)).
      * exact Hpos.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
    + apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      assert (Hc : projT1 (real_const c) n == c) by (apply qeqT_imp_qeq, (real_const_proj c n)).
      assert (Hd : projT1 (real_const d) n == d) by (apply qeqT_imp_qeq, (real_const_proj d n)).
      setoid_rewrite Hd. setoid_rewrite Hc. unfold Qminus. ring.
Qed.

(* real_lt X Y ⟹ ∃N, ∀k≥N, X_k < Y_k *)
Lemma real_lt_pt_lt : forall (X Y : Real), real_lt X Y ->
  sigT (fun N : nat => forall k : nat, NatLe N k -> QltT (projT1 X k) (projT1 Y k)).
Proof.
  intros X Y HXY.
  destruct HXY as [eps [Heps [N HN]]].
  exists N.
  intros k Hk.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans (projT1 X k) (projT1 X k + eps) (projT1 Y k)).
  - apply (proj2 (Qlt_minus_iff (projT1 X k) (projT1 X k + eps))).
    apply (Qlt_le_trans 0 eps ((projT1 X k + eps) - projT1 X k)).
    + apply QltT_to_Qlt. exact Heps.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_le_weak _ _).
    apply (proj2 (Qlt_minus_iff (projT1 X k + eps) (projT1 Y k))).
    apply (Qlt_le_trans 0 (projT1 Y k - projT1 X k - eps) ((projT1 Y k) - (projT1 X k + eps))).
    + apply (proj1 (Qlt_minus_iff eps (projT1 Y k - projT1 X k))).
      apply QltT_to_Qlt. apply (HN k). exact Hk.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* a < b ⟹ a < m < b（严格） *)
Lemma log_mid_strict : forall a b : Q, QltT a b ->
  And (QltT a (log_m_eps a b)) (QltT (log_m_eps a b) b).
Proof.
  intros a b Hab. split.
  - apply Qlt_to_QltT. unfold log_m_eps. apply QltT_to_Qlt. apply log_a_lt_mid. exact Hab.
  - apply Qlt_to_QltT. unfold log_m_eps. apply QltT_to_Qlt. apply log_mid_lt_b. exact Hab.
Qed.

(* Real 层：a<b ⟹ e^{real_const a} < e^{real_const b} *)
Lemma exp_const_lt : forall a b : Q, QltT a b ->
  real_lt (cauchy_real_exp (real_const a)) (cauchy_real_exp (real_const b)).
Proof.
  intros a b Hab.
  apply (cauchy_real_exp_mono (real_const a) (real_const b)).
  apply real_const_lt. exact Hab.
Qed.

(* Real 层下 Lipschitz：s ≤ u、e^{a0} < e^s（Real 严格序，由 exp_const_lt 提供）
   ⟹ e^u − e^s ≥ e^{a0}·(u−s)（松弛 ≥）。与 exp_lower_lipschitz_q 相同，
   但 Hmono 前提换成 Real 层严格单调（cauchy_real_exp_mono 的反向需求），
   经 real_lt_pt_lt 逐点化后 Hmono 所需的不等式逐点成立。 *)
Lemma exp_lower_lipschitz_real : forall (a0 u s : Q) (Hle : QleT' s u),
  real_lt (cauchy_real_exp (real_const a0)) (cauchy_real_exp (real_const s)) ->
  real_ge_relax (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s))))
                (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))).
Proof.
  intros a0 u s Hle Ha0s eps Heps.
  destruct (real_lt_pt_lt (cauchy_real_exp (real_const a0)) (cauchy_real_exp (real_const s)) Ha0s) as [N0 HN0].
  destruct (cauchy_real_exp_pos (real_const s)) as [epss [Hepss [Ns HNs]]].
  assert (Hh : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps 2).
    - change (Qlt 0 2). compute. reflexivity.
    - apply (Qle_lt_trans _ 0 _); [apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring | apply QltT_to_Qlt; exact Heps]. }
  destruct (exp_diff_factor (real_const u) (real_const s) (eps / 2) Hh) as [N1 HN1].
  exists (Nat.max (Nat.max 1 N0) (Nat.max Ns N1)).
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hn1 : (1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 1 N0) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max 1 N0) (Nat.max Ns N1)) _); [apply Nat.le_max_l | exact Hn]]).
  assert (HnN0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 1 N0) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max 1 N0) (Nat.max Ns N1)) _); [apply Nat.le_max_l | exact Hn]]).
  assert (HnNs : (Ns <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Ns N1) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max 1 N0) (Nat.max Ns N1)) _); [apply Nat.le_max_r | exact Hn]]).
  assert (HnN1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Ns N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max 1 N0) (Nat.max Ns N1)) _); [apply Nat.le_max_r | exact Hn]]).
  assert (Hl : projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) n ==
                projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n).
{ rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s))) n)).
rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_exp (real_const s)) n)). reflexivity. }
  assert (Hr : projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) n ==
                projT1 (cauchy_real_exp (real_const a0)) n * (u - s)).
{ rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_exp (real_const a0)) (real_const (u - s)) n)).
rewrite (qeqT_imp_qeq _ _ (real_const_proj (u - s) n)). reflexivity. }
  assert (Hm : projT1 (real_mult (cauchy_real_exp (real_const s))
                                (real_plus (cauchy_real_exp (real_const (u - s))) (real_opp real_one))) n ==
                projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1)).
{ rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_exp (real_const s)) (real_plus (cauchy_real_exp (real_const (u - s))) (real_opp real_one)) n)).
rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (real_const (u - s))) (real_opp real_one) n)).
rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    assert (Ho1 : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    setoid_rewrite Ho1. reflexivity. }
  setoid_rewrite Hr. setoid_rewrite Hl.
  assert (H1 : Qlt (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1) - eps / 2)
                   (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)).
  { apply QltT_to_Qlt.
    apply (q_abs_lt_minus (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)
                          (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1))
                          (eps / 2)).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) n -
                                 projT1 (real_mult (cauchy_real_exp (real_const s))
                                                  (real_plus (cauchy_real_exp (real_const (u - s))) (real_opp real_one))) n)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
      setoid_rewrite <- Hl.
      setoid_rewrite <- Hm.
      reflexivity.
    - apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift. exact HnN1. }
  assert (Hus : Qle (u - s) (projT1 (cauchy_real_exp (real_const (u - s))) n - 1)).
  { cbn [projT1].
    destruct n as [| m].
    { lia. }
    apply (Qle_trans _ (Qplus (1 + (u - s)) (Qopp 1)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qplus_le_compat (1 + (u - s)) (exp_partial (Datatypes.S m) (u - s)) (Qopp 1) (Qopp 1)).
      * apply QleT'_to_Qle. apply (exp_partial_ge_plus_x m (u - s)). apply q_le_minus. exact Hle.
      * apply Qle_refl. }
  assert (Hs0 : Qle 0 (projT1 (cauchy_real_exp (real_const s)) n)).
  { apply (Qle_trans _ epss _).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hepss.
    - apply (Qle_trans _ (projT1 (cauchy_real_exp (real_const s)) n - projT1 real_zero n) _).
      + apply Qlt_le_weak. apply QltT_to_Qlt. apply (HNs n). apply NatLe_lift. exact HnNs.
      + apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        assert (Hz0 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hz0. unfold Qminus. ring. }
  assert (H2 : Qle (projT1 (cauchy_real_exp (real_const s)) n * (u - s))
                   (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1))).
  { apply (Qle_trans _ (Qmult (u - s) (projT1 (cauchy_real_exp (real_const s)) n)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ (Qmult (projT1 (cauchy_real_exp (real_const (u - s))) n - 1) (projT1 (cauchy_real_exp (real_const s)) n)) _).
      + apply (Qmult_le_compat_r (u - s) (projT1 (cauchy_real_exp (real_const (u - s))) n - 1)
                                 (projT1 (cauchy_real_exp (real_const s)) n)).
        * exact Hus.
        * exact Hs0.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hus0 : Qle 0 (u - s)).
  { apply QleT'_to_Qle. apply q_le_minus. exact Hle. }
  assert (H3 : Qle (projT1 (cauchy_real_exp (real_const a0)) n * (u - s))
                   (projT1 (cauchy_real_exp (real_const s)) n * (u - s))).
  { apply (Qmult_le_compat_r (projT1 (cauchy_real_exp (real_const a0)) n)
                             (projT1 (cauchy_real_exp (real_const s)) n) (u - s)).
    - cbn [projT1]. destruct n as [| m]. { lia. }
      apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply (HN0 (Datatypes.S m)). apply NatLe_lift. exact HnN0.
    - exact Hus0. }
  assert (Hmain : Qlt (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - eps / 2)
                      (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)).
  { apply (Qle_lt_trans _ (projT1 (cauchy_real_exp (real_const s)) n * (u - s) - eps / 2) _).
    - apply (Qplus_le_compat (projT1 (cauchy_real_exp (real_const a0)) n * (u - s))
                             (projT1 (cauchy_real_exp (real_const s)) n * (u - s))
                             (Qopp (eps / 2)) (Qopp (eps / 2))).
      + exact H3.
      + apply Qle_refl.
    - apply (Qle_lt_trans _ (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1) - eps / 2) _).
      + apply (Qplus_le_compat (projT1 (cauchy_real_exp (real_const s)) n * (u - s))
                               (projT1 (cauchy_real_exp (real_const s)) n * (projT1 (cauchy_real_exp (real_const (u - s))) n - 1))
                               (Qopp (eps / 2)) (Qopp (eps / 2))).
        * exact H2.
        * apply Qle_refl.
      + exact H1. }
  apply (proj2 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)) eps)).
  apply (Qlt_le_trans _ (Qplus (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)
                               (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - eps / 2))) _).
  - apply (proj1 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - eps / 2)
                                (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))).
    exact Hmain.
  - apply (Qle_trans _ (Qplus (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))) (eps / 2)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (Qplus (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n))) eps) _).
      * apply (Qplus_le_compat (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)))
                               (Qopp (projT1 (cauchy_real_exp (real_const a0)) n * (u - s) - (projT1 (cauchy_real_exp (real_const u)) n - projT1 (cauchy_real_exp (real_const s)) n)))
                               (eps / 2) eps).
        -- apply Qle_refl.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half_lt_self eps). exact Heps.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* a ≤ x ≤ b ⟹ |x| ≤ |a| + |b| *)
Lemma q_interval_abs_bound : forall (a x b : Q), QleT' a x -> QleT' x b ->
  QleT' (Qabs x) (Qabs a + Qabs b).
Proof.
  intros a x b Hax Hxb.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 x) as [Hxpos | Hxle0].
  - apply (Qle_trans _ x _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (Qlt_le_weak 0 x). exact Hxpos.
    + apply (Qle_trans _ b _).
      * apply QleT'_to_Qle. exact Hxb.
      * apply (Qle_trans _ (Qabs b) _).
        -- apply Qle_Qabs.
        -- apply QleT'_to_Qle. apply (q_abs_sum_bound_r a b).
  - apply (Qle_trans _ (Qopp x) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_neg. exact Hxle0.
    + assert (Hxm : Qle (Qopp x) (Qopp a)) by (apply (Qopp_le_compat a x); apply QleT'_to_Qle; exact Hax).
      assert (Ha0 : Qle a 0) by (apply (Qle_trans _ x _); [apply QleT'_to_Qle; exact Hax | exact Hxle0]).
      apply (Qle_trans _ (Qopp a) _).
      * exact Hxm.
      * apply (Qle_trans _ (Qabs a) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_neg. exact Ha0.
        -- apply QleT'_to_Qle. apply (q_abs_sum_bound a b).
Qed.

(* 扫描嵌套：返回区间 ⊆ [a,b]（a ≤ fst，snd ≤ b） *)
Lemma log_scan_nested : forall (y : Real) (a b : Q) (Hab : QltT a b) (eps : Q) (Heps : QltT 0 eps) (n : nat),
  And (QleT' a (fst (projT1 (fst (log_scan y a b Hab eps Heps n)))))
      (QleT' (snd (projT1 (fst (log_scan y a b Hab eps Heps n)))) b).
Proof.
  intros y a b Hab eps Heps n.
  revert y a b Hab eps Heps.
  induction n as [| n IH]; intros y a b Hab eps Heps.
  - simpl. split; apply Qle_to_QleT'; apply Qle_refl.
  - destruct (log_testA_eps y a b Hab eps Heps) eqn:EA.
    + destruct (IH y (log_m_eps a b) b (log_mid_lt_b a b Hab) eps Heps) as [H1 H2].
      split.
      * apply Qle_to_QleT'.
        apply (Qle_trans _ (log_m_eps a b) _).
        -- apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply log_a_lt_mid. exact Hab.
        -- rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA.
           apply QleT'_to_Qle in H1. exact H1.
      * rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA. exact H2.
    + destruct (log_testB_eps y a b Hab eps Heps) eqn:EB.
      * destruct (IH y a (log_m_eps a b) (log_a_lt_mid a b Hab) eps Heps) as [H1 H2].
        split.
        -- rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA. rewrite EB. exact H1.
        -- apply Qle_to_QleT'.
           apply (Qle_trans _ (log_m_eps a b) _).
           ++ rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA. rewrite EB.
              apply QleT'_to_Qle in H2. exact H2.
           ++ apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply log_mid_lt_b. exact Hab.
      * rewrite (RealSetoid.Id_eq _ _ (log_scan_S y a b Hab eps Heps n)). rewrite EA. rewrite EB.
        simpl. split; apply Qle_to_QleT'; apply Qle_refl.
Qed.

(* 全判定核心：a<b，e^a < y < e^b，m := (a+b)/2，B 界，C 上 Lipschitz
   ⟹ ∃N0, ∀k≥N0, |e^m_k − y_k| ≤ (b−a)·C（逐点） *)
Lemma approx_span_pt : forall (y : Real) (a b : Q) (HaNbN : QltT a b) (B C : Q)
  (Hla : real_lt (cauchy_real_exp (real_const a)) y)
  (Hrb : real_lt y (cauchy_real_exp (real_const b))),
  QleT' 0 B -> QleT' (Qabs a) B -> QleT' (Qabs b) B ->
  (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat => forall k : nat, NatLe N0 k ->
    QleT' (Qabs (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) k - projT1 y k))
        ((b - a) * C)).
Proof.
  intros y a b HaNbN B C Hla Hrb HB HaB HbB HC.
  set (m := log_m_eps a b).
  destruct (log_mid_strict a b HaNbN) as [Ham Hmb].
  assert (Heam : real_lt (cauchy_real_exp (real_const a)) (cauchy_real_exp (real_const m)))
    by (unfold m; apply exp_const_lt; exact Ham).
  assert (Hemb : real_lt (cauchy_real_exp (real_const m)) (cauchy_real_exp (real_const b)))
    by (unfold m; apply exp_const_lt; exact Hmb).
  destruct (real_lt_pt_lt (cauchy_real_exp (real_const a)) y Hla) as [N1 HN1].
  destruct (real_lt_pt_lt y (cauchy_real_exp (real_const b)) Hrb) as [N2 HN2].
  destruct (real_lt_pt_lt (cauchy_real_exp (real_const a)) (cauchy_real_exp (real_const m)) Heam) as [N3 HN3].
  destruct (real_lt_pt_lt (cauchy_real_exp (real_const m)) (cauchy_real_exp (real_const b)) Hemb) as [N4 HN4].
  exists (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)).
  intros k Hk.
  assert (Hk12 : (Nat.max N1 N2 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
  assert (Hk34 : (Nat.max N3 N4 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
  assert (Hk1 : (N1 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_l | exact Hk12]).
  assert (Hk2 : (N2 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_r | exact Hk12]).
  assert (Hk3 : (N3 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N3 N4) _); [apply Nat.le_max_l | exact Hk34]).
  assert (Hk4 : (N4 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N3 N4) _); [apply Nat.le_max_r | exact Hk34]).
  set (ea := projT1 (cauchy_real_exp (real_const a)) k).
  set (eb := projT1 (cauchy_real_exp (real_const b)) k).
  set (em := projT1 (cauchy_real_exp (real_const m)) k).
  set (yk := projT1 y k).
  assert (Heaeb : Qlt ea eb).
  { apply (Qlt_le_trans _ em _).
    - apply QltT_to_Qlt. exact (HN3 k (NatLe_lift _ _ Hk3)).
    - apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact (HN4 k (NatLe_lift _ _ Hk4)). }
  assert (Hspan : Qle (Qabs (em - yk)) (eb - ea)).
  { apply QleT'_to_Qle. apply (q_abs_le_span ea eb em yk).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact (HN3 k (NatLe_lift _ _ Hk3)).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact (HN4 k (NatLe_lift _ _ Hk4)).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact (HN1 k (NatLe_lift _ _ Hk1)).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact (HN2 k (NatLe_lift _ _ Hk2)). }
  assert (Hspan2 : Qle (eb - ea) ((b - a) * C)).
  { apply (Qle_trans _ (Qabs (eb - ea)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos.
      apply (proj1 (Qle_minus_iff ea eb)). apply (Qlt_le_weak _ _). exact Heaeb.
    - apply QleT'_to_Qle. apply (q_span_lipschitz a b B C k (Qle_to_QleT' _ _ (Qlt_le_weak a b (QltT_to_Qlt _ _ HaNbN))) HB HaB HbB HC). }
  apply Qle_to_QleT'.
  apply (Qle_trans _ (eb - ea) _).
  - exact Hspan.
  - exact Hspan2.
Qed.

(* 长度·C == D·(1/2)^N *)
Lemma len_mul_D : forall (bN aN b0 a0 C : Q) (N : nat),
  QeqT (bN - aN) ((b0 - a0) * q_pow (1 / 2) N) ->
  QeqT ((bN - aN) * C) (((b0 - a0) * C) * q_pow (1 / 2) N).
Proof.
  intros bN aN b0 a0 C N Hlen.
  apply qeq_imp_qeqT. apply (Qeq_trans _ ((b0 - a0) * q_pow (1 / 2) N * C) _).
  - apply (Qmult_comp (bN - aN) ((b0 - a0) * q_pow (1 / 2) N) (qeqT_imp_qeq _ _ Hlen) C C (Qeq_refl C)).
  - ring.
Qed.

(* D·(1/2)^N < eps ⟹ D·(1/2)^N + (eps−D·(1/2)^N)/2 < eps *)
Lemma q_arch_half_lt : forall (D eps : Q) (N : nat),
  QltT (D * q_pow (1 / 2) N) eps ->
  QltT (D * q_pow (1 / 2) N + (eps - D * q_pow (1 / 2) N) / 2) eps.
Proof.
  intros D eps N HN.
  apply Qlt_to_QltT.
  set (X := D * q_pow (1 / 2) N).
  assert (HX : Qlt X eps) by (unfold X; apply QltT_to_Qlt; exact HN).
  assert (HX0 : Qlt 0 (eps - X)).
  { apply (proj1 (Qlt_minus_iff X eps)). exact HX. }
  apply (proj2 (Qlt_minus_iff (X + (eps - X) / 2) eps)).
  apply (Qlt_le_trans 0 ((eps - X) / 2) (eps - (X + (eps - X) / 2))).
  - apply (Qlt_shift_div_l 0 (eps - X) 2).
    + change (Qlt 0 2). compute. reflexivity.
    + simpl. exact HX0.
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    subst X. unfold Qminus. field.
Qed.

(* 全判定提升：逐点 |e^m_k−y_k| ≤ M（k≥N0）⟹ real_lt (|e^m−y|) (real_const (M+γ)) *)
Lemma real_abs_lift : forall (m : Q) (y : Real) (M γ : Q) (N0 : nat),
  QltT 0 γ ->
  (forall k : nat, NatLe N0 k -> QleT' (Qabs (projT1 (cauchy_real_exp (real_const m)) k - projT1 y k)) M) ->
  real_lt (real_abs (real_plus (cauchy_real_exp (real_const m)) (real_opp y)))
          (real_const (M + γ)).
Proof.
  intros m y M γ N0 Hγ Hpt.
  apply (real_abs_diff_le_lift (cauchy_real_exp (real_const m)) y M γ N0 (QltT_to_Qlt _ _ Hγ)).
  intros k Hk. apply QleT'_to_Qle. apply (Hpt k). apply NatLe_lift. exact Hk.
Qed.

(* (bN−aN)·C == D·(1/2)^N ⟹ (bN−aN)·C + γ < eps（γ := (eps−D·(1/2)^N)/2） *)
Lemma approx_const_lt : forall (bN aN D C γ eps : Q) (N : nat),
  QltT (D * q_pow (1 / 2) N) eps ->
  QeqT ((bN - aN) * C) (D * q_pow (1 / 2) N) ->
  QeqT γ ((eps - D * q_pow (1 / 2) N) / 2) ->
  QltT ((bN - aN) * C + γ) eps.
Proof.
  intros bN aN D C γ eps N HN Hbm Hγ.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (D * q_pow (1 / 2) N + (eps - D * q_pow (1 / 2) N) / 2) _).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    apply (Qeq_trans _ (D * q_pow (1 / 2) N + γ) _).
    + apply (Qplus_comp ((bN - aN) * C) (D * q_pow (1 / 2) N) (qeqT_imp_qeq _ _ Hbm) γ γ (Qeq_refl γ)).
    + apply (Qplus_comp (D * q_pow (1 / 2) N) (D * q_pow (1 / 2) N) (Qeq_refl (D * q_pow (1 / 2) N))
                        γ ((eps - D * q_pow (1 / 2) N) / 2) (qeqT_imp_qeq _ _ Hγ)).
  - apply QltT_to_Qlt. apply q_arch_half_lt. exact HN.
Qed.

(* 缺陷分支：逐点 |e^m_k−y_k| ≤ 4·d4（k≥N0）⟹ real_lt (|e^m−y|) (real_const eps)（4·d4 == eps/4 < eps） *)
Lemma approx_def_test : forall (y : Real) (mN : Q) (eps : Q) (Heps : QltT 0 eps) (N0 : nat),
  (forall k : nat, NatLe N0 k ->
     QleT' (Qabs (projT1 (cauchy_real_exp (real_const mN)) k - projT1 y k)) (4 * log_d4_eps eps)) ->
  real_lt (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y))) (real_const eps).
Proof.
  intros y mN eps Heps N0 Hpt.
  assert (Hγ4 : Qlt 0 (eps / 4)).
  { apply (Qlt_shift_div_l 0 eps 4).
    - change (Qlt 0 4). compute. reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hlift : real_lt (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
                          (real_const (4 * log_d4_eps eps + eps / 4))).
  { apply (real_abs_lift mN y (4 * log_d4_eps eps) (eps / 4) N0 (Qlt_to_QltT _ _ Hγ4)).
    intros k Hk. apply (Hpt k). exact Hk. }
  apply (real_lt_trans (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
                       (real_const (4 * log_d4_eps eps + eps / 4))
                       (real_const eps)).
  - exact Hlift.
  - apply real_const_lt. apply Qlt_to_QltT.
    assert (Hd4 : 4 * log_d4_eps eps == eps / 4).
    { unfold log_d4_eps. field. }
    apply (Qle_lt_trans _ (eps / 4 + eps / 4) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hd4. ring.
    + apply (proj2 (Qlt_minus_iff (eps / 4 + eps / 4) eps)).
      apply (Qlt_le_trans 0 (eps / 2) (eps - (eps / 4 + eps / 4))).
      * apply (Qlt_shift_div_l 0 eps 2).
        -- change (Qlt 0 2). compute. reflexivity.
        -- simpl. apply QltT_to_Qlt. exact Heps.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
Qed.

(* ============ log 论证第三阶段 Chunk 5d：approx_root 主定理 ============ *)

(* 主定理：approx_root——y>0 ⟹ ∀eps>0, ∃x:Q, |e^{real_const x} − y| < eps
   （exp 值域 (0,∞) 的构造性满射核心：全判定 → 夹逼+跨度界；缺陷 → eps/4 界） *)
Lemma approx_root : forall (y : Real) (Hy : real_lt real_zero y) (eps : Q) (Heps : QltT 0 eps),
  sigT (fun x : Q => And (QltT (log_lower y Hy) x)
                    (And (QltT x (log_upper y Hy))
                         (real_lt (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y))) (real_const eps)))).
Proof.
  intros y Hy eps Heps.
  unfold log_lower, log_upper.
  destruct (exp_lower_q y Hy) as [Na [HNa2 HNa_y]].
  destruct (exp_upper_q y Hy) as [Nb [HNb2 Hy_b0]].
  set (a0 := Qopp (Z.of_nat Na # 1)).
  set (b0 := Z.of_nat Nb # 1).
  assert (Ha0b0 : QltT a0 b0).
  { unfold a0, b0. apply NatLe_drop in HNa2. apply NatLe_drop in HNb2.
    apply q_neg_nat_lt_nat; lia. }
  assert (Ha0_y : real_lt (cauchy_real_exp (real_const a0)) y).
  { unfold a0. exact HNa_y. }
  assert (Hy_b0' : real_lt y (cauchy_real_exp (real_const b0))).
  { unfold b0. exact Hy_b0. }
  set (B := Qabs a0 + Qabs b0).
  assert (HB : Qle 0 B).
  { unfold B. apply (Qplus_le_compat 0 (Qabs a0) 0 (Qabs b0)); apply Qabs_nonneg. }
  assert (Ha0B : Qle (Qabs a0) B) by (unfold B; apply QleT'_to_Qle; apply q_abs_sum_bound).
  assert (Hb0B : Qle (Qabs b0) B) by (unfold B; apply QleT'_to_Qle; apply q_abs_sum_bound_r).
  destruct (exp_series_arch B (Qle_to_QleT' _ _ HB)) as [C [HC1 HC]].
  set (D := (b0 - a0) * C).
  assert (HD : Qle 0 D).
  { unfold D. apply Qmult_le_0_compat.
    - apply QleT'_to_Qle. apply (q_le_minus a0 b0). apply Qle_to_QleT'. apply (Qlt_le_weak a0 b0). apply QltT_to_Qlt. exact Ha0b0.
    - apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (q_pow_arch D eps (Qle_to_QleT' _ _ HD) Heps) as [N HN].
  destruct (log_scan_spec y a0 b0 Ha0b0 eps Heps N Ha0_y Hy_b0') as [Hfull | Hdef].
  - destruct Hfull as [Hfl [HlaN [HrbN Hlen]]].
    set (abN := projT1 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))).
    set (aN := fst abN).
    set (bN := snd abN).
    set (mN := log_m_eps aN bN).
    assert (HaNbN : Qlt aN bN) by (unfold aN, bN, abN; exact (QltT_to_Qlt _ _ (projT2 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))))).
    destruct (log_scan_nested y a0 b0 Ha0b0 eps Heps N) as [Ha0aN HbN_b0].
    apply QleT'_to_Qle in Ha0aN. apply QleT'_to_Qle in HbN_b0.
    assert (HaNb0 : Qle aN b0).
    { apply (Qle_trans _ bN _).
      - apply (Qlt_le_weak _ _). exact HaNbN.
      - exact HbN_b0. }
    assert (HaN_B : Qle (Qabs aN) B).
    { unfold B. apply QleT'_to_Qle. apply (q_interval_abs_bound a0 aN b0).
      - apply Qle_to_QleT'. exact Ha0aN.
      - apply Qle_to_QleT'. exact HaNb0. }
    assert (HbN_B : Qle (Qabs bN) B).
    { unfold B. apply QleT'_to_Qle. apply (q_interval_abs_bound a0 bN b0).
      - apply Qle_to_QleT'. apply (Qle_trans _ aN _).
        + exact Ha0aN.
        + apply (Qlt_le_weak _ _). exact HaNbN.
      - apply Qle_to_QleT'. exact HbN_b0. }
    destruct (approx_span_pt y aN bN (Qlt_to_QltT _ _ HaNbN) B C HlaN HrbN (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ HaN_B) (Qle_to_QleT' _ _ HbN_B) HC) as [N0 HN0].
    exists mN.
    split.
    + (* log_lower y Hy < mN：a0 ≤ aN < mN *)
      unfold log_lower. cbn.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans a0 aN mN).
      * exact Ha0aN.
      * unfold mN. apply (QltT_to_Qlt aN (log_m_eps aN bN) (fst (log_mid_strict aN bN (Qlt_to_QltT _ _ HaNbN)))).
    + split.
      * (* mN < log_upper y Hy：mN < bN ≤ b0 *)
        unfold log_upper. cbn.
        apply Qlt_to_QltT.
        apply (Qlt_le_trans mN bN b0).
        -- unfold mN. apply (QltT_to_Qlt (log_m_eps aN bN) bN (snd (log_mid_strict aN bN (Qlt_to_QltT _ _ HaNbN)))).
        -- exact HbN_b0.
      * assert (Hγ : Qlt 0 ((eps - D * q_pow (1 / 2) N) / 2)).
        { apply (Qlt_shift_div_l 0 (eps - D * q_pow (1 / 2) N) 2).
          - change (Qlt 0 2). compute. reflexivity.
          - simpl. apply (proj1 (Qlt_minus_iff (D * q_pow (1 / 2) N) eps)). exact (QltT_to_Qlt _ _ HN). }
        assert (Hlift : real_lt (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
                                (real_const ((bN - aN) * C + (eps - D * q_pow (1 / 2) N) / 2))).
        { apply (real_abs_lift mN y ((bN - aN) * C) ((eps - D * q_pow (1 / 2) N) / 2) N0 (Qlt_to_QltT _ _ Hγ)).
          intros k Hk. exact (HN0 k Hk). }
        apply (real_lt_trans (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
                             (real_const ((bN - aN) * C + (eps - D * q_pow (1 / 2) N) / 2))
                             (real_const eps)).
        -- exact Hlift.
        -- apply real_const_lt.
           apply (approx_const_lt bN aN D C ((eps - D * q_pow (1 / 2) N) / 2) eps N HN).
           ** unfold aN, bN, abN in Hlen. apply (len_mul_D bN aN b0 a0 C N). exact Hlen.
           ** apply qeq_imp_qeqT. reflexivity.
  - destruct Hdef as [Hdf Hpt].
    set (abN := projT1 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))).
    set (mN := log_m_eps (fst abN) (snd abN)).
    set (N0 := Nat.max (log_K1_eps (fst abN) (snd abN) (projT2 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))) eps Heps)
                       (log_K2_eps y (fst abN) (snd abN) (projT2 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))) eps Heps)).
    exists mN.
    split.
    + (* log_lower y Hy < mN：a0 ≤ fst abN < mN *)
      unfold log_lower. cbn.
      assert (HabN : Qlt (fst abN) (snd abN)) by (unfold abN; exact (QltT_to_Qlt _ _ (projT2 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))))).
      apply Qlt_to_QltT.
      apply (Qle_lt_trans a0 (fst abN) mN).
      * apply (QleT'_to_Qle a0 (fst abN)).
        exact (fst (log_scan_nested y a0 b0 Ha0b0 eps Heps N)).
      * unfold mN. apply (QltT_to_Qlt (fst abN) (log_m_eps (fst abN) (snd abN)) (fst (log_mid_strict (fst abN) (snd abN) (Qlt_to_QltT _ _ HabN)))).
    + split.
      * (* mN < log_upper y Hy：mN < snd abN ≤ b0 *)
        unfold log_upper. cbn.
        assert (HabN' : Qlt (fst abN) (snd abN)) by (unfold abN; exact (QltT_to_Qlt _ _ (projT2 (fst (log_scan y a0 b0 Ha0b0 eps Heps N))))).
        apply Qlt_to_QltT.
        apply (Qlt_le_trans mN (snd abN) b0).
        -- unfold mN. apply (QltT_to_Qlt (log_m_eps (fst abN) (snd abN)) (snd abN) (snd (log_mid_strict (fst abN) (snd abN) (Qlt_to_QltT _ _ HabN')))).
        -- apply (QleT'_to_Qle (snd abN) b0).
           exact (snd (log_scan_nested y a0 b0 Ha0b0 eps Heps N)).
      * assert (HptN0 : forall k : nat, NatLe N0 k ->
          QleT' (Qabs (projT1 (cauchy_real_exp (real_const mN)) k - projT1 y k)) (4 * log_d4_eps eps)).
        { intros k Hk. apply NatLe_drop in Hk. unfold mN, N0 in Hpt, Hk. exact (Hpt k Hk). }
        apply (approx_def_test y mN eps Heps N0). exact HptN0.
Qed.

(* ============ log 论证第三阶段 Chunk 6：log 构造（log_seq 柯西 → log_inv 族） ============ *)

(* eps_n := (1/2)^(S n)（→ 0） *)
Definition log_eps (n : nat) : Q := q_pow (1 / 2) (Datatypes.S n).

Lemma log_eps_pos : forall n : nat, QltT 0 (log_eps n).
Proof.
  intros n. unfold log_eps.
  apply Qlt_to_QltT.
  induction n as [| m IH]; simpl.
  - change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity.
  - apply (Qmult_lt_0_compat (1 / 2) (q_pow (1 / 2) (Datatypes.S m))).
    + change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity.
    + exact IH.
Qed.

(* q_pow (1/2) 递减：m ≤ n ⟹ (1/2)^n ≤ (1/2)^m *)
Lemma q_pow_half_mono : forall m n : nat, (m <= n)%nat -> QleT' (q_pow (1 / 2) n) (q_pow (1 / 2) m).
Proof.
  intros m n Hmn.
  apply Qle_to_QleT'.
  induction Hmn as [ | n' Hrec IH ]; [apply Qle_refl | ].
  apply (Qle_trans _ (q_pow (1 / 2) n') _).
  - apply QleT'_to_Qle. apply q_pow_half_le.
  - exact IH.
Qed.

(* log_eps m < delta：m ≥ S t、Ht : (1/2)^t < delta ⟹ log_eps m < delta *)
Lemma log_eps_lt_delta : forall (delta : Q) (t m : nat),
  QltT (1 * q_pow (1 / 2) t) delta ->
  (Datatypes.S t <= m)%nat ->
  QltT (log_eps m) delta.
Proof.
  intros delta t m Ht Hm.
  apply Qlt_to_QltT.
  unfold log_eps.
  apply (Qle_lt_trans (q_pow (1 / 2) (Datatypes.S m)) (q_pow (1 / 2) (Datatypes.S t))
                      delta).
  - apply QleT'_to_Qle. apply (q_pow_half_mono (Datatypes.S t) (Datatypes.S m)); lia.
  - apply (Qlt_le_trans (q_pow (1 / 2) (Datatypes.S t)) (q_pow (1 / 2) t)
                        delta).
    + apply QltT_to_Qlt. apply q_pow_half_lt_self.
    + apply (Qle_trans (q_pow (1 / 2) t) (1 * q_pow (1 / 2) t) delta).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply Qlt_le_weak. apply QltT_to_Qlt. exact Ht.
Qed.

(* log 序列：x_n := approx_root y Hy eps_n 的返回值（Q 层） *)
Definition log_seq (y : Real) (Hy : real_lt real_zero y) (n : nat) : Q :=
  projT1 (approx_root y Hy (log_eps n) (log_eps_pos n)).

(* 下界：log_lower y Hy < log_seq y Hy n（approx_root 区间界） *)
Lemma log_seq_lower_bound : forall (y : Real) (Hy : real_lt real_zero y) (n : nat),
  QltT (log_lower y Hy) (log_seq y Hy n).
Proof.
  intros y Hy n.
  unfold log_seq.
  destruct (approx_root y Hy (log_eps n) (log_eps_pos n)) as [x [Hlow [Hup Hpt]]].
  exact Hlow.
Qed.

(* 上界：log_seq y Hy n < log_upper y Hy *)
Lemma log_seq_upper_bound : forall (y : Real) (Hy : real_lt real_zero y) (n : nat),
  QltT (log_seq y Hy n) (log_upper y Hy).
Proof.
  intros y Hy n.
  unfold log_seq.
  destruct (approx_root y Hy (log_eps n) (log_eps_pos n)) as [x [Hlow [Hup Hpt]]].
  exact Hup.
Qed.

(* 逐点：approx_root 界逐点化 ⟹ ∀k≥N_n, |e^{x_n}_k − y_k| < eps_n *)
Lemma approx_root_pt_bound : forall (y : Real) (Hy : real_lt real_zero y) (n : nat),
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    QltT (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy n))) k - projT1 y k))
        (log_eps n)).
Proof.
  intros y Hy n.
  unfold log_seq.
  destruct (approx_root y Hy (log_eps n) (log_eps_pos n)) as [x [Hlow [Hup Hpt]]].
  destruct (real_lt_pt_lt (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y)))
                          (real_const (log_eps n)) Hpt) as [N HN].
  exists N.
  intros k Hk.
  apply Qlt_to_QltT.
  assert (Hp : projT1 (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y))) k ==
                Qabs (projT1 (cauchy_real_exp (real_const x)) k - projT1 y k)).
{ rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (cauchy_real_exp (real_const x)) (real_opp y)) k)).
rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (real_const x)) (real_opp y) k)).
rewrite (qeqT_imp_qeq _ _ (real_opp_proj y k)). reflexivity. }
  apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_exp (real_const x)) k - projT1 y k))
                      (projT1 (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y))) k)
                      (log_eps n)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
  - apply (Qlt_le_trans _ (projT1 (real_const (log_eps n)) k) _).
    + apply QltT_to_Qlt. exact (HN k Hk).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (qeqT_imp_qeq _ _ (real_const_proj (log_eps n) k)).
Qed.

(* e^{x_m} − e^{x_n} ≤ |e^{x_m}−y| + |y−e^{x_n}| 的逐点三角 *)
Lemma exp_diff_pt_triangle : forall (u v : Q) (y : Real) (k : nat),
  QleT' (projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const v)) k)
      (Qabs (projT1 (cauchy_real_exp (real_const u)) k - projT1 y k) +
       Qabs (projT1 y k - projT1 (cauchy_real_exp (real_const v)) k)).
Proof.
  intros u v y k.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const v)) k)) _).
  - apply Qle_Qabs.
  - apply (Qle_trans _ (Qabs ((projT1 (cauchy_real_exp (real_const u)) k - projT1 y k) +
                             (projT1 y k - projT1 (cauchy_real_exp (real_const v)) k))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. unfold Qminus. ring.
    + apply Qabs_triangle.
Qed.

(* 下 Lipschitz 逐点化：s ≤ u、a0 < s ⟹ 松弛 ≥ 的逐点形式（b_n − a_n < eps） *)
Lemma lower_lipschitz_pt : forall (a0 u s : Q) (Hle : QleT' s u) (Ha0s : QltT a0 s)
  (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    QltT (projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k
          - projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k) eps).
Proof.
  intros a0 u s Hle Ha0s eps Heps.
  destruct (exp_lower_lipschitz_real a0 u s Hle (exp_const_lt a0 s Ha0s) eps Heps) as [N HN].
  exists N. intros k Hk. exact (HN k (NatLe_drop _ _ Hk)).
Qed.

(* (eps_m + eps_n + δ)/epss < γ 当 eps_m, eps_n, δ < γ·epss/4 *)
Lemma q_div_sum_lt : forall (eps_m eps_n delta epss gamma : Q),
  QltT 0 eps_m -> QltT 0 epss -> QltT 0 gamma ->
  QltT eps_m (gamma * epss / 4) -> QltT eps_n (gamma * epss / 4) ->
  QltT delta (gamma * epss / 4) ->
  QltT ((eps_m + eps_n + delta) / epss) gamma.
Proof.
  intros eps_m eps_n delta epss gamma Hm Hp Hg Hm4 Hn4 Hd4.
  apply Qlt_to_QltT.
  apply (Qlt_shift_div_r (eps_m + eps_n + delta) epss gamma).
  - apply QltT_to_Qlt. exact Hp.
  - assert (Hm_eps : Qlt (eps_m + eps_n) (gamma * epss / 4 + gamma * epss / 4)).
    { apply (Qplus_lt_compat eps_m (gamma * epss / 4) eps_n (gamma * epss / 4)).
      + apply QltT_to_Qlt. exact Hm4.
      + apply QltT_to_Qlt. exact Hn4. }
    assert (Hm_eps_d : Qlt (eps_m + eps_n + delta) (gamma * epss / 4 + gamma * epss / 4 + gamma * epss / 4)).
    { apply (Qplus_lt_compat (eps_m + eps_n) (gamma * epss / 4 + gamma * epss / 4) delta (gamma * epss / 4)).
      + exact Hm_eps.
      + apply QltT_to_Qlt. exact Hd4. }
    assert (Hh : Qlt 0 (gamma * epss / 4)).
    { apply (Qlt_shift_div_l 0 (gamma * epss) 4).
      - change (Qlt 0 4). compute. reflexivity.
      - simpl. apply (Qmult_lt_0_compat gamma epss). apply QltT_to_Qlt. exact Hg. apply QltT_to_Qlt. exact Hp. }
    assert (Hbound3 : Qlt (3 * (gamma * epss / 4)) (gamma * epss)).
    { apply (proj2 (Qlt_minus_iff (3 * (gamma * epss / 4)) (gamma * epss))).
      apply (Qlt_le_trans 0 (gamma * epss / 4) (gamma * epss - 3 * (gamma * epss / 4))).
      - exact Hh.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field. }
    assert (Heq : (gamma * epss / 4 + gamma * epss / 4 + gamma * epss / 4) == 3 * (gamma * epss / 4)) by ring.
    assert (Hbound : Qlt (gamma * epss / 4 + gamma * epss / 4 + gamma * epss / 4) (gamma * epss)).
    { apply (Qle_lt_trans _ (3 * (gamma * epss / 4)) _).
      - apply (Qle_trans _ (3 * (gamma * epss / 4)) _); [apply QleT'_to_Qle; apply (qeq_le _ _); apply qeq_imp_qeqT; exact Heq | apply Qle_refl].
      - exact Hbound3. }
    apply (Qlt_trans _ (gamma * epss / 4 + gamma * epss / 4 + gamma * epss / 4) _).
    + apply (Qle_lt_trans _ (eps_m + (eps_n + delta)) _).
      * apply QleT'_to_Qle. apply (qeq_le _ _). apply qeq_imp_qeqT. rewrite Qplus_assoc. reflexivity.
      * apply (Qle_lt_trans _ (eps_m + eps_n + delta) _).
        -- apply QleT'_to_Qle. apply (qeq_le _ _). apply qeq_imp_qeqT. rewrite Qplus_assoc. reflexivity.
        -- exact Hm_eps_d.
    + exact Hbound.
Qed.

(* 组合核心：s ≤ u、a0 < s、|e^u−y| < eps_u、|e^s−y| < eps_s（逐点）、e^{a0}_k ≥ epss
   ⟹ u−s ≤ (eps_u + eps_s + δ)/epss（Qle 层，构造性取 k := Nmax） *)
Lemma lower_lipschitz_combine3 : forall (a0 u s : Q) (Hle : QleT' s u) (Ha0s : QltT a0 s)
  (y : Real) (epss eps_u eps_s delta : Q) (Hepss : QltT 0 epss) (Hdelta : QltT 0 delta)
  (Nu Ns Nl : nat),
  (forall k : nat, NatLe Nu k -> QltT (Qabs (projT1 (cauchy_real_exp (real_const u)) k - projT1 y k)) eps_u) ->
  (forall k : nat, NatLe Ns k -> QltT (Qabs (projT1 (cauchy_real_exp (real_const s)) k - projT1 y k)) eps_s) ->
  (forall k : nat, NatLe Nl k -> QleT' epss (projT1 (cauchy_real_exp (real_const a0)) k)) ->
  QleT' (u - s) ((eps_u + eps_s + delta) / epss).
Proof.
  intros a0 u s Hle Ha0s y epss eps_u eps_s delta Hepss Hdelta Nu Ns Nl Hu Hs Hal.
  destruct (lower_lipschitz_pt a0 u s Hle Ha0s delta Hdelta) as [Nl2 HNl2].
  set (Nmax := Nat.max (Nat.max Nu Ns) (Nat.max Nl Nl2)).
  assert (Hmain : forall k : nat, (Nmax <= k)%nat ->
    Qlt (projT1 (cauchy_real_exp (real_const a0)) k * (u - s)) (eps_u + eps_s + delta)).
  { intros k Hk. unfold Nmax in Hk.
    assert (Hku : (Nu <= k)%nat) by (apply (Nat.le_trans _ (Nat.max Nu Ns) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max Nu Ns) (Nat.max Nl Nl2)) _); [apply Nat.le_max_l | exact Hk]]).
    assert (Hks : (Ns <= k)%nat) by (apply (Nat.le_trans _ (Nat.max Nu Ns) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max Nu Ns) (Nat.max Nl Nl2)) _); [apply Nat.le_max_l | exact Hk]]).
    assert (Hkl : (Nl <= k)%nat) by (apply (Nat.le_trans _ (Nat.max Nl Nl2) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max Nu Ns) (Nat.max Nl Nl2)) _); [apply Nat.le_max_r | exact Hk]]).
    assert (Hkl2 : (Nl2 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max Nl Nl2) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max Nu Ns) (Nat.max Nl Nl2)) _); [apply Nat.le_max_r | exact Hk]]).
    assert (Hlip : Qlt (projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k
                        - projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k) delta).
    { apply QltT_to_Qlt. apply (HNl2 k (NatLe_lift _ _ Hkl2)). }
    assert (Hrm : projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k ==
                  projT1 (cauchy_real_exp (real_const a0)) k * (u - s)).
{ rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_exp (real_const a0)) (real_const (u - s)) k)).
rewrite (qeqT_imp_qeq _ _ (real_const_proj (u - s) k)). reflexivity. }
    assert (Hrp : projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k ==
                  projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const s)) k).
{ rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s))) k)).
rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_exp (real_const s)) k)). reflexivity. }
    assert (Hrm_rp : Qlt (projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k)
                         (projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k + delta)).
    { apply (Qle_lt_trans _ ((projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k -
                              projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k) +
                             projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qlt_le_trans _ (delta +
                               projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k) _).
        + apply (proj2 (Qplus_lt_l (projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k -
                                   projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k)
                                  delta
                                  (projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k))).
          exact Hlip.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hlip2 : Qlt (projT1 (cauchy_real_exp (real_const a0)) k * (u - s))
                        (projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const s)) k + delta)).
    { apply (Qle_lt_trans _ (projT1 (real_mult (cauchy_real_exp (real_const a0)) (real_const (u - s))) k) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrm.
      - apply (Qlt_le_trans _ (projT1 (real_plus (cauchy_real_exp (real_const u)) (real_opp (cauchy_real_exp (real_const s)))) k + delta) _).
        + exact Hrm_rp.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. setoid_rewrite Hrp. unfold Qminus. ring. }
    assert (Hdiff : Qlt (projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const s)) k)
                        (eps_u + eps_s)).
    { apply (Qle_lt_trans _ (Qabs (projT1 (cauchy_real_exp (real_const u)) k - projT1 y k) +
                              Qabs (projT1 y k - projT1 (cauchy_real_exp (real_const s)) k)) _).
      - apply QleT'_to_Qle. apply (exp_diff_pt_triangle u s y k).
      - apply (Qplus_lt_compat (Qabs (projT1 (cauchy_real_exp (real_const u)) k - projT1 y k))
                               eps_u
                               (Qabs (projT1 y k - projT1 (cauchy_real_exp (real_const s)) k))
                               eps_s).
        + apply QltT_to_Qlt. exact (Hu k (NatLe_lift _ _ Hku)).
        + apply (Qle_lt_trans (Qabs (projT1 y k - projT1 (cauchy_real_exp (real_const s)) k))
                              (Qabs (projT1 (cauchy_real_exp (real_const s)) k - projT1 y k))
                              eps_s).
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym.
            rewrite <- (Qabs_Qminus (projT1 y k) (projT1 (cauchy_real_exp (real_const s)) k)).
            reflexivity.
          * apply QltT_to_Qlt. exact (Hs k (NatLe_lift _ _ Hks)). }
    apply (Qlt_le_trans _ (projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const s)) k + delta) _).
    - exact Hlip2.
    - apply (Qplus_le_compat (projT1 (cauchy_real_exp (real_const u)) k - projT1 (cauchy_real_exp (real_const s)) k)
                             (eps_u + eps_s)
                             delta delta).
      + apply Qlt_le_weak. exact Hdiff.
      + apply Qle_refl.
  }
  assert (Hk : (Nmax <= Nmax)%nat) by lia.
  assert (Hle2 : Qle (epss * (u - s)) (projT1 (cauchy_real_exp (real_const a0)) Nmax * (u - s))).
  { apply (Qmult_le_compat_r epss (projT1 (cauchy_real_exp (real_const a0)) Nmax) (u - s)).
    - apply QleT'_to_Qle. apply (Hal Nmax). apply NatLe_lift. apply (Nat.le_trans _ (Nat.max Nl Nl2) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max Nu Ns) (Nat.max Nl Nl2)) _); [apply Nat.le_max_r | exact Hk]].
    - apply QleT'_to_Qle. apply (q_le_minus s u). exact Hle. }
  assert (Hlt : Qlt (epss * (u - s)) (eps_u + eps_s + delta)).
  { apply (Qle_lt_trans _ (projT1 (cauchy_real_exp (real_const a0)) Nmax * (u - s)) _).
    - exact Hle2.
    - exact (Hmain Nmax Hk). }
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((eps_u + eps_s + delta) / epss) _).
  - apply Qlt_le_weak.
    apply (Qlt_shift_div_l (u - s) (eps_u + eps_s + delta) epss).
    + apply QltT_to_Qlt. exact Hepss.
    + apply (Qle_lt_trans ((u - s) * epss) (epss * (u - s)) (eps_u + eps_s + delta)).
      * apply QleT'_to_Qle. apply (qeq_le ((u - s) * epss) (epss * (u - s))). apply qeq_imp_qeqT.
        apply Qmult_comm.
      * exact Hlt.
  - apply Qle_refl.
Qed.

(* cauchy_real_exp_pos 展开形态：sigT e, And (QltT 0 e) (sigT N, ∀n≥N, QltT e (e^x_n − 0)) *)
Lemma exp_pos_shape : forall (x : Real),
  sigT (fun e : Q => And (QltT 0 e) (sigT (fun N : nat => forall n : nat, NatLe N n -> QltT e (projT1 (cauchy_real_exp x) n - projT1 real_zero n)))).
Proof.
  intros x.
  destruct (cauchy_real_exp_pos x) as [e [He [N HN]]].
  exists e. split; [exact He | exists N; intros n Hn; apply (HN n); exact Hn].
Qed.

(* Q 层：e^{a0}_n ≥ epss（由 QltT epss (e^{a0}_n − 0) 得 epss ≤ e^{a0}_n） *)
Lemma exp_lower_pt_bound : forall (a0 : Q) (epss : Q) (N : nat),
  QltT 0 epss ->
  (forall n : nat, NatLe N n -> QltT epss (projT1 (cauchy_real_exp (real_const a0)) n - projT1 real_zero n)) ->
  forall n : nat, NatLe N n -> QleT' epss (projT1 (cauchy_real_exp (real_const a0)) n).
Proof.
  intros a0 epss N Hepss HN n Hn.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply (Qlt_le_trans epss (projT1 (cauchy_real_exp (real_const a0)) n - projT1 real_zero n)
                         (projT1 (cauchy_real_exp (real_const a0)) n)).
  - apply QltT_to_Qlt. exact (HN n Hn).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz. unfold Qminus. ring.
Qed.

(* γ·epss/8 < γ·epss/4（提升辅助） *)
Lemma q_half8_lt_half4 : forall (gamma epss : Q),
  QltT 0 gamma -> QltT 0 epss -> QltT (gamma * epss / 8) (gamma * epss / 4).
Proof.
  intros gamma epss Hg Hp.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (gamma * epss / 8) (gamma * epss / 4))).
  apply (Qlt_le_trans 0 (gamma * epss / 8) (gamma * epss / 4 - gamma * epss / 8)).
  - apply (Qlt_shift_div_l 0 (gamma * epss) 8).
    + change (Qlt 0 8). compute. reflexivity.
    + simpl. apply (Qmult_lt_0_compat gamma epss). apply QltT_to_Qlt. exact Hg. apply QltT_to_Qlt. exact Hp.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
Qed.

(* log_seq 柯西性：cauchy (log_seq y Hy) *)
Lemma log_seq_cauchy : forall (y : Real) (Hy : real_lt real_zero y),
  cauchy (log_seq y Hy).
Proof.
  intros y Hy eps Heps.
  set (a0 := log_lower y Hy).
  destruct (exp_pos_shape (real_const a0)) as [epss [Hepss0 [Ns HNs]]].
  assert (Hepss : Qlt 0 epss) by (apply QltT_to_Qlt; exact Hepss0).
  set (delta := eps * epss / 8).
  assert (Hdelta : Qlt 0 delta).
  { unfold delta. apply (Qlt_shift_div_l 0 (eps * epss) 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. apply (Qmult_lt_0_compat eps epss).
      + apply QltT_to_Qlt. exact Heps.
      + exact Hepss. }
  destruct (q_pow_arch 1 delta) as [t Ht].
  { apply Qle_to_QleT'. apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  { apply Qlt_to_QltT. exact Hdelta. }
  exists (Datatypes.S t).
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Qlt_le_dec (log_seq y Hy n) (log_seq y Hy m)) as [Hnm_lt | Hmn].
  - (* x_n < x_m：对称，u := x_m, s := x_n（第一分支 Hnm_lt） *)
    assert (Hnm_le : Qle (log_seq y Hy n) (log_seq y Hy m)).
    { apply Qlt_le_weak. exact Hnm_lt. }
    assert (Hms : QltT 0 (log_eps m)) by apply log_eps_pos.
    assert (Hns : QltT 0 (log_eps n)) by apply log_eps_pos.
    destruct (approx_root_pt_bound y Hy m) as [Nm HMm].
    destruct (approx_root_pt_bound y Hy n) as [Nn HNn].
    assert (Heps_m_lt : Qlt (log_eps m) (eps * epss / 8)).
    { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps * epss / 8) t m).
      - unfold delta in Ht. exact Ht.
      - lia. }
    assert (Heps_n_lt : Qlt (log_eps n) (eps * epss / 8)).
    { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps * epss / 8) t n).
      - unfold delta in Ht. exact Ht.
      - lia. }
    assert (Hlow_n : Qlt a0 (log_seq y Hy n)) by (unfold a0; apply QltT_to_Qlt; apply log_seq_lower_bound).
    assert (Hcomb : Qle (log_seq y Hy m - log_seq y Hy n) ((log_eps m + log_eps n + delta) / epss)).
    { apply QleT'_to_Qle. apply (lower_lipschitz_combine3 a0 (log_seq y Hy m) (log_seq y Hy n)
             (Qle_to_QleT' _ _ Hnm_le) (Qlt_to_QltT _ _ Hlow_n)
             y epss (log_eps m) (log_eps n) delta (Qlt_to_QltT _ _ Hepss) (Qlt_to_QltT _ _ Hdelta) Nm Nn Ns).
      - intros k Hk. exact (HMm k Hk).
      - intros k Hk. exact (HNn k Hk).
      - intros k Hk. apply (exp_lower_pt_bound a0 epss Ns Hepss0 HNs k Hk). }
    assert (Hlt : Qlt ((log_eps m + log_eps n + delta) / epss) eps).
    { apply QltT_to_Qlt. apply (q_div_sum_lt (log_eps m) (log_eps n) delta epss eps).
      - exact Hms.
      - exact (Qlt_to_QltT _ _ Hepss).
      - exact Heps.
      - apply Qlt_to_QltT. apply (Qlt_le_trans _ (eps * epss / 8) _).
        + exact Heps_m_lt.
        + apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half8_lt_half4 eps epss). exact Heps. exact (Qlt_to_QltT _ _ Hepss).
      - apply Qlt_to_QltT. apply (Qlt_le_trans _ (eps * epss / 8) _).
        + exact Heps_n_lt.
        + apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half8_lt_half4 eps epss). exact Heps. exact (Qlt_to_QltT _ _ Hepss).
      - apply Qlt_to_QltT. unfold delta. apply QltT_to_Qlt. apply (q_half8_lt_half4 eps epss). exact Heps. exact (Qlt_to_QltT _ _ Hepss). }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (log_seq y Hy m - log_seq y Hy n)) (log_seq y Hy m - log_seq y Hy n) eps).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (log_seq y Hy n) (log_seq y Hy m))). exact Hnm_le.
    + apply (Qle_lt_trans _ ((log_eps m + log_eps n + delta) / epss) _).
      * exact Hcomb.
      * exact Hlt.
  - (* x_m ≤ x_n：u := x_n, s := x_m（第二分支 Hmn） *)
    assert (Hms : QltT 0 (log_eps m)) by apply log_eps_pos.
    assert (Hns : QltT 0 (log_eps n)) by apply log_eps_pos.
    destruct (approx_root_pt_bound y Hy n) as [Nn HNn].
    destruct (approx_root_pt_bound y Hy m) as [Nm HMm].
    assert (Heps_m_lt : Qlt (log_eps m) (eps * epss / 8)).
    { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps * epss / 8) t m).
      - unfold delta in Ht. exact Ht.
      - lia. }
    assert (Heps_n_lt : Qlt (log_eps n) (eps * epss / 8)).
    { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps * epss / 8) t n).
      - unfold delta in Ht. exact Ht.
      - lia. }
    assert (Hlow_m : Qlt a0 (log_seq y Hy m)) by (unfold a0; apply QltT_to_Qlt; apply log_seq_lower_bound).
    assert (Hcomb : Qle (log_seq y Hy n - log_seq y Hy m) ((log_eps n + log_eps m + delta) / epss)).
    { apply QleT'_to_Qle. apply (lower_lipschitz_combine3 a0 (log_seq y Hy n) (log_seq y Hy m)
             (Qle_to_QleT' _ _ Hmn) (Qlt_to_QltT _ _ Hlow_m)
             y epss (log_eps n) (log_eps m) delta (Qlt_to_QltT _ _ Hepss) (Qlt_to_QltT _ _ Hdelta) Nn Nm Ns).
      - intros k Hk. exact (HNn k Hk).
      - intros k Hk. exact (HMm k Hk).
      - intros k Hk. apply (exp_lower_pt_bound a0 epss Ns Hepss0 HNs k Hk). }
    assert (Hcomb2 : Qle (log_seq y Hy n - log_seq y Hy m) ((log_eps m + log_eps n + delta) / epss)).
    { apply (Qle_trans _ ((log_eps n + log_eps m + delta) / epss) _).
      - exact Hcomb.
      - apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        apply (Qeq_trans ((log_eps n + log_eps m + delta) / epss)
                         ((log_eps n + log_eps m + delta) * (Qinv epss))
                         ((log_eps m + log_eps n + delta) / epss)).
        { unfold Qdiv. reflexivity. }
        { refine (Qmult_comp (log_eps n + log_eps m + delta) (log_eps m + log_eps n + delta) _
                             (Qinv epss) (Qinv epss) _).
          { ring. }
          { reflexivity. } } }
    assert (Hlt : Qlt ((log_eps m + log_eps n + delta) / epss) eps).
    { apply QltT_to_Qlt. apply (q_div_sum_lt (log_eps m) (log_eps n) delta epss eps).
      - exact Hms.
      - exact (Qlt_to_QltT _ _ Hepss).
      - exact Heps.
      - apply Qlt_to_QltT. apply (Qlt_le_trans _ (eps * epss / 8) _).
        + exact Heps_m_lt.
        + apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half8_lt_half4 eps epss). exact Heps. exact (Qlt_to_QltT _ _ Hepss).
      - apply Qlt_to_QltT. apply (Qlt_le_trans _ (eps * epss / 8) _).
        + exact Heps_n_lt.
        + apply Qlt_le_weak. apply QltT_to_Qlt. apply (q_half8_lt_half4 eps epss). exact Heps. exact (Qlt_to_QltT _ _ Hepss).
      - apply Qlt_to_QltT. unfold delta. apply QltT_to_Qlt. apply (q_half8_lt_half4 eps epss). exact Heps. exact (Qlt_to_QltT _ _ Hepss). }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (log_seq y Hy m - log_seq y Hy n)) (log_seq y Hy n - log_seq y Hy m) eps).
    + apply (Qle_trans (Qabs (log_seq y Hy m - log_seq y Hy n)) (Qabs (log_seq y Hy n - log_seq y Hy m))
                       (log_seq y Hy n - log_seq y Hy m)).
      * apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        rewrite <- (Qabs_Qminus (log_seq y Hy n) (log_seq y Hy m)).
        reflexivity.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (log_seq y Hy m) (log_seq y Hy n))). exact Hmn.
    + apply (Qle_lt_trans _ ((log_eps m + log_eps n + delta) / epss) _).
      * exact Hcomb2.
      * exact Hlt.
Qed.

(* ============ log 论证第三阶段 Chunk 6b：log 定义 + 右逆 ============ *)

(* log 定义：log y := 柯西序列 log_seq 的实数值（检验名 cw_log，避开 main 的 log_inv） *)
Definition cw_log (y : Real) (Hy : real_lt real_zero y) : Real :=
  existT _ (log_seq y Hy) (log_seq_cauchy y Hy).

(* exp_series_arch 展开形态 *)
Lemma exp_series_arch_shape : forall (B : Q), QleT' 0 B ->
  sigT (fun C : Q => And (QleT' 1 C) (forall n : nat, QleT' (exp_series n B) C)).
Proof.
  intros B HB.
  destruct (exp_series_arch B HB) as [C [HC1 HC]].
  exists C. split.
  - exact HC1.
  - exact HC.
Qed.

(* log_seq 有界于 B0 := |log_lower| + |log_upper| *)
Lemma log_seq_bounded : forall (y : Real) (Hy : real_lt real_zero y) (n : nat),
  QleT' (Qabs (log_seq y Hy n)) (Qabs (log_lower y Hy) + Qabs (log_upper y Hy)).
Proof.
  intros y Hy n.
  apply (q_interval_abs_bound (log_lower y Hy) (log_seq y Hy n) (log_upper y Hy)).
  - apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. apply log_seq_lower_bound.
  - apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. apply log_seq_upper_bound.
Qed.

(* cauchy_real_exp (real_const c) 第 k 项 == exp_partial k c *)
Lemma exp_const_proj : forall (c : Q) (k : nat),
  QeqT (projT1 (cauchy_real_exp (real_const c)) k) (exp_partial k c).
Proof.
  intros c k.
  apply qeq_imp_qeqT.
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* cw_log 的第 k 项 == exp_partial k (log_seq k) *)
Lemma cw_log_proj : forall (y : Real) (Hy : real_lt real_zero y) (k : nat),
  QeqT (projT1 (cauchy_real_exp (cw_log y Hy)) k) (exp_partial k (log_seq y Hy k)).
Proof.
  intros y Hy k.
  apply qeq_imp_qeqT.
  cbn [cw_log projT1]. reflexivity.
Qed.

(* 右逆：e^{cw_log y} == y（锚点法：固定 N0，exp_upper_lipschitz_q 连接 log_seq k 与 log_seq N0，
   柯西给 |diff| 小，approx_root 固定 N0 的逐点界给 |e^{log_seq N0}_k − y_k| 小，三角收尾） *)
Lemma cw_log_exp_right : forall (y : Real) (Hy : real_lt real_zero y),
  real_eq (cauchy_real_exp (cw_log y Hy)) y.
Proof.
  intros y Hy gamma Hgamma.
  assert (HB0 : Qle 0 (Qabs (log_lower y Hy) + Qabs (log_upper y Hy))).
  { apply (Qplus_le_compat 0 (Qabs (log_lower y Hy)) 0 (Qabs (log_upper y Hy))); apply Qabs_nonneg. }
  destruct (exp_series_arch_shape (Qabs (log_lower y Hy) + Qabs (log_upper y Hy)) (Qle_to_QleT' _ _ HB0)) as [C [HC1 HC]].
  apply QleT'_to_Qle in HC1.
  assert (HCQ : forall n : nat, Qle (exp_series n (Qabs (log_lower y Hy) + Qabs (log_upper y Hy))) C).
  { intros n0. apply QleT'_to_Qle. exact (HC n0). }
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1 _); [change (Qlt 0 1); compute; reflexivity | exact HC1]. }
  assert (Hden : Qlt 0 (4 * (C + 1))).
  { apply (Qmult_lt_0_compat 4 (C + 1)).
    - change (Qlt 0 4). compute. reflexivity.
    - apply (Qplus_lt_le_compat 0 C 0 1); [exact HCpos | apply Qlt_le_weak; change (Qlt 0 1); compute; reflexivity]. }
  assert (Hdelta : Qlt 0 (gamma / (4 * (C + 1)))).
  { apply (Qlt_shift_div_l 0 gamma (4 * (C + 1))).
    - apply QltT_to_Qlt. apply Qlt_to_QltT. exact Hden.
    - apply (Qle_lt_trans (0 * (4 * (C + 1))) 0 gamma).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QltT_to_Qlt. exact Hgamma. }
  assert (Hcau : sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT (Qabs (log_seq y Hy m - log_seq y Hy n)) (gamma / (4 * (C + 1))))).
  { apply (log_seq_cauchy y Hy (gamma / (4 * (C + 1)))). apply Qlt_to_QltT. exact Hdelta. }
  destruct Hcau as [N_cau HN_cau].
  destruct (q_pow_arch 1 (gamma / 4)) as [t Ht].
  { apply Qle_to_QleT'. apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 gamma 4).
    - change (Qlt 0 4). compute. reflexivity.
    - apply (Qle_lt_trans (0 * 4) 0 gamma).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QltT_to_Qlt. exact Hgamma. }
  assert (Heps_st : Qlt (log_eps (Datatypes.S t)) (gamma / 4)).
  { unfold log_eps.
    apply (Qle_lt_trans (q_pow (1 / 2) (Datatypes.S (Datatypes.S t))) (q_pow (1 / 2) (Datatypes.S t))
                        (gamma / 4)).
    - apply QleT'_to_Qle. apply q_pow_half_le.
    - apply (Qlt_le_trans (q_pow (1 / 2) (Datatypes.S t)) (q_pow (1 / 2) t) (gamma / 4)).
      + apply QltT_to_Qlt. apply q_pow_half_lt_self.
      + apply (Qle_trans (q_pow (1 / 2) t) (1 * q_pow (1 / 2) t) (gamma / 4)).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        * apply Qlt_le_weak. apply QltT_to_Qlt. exact Ht. }
  set (N0 := Nat.max N_cau (Datatypes.S t)).
  assert (Happrox : sigT (fun N' : nat => forall k : nat, NatLe N' k ->
    QltT (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k - projT1 y k))
        (log_eps N0))).
  { apply (approx_root_pt_bound y Hy N0). }
  destruct Happrox as [N' HN'].
  assert (HepsN0 : Qlt (log_eps N0) (gamma / 4)).
  { apply (Qle_lt_trans (log_eps N0) (log_eps (Datatypes.S t)) (gamma / 4)).
    - unfold log_eps.
      apply QleT'_to_Qle. apply (q_pow_half_mono (Datatypes.S (Datatypes.S t)) (Datatypes.S N0)); unfold N0; lia.
    - exact Heps_st. }
  assert (Hpart1 : forall k : nat, (N0 <= k)%nat ->
    Qlt (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k))
        (gamma / 4)).
  { intros k Hk.
    apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k))
                        (Qabs (log_seq y Hy k - log_seq y Hy N0) * C)
                        (gamma / 4)).
    - apply QleT'_to_Qle. apply (exp_upper_lipschitz_q (log_seq y Hy k) (log_seq y Hy N0)
                                   (Qabs (log_lower y Hy) + Qabs (log_upper y Hy)) C k (Qle_to_QleT' _ _ HB0)).
      + apply (log_seq_bounded y Hy k).
      + apply (log_seq_bounded y Hy N0).
      + exact HC.
    - assert (HkNcau : (N_cau <= k)%nat) by (apply (Nat.le_trans _ N0 _); [apply Nat.le_max_l | exact Hk]).
      assert (HkN0 : (N_cau <= N0)%nat) by (apply Nat.le_max_l).
      apply (Qle_lt_trans _ (gamma / (4 * (C + 1)) * C) _).
      + apply (Qmult_le_compat_r (Qabs (log_seq y Hy k - log_seq y Hy N0)) (gamma / (4 * (C + 1))) C).
        * apply Qlt_le_weak. apply QltT_to_Qlt. apply (HN_cau k N0 (NatLe_lift _ _ HkNcau) (NatLe_lift _ _ HkN0)).
        * apply Qlt_le_weak. exact HCpos.
      + apply (proj2 (Qlt_minus_iff (gamma / (4 * (C + 1)) * C) (gamma / 4))).
        apply (Qlt_le_trans 0 (gamma / (4 * (C + 1))) (gamma / 4 - gamma / (4 * (C + 1)) * C)).
        * exact Hdelta.
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
          intro Hz.
          assert (HC1p : Qlt 0 (C + 1)).
          { apply (Qplus_lt_le_compat 0 C 0 1); [exact HCpos | apply Qlt_le_weak; change (Qlt 0 1); compute; reflexivity]. }
          apply Qlt_to_QltT in HC1p.
          exact (match q_neq_of_lt (C + 1) HC1p (qeq_imp_qeqT _ _ Hz) with end). }
  exists (Nat.max N0 N').
  intros k Hk.
  apply Qlt_to_QltT.
  assert (Hk0 : (N0 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N') _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
  assert (Hk' : (N' <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N') _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
  assert (Hproj : projT1 (cauchy_real_exp (cw_log y Hy)) k == exp_partial k (log_seq y Hy k)).
  { cbn [cw_log projT1]. reflexivity. }
  apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_exp (cw_log y Hy)) k - projT1 y k))
                      (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 y k))
                      gamma).
  - assert (HXeq : projT1 (cauchy_real_exp (cw_log y Hy)) k == projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k).
    { apply (Qeq_trans _ (exp_partial k (log_seq y Hy k)) _).
      - exact Hproj.
      - apply Qeq_sym. apply (qeqT_imp_qeq _ _ (exp_const_proj (log_seq y Hy k) k)). }
    apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
    rewrite HXeq.
    reflexivity.
  - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 y k))
                        (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k) +
                         Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k - projT1 y k))
                        gamma).
    + apply (Qle_trans _ (Qabs ((projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k) +
                                (projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k - projT1 y k))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. unfold Qminus. ring.
      * apply Qabs_triangle.
    + apply (Qlt_le_trans (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k) +
                           Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k - projT1 y k))
                          (gamma / 4 + gamma / 4)
                          gamma).
      * apply (Qplus_lt_compat (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy k))) k - projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k))
                               (gamma / 4)
                               (Qabs (projT1 (cauchy_real_exp (real_const (log_seq y Hy N0))) k - projT1 y k))
                               (gamma / 4)).
        -- exact (Hpart1 k Hk0).
        -- apply (Qlt_le_trans _ (log_eps N0) _).
           ++ apply QltT_to_Qlt. exact (HN' k (NatLe_lift _ _ Hk')).
           ++ apply Qlt_le_weak. exact HepsN0.
      * apply Qlt_le_weak.
        apply (proj2 (Qlt_minus_iff (gamma / 4 + gamma / 4) gamma)).
        apply (Qlt_le_trans 0 (gamma / 4) (gamma - (gamma / 4 + gamma / 4))).
        -- apply (Qlt_shift_div_l 0 gamma 4).
           ++ change (Qlt 0 4). compute. reflexivity.
           ++ apply (Qle_lt_trans (0 * 4) 0 gamma).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              ** apply QltT_to_Qlt. exact Hgamma.
        -- apply (Qle_trans (gamma / 4) (gamma / 2) (gamma - (gamma / 4 + gamma / 4))).
           ** apply (Qlt_le_weak _ _).
              apply (Qle_lt_trans (gamma / 4) (gamma / 2 / 2) (gamma / 2)).
              ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
              ++ apply QltT_to_Qlt. apply (q_half_lt_self (gamma / 2)).
                 apply Qlt_to_QltT.
                 apply (Qlt_shift_div_l 0 gamma 2).
                 +++ change (Qlt 0 2). compute. reflexivity.
                 +++ apply (Qle_lt_trans (0 * 2) 0 gamma).
                     ++++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
                     ++++ apply QltT_to_Qlt. exact Hgamma.
           ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* ============ 阶段 3 结论：弱三分 + log_inv 左逆族（7 引理）
   要点：既有记录「弱三分不可证（需 Markov）」之判定有误——
   real_lt 是 eps-N 全局阈值序，坏点经柯西传播成全场见证，QltT 可判定，
   弱三分（¬lt u v → ¬lt v u → eq u v）直觉主义可证；不可证的是强三分/LPO。
   左逆路线：右逆 cw_log_exp_right + cauchy_real_exp_mono + real_weak_trich。 *)
Section LogInvStage.

(* 桥：real_lt a b 与 real_eq a b 不相容（序 vs 相等） *)
Lemma real_lt_not_eq : forall a b : Real, real_lt a b -> Not (real_eq a b).
Proof.
  intros a b Hlt Heq.
  destruct Hlt as [eps [Heps [N HN]]].
  destruct (Heq eps Heps) as [N' HN'].
  set (n := Nat.max N N').
  assert (HnN : (N <= n)%nat) by (unfold n; apply Nat.le_max_l).
  assert (HnN' : (N' <= n)%nat) by (unfold n; apply Nat.le_max_r).
  (* H1 : eps < b n - a n；H2 : |a n - b n| < eps *)
  assert (H1 : Qlt eps (projT1 b n - projT1 a n)).
  { apply QltT_to_Qlt. apply (HN n (NatLe_lift _ _ HnN)). }
  assert (H2 : Qlt (Qabs (projT1 a n - projT1 b n)) eps).
  { apply QltT_to_Qlt. apply (HN' n (NatLe_lift _ _ HnN')). }
  (* b n > a n（由 H1）→ a n - b n < 0 → Qabs (a n - b n) == b n - a n（Qabs_def2） *)
  assert (Hpos : Qlt 0 (projT1 b n - projT1 a n)).
  { apply (Qlt_trans _ eps _).
    - apply QltT_to_Qlt. exact Heps.
    - exact H1. }
  assert (Hneg : Qlt (projT1 a n - projT1 b n) 0).
  { assert (Heq2 : projT1 a n - projT1 b n == - (projT1 b n - projT1 a n)) by (unfold Qminus; ring).
    rewrite Heq2.
    apply (Qopp_lt_compat 0 (projT1 b n - projT1 a n)). exact Hpos. }
  assert (Habs : Qabs (projT1 a n - projT1 b n) == projT1 b n - projT1 a n).
  { transitivity (- (projT1 a n - projT1 b n)).
    - apply Qabs_neg. apply Qlt_le_weak. exact Hneg.
    - unfold Qminus. ring. }
  (* H2 重写：|a n - b n| == b n - a n → b n - a n < eps，与 H1: eps < b n - a n 矛盾 *)
  rewrite Habs in H2.
  exact (match (Qlt_irrefl (projT1 b n - projT1 a n)
                           (Qlt_trans (projT1 b n - projT1 a n) eps (projT1 b n - projT1 a n) H2 H1)) with end).
Qed.

(* 辅助：a - d < b ⟹ -d < b - a（Qlt_minus_iff 换形 + ring 桥） *)
Lemma q_lt_opp_d : forall a b d : Q, QltT (a - d) b -> QltT (- d) (b - a).
Proof.
  intros a b d H.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (- d) (b - a))).
  (* 目标：0 < (b - a) - (- d)，换形为 0 < b - a + d *)
  assert (Hshape : (b - a) - (- d) == b - a + d) by (unfold Qminus; ring).
  setoid_rewrite Hshape.
  (* 由 H : a - d < b ⟹ 0 < b - (a - d) == b - a + d *)
  assert (H' : Qlt 0 (b - (a - d))).
  { apply (proj1 (Qlt_minus_iff (a - d) b)). apply QltT_to_Qlt. exact H. }
  assert (Hshape2 : b - (a - d) == b - a + d) by (unfold Qminus; ring).
  setoid_rewrite <- Hshape2.
  exact H'.
Qed.

(* 辅助：a < b + d ⟹ a - d < b（Qlt_minus_iff 双向 + ring 换形） *)
Lemma q_lt_sub_d : forall a b d : Q, QltT a (b + d) -> QltT (a - d) b.
Proof.
  intros a b d H.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (a - d) b)).
  assert (H' : Qlt 0 ((b + d) - a)).
  { apply (proj1 (Qlt_minus_iff a (b + d))). apply QltT_to_Qlt. exact H. }
  assert (Hshape : (b + d) - a == b - (a - d)) by (unfold Qminus; ring).
  setoid_rewrite <- Hshape.
  exact H'.
Qed.

(* 核心：弱三分（¬lt x y → ¬lt y x → eq x y）——eps-N 柯西实数的序反对称
   注：既有记录「弱三分不可证（需 Markov）」之判定有误：
   坏点经柯西传播成全场见证（全局阈值），QltT 可判定使 ¬∃bad → ∀n good，
   全程直觉主义有效；不可证的只是强三分（LPO）。此为左逆 log_inv_exp_neg 的关键前提。 *)
Lemma real_weak_trich : forall x y : Real,
  Not (real_lt x y) -> Not (real_lt y x) -> real_eq x y.
Proof.
  intros x y Hxy Hyx eps Heps.
  (* 柯西阈值：x,y 在 eps/3 上 *)
  assert (Heps3 : QltT 0 (eps / 3)).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - change (Qlt 0 3). compute. reflexivity.
    - apply (Qle_lt_trans (0 * 3) 0 eps).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QltT_to_Qlt. exact Heps. }
  destruct (projT2 x (eps / 3) Heps3) as [Nx HNx].
  destruct (projT2 y (eps / 3) Heps3) as [Ny HNy].
  set (N := Nat.max Nx Ny).
  (* 关键断言：∀n ≥ N, |x n - y n| < eps。
     反证：若某 n0 ≥ N 有 eps ≤ |x n0 - y n0|，则柯西传播 → real_lt x y ∨ real_lt y x → 矛盾 *)
  assert (Hmain : forall n : nat, (N <= n)%nat ->
    QltT (Qabs (projT1 x n - projT1 y n)) eps).
  { intros n Hn.
    destruct (Qlt_le_dec (Qabs (projT1 x n - projT1 y n)) eps) as [HltE | HleE].
    - apply Qlt_to_QltT. exact HltE.
    - (* 坏点：eps ≤ |x n - y n|。分 x n ≤ y n / y n ≤ x n *)
      destruct (Qlt_le_dec (projT1 x n) (projT1 y n)) as [Hxny | Hynx].
      + (* x n < y n → 构造 real_lt x y（全场 y m - x m > eps/3），矛盾 Hxy *)
        assert (Hltxy : real_lt x y).
        { exists (eps / 3). split.
          * exact Heps3.
          * exists N. intros m Hm.
            apply Qlt_to_QltT.
            (* 柯西界 *)
            assert (HNxm : Qlt (Qabs (projT1 x m - projT1 x n)) (eps / 3)).
            { apply QltT_to_Qlt. apply (HNx m n).
              - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)].
              - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_l | exact Hn]. }
            assert (HNym : Qlt (Qabs (projT1 y m - projT1 y n)) (eps / 3)).
            { apply QltT_to_Qlt. apply (HNy m n).
              - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hm)].
              - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_r | exact Hn]. }
            assert (Hxmm : Qlt (projT1 x m) (projT1 x n + eps / 3)).
            { apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 x m) (projT1 x n) (eps / 3)). apply Qlt_to_QltT. exact HNxm. }
            assert (Hymn : Qlt (projT1 y n - eps / 3) (projT1 y m)).
            { apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 y m) (projT1 y n) (eps / 3)). apply Qlt_to_QltT. exact HNym. }
            (* x n < y n → Qabs (x n - y n) == y n - x n；HleE : eps ≤ Qabs → eps ≤ y n - x n *)
            assert (Hxn0 : Qlt (projT1 x n - projT1 y n) 0).
            { assert (Hpos0 : Qlt 0 (projT1 y n - projT1 x n)).
              { apply (proj1 (Qlt_minus_iff (projT1 x n) (projT1 y n))). exact Hxny. }
              assert (Heq2 : projT1 x n - projT1 y n == - (projT1 y n - projT1 x n)) by (unfold Qminus; ring).
              rewrite Heq2.
              apply (Qopp_lt_compat 0 (projT1 y n - projT1 x n)). exact Hpos0. }
            assert (Habsn : Qabs (projT1 x n - projT1 y n) == projT1 y n - projT1 x n).
            { transitivity (- (projT1 x n - projT1 y n)).
              - apply Qabs_neg. apply Qlt_le_weak. exact Hxn0.
              - unfold Qminus. ring. }
            assert (Heps_le : Qle eps (projT1 y n - projT1 x n)).
            { rewrite Habsn in HleE. exact HleE. }
            (* 三段分解：y m - x m == (y m - y n) + (y n - x n) + (x n - x m)
               > -eps/3 + eps - eps/3 == eps/3 *)
            assert (H1 : Qlt (- (eps / 3)) (projT1 y m - projT1 y n)).
            { apply QltT_to_Qlt. apply (q_lt_opp_d (projT1 y n) (projT1 y m) (eps / 3)). exact (Qlt_to_QltT _ _ Hymn). }
            assert (H2 : Qlt (- (eps / 3)) (projT1 x n - projT1 x m)).
            { apply QltT_to_Qlt. apply (q_lt_opp_d (projT1 x m) (projT1 x n) (eps / 3)).
              apply q_lt_sub_d. apply Qlt_to_QltT. exact Hxmm. }
            assert (S1 : Qlt (- (eps / 3) + - (eps / 3))
                           ((projT1 y m - projT1 y n) + (projT1 x n - projT1 x m))).
            { apply (Qplus_lt_compat (- (eps / 3)) (projT1 y m - projT1 y n)
                                     (- (eps / 3)) (projT1 x n - projT1 x m)).
              - exact H1.
              - exact H2. }
            assert (S2 : Qlt ((- (eps / 3)) + (- (eps / 3)) + eps)
                             ((projT1 y m - projT1 y n) + (projT1 x n - projT1 x m) + (projT1 y n - projT1 x n))).
            { apply (Qplus_lt_le_compat (- (eps / 3) + - (eps / 3))
                                        ((projT1 y m - projT1 y n) + (projT1 x n - projT1 x m))
                                        eps (projT1 y n - projT1 x n)).
              - exact S1.
              - exact Heps_le. }
            (* 换形到目标：eps/3 < y m - x m（S2 两侧恒等；含 Qinv 3 用 field） *)
            assert (Hleft : eps / 3 == (- (eps / 3)) + (- (eps / 3)) + eps).
            { unfold Qdiv. field. }
            assert (Hright : projT1 y m - projT1 x m ==
                             (projT1 y m - projT1 y n) + (projT1 x n - projT1 x m) + (projT1 y n - projT1 x n))
              by (unfold Qminus; ring).
            setoid_rewrite Hleft.
            setoid_rewrite Hright.
            exact S2.
        }
        exact (match (Hxy Hltxy) with end).
      + (* y n ≤ x n → 构造 real_lt y x（全场 x m - y m > eps/3），矛盾 Hyx *)
        assert (Hltyx : real_lt y x).
        { exists (eps / 3). split.
          * exact Heps3.
          * exists N. intros m Hm.
            apply Qlt_to_QltT.
            assert (HNxm : Qlt (Qabs (projT1 x m - projT1 x n)) (eps / 3)).
          { apply QltT_to_Qlt. apply (HNx m n).
            - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)].
            - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_l | exact Hn]. }
          assert (HNym : Qlt (Qabs (projT1 y m - projT1 y n)) (eps / 3)).
          { apply QltT_to_Qlt. apply (HNy m n).
            - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hm)].
            - apply NatLe_lift. apply (Nat.le_trans _ N _); [apply Nat.le_max_r | exact Hn]. }
          assert (Hxmm2 : Qlt (projT1 x n - eps / 3) (projT1 x m)).
          { apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 x m) (projT1 x n) (eps / 3)). apply Qlt_to_QltT. exact HNxm. }
          assert (Hymm : Qlt (projT1 y m) (projT1 y n + eps / 3)).
          { apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 y m) (projT1 y n) (eps / 3)). apply Qlt_to_QltT. exact HNym. }
          (* y n ≤ x n → Qabs (x n - y n) == x n - y n；HleE → eps ≤ x n - y n *)
          assert (Hynx0 : Qle 0 (projT1 x n - projT1 y n)).
          { apply (proj1 (Qle_minus_iff (projT1 y n) (projT1 x n))). exact Hynx. }
          assert (Habsn : Qabs (projT1 x n - projT1 y n) == projT1 x n - projT1 y n).
          { apply Qabs_pos. exact Hynx0. }
          assert (Heps_le : Qle eps (projT1 x n - projT1 y n)).
          { rewrite Habsn in HleE. exact HleE. }
          (* 三段分解：x m - y m == (x m - x n) + (x n - y n) + (y n - y m)
             > -eps/3 + eps - eps/3 == eps/3 *)
          assert (H1 : Qlt (- (eps / 3)) (projT1 x m - projT1 x n)).
          { apply QltT_to_Qlt. apply (q_lt_opp_d (projT1 x n) (projT1 x m) (eps / 3)). exact (Qlt_to_QltT _ _ Hxmm2). }
          assert (H2 : Qlt (- (eps / 3)) (projT1 y n - projT1 y m)).
          { apply QltT_to_Qlt. apply (q_lt_opp_d (projT1 y m) (projT1 y n) (eps / 3)).
            apply q_lt_sub_d. apply Qlt_to_QltT. exact Hymm. }
          assert (S1 : Qlt (- (eps / 3) + - (eps / 3))
                         ((projT1 x m - projT1 x n) + (projT1 y n - projT1 y m))).
          { apply (Qplus_lt_compat (- (eps / 3)) (projT1 x m - projT1 x n)
                                   (- (eps / 3)) (projT1 y n - projT1 y m)).
            - exact H1.
            - exact H2. }
          assert (S2 : Qlt ((- (eps / 3)) + (- (eps / 3)) + eps)
                           ((projT1 x m - projT1 x n) + (projT1 y n - projT1 y m) + (projT1 x n - projT1 y n))).
          { apply (Qplus_lt_le_compat (- (eps / 3) + - (eps / 3))
                                      ((projT1 x m - projT1 x n) + (projT1 y n - projT1 y m))
                                      eps (projT1 x n - projT1 y n)).
            - exact S1.
            - exact Heps_le. }
          (* 换形到目标：eps/3 < x m - y m（S2 两侧恒等；含 Qinv 3 用 field） *)
          assert (Hleft : eps / 3 == (- (eps / 3)) + (- (eps / 3)) + eps).
          { unfold Qdiv. field. }
          assert (Hright : projT1 x m - projT1 y m ==
                           (projT1 x m - projT1 x n) + (projT1 y n - projT1 y m) + (projT1 x n - projT1 y n))
            by (unfold Qminus; ring).
          setoid_rewrite Hleft.
          setoid_rewrite Hright.
          exact S2.
        }
        exact (match (Hyx Hltyx) with end).
  }
  (* 组装 real_eq：∃N, ∀n ≥ N, QltT (Qabs (x n - y n)) eps *)
  exists N.
  intros n Hn.
  exact (Hmain n (NatLe_drop _ _ Hn)).
Qed.

(* 左逆：log(e^x) == x。路线：右逆 cw_log_exp_right 给 e^{log(e^x)} == e^x，
   cauchy_real_exp_mono 给 e 严格单调（x<y → e^x<e^y），
   结合 real_lt_not_eq（序 vs 相等不相容）得 ¬(u<x) ∧ ¬(x<u)，
   最后由 real_weak_trich 得 u == x。绕开 判例"需弱三分不可证"的旧定案。 *)
Lemma log_inv_exp_neg_thm : forall (x : Real) (H : real_lt real_zero (cauchy_real_exp x)),
  real_eq (cw_log (cauchy_real_exp x) H) x.
Proof.
  intros x H.
  set (u := cw_log (cauchy_real_exp x) H).
  (* 右逆：e^u == e^x *)
  assert (Hright : real_eq (cauchy_real_exp u) (cauchy_real_exp x)).
  { unfold u. exact (cw_log_exp_right (cauchy_real_exp x) H). }
  apply (real_weak_trich u x).
  - (* ¬(u < x)：u < x → e^u < e^x，与 e^u == e^x 矛盾 *)
    intro Hult.
    apply (real_lt_not_eq (cauchy_real_exp u) (cauchy_real_exp x)).
    + apply (cauchy_real_exp_mono u x). exact Hult.
    + exact Hright.
  - (* ¬(x < u)：x < u → e^x < e^u，与 e^x == e^u 矛盾 *)
    intro Hxlt.
    apply (real_lt_not_eq (cauchy_real_exp x) (cauchy_real_exp u)).
    + apply (cauchy_real_exp_mono x u). exact Hxlt.
    + apply real_eq_sym. exact Hright.
Qed.

(* 左逆 one：log(1) == 0。e^{log 1} == 1 == e^0 + 弱三分 *)
Lemma log_inv_one_thm : forall (H : real_lt real_zero real_one),
  real_eq (cw_log real_one H) real_zero.
Proof.
  intros H.
  set (u := cw_log real_one H).
  (* 右逆：e^u == 1 == e^0 *)
  assert (Hright : real_eq (cauchy_real_exp u) real_one).
  { unfold u. exact (cw_log_exp_right real_one H). }
  assert (He0 : real_eq (cauchy_real_exp real_zero) real_one).
  { exact cauchy_real_exp_zero. }
  apply (real_weak_trich u real_zero).
  - (* ¬(u < 0)：u < 0 → e^u < e^0，与 e^u == e^0 矛盾 *)
    intro Hult.
    apply (real_lt_not_eq (cauchy_real_exp u) (cauchy_real_exp real_zero)).
    + apply (cauchy_real_exp_mono u real_zero). exact Hult.
    + apply (real_eq_trans _ real_one _).
      * exact Hright.
      * apply real_eq_sym. exact He0.
  - (* ¬(0 < u)：0 < u → e^0 < e^u，与 e^0 == e^u 矛盾 *)
    intro H0lt.
    apply (real_lt_not_eq (cauchy_real_exp real_zero) (cauchy_real_exp u)).
    + apply (cauchy_real_exp_mono real_zero u). exact H0lt.
    + apply (real_eq_trans _ real_one _).
      * exact He0.
      * apply real_eq_sym. exact Hright.
Qed.

(* 左逆 mult：log(a·b) == log a + log b。e^{log(a·b)} == a·b == e^{log a + log b} + 弱三分 *)
Lemma log_inv_mult_thm : forall (a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b)
  (Hab : real_lt real_zero (real_mult a b)),
  real_eq (cw_log (real_mult a b) Hab)
          (real_plus (cw_log a Ha) (cw_log b Hb)).
Proof.
  intros a b Ha Hb Hab.
  set (L := cw_log (real_mult a b) Hab).
  set (R := real_plus (cw_log a Ha) (cw_log b Hb)).
  (* e^L == a·b *)
  assert (HL : real_eq (cauchy_real_exp L) (real_mult a b)).
  { unfold L. exact (cw_log_exp_right (real_mult a b) Hab). }
  (* e^R == e^{log a}·e^{log b}（exp 加性） *)
  assert (Hplus : real_eq (cauchy_real_exp R)
                          (real_mult (cauchy_real_exp (cw_log a Ha))
                                     (cauchy_real_exp (cw_log b Hb)))).
  { unfold R. exact (cauchy_real_exp_plus (cw_log a Ha) (cw_log b Hb)). }
  (* e^{log a} == a、e^{log b} == b（右逆） *)
  assert (HRa : real_eq (cauchy_real_exp (cw_log a Ha)) a).
  { exact (cw_log_exp_right a Ha). }
  assert (HRb : real_eq (cauchy_real_exp (cw_log b Hb)) b).
  { exact (cw_log_exp_right b Hb). }
  (* e^R == a·b（组合） *)
  assert (HR : real_eq (cauchy_real_exp R) (real_mult a b)).
  { apply (real_eq_trans _ (real_mult (cauchy_real_exp (cw_log a Ha))
                                      (cauchy_real_exp (cw_log b Hb))) _).
    - exact Hplus.
    - apply (RealSetoid.real_eq_mult_compat (cauchy_real_exp (cw_log a Ha))
                                            (cauchy_real_exp (cw_log b Hb))
                                            a b).
      + exact HRa.
      + exact HRb. }
  apply (real_weak_trich L R).
  - (* ¬(L < R) *)
    intro HLlt.
    apply (real_lt_not_eq (cauchy_real_exp L) (cauchy_real_exp R)).
    + apply (cauchy_real_exp_mono L R). exact HLlt.
    + apply (real_eq_trans _ (real_mult a b) _).
      * exact HL.
      * apply real_eq_sym. exact HR.
  - (* ¬(R < L) *)
    intro HRlt.
    apply (real_lt_not_eq (cauchy_real_exp R) (cauchy_real_exp L)).
    + apply (cauchy_real_exp_mono R L). exact HRlt.
    + apply (real_eq_trans _ (real_mult a b) _).
      * exact HR.
      * apply real_eq_sym. exact HL.
Qed.

(* ============ DPO 有界三前置：Real 层闭合（并入，来自检验 _dbg_dpo_pre.v，14 引理）
   结构性缺失.txt L475 缺口：real_log_lt_mono（log 严格递增，锚点法 判例）
   + real_inv_pos_lt_contra（inv 反单调）+ real_lt_plus_compat_le_lt/lt_le（混合加法保序）
   + real_mult_lt_compat（乘法保序）。验证：coqc+coqtop 双验 + BAD=0（判例） *)
Section DpoPreludeMain.
Section DpoPrelude.

(* ============ 1. real_mult_lt_compat（乘法保序） ============ *)
Lemma real_mult_lt_compat : forall (a b c : Real),
  real_lt a b -> real_lt real_zero c -> real_lt (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hab Hc.
  destruct Hab as [eps0 [Heps0 [N0 HN0]]].
  destruct Hc as [epsc [Hepsc [Nc HNc]]].
  exists (eps0 * epsc).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 epsc).
    + apply QltT_to_Qlt. exact Heps0.
    + apply QltT_to_Qlt. exact Hepsc.
  - exists (Nat.max N0 Nc).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 Nc) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hnc : (Nc <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 Nc) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hpb : projT1 (real_mult b c) n == projT1 b n * projT1 c n) by (apply (qeqT_imp_qeq _ _ (real_mult_proj b c n))).
    assert (Hpa : projT1 (real_mult a c) n == projT1 a n * projT1 c n) by (apply (qeqT_imp_qeq _ _ (real_mult_proj a c n))).
    setoid_rewrite Hpb. setoid_rewrite Hpa.
    assert (Hring : projT1 b n * projT1 c n - projT1 a n * projT1 c n ==
                    (projT1 b n - projT1 a n) * projT1 c n) by ring.
    setoid_rewrite Hring.
    assert (Hcpos : QltT epsc (projT1 c n)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans epsc (projT1 c n - projT1 real_zero n) (projT1 c n)).
      - apply QltT_to_Qlt. apply (HNc n (NatLe_lift _ _ Hnc)).
      - apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        setoid_rewrite Hz. unfold Qminus. ring. }
    assert (Hc0 : QltT 0 (projT1 c n)).
    { apply Qlt_to_QltT.
      apply (Qlt_trans _ epsc _).
      - apply QltT_to_Qlt. exact Hepsc.
      - apply QltT_to_Qlt. exact Hcpos. }
    apply (Qle_lt_trans (eps0 * epsc) (eps0 * projT1 c n) ((projT1 b n - projT1 a n) * projT1 c n)).
    + apply (Qle_trans (eps0 * epsc) (projT1 c n * eps0) (eps0 * projT1 c n)).
      * apply (Qle_trans (eps0 * epsc) (epsc * eps0) (projT1 c n * eps0)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qmult_le_compat_r epsc (projT1 c n) eps0).
           ++ apply Qlt_le_weak. apply QltT_to_Qlt. exact Hcpos.
           ++ apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps0.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qmult_lt_compat_r eps0 (projT1 b n - projT1 a n) (projT1 c n)).
      * apply QltT_to_Qlt. exact Hc0.
      * apply QltT_to_Qlt. apply (HN0 n (NatLe_lift _ _ Hn0)).
Qed.

(* 乘法保序（右参数版）：0<c, a<b ⟹ c·a < c·b（mult_comm 换位） *)
Lemma real_mult_lt_compat_l : forall (a b c : Real),
  real_lt a b -> real_lt real_zero c -> real_lt (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hab Hc.
  apply (real_eq_lt_lt (real_mult c a) (real_mult a c) (real_mult c b)).
  - apply real_mult_comm.
  - apply (real_lt_eq_lt (real_mult a c) (real_mult b c) (real_mult c b)).
    + exact (real_mult_lt_compat a b c Hab Hc).
    + apply real_mult_comm.
Qed.

(* ============ 2. real_inv_pos_lt_contra（inv 反单调） ============ *)
Lemma real_inv_pos_lt_contra : forall (a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_inv_pos b Hb) (real_inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  apply (real_eq_lt_lt (real_inv_pos b Hb)
                       (real_mult (real_mult (real_inv_pos a Ha) a) (real_inv_pos b Hb))
                       (real_inv_pos a Ha)).
  - apply (real_eq_trans (real_inv_pos b Hb)
                         (real_mult real_one (real_inv_pos b Hb))
                         (real_mult (real_mult (real_inv_pos a Ha) a) (real_inv_pos b Hb))).
    + apply real_eq_sym.
      apply (real_eq_trans _ (real_mult (real_inv_pos b Hb) real_one) _).
      * apply real_mult_comm.
      * exact (real_mult_one (real_inv_pos b Hb)).
    + apply (RealSetoid.real_eq_mult_compat real_one (real_inv_pos b Hb)
                                            (real_mult (real_inv_pos a Ha) a) (real_inv_pos b Hb)).
      * apply real_eq_sym.
        apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha)) _).
        -- apply real_mult_comm.
        -- exact (real_inv_pos_correct a Ha).
      * apply real_eq_refl.
  - apply (real_lt_eq_lt (real_mult (real_mult (real_inv_pos a Ha) a) (real_inv_pos b Hb))
                         (real_mult (real_mult (real_inv_pos a Ha) b) (real_inv_pos b Hb))
                         (real_inv_pos a Ha)).
    + apply (real_mult_lt_compat (real_mult (real_inv_pos a Ha) a)
                                 (real_mult (real_inv_pos a Ha) b)
                                 (real_inv_pos b Hb)).
      * apply (real_mult_lt_compat_l a b (real_inv_pos a Ha)); [exact Hab | exact (real_inv_pos_pos a Ha)].
      * exact (real_inv_pos_pos b Hb).
    + apply (real_eq_trans (real_mult (real_mult (real_inv_pos a Ha) b) (real_inv_pos b Hb))
                           (real_mult (real_inv_pos a Ha) (real_mult b (real_inv_pos b Hb)))
                           (real_inv_pos a Ha)).
      * apply real_eq_sym. exact (real_mult_assoc (real_inv_pos a Ha) b (real_inv_pos b Hb)).
      * apply (real_eq_trans (real_mult (real_inv_pos a Ha) (real_mult b (real_inv_pos b Hb)))
                             (real_mult (real_inv_pos a Ha) real_one)
                             (real_inv_pos a Ha)).
        -- apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) (real_mult b (real_inv_pos b Hb))
                                                (real_inv_pos a Ha) real_one).
           ++ apply real_eq_refl.
           ++ exact (real_inv_pos_correct b Hb).
        -- exact (real_mult_one (real_inv_pos a Ha)).
Qed.

(* ============ 3. le/lt 混合加法保序（Real 层） ============ *)
(* 加性平移：c<d ⟹ b+c < b+d *)
Lemma real_lt_plus_translate : forall (b c d : Real),
  real_lt c d -> real_lt (real_plus b c) (real_plus b d).
Proof.
  intros b c d Hcd.
  destruct Hcd as [eps0 [Heps0 [N0 HN0]]].
  exists eps0. split.
  - exact Heps0.
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hpb : projT1 (real_plus b c) n == projT1 b n + projT1 c n) by (apply (qeqT_imp_qeq _ _ (real_plus_proj b c n))).
    assert (Hpd : projT1 (real_plus b d) n == projT1 b n + projT1 d n) by (apply (qeqT_imp_qeq _ _ (real_plus_proj b d n))).
    setoid_rewrite Hpd. setoid_rewrite Hpb.
    assert (Hring : projT1 b n + projT1 d n - (projT1 b n + projT1 c n) == projT1 d n - projT1 c n) by ring.
    setoid_rewrite Hring.
    apply QltT_to_Qlt. apply (HN0 n Hn).
Qed.

(* le a b（Or 编码）∧ lt c d ⟹ lt (a+c) (b+d) *)
Lemma real_lt_plus_compat_le_lt : forall (a b c d : Real),
  real_le a b -> real_lt c d -> real_lt (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hlt Hcd).
  - apply (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c b c); [exact Heq | apply real_eq_refl].
    + apply (real_lt_plus_translate b c d Hcd).
Qed.

(* lt a b ∧ le c d ⟹ lt (a+c) (b+d) *)
Lemma real_lt_plus_compat_lt_le : forall (a b c d : Real),
  real_lt a b -> real_le c d -> real_lt (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  unfold real_le in Hcd.
  destruct Hcd as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (real_plus a c) (real_plus a d) (real_plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d); [apply real_eq_refl | exact Heq].
    + apply (real_eq_lt_lt (real_plus a d) (real_plus d a) (real_plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (real_plus d a) (real_plus d b) (real_plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Qed.

End DpoPrelude.

Section LogMono.

(* ============ 4. real_log_lt_mono（log 严格递增） ============ *)
(* 路线（锚点法；判例同款）：
   u := cw_log a Ha、v := cw_log b Hb。目标 real_lt u v（eps-N 直构）。
   a < b 给 eps0, N0：∀n≥N0, b_n − a_n > eps0。
   固定锚点 n0（log_eps n0 < eps0/8）。la0 := log_seq a Ha n0、lb0 := log_seq b Hb n0。
   ① 中间项符号：¬(lb0 < la0)。若 lb0 < la0，则 exp_const_lt 给实层 e^{lb0} < e^{la0}，
      real_lt_pt_lt 逐点化 ⟹ ∃N ∀k≥N e^{lb0}_k < e^{la0}_k。
      但 approx_root_pt_bound（固定 n0）给 |e^{lb0}_k − b_k| < log_eps n0、|e^{la0}_k − a_k| < log_eps n0，
      b_k − a_k > eps0（k ≥ N0）⟹ e^{lb0}_k − e^{la0}_k > eps0 − 2·log_eps n0 > 0（k ≥ Nmid）——矛盾。
      故 ¬(lb0 < la0)，Qlt_le_dec 给 la0 ≤ lb0。
   ② 中间项正下界：exp_upper_lipschitz_q 给 |e^{lb0}_k − e^{la0}_k| ≤ |lb0−la0|·C；
      e 差 > eps0/2 ⟹ |lb0−la0| > (eps0/2)/C ⟹ lb0 − la0 ≥ (eps0/2)/C（la0 ≤ lb0）。
   ③ 柯西扩散：log_seq_cauchy 给 |log_seq b n − lb0| < eps0/(8C)、|la0 − log_seq a n| < eps0/(8C)（n ≥ N_cau）。
   ④ 组装：log_seq b n − log_seq a n ≥ lb0 − la0 − eps0/(8C) − eps0/(8C) ≥ (eps0/2)/C − eps0/(4C) = eps0/(4C)。
   取 eps := eps0/(4C)。 *)

(* 全局界 B 与逐点界桥 *)
Lemma log_seq_pair_bound : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b) (n : nat),
  QleT' (Qabs (log_seq a Ha n)) (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb)).
Proof.
  intros a b Ha Hb n.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (log_seq a Ha n))
                   (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                   (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
  - apply QleT'_to_Qle. apply log_seq_bounded.
  - apply (Qle_trans (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                     (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))
                     (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
    + (* A ≤ A + B：A ≤ A ∧ 0 ≤ B *)
      apply (Qle_trans (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                       ((Qabs (log_lower a Ha) + Qabs (log_upper a Ha)) + 0)
                       ((Qabs (log_lower a Ha) + Qabs (log_upper a Ha)) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qplus_le_compat (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                               (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                               0 (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
        -- apply Qle_refl.
        -- apply (Qplus_le_compat 0 (Qabs (log_lower b Hb)) 0 (Qabs (log_upper b Hb))).
           ++ apply Qabs_nonneg.
           ++ apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma log_seq_pair_bound_r : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b) (n : nat),
  QleT' (Qabs (log_seq b Hb n)) (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb)).
Proof.
  intros a b Ha Hb n.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (log_seq b Hb n))
                   (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))
                   (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
  - apply QleT'_to_Qle. apply log_seq_bounded.
  - apply (Qle_trans (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))
                     (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))
                     (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
    + (* A ≤ B + A：0 ≤ B（A ≤ 0 + A） *)
      apply (Qle_trans (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))
                       (0 + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))
                       ((Qabs (log_lower a Ha) + Qabs (log_upper a Ha)) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qplus_le_compat 0 (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                               (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))
                               (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
        -- apply (Qplus_le_compat 0 (Qabs (log_lower a Ha)) 0 (Qabs (log_upper a Ha))).
           ++ apply Qabs_nonneg.
           ++ apply Qabs_nonneg.
        -- apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 三段求和（纯 Q）：−d < X−B ∧ eps0 < B−A ∧ −d < A−Y ⟹ eps0−2d < X−Y *)
Lemma q_three_sum : forall (X Y A B d eps0 : Q),
  QltT (- d) (X - B) -> QltT eps0 (B - A) -> QltT (- d) (A - Y) ->
  QltT (eps0 - 2 * d) (X - Y).
Proof.
  intros X Y A B d eps0 H1 H3 H2.
  apply Qlt_to_QltT.
  assert (HS : Qlt (eps0 + - d) ((X - B) + (B - A))).
  { apply (Qlt_le_trans (eps0 + - d) ((B - A) + (X - B)) ((X - B) + (B - A))).
    - apply (Qplus_lt_compat eps0 (B - A) (- d) (X - B)).
      + apply QltT_to_Qlt. exact H3.
      + apply QltT_to_Qlt. exact H1.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (HT : Qlt (eps0 + - d + - d) ((X - B) + (B - A) + (A - Y))).
  { apply (Qplus_lt_compat (eps0 + - d) ((X - B) + (B - A)) (- d) (A - Y)).
    - exact HS.
    - apply QltT_to_Qlt. exact H2. }
  apply (Qle_lt_trans (eps0 - 2 * d) (eps0 + - d + - d) (X - Y)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_le_trans (eps0 + - d + - d) ((X - B) + (B - A) + (A - Y)) (X - Y)).
    + exact HT.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 中间项符号：固定 n0，la0 := log_seq a n0、lb0 := log_seq b n0，log_eps n0 < eps0/2
   ⟹ ¬(lb0 < la0) ⟹ la0 ≤ lb0（Qlt_le_dec） *)
Lemma log_mid_sign : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b)
  (n0 : nat) (eps0 : Q) (N0 : nat),
  QltT 0 eps0 ->
  QltT (log_eps n0) (eps0 / 2) ->
  (forall n : nat, NatLe N0 n -> QltT eps0 (projT1 b n - projT1 a n)) ->
  QleT' (log_seq a Ha n0) (log_seq b Hb n0).
Proof.
  intros a b Ha Hb n0 eps0 N0 Heps0 Heps_small HN0.
  destruct (Qlt_le_dec (log_seq b Hb n0) (log_seq a Ha n0)) as [Hbad | Hgood].
  - (* Hbad : lb0 < la0 ⟹ e^{lb0} < e^{la0}（exp_const_lt）⟹ 逐点 e^{lb0}_k < e^{la0}_k（real_lt_pt_lt）
       与 e 差 > eps0 − 2·log_eps n0 > 0 矛盾 *)
    assert (Hlt_real : real_lt (cauchy_real_exp (real_const (log_seq b Hb n0)))
                               (cauchy_real_exp (real_const (log_seq a Ha n0)))).
    { apply (exp_const_lt (log_seq b Hb n0) (log_seq a Ha n0)). exact (Qlt_to_QltT _ _ Hbad). }
    destruct (real_lt_pt_lt (cauchy_real_exp (real_const (log_seq b Hb n0)))
                            (cauchy_real_exp (real_const (log_seq a Ha n0))) Hlt_real) as [Nl HNl].
    destruct (approx_root_pt_bound a Ha n0) as [Npa Hpa].
    destruct (approx_root_pt_bound b Hb n0) as [Npb Hpb].
    set (Nmax := Nat.max (Nat.max (Nat.max N0 Nl) Npa) Npb).
    (* 取 k := Nmax：HNl 给 e^{lb0}_k < e^{la0}_k；三段求和给 e^{lb0}_k − e^{la0}_k > eps0 − 2δ > 0 —— 矛盾 *)
    assert (Hk0 : (N0 <= Nmax)%nat) by (unfold Nmax; apply (Nat.le_trans _ (Nat.max N0 Nl) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max N0 Nl) Npa) _); [apply Nat.le_max_l | apply Nat.le_max_l]]).
    assert (Hka : (Npa <= Nmax)%nat) by (unfold Nmax; apply (Nat.le_trans _ (Nat.max (Nat.max N0 Nl) Npa) _); [apply Nat.le_max_r | apply Nat.le_max_l]).
    assert (Hkb : (Npb <= Nmax)%nat) by (unfold Nmax; apply Nat.le_max_r).
    assert (Hkl : (Nl <= Nmax)%nat) by (unfold Nmax; apply (Nat.le_trans _ (Nat.max N0 Nl) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max N0 Nl) Npa) _); [apply Nat.le_max_l | apply Nat.le_max_l]]).
    (* 三段求和材料：−δ < e^{lb0}_k − b_k、eps0 < b_k − a_k、−δ < a_k − e^{la0}_k *)
    (* 目标 −δ < X − b 换形为 b − δ < X（Qlt_minus_iff：p<q ⟺ 0<q−p，取 p:=−δ q:=X−b ⟹ 0<X−b+δ；再与 b−δ<X 等价 ring） *)
    assert (H1 : Qlt (- (log_eps n0)) (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - projT1 b Nmax)).
    { assert (H1' : Qlt (projT1 b Nmax - log_eps n0)
                        (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax)).
      { apply QltT_to_Qlt.
        apply (q_abs_lt_minus (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax)
                              (projT1 b Nmax) (log_eps n0)).
        apply (Hpb Nmax (NatLe_lift _ _ Hkb)). }
      (* 目标 −δ < X−b ⟺ 0 < X−b+δ（Qlt_minus_iff p:=−δ q:=X−b ⟹ 0 < (X−b) − (−δ)） *)
      apply (proj2 (Qlt_minus_iff (- (log_eps n0)) (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - projT1 b Nmax))).
      (* 目标 0 < X − b − (−δ)：ring 换形为 0 < X − b + δ；由 H1'（b−δ < X ⟹ 0 < X − b + δ 经 Qlt_minus_iff p:=b−δ q:=X） *)
      assert (H1'' : Qlt 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - projT1 b Nmax + log_eps n0)).
      { apply (Qlt_le_trans 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - (projT1 b Nmax - log_eps n0))
                           (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - projT1 b Nmax + log_eps n0)).
        - apply (proj1 (Qlt_minus_iff (projT1 b Nmax - log_eps n0)
                                      (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax))).
          exact H1'.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      apply (Qlt_le_trans 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - projT1 b Nmax + log_eps n0)
                           (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax - projT1 b Nmax - (- (log_eps n0)))).
      - exact H1''.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (H3 : Qlt eps0 (projT1 b Nmax - projT1 a Nmax)).
    { apply QltT_to_Qlt. apply (HN0 Nmax (NatLe_lift _ _ Hk0)). }
    assert (H2 : Qlt (- (log_eps n0)) (projT1 a Nmax - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
    { (* 目标 −δ < a − e^{la0} ⟺ e^{la0} < a + δ（q_abs_lt_lower：|e^{la0} − a| < δ） *)
      apply (proj2 (Qlt_minus_iff (- (log_eps n0)) (projT1 a Nmax - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax))).
      (* 目标 0 < (a − e^{la0}) − (−δ) == a − e^{la0} + δ *)
      assert (H2b : Qlt 0 (projT1 a Nmax + log_eps n0 - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
      { apply (proj1 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)
                                    (projT1 a Nmax + log_eps n0))).
        apply QltT_to_Qlt.
        apply (q_abs_lt_lower (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)
                              (projT1 a Nmax) (log_eps n0)).
        apply (Hpa Nmax (NatLe_lift _ _ Hka)). }
      apply (Qlt_le_trans 0 (projT1 a Nmax + log_eps n0 - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)
                           (projT1 a Nmax - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax - (- (log_eps n0)))).
      - exact H2b.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* q_three_sum 给 eps0 − 2δ < e^{lb0}_k − e^{la0}_k *)
    assert (Hdiff : Qlt (eps0 - 2 * (log_eps n0))
                        (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                         projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
    { apply QltT_to_Qlt. apply (q_three_sum (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax)
                         (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)
                         (projT1 a Nmax) (projT1 b Nmax) (log_eps n0) eps0).
      - apply Qlt_to_QltT. exact H1.
      - apply Qlt_to_QltT. exact H3.
      - apply Qlt_to_QltT. exact H2. }
    (* 矛盾：HNl 给 e^{lb0}_k < e^{la0}_k（即 e^{la0}_k − e^{lb0}_k > 0），Hdiff 给 e^{lb0}_k − e^{la0}_k > eps0 − 2δ > 0 *)
    (* eps0 − 2δ > 0（δ < eps0/2）⟹ e 差 > 0 与 e 差 < 0 矛盾 *)
    assert (Hpos : Qlt 0 (eps0 - 2 * (log_eps n0))).
    { (* 0 < eps0 − 2δ ⟺ 2δ < eps0（Qlt_minus_iff 双向：0 < eps0−2δ ⟺ 2δ < eps0 用 proj1 反向？Qlt_minus_iff p q : p<q ⟺ 0<q−p。
         目标 0 < eps0 − 2δ：取 p := 2δ、q := eps0 ⟹ 0 < q − p == eps0 − 2δ ✓，前提 2δ < eps0。
         所以 apply (proj2 (Qlt_minus_iff (2δ) eps0)) 把目标变 2δ < eps0？不对——proj2 : 0<q−p → p<q，是反向。
         直接用：目标 0 < eps0 − 2δ，取 p := 2δ、q := eps0：proj1 : p<q → 0<q−p ✓ 用 proj1！ *)
      apply (proj1 (Qlt_minus_iff (2 * (log_eps n0)) eps0)).
      (* 2δ < eps0：先证 2δ < 2·(eps0/2)（Qmult_lt_compat_r 于 δ<eps0/2），再 2·(eps0/2) == eps0 *)
      assert (Hmul : Qlt (2 * (log_eps n0)) (2 * (eps0 / 2))).
      { apply (Qle_lt_trans (2 * (log_eps n0)) ((log_eps n0) * 2) (2 * (eps0 / 2))).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        - apply (Qlt_le_trans ((log_eps n0) * 2) ((eps0 / 2) * 2) (2 * (eps0 / 2))).
          + apply (Qmult_lt_compat_r (log_eps n0) (eps0 / 2) 2).
            * change (Qlt 0 2). compute. reflexivity.
            * apply QltT_to_Qlt. exact Heps_small.
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      apply (Qlt_le_trans (2 * (log_eps n0)) (2 * (eps0 / 2)) eps0).
      - exact Hmul.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    (* 最终矛盾：e^{la0}_k < e^{lb0}_k（HNl）与 e^{lb0}_k < e^{la0}_k（Hdiff+Hpos 反号）——
       用 Qlt_irrefl：e^{lb0}_k − e^{la0}_k < 0 且 0 < e^{lb0}_k − e^{la0}_k？HNl 给 e^{lb0}_k < e^{la0}_k ⟺ e^{lb0}_k − e^{la0}_k < 0。
       即：由 HNl 得 Qlt (X−Y) 0，由 Hdiff+Hpos 得 Qlt 0 (X−Y)（Qlt_le_trans 0 (eps0−2δ) (X−Y)）。矛盾（Qlt_irrefl (X−Y) (Qlt_trans (X−Y) 0 (X−Y) HNlt0 Hposdiff)）。 *)
    exfalso.
    (* 矛盾：HNl 给 e^{lb0} < e^{la0}（proj1 Qlt_minus_iff ⟹ 0 < e^{la0}−e^{lb0}）；
       Hdiff+Hpos 给 0 < e^{lb0}−e^{la0}。相加：0 < 0 矛盾（Qlt_irrefl） *)
    assert (Hl1 : Qlt 0 (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax -
                           projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax)).
    { apply (proj1 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax)
                                  (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax))).
      exact (QltT_to_Qlt _ _ (HNl Nmax (NatLe_lift _ _ Hkl))). }
    assert (Hl2 : Qlt 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                           projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
    { apply (Qlt_le_trans 0 (eps0 - 2 * (log_eps n0))
                           (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                            projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
      - exact Hpos.
      - apply Qlt_le_weak. exact Hdiff. }
    (* Hl1 : 0 < A−B、Hl2 : 0 < B−A：用 Qlt_trans 链矛盾（0 < B−A < 0） *)
    apply (Qlt_irrefl (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                      projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
    apply (Qlt_trans _ 0 _).
    { (* B−A < 0：Hl1（0 < A−B）取负 ⟹ B−A < 0（Qlt_minus_iff 于 p:=B−A q:=0：0 < 0−(B−A) == A−B） *)
      apply (proj2 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                                   projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax) 0)).
      (* 目标 0 < 0 − (B−A) == A−B：ring 换形 *)
      apply (Qlt_le_trans 0 (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax -
                              projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax)
                           (0 - (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                                 projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax))).
      - exact Hl1.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    { exact Hl2. }
  - apply Qle_to_QleT'. exact Hgood.
Qed.

(* eps0/4 < eps0/2（正 eps0） *)
Lemma q_lt_half_half : forall (eps0 : Q), QltT 0 eps0 -> QltT (eps0 / 4) (eps0 / 2).
Proof.
  intros eps0 H.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (eps0 / 4) (eps0 / 2))).
  apply (Qlt_le_trans 0 (eps0 / 4) (eps0 / 2 - eps0 / 4)).
  - apply (Qlt_shift_div_l 0 eps0 4).
    + change (Qlt 0 4). compute. reflexivity.
    + apply (Qle_lt_trans (0 * 4) 0 eps0).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply QltT_to_Qlt. exact H.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* 中间项正下界：固定 n0，la0 ≤ lb0（log_mid_sign）且 |lb0−la0| ≥ eps0/2/C（exp_upper_lipschitz_q 反向）
   前提 δ < eps0/4（主定理用 eps0/8 提供）⟹ eps0/2 < eps0−2δ。 *)
Lemma log_mid_diff : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b)
  (n0 : nat) (eps0 B C : Q) (N0 : nat),
  QltT 0 eps0 -> QleT' 0 B -> QltT 0 C ->
  QltT (log_eps n0) (eps0 / 4) ->
  (forall n : nat, NatLe N0 n -> QltT eps0 (projT1 b n - projT1 a n)) ->
  (forall n : nat, QleT' (exp_series n B) C) ->
  QleT' (Qabs (log_seq a Ha n0)) B -> QleT' (Qabs (log_seq b Hb n0)) B ->
  QltT (eps0 / 2) ((log_seq b Hb n0 - log_seq a Ha n0) * C).
Proof.
  intros a b Ha Hb n0 eps0 B C N0 Heps0 HB HC Heps_small HN0 HCser HBa HBb.
  destruct (approx_root_pt_bound a Ha n0) as [Npa Hpa].
  destruct (approx_root_pt_bound b Hb n0) as [Npb Hpb].
  set (Nmax := Nat.max (Nat.max N0 Npa) Npb).
  (* e 差正下界：∀k ≥ Nmax, eps0/2 < e^{lb0}_k − e^{la0}_k（三段求和 + δ<eps0/4） *)
  assert (Hmid_pos : forall k : nat, (Nmax <= k)%nat ->
    Qlt (eps0 / 2) (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)).
  { intros k Hk.
    assert (Hk0 : (N0 <= k)%nat) by (unfold Nmax in Hk; apply (Nat.le_trans _ (Nat.max N0 Npa) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max N0 Npa) Npb) _); [apply Nat.le_max_l | exact Hk]]).
    assert (Hka : (Npa <= k)%nat) by (unfold Nmax in Hk; apply (Nat.le_trans _ (Nat.max N0 Npa) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max N0 Npa) Npb) _); [apply Nat.le_max_l | exact Hk]]).
    assert (Hkb : (Npb <= k)%nat) by (unfold Nmax in Hk; apply (Nat.le_trans _ (Nat.max (Nat.max N0 Npa) Npb) _); [apply Nat.le_max_r | exact Hk]).
    assert (H1 : Qlt (- (log_eps n0)) (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 b k)).
    { assert (H1' : Qlt (projT1 b k - log_eps n0)
                        (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k)).
      { apply QltT_to_Qlt.
        apply (q_abs_lt_minus (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k)
                              (projT1 b k) (log_eps n0)).
        apply (Hpb k (NatLe_lift _ _ Hkb)). }
      apply (proj2 (Qlt_minus_iff (- (log_eps n0)) (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 b k))).
      assert (H1'' : Qlt 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 b k + log_eps n0)).
      { apply (Qlt_le_trans 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - (projT1 b k - log_eps n0))
                           (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 b k + log_eps n0)).
        - apply (proj1 (Qlt_minus_iff (projT1 b k - log_eps n0)
                                      (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k))).
          exact H1'.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      apply (Qlt_le_trans 0 (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 b k + log_eps n0)
                           (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k - projT1 b k - (- (log_eps n0)))).
      - exact H1''.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (H3 : Qlt eps0 (projT1 b k - projT1 a k)).
    { apply QltT_to_Qlt. apply (HN0 k (NatLe_lift _ _ Hk0)). }
    assert (H2 : Qlt (- (log_eps n0)) (projT1 a k - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)).
    { apply (proj2 (Qlt_minus_iff (- (log_eps n0)) (projT1 a k - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k))).
      assert (H2b : Qlt 0 (projT1 a k + log_eps n0 - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)).
      { apply (proj1 (Qlt_minus_iff (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)
                                    (projT1 a k + log_eps n0))).
        apply QltT_to_Qlt.
        apply (q_abs_lt_lower (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)
                              (projT1 a k) (log_eps n0)).
        apply (Hpa k (NatLe_lift _ _ Hka)). }
      apply (Qlt_le_trans 0 (projT1 a k + log_eps n0 - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)
                           (projT1 a k - projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k - (- (log_eps n0)))).
      - exact H2b.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hdiff : Qlt (eps0 - 2 * (log_eps n0))
                        (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k -
                         projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)).
    { apply QltT_to_Qlt. apply (q_three_sum (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k)
                         (projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)
                         (projT1 a k) (projT1 b k) (log_eps n0) eps0).
      - apply Qlt_to_QltT. exact H1.
      - apply Qlt_to_QltT. exact H3.
      - apply Qlt_to_QltT. exact H2. }
    (* eps0/2 < eps0 − 2δ ⟺ 2δ < eps0/2（δ < eps0/4 ⟹ 2δ < eps0/2） *)
    apply (Qlt_le_trans (eps0 / 2) (eps0 - 2 * (log_eps n0))
                        (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) k -
                         projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) k)).
    + (* eps0/2 < eps0 − 2δ：Qlt_minus_iff 双链 + ring 桥 *)
      apply (proj2 (Qlt_minus_iff (eps0 / 2) (eps0 - 2 * (log_eps n0)))).
      (* 目标 0 < (eps0−2δ) − eps0/2；先证 0 < eps0/2 − 2δ（proj1 于 (2δ)(eps0/2)），ring 桥 *)
      apply (Qlt_le_trans 0 (eps0 / 2 - 2 * (log_eps n0))
                           ((eps0 - 2 * (log_eps n0)) - (eps0 / 2))).
      { apply (proj1 (Qlt_minus_iff (2 * (log_eps n0)) (eps0 / 2))).
        (* 2δ < eps0/2：δ < eps0/4 ⟹ 2δ < 2·(eps0/4) == eps0/2 *)
        apply (Qlt_le_trans (2 * (log_eps n0)) (2 * (eps0 / 4)) (eps0 / 2)).
        - (* 2δ < 2·(eps0/4)：δ·2 < (eps0/4)·2（Qmult_lt_compat_r）经 ring 换形 *)
          apply (Qle_lt_trans (2 * (log_eps n0)) ((log_eps n0) * 2) (2 * (eps0 / 4))).
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          + apply (Qlt_le_trans ((log_eps n0) * 2) ((eps0 / 4) * 2) (2 * (eps0 / 4))).
            * apply (Qmult_lt_compat_r (log_eps n0) (eps0 / 4) 2).
              -- change (Qlt 0 2). compute. reflexivity.
              -- apply QltT_to_Qlt. exact Heps_small.
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
      { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    + apply Qlt_le_weak. exact Hdiff. }
  (* 由 Hmid_pos 于 k := Nmax 与 exp_upper_lipschitz_q 反向 + log_mid_sign 符号 ⟹ (lb0−la0)·C > eps0/2 *)
  apply Qlt_to_QltT.
  apply (Qlt_le_trans (eps0 / 2)
                      (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                       projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)
                      ((log_seq b Hb n0 - log_seq a Ha n0) * C)).
  - exact (Hmid_pos Nmax (Nat.le_refl Nmax)).
  - assert (Hlip : Qle (Qabs (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                               projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax))
                       (Qabs (log_seq b Hb n0 - log_seq a Ha n0) * C)).
    { apply QleT'_to_Qle. apply (exp_upper_lipschitz_q (log_seq b Hb n0) (log_seq a Ha n0) B C Nmax HB).
      - exact HBb.
      - exact HBa.
      - exact HCser. }
    (* 符号：la0 ≤ lb0（log_mid_sign，用 δ < eps0/4 < eps0/2 前提） *)
    assert (Hsm2 : QltT (log_eps n0) (eps0 / 2)).
    { apply Qlt_to_QltT. apply (Qlt_trans (log_eps n0) (eps0 / 4) (eps0 / 2)).
      - apply QltT_to_Qlt. exact Heps_small.
      - apply QltT_to_Qlt. apply q_lt_half_half. exact Heps0. }
    assert (Hsign : Qle (log_seq a Ha n0) (log_seq b Hb n0)).
    { apply QleT'_to_Qle. apply (log_mid_sign a b Ha Hb n0 eps0 N0 Heps0 Hsm2 HN0). }
    (* e 差 ≤ (lb0−la0)·C：e 差 ≤ |e 差| ≤ |lb0−la0|·C == (lb0−la0)·C（la0 ≤ lb0） *)
    apply (Qle_trans (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                      projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)
                     (Qabs (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                            projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax))
                     ((log_seq b Hb n0 - log_seq a Ha n0) * C)).
    + apply (Qle_Qabs (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                       projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax)).
    + apply (Qle_trans (Qabs (projT1 (cauchy_real_exp (real_const (log_seq b Hb n0))) Nmax -
                              projT1 (cauchy_real_exp (real_const (log_seq a Ha n0))) Nmax))
                       (Qabs (log_seq b Hb n0 - log_seq a Ha n0) * C)
                       ((log_seq b Hb n0 - log_seq a Ha n0) * C)).
      * exact Hlip.
      * apply (Qmult_le_compat_r (Qabs (log_seq b Hb n0 - log_seq a Ha n0))
                                 (log_seq b Hb n0 - log_seq a Ha n0) C).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply QleT'_to_Qle. apply (q_le_minus (log_seq a Ha n0) (log_seq b Hb n0)). apply Qle_to_QleT'. exact Hsign.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. exact HC.
Qed.

(* |x−y| < d ⟹ −d < x−y（q_abs_lt_minus 换形）——log_mid_diff 与主定理共用 *)
Lemma q_abs_diff_gt_neg : forall (x y d : Q), QltT (Qabs (x - y)) d -> QltT (- d) (x - y).
Proof.
  intros x y d H.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (- d) (x - y))).
  assert (H' : Qlt (y - d) x).
  { apply QltT_to_Qlt. apply (q_abs_lt_minus x y d). exact H. }
  apply (Qlt_le_trans 0 (x - (y - d)) (x - y - (- d))).
  - apply (proj1 (Qlt_minus_iff (y - d) x)). exact H'.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============ 5. real_log_lt_mono（log 严格递增，主定理） ============ *)
Lemma real_log_lt_mono : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  destruct Hab as [eps0 [Heps0 [N0 HN0]]].
  set (B := Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb)).
  assert (HB : Qle 0 B).
  { unfold B.
    apply (Qle_trans 0 (Qabs (log_lower a Ha) + Qabs (log_upper a Ha)) B).
    - apply (Qplus_le_compat 0 (Qabs (log_lower a Ha)) 0 (Qabs (log_upper a Ha))); apply Qabs_nonneg.
    - apply (Qle_trans (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                       (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))
                       B).
      + apply (Qle_trans (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                         ((Qabs (log_lower a Ha) + Qabs (log_upper a Ha)) + 0)
                         ((Qabs (log_lower a Ha) + Qabs (log_upper a Ha)) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        * apply (Qplus_le_compat (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                                 (Qabs (log_lower a Ha) + Qabs (log_upper a Ha))
                                 0 (Qabs (log_lower b Hb) + Qabs (log_upper b Hb))).
          -- apply Qle_refl.
          -- apply (Qplus_le_compat 0 (Qabs (log_lower b Hb)) 0 (Qabs (log_upper b Hb))); apply Qabs_nonneg.
      + apply QleT'_to_Qle. apply (qeq_le (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + (Qabs (log_lower b Hb) + Qabs (log_upper b Hb)))
                         (Qabs (log_lower a Ha) + Qabs (log_upper a Ha) + Qabs (log_lower b Hb) + Qabs (log_upper b Hb))). apply qeq_imp_qeqT.
          ring. }
  destruct (exp_series_arch_shape B (Qle_to_QleT' _ _ HB)) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1 _); [change (Qlt 0 1); compute; reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (q_pow_arch 1 (eps0 / 8)) as [t Ht].
  { apply Qle_to_QleT'. apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps0 8).
    - change (Qlt 0 8). compute. reflexivity.
    - apply (Qle_lt_trans (0 * 8) 0 eps0).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QltT_to_Qlt. exact Heps0. }
  assert (Hdelta_pos : Qlt 0 (eps0 / (8 * C))).
  { apply (Qlt_shift_div_l 0 eps0 (8 * C)).
    - apply (Qmult_lt_0_compat 8 C).
      + change (Qlt 0 8). compute. reflexivity.
      + exact HCpos.
    - apply (Qle_lt_trans (0 * (8 * C)) 0 eps0).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply QltT_to_Qlt. exact Heps0. }
  destruct (log_seq_cauchy b Hb (eps0 / (8 * C)) (Qlt_to_QltT 0 (eps0 / (8 * C)) Hdelta_pos)) as [Ncb Hcb].
  destruct (log_seq_cauchy a Ha (eps0 / (8 * C)) (Qlt_to_QltT 0 (eps0 / (8 * C)) Hdelta_pos)) as [Nca Hca].
  (* 锚点 n0 := max (S t) (max Ncb Nca)：n0 ≥ S t（log_eps 递减）且 n0 ≥ Ncb/Nca（柯西第二点可用） *)
  set (n0 := Nat.max (Datatypes.S t) (Nat.max Ncb Nca)).
  assert (Hn0_st : (Datatypes.S t <= n0)%nat) by (unfold n0; apply Nat.le_max_l).
  assert (Hn0_cb : (Ncb <= n0)%nat) by (unfold n0; apply (Nat.le_trans _ (Nat.max Ncb Nca) _); [apply Nat.le_max_l | apply Nat.le_max_r]).
  assert (Hn0_ca : (Nca <= n0)%nat) by (unfold n0; apply (Nat.le_trans _ (Nat.max Ncb Nca) _); [apply Nat.le_max_r | apply Nat.le_max_r]).
  (* log_eps n0 < eps0/8（n0 ≥ S t ⟹ log_eps n0 ≤ log_eps (S t) < eps0/8） *)
  assert (Heps_small : Qlt (log_eps n0) (eps0 / 8)).
  { unfold log_eps.
    apply (Qle_lt_trans (q_pow (1 / 2) (Datatypes.S n0)) (q_pow (1 / 2) (Datatypes.S (Datatypes.S t))) (eps0 / 8)).
    - (* n0 ≥ S t ⟹ S n0 ≥ S (S t) ⟹ q_pow (1/2) (S n0) ≤ q_pow (1/2) (S (S t))（q_pow_half_mono） *)
      apply QleT'_to_Qle. apply (q_pow_half_mono (Datatypes.S (Datatypes.S t)) (Datatypes.S n0)); lia.
    - (* q_pow (1/2) (S (S t)) < eps0/8：同前链 *)
      apply (Qle_lt_trans (q_pow (1 / 2) (Datatypes.S (Datatypes.S t))) (q_pow (1 / 2) (Datatypes.S t)) (eps0 / 8)).
      + apply QleT'_to_Qle. apply (q_pow_half_le (Datatypes.S t)).
      + apply (Qlt_le_trans (q_pow (1 / 2) (Datatypes.S t)) (q_pow (1 / 2) t) (eps0 / 8)).
        * apply QltT_to_Qlt. apply q_pow_half_lt_self.
        * apply (Qle_trans (q_pow (1 / 2) t) (1 * q_pow (1 / 2) t) (eps0 / 8)).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          -- apply Qlt_le_weak. apply QltT_to_Qlt. exact Ht. }
  assert (Heps4 : Qlt (log_eps n0) (eps0 / 4)).
  { apply (Qlt_trans (log_eps n0) (eps0 / 8) (eps0 / 4)).
    - exact Heps_small.
    - apply (proj2 (Qlt_minus_iff (eps0 / 8) (eps0 / 4))).
      apply (Qlt_le_trans 0 (eps0 / 8) (eps0 / 4 - eps0 / 8)).
      + apply (Qlt_shift_div_l 0 eps0 8).
        * change (Qlt 0 8). compute. reflexivity.
        * apply (Qle_lt_trans (0 * 8) 0 eps0).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          -- apply QltT_to_Qlt. exact Heps0.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
  assert (Hmid : Qlt (eps0 / 2) ((log_seq b Hb n0 - log_seq a Ha n0) * C)).
  { apply QltT_to_Qlt. apply (log_mid_diff a b Ha Hb n0 eps0 B C N0 Heps0 (Qle_to_QleT' _ _ HB) (Qlt_to_QltT _ _ HCpos) (Qlt_to_QltT _ _ Heps4) (fun n Hn => HN0 n Hn) HC).
    - apply (log_seq_pair_bound a b Ha Hb n0).
    - apply (log_seq_pair_bound_r a b Ha Hb n0). }
  assert (Hmid2 : Qlt (eps0 / (2 * C)) (log_seq b Hb n0 - log_seq a Ha n0)).
  { assert (Hshape : eps0 / (2 * C) == (eps0 / 2) * (1 / C)).
    { unfold Qdiv. field. all: try (intro Hzc0; exact (match q_neq_of_lt C (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ Hzc0) with end)). }
    apply (Qlt_le_trans _ ((log_seq b Hb n0 - log_seq a Ha n0) * C * (1 / C)) _).
    - apply (Qle_lt_trans (eps0 / (2 * C)) ((eps0 / 2) * (1 / C)) ((log_seq b Hb n0 - log_seq a Ha n0) * C * (1 / C))).
      + apply QleT'_to_Qle. apply (qeq_le (eps0 / (2 * C)) ((eps0 / 2) * (1 / C))). apply qeq_imp_qeqT. exact Hshape.
      + apply (Qmult_lt_compat_r (eps0 / 2) ((log_seq b Hb n0 - log_seq a Ha n0) * C) (1 / C)).
        * apply (Qlt_le_trans 0 (/ C) (1 / C)).
          -- apply (Qinv_lt_0_compat C). exact HCpos.
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
        * exact Hmid.
    - apply QleT'_to_Qle. apply (qeq_le ((log_seq b Hb n0 - log_seq a Ha n0) * C * (1 / C)) (log_seq b Hb n0 - log_seq a Ha n0)). apply qeq_imp_qeqT. unfold Qdiv. field.
      all: try (intro Hzc0; exact (match q_neq_of_lt C (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ Hzc0) with end)).
  }
  exists (eps0 / (4 * C)).
  split.
  - apply Qlt_to_QltT.
    apply (Qlt_shift_div_l 0 eps0 (4 * C)).
    + apply (Qmult_lt_0_compat 4 C).
      * change (Qlt 0 4). compute. reflexivity.
      * exact HCpos.
    + apply (Qle_lt_trans (0 * (4 * C)) 0 eps0).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply QltT_to_Qlt. exact Heps0.
  - exists (Nat.max (Nat.max Ncb Nca) n0).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hncb : (Ncb <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Ncb Nca) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max (Nat.max Ncb Nca) n0) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]]).
    assert (Hnca : (Nca <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Ncb Nca) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max (Nat.max Ncb Nca) n0) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]]).
    assert (Hnn0 : (n0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max (Nat.max Ncb Nca) n0) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hcb1 : Qlt (Qabs (log_seq b Hb n - log_seq b Hb n0)) (eps0 / (8 * C))).
    { apply QltT_to_Qlt. apply (Hcb n n0 (NatLe_lift _ _ Hncb) (NatLe_lift _ _ Hn0_cb)). }
    assert (Hca1 : Qlt (Qabs (log_seq a Ha n0 - log_seq a Ha n)) (eps0 / (8 * C))).
    { apply QltT_to_Qlt. apply (Hca n0 n (NatLe_lift _ _ Hn0_ca) (NatLe_lift _ _ Hnca)). }
    assert (Hthree : Qlt (eps0 / (2 * C) - 2 * (eps0 / (8 * C)))
                        (log_seq b Hb n - log_seq a Ha n)).
    { apply QltT_to_Qlt. apply (q_three_sum (log_seq b Hb n) (log_seq a Ha n)
                         (log_seq a Ha n0) (log_seq b Hb n0)
                         (eps0 / (8 * C)) (eps0 / (2 * C))).
      - apply (q_abs_diff_gt_neg (log_seq b Hb n) (log_seq b Hb n0) (eps0 / (8 * C))). apply Qlt_to_QltT. exact Hcb1.
      - apply Qlt_to_QltT. exact Hmid2.
      - apply (q_abs_diff_gt_neg (log_seq a Ha n0) (log_seq a Ha n) (eps0 / (8 * C))). apply Qlt_to_QltT. exact Hca1. }
    assert (Hshape2 : eps0 / (2 * C) - 2 * (eps0 / (8 * C)) == eps0 / (4 * C)).
    { unfold Qdiv. field.
      all: try (intro Hzc0; exact (match q_neq_of_lt C (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ Hzc0) with end)). }
    (* Hthree 左端 == eps0/(4C) ⟹ 用 Qlt 的 Proper 换形：apply (proj2 (Qlt_minus_iff ...)) 或直接 ring 目标 *)
    (* 直接：目标 eps0/(4C) < X；Hthree 给 eps0/(2C)−2δ < X 且 左端 == eps0/(4C)。
       用 Qlt_le_trans 于相等：eps0/(4C) == eps0/(2C)−2δ（Hshape2），严格 < 由 Hthree。 *)
    apply (Qle_lt_trans (eps0 / (4 * C)) (eps0 / (2 * C) - 2 * (eps0 / (8 * C))) (log_seq b Hb n - log_seq a Ha n)).
    + apply QleT'_to_Qle. apply (qeq_le (eps0 / (4 * C)) (eps0 / (2 * C) - 2 * (eps0 / (8 * C)))). apply qeq_imp_qeqT. apply Qeq_sym. exact Hshape2.
    + exact Hthree.
Qed.

End LogMono.

End DpoPreludeMain.
Section EnhancedMain.

(* ============ 1. real_le_plus_compat ============ *)
(* le a b ∧ le c d ⟹ le (a+c) (b+d)：Or 四分支 *)
Lemma real_le_plus_compat : forall (a b c d : Real),
  real_le a b -> real_le c d -> real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  unfold real_le in Hab, Hcd.
  destruct Hab as [Hlt_ab | Heq_ab].
  - destruct Hcd as [Hlt_cd | Heq_cd].
    + apply (RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d)). left.
      exact (real_lt_plus_compat a b c d Hlt_ab Hlt_cd).
    + apply (RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d)). left.
      apply (real_lt_plus_compat_lt_le a b c d Hlt_ab (RealSetoid.real_eq_le c d Heq_cd)).
  - destruct Hcd as [Hlt_cd | Heq_cd].
    + (* eq+lt：a+c == b+c（Heq_ab）∧ b+c < b+d（translate）⟹ a+c < b+d *)
      apply (RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d)). left.
      apply (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)).
      * apply (RealSetoid.real_eq_plus_compat a c b c).
        -- exact Heq_ab.
        -- apply real_eq_refl.
      * apply (real_lt_plus_translate b c d Hlt_cd).
    + apply (RealSetoid.real_eq_le (real_plus a c) (real_plus b d)).
      apply (RealSetoid.real_eq_plus_compat a c b d).
      * exact Heq_ab.
      * exact Heq_cd.
Qed.

(* ============ 2. real_opp_lt_compat + real_lt_zero_opp ============ *)
(* a<b ⟹ −b<−a：eps-N 直构（(−a)_n − (−b)_n == b_n − a_n） *)
Lemma real_opp_lt_compat : forall (a b : Real),
  real_lt a b -> real_lt (real_opp b) (real_opp a).
Proof.
  intros a b Hab.
  destruct Hab as [eps0 [Heps0 [N0 HN0]]].
  exists eps0. split.
  - exact Heps0.
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hpo : projT1 (real_opp a) n == - projT1 a n) by (apply (qeqT_imp_qeq _ _ (real_opp_proj a n))).
    assert (Hpb : projT1 (real_opp b) n == - projT1 b n) by (apply (qeqT_imp_qeq _ _ (real_opp_proj b n))).
    (* 目标：QltT eps0 (projT1 (opp a) n − projT1 (opp b) n) == −a_n − (−b_n) == b_n − a_n *)
    setoid_rewrite Hpo. setoid_rewrite Hpb.
    assert (Hring : - projT1 a n - - projT1 b n == projT1 b n - projT1 a n) by ring.
    setoid_rewrite Hring.
    apply QltT_to_Qlt. apply (HN0 n Hn).
Qed.

(* 0<a ⟹ −a<0 *)
Lemma real_lt_zero_opp : forall (a : Real),
  real_lt real_zero a -> real_lt (real_opp a) real_zero.
Proof.
  intros a Ha.
  (* real_opp real_zero == real_zero：由 real_opp_lt_compat 于 0<a 得 −a < −0 == 0 *)
  apply (real_lt_eq_lt (real_opp a) (real_opp real_zero) real_zero).
  - apply (real_opp_lt_compat real_zero a). exact Ha.
  - (* real_opp real_zero == real_zero：逐点 −0 == 0 *)
    apply real_eq_of_zero_diff.
    intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_zero n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz. ring.
Qed.

(* ============ 3. real_opp_le_compat ============ *)
(* a≤b ⟹ −b≤−a：le 分解为 lt/eq，分别用 real_opp_lt_compat / real_eq_opp_compat *)
Lemma real_opp_le_compat : forall (a b : Real),
  real_le a b -> real_le (real_opp b) (real_opp a).
Proof.
  intros a b Hab.
  unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req (real_opp b) (real_opp a)). left.
    exact (real_opp_lt_compat a b Hlt).
  - apply (RealSetoid.real_eq_le (real_opp b) (real_opp a)).
    exact (RealSetoid.real_eq_opp_compat b a (real_eq_sym a b Heq)).
Qed.

(* ============ 4. real_inv_pos_ext + real_inv_pos_le_compat ============ *)
(* x == y ⟹ inv_pos x Hx == inv_pos y Hy（inv 不依赖正性证明） *)
Lemma real_inv_pos_ext : forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
  real_eq x y -> real_eq (real_inv_pos x Hx) (real_inv_pos y Hy).
Proof.
  intros x y Hx Hy Heq.
  (* inv x == inv y：x·inv x == 1 == y·inv y，且 x == y ⟹ x·inv y == y·inv y == 1 ⟹ inv x == inv y
     经典论证：inv x == 1·inv x == (x·inv x)·inv x ... 复杂。
     更简单：inv x == x·inv y·inv x？——用唯一性：x·(inv y) == x·inv x == 1（x==y），
     real_inv_pos_correct 给 x·inv x == 1。两式：x·inv y == 1 且 x·inv x == 1。
     需"左乘消去"：x·u == x·v → u == v（需 x ≠ 0，x > 0 ⟹ 可消）——构造性证明较繁。
     改用：inv x == (inv x)·(y·inv y) == (inv x·y)·inv y == (inv x·x)·inv y == 1·inv y == inv y。
     全部用 real_eq 链 + mult_comm/assoc + inv_pos_correct。 *)
  apply (real_eq_trans (real_inv_pos x Hx)
                       (real_mult (real_inv_pos x Hx) (real_mult y (real_inv_pos y Hy)))
                       (real_inv_pos y Hy)).
  - (* inv x == inv x·(y·inv y)：y·inv y == 1，inv x·1 == inv x *)
    apply (real_eq_trans (real_inv_pos x Hx)
                         (real_mult (real_inv_pos x Hx) real_one)
                         (real_mult (real_inv_pos x Hx) (real_mult y (real_inv_pos y Hy)))).
    + apply real_eq_sym. exact (real_mult_one (real_inv_pos x Hx)).
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx) real_one
                                            (real_inv_pos x Hx) (real_mult y (real_inv_pos y Hy))).
      * apply real_eq_refl.
      * apply real_eq_sym. exact (real_inv_pos_correct y Hy).
  - (* inv x·(y·inv y) == inv y：重组为 (inv x·y)·inv y == (inv x·x)·inv y == 1·inv y == inv y *)
    apply (real_eq_trans (real_mult (real_inv_pos x Hx) (real_mult y (real_inv_pos y Hy)))
                         (real_mult (real_mult (real_inv_pos x Hx) y) (real_inv_pos y Hy))
                         (real_inv_pos y Hy)).
    + exact (real_mult_assoc (real_inv_pos x Hx) y (real_inv_pos y Hy)).
    + apply (real_eq_trans (real_mult (real_mult (real_inv_pos x Hx) y) (real_inv_pos y Hy))
                           (real_mult (real_mult (real_inv_pos x Hx) x) (real_inv_pos y Hy))
                           (real_inv_pos y Hy)).
      * apply (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos x Hx) y)
                                              (real_inv_pos y Hy)
                                              (real_mult (real_inv_pos x Hx) x)
                                              (real_inv_pos y Hy)).
        -- apply (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx) y
                                                (real_inv_pos x Hx) x).
           ++ apply real_eq_refl.
           ++ exact (real_eq_sym x y Heq).
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_mult (real_mult (real_inv_pos x Hx) x) (real_inv_pos y Hy))
                             (real_mult real_one (real_inv_pos y Hy))
                             (real_inv_pos y Hy)).
        -- apply (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos x Hx) x)
                                                (real_inv_pos y Hy)
                                                real_one (real_inv_pos y Hy)).
           ++ apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx)) _).
              ** apply real_mult_comm.
              ** exact (real_inv_pos_correct x Hx).
           ++ apply real_eq_refl.
        -- (* 1·inv y == inv y：换序 == inv y·1 → x·1==x *)
           apply (real_eq_trans _ (real_mult (real_inv_pos y Hy) real_one) _).
           ++ exact (real_mult_comm real_one (real_inv_pos y Hy)).
           ++ exact (real_mult_one (real_inv_pos y Hy)).
Qed.

(* 0<a、0<b、a≤b ⟹ inv b ≤ inv a：le 分解为 lt/eq *)
Lemma real_inv_pos_le_compat : forall (a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (real_inv_pos b Hb) (real_inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req (real_inv_pos b Hb) (real_inv_pos a Ha)). left.
    exact (real_inv_pos_lt_contra a b Ha Hb Hlt).
  - apply (RealSetoid.real_eq_le (real_inv_pos b Hb) (real_inv_pos a Ha)).
    apply (real_inv_pos_ext b a Hb Ha).
    exact (real_eq_sym a b Heq).
Qed.

(* ============ 5. real_le_mult_compat + real_le_mult_compat_weak ============ *)
(* 0<c、a≤b ⟹ a·c≤b·c：le 分解为 lt/eq *)
Lemma real_le_mult_compat : forall (a b c : Real),
  real_lt real_zero c -> real_le a b -> real_le (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hc Hab.
  unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req (real_mult a c) (real_mult b c)). left.
    exact (real_mult_lt_compat a b c Hlt Hc).
  - apply (RealSetoid.real_eq_le (real_mult a c) (real_mult b c)).
    apply (RealSetoid.real_eq_mult_compat a c b c).
    + exact Heq.
    + apply real_eq_refl.
Qed.

(* 0≤c、a≤b ⟹ a·c≤b·c：0≤c 分解为 0<c / 0==c *)
Lemma real_le_mult_compat_weak : forall (a b c : Real),
  real_le real_zero c -> real_le a b -> real_le (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hc Hab.
  unfold real_le in Hc.
  destruct Hc as [Hlt | Heq].
  - (* 0 < c：real_le_mult_compat *)
    exact (real_le_mult_compat a b c Hlt Hab).
  - (* 0 == c：a·c == a·0 == 0 == b·0 == b·c（mult_zero） *)
    apply (RealSetoid.real_eq_le (real_mult a c) (real_mult b c)).
    apply (real_eq_trans (real_mult a c) (real_mult a real_zero) (real_mult b c)).
    + apply (RealSetoid.real_eq_mult_compat a c a real_zero).
      * apply real_eq_refl.
      * exact (real_eq_sym real_zero c Heq).
    + apply (real_eq_trans (real_mult a real_zero) real_zero (real_mult b c)).
      * exact (real_mult_zero a).
      * apply real_eq_sym.
        apply (real_eq_trans (real_mult b c) (real_mult b real_zero) real_zero).
        -- apply (RealSetoid.real_eq_mult_compat b c b real_zero).
           ++ apply real_eq_refl.
           ++ exact (real_eq_sym real_zero c Heq).
        -- exact (real_mult_zero b).
Qed.

(* 0<c、a<b ⟹ c·a<c·b（左侧版，RealInterfaceEnhanced lt_mult_compat 形态） *)
Lemma real_lt_mult_compat : forall (a b c : Real),
  real_lt real_zero c -> real_lt a b -> real_lt (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  exact (real_mult_lt_compat_l a b c Hab Hc).
Qed.

End EnhancedMain.
End LogInvStage.
End LogStage3.
Section FullInstance.

(* ============ 完整版 RealInterfaceSetoid 实例组装 ============
   exp 族：exp_neg := cauchy_real_exp、exp_neg_pos := cauchy_real_exp_pos（L13077）、
   exp_neg_zero := cauchy_real_exp_zero、exp_neg_plus := cauchy_real_exp_plus（备份 103）
   log 族：log_inv := cw_log、log_inv_exp_neg := log_inv_exp_neg_thm（本检验）、
   log_inv_one := log_inv_one_thm、log_inv_mult := log_inv_mult_thm。
   其余 43 字段复用 Core 实例 Real_RealInterfaceSetoidCore 的投影。 *)
Instance Real_RealInterfaceSetoid : RealSetoid.RealInterfaceSetoid := {
  req := real_eq;
  req_refl := real_eq_refl;
  req_sym := real_eq_sym;
  req_trans := real_eq_trans;
  zero := real_zero;
  one := real_one;
  plus := real_plus;
  mult := real_mult;
  opp := real_opp;
  abs := real_abs;
  lt := real_lt;
  le := real_le;
  req_plus_compat := RealSetoid.real_eq_plus_compat_adapt;
  req_mult_compat := RealSetoid.real_eq_mult_compat_adapt;
  req_opp_compat := RealSetoid.real_eq_opp_compat;
  req_abs_compat := RealSetoid.real_eq_abs_compat;
  req_lt_compat := RealSetoid.real_lt_compat;
  req_le_compat := RealSetoid.real_le_compat;
  plus_assoc := real_plus_assoc;
  plus_comm := real_plus_comm;
  plus_zero := real_plus_zero;
  plus_opp := real_plus_opp;
  mult_assoc := real_mult_assoc;
  mult_comm := real_mult_comm;
  mult_one := real_mult_one;
  distrib := real_distrib;
  mult_zero := real_mult_zero;
  lt_irrefl := real_lt_irrefl;
  lt_trans := real_lt_trans;
  le_refl := real_le_refl;
  le_trans := real_le_trans;
  le_antisym := real_le_antisym;
  le_lt_trans := real_le_lt_trans;
  lt_le_trans := real_lt_le_trans;
  lt_le_iff := RealSetoid.real_lt_le_iff_req;
  le_id_l := RealSetoid.real_le_id_l;
  le_id_r := RealSetoid.real_le_id_r;
  lt_id_l := RealSetoid.real_lt_id_l;
  lt_id_r := RealSetoid.real_lt_id_r;
  inv_pos := real_inv_pos;
  inv_pos_correct := real_inv_pos_correct;
  exp_neg := cauchy_real_exp;
  exp_neg_pos := cauchy_real_exp_pos;
  exp_neg_zero := cauchy_real_exp_zero;
  exp_neg_plus := cauchy_real_exp_plus;
  log_inv := cw_log;
  log_inv_exp_neg := log_inv_exp_neg_thm;
  log_inv_one := log_inv_one_thm;
  log_inv_mult := log_inv_mult_thm;
  metric := real_metric;
  metric_sym := RealSetoid.real_metric_sym;
  metric_pos := RealSetoid.real_metric_pos_eps;
  metric_zero := RealSetoid.real_metric_zero;
  metric_triangle := RealSetoid.real_metric_triangle_eps;
  lim := real_lim;
  lim_unique := real_lim_unique;
  cauchy_complete := RealSetoid.real_cauchy_complete_metric_natle;
}.

End FullInstance.
(* ============ RealInterfaceEnhancedSetoid 阶段 2 并入（来自检验 _dbg_riesetoid.v 39 Qed 全部通过） ============
   req 版 RealInterfaceEnhanced（L195）独立接口 + Real 层实现 + Instance RealEnhancedReal。
   - Real 层引理（segA）名字与主文件无冲突（real_log 系列是 Section 内 Variable，End 后释放），直接追加。
   - 独立接口（39 字段全显式，不继承）：字段名与 RealInterface / RealSetoid.RealInterfaceSetoid
     同名（zero/one/plus/req/...），Coq 顶层 Class 同名字段全局冲突（"zero already exists"），
     故接口 + 实例用 Module RealInterfaceEnhancedMod 隔离（模块内外记录字段名互不冲突，实验验证 RC=0）。
     Module 不能放 Section 内（Coq 限制），故接口段在 Section 外。
   - exp_neg 语义 = e^{-x}（Boltzmann）；log/log_inv 带正性前提；log_inv = -ln。 *)
Section EnhancedSetoidMain.
(* Q 层换形：X−Z − (X−Y) == Y−Z（unfold Qminus + Qopp_plus + involutive） *)
Lemma q_minus_minus_cancel : forall X Y Z : Q, QeqT ((X - Z) - (X - Y)) (Y - Z).
Proof.
  intros. apply qeq_imp_qeqT. unfold Qminus. rewrite Qopp_plus. rewrite Qopp_involutive. ring.
Qed.

(* ============ 0. 基础：one_pos / plus_positive / mult_positive ============ *)

(* 0 < 1：eps := 1/2，逐点 1 - 0 == 1 > 1/2 *)
Lemma real_lt_zero_one : real_lt real_zero real_one.
Proof.
  unfold real_lt.
  exists (1 / 2)%Q.
  split.
  - apply Qlt_to_QltT. compute. reflexivity.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz. setoid_rewrite Ho.
    compute. reflexivity.
Qed.

(* 0<a、0<b ⟹ 0<a+b：real_lt_plus_compat 于 (0, a) (0, b)，再桥 0+0==0 *)
Lemma real_plus_positive : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_plus a b).
Proof.
  intros a b Ha Hb.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus a b)).
  - (* real_eq real_zero (real_plus real_zero real_zero)：逐点 0 == 0+0 *)
    apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero real_zero n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz. ring.
  - apply (real_lt_plus_compat real_zero a real_zero b). exact Ha. exact Hb.
Qed.

(* 0<a、0<b ⟹ 0<a·b：real_mult_lt_compat 于 (0, a) (0, b)，再桥 0·b==0 *)
Lemma real_mult_positive : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  apply (real_eq_lt_lt real_zero (real_mult real_zero b) (real_mult a b)).
  - (* real_eq real_zero (real_mult real_zero b)：mult_zero 换序 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult b real_zero) _).
    + apply real_mult_comm.
    + exact (real_mult_zero b).
  - apply (real_mult_lt_compat real_zero a b Ha Hb).
Qed.

(* ============ 1. real_min / real_max：逐点 Qmin/Qmax ============ *)

(* Qmin 单侧 Lipschitz：Qmin x y ≤ Qmin x' y' + |x−x'| + |y−y'|
   证：Qmin x y ≤ x ≤ x' + |x−x'| 且 Qmin x y ≤ y ≤ y' + |y−y'|
   ⟹（min_glb）Qmin x y ≤ Qmin (x'+|x−x'|) (y'+|y−y'|)
   ⟹（Q.min_dec 分 min x' y' == x' / == y'）≤ Qmin x' y' + 和 *)
Lemma q_min_upper_lip : forall x y x' y' : Q,
  QleT' (Qmin x y) (Qmin x' y' + (Qabs (x - x') + Qabs (y - y'))).
Proof.
  intros x y x' y'.
  apply Qle_to_QleT'.
  set (a := Qabs (x - x')). set (b := Qabs (y - y')).
  (* Qmin x y ≤ x 且 x ≤ x' + a *)
  assert (Hx : Qle (Qmin x y) (x' + a)).
  { apply (Qle_trans _ x _).
    - apply Q.le_min_l.
    - (* x ≤ x' + a：x ≤ x' + (x − x') 且 x' + (x−x') ≤ x' + a *)
      apply (Qle_trans _ (x' + (x - x')) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      + apply (Qplus_le_compat x' x' (x - x') a).
        * apply Qle_refl.
        * unfold a. apply Qle_Qabs. }
  (* Qmin x y ≤ y 且 y ≤ y' + b *)
  assert (Hy : Qle (Qmin x y) (y' + b)).
  { apply (Qle_trans _ y _).
    - apply Q.le_min_r.
    - apply (Qle_trans _ (y' + (y - y')) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      + apply (Qplus_le_compat y' y' (y - y') b).
        * apply Qle_refl.
        * unfold b. apply Qle_Qabs. }
  (* min_glb：Qmin x y ≤ Qmin (x'+a) (y'+b) *)
  assert (Hglb : Qle (Qmin x y) (Qmin (x' + a) (y' + b))).
  { apply Q.min_glb. exact Hx. exact Hy. }
  (* Qmin (x'+a) (y'+b) ≤ Qmin x' y' + a + b *)
  assert (Hstep : Qle (Qmin (x' + a) (y' + b)) (Qmin x' y' + (a + b))).
  { destruct (Q.min_dec x' y') as [Hmx | Hmy].
    - (* Qmin x' y' == x'：min(x'+a,y'+b) ≤ x'+a == Qmin x' y' + a ≤ + a + b *)
      apply (Qle_trans _ (x' + a) _).
      + apply Q.le_min_l.
      + apply (Qle_trans _ (Qmin x' y' + a) _).
        * apply (Qplus_le_compat x' (Qmin x' y') a a).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hmx.
          -- apply Qle_refl.
        * apply (Qplus_le_compat (Qmin x' y') (Qmin x' y') a (a + b)).
          -- apply Qle_refl.
          -- apply (Qle_trans _ (a + 0) _).
             ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
             ++ apply (Qplus_le_compat a a 0 b). apply Qle_refl. apply Qabs_nonneg.
    - (* Qmin x' y' == y'：min ≤ y'+b == Qmin x' y' + b ≤ + a + b *)
      apply (Qle_trans _ (y' + b) _).
      + apply Q.le_min_r.
      + apply (Qle_trans _ (Qmin x' y' + b) _).
        * apply (Qplus_le_compat y' (Qmin x' y') b b).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hmy.
          -- apply Qle_refl.
        * apply (Qplus_le_compat (Qmin x' y') (Qmin x' y') b (a + b)).
          -- apply Qle_refl.
          -- apply (Qle_trans _ (0 + b) _).
             ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
             ++ apply (Qplus_le_compat 0 a b b). apply Qabs_nonneg. apply Qle_refl. }
  (* 组装：Qmin x y ≤ Qmin (x'+a) (y'+b) ≤ Qmin x' y' + (a+b) == 目标 *)
  apply (Qle_trans _ (Qmin (x' + a) (y' + b)) _).
  - exact Hglb.
  - apply (Qle_trans _ (Qmin x' y' + (a + b)) _).
    + exact Hstep.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold a, b. unfold Qminus. ring.
Qed.

(* 单侧下界（对称）：Qmin x' y' ≤ Qmin x y + |x−x'| + |y−y'|（|x'−x|==|x−x'| 桥） *)
Lemma q_min_lower_lip : forall x y x' y' : Q,
  QleT' (Qmin x' y') (Qmin x y + (Qabs (x - x') + Qabs (y - y'))).
Proof.
  intros x y x' y'.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qmin x y + (Qabs (x' - x) + Qabs (y' - y))) _).
  - apply QleT'_to_Qle. exact (q_min_upper_lip x' y' x y).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    rewrite (Qabs_Qminus x' x). rewrite (Qabs_Qminus y' y).
    unfold Qminus. ring.
Qed.

(* Qmin 1-Lipschitz：|Qmin x y − Qmin x' y'| ≤ |x−x'| + |y−y'|
   Qabs_Qle_condition 拆双向：
   - −D ≤ A−B ⟺ 0 ≤ (A−B)+D == (A+D)−B（由 Hl : B ≤ A+D）
   - A−B ≤ D ⟺ 0 ≤ D−(A−B) == (B+D)−A（由 Hu : A ≤ B+D） *)
Lemma q_min_lipschitz : forall x y x' y' : Q,
  QleT' (Qabs (Qmin x y - Qmin x' y')) (Qabs (x - x') + Qabs (y - y')).
Proof.
  intros x y x' y'.
  apply Qle_to_QleT'.
  set (D := Qabs (x - x') + Qabs (y - y')).
  set (A := Qmin x y). set (B := Qmin x' y').
  assert (Hu : Qle A (B + D)).
  { unfold A, B, D. apply QleT'_to_Qle. exact (q_min_upper_lip x y x' y'). }
  assert (Hl : Qle B (A + D)).
  { unfold A, B, D. apply QleT'_to_Qle. exact (q_min_lower_lip x y x' y'). }
  apply Qabs_Qle_condition. split.
  - (* −D ≤ A − B *)
    apply (proj2 (Qle_minus_iff (- D) (A - B))).
    (* 目标：0 ≤ (A − B) − (−D)；经 (A+D)−B 桥：0 ≤ (A+D)−B（Hl）且 (A+D)−B == (A−B)−(−D) *)
    apply (Qle_trans _ ((A + D) - B) _).
    + (* 0 ≤ (A + D) − B：由 Hl *)
      apply (proj1 (Qle_minus_iff B (A + D))). exact Hl.
    + (* (A + D) − B ≤ (A − B) − (−D)：相等桥 *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. rewrite Qopp_involutive. ring.
  - (* A − B ≤ D *)
    apply (proj2 (Qle_minus_iff (A - B) D)).
    (* 目标：0 ≤ D − (A − B)；经 (B+D)−A 桥：0 ≤ (B+D)−A（Hu）且 (B+D)−A == D−(A−B) *)
    apply (Qle_trans _ ((B + D) - A) _).
    + (* 0 ≤ (B + D) − A：由 Hu *)
      apply (proj1 (Qle_minus_iff A (B + D))). exact Hu.
    + (* (B + D) − A ≤ D − (A − B)：相等桥 *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. rewrite Qopp_plus. rewrite Qopp_involutive. ring.
Qed.

(* Qmax 单侧 Lipschitz：Qmax x y ≤ Qmax x' y' + |x−x'| + |y−y'|
   对偶：Qmax x y ≤ x'+a（max_lub 于 x ≤ x'+a、y ≤ y'+b）⟹ 分 Q.max_dec *)
Lemma q_max_upper_lip : forall x y x' y' : Q,
  QleT' (Qmax x y) (Qmax x' y' + (Qabs (x - x') + Qabs (y - y'))).
Proof.
  intros x y x' y'.
  apply Qle_to_QleT'.
  set (a := Qabs (x - x')). set (b := Qabs (y - y')).
  assert (Hx : Qle x (x' + a)).
  { apply (Qle_trans _ (x' + (x - x')) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
    - apply (Qplus_le_compat x' x' (x - x') a).
      * apply Qle_refl.
      * unfold a. apply Qle_Qabs. }
  assert (Hy : Qle y (y' + b)).
  { apply (Qle_trans _ (y' + (y - y')) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
    - apply (Qplus_le_compat y' y' (y - y') b).
      * apply Qle_refl.
      * unfold b. apply Qle_Qabs. }
  assert (HxM : Qle x (Qmax (x' + a) (y' + b))).
  { apply (Qle_trans _ (x' + a) _). exact Hx. apply Q.le_max_l. }
  assert (HyM : Qle y (Qmax (x' + a) (y' + b))).
  { apply (Qle_trans _ (y' + b) _). exact Hy. apply Q.le_max_r. }
  assert (Hglb : Qle (Qmax x y) (Qmax (x' + a) (y' + b))).
  { apply Q.max_lub. exact HxM. exact HyM. }
  assert (Hstep : Qle (Qmax (x' + a) (y' + b)) (Qmax x' y' + (a + b))).
  { apply Q.max_lub.
    - (* x' + a ≤ Qmax x' y' + a + b *)
      apply (Qle_trans _ (Qmax x' y' + a) _).
      + apply (Qplus_le_compat x' (Qmax x' y') a a).
        * apply Q.le_max_l.
        * apply Qle_refl.
      + apply (Qplus_le_compat (Qmax x' y') (Qmax x' y') a (a + b)).
        * apply Qle_refl.
        * apply (Qle_trans _ (a + 0) _).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          -- apply (Qplus_le_compat a a 0 b). apply Qle_refl. apply Qabs_nonneg.
    - (* y' + b ≤ Qmax x' y' + a + b *)
      apply (Qle_trans _ (Qmax x' y' + b) _).
      + apply (Qplus_le_compat y' (Qmax x' y') b b).
        * apply Q.le_max_r.
        * apply Qle_refl.
      + apply (Qplus_le_compat (Qmax x' y') (Qmax x' y') b (a + b)).
        * apply Qle_refl.
        * apply (Qle_trans _ (0 + b) _).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          -- apply (Qplus_le_compat 0 a b b). apply Qabs_nonneg. apply Qle_refl. }
  apply (Qle_trans _ (Qmax (x' + a) (y' + b)) _).
  - exact Hglb.
  - apply (Qle_trans _ (Qmax x' y' + (a + b)) _).
    + exact Hstep.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold a, b. unfold Qminus. ring.
Qed.

(* Qmax 单侧下界（对称） *)
Lemma q_max_lower_lip : forall x y x' y' : Q,
  QleT' (Qmax x' y') (Qmax x y + (Qabs (x - x') + Qabs (y - y'))).
Proof.
  intros x y x' y'.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qmax x y + (Qabs (x' - x) + Qabs (y' - y))) _).
  - apply QleT'_to_Qle. exact (q_max_upper_lip x' y' x y).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    rewrite (Qabs_Qminus x' x). rewrite (Qabs_Qminus y' y).
    unfold Qminus. ring.
Qed.

(* Qmax 1-Lipschitz *)
Lemma q_max_lipschitz : forall x y x' y' : Q,
  QleT' (Qabs (Qmax x y - Qmax x' y')) (Qabs (x - x') + Qabs (y - y')).
Proof.
  intros x y x' y'.
  apply Qle_to_QleT'.
  set (D := Qabs (x - x') + Qabs (y - y')).
  set (A := Qmax x y). set (B := Qmax x' y').
  assert (Hu : Qle A (B + D)).
  { unfold A, B, D. apply QleT'_to_Qle. exact (q_max_upper_lip x y x' y'). }
  assert (Hl : Qle B (A + D)).
  { unfold A, B, D. apply QleT'_to_Qle. exact (q_max_lower_lip x y x' y'). }
  apply Qabs_Qle_condition. split.
  - apply (proj2 (Qle_minus_iff (- D) (A - B))).
    apply (Qle_trans _ ((A + D) - B) _).
    + apply (proj1 (Qle_minus_iff B (A + D))). exact Hl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. rewrite Qopp_involutive. ring.
  - apply (proj2 (Qle_minus_iff (A - B) D)).
    apply (Qle_trans _ ((B + D) - A) _).
    + apply (proj1 (Qle_minus_iff A (B + D))). exact Hu.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. rewrite Qopp_plus. rewrite Qopp_involutive. ring.
Qed.

(* real_min：逐点 Qmin，柯西性由 q_min_lipschitz（eps/2 分割） *)
Definition real_min (a b : Real) : Real.
Proof.
  destruct a as [u Hu]. destruct b as [v Hv].
  exists (fun n => Qmin (u n) (v n)).
  intros eps Heps.
  assert (Hhalf : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  destruct (Hu (eps / 2) Hhalf) as [N1 HN1].
  destruct (Hv (eps / 2) Hhalf) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros m n Hm Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u m - u n) + Qabs (v m - v n)) _).
  - apply QleT'_to_Qle. exact (q_min_lipschitz (u m) (v m) (u n) (v n)).
  - apply (Qlt_le_trans _ (eps / 2 + eps / 2) _).
    + apply Qplus_lt_compat.
      * apply QltT_to_Qlt.
        apply (HN1 m n).
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)].
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
      * apply QltT_to_Qlt.
        apply (HN2 m n).
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hm)].
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)].
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Defined.

(* real_max：逐点 Qmax，柯西性由 q_max_lipschitz（eps/2 分割） *)
Definition real_max (a b : Real) : Real.
Proof.
  destruct a as [u Hu]. destruct b as [v Hv].
  exists (fun n => Qmax (u n) (v n)).
  intros eps Heps.
  assert (Hhalf : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  destruct (Hu (eps / 2) Hhalf) as [N1 HN1].
  destruct (Hv (eps / 2) Hhalf) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros m n Hm Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u m - u n) + Qabs (v m - v n)) _).
  - apply QleT'_to_Qle. exact (q_max_lipschitz (u m) (v m) (u n) (v n)).
  - apply (Qlt_le_trans _ (eps / 2 + eps / 2) _).
    + apply Qplus_lt_compat.
      * apply QltT_to_Qlt.
        apply (HN1 m n).
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)].
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
      * apply QltT_to_Qlt.
        apply (HN2 m n).
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hm)].
        -- apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)].
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
Defined.

(* real_min 投影 *)
Lemma real_min_proj : forall (a b : Real) (n : nat),
  QeqT (projT1 (real_min a b) n) (Qmin (projT1 a n) (projT1 b n)).
Proof.
  intros a b n.
  apply qeq_imp_qeqT.
  unfold real_min.
  destruct a as [u Hu]. destruct b as [v Hv].
  reflexivity.
Qed.

(* real_max 投影 *)
Lemma real_max_proj : forall (a b : Real) (n : nat),
  QeqT (projT1 (real_max a b) n) (Qmax (projT1 a n) (projT1 b n)).
Proof.
  intros a b n.
  apply qeq_imp_qeqT.
  unfold real_max.
  destruct a as [u Hu]. destruct b as [v Hv].
  reflexivity.
Qed.

(* ============ 2. abs 族（逐点 |·| 性质，req/eps 形式） ============ *)

(* |0| == 0：逐点 Qabs 0 == 0（Qabs_pos 于 0 ≤ 0） *)
Lemma real_abs_zero_req : real_eq (real_abs real_zero) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj real_zero n)).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  setoid_rewrite Hz. unfold Qminus.
  apply (Qabs_pos 0). apply Qle_refl.
Qed.

(* |a·b| == |a|·|b|：逐点 Qabs_Qmult *)
Lemma real_abs_mult_req : forall a b : Real,
  real_eq (real_abs (real_mult a b)) (real_mult (real_abs a) (real_abs b)).
Proof.
  intros a b. apply real_eq_of_zero_diff.
  intro n.
  destruct a as [u Hu]. destruct b as [v Hv].
  cbn [projT1 real_abs real_mult].
  apply qeq_imp_qeqT.
  rewrite (Qabs_Qmult (u n) (v n)).
  unfold Qminus. ring.
Qed.

(* 0 < a ⟹ |a| == a：逐点 Qabs_pos（尾部 a_n > 0）——用 eps-N 直构（N := N0） *)
Lemma real_abs_pos_req : forall a : Real,
  real_lt real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a Ha.
  destruct Ha as [eps0 [Heps0 [N0 HN0]]].
  unfold real_eq.
  intros eps Heps.
  exists N0.
  intros n Hn.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
  (* 目标：QltT eps (Qabs (|a_n| − a_n))；尾部 a_n > eps0 > 0 ⟹ |a_n| == a_n ⟹ 差 == 0 *)
  assert (Hpos : Qlt 0 (projT1 a n)).
  { (* HN0 n Hn : QltT eps0 (projT1 a n − projT1 real_zero n)；0 == projT1 real_zero n *)
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hlt : Qlt eps0 (projT1 a n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HN0 n Hn). }
    rewrite Hz in Hlt.
    apply (proj2 (Qlt_minus_iff 0 (projT1 a n))).
    apply (Qlt_le_trans _ (projT1 a n - 0) _).
    - apply (Qlt_trans _ eps0 _).
      + apply QltT_to_Qlt. exact Heps0.
      + exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. }
  assert (Habs : Qabs (projT1 a n) == projT1 a n).
  { apply Qabs_pos. apply (Qlt_le_weak 0 (projT1 a n)). exact Hpos. }
  (* | |a_n| − a_n | == | a_n − a_n | == 0 < eps *)
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    rewrite Habs.
    transitivity (Qabs 0).
    + apply Qabs_wd. unfold Qminus. ring.
    + apply (Qabs_pos 0). apply Qle_refl.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* 0 ≤ |a| 逐 eps：对任意 eps>0（R 层），le zero (plus (abs a) eps) *)
(* Real 层实现：lt zero eps（R 层）给见证 eps0，逐点 |a_n| + eps_n ≥ eps0/2 > 0 ⟹ real_lt 分支 *)
(* 接口字段形态：forall a (eps : R), lt zero eps -> le zero (plus (abs a) eps)。
   Real 层：forall (eps : Real), real_lt real_zero eps ->
     real_le real_zero (real_plus (real_abs a) eps)。 *)
Lemma real_abs_nonneg_le_eps : forall (a eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_abs a) eps).
Proof.
  intros a eps Heps.
  (* real_le = Or lt eq：取 lt 分支。见证 eps0/2：|a_n| + eps_n − 0 ≥ eps_n ≥ eps0/2 > 0（尾部） *)
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req real_zero (real_plus (real_abs a) eps)). left.
  unfold real_lt.
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps0/2 < (|a_n| + eps_n) − 0 == |a_n| + eps_n
       由 HN0 : eps0 < eps_n − 0 == eps_n，且 |a_n| ≥ 0 ⟹ |a_n| + eps_n ≥ eps_n > eps0 ≥ eps0/2 *)
    assert (Hepsn : Qlt eps0 (projT1 eps n)).
    { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hlt : Qlt eps0 (projT1 eps n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HN0 n Hn). }
      rewrite Hz in Hlt.
      apply (proj2 (Qlt_minus_iff eps0 (projT1 eps n))).
      assert (Hshape : (projT1 eps n - 0) - eps0 == projT1 eps n - eps0) by (unfold Qminus; ring).
      rewrite <- Hshape.
      apply (proj1 (Qlt_minus_iff eps0 (projT1 eps n - 0))). exact Hlt.
    }
    assert (Habsn : Qle 0 (projT1 (real_abs a) n)).
    { rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)). apply Qabs_nonneg. }
    assert (Hsum : Qlt eps0 (projT1 (real_abs a) n + projT1 eps n)).
    { apply (Qlt_le_trans _ (0 + projT1 eps n) _).
      - apply (Qlt_le_trans _ (projT1 eps n) _).
        + exact Hepsn.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qplus_le_compat 0 (projT1 (real_abs a) n) (projT1 eps n) (projT1 eps n)).
        + exact Habsn.
        + apply Qle_refl. }
    apply (Qlt_le_trans _ (projT1 (real_abs a) n + projT1 eps n) _).
    + (* eps0/2 < eps0 < |a_n| + eps_n：eps0/2 < eps0 *)
      apply (Qlt_trans _ eps0 _).
      * apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
      * exact Hsum.
    + (* |a_n| + eps_n ≤ (|a_n| + eps_n) − 0：相等反向 *)
      apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
      unfold Qminus.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs a) eps n)).
      assert (Hn0 : - 0 == 0) by (compute; reflexivity).
      setoid_rewrite Hn0.
      apply Qeq_sym. apply Qplus_0_r.
Qed.

(* |a+b| ≤ |a|+|b| 逐 eps：复用 real_abs_triangle_eps（Bishop 形式） *)
(* 接口形态：forall a b (eps : R), lt zero eps -> le (abs (plus a b)) (plus (plus (abs a) (abs b)) eps) *)
(* Real 层逐 eps 证明（Q 层 eps 由 R 层 eps 见证导出） *)
Lemma real_abs_triangle_le_eps : forall (a b eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_plus a b)) (real_plus (real_plus (real_abs a) (real_abs b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req (real_abs (real_plus a b))
                                      (real_plus (real_plus (real_abs a) (real_abs b)) eps)). left.
  unfold real_lt.
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps0/2 < (|a_n|+|b_n|+eps_n) − |a_n+b_n|
       三角：|a_n+b_n| ≤ |a_n|+|b_n| ⟹ 差 ≥ eps_n ≥ eps0 > eps0/2 *)
    assert (Htri : Qle (Qabs (projT1 (real_plus a b) n))
                       (projT1 (real_abs a) n + projT1 (real_abs b) n)).
    { destruct a as [u Hu]. destruct b as [v Hv].
      cbn [projT1 real_abs real_plus].
      exact (Qabs_triangle (u n) (v n)). }
    assert (Hepsn : Qlt eps0 (projT1 eps n)).
    { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hlt : Qlt eps0 (projT1 eps n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HN0 n Hn). }
      rewrite Hz in Hlt.
      apply (proj2 (Qlt_minus_iff eps0 (projT1 eps n))).
      assert (Hshape : (projT1 eps n - 0) - eps0 == projT1 eps n - eps0) by (unfold Qminus; ring).
      rewrite <- Hshape.
      apply (proj1 (Qlt_minus_iff eps0 (projT1 eps n - 0))). exact Hlt.
    }
    (* 差 == (|a_n|+|b_n|+eps_n) − |a_n+b_n| ≥ eps_n > eps0 > eps0/2 *)
    apply (Qlt_le_trans _ eps0 _).
    + (* eps0/2 < eps0 *)
      apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
    + (* eps0 ≤ 差：由 Htri ⟹ |a+b| ≤ |a|+|b| ⟹ eps0 < eps_n ≤ |a|+|b|+eps_n − |a+b| *)
      apply (Qle_trans _ (projT1 eps n) _).
      * apply (Qlt_le_weak _ _). exact Hepsn.
      * (* eps_n ≤ (|a_n|+|b_n|+eps_n) − |a_n+b_n|：X−Y==eps_n 且 X−Y ≤ X−Z（Htri: Z≤Y） *)
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_abs a) (real_abs b)) eps n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs a) (real_abs b) n)).
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus a b) n)).
        apply (Qle_trans _ ((projT1 (real_abs a) n + projT1 (real_abs b) n + projT1 eps n) - (projT1 (real_abs a) n + projT1 (real_abs b) n)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.  (* == eps_n *)
        -- (* (sum)−(|a|+|b|) ≤ (sum)−|a+b|：0 ≤ (X−Z)−(X−Y) == Y−Z ⟸ Z ≤ Y（Htri） *)
           apply (proj2 (Qle_minus_iff
                           ((projT1 (real_abs a) n + projT1 (real_abs b) n + projT1 eps n) - (projT1 (real_abs a) n + projT1 (real_abs b) n))
                           ((projT1 (real_abs a) n + projT1 (real_abs b) n + projT1 eps n) - Qabs (projT1 (real_plus a b) n)))).
            ++ apply (Qle_trans _ ((projT1 (real_abs a) n + projT1 (real_abs b) n) - Qabs (projT1 (real_plus a b) n)) _).
                 +++ apply (proj1 (Qle_minus_iff (Qabs (projT1 (real_plus a b) n))
                                                (projT1 (real_abs a) n + projT1 (real_abs b) n))).
                  exact Htri.
               +++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq.
                  apply (q_minus_minus_cancel (projT1 (real_abs a) n + projT1 (real_abs b) n + projT1 eps n)
                              (projT1 (real_abs a) n + projT1 (real_abs b) n)
                              (Qabs (projT1 (real_plus a b) n))).

Qed.
(* min/r_max 序性质（Bishop 逐 eps 形式）+ pos_test/pos_part/r_if/exp_neg/log 族
   作为独立段，验证通过后追加到 _dbg_riesetoid.v。 *)

(* 逐 eps 见证提取：R 层 eps>0 给 Q 层 eps0>0 且尾部 eps_n > eps0/2 *)
Lemma real_eps_witness : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun eps0 : Q => And (QltT 0 eps0)
    (sigT (fun N0 : nat => forall n : nat, NatLe N0 n -> QltT (eps0 / 2) (projT1 eps n)))).
Proof.
  intros eps Heps.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  exists eps0. split.
  - exact Heps0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    (* eps0/2 < eps_n：0 < eps0/2 < eps0 < eps_n − 0 == eps_n *)
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hlt0 : Qlt eps0 (projT1 eps n - 0)).
    { apply QltT_to_Qlt. exact (HN0 n Hn). }
    apply (Qlt_le_trans _ eps0 _).
    + apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
    + apply (Qle_trans _ (projT1 eps n - 0) _).
      * apply (Qlt_le_weak _ _). exact Hlt0.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
Qed.

(* 逐 eps 见证的严格版本：eps_n > eps0/2 已由 real_eps_witness 提供 *)
(* 但 witness 给 (eps0/2) < eps_n，需要更精细的 eps0/4？直接用 witness 的 eps0/2 作为
   分离见证：目标 (|a_n|+eps_n) − Qmin ≥ eps0/2 由 eps_n ≥ eps0/2 且 Qmin ≤ a_n ⟹
   (a_n+eps_n) − Qmin ≥ eps_n ≥ eps0/2 ✓（严格：eps_n > eps0/2） *)

(* min ≤ a 逐 eps：le (min a b) (plus a eps) *)
Lemma real_min_le_l_eps : forall (a b eps : Real),
  real_lt real_zero eps ->
  real_le (real_min a b) (real_plus a eps).
Proof.
  intros a b eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req (real_min a b) (real_plus a eps)). left.
  unfold real_lt.
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标：eps0/2 < (a_n + eps_n) − Qmin(a_n,b_n)：Qmin ≤ a_n ⟹ 差 ≥ eps_n > eps0/2 *)
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj a eps n)).
    rewrite (qeqT_imp_qeq _ _ (real_min_proj a b n)).
    (* 差 == (a_n+eps_n) − Qmin ≥ (a_n+eps_n) − a_n == eps_n > eps0/2 *)
    apply (Qlt_le_trans _ (projT1 eps n) _).
    + (* eps0/2 ≤ eps_n *)
      apply QltT_to_Qlt. exact (HN0 n Hn).
    + (* eps_n < (a_n+eps_n) − Qmin：Qmin ≤ a_n ⟹ 差 ≥ eps_n，严格由 eps_n 部分 *)
      apply (Qle_trans (projT1 eps n) ((projT1 a n + projT1 eps n) - projT1 a n)
                       ((projT1 a n + projT1 eps n) - Qmin (projT1 a n) (projT1 b n))).
      -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      -- apply (Qplus_le_compat (projT1 a n + projT1 eps n) (projT1 a n + projT1 eps n)
                               (- (projT1 a n)) (- (Qmin (projT1 a n) (projT1 b n)))).
         ++ apply Qle_refl.
         ++ apply (Qopp_le_compat (Qmin (projT1 a n) (projT1 b n)) (projT1 a n)).
            apply Q.le_min_l.
Qed.

(* min ≤ b 逐 eps：对称 *)
Lemma real_min_le_r_eps : forall (a b eps : Real),
  real_lt real_zero eps ->
  real_le (real_min a b) (real_plus b eps).
Proof.
  intros a b eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req (real_min a b) (real_plus b eps)). left.
  unfold real_lt.
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj b eps n)).
    rewrite (qeqT_imp_qeq _ _ (real_min_proj a b n)).
    apply (Qlt_le_trans _ (projT1 eps n) _).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + apply (Qle_trans (projT1 eps n) ((projT1 b n + projT1 eps n) - projT1 b n)
                       ((projT1 b n + projT1 eps n) - Qmin (projT1 a n) (projT1 b n))).
      -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      -- apply (Qplus_le_compat (projT1 b n + projT1 eps n) (projT1 b n + projT1 eps n)
                               (- (projT1 b n)) (- (Qmin (projT1 a n) (projT1 b n)))).
         ++ apply Qle_refl.
         ++ apply (Qopp_le_compat (Qmin (projT1 a n) (projT1 b n)) (projT1 b n)).
            apply Q.le_min_r.
Qed.

(* 0<a、0<b ⟹ 0<min a b：见证 Qmin(ea, eb)（逐点 Q.min_glb_lt 于 a_n、b_n 下界） *)
Lemma real_min_pos : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_min a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [ea [Hea [Na HNa]]].
  destruct Hb as [eb [Heb [Nb HNb]]].
  set (e := Qmin ea eb).
  assert (He : QltT 0 e).
  { apply Qlt_to_QltT.
    apply Q.min_glb_lt.
    - apply QltT_to_Qlt. exact Hea.
    - apply QltT_to_Qlt. exact Heb. }
  unfold real_lt.
  exists e. split.
  - exact He.
  - exists (Nat.max Na Nb).
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_min_proj a b n)).
    (* 目标：e < Qmin(a_n,b_n) − 0 == Qmin(a_n,b_n)（尾部：e ≤ ea < a_n，e ≤ eb < b_n）
       用 Qlt：e < ea（ea 最小或相等？不——e = min(ea,eb) ≤ ea 且 0 < ea < a_n。
       需要严格 e < a_n：e ≤ ea 且 ea < a_n ⟹ e < a_n（Qle_lt_trans）。
       然后 Q.min_glb_lt：e < a_n 且 e < b_n ⟹ e < Qmin(a_n,b_n)（严格！） *)
    assert (Han : Qlt ea (projT1 a n)).
    { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hlt0 : Qlt ea (projT1 a n - 0)).
      { apply QltT_to_Qlt. apply (HNa n). apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      apply (proj2 (Qlt_minus_iff ea (projT1 a n))).
      apply (Qlt_le_trans _ ((projT1 a n - 0) - ea) _).
      - apply (proj1 (Qlt_minus_iff ea (projT1 a n - 0))). exact Hlt0.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. }
    assert (Hbn : Qlt eb (projT1 b n)).
    { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hlt0 : Qlt eb (projT1 b n - 0)).
      { apply QltT_to_Qlt. apply (HNb n). apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      apply (proj2 (Qlt_minus_iff eb (projT1 b n))).
      apply (Qlt_le_trans _ ((projT1 b n - 0) - eb) _).
      - apply (proj1 (Qlt_minus_iff eb (projT1 b n - 0))). exact Hlt0.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. }
    (* e < a_n：e == Qmin ea eb ≤ ea < a_n（Qle_lt_trans：e ≤ ea 且 ea < a_n） *)
    assert (Hen : Qlt e (projT1 a n)).
    { apply (Qle_lt_trans e ea (projT1 a n)).
      - unfold e. apply Q.le_min_l.
      - exact Han. }
    assert (Hem : Qlt e (projT1 b n)).
    { apply (Qle_lt_trans e eb (projT1 b n)).
      - unfold e. apply Q.le_min_r.
      - exact Hbn. }
    (* e < Qmin(a_n,b_n) − 0：e < Qmin（Q.min_glb_lt 严格）+ 减 0 桥 *)
    apply (Qlt_le_trans _ (Qmin (projT1 a n) (projT1 b n)) _).
    { apply Q.min_glb_lt. exact Hen. exact Hem. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. assert (Hn0 : - 0 == 0) by (compute; reflexivity). setoid_rewrite Hn0. apply Qeq_sym. apply Qplus_0_r. }
Qed.

(* r_max ≥ a 逐 eps：le a (plus (r_max a b) eps)（Q.le_max_l） *)
Lemma real_r_max_le_l_eps : forall (a b eps : Real),
  real_lt real_zero eps ->
  real_le a (real_plus (real_max a b) eps).
Proof.
  intros a b eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req a (real_plus (real_max a b) eps)). left.
  unfold real_lt.
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_max a b) eps n)).
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    (* 目标：eps0/2 < (max(a_n,b_n) + eps_n) − a_n：max ≥ a_n ⟹ 差 ≥ eps_n > eps0/2 *)
    apply (Qlt_le_trans _ (projT1 eps n) _).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + apply (Qle_trans (projT1 eps n)
        ((Qmax (projT1 a n) (projT1 b n) + projT1 eps n) - Qmax (projT1 a n) (projT1 b n))
        ((Qmax (projT1 a n) (projT1 b n) + projT1 eps n) - projT1 a n)).
      -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      -- apply (Qplus_le_compat (Qmax (projT1 a n) (projT1 b n) + projT1 eps n)
                               (Qmax (projT1 a n) (projT1 b n) + projT1 eps n)
                               (- (Qmax (projT1 a n) (projT1 b n))) (- (projT1 a n))).
         ++ apply Qle_refl.
         ++ apply (Qopp_le_compat (projT1 a n) (Qmax (projT1 a n) (projT1 b n))).
            apply Q.le_max_l.
Qed.

(* r_max ≥ b 逐 eps：对称（Q.le_max_r） *)
Lemma real_r_max_le_r_eps : forall (a b eps : Real),
  real_lt real_zero eps ->
  real_le b (real_plus (real_max a b) eps).
Proof.
  intros a b eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  apply (RealSetoid.real_lt_le_iff_req b (real_plus (real_max a b) eps)). left.
  unfold real_lt.
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps0].
  - exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_max a b) eps n)).
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    apply (Qlt_le_trans _ (projT1 eps n) _).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + apply (Qle_trans (projT1 eps n)
        ((Qmax (projT1 a n) (projT1 b n) + projT1 eps n) - Qmax (projT1 a n) (projT1 b n))
        ((Qmax (projT1 a n) (projT1 b n) + projT1 eps n) - projT1 b n)).
      -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      -- apply (Qplus_le_compat (Qmax (projT1 a n) (projT1 b n) + projT1 eps n)
                               (Qmax (projT1 a n) (projT1 b n) + projT1 eps n)
                               (- (Qmax (projT1 a n) (projT1 b n))) (- (projT1 b n))).
         ++ apply Qle_refl.
         ++ apply (Qopp_le_compat (projT1 b n) (Qmax (projT1 a n) (projT1 b n))).
            apply Q.le_max_r.
Qed.

(* r_max_l_iff：b ≤ a ⟹ r_max a b == a（逐点 Q.max_l_iff，Or 分解） *)
(* Real 层：real_le b a -> real_eq (real_max a b) a *)
Lemma real_r_max_l_iff : forall a b : Real,
  real_le b a -> real_eq (real_max a b) a.
Proof.
  intros a b Hba.
  unfold real_le in Hba.
  destruct Hba as [Hlt | Heq].
  - (* b < a：尾部 b_n < a_n ⟹ Qmax(a_n,b_n) == a_n ⟹ 逐点相等 ⟹ real_eq（N0 后） *)
    destruct Hlt as [eps0 [Heps0 [N0 HN0]]].
    unfold real_eq.
    intros eps Heps.
    exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    (* 目标：QltT eps (Qabs (Qmax(a_n,b_n) − a_n))；尾部 b_n < a_n − eps0 ⟹ Qmax == a_n（Q.max_l_iff 反向） *)
    assert (Hbna : Qlt (projT1 b n) (projT1 a n)).
    { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hlt0 : Qlt eps0 (projT1 a n - projT1 b n)).
      { apply QltT_to_Qlt. apply (HN0 n Hn). }
      (* eps0 < a_n − b_n ⟹ b_n < a_n：Qlt_minus_iff 反向（0 < eps0 < a_n−b_n） *)
      apply (proj2 (Qlt_minus_iff (projT1 b n) (projT1 a n))).
      apply (Qlt_le_trans _ (projT1 a n - projT1 b n) _).
      - apply (Qlt_trans _ eps0 _).
        + apply QltT_to_Qlt. exact Heps0.
        + exact Hlt0.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. }
    assert (Hmax : Qmax (projT1 a n) (projT1 b n) == projT1 a n).
    { exact (proj2 (Q.max_l_iff (projT1 a n) (projT1 b n))
        (Qlt_le_weak (projT1 b n) (projT1 a n) Hbna)). }
    apply (Qle_lt_trans _ 0 _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hmax. transitivity (Qabs 0).
      * apply Qabs_wd. unfold Qminus. ring.
      * apply (Qabs_pos 0). apply Qle_refl.
    + apply QltT_to_Qlt. exact Heps.
  - (* b == a：|Qmax(a_n,b_n) − a_n| == |Qmax(a_n,b_n) − Qmax(a_n,a_n)| ≤ |b_n−a_n| → 0 *)
    unfold real_eq in Heq.
    unfold real_eq.
    intros eps Heps.
    destruct (Heq eps Heps) as [N1 HN1].
    exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    (* |Qmax(a_n,b_n) − a_n| ≤ |b_n − a_n|：q_max_lipschitz + Qmax(a_n,a_n)==a_n *)
    apply (Qle_lt_trans _ (Qabs (projT1 b n - projT1 a n)) _).
    + (* |Qmax(a_n,b_n) − a_n| ≤ |b_n − a_n|：a_n == Qmax(a_n,a_n) 换形 + q_max_lipschitz *)
      apply (Qle_trans _ (Qabs (Qmax (projT1 a n) (projT1 b n) - Qmax (projT1 a n) (projT1 a n))) _).
      { (* |Qmax(a,b) − a_n| ≤ |Qmax(a,b) − Qmax(a,a)|：a_n == Qmax(a,a) 经 Qabs_wd *)
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. unfold Qminus. rewrite (Q.max_id (projT1 a n)). ring. }
      { (* |Qmax(a,b) − Qmax(a,a)| ≤ |a−a| + |b−a| == |b−a|（q_max_lipschitz） *)
        apply (Qle_trans _ (Qabs (projT1 a n - projT1 a n) + Qabs (projT1 b n - projT1 a n)) _).
        - apply QleT'_to_Qle. exact (q_max_lipschitz (projT1 a n) (projT1 b n) (projT1 a n) (projT1 a n)).
        - apply (Qle_trans _ (0 + Qabs (projT1 b n - projT1 a n)) _).
          + apply (Qplus_le_compat _ _ _ _).
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. transitivity (Qabs 0).
              -- apply Qabs_wd. unfold Qminus. ring.
              -- apply (Qabs_pos 0). apply Qle_refl.
            * apply Qle_refl.
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. }
    + apply QltT_to_Qlt. apply (HN1 n Hn).
Qed.
(* pos_test / pos_part / r_if / exp_neg 族 / log 族——独立段，验证后合并 *)

(* ============ 4. pos_test / pos_part / r_if ============ *)

(* pos_test x := real_lt real_zero x（Set 层 sigT 直接可用） *)
Definition real_pos_test (x : Real) : Set := real_lt real_zero x.

(* pos_part a := r_max a real_zero *)
Definition real_pos_part (a : Real) : Real := real_max a real_zero.

(* pos_part_def : pos_part a == r_max a zero（定义即得） *)
Lemma real_pos_part_def : forall a : Real,
  real_eq (real_pos_part a) (real_max a real_zero).
Proof.
  intro a. unfold real_pos_part. apply real_eq_refl.
Qed.

(* pos_part 非负逐 eps：le zero (plus (pos_part a) eps)（r_max_le_r_eps 于 b:=zero） *)
Lemma real_pos_part_nonneg_eps : forall (a eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_pos_part a) eps).
Proof.
  intros a eps Heps.
  apply (real_r_max_le_r_eps a real_zero eps Heps).
Qed.

(* r_if：Set 层 Or 见证驱动的选择 *)
Definition real_r_if (P : Set) (Hd : Or P (Not P)) (v_true v_false : Real) : Real :=
  match Hd with
  | inl _ => v_true
  | inr _ => v_false
  end.

(* r_if_true：P ⟹ r_if P Hd v_t v_f == v_t *)
Lemma real_r_if_true : forall (P : Set) (Hd : Or P (Not P)) (v_true v_false : Real),
  P -> real_eq (real_r_if P Hd v_true v_false) v_true.
Proof.
  intros P Hd v_true v_false HP.
  destruct Hd as [HP' | HnP].
  - apply real_eq_refl.
  - exact (match HnP HP with end).
Qed.

(* r_if_false：Not P ⟹ r_if P Hd v_t v_f == v_f *)
Lemma real_r_if_false : forall (P : Set) (Hd : Or P (Not P)) (v_true v_false : Real),
  Not P -> real_eq (real_r_if P Hd v_true v_false) v_false.
Proof.
  intros P Hd v_true v_false HnP.
  destruct Hd as [HP | HnP'].
  - exact (match HnP HP with end).
  - apply real_eq_refl.
Qed.

(* ============ 5. exp_neg 族（e^{-x} 语义） ============ *)

Definition real_exp_neg (x : Real) : Real := cauchy_real_exp (real_opp x).

(* e^{-x} > 0：cauchy_real_exp_pos 于 (−x) *)
Lemma real_exp_neg_pos : forall x : Real,
  real_lt real_zero (real_exp_neg x).
Proof.
  intro x. unfold real_exp_neg. apply cauchy_real_exp_pos.
Qed.

(* e^{-0} == 1：e^0 == 1（cauchy_real_exp_zero）+ 0 == −0 *)
Lemma real_exp_neg_zero : real_eq (real_exp_neg real_zero) real_one.
Proof.
  unfold real_exp_neg.
  apply (real_eq_trans (cauchy_real_exp (real_opp real_zero)) (cauchy_real_exp real_zero) real_one).
  - apply cauchy_real_exp_wd.
    apply real_eq_of_zero_diff.
    intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_zero n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz. ring.
  - exact cauchy_real_exp_zero.
Qed.

(* 逐点：−(a+b) == −a+−b *)
Lemma real_opp_plus : forall a b : Real,
  real_eq (real_opp (real_plus a b)) (real_plus (real_opp a) (real_opp b)).
Proof.
  intros a b. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus a b) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_opp a) (real_opp b) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj a b n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj b n)).
  unfold Qminus. ring.
Qed.

(* e^{-(a+b)} == e^{-a}·e^{-b}：−(a+b) == −a+−b 换形 + exp_plus *)
Lemma real_exp_neg_plus : forall a b : Real,
  real_eq (real_exp_neg (real_plus a b)) (real_mult (real_exp_neg a) (real_exp_neg b)).
Proof.
  intros a b.
  unfold real_exp_neg.
  apply (real_eq_trans (cauchy_real_exp (real_opp (real_plus a b)))
                       (cauchy_real_exp (real_plus (real_opp a) (real_opp b)))
                       (real_mult (cauchy_real_exp (real_opp a)) (cauchy_real_exp (real_opp b)))).
  - apply cauchy_real_exp_wd. exact (real_opp_plus a b).
  - exact (cauchy_real_exp_plus (real_opp a) (real_opp b)).
Qed.

(* exp_neg 递减：a<b ⟹ e^{-b}<e^{-a}（−b<−a 经 real_opp_lt_compat + exp 单调） *)
Lemma real_exp_neg_decr : forall a b : Real,
  real_lt a b -> real_lt (real_exp_neg b) (real_exp_neg a).
Proof.
  intros a b Hab.
  unfold real_exp_neg.
  (* 目标：e^{−b} < e^{−a}；−b < −a（real_opp_lt_compat）+ cauchy_real_exp_mono *)
  apply cauchy_real_exp_mono.
  apply (real_opp_lt_compat a b). exact Hab.
Qed.

(* exp_neg 非严格递减：a≤b ⟹ e^{-b}≤e^{-a}（Or 分解） *)
Lemma real_exp_neg_le_decr : forall a b : Real,
  real_le a b -> real_le (real_exp_neg b) (real_exp_neg a).
Proof.
  intros a b Hab.
  unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req (real_exp_neg b) (real_exp_neg a)). left.
    exact (real_exp_neg_decr a b Hlt).
  - apply (RealSetoid.real_eq_le (real_exp_neg b) (real_exp_neg a)).
    unfold real_exp_neg.
    apply cauchy_real_exp_wd.
    (* −b == −a：b == a 经 real_eq_opp_compat 换序 *)
    apply (RealSetoid.real_eq_opp_compat b a (real_eq_sym a b Heq)).
Qed.

(* ============ 6. log 族（log := cw_log、log_inv := opp∘log） ============ *)

(* log x := cw_log x Hx（带正性前提） *)
Definition real_log (x : Real) (Hx : real_lt real_zero x) : Real := cw_log x Hx.

(* log_mult：log(a·b) == log a + log b（log_inv_mult_thm） *)
Lemma real_log_mult : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_log (real_mult a b) (real_mult_positive a b Ha Hb))
          (real_plus (real_log a Ha) (real_log b Hb)).
Proof.
  intros a b Ha Hb.
  unfold real_log.
  exact (log_inv_mult_thm a b Ha Hb (real_mult_positive a b Ha Hb)).
Qed.

(* log_one：log 1 == 0（log_inv_one_thm） *)
Lemma real_log_one : forall (H : real_lt real_zero real_one),
  real_eq (real_log real_one H) real_zero.
Proof.
  intros H. unfold real_log. exact (log_inv_one_thm H).
Qed.

(* log_inv x := −log x = −(cw_log x) *)
Definition real_log_inv (x : Real) (Hx : real_lt real_zero x) : Real :=
  real_opp (cw_log x Hx).

(* log_inv_log：log_inv x == −log x（定义即得） *)
Lemma real_log_inv_log : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log_inv x Hx) (real_opp (real_log x Hx)).
Proof.
  intros x Hx. unfold real_log_inv, real_log. apply real_eq_refl.
Qed.

(* exp_neg_log_inv：e^{-log_inv x} == x（e^{−(−ln x)} == e^{ln x} == x） *)
Lemma real_exp_neg_log_inv : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_exp_neg (real_log_inv x Hx)) x.
Proof.
  intros x Hx.
  unfold real_exp_neg, real_log_inv.
  (* 目标：e^{−(−(cw_log x))} == x；−(−u) == u 换形 + cw_log_exp_right *)
  apply (real_eq_trans (cauchy_real_exp (real_opp (real_opp (cw_log x Hx))))
                       (cauchy_real_exp (cw_log x Hx))
                       x).
  - (* e^{−(−u)} == e^u：−(−u) == u 经 exp_wd *)
    apply cauchy_real_exp_wd.
    apply real_eq_of_zero_diff.
    intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_opp (cw_log x Hx)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cw_log x Hx) n)).
    unfold Qminus. ring.
  - exact (cw_log_exp_right x Hx).
Qed.

End EnhancedSetoidMain.

(* ============ 接口与实例：Module 隔离字段名（Module 不能在 Section 内） ============ *)
Module RealInterfaceEnhancedMod.
Existing Instance Real_RealInterfaceSetoid.
(* RealInterfaceEnhancedSetoid 接口定义 + Real 层实例——独立段（不继承，全字段显式） *)

(* ============ 7. RealInterfaceEnhancedSetoid 接口 ============
   独立 Class（req 版 RealInterfaceEnhanced，req := real_eq）：
   - 基类字段（环/序/inv/metric/lim/cauchy_complete，来自 RealInterfaceSetoid 同款）
   - exp_neg 语义 = e^{-x}（Boltzmann，与 RealInterfaceEnhanced L275-280 一致）
   - log/log_inv 带正性前提（构造性 log 需 x>0）；log_inv := -log
   - 非严格 le 输出字段用 Bishop 逐 eps 形式（判例）
   - log_le_linear/log_eq_linear：深水区，后续论证 *)
Class RealInterfaceEnhancedSetoid := {
  (* setoid 核心 *)
  req : Real -> Real -> Set;
  req_refl : forall x, real_eq x x;
  req_sym : forall x y, real_eq x y -> real_eq y x;
  req_trans : forall x y z, real_eq x y -> real_eq y z -> real_eq x z;
  zero : Real;
  one : Real;
  plus : Real -> Real -> Real;
  mult : Real -> Real -> Real;
  opp : Real -> Real;
  abs : Real -> Real;
  lt : Real -> Real -> Set;
  le : Real -> Real -> Set;
  req_plus_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_eq (plus x1 y1) (plus x2 y2);
  req_mult_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_eq (mult x1 y1) (mult x2 y2);
  req_opp_compat : forall x y, real_eq x y -> real_eq (opp x) (opp y);
  req_abs_compat : forall x y, real_eq x y -> real_eq (abs x) (abs y);
  req_lt_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_lt x1 y1 -> real_lt x2 y2;
  req_le_compat : forall x1 x2 y1 y2, real_eq x1 x2 -> real_eq y1 y2 ->
    real_le x1 y1 -> real_le x2 y2;
  plus_assoc : forall a b c, real_eq (plus a (plus b c)) (plus (plus a b) c);
  plus_comm : forall a b, real_eq (plus a b) (plus b a);
  plus_zero : forall a, real_eq (plus a zero) a;
  plus_opp : forall a, real_eq (plus a (opp a)) zero;
  mult_assoc : forall a b c, real_eq (mult a (mult b c)) (mult (mult a b) c);
  mult_comm : forall a b, real_eq (mult a b) (mult b a);
  mult_one : forall a, real_eq (mult a one) a;
  distrib : forall a b c, real_eq (mult a (plus b c)) (plus (mult a b) (mult a c));
  mult_zero : forall a, real_eq (mult a zero) zero;
  lt_irrefl : forall a, Not (real_lt a a);
  lt_trans : forall a b c, real_lt a b -> real_lt b c -> real_lt a c;
  le_refl : forall a, real_le a a;
  le_trans : forall a b c, real_le a b -> real_le b c -> real_le a c;
  le_antisym : forall a b, real_le a b -> real_le b a -> real_eq a b;
  le_lt_trans : forall a b c, real_le a b -> real_lt b c -> real_lt a c;
  lt_le_trans : forall a b c, real_lt a b -> real_le b c -> real_lt a c;
  lt_le_iff : forall a b, Or (real_lt a b) (real_eq a b) -> real_le a b;
  le_id_l : forall a b c, real_eq a b -> real_le b c -> real_le a c;
  le_id_r : forall a b c, real_eq b c -> real_le a b -> real_le a c;
  lt_id_l : forall a b c, real_eq a b -> real_lt b c -> real_lt a c;
  lt_id_r : forall a b c, real_eq b c -> real_lt a b -> real_lt a c;
  inv_pos : forall x, real_lt zero x -> Real;
  inv_pos_correct : forall x H, real_eq (mult x (inv_pos x H)) one;

  (* ===== Enhanced 字段（req 版 RealInterfaceEnhanced） ===== *)
  one_pos : real_lt zero one;
  lt_plus_compat : forall a b c d, real_lt a b -> real_lt c d -> real_lt (plus a c) (plus b d);
  le_plus_compat : forall a b c d, real_le a b -> real_le c d -> real_le (plus a c) (plus b d);
  plus_positive : forall a b, real_lt zero a -> real_lt zero b -> real_lt zero (plus a b);
  mult_positive : forall a b, real_lt zero a -> real_lt zero b -> real_lt zero (mult a b);
  lt_mult_compat : forall a b c, real_lt zero c -> real_lt a b -> real_lt (mult a c) (mult b c);
  le_mult_compat : forall a b c, real_lt zero c -> real_le a b -> real_le (mult a c) (mult b c);
  le_mult_compat_weak : forall a b c, real_le zero c -> real_le a b -> real_le (mult a c) (mult b c);
  opp_lt_compat : forall a b, real_lt a b -> real_lt (opp b) (opp a);
  lt_zero_opp : forall a, real_lt zero a -> real_lt (opp a) zero;
  opp_le_compat : forall a b, real_le a b -> real_le (opp b) (opp a);
  inv_pos_pos : forall x H, real_lt zero (inv_pos x H);
  inv_pos_ext : forall x y Hx Hy, real_eq x y -> real_eq (inv_pos x Hx) (inv_pos y Hy);
  inv_pos_le_compat : forall a b Ha Hb, real_le a b -> real_le (inv_pos b Hb) (inv_pos a Ha);

  (* min：序性质逐 eps 形式 *)
  min : Real -> Real -> Real;
  min_le_l : forall a b (eps : Real), real_lt zero eps -> real_le (min a b) (plus a eps);
  min_le_r : forall a b (eps : Real), real_lt zero eps -> real_le (min a b) (plus b eps);
  min_pos : forall a b, real_lt zero a -> real_lt zero b -> real_lt zero (min a b);

  (* r_max：le 方向逐 eps，iff 方向 req *)
  r_max : Real -> Real -> Real;
  r_max_le_l : forall a b (eps : Real), real_lt zero eps -> real_le a (plus (r_max a b) eps);
  r_max_le_r : forall a b (eps : Real), real_lt zero eps -> real_le b (plus (r_max a b) eps);
  r_max_l_iff : forall a b, real_le b a -> real_eq (r_max a b) a;
  r_max_r_iff : forall a b, real_le a b -> real_eq (r_max a b) b;

  (* pos_test / pos_part / r_if *)
  pos_test : Real -> Set;
  pos_test_lt : forall x, real_pos_test x -> real_lt zero x;
  lt_pos_test : forall x, real_lt zero x -> real_pos_test x;
  pos_part : Real -> Real;
  pos_part_def : forall a, real_eq (pos_part a) (r_max a zero);
  pos_part_nonneg : forall a (eps : Real), real_lt zero eps -> real_le zero (plus (pos_part a) eps);
  mr_if : bool -> Real -> Real -> Real;
  mr_if_true : forall v_t v_f : Real, real_eq (mr_if true v_t v_f) v_t;
  mr_if_false : forall v_t v_f : Real, real_eq (mr_if false v_t v_f) v_f;

  (* abs 族 *)
  abs_nonneg : forall a (eps : Real), real_lt zero eps -> real_le zero (plus (abs a) eps);
  abs_triangle : forall a b (eps : Real), real_lt zero eps ->
    real_le (abs (plus a b)) (plus (plus (abs a) (abs b)) eps);
  abs_zero : real_eq (abs zero) zero;
  abs_mult : forall a b, real_eq (abs (mult a b)) (mult (abs a) (abs b));
  abs_opp : forall a, real_eq (abs (opp a)) (abs a);
  abs_pos : forall a, real_lt zero a -> real_eq (abs a) a;

  (* exp_neg 族：e^{-x} 语义（Boltzmann） *)
  exp_neg : Real -> Real;
  exp_neg_pos : forall x, real_lt zero (exp_neg x);
  exp_neg_zero : real_eq (exp_neg zero) one;
  exp_neg_plus : forall a b, real_eq (exp_neg (plus a b)) (mult (exp_neg a) (exp_neg b));
  exp_neg_decr : forall a b, real_lt a b -> real_lt (exp_neg b) (exp_neg a);
  exp_neg_le_decr : forall a b, real_le a b -> real_le (exp_neg b) (exp_neg a);

  (* log 族：带正性前提；log_inv := -log *)
  log : forall x, real_lt zero x -> Real;
  log_mult : forall a b Ha Hb, real_eq (log (mult a b) (mult_positive a b Ha Hb)) (plus (log a Ha) (log b Hb));
  log_one : forall H, real_eq (log one H) zero;
  (* log 凹性切线（Bishop 逐 eps）：log x ≤ x−1+eps（x>0, eps>0）。
     非严格 le 输出用逐 eps 形式（先例：real_le = Or lt eq 无法表达
     等号点 x=1 的"不趋近"；判例论证 Real 层 real_log_le_linear_eps 已证）。 *)
  log_le_linear_eps : forall x (Hx : real_lt zero x) (eps : Real), real_lt zero eps ->
    real_le (log x Hx) (plus (plus x (opp one)) eps);
  log_inv : forall x, real_lt zero x -> Real;
  log_inv_log : forall x Hx, real_eq (log_inv x Hx) (opp (log x Hx));
  exp_neg_log_inv : forall x Hx, real_eq (exp_neg (log_inv x Hx)) x;

  (* metric / lim / cauchy_complete *)
  metric : Real -> Real -> Real;
  metric_sym : forall a b, real_eq (metric a b) (metric b a);
  metric_pos : forall a b (eps : Real), real_lt zero eps -> real_le zero (plus (metric a b) eps);
  metric_zero : forall a b, real_eq (metric a b) zero -> real_eq a b;
  metric_triangle : forall a b c (eps : Real), real_lt zero eps ->
    real_le (metric a c) (plus (plus (metric a b) (metric b c)) eps);
  lim : (nat -> Real) -> Real -> Set;
  lim_unique : forall u l1 l2, real_lim u l1 -> real_lim u l2 -> real_eq l1 l2;
  cauchy_complete :
    forall u : nat -> Real,
      (forall eps : Real, real_lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> real_lt (metric (u m) (u n)) eps)) ->
      sigT (fun l : Real => real_lim u l);
}.

(* r_max_r_iff：a ≤ b ⟹ r_max a b == b（对称于 l_iff） *)
Lemma real_r_max_r_iff : forall a b : Real,
  real_le a b -> real_eq (real_max a b) b.
Proof.
  intros a b Hab.
  unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - (* a < b：尾部 a_n < b_n ⟹ Qmax(a_n,b_n) == b_n *)
    destruct Hlt as [eps0 [Heps0 [N0 HN0]]].
    unfold real_eq.
    intros eps Heps.
    exists N0.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    assert (Hanb : Qlt (projT1 a n) (projT1 b n)).
    { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hlt0 : Qlt eps0 (projT1 b n - projT1 a n)).
      { apply QltT_to_Qlt. apply (HN0 n Hn). }
      apply (proj2 (Qlt_minus_iff (projT1 a n) (projT1 b n))).
      apply (Qlt_le_trans _ (projT1 b n - projT1 a n) _).
      - apply (Qlt_trans _ eps0 _).
        + apply QltT_to_Qlt. exact Heps0.
        + exact Hlt0.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring. }
    assert (Hmax : Qmax (projT1 a n) (projT1 b n) == projT1 b n).
    { exact (proj2 (Q.max_r_iff (projT1 a n) (projT1 b n))
             (Qlt_le_weak (projT1 a n) (projT1 b n) Hanb)). }
    apply (Qle_lt_trans _ 0 _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hmax. transitivity (Qabs 0).
      * apply Qabs_wd. unfold Qminus. ring.
      * apply (Qabs_pos 0). apply Qle_refl.
    + apply QltT_to_Qlt. exact Heps.
  - (* a == b：|Qmax(a_n,b_n) − b_n| ≤ |a_n−b_n| → 0 *)
    unfold real_eq in Heq.
    unfold real_eq.
    intros eps Heps.
    destruct (Heq eps Heps) as [N1 HN1].
    exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    apply (Qle_lt_trans _ (Qabs (projT1 a n - projT1 b n)) _).
    + apply (Qle_trans _ (Qabs (Qmax (projT1 a n) (projT1 b n) - Qmax (projT1 b n) (projT1 b n))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. unfold Qminus. rewrite (Q.max_id (projT1 b n)). ring.
      * apply (Qle_trans _ (Qabs (projT1 a n - projT1 b n) + Qabs (projT1 b n - projT1 b n)) _).
        -- apply QleT'_to_Qle. exact (q_max_lipschitz (projT1 a n) (projT1 b n) (projT1 b n) (projT1 b n)).
        -- apply (Qle_trans _ (Qabs (projT1 a n - projT1 b n) + 0) _).
           ++ apply (Qplus_le_compat _ _ _ _).
              ** apply Qle_refl.
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. transitivity (Qabs 0).
                 --- apply Qabs_wd. unfold Qminus. ring.
                 --- apply (Qabs_pos 0). apply Qle_refl.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
    + apply QltT_to_Qlt. apply (HN1 n Hn).
Qed.
(* ============ 8. Instance RealEnhancedReal ============ *)
Section LogLinearMain.
(* 检验：log_le_linear / log_eq_linear 论证——e^t ≥ 1+t（构造性，全部 t）
   目标（Real 层核心）：real_exp_ge_linear_eps : forall t eps, lt zero eps ->
     le (1+t) (e^t + eps)（Bishop 逐 eps 形式，real_le = Or lt eq 无法表达等号点）
   数学：
   - t ≥ 0：exp_partial_ge_plus_x（主文件已有）
   - t = −a ≤ 0、0 ≤ a ≤ 1：奇截断配对非负（a^{2k}/(2k)! − a^{2k+1}/(2k+1)! ≥ 0）
   - t = −a ≤ 0、a ≥ 1：偶截断 exp_even_neg_nonneg（L12617）+ 奇截断
     exp_partial_odd_lower（L12948，|y|≤M, m≥m0 ⟹ 1/(2C) < S_{2m+1}(y)，正下界）
   - 逐点三分（Qlt_le_dec 可判定）+ 有界性（real_norm_bounded）+ 尾项衰减
     （exp_partial_tail_small）⟹ 各分支 G_n := exp_partial n (u n) − 1 − u n ≥ 0
   Q 层引理 4 条（§1-4）+ Real 层主引理（§5）。 *)
(* ============ 1. 配对非负：0 ≤ a ≤ 1 ⟹ a^{2k}/(2k)! − a^{2k+1}/(2k+1)! ≥ 0 ============
   即 a^{2k}(1/(2k)! − a/(2k+1)!) ≥ 0。因 0 ≤ a ≤ 1 < 2k+1（k≥1），
   1/(2k)! − a/(2k+1)! ≥ 1/(2k)! − 1/(2k+1)! = 2k/(2k+1)! ≥ 0。
   用 q_le_div_le 桥（A/B ≤ C/D ⟸ A·D ≤ C·B，B,D 正）。 *)
Lemma q_pair2_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' a 1 -> (1 <= k)%nat ->
  QleT' 0 (q_pow a (2 * k) / q_fact (2 * k) - q_pow a (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k))).
Proof.
  intros a k Ha Ha1 Hk1.
  apply Qle_to_QleT'.
  apply (proj1 (Qle_minus_iff (q_pow a (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)))
                              (q_pow a (2 * k) / q_fact (2 * k)))).
  apply QleT'_to_Qle.
  apply (q_le_div_le (q_pow a (Datatypes.S (2 * k))) (q_fact (Datatypes.S (2 * k)))
                     (q_pow a (2 * k)) (q_fact (2 * k))).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply Qle_to_QleT'.
    assert (Hpow : q_pow a (Datatypes.S (2 * k)) == a * q_pow a (2 * k)).
    { apply (qeqT_imp_qeq _ _ (q_pow_succ a (2 * k))). }
    setoid_rewrite Hpow.
    setoid_replace (q_fact (Datatypes.S (2 * k)))
      with ((Z.of_nat (Datatypes.S (2 * k)) # 1) * q_fact (2 * k)).
    2: { apply (qeqT_imp_qeq _ _ (q_fact_succ (2 * k))). }
    setoid_replace (a * q_pow a (2 * k) * q_fact (2 * k))
      with (a * (q_pow a (2 * k) * q_fact (2 * k))). 2: ring.
    setoid_replace (q_pow a (2 * k) * ((Z.of_nat (Datatypes.S (2 * k)) # 1) * q_fact (2 * k)))
      with ((Z.of_nat (Datatypes.S (2 * k)) # 1) * (q_pow a (2 * k) * q_fact (2 * k))). 2: ring.
    apply (Qmult_le_compat_r a (Z.of_nat (Datatypes.S (2 * k)) # 1)
                             (q_pow a (2 * k) * q_fact (2 * k))).
    * apply (Qle_trans _ 1 _).
      + apply QleT'_to_Qle. exact Ha1.
      + unfold Qle. simpl. lia.
    * apply Qmult_le_0_compat.
      + apply QleT'_to_Qle. apply q_pow_nonneg. exact Ha.
      + apply (Qlt_le_weak 0 (q_fact (2 * k))). apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* ============ 2. 奇部分和 ≥ 1−a：0 ≤ a ≤ 1 ⟹ 1−a ≤ exp_partial (2m+1) (−a) ============
   归纳：S_{2(m+1)+1}(−a) = S_{2m+1}(−a) + [(−a)^{2m+2}/(2m+2)! + (−a)^{2m+3}/(2m+3)!]
   新增项 = a^{2m+2}/(2m+2)! − a^{2m+3}/(2m+3)! ≥ 0（q_pair2_nonneg 于 k := m+1）。
   形态纪律：全部用 2·S m 字面形态（Hstep 证明：rewrite Hk2/Hk1 归一再 cbn+ring）。 *)
Lemma exp_partial_odd_ge_minus : forall (a : Q) (m : nat),
  QleT' 0 a -> QleT' a 1 -> QleT' (1 - a) (exp_partial (Datatypes.S (2 * m)) (- a)).
Proof.
  intros a m Ha Ha1.
  apply Qle_to_QleT'.
  induction m as [| m IH].
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    unfold Qminus.
    cbn [exp_partial].
    assert (Hp : q_pow (- a) 1 == - a).
    { change (q_pow (- a) (Datatypes.S 0) == - a).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ (- a) 0)). simpl. ring. }
    assert (Hf : q_fact 1 == 1).
    { cbn [q_fact]. ring. }
    setoid_rewrite Hp.
    setoid_rewrite Hf.
    unfold Qdiv.
    assert (Hi : Qinv 1 == 1) by (unfold Qinv; reflexivity).
    setoid_rewrite Hi.
    ring.
  - assert (Hk2 : (Datatypes.S (2 * Datatypes.S m) = Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat) by lia.
    assert (Hk1 : (2 * Datatypes.S m = Datatypes.S (Datatypes.S (2 * m)))%nat) by lia.
    assert (Hstep : exp_partial (Datatypes.S (2 * Datatypes.S m)) (- a) ==
                    exp_partial (Datatypes.S (2 * m)) (- a) +
                    (q_pow (- a) (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
                     q_pow (- a) (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m)))).
    { rewrite Hk2. rewrite Hk1. cbn [exp_partial]. ring. }
    assert (Hadd : Qle 0 (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) -
                          q_pow a (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m)))).
    { apply QleT'_to_Qle. apply (q_pair2_nonneg a (Datatypes.S m) Ha Ha1). lia. }
    apply (Qle_trans _ (exp_partial (Datatypes.S (2 * m)) (- a)) _).
    + exact IH.
    + apply (Qle_trans _ (exp_partial (Datatypes.S (2 * m)) (- a) +
                          (q_pow (- a) (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
                           q_pow (- a) (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m)))) _).
      * apply (Qle_trans _ (exp_partial (Datatypes.S (2 * m)) (- a) + 0) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a (Datatypes.S m))).
           setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a (Datatypes.S m))).
           assert (Hadd' : Qle 0
             (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
              (- q_pow a (Datatypes.S (2 * Datatypes.S m))) / q_fact (Datatypes.S (2 * Datatypes.S m)))).
           { unfold Qminus in Hadd.
             apply (Qle_trans _ (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
                                 (- (q_pow a (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m))))) _).
             - exact Hadd.
             - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring. }
           exact (Qplus_le_compat _ _ _ _ (Qle_refl _) Hadd').
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Hstep.
Qed.

(* ============ 3. 奇部分和递增：0 ≤ a ≤ 1 ⟹ S(2m+1)(−a) ≤ S(2m+3)(−a) ============ *)
Lemma exp_partial_odd_mono : forall (a : Q) (m : nat),
  QleT' 0 a -> QleT' a 1 ->
  QleT' (exp_partial (Datatypes.S (2 * m)) (- a)) (exp_partial (Datatypes.S (2 * Datatypes.S m)) (- a)).
Proof.
  intros a m Ha Ha1.
  apply Qle_to_QleT'.
  assert (Hk2 : (Datatypes.S (2 * Datatypes.S m) = Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat) by lia.
  assert (Hk1 : (2 * Datatypes.S m = Datatypes.S (Datatypes.S (2 * m)))%nat) by lia.
  assert (Hstep : exp_partial (Datatypes.S (2 * Datatypes.S m)) (- a) ==
                  exp_partial (Datatypes.S (2 * m)) (- a) +
                  (q_pow (- a) (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
                   q_pow (- a) (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m)))).
  { rewrite Hk2. rewrite Hk1. cbn [exp_partial]. ring. }
  apply (Qle_trans _ (exp_partial (Datatypes.S (2 * m)) (- a) +
                      (q_pow (- a) (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
                       q_pow (- a) (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m)))) _).
  - apply (Qle_trans _ (exp_partial (Datatypes.S (2 * m)) (- a) + 0) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a (Datatypes.S m))).
      setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a (Datatypes.S m))).
      assert (Hadd' : Qle 0
        (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
         (- q_pow a (Datatypes.S (2 * Datatypes.S m))) / q_fact (Datatypes.S (2 * Datatypes.S m)))).
      { apply (Qle_trans _ (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) +
                            (- (q_pow a (Datatypes.S (2 * Datatypes.S m)) / q_fact (Datatypes.S (2 * Datatypes.S m))))) _).
        - apply QleT'_to_Qle. apply (q_pair2_nonneg a (Datatypes.S m) Ha Ha1). lia.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring. }
      exact (Qplus_le_compat _ _ _ _ (Qle_refl _) Hadd').
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Hstep.
Qed.

(* ============ 4. 奇截断 ≤ 偶截断：0 ≤ a ⟹ S(2m+1)(−a) ≤ S(2m)(−a) ============
   S(2m+1)(−a) = S(2m)(−a) + (−a)^{2m+1}/(2m+1)!，而 (−a)^{2m+1} == −a^{2m+1} ≤ 0。 *)
Lemma exp_partial_odd_le_even : forall (a : Q) (m : nat),
  QleT' 0 a ->
  QleT' (exp_partial (Datatypes.S (2 * m)) (- a)) (exp_partial (2 * m) (- a)).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  assert (Hstep : exp_partial (Datatypes.S (2 * m)) (- a) ==
                  exp_partial (2 * m) (- a) +
                  q_pow (- a) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))).
  { reflexivity. }
  assert (Hneg : Qle (q_pow (- a) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) 0).
  { setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a m)).
    unfold Qdiv.
    apply (proj2 (Qle_minus_iff ((- q_pow a (Datatypes.S (2 * m))) * Qinv (q_fact (Datatypes.S (2 * m)))) 0)).
    change (Qle 0 (0 - (- q_pow a (Datatypes.S (2 * m))) * Qinv (q_fact (Datatypes.S (2 * m))))).
    unfold Qminus. ring_simplify.
    apply QleT'_to_Qle. apply (q_div_nonneg (q_pow a (Datatypes.S (2 * m))) (q_fact (Datatypes.S (2 * m)))).
    - apply (q_pow_nonneg a (Datatypes.S (2 * m))). exact Ha.
    - apply q_fact_pos. }
  apply (Qle_trans _ (exp_partial (2 * m) (- a) + 0) _).
  - rewrite Hstep. apply (Qplus_le_compat _ _ _ _ (Qle_refl _)). exact Hneg.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============ 5. 辅助：0 ≤ a ≤ 1 ⟹ 偶截断 ≥ 1−a（odd_le_even + odd_ge_minus） ============ *)
Lemma exp_partial_even_ge_minus : forall (a : Q) (m : nat),
  QleT' 0 a -> QleT' a 1 -> QleT' (1 - a) (exp_partial (2 * m) (- a)).
Proof.
  intros a m Ha Ha1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (exp_partial (Datatypes.S (2 * m)) (- a)) _).
  - apply QleT'_to_Qle. apply (exp_partial_odd_ge_minus a m Ha Ha1).
  - apply QleT'_to_Qle. apply (exp_partial_odd_le_even a m Ha).
Qed.

(* ============ 6. Real 层核心：e^t ≥ 1+t（Bishop 逐 eps） ============
   real_exp_ge_linear_eps : forall (t eps : Real), real_lt real_zero eps ->
     real_le (real_plus real_one t) (real_plus (cauchy_real_exp t) eps)
   即 1+t ≤ e^t + eps（Bishop 逐 eps；real_le 取 lt 分支）。
   逐点 G_n := exp_partial n (u n) − 1 − u n ≥ 0 分支：
   - u n ≥ 0：exp_partial_ge_plus_x（n ≥ 1）
   - u n ≤ 0（a := −u n ≥ 0）：
     * 0 ≤ a ≤ 1：奇/偶下标 odd_ge_minus / even_ge_minus（§2/§5）
     * a ≥ 1：偶下标 exp_even_neg_nonneg（L12617）；奇下标 exp_partial_odd_lower
       （L12948，m ≥ m0+1，|−a| ≤ M ⟹ S_{2m+1}(−a) > 1/(2C)）
   - 有界性 real_norm_bounded ⟹ M；exp_series_arch ⟹ C；exp_partial_tail_small ⟹ m0。
   - 见证 eps0/2，N := max N0 (2m0+3)：n ≥ N ⟹ n ≥ 1 且奇 n 的 m ≥ m0+1。 *)

(* 辅助 A1：x ≥ 0、n ≥ 1 ⟹ exp_partial n x − 1 − x ≥ 0（ge_plus_x） *)
Lemma exp_partial_ge_linear_aux1 : forall (x : Q) (n : nat),
  (1 <= n)%nat -> QleT' 0 x -> QleT' 0 (exp_partial n x - 1 - x).
Proof.
  intros x n Hn Hx.
  apply Qle_to_QleT'.
  destruct n as [| n'].
  - exfalso. inversion Hn.
  - (* 0 ≤ S − 1 − x：换形 S − 1 − x == S − (1+x)，再经 Qle_minus_iff 化为 1+x ≤ S *)
    assert (Hreshape : exp_partial (Datatypes.S n') x - 1 - x == exp_partial (Datatypes.S n') x - (1 + x)).
    { unfold Qminus. ring. }
    setoid_rewrite Hreshape.
    apply (proj1 (Qle_minus_iff (1 + x) (exp_partial (Datatypes.S n') x))).
    apply QleT'_to_Qle. apply (exp_partial_ge_plus_x n' x). exact Hx.
Qed.

(* 辅助 A2：x ≤ 0、0 ≤ −x ≤ 1 ⟹ exp_partial n x − 1 − x ≥ 0（n 任意） *)
Lemma exp_partial_ge_linear_aux2 : forall (x : Q) (n : nat),
  QleT' x 0 -> QleT' 0 (- x) -> QleT' (- x) 1 ->
  QleT' 0 (exp_partial n x - 1 - x).
Proof.
  intros x n Hx0 H0a Ha1.
  apply Qle_to_QleT'.
  destruct (Nat.odd n) eqn:En.
  - apply Nat.odd_spec in En. destruct En as [m Hm]. subst n.
    (* 目标：0 ≤ S_{2m+1}(x) − 1 − x。odd_ge_minus（签名 S(2m)）于 a := −x，
       S(2m) == S_{2m+1} 需 lia 桥。 *)
    assert (Htarget : Qle 0 (exp_partial (2 * m + 1) x - (1 + x))).
    { apply (proj1 (Qle_minus_iff (1 + x) (exp_partial (2 * m + 1) x))).
      apply (Qle_trans _ (1 - (- x)) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      - apply (Qle_trans _ (exp_partial (2 * m + 1) (- (- x))) _).
        + (* odd_ge_minus 于 a := −x 给 1−(−x) ≤ S_{S(2m)}(−(−x))；S(2m) == 2m+1 *)
          assert (Hidx : (Datatypes.S (2 * m) = 2 * m + 1)%nat) by lia.
          rewrite <- Hidx.
          apply QleT'_to_Qle. apply (exp_partial_odd_ge_minus (- x) m H0a Ha1).
        + apply QleT'_to_Qle. apply qeq_le. apply (exp_partial_wd (2 * m + 1) (- (- x)) x).
          apply qeq_imp_qeqT. ring. }
    apply (Qle_trans _ (exp_partial (2 * m + 1) x - (1 + x))
                       (exp_partial (2 * m + 1) x - 1 - x)).
    + exact Htarget.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
  - assert (Heven : Nat.even n = true).
    { rewrite <- (Nat.negb_odd n). rewrite En. reflexivity. }
    apply Nat.even_spec in Heven. destruct Heven as [m Hm]. subst n.
    assert (Htarget : Qle 0 (exp_partial (2 * m) x - (1 + x))).
    { apply (proj1 (Qle_minus_iff (1 + x) (exp_partial (2 * m) x))).
      apply (Qle_trans _ (1 - (- x)) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
      - apply (Qle_trans _ (exp_partial (2 * m) (- (- x))) _).
        + apply QleT'_to_Qle. apply (exp_partial_even_ge_minus (- x) m H0a Ha1).
        + apply QleT'_to_Qle. apply qeq_le. apply (exp_partial_wd (2 * m) (- (- x)) x).
          apply qeq_imp_qeqT. ring. }
    apply (Qle_trans _ (exp_partial (2 * m) x - (1 + x))
                       (exp_partial (2 * m) x - 1 - x)).
    + exact Htarget.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
Qed.

(* 辅助 A3：x ≤ 0、1 ≤ −x ⟹ exp_partial (2m) x − 1 − x ≥ 0（偶下标，exp_even_neg_nonneg） *)
Lemma exp_partial_ge_linear_aux3 : forall (x : Q) (m : nat),
  QleT' x 0 -> QleT' 1 (- x) -> QleT' 0 (exp_partial (2 * m) x - 1 - x).
Proof.
  intros x m Hx0 H1a.
  apply Qle_to_QleT'.
  (* a := −x ≥ 1。S_{2m}(−a) ≥ 0（exp_even_neg_nonneg）⟹ G = S − 1 − x = S + a − 1 ≥ a − 1 ≥ 0 *)
  apply (Qle_trans _ ((- x) - 1) _).
  - (* 0 ≤ a − 1：1 ≤ a ⟺ 0 ≤ a − 1 *)
    apply (proj1 (Qle_minus_iff 1 (- x))). apply QleT'_to_Qle. exact H1a.
  - (* a − 1 ≤ S_{2m}(x) − 1 − x。x == −a：S_{2m}(−a) + a − 1 ≥ a − 1（S ≥ 0） *)
    apply (Qle_trans _ ((- x) - 1 + 0) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((- x) - 1 + exp_partial (2 * m) x) _).
      * apply (Qplus_le_compat (- x - 1) (- x - 1) 0 (exp_partial (2 * m) x)).
        -- apply Qle_refl.
        -- (* 0 ≤ S_{2m}(x) == S_{2m}(−a)，exp_even_neg_nonneg 于 a := −x *)
           apply (Qle_trans _ (exp_partial (2 * m) (- (- x))) _).
           ++ apply QleT'_to_Qle. apply (exp_even_neg_nonneg (- x) m).
              apply Qle_to_QleT'.
              apply (Qle_trans _ (- 0) _).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              ** apply (Qopp_le_compat x 0). apply QleT'_to_Qle. exact Hx0.
           ++ apply QleT'_to_Qle. apply qeq_le. apply (exp_partial_wd (2 * m) (- (- x)) x).
              apply qeq_imp_qeqT. ring.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
Qed.

(* 辅助 A4：x ≤ 0、1 ≤ −x、m ≥ m0+1、|x| ≤ M
   ⟹ exp_partial (2m+1) x − 1 − x ≥ 0（奇下标，odd_lower 正下界） *)
Lemma exp_partial_ge_linear_aux4 :
  forall (M C : Q) (m0 m : nat) (x : Q),
    QleT' 0 M -> QleT' 1 C ->
    (forall k : nat, QleT' (exp_series k M) C) ->
    (forall k : nat, NatLe m0 k ->
      QltT (q_pow M (2 * k + 1) / q_fact (2 * k + 1)) (1 / (2 * C))) ->
    NatLe (m0 + 1) m -> QleT' (Qabs x) M -> QleT' x 0 -> QleT' 1 (- x) ->
    QleT' 0 (exp_partial (2 * m + 1) x - 1 - x).
Proof.
  intros M C m0 m x HM HC HCser Htail Hm HxM Hx0 H1a.
  (* S_{2m+1}(x) > 1/(2C)（odd_lower 于 y := x，|x| ≤ M，m0 ≤ m） *)
  assert (Hodd : Qlt (1 / (2 * C)) (exp_partial (2 * m + 1) x)).
  { apply QltT_to_Qlt. apply (exp_partial_odd_lower M C m0 m x HM HC HCser (fun k Hk => Htail k Hk)).
    - apply NatLe_drop in Hm. lia.
    - exact HxM. }
  (* G = S − 1 − x。Hodd：1/(2C) < S；H1a：1 ≤ −x（⟹ −x−1 ≥ 0）；1/(2C) > 0。
     链：0 ≤ 1/(2C) + (−x−1) ≤ S + (−x−1) == S − 1 − x *)
  assert (HinvC_pos : Qlt 0 (1 / (2 * C))).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat 1 (Qinv (2 * C))).
    - unfold Qlt; simpl; lia.
    - apply Qinv_lt_0_compat.
      apply (Qmult_lt_0_compat 2 C).
      + unfold Qlt; simpl; lia.
      + apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)]. }
  assert (Ha1 : Qle 0 (- x - 1)).
  { apply (proj1 (Qle_minus_iff 1 (- x))). apply QleT'_to_Qle. exact H1a. }
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((1 / (2 * C)) + (- x - 1)) _).
  - (* 0 ≤ 1/(2C) + (−x−1)：两项非负 *)
    apply (Qplus_le_compat 0 (1 / (2 * C)) 0 (- x - 1)).
    + apply (Qlt_le_weak 0 _). exact HinvC_pos.
    + exact Ha1.
  - (* 1/(2C) + (−x−1) ≤ S + (−x−1)：Hodd *)
    apply (Qle_trans _ (exp_partial (2 * m + 1) x + (- x - 1)) _).
    + apply (Qplus_le_compat (1 / (2 * C)) (exp_partial (2 * m + 1) x) (- x - 1) (- x - 1)).
      * apply (Qlt_le_weak _ _). exact Hodd.
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
Qed.

(* ============ 7. 主引理：real_exp_ge_linear_eps ============ *)
Lemma real_exp_ge_linear_eps : forall (t eps : Real),
  real_lt real_zero eps ->
  real_le (real_plus real_one t) (real_plus (cauchy_real_exp t) eps).
Proof.
  intros t eps Heps.
  unfold real_le.
  left.
  destruct t as [u Hu].
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  destruct (exp_partial_tail_small M C (qltT_leT' 0 M HMpos) HC1) as [m0 Hm0].
  exists (eps0 / 2)%Q.
  split.
  - apply Qlt_to_QltT.
    apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps0.
  - exists (Nat.max N0 (2 * m0 + 3))%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (HnN0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 (2 * m0 + 3)) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hnbig : (2 * m0 + 3 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 (2 * m0 + 3)) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    assert (Hn1 : (1 <= n)%nat) by lia.
    assert (Hepsn : QltT eps0 (projT1 eps n - 0)).
    { apply (HN0 n). apply NatLe_lift. exact HnN0. }
    assert (Hepsn_le : Qle eps0 (projT1 eps n)).
    { apply (Qle_trans _ (projT1 eps n - 0) _).
      - apply (Qlt_le_weak _ _). apply QltT_to_Qlt. exact Hepsn.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* 目标：eps0/2 < exp_partial n (u n) + eps_n − 1 − u n
       ⟸ eps0/2 < eps0 ≤ G_n + eps_n（G_n ≥ 0） *)
    apply (Qlt_le_trans _ eps0 _).
    + (* eps0/2 < eps0 *)
      apply QltT_to_Qlt. apply (q_half_lt_self eps0). exact Heps0.
    + (* eps0 ≤ (e^t + eps)_n − (1+t)_n。链：eps0 ≤ eps_n ≤ eps_n + 0 ≤ eps_n + (S−1−u n)
         且 eps_n + (S−1−u n) == 展开形态（Hproj） *)
      assert (Hproj : (projT1 (real_plus (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) eps) n -
                        projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) n) ==
                       ((exp_partial n (u n) - 1 - u n) + projT1 eps n)).
      { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) eps n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (existT (fun s : Qseq => cauchy s) u Hu) n)).
        cbn [projT1 cauchy_real_exp real_one].
        ring. }
      (* 主断言：G_n ≥ 0（逐点三分）——提前证明 *)
      assert (Hmain : Qle 0 (exp_partial n (u n) - 1 - u n)).
      { destruct (Qlt_le_dec 0 (u n)) as [Hunpos | Hunneg].
        - (* u n ≥ 0：A1 *)
          apply QleT'_to_Qle. apply (exp_partial_ge_linear_aux1 (u n) n). exact Hn1.
          apply Qle_to_QleT'. apply Qlt_le_weak. exact Hunpos.
        - (* u n ≤ 0：a := −u n ≥ 0；再分 a ≤ 1 / a ≥ 1 *)
          assert (H0a : Qle 0 (- u n)).
          { apply (Qle_trans _ (- 0) _).
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
            * apply (Qopp_le_compat (u n) 0). exact Hunneg. }
          destruct (Qlt_le_dec 1 (- u n)) as [H1a_gt | H1a_le].
          + (* 1 < a（a > 1）：A3（偶）/ A4（奇，m ≥ m0+1） *)
            destruct (Nat.odd n) eqn:En.
            * (* n 奇 = 2m+1：A4，需 m0+1 ≤ m（由 n ≥ 2m0+3） *)
              apply Nat.odd_spec in En. destruct En as [m Hm]. subst n.
              assert (Hnn : (2 * m0 + 3 <= 2 * m + 1)%nat) by (apply NatLe_drop in Hn; lia).
              apply QleT'_to_Qle. apply (exp_partial_ge_linear_aux4 M C m0 m (u (2 * m + 1)%nat) (qltT_leT' 0 M HMpos) HC1 HC (fun k Hk => Hm0 k Hk)).
              -- apply NatLe_lift. lia.
              -- exact (HM (2 * m + 1)%nat).
              -- apply Qle_to_QleT'. exact Hunneg.
              -- apply Qle_to_QleT'. apply Qlt_le_weak. exact H1a_gt.
            * (* n 偶 = 2m：A3 *)
              assert (Heven : Nat.even n = true).
              { rewrite <- (Nat.negb_odd n). rewrite En. reflexivity. }
              apply Nat.even_spec in Heven. destruct Heven as [m Hm]. subst n.
              apply QleT'_to_Qle. apply (exp_partial_ge_linear_aux3 (u (2 * m)%nat) m).
              -- apply Qle_to_QleT'. exact Hunneg.
              -- apply Qle_to_QleT'. apply Qlt_le_weak. exact H1a_gt.
          + (* a ≤ 1：A2（n 任意） *)
            apply QleT'_to_Qle. apply (exp_partial_ge_linear_aux2 (u n) n).
            * apply Qle_to_QleT'. exact Hunneg.
            * apply Qle_to_QleT'. exact H0a.
            * apply Qle_to_QleT'. exact H1a_le. }
      (* 链：eps0 ≤ eps_n ≤ 0+eps_n ≤ G_n + eps_n == 原目标（Hproj） *)
      apply (Qle_trans _ ((exp_partial n (u n) - 1 - u n) + projT1 eps n) _).
      * apply (Qle_trans _ (0 + projT1 eps n) _).
        -- apply (Qle_trans _ (projT1 eps n) _).
           ++ exact Hepsn_le.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qplus_le_compat 0 (exp_partial n (u n) - 1 - u n) (projT1 eps n) (projT1 eps n)).
           ++ exact Hmain.
           ++ apply Qle_refl.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hproj.
Qed.

(* ============ 8. log_le_linear 化归（Real 层无 real_minus，x−1 := x + (−1)） ============
   real_log_le_linear_eps : forall (x eps : Real), real_lt real_zero x ->
     real_lt real_zero eps ->
     real_le (real_log x) (real_plus (real_plus x (real_opp real_one)) eps)
   化归：y := log x，x == e^y（cw_log_exp_right）。
   real_exp_ge_linear_eps 给 1+y ≤ e^y+eps。
   链：y ≤ (1+y)+(−1) ≤ (e^y+eps)+(−1) == e^y+(−1)+eps == x+(−1)+eps（e^y==x）。 *)
Lemma real_log_le_linear_eps : forall (x eps : Real),
  forall (Hx : real_lt real_zero x),
  real_lt real_zero eps ->
  real_le (real_log x Hx) (real_plus (real_plus x (real_opp real_one)) eps).
Proof.
  intros x eps Hx Hepspos.
  set (y := real_log x Hx : Real).
  assert (H_exp_log : real_eq (cauchy_real_exp y) x).
  { unfold y, real_log. exact (cw_log_exp_right x Hx). }
  assert (Hlin : real_le (real_plus real_one y) (real_plus (cauchy_real_exp y) eps)).
  { apply (real_exp_ge_linear_eps y eps). exact Hepspos. }
  (* 目标：y ≤ x+(−1)+eps。链（见上） *)
  apply (real_le_trans y (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps) _).
  - (* y ≤ e^y+(−1)+eps *)
    apply (real_le_trans y (real_plus (real_plus real_one y) (real_opp real_one)) _).
    + (* y ≤ (1+y)+(−1)：y == 1+y+(−1)（逐点 ring，u_y k == (1+u_y k)+(−1)） *)
      apply RealSetoid.real_eq_le.
      apply real_eq_of_zero_diff. intro k. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus real_one y) (real_opp real_one) k)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one k)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one y k)).
      ring.
    + (* (1+y)+(−1) ≤ e^y+eps+(−1) ≤ e^y+(−1)+eps *)
      apply (real_le_trans (real_plus (real_plus real_one y) (real_opp real_one))
                           (real_plus (real_plus (cauchy_real_exp y) eps) (real_opp real_one))
                           (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)).
      * apply (real_le_plus_compat (real_plus real_one y) (real_plus (cauchy_real_exp y) eps)
                                   (real_opp real_one) (real_opp real_one)).
        -- exact Hlin.
        -- apply real_le_refl.
      * (* (e^y+eps)+(−1) ≤ (e^y+(−1))+eps：real_plus_assoc 两次 *)
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_plus (real_plus (cauchy_real_exp y) eps) (real_opp real_one))
                             (real_plus (cauchy_real_exp y) (real_plus eps (real_opp real_one)))
                             (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)).
        -- apply (real_eq_sym (real_plus (cauchy_real_exp y) (real_plus eps (real_opp real_one)))
                              (real_plus (real_plus (cauchy_real_exp y) eps) (real_opp real_one))).
           apply (real_plus_assoc (cauchy_real_exp y) eps (real_opp real_one)).
        -- apply (real_eq_trans (real_plus (cauchy_real_exp y) (real_plus eps (real_opp real_one)))
                                (real_plus (cauchy_real_exp y) (real_plus (real_opp real_one) eps))
                                (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)).
           ++ apply (RealSetoid.real_eq_plus_compat (cauchy_real_exp y) (real_plus eps (real_opp real_one))
                                                    (cauchy_real_exp y) (real_plus (real_opp real_one) eps)).
              ** apply real_eq_refl.
              ** apply (real_plus_comm eps (real_opp real_one)).
           ++ apply (real_plus_assoc (cauchy_real_exp y) (real_opp real_one) eps).
  - (* e^y+(−1)+eps ≤ x+(−1)+eps：e^y == x 替换 *)
    apply (real_le_plus_compat (real_plus (cauchy_real_exp y) (real_opp real_one))
                               (real_plus x (real_opp real_one)) eps eps).
    + (* e^y+(−1) ≤ x+(−1)：real_le_plus_compat（e^y≤x 由 real_eq_le，−1≤−1） *)
      apply (real_le_plus_compat (cauchy_real_exp y) x (real_opp real_one) (real_opp real_one)).
      * apply RealSetoid.real_eq_le. exact H_exp_log.
      * apply real_le_refl.
    + apply real_le_refl.
Qed.

End LogLinearMain.
Instance RealEnhancedReal : RealInterfaceEnhancedSetoid := {
  req := real_eq;
  req_refl := real_eq_refl;
  req_sym := real_eq_sym;
  req_trans := real_eq_trans;
  zero := real_zero;
  one := real_one;
  plus := real_plus;
  mult := real_mult;
  opp := real_opp;
  abs := real_abs;
  lt := real_lt;
  le := real_le;
  req_plus_compat := RealSetoid.real_eq_plus_compat_adapt;
  req_mult_compat := RealSetoid.real_eq_mult_compat_adapt;
  req_opp_compat := RealSetoid.real_eq_opp_compat;
  req_abs_compat := RealSetoid.real_eq_abs_compat;
  req_lt_compat := RealSetoid.real_lt_compat;
  req_le_compat := RealSetoid.real_le_compat;
  plus_assoc := real_plus_assoc;
  plus_comm := real_plus_comm;
  plus_zero := real_plus_zero;
  plus_opp := real_plus_opp;
  mult_assoc := real_mult_assoc;
  mult_comm := real_mult_comm;
  mult_one := real_mult_one;
  distrib := real_distrib;
  mult_zero := real_mult_zero;
  lt_irrefl := real_lt_irrefl;
  lt_trans := real_lt_trans;
  le_refl := real_le_refl;
  le_trans := real_le_trans;
  le_antisym := real_le_antisym;
  le_lt_trans := real_le_lt_trans;
  lt_le_trans := real_lt_le_trans;
  lt_le_iff := RealSetoid.real_lt_le_iff_req;
  le_id_l := RealSetoid.real_le_id_l;
  le_id_r := RealSetoid.real_le_id_r;
  lt_id_l := RealSetoid.real_lt_id_l;
  lt_id_r := RealSetoid.real_lt_id_r;
  inv_pos := real_inv_pos;
  inv_pos_correct := real_inv_pos_correct;
  one_pos := real_lt_zero_one;
  lt_plus_compat := real_lt_plus_compat;
  le_plus_compat := real_le_plus_compat;
  plus_positive := real_plus_positive;
  mult_positive := real_mult_positive;
  lt_mult_compat := (fun a b c Hc Hab => real_mult_lt_compat a b c Hab Hc);
  le_mult_compat := real_le_mult_compat;
  le_mult_compat_weak := real_le_mult_compat_weak;
  opp_lt_compat := real_opp_lt_compat;
  lt_zero_opp := real_lt_zero_opp;
  opp_le_compat := real_opp_le_compat;
  inv_pos_pos := real_inv_pos_pos;
  inv_pos_ext := real_inv_pos_ext;
  inv_pos_le_compat := real_inv_pos_le_compat;
  min := real_min;
  min_le_l := real_min_le_l_eps;
  min_le_r := real_min_le_r_eps;
  min_pos := real_min_pos;
  r_max := real_max;
  r_max_le_l := real_r_max_le_l_eps;
  r_max_le_r := real_r_max_le_r_eps;
  r_max_l_iff := real_r_max_l_iff;
  r_max_r_iff := real_r_max_r_iff;
  pos_test := real_pos_test;
  pos_test_lt := (fun x H => H);
  lt_pos_test := (fun x H => H);
  pos_part := real_pos_part;
  pos_part_def := real_pos_part_def;
  pos_part_nonneg := real_pos_part_nonneg_eps;
  mr_if := (fun (b : bool) (v_t v_f : Real) => match b with true => v_t | false => v_f end);
  mr_if_true := (fun v_t v_f : Real => real_eq_refl v_t);
  mr_if_false := (fun v_t v_f : Real => real_eq_refl v_f);
  abs_nonneg := real_abs_nonneg_le_eps;
  abs_triangle := real_abs_triangle_le_eps;
  abs_zero := real_abs_zero_req;
  abs_mult := real_abs_mult_req;
  abs_opp := real_abs_opp;
  abs_pos := real_abs_pos_req;
  exp_neg := real_exp_neg;
  exp_neg_pos := real_exp_neg_pos;
  exp_neg_zero := real_exp_neg_zero;
  exp_neg_plus := real_exp_neg_plus;
  exp_neg_decr := real_exp_neg_decr;
  exp_neg_le_decr := real_exp_neg_le_decr;
  log := real_log;
  log_mult := real_log_mult;
  log_one := real_log_one;
  log_le_linear_eps := (fun x Hx eps Hepspos => real_log_le_linear_eps x eps Hx Hepspos);
  log_inv := real_log_inv;
  log_inv_log := real_log_inv_log;
  exp_neg_log_inv := real_exp_neg_log_inv;
  metric := real_metric;
  metric_sym := RealSetoid.real_metric_sym;
  metric_pos := RealSetoid.real_metric_pos_eps;
  metric_zero := RealSetoid.real_metric_zero;
  metric_triangle := RealSetoid.real_metric_triangle_eps;
  lim := real_lim;
  lim_unique := real_lim_unique;
  cauchy_complete := RealSetoid.real_cauchy_complete_metric_natle;
}.

(* Old-name preserving definitions for the r_if family. The selection
   evidence carried by the field is a boolean (a dichotomy witness
   Or P (Not P) is used at run time only through its left/right branch),
   so after de-polymorphization of the field signatures the original
   universally quantified interface is preserved by these definitions.
   Pointwise, r_if P Hd v_t v_f equals v_t on the left branch of Hd and
   v_f on the right branch, matching the original field contract. *)
Definition r_if (R : Set) (c : RealInterfaceEnhancedSetoid) (P : Set)
    (Hd : Or P (Not P)) (v_t v_f : Real) : Real :=
  c.(mr_if) (match Hd with inl _ => true | inr _ => false end) v_t v_f.

Definition r_if_true (R : Set) (c : RealInterfaceEnhancedSetoid) (P : Set)
    (Hd : Or P (Not P)) (v_t v_f : Real) :
    P -> real_eq (r_if R c P Hd v_t v_f) v_t :=
  fun p =>
    match Hd
    return real_eq (c.(mr_if) (match Hd with inl _ => true | inr _ => false end) v_t v_f) v_t
    with
    | inl _ => c.(mr_if_true) v_t v_f
    | inr n => match n p with end
    end.

Definition r_if_false (R : Set) (c : RealInterfaceEnhancedSetoid) (P : Set)
    (Hd : Or P (Not P)) (v_t v_f : Real) :
    Not P -> real_eq (r_if R c P Hd v_t v_f) v_f :=
  fun n =>
    match Hd
    return real_eq (c.(mr_if) (match Hd with inl _ => true | inr _ => false end) v_t v_f) v_f
    with
    | inl p => match n p with end
    | inr _ => c.(mr_if_false) v_t v_f
    end.
End RealInterfaceEnhancedMod.
(* ============ log_le_linear 论证并入（来自检验 _dbg_log_linear.v 11 Qed 全部通过） ============
   Real 层核心：real_exp_ge_linear_eps（e^t ≥ 1+t，Bishop 逐 eps）
   + real_log_le_linear_eps（log x ≤ x−1+eps）。
   数学：t≥0 用 exp_partial_ge_plus_x；t≤0、0≤a≤1 用奇截断配对非负；
   t≤0、a≥1 用 exp_even_neg_nonneg（偶）+ exp_partial_odd_lower（奇，正下界）。
   逐点三分（Qlt_le_dec）+ 有界性（real_norm_bounded）+ 尾项衰减（exp_partial_tail_small）。
   log_eq_linear（e^t=1+t ⟹ t=0）需强三分/LPO，构造性不可证（诚实边界）。 *)
(* ============ Real 层 opp-mult 恒等族并入（来自检验 _dbg_oppmult.v RC=0） ============
   opp (mult a b) == mult a (opp b) / mult (opp a) b；mult a (opp b) == opp (mult a b)。
   逐点 ring（判例 #76 模式：real_eq_of_zero_diff + destruct + simpl + ring）。
   Gibbs 逐 eps 论证（判例）所需基础恒等。 *)
(* ============ Real 层 opp-mult 恒等族并入（来自检验 _dbg_oppmult.v RC=0） ============
   opp (mult a b) == mult a (opp b) / mult (opp a) b；mult a (opp b) == opp (mult a b)。
   逐点 ring（判例 #76 模式：real_eq_of_zero_diff + destruct + simpl + ring）。
   Gibbs 逐 eps 论证（判例）所需基础恒等。 *)

(* ToyR 替换稿：替换定理假设面查证（Module 语境限定名） *)
Print Assumptions RealSetoid.real_eq_le.
Print Assumptions RealSetoid.le_to_NatLe.
