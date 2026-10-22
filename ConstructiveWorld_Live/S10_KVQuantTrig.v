(* ============================================================
   使命：本件定理/引理声明面所述性质的形式化（原头注为历史注记块，
         实质整编尚待后续；本块为五字段指针）。
   依赖：件内 Require 声明面所列库件。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)

(* ============================================================ *)
(* S10_KVQuantTrig.v                                           *)
(*                                                             *)
(* 目的：KV 量化相关的三角函数与指数界：sin/cos 构造性级数、     *)
(*       扫描式零点、加法定理与 setoid 化稳态方程（Set 层）。    *)
(* 主件：steady_state_boltzmann_attn_setoid（稳态方程 setoid 版）；*)
(*       cos²+sin²==1 的代数核心（sc_cs_sq 分解）。              *)
(* 依赖：S01–S09；Stdlib（QArith、List、Bool、Arith 等）。       *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 拆分模块之一，原文区间 *)
(*       L53932-L66414，去头正文与原文区间逐字节同源。           *)
(* ============================================================ *)
(* ============================================================ *)
(* ToyR 工程 （S 系下半） · 记录册号         *)
(* 替换定理清单：sc_lp_four_nonneg（共 1 条，语句不变）；          *)
(*   其余 reflexive/转发族玩具经复核属定义性等式或库引理转发，     *)
(*   非平凡化无语义增益或损语义风险高，如实遗留不硬编。            *)
(* 非平凡性说明：仅替换上列 1 条证明体；声明面、其余定理、原头注   *)
(*   一律原样保留。口径：lp_four 定义展开 + Qle 展开 = Z 层交叉积，  *)
(*   字面归约后线性判定闭合——消除原两跳转发。纯构造性：零 公理、  *)
(*   零 承认件、零经典逻辑。编译态：深依赖链整件遗留。             *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.

Section RealKVQuantMain.
(* ---- 状态空间（Real 层模式：独立 Type，同 B-8） ---- *)
Variable S : Type.

(* ---- 逐出结构与动力学（诚实接口，Set 层可判定） ---- *)
Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Variable real_transition : S -> S -> Real.
Variable real_transition_nonneg : forall s s', real_le real_zero (real_transition s s').
(* 无向转移核（对称）：T(s,s') == T(s',s)——KV 缓存/相似度核的诚实假设 *)
Variable real_transition_sym : forall s s', real_eq (real_transition s s') (real_transition s' s).

Variable real_energy : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.

(* ---- B3 分析组装接口（T4.3 模式，可实例化） ---- *)
Variable L : Real.
Variable real_L_pos : real_lt real_zero L.
Variable E_max : Real.
Variable real_metric : S -> S -> Real.
Variable real_metric_nonneg : forall s s', real_le real_zero (real_metric s s').
(* 能量 Lipschitz：|e(s) − e(s')| ≤ L·metric(s,s')（评审点名假设） *)
Variable real_energy_lipschitz : forall s s',
  real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
          (real_mult L (real_metric s s')).
(* 能量下界：−E_max ≤ e(s)（e^{−v} 有界的温度侧来源） *)
Variable real_energy_lower : forall s,
  real_le (real_opp E_max) (real_energy s).

(* ---- 求和接口（T4.3 模式，Real 层可实例化，同 B-8） ---- *)
Variable real_sum_over_S : (S -> Real) -> Real.

(* ---- Boltzmann 因子与逐出分布 ---- *)
Definition real_kv_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (real_energy s)).

Definition real_evicted_partition : Real :=
  real_sum_over_S (fun s => if keep_dec s then real_kv_boltzmann_factor s else real_zero).

Variable real_evicted_partition_pos : real_lt real_zero real_evicted_partition.

Definition real_evicted_transition (s s' : S) : Real :=
  if keep_dec s then
    if keep_dec s' then real_transition s s' else real_zero
  else real_zero.

Definition real_evicted_boltzmann (s : S) : Real :=
  if keep_dec s then
    real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
              (real_kv_boltzmann_factor s)
  else real_zero.

(* 逐出导致的详细平衡破缺（Real 层复刻） *)
Definition real_db_breaking (s s' : S) : Real :=
  real_abs (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
                      (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s)))).

(* ============================================================ *)
(* 工具族（Real 层环组装）                                       *)
(* ============================================================ *)

(* 工具 A：a·x + (−(a·y)) == a·(x + (−y))（左提公因子，distrib + mult_opp_l） *)
Lemma real_mult_minus_l : forall (a x y : Real),
  real_eq (real_plus (real_mult a x) (real_opp (real_mult a y)))
          (real_mult a (real_plus x (real_opp y))).
Proof.
intros a x y.
  apply real_eq_sym.
  apply (real_eq_trans _ (real_plus (real_mult a x) (real_mult a (real_opp y))) _).
  - apply (real_distrib a x (real_opp y)).
  - apply (RealSetoid.real_eq_plus_compat (real_mult a x) (real_mult a (real_opp y))
                                          (real_mult a x) (real_opp (real_mult a y))
                                          (real_eq_refl _) (real_mult_opp_l a y)).
Qed.

(* 工具 B：(opp a)·b == opp (a·b)（real_opp_mult_r 反向） *)
Lemma real_opp_mult_r_sym : forall (a b : Real),
  real_eq (real_mult (real_opp a) b) (real_opp (real_mult a b)).
Proof.  intros a b.
  exact (real_eq_sym (real_opp (real_mult a b)) (real_mult (real_opp a) b)
    (real_opp_mult_r a b)).
Qed.

(* 工具 C：x·z + (−(y·z)) == (x + (−y))·z（右提公因子，distrib_r + 工具 B） *)
Lemma real_mult_minus_r : forall (x y z : Real),
  real_eq (real_plus (real_mult x z) (real_opp (real_mult y z)))
          (real_mult (real_plus x (real_opp y)) z).
Proof.
intros x y z.
  apply (real_eq_trans _ (real_plus (real_mult x z) (real_mult (real_opp y) z)) _).
  - (* 段 1：A == M：opp (mult y z) == mult (opp y) z（工具 B 反向） *)
    apply real_eq_sym.
    apply (RealSetoid.real_eq_plus_compat (real_mult x z) (real_mult (real_opp y) z)
                                          (real_mult x z) (real_opp (real_mult y z))
                                          (real_eq_refl _) (real_opp_mult_r_sym y z)).
  - (* 段 2：M == B：distrib_r 正向 *)
    apply (real_distrib_r x (real_opp y) z).
Qed.

(* 工具 D：0 ≤ x ⟹ |x| == x（Or 分解：lt 分支 real_abs_pos_req；eq 分支 |0|==0==x） *)
Lemma real_abs_nonneg_req : forall (x : Real),
  real_le real_zero x -> real_eq (real_abs x) x.
Proof.
  intros x Hle.
  destruct Hle as [Hlt | Heq].
  - apply (real_abs_pos_req x Hlt).
  - (* x == 0（Heq : real_eq real_zero x）：|x| == |0| == 0 == x *)
    apply (real_eq_trans _ real_zero _).
    + apply (real_eq_trans _ (real_abs real_zero) _).
      * apply real_eq_sym.
        apply (real_abs_eq_compat real_zero x Heq).
      * exact real_abs_zero_req.
    + (* 段 2：real_zero == x（Heq 直接匹配） *)
      exact Heq.
Qed.
(* ============================================================ *)
(* B1：逐出分支归零——db_breaking(s,s') == 0 当 s 或 s' 被逐出   *)
(* （逐出侧概率质量与转移同时为 0 ⟹ 破缺项为零）                  *)
(* ============================================================ *)

Lemma real_db_breaking_evicted_l : forall s s' : S, Not (keep s) ->
  real_eq (real_db_breaking s s') real_zero.
Proof.
  intros s s' Hnk.
  unfold real_db_breaking.
  assert (H1 : real_eq (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
                       real_zero).
  {
    unfold real_evicted_boltzmann, real_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - exact (match Hnk Hks with end).
    - (* s 逐出：ev_b s = zero 且 ev_t(s,s') 外层短路为零 ⟹ zero·zero == zero *)
      apply (real_mult_zero real_zero).
  }
  assert (H2 : real_eq (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))
                       real_zero).
  {
    unfold real_evicted_boltzmann, real_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - exact (match Hnk Hks with end).
    - destruct (keep_dec s') as [Hks' | Hnks'].
      + (* s' 保留：ev_t(s',s) == zero（内层 keep s 假）⟹ X·zero == zero *)
        apply (real_mult_zero (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                         (real_kv_boltzmann_factor s'))).
      + (* s' 逐出：zero·zero == zero *)
        apply (real_mult_zero real_zero).
  }
  assert (Hopp : real_eq (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s)))
                         real_zero).
  {
    apply (real_eq_trans _ (real_opp real_zero) _).
    - apply (RealSetoid.real_eq_opp_compat (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))
                                           real_zero H2).
    - exact real_opp_zero.
  }
  assert (Hz : real_eq
    (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
               (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))))
    (real_plus real_zero real_zero)).
  {
    apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
             (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s)))
             real_zero real_zero
             H1 Hopp).
  }
  (* db = |W| == |plus zero zero| == |zero| == zero *)
  apply (real_eq_trans _ (real_abs (real_plus real_zero real_zero)) _).
  - apply (real_abs_eq_compat
             (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
                        (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))))
             (real_plus real_zero real_zero)
             Hz).
  - apply (real_eq_trans _ (real_abs real_zero) _).
    + apply (real_abs_eq_compat (real_plus real_zero real_zero) real_zero
                                (real_plus_zero real_zero)).
    + exact real_abs_zero_req.
Qed.

Lemma real_db_breaking_evicted_r : forall s s' : S, Not (keep s') ->
  real_eq (real_db_breaking s s') real_zero.
Proof.
  intros s s' Hnk'.
  unfold real_db_breaking.
  assert (H1 : real_eq (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
                       real_zero).
  {
    unfold real_evicted_boltzmann, real_evicted_transition.
    destruct (keep_dec s') as [Hks' | Hnks'].
    - exact (match Hnk' Hks' with end).
    - destruct (keep_dec s) as [Hks | Hnks].
      + (* s 保留、s' 逐出：X·zero == zero（ev_t(s,s') 内层 keep s' 假） *)
        apply (real_mult_zero (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                         (real_kv_boltzmann_factor s))).
      + (* 双双逐出：zero·zero == zero *)
        apply (real_mult_zero real_zero).
  }
  assert (H2 : real_eq (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))
                       real_zero).
  {
    unfold real_evicted_boltzmann, real_evicted_transition.
    destruct (keep_dec s') as [Hks' | Hnks'].
    - exact (match Hnk' Hks' with end).
    - (* s' 逐出：ev_b s' = zero 且 ev_t(s',s) 外层短路为零 ⟹ zero·zero == zero *)
      apply (real_mult_zero real_zero).
  }
  assert (Hopp : real_eq (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s)))
                         real_zero).
  {
    apply (real_eq_trans _ (real_opp real_zero) _).
    - apply (RealSetoid.real_eq_opp_compat (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))
                                           real_zero H2).
    - exact real_opp_zero.
  }
  assert (Hz : real_eq
    (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
               (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))))
    (real_plus real_zero real_zero)).
  {
    apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
             (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s)))
             real_zero real_zero
             H1 Hopp).
  }
  (* db = |W| == |plus zero zero| == |zero| == zero *)
  apply (real_eq_trans _ (real_abs (real_plus real_zero real_zero)) _).
  - apply (real_abs_eq_compat
             (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
                        (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))))
             (real_plus real_zero real_zero)
             Hz).
  - apply (real_eq_trans _ (real_abs real_zero) _).
    + apply (real_abs_eq_compat (real_plus real_zero real_zero) real_zero
                                (real_plus_zero real_zero)).
    + exact real_abs_zero_req.
Qed.

(* ============================================================ *)
(* B2：都保留分支提因子——                                        *)
(*   db(s,s') == inv Z_ev · T(s,s') · |b(s) − b(s')|            *)
(* 链：|·| 内项 == inv·(b·T − b'·T')（assoc 反向 + 左提公因子）  *)
(*      → T' == T（对称）→ 右提公因子 → |mult Z T| == |Z|·T     *)
(* ============================================================ *)

Lemma real_db_breaking_kept : forall s s' : S,
  keep s -> keep s' ->
  real_eq (real_db_breaking s s')
          (real_abs (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                               (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                          (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))).
Proof.
  intros s s' Hs Hs'.
  unfold real_db_breaking.
  assert (Hw : real_eq
    (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
               (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))))
    (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
               (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                          (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))).
  {
    unfold real_evicted_boltzmann, real_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - destruct (keep_dec s') as [Hks' | Hnks'].
      + (* s、s' 都保留：继续 *)
        apply (real_eq_trans
                 _ (real_plus (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                         (real_mult (real_kv_boltzmann_factor s) (real_transition s s')))
                              (real_opp (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                                   (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))) _).
        * assert (Hl : real_eq
                  (real_mult (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                        (real_kv_boltzmann_factor s)) (real_transition s s'))
                  (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                             (real_mult (real_kv_boltzmann_factor s) (real_transition s s')))).
          { apply real_eq_sym.
            apply (real_mult_assoc (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                   (real_kv_boltzmann_factor s) (real_transition s s')). }
          assert (Hr : real_eq
                  (real_opp (real_mult (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                                  (real_kv_boltzmann_factor s')) (real_transition s' s)))
                  (real_opp (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                       (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))).
          { apply (RealSetoid.real_eq_opp_compat
                     (real_mult (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                           (real_kv_boltzmann_factor s')) (real_transition s' s))
                     (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))).
            apply real_eq_sym.
            apply (real_mult_assoc (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                   (real_kv_boltzmann_factor s') (real_transition s' s)). }
          exact (RealSetoid.real_eq_plus_compat
                   (real_mult (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                         (real_kv_boltzmann_factor s)) (real_transition s s'))
                   (real_opp (real_mult (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                                   (real_kv_boltzmann_factor s')) (real_transition s' s)))
                   (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                              (real_mult (real_kv_boltzmann_factor s) (real_transition s s')))
                   (real_opp (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                        (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))
                   Hl Hr).
        * apply (real_mult_minus_l (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                   (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                   (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))).
      + (* s' 逐出：与 Hs' 矛盾 *)
        exact (match Hnks' Hs' with end).
    - (* s 逐出：与 Hs 矛盾 *)
      exact (match Hnks Hs with end).
  }
  apply (real_eq_trans
           _ (real_abs (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                  (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                             (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))) _).
  - apply (real_abs_eq_compat
             (real_plus (real_mult (real_evicted_boltzmann s) (real_evicted_transition s s'))
                        (real_opp (real_mult (real_evicted_boltzmann s') (real_evicted_transition s' s))))
             (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                        (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                   (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))
             Hw).
  - apply real_eq_refl.
Qed.

(* B2b：|·| 提出 inv（|inv·W| == inv·|W|，inv 正） *)
Lemma real_db_breaking_kept_abs : forall s s' : S,
  keep s -> keep s' ->
  real_eq (real_db_breaking s s')
          (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                     (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                          (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))).
Proof.
  intros s s' Hs Hs'.
  pose proof (real_db_breaking_kept s s' Hs Hs') as Hk.
  (* |inv·W| == |inv|·|W| == inv·|W|（abs_mult_req + abs_pos_req，inv > 0） *)
  assert (Habs : real_eq
    (real_abs (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                         (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                    (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))))
    (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
               (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                    (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))))).
  {
    apply (real_eq_trans
             _ (real_mult (real_abs (real_inv_pos real_evicted_partition real_evicted_partition_pos))
                          (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                               (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))) _).
    - apply (real_abs_mult_req (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                               (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                          (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))).
    - apply (RealSetoid.real_eq_mult_compat
               (real_abs (real_inv_pos real_evicted_partition real_evicted_partition_pos))
               (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                    (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))
               (real_inv_pos real_evicted_partition real_evicted_partition_pos)
               (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                    (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))
               (real_abs_pos_req (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                 (real_inv_pos_pos real_evicted_partition real_evicted_partition_pos))
               (real_eq_refl _)).
  }
  apply (real_eq_trans _ (real_abs (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                              (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                                         (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))) _).
  - exact Hk.
  - exact Habs.
Qed.

(* B2c：T' == T（对称）+ 右提公因子 + |T| == T（非负）
   最终形态：db == inv Z_ev · T(s,s') · |b(s) − b(s')| *)
Lemma real_db_breaking_kept_final : forall s s' : S,
  keep s -> keep s' ->
  real_eq (real_db_breaking s s')
          (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                     (real_mult (real_transition s s')
                                (real_abs (real_plus (real_kv_boltzmann_factor s)
                                                     (real_opp (real_kv_boltzmann_factor s')))))).
Proof.
  intros s s' Hs Hs'.
  pose proof (real_db_breaking_kept_abs s s' Hs Hs') as Ha.
  (* 内部：plus (mult (b s) T) (opp (mult (b s') T')) == mult T (abs (b s − b s')) 的 |·| *)
  assert (Hinner : real_eq
    (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                         (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))
    (real_mult (real_transition s s')
               (real_abs (real_plus (real_kv_boltzmann_factor s)
                                    (real_opp (real_kv_boltzmann_factor s')))))).
  {
    (* 第一步：T' == T（sym 接口）替换第二项 *)
    assert (Ht : real_eq (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))
                         (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))).
    {
      apply (RealSetoid.real_eq_mult_compat
               (real_kv_boltzmann_factor s') (real_transition s' s)
               (real_kv_boltzmann_factor s') (real_transition s s')
               (real_eq_refl _) (real_transition_sym s' s)).
    }
    assert (Hw2 : real_eq
      (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                 (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))
      (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                 (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))))).
    {
      apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
               (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))
               (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
               (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s s')))
               (real_eq_refl _)
               (RealSetoid.real_eq_opp_compat
                  (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))
                  (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))
                  Ht)).
    }
    (* 第二步：右提公因子（工具 C） *)
    assert (Hw3 : real_eq
      (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                 (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))))
      (real_mult (real_plus (real_kv_boltzmann_factor s)
                            (real_opp (real_kv_boltzmann_factor s')))
                 (real_transition s s'))).
    {
      apply (real_mult_minus_r (real_kv_boltzmann_factor s) (real_kv_boltzmann_factor s')
                               (real_transition s s')).
    }
    (* 第三步：|mult Z T| == |Z|·T（abs_mult_req + |T|==T 非负） *)
    assert (Habs2 : real_eq
      (real_abs (real_mult (real_plus (real_kv_boltzmann_factor s)
                                      (real_opp (real_kv_boltzmann_factor s')))
                           (real_transition s s')))
      (real_mult (real_abs (real_plus (real_kv_boltzmann_factor s)
                                      (real_opp (real_kv_boltzmann_factor s'))))
                 (real_transition s s'))).
    {
      apply (real_eq_trans
               _ (real_mult (real_abs (real_plus (real_kv_boltzmann_factor s)
                                                 (real_opp (real_kv_boltzmann_factor s'))))
                            (real_abs (real_transition s s'))) _).
      - apply (real_abs_mult_req (real_plus (real_kv_boltzmann_factor s)
                                            (real_opp (real_kv_boltzmann_factor s')))
                                 (real_transition s s')).
      - apply (RealSetoid.real_eq_mult_compat
                 (real_abs (real_plus (real_kv_boltzmann_factor s)
                                      (real_opp (real_kv_boltzmann_factor s'))))
                 (real_abs (real_transition s s'))
                 (real_abs (real_plus (real_kv_boltzmann_factor s)
                                      (real_opp (real_kv_boltzmann_factor s'))))
                 (real_transition s s')
                 (real_eq_refl _) (real_abs_nonneg_req (real_transition s s')
                                                       (real_transition_nonneg s s'))).
    }
    (* 第四步：mult |Z| T == mult T |Z|（comm） *)
    assert (Hcomm : real_eq
      (real_mult (real_abs (real_plus (real_kv_boltzmann_factor s)
                                      (real_opp (real_kv_boltzmann_factor s'))))
                 (real_transition s s'))
      (real_mult (real_transition s s')
                 (real_abs (real_plus (real_kv_boltzmann_factor s)
                                      (real_opp (real_kv_boltzmann_factor s')))))).
    {
      apply (real_mult_comm (real_abs (real_plus (real_kv_boltzmann_factor s)
                                                 (real_opp (real_kv_boltzmann_factor s'))))
                            (real_transition s s')).
    }
    (* 组装：|W| == |W2| == |mult Z T| == |Z|·T == T·|Z| *)
    apply (real_eq_trans _ (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                                 (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))))) _).
    - apply (real_abs_eq_compat
               (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                          (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s))))
               (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                          (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))))
               Hw2).
    - apply (real_eq_trans
               _ (real_abs (real_mult (real_plus (real_kv_boltzmann_factor s)
                                                 (real_opp (real_kv_boltzmann_factor s')))
                                      (real_transition s s'))) _).
      + apply (real_abs_eq_compat
                 (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                            (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s s'))))
                 (real_mult (real_plus (real_kv_boltzmann_factor s)
                                       (real_opp (real_kv_boltzmann_factor s')))
                            (real_transition s s'))
                 Hw3).
      + apply (real_eq_trans
                 _ (real_mult (real_abs (real_plus (real_kv_boltzmann_factor s)
                                                   (real_opp (real_kv_boltzmann_factor s'))))
                              (real_transition s s')) _).
        * exact Habs2.
        * exact Hcomm.
  }
  (* 最终：inv·|W| == inv·(T·|Z|)（mult wd） *)
  apply (real_eq_trans
           _ (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                        (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                             (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))) _).
  - exact Ha.
  - apply (RealSetoid.real_eq_mult_compat
             (real_inv_pos real_evicted_partition real_evicted_partition_pos)
             (real_abs (real_plus (real_mult (real_kv_boltzmann_factor s) (real_transition s s'))
                                  (real_opp (real_mult (real_kv_boltzmann_factor s') (real_transition s' s)))))
             (real_inv_pos real_evicted_partition real_evicted_partition_pos)
             (real_mult (real_transition s s')
                        (real_abs (real_plus (real_kv_boltzmann_factor s)
                                             (real_opp (real_kv_boltzmann_factor s')))))
             (real_eq_refl _) Hinner).
Qed.

(* ============================================================ *)
(* B3：能量 Lipschitz / 温度进入 Boltzmann 因子——分析组装骨干 *)
(* ============================================================ *)


(* 工具 E：real_le 左侧等价替换（Or 分解：lt 分支 real_eq_lt_lt / eq 分支 trans） *)
Lemma real_le_eq_l : forall (x y z : Real),
  real_eq x y -> real_le y z -> real_le x z.
Proof.
  intros x y z Hxy Hyz.
  destruct Hyz as [Hlt | Heq].
  - left. exact (real_eq_lt_lt x y z Hxy Hlt).
  - right. apply (real_eq_trans x y z Hxy Heq).
Qed.

(* 工具 F：e^x 非严格单调（Or 分解：lt 分支 cauchy_real_exp_mono / eq 分支 wd） *)
Lemma real_exp_le_mono : forall (x y : Real),
  real_le x y -> real_le (cauchy_real_exp x) (cauchy_real_exp y).
Proof.
  intros x y Hxy.
  destruct Hxy as [Hlt | Heq].
  - left. apply (cauchy_real_exp_mono x y Hlt).
  - right. apply (cauchy_real_exp_wd x y Heq).
Qed.

(* B3a：|u − v| ≤ (L/D)·metric(s,s')（u := e(s)/D；Lipschitz 缩放传递）
   链：u−v == invD·(e(s)−e(s'))（左提公因子）→ |·| == invD·|e−e'|
       （abs_mult + abs_pos invD）→ ≤ invD·(L·metric)（lipschitz + 乘保序）
       == (invD·L)·metric（assoc） *)
Lemma real_energy_lipschitz_scaled : forall s s' : S,
  real_le (real_abs (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                               (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s')))))
          (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')).
Proof.
  intros s s'.
  (* 1. W == invD·(e s − e s')（左提公因子） *)
  assert (Hw : real_eq
    (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
               (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s'))))
    (real_mult (real_inv_pos D D_pos)
               (real_plus (real_energy s) (real_opp (real_energy s'))))).
  { apply (real_mult_minus_l (real_inv_pos D D_pos) (real_energy s) (real_energy s')). }
  (* 2. |W| == invD·|e s − e s'| *)
  assert (Habs : real_eq
    (real_abs (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                         (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s')))))
    (real_mult (real_inv_pos D D_pos)
               (real_abs (real_plus (real_energy s) (real_opp (real_energy s')))))).
  {
    apply (real_eq_trans
             _ (real_abs (real_mult (real_inv_pos D D_pos)
                                    (real_plus (real_energy s) (real_opp (real_energy s'))))) _).
    - apply (real_abs_eq_compat
               (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                          (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s'))))
               (real_mult (real_inv_pos D D_pos)
                          (real_plus (real_energy s) (real_opp (real_energy s'))))
               Hw).
    - (* |invD·X| == |invD|·|X| == invD·|X| *)
      apply (real_eq_trans
               _ (real_mult (real_abs (real_inv_pos D D_pos))
                            (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))) _).
      + apply (real_abs_mult_req (real_inv_pos D D_pos)
                                 (real_plus (real_energy s) (real_opp (real_energy s')))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_abs (real_inv_pos D D_pos))
                 (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                 (real_inv_pos D D_pos)
                 (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                 (real_abs_pos_req (real_inv_pos D D_pos) (real_inv_pos_pos D D_pos))
                 (real_eq_refl _)).
  }
  (* 3. invD·|e−e'| ≤ invD·(L·metric)（乘保序：invD ≥ 0 + lipschitz） *)
  assert (Hle : real_le
    (real_mult (real_inv_pos D D_pos)
               (real_abs (real_plus (real_energy s) (real_opp (real_energy s')))))
    (real_mult (real_inv_pos D D_pos) (real_mult L (real_metric s s')))).
  {
    apply (real_le_mult_compat_r (real_inv_pos D D_pos)
                                 (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                                 (real_mult L (real_metric s s'))).
    - apply (RealSetoid.real_lt_le_iff_req real_zero (real_inv_pos D D_pos)).
      left. apply (real_inv_pos_pos D D_pos).
    - exact (real_energy_lipschitz s s').
  }
  (* 4. 组装：|W| == invD·|e−e'| ≤ invD·(L·metric) == (invD·L)·metric *)
  assert (Hr : real_eq (real_mult (real_inv_pos D D_pos) (real_mult L (real_metric s s')))
                       (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))).
  { apply (real_mult_assoc (real_inv_pos D D_pos) L (real_metric s s')). }
  apply (real_le_eq_l
           (real_abs (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                                (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s')))))
           (real_mult (real_inv_pos D D_pos)
                      (real_abs (real_plus (real_energy s) (real_opp (real_energy s')))))
           (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))).
  - exact Habs.
  - exact (real_le_eq_r
             (real_mult (real_inv_pos D D_pos)
                        (real_abs (real_plus (real_energy s) (real_opp (real_energy s')))))
             (real_mult (real_inv_pos D D_pos) (real_mult L (real_metric s s')))
             (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
             Hle Hr).
Qed.

(* B3b：b(s') == e^{−e(s')/D} ≤ e^{E_max/D}（能量下界 + exp_neg 单调）
   链：−E_max ≤ e(s') → invD·(−E_max) ≤ invD·e(s')（乘保序）
       → exp_neg 递减：e^{−v} ≤ e^{−(−E_max/D)} == e^{E_max/D} *)
Lemma real_boltzmann_upper : forall s' : S,
  real_le (real_kv_boltzmann_factor s')
          (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)).
Proof.
  intro s'.
  (* 1. invD·(−E_max) ≤ invD·e(s') *)
  assert (Hle : real_le (real_mult (real_inv_pos D D_pos) (real_opp E_max))
                        (real_mult (real_inv_pos D D_pos) (real_energy s'))).
  {
    apply (real_le_mult_compat_r (real_inv_pos D D_pos)
                                 (real_opp E_max) (real_energy s')).
    - apply (RealSetoid.real_lt_le_iff_req real_zero (real_inv_pos D D_pos)).
      left. apply (real_inv_pos_pos D D_pos).
    - exact (real_energy_lower s').
  }
  (* 2. exp_neg 递减：e^{−v} ≤ e^{−(−E_max/D)}（v := invD·e(s')，a := invD·(−E_max)） *)
  assert (Hdec : real_le (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_energy s')))
                         (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_opp E_max)))).
  { apply (real_exp_neg_le_decr (real_mult (real_inv_pos D D_pos) (real_opp E_max))
                                (real_mult (real_inv_pos D D_pos) (real_energy s'))).
    exact Hle. }
  (* 3. e^{−(−E_max/D)} == e^{E_max/D}：−(invD·(−E_max)) == invD·E_max *)
  assert (Heq : real_eq
    (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_opp E_max)))
    (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))).
  {
    unfold real_exp_neg.
    apply cauchy_real_exp_wd.
    apply (real_eq_trans _ (real_opp (real_opp (real_mult (real_inv_pos D D_pos) E_max))) _).
    - apply (RealSetoid.real_eq_opp_compat
               (real_mult (real_inv_pos D D_pos) (real_opp E_max))
               (real_opp (real_mult (real_inv_pos D D_pos) E_max))).
      apply (real_mult_opp_l (real_inv_pos D D_pos) E_max).
    - apply (real_opp_opp (real_mult (real_inv_pos D D_pos) E_max)).
  }
  (* 4. 组装：b s' == e^{−v} ≤ e^{−(−E_max/D)} == e^{E_max/D} *)
  unfold real_kv_boltzmann_factor.
  apply (real_le_eq_r
           (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_energy s')))
           (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_opp E_max)))
           (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
           Hdec Heq).
Qed.

(* B3c：乘积界——|u−v|·e^{|u−v|} ≤ Ulips·e^{Ulips} + eps'
   （real_abs_prod_le_eps + B3a + exp 单调 + abs 幂等替换） *)
Lemma real_abs_diff_prod_bound : forall (s s' : S) (eps' : Real),
  real_lt real_zero eps' ->
  real_le (real_mult (real_abs (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                                          (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s')))))
                     (cauchy_real_exp (real_abs (real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                                                           (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s')))))))
          (real_plus (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))))
                     eps').
Proof.
  intros s s' eps' Hep'.
  set (a := real_plus (real_mult (real_inv_pos D D_pos) (real_energy s))
                      (real_opp (real_mult (real_inv_pos D D_pos) (real_energy s')))).
  set (Ulips := real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')).
  (* 前提 1：le (abs a) Ulips（B3a） *)
  assert (H1 : real_le (real_abs a) Ulips).
  { unfold a, Ulips. exact (real_energy_lipschitz_scaled s s'). }
  (* 前提 2：le (abs (e^{|u−v|})) (e^{Ulips})（abs 幂等 + exp 单调） *)
  assert (H2 : real_le (real_abs (cauchy_real_exp (real_abs a)))
                       (cauchy_real_exp Ulips)).
  {
    apply (real_le_eq_l (real_abs (cauchy_real_exp (real_abs a)))
                        (cauchy_real_exp (real_abs a))
                        (cauchy_real_exp Ulips)).
    - apply (real_abs_pos_req (cauchy_real_exp (real_abs a))
                              (cauchy_real_exp_pos (real_abs a))).
    - apply (real_exp_le_mono (real_abs a) Ulips).
      exact H1.
  }
  (* real_abs_prod_le_eps 结论 + 左侧 abs 幂等替换 *)
  pose proof (real_abs_prod_le_eps a (cauchy_real_exp (real_abs a))
                                   Ulips (cauchy_real_exp Ulips) eps' Hep' H1 H2) as Hp.
  (* Hp : le (mult (abs a)(abs (e^{abs a}))) (plus (mult Ulips (e^{Ulips})) eps')
     左侧：abs (e^{abs a}) == e^{abs a} *)
  assert (Hae : real_eq (real_abs (cauchy_real_exp (real_abs a)))
                        (cauchy_real_exp (real_abs a))).
  { apply (real_abs_pos_req (cauchy_real_exp (real_abs a))
                            (cauchy_real_exp_pos (real_abs a))). }
  assert (Hl : real_eq (real_mult (real_abs a) (real_abs (cauchy_real_exp (real_abs a))))
                       (real_mult (real_abs a) (cauchy_real_exp (real_abs a)))).
  {
    apply (RealSetoid.real_eq_mult_compat (real_abs a) (real_abs (cauchy_real_exp (real_abs a)))
                                          (real_abs a) (cauchy_real_exp (real_abs a))
                                          (real_eq_refl _) Hae).
  }
  apply (real_le_eq_l
           (real_mult (real_abs a) (cauchy_real_exp (real_abs a)))
           (real_mult (real_abs a) (real_abs (cauchy_real_exp (real_abs a))))
           (real_plus (real_mult Ulips (cauchy_real_exp Ulips)) eps')).
  - apply real_eq_sym. exact Hl.
  - (* 目标形态换回 a/Ulips 展开：unfold 后与 Hp 同项 *)
    unfold a, Ulips.
    exact Hp.
Qed.


(* B3 最终：|b(s) − b(s')| ≤ e^{E_max/D}·((L/D)·metric·e^{(L/D)·metric}) + e^{E_max/D}·eps + eps'
   组装：P1（exp_neg 差界）→ distrib 展开 → 第一项重组 + real_abs_prod_le_eps
         （e^{−v}·e^{|duv|} ≤ Emax_exp·e^{Ulips}：strict 乘 + 单调 ×2）
         → 第二项 e^{−v}·eps ≤ Emax_exp·eps（strict 乘）
         → 加法保序 + RHS 重排 *)
Lemma real_boltzmann_diff_bound : forall (s s' : S) (eps eps' : Real),
  real_lt real_zero eps -> real_lt real_zero eps' ->
  real_le (real_abs (real_plus (real_kv_boltzmann_factor s) (real_opp (real_kv_boltzmann_factor s'))))
          (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                           (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                     (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps')).
Proof.
  intros s s' eps eps' Hep Hep'.
  set (u := real_mult (real_inv_pos D D_pos) (real_energy s)).
  set (v := real_mult (real_inv_pos D D_pos) (real_energy s')).
  set (duv := real_plus u (real_opp v)).
  set (Ulips := real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')).
  set (Emax_exp := cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)).
  (* P1：|e^{−u} − e^{−v}| ≤ e^{−v}·(|duv|·e^{|duv|} + eps) *)
  pose proof (real_exp_neg_diff_bound u v eps Hep) as Hp1.
  (* 1. distrib 展开 P1 RHS *)
  assert (Hexp : real_eq
    (real_mult (real_exp_neg v)
               (real_plus (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))) eps))
    (real_plus (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
               (real_mult (real_exp_neg v) eps))).
  { apply (real_distrib (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))) eps). }
  assert (Hle1 : real_le
    (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
    (real_plus (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
               (real_mult (real_exp_neg v) eps))).
  { apply (real_le_eq_r _ _ _ Hp1 Hexp). }
  (* 2. 第一项重组：e^{−v}·(|duv|·e^{|duv|}) == |duv|·(e^{−v}·e^{|duv|}) *)
  assert (Heq1 : real_eq
    (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
    (real_mult (real_abs duv) (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))).
  {
    apply (real_eq_trans _ (real_mult (real_mult (real_exp_neg v) (real_abs duv))
                                      (cauchy_real_exp (real_abs duv))) _).
    - apply (real_mult_assoc (real_exp_neg v) (real_abs duv) (cauchy_real_exp (real_abs duv))).
    - apply (real_eq_trans _ (real_mult (real_mult (real_abs duv) (real_exp_neg v))
                                        (cauchy_real_exp (real_abs duv))) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_exp_neg v) (real_abs duv))
                 (cauchy_real_exp (real_abs duv))
                 (real_mult (real_abs duv) (real_exp_neg v))
                 (cauchy_real_exp (real_abs duv))
                 (real_mult_comm (real_exp_neg v) (real_abs duv)) (real_eq_refl _)).
      + apply real_eq_sym.
        apply (real_mult_assoc (real_abs duv) (real_exp_neg v) (cauchy_real_exp (real_abs duv))).
  }
  (* 3. e^{−v} ≤ e^{E_max/D}（real_boltzmann_upper） *)
  assert (HleEv : real_le (real_exp_neg v) Emax_exp).
  { unfold v, Emax_exp. exact (real_boltzmann_upper s'). }
  (* 4. 第二因子：e^{|duv|} ≤ e^{Ulips}（B3a + exp 单调） *)
  assert (HleUl : real_le (cauchy_real_exp (real_abs duv)) (cauchy_real_exp Ulips)).
  {
    apply (real_exp_le_mono (real_abs duv) Ulips).
    unfold duv, u, v, Ulips.
    exact (real_energy_lipschitz_scaled s s').
  }
  (* 5. e^{−v}·e^{|duv|} ≤ Emax_exp·e^{Ulips}：两层乘保序 *)
  assert (Hmm1 : real_le
    (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))
    (real_mult Emax_exp (cauchy_real_exp (real_abs duv)))).
  {
    apply (real_le_mult_compat (real_exp_neg v) Emax_exp (cauchy_real_exp (real_abs duv))).
    - apply (cauchy_real_exp_pos (real_abs duv)).
    - exact HleEv.
  }
  assert (Hmm2 : real_le
    (real_mult Emax_exp (cauchy_real_exp (real_abs duv)))
    (real_mult Emax_exp (cauchy_real_exp Ulips))).
  {
    apply (real_le_mult_compat_r Emax_exp (cauchy_real_exp (real_abs duv)) (cauchy_real_exp Ulips)).
    - apply (RealSetoid.real_lt_le_iff_req real_zero Emax_exp).
      left. unfold Emax_exp. apply (cauchy_real_exp_pos (real_mult (real_inv_pos D D_pos) E_max)).
    - exact HleUl.
  }
  assert (Hmm3 : real_le
    (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))
    (real_mult Emax_exp (cauchy_real_exp Ulips))).
  { apply (real_le_trans _ (real_mult Emax_exp (cauchy_real_exp (real_abs duv))) _).
    - exact Hmm1.
    - exact Hmm2. }
  (* 6. real_abs_prod_le_eps：|duv|·(e^{−v}·e^{|duv|}) ≤ Ulips·(Emax_exp·e^{Ulips}) + eps' *)
  assert (HposE : real_lt real_zero
    (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))).
  { apply (real_mult_pos_compat (real_exp_neg v) (cauchy_real_exp (real_abs duv))).
    - apply (real_exp_neg_pos v).
    - apply (cauchy_real_exp_pos (real_abs duv)). }
  assert (Hae2 : real_eq
    (real_abs (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
    (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))).
  { apply (real_abs_pos_req (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))) HposE). }
  assert (Hprem2 : real_le
    (real_abs (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
    (real_mult Emax_exp (cauchy_real_exp Ulips))).
  {
    apply (real_le_eq_l (real_abs (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
                        (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))
                        (real_mult Emax_exp (cauchy_real_exp Ulips))
                        Hae2 Hmm3).
  }
  assert (HleUlips1 : real_le (real_abs duv) Ulips).
  { unfold duv, u, v, Ulips. exact (real_energy_lipschitz_scaled s s'). }
  pose proof (real_abs_prod_le_eps duv (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))
                                   Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))
                                   eps' Hep' HleUlips1 Hprem2) as Hprod.
  (* 左侧替换：mult |duv| (abs (e^{−v}·e^{|duv|})) == mult |duv| (e^{−v}·e^{|duv|}) *)
  assert (Hl2 : real_eq
    (real_mult (real_abs duv) (real_abs (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))))
    (real_mult (real_abs duv) (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))).
  {
    apply (RealSetoid.real_eq_mult_compat (real_abs duv)
                                          (real_abs (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
                                          (real_abs duv)
                                          (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))
                                          (real_eq_refl _) Hae2).
  }
  assert (Hbig1 : real_le
    (real_mult (real_abs duv) (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
    (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')).
  {
    apply (real_le_eq_l (real_mult (real_abs duv) (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
                        (real_mult (real_abs duv) (real_abs (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv)))))
                        (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')).
    - apply real_eq_sym. exact Hl2.
    - exact Hprod.
  }
  (* 组装第一项：e^{−v}·A ≤ Ulips·(Emax_exp·e^{Ulips}) + eps' *)
  assert (Hbig1a : real_le
    (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
    (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')).
  {
    apply (real_le_eq_l
             (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
             (real_mult (real_abs duv) (real_mult (real_exp_neg v) (cauchy_real_exp (real_abs duv))))
             (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')
             Heq1 Hbig1).
  }
  (* 7. 第二项：e^{−v}·eps ≤ Emax_exp·eps *)
  assert (Hbig2 : real_le (real_mult (real_exp_neg v) eps) (real_mult Emax_exp eps)).
  {
    apply (real_le_mult_compat (real_exp_neg v) Emax_exp eps).
    - exact Hep.
    - exact HleEv.
  }
  (* 8. 加法保序 *)
  assert (Hsum : real_le
    (real_plus (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
               (real_mult (real_exp_neg v) eps))
    (real_plus (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')
               (real_mult Emax_exp eps))).
  { apply (real_le_plus_compat
             (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
             (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')
             (real_mult (real_exp_neg v) eps)
             (real_mult Emax_exp eps)
             Hbig1a Hbig2). }
  (* 9. RHS 重排为 Emax_exp·(Ulips·e^{Ulips}) + (Emax_exp·eps + eps') *)
  assert (Hr1 : real_eq
    (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
    (real_mult Emax_exp (real_mult Ulips (cauchy_real_exp Ulips)))).
  {
    apply (real_eq_trans _ (real_mult (real_mult Ulips Emax_exp) (cauchy_real_exp Ulips)) _).
    - apply (real_mult_assoc Ulips Emax_exp (cauchy_real_exp Ulips)).
    - apply (real_eq_trans _ (real_mult (real_mult Emax_exp Ulips) (cauchy_real_exp Ulips)) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult Ulips Emax_exp)
                 (cauchy_real_exp Ulips)
                 (real_mult Emax_exp Ulips)
                 (cauchy_real_exp Ulips)
                 (real_mult_comm Ulips Emax_exp) (real_eq_refl _)).
      + apply real_eq_sym.
        apply (real_mult_assoc Emax_exp Ulips (cauchy_real_exp Ulips)).
  }
  assert (Hr2 : real_eq
    (real_plus (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips))) eps')
               (real_mult Emax_exp eps))
    (real_plus (real_mult Emax_exp (real_mult Ulips (cauchy_real_exp Ulips)))
               (real_plus (real_mult Emax_exp eps) eps'))).
  {
    apply (real_eq_trans
             _ (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
                          (real_plus (real_mult Emax_exp eps) eps')) _).
    - apply (real_eq_trans
               _ (real_plus (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
                            (real_plus eps' (real_mult Emax_exp eps))) _).
      + apply real_eq_sym.
        apply (real_plus_assoc (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
                               eps' (real_mult Emax_exp eps)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
                 (real_plus eps' (real_mult Emax_exp eps))
                 (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
                 (real_plus (real_mult Emax_exp eps) eps')
                 (real_eq_refl _) (real_plus_comm eps' (real_mult Emax_exp eps))).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult Ulips (real_mult Emax_exp (cauchy_real_exp Ulips)))
               (real_plus (real_mult Emax_exp eps) eps')
               (real_mult Emax_exp (real_mult Ulips (cauchy_real_exp Ulips)))
               (real_plus (real_mult Emax_exp eps) eps')
               Hr1 (real_eq_refl _)).
  }
  (* 10. 组装最终 *)
  assert (Hsum2 : real_le
    (real_plus (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
               (real_mult (real_exp_neg v) eps))
    (real_plus (real_mult Emax_exp (real_mult Ulips (cauchy_real_exp Ulips)))
               (real_plus (real_mult Emax_exp eps) eps'))).
  { apply (real_le_eq_r _ _ _ Hsum Hr2). }
  (* 目标：unfold 后经 trans + 左侧替换 *)
  unfold real_kv_boltzmann_factor.
  apply (real_le_trans
           (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
           (real_plus (real_mult (real_exp_neg v) (real_mult (real_abs duv) (cauchy_real_exp (real_abs duv))))
                      (real_mult (real_exp_neg v) eps))
           (real_plus (real_mult Emax_exp (real_mult Ulips (cauchy_real_exp Ulips)))
                      (real_plus (real_mult Emax_exp eps) eps'))).
  - exact Hle1.
  - unfold duv, u, v, Ulips, Emax_exp.
    exact Hsum2.
Qed.

(* B4 最终定理：保留对 (s,s') 的 db_breaking 温度-Lipschitz 定量界
   db(s,s') ≤ inv Z_ev · T(s,s') · [ e^{E_max/D}·(L/D)·metric·e^{(L/D)·metric}
                                    + e^{E_max/D}·eps + eps' ]
   组装：B2c 结构（db == invZ·T·|b−b'|）→ B3（|b−b'| 界）→ 两层乘保序
         （T ≥ 0 非负接口 + invZ > 0） *)
Theorem real_db_breaking_bound_eps : forall (s s' : S) (eps eps' : Real),
  keep s -> keep s' ->
  real_lt real_zero eps -> real_lt real_zero eps' ->
  real_le (real_db_breaking s s')
          (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                     (real_mult (real_transition s s')
                                (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                                      (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                                                 (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                                           (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps')))).
Proof.
  intros s s' eps eps' Hs Hs' Hep Hep'.
  (* 1. 结构：db == invZ·T·|b(s) − b(s')|（B2c） *)
  pose proof (real_db_breaking_kept_final s s' Hs Hs') as Hkeq.
  assert (Hk : real_le (real_db_breaking s s')
                       (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                                  (real_mult (real_transition s s')
                                             (real_abs (real_plus (real_kv_boltzmann_factor s)
                                                                  (real_opp (real_kv_boltzmann_factor s'))))))).
  { apply (RealSetoid.real_eq_le _ _ Hkeq). }
  (* 2. |b−b'| 定量界（B3） *)
  pose proof (real_boltzmann_diff_bound s s' eps eps' Hep Hep') as Hbd.
  (* 3. 内层：T·|b−b'| ≤ T·RHS3（T ≥ 0） *)
  assert (Hin : real_le
    (real_mult (real_transition s s')
               (real_abs (real_plus (real_kv_boltzmann_factor s) (real_opp (real_kv_boltzmann_factor s')))))
    (real_mult (real_transition s s')
               (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                     (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                                (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                          (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps')))).
  {
    apply (real_le_mult_compat_r (real_transition s s')
                                 (real_abs (real_plus (real_kv_boltzmann_factor s) (real_opp (real_kv_boltzmann_factor s'))))
                                 (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                                       (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                                                  (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                                            (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps'))).
    - exact (real_transition_nonneg s s').
    - exact Hbd.
  }
  (* 4. 外层：invZ·(T·|b−b'|) ≤ invZ·(T·RHS3)（invZ > 0） *)
  assert (Hout : real_le
    (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
               (real_mult (real_transition s s')
                          (real_abs (real_plus (real_kv_boltzmann_factor s) (real_opp (real_kv_boltzmann_factor s'))))))
    (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
               (real_mult (real_transition s s')
                          (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                                (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                                           (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                                     (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps'))))).
  {
    apply (real_le_mult_compat_r
             (real_inv_pos real_evicted_partition real_evicted_partition_pos)
             (real_mult (real_transition s s')
                        (real_abs (real_plus (real_kv_boltzmann_factor s) (real_opp (real_kv_boltzmann_factor s')))))
             (real_mult (real_transition s s')
                        (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                              (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                                         (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                                   (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps')))).
    - apply (RealSetoid.real_lt_le_iff_req real_zero
                                           (real_inv_pos real_evicted_partition real_evicted_partition_pos)).
      left. apply (real_inv_pos_pos real_evicted_partition real_evicted_partition_pos).
    - exact Hin.
  }
  (* 5. trans 组装 *)
  apply (real_le_trans
           (real_db_breaking s s')
           (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                      (real_mult (real_transition s s')
                                 (real_abs (real_plus (real_kv_boltzmann_factor s)
                                                      (real_opp (real_kv_boltzmann_factor s'))))))
           (real_mult (real_inv_pos real_evicted_partition real_evicted_partition_pos)
                      (real_mult (real_transition s s')
                                 (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                                       (real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                                                                  (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))
                                            (real_plus (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) eps) eps'))))).
  - exact Hk.
  - exact Hout.
Qed.
End RealKVQuantMain.


(* ============================================================ *)
(* 项 5：DPO 损失 log-ratio 凸性（softplus 凸）——     *)
(* 并入（检验 _dbg_dpo_conv.v 平移）                             *)
(*   real_dpo_logit：ℓ(x) := −log σ(x)（dpo 单样本 logit 损失）  *)
(*   A1 real_softplus_sigmoid_eq：ℓ(x) == log(1+e^{−x})          *)
(*     （损失 ↔ softplus 形态连接；inv 对合 + log_inv_one_inv）   *)
(*   A2 real_one_minus_sigmoid_pos：1 − σ(x) > 0                 *)
(*   A3 real_sigmoid_deriv_mass_pos：σ(x)(1−σ(x)) > 0            *)
(*     （−log σ 二阶导 σ(1−σ) 的构造性正性证据）                 *)
(*   A4 real_dpo_logit_loss_decr：x < y ⟹ ℓ(y) < ℓ(x)            *)
(*     （损失随偏好 logit 严格递减——收敛的单调前提）             *)
(* 纪律：纯构造性 / Set 层 / 零 承认 / 零经典；全部非平凡组装。 *)
(* ============================================================ *)
(* ---- dpo logit 损失：ℓ(x) := −log σ(x) ---- *)
Definition real_dpo_logit (x : Real) : Real :=
  real_opp (real_log (real_sigmoid x) (real_sigmoid_pos x)).

(* ---- 工具：inv 对合 inv(inv z) == z
   链：b == 1·b == (z·a)·b == z·(a·b) == z·1 == z
   （z·a == 1 由 inv_pos_correct；a·b == 1 由 inv_pos_correct a） ---- *)
Lemma real_inv_pos_inv_gen : forall (z : Real) (Hz : real_lt real_zero z)
  (Hz' : real_lt real_zero (real_inv_pos z Hz)),
  real_eq (real_inv_pos (real_inv_pos z Hz) Hz') z.
Proof.
  intros z Hz Hz'.
  set (a := real_inv_pos z Hz).
  set (b := real_inv_pos a Hz').
  assert (Ha : real_lt real_zero a) by (unfold a; apply (real_inv_pos_pos z Hz)).
  assert (Hza : real_eq (real_mult z a) real_one).
  { unfold a. apply (real_inv_pos_correct z Hz). }
  assert (Hab : real_eq (real_mult a b) real_one).
  { apply (real_inv_pos_correct a Hz'). }
  apply (real_eq_trans _ (real_mult real_one b) _).
  - apply (real_eq_trans _ (real_mult b real_one) _).
    + apply real_eq_sym. apply (real_mult_one b).
    + apply real_eq_sym. apply (real_mult_comm real_one b).
  - apply (real_eq_trans _ (real_mult (real_mult z a) b) _).
    + apply (RealSetoid.real_eq_mult_compat real_one b (real_mult z a) b
                                            (real_eq_sym (real_mult z a) real_one Hza)
                                            (real_eq_refl b)).
    + apply (real_eq_trans _ (real_mult z (real_mult a b)) _).
      * apply real_eq_sym. apply (real_mult_assoc z a b).
      * apply (real_eq_trans _ (real_mult z real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat z (real_mult a b) z real_one
                                                (real_eq_refl z) Hab).
        -- apply (real_mult_one z).
Qed.

(* ---- A2：1 − σ(x) > 0（σ < 1 经 real_lt_opp_plus） ---- *)
Lemma real_one_minus_sigmoid_pos : forall x : Real,
  real_lt real_zero (real_plus real_one (real_opp (real_sigmoid x))).
Proof.  intro x.
  exact (real_lt_opp_plus (real_sigmoid x) real_one (real_sigmoid_lt_one x)).
Qed.

(* ---- A3：σ(x)·(1−σ(x)) > 0（−log σ 二阶导的正性证据） ---- *)
Lemma real_sigmoid_deriv_mass_pos : forall x : Real,
  real_lt real_zero (real_mult (real_sigmoid x)
                               (real_plus real_one (real_opp (real_sigmoid x)))).
Proof.
  intro x.
  exact (real_mult_pos_compat (real_sigmoid x)
    (real_plus real_one (real_opp (real_sigmoid x)))
    (real_sigmoid_pos x) (real_one_minus_sigmoid_pos x)).
Qed.

(* ---- A1：−log σ(x) == log(1+e^{−x})（dpo 损失 ↔ softplus 连接） ---- *)
Lemma real_softplus_sigmoid_eq : forall x : Real,
  real_eq (real_dpo_logit x)
          (real_log (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x)).
Proof.
  intro x.
  unfold real_dpo_logit.
  (* −log σ == log(inv σ)（real_log_inv_one_inv 反向） *)
  assert (H1 : real_eq (real_opp (real_log (real_sigmoid x) (real_sigmoid_pos x)))
                       (real_log (real_inv_pos (real_sigmoid x) (real_sigmoid_pos x))
                                 (real_inv_pos_pos (real_sigmoid x) (real_sigmoid_pos x)))).
  { apply real_eq_sym.
    apply (real_log_inv_one_inv (real_sigmoid x) (real_sigmoid_pos x)
                                (real_inv_pos_pos (real_sigmoid x) (real_sigmoid_pos x))). }
  (* log wd：inv σ == 1 + e^{−x} *)
  assert (Hinv : real_eq
    (real_inv_pos (real_sigmoid x) (real_sigmoid_pos x))
    (real_plus real_one (real_exp_neg x))).
  { apply (real_inv_pos_inv_gen (real_plus real_one (real_exp_neg x))
                                (real_sigmoid_denom_pos x)
                                (real_sigmoid_pos x)). }
  assert (Hlog : real_eq
    (real_log (real_inv_pos (real_sigmoid x) (real_sigmoid_pos x))
              (real_inv_pos_pos (real_sigmoid x) (real_sigmoid_pos x)))
    (real_log (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x))).
  { apply (real_log_wd
             (real_inv_pos (real_sigmoid x) (real_sigmoid_pos x))
             (real_plus real_one (real_exp_neg x))
             (real_inv_pos_pos (real_sigmoid x) (real_sigmoid_pos x))
             (real_sigmoid_denom_pos x)
             Hinv). }
  apply (real_eq_trans _ _ _ H1 Hlog).
Qed.

(* ---- A4：dpo logit 损失严格递减：x < y ⟹ ℓ(y) < ℓ(x)
   （损失随偏好 logit 递增而下降——收敛的单调前提）
   链：x<y → σ x < σ y（sigmoid 严格增）→ log σ x < log σ y（log 严格增）
       → −log σ y < −log σ x（opp 反序） *)
Lemma real_dpo_logit_loss_decr : forall (x y : Real),
  real_lt x y -> real_lt (real_dpo_logit y) (real_dpo_logit x).
Proof.
  intros x y Hxy.
  unfold real_dpo_logit.
  (* log σ x < log σ y *)
  assert (Hlog : real_lt (real_log (real_sigmoid x) (real_sigmoid_pos x))
                         (real_log (real_sigmoid y) (real_sigmoid_pos y))).
  { apply (real_log_lt_mono (real_sigmoid x) (real_sigmoid y)
                            (real_sigmoid_pos x) (real_sigmoid_pos y)).
    exact (real_sigmoid_strict_inc x y Hxy). }
  (* −log σ y < −log σ x *)
  exact (real_opp_lt_compat (real_log (real_sigmoid x) (real_sigmoid_pos x))
                            (real_log (real_sigmoid y) (real_sigmoid_pos y))
                            Hlog).
Qed.

(* ============================================================ *)
(* SC-1：sin/cos 构造性级数（Q 层 + Real 层）                *)
(* ============================================================ *)


(* ---- 项与部分和 ---- *)
(* sin_term j x := (−1)^j · x^{2j+1}/(2j+1)! *)
Definition sin_term (j : nat) (x : Q) : Q :=
  q_pow (-1) j * (q_pow x (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).

(* cos_term j x := (−1)^j · x^{2j}/(2j)! *)
Definition cos_term (j : nat) (x : Q) : Q :=
  q_pow (-1) j * (q_pow x (2 * j) / q_fact (2 * j)).

(* sin_partial n x := Σ_{j=0}^{n} sin_term j x（exp_partial 惯例：含 j=n） *)
Fixpoint sin_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => sin_term 0%nat x
  | Datatypes.S m => sin_partial m x + sin_term (Datatypes.S m) x
  end.

(* cos_partial n x := Σ_{j=0}^{n} cos_term j x *)
Fixpoint cos_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => cos_term 0%nat x
  | Datatypes.S m => cos_partial m x + cos_term (Datatypes.S m) x
  end.

(* ---- 符号因子 ---- *)
Lemma sc_q_pow_one : forall j : nat, QeqT (q_pow 1 j) (1).
Proof.
  induction j as [| j IH]; simpl.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IH). ring.
Qed.

Lemma sc_q_abs_one : QeqT (Qabs 1) (1).
Proof. reflexivity. Qed.

Lemma sc_abs_sign : forall j : nat, QeqT (Qabs (q_pow (-1) j)) (1).
Proof.
  intro j.
  apply qeq_imp_qeqT.
  assert (HabsQ1 : Qabs (-1) == 1) by (unfold Qabs; simpl; reflexivity).
  rewrite (qeqT_imp_qeq _ _ (q_pow_abs (-1) j)).
  rewrite (qeqT_imp_qeq _ _ (q_pow_wd (Qabs (-1)) 1 j (qeq_imp_qeqT _ _ HabsQ1))).
  apply qeqT_imp_qeq. apply sc_q_pow_one.
Qed.

(* ---- 项的绝对值 == 绝对级数项 ---- *)
Lemma sc_abs_sin_term : forall (j : nat) (x : Q), QeqT (Qabs (sin_term j x)) (q_pow (Qabs x) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).
Proof.
  intros j x.
  apply qeq_imp_qeqT.
  unfold sin_term.
  rewrite Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (sc_abs_sign _)).
  rewrite (qeqT_imp_qeq _ _ (q_abs_pow_fact x (2 * j))).
  ring.
Qed.

Lemma sc_abs_cos_term : forall (j : nat) (x : Q), QeqT (Qabs (cos_term j x)) (q_pow (Qabs x) (2 * j) / q_fact (2 * j)).
Proof.
  intros j x.
  apply qeq_imp_qeqT.
  unfold cos_term.
  rewrite Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (sc_abs_sign _)).
  rewrite (qeqT_imp_qeq _ _ (q_abs_div _ _)).
  rewrite (qeqT_imp_qeq _ _ (q_pow_abs _ _)).
  rewrite (Qabs_pos (q_fact (2 * j)) (Qlt_le_weak 0 (q_fact (2 * j)) (QltT_to_Qlt 0 (q_fact (2 * j)) (q_fact_pos (2 * j))))).
  ring.
Qed.

(* ---- 尾和（指标 j ∈ [m, n)，guard 版，仿 exp_tail）---- *)
Fixpoint sin_tail (m : nat) (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => sin_tail m n' x + (if Nat.leb m n' then sin_term n' x else 0)
  end.

Fixpoint cos_tail (m : nat) (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => cos_tail m n' x + (if Nat.leb m n' then cos_term n' x else 0)
  end.

Fixpoint sin_tail_abs (m : nat) (n : nat) (A : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => sin_tail_abs m n' A + (if Nat.leb m n' then q_pow A (Datatypes.S (2 * n')) / q_fact (Datatypes.S (2 * n')) else 0)
  end.

Fixpoint cos_tail_abs (m : nat) (n : nat) (A : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => cos_tail_abs m n' A + (if Nat.leb m n' then q_pow A (2 * n') / q_fact (2 * n') else 0)
  end.

(* n ≤ m ⟹ 尾和为零 *)
Lemma sc_sin_tail_le_m : forall m n x, (n <= m)%nat ->QeqT (sin_tail m n x) (0).
Proof.
  intros m n x Hn. induction n as [| n IH]; simpl.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (IH Hn')). ring.
Qed.

Lemma sc_cos_tail_le_m : forall m n x, (n <= m)%nat ->QeqT (cos_tail m n x) (0).
Proof.
  intros m n x Hn. induction n as [| n IH]; simpl.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (IH Hn')). ring.
Qed.

Lemma sc_sin_tail_abs_le_m : forall m n A, (n <= m)%nat ->QeqT (sin_tail_abs m n A) (0).
Proof.
  intros m n A Hn. induction n as [| n IH]; simpl.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (IH Hn')). ring.
Qed.

Lemma sc_cos_tail_abs_le_m : forall m n A, (n <= m)%nat ->QeqT (cos_tail_abs m n A) (0).
Proof.
  intros m n A Hn. induction n as [| n IH]; simpl.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (IH Hn')). ring.
Qed.

(* ---- 差恒等式：m ≤ n ⟹ partial n − partial m == tail (S m) (S n) ---- *)
(* 先证 tail 归零引理（m = S n 情形） *)
Lemma sc_sin_tail_self : forall n x, QeqT (sin_tail (Datatypes.S n) (Datatypes.S n) x) (0).
Proof.
  intros n x.
  apply qeq_imp_qeqT.
  apply qeqT_imp_qeq. apply (sc_sin_tail_le_m (Datatypes.S n) (Datatypes.S n) x). lia.
Qed.

Lemma sc_cos_tail_self : forall n x, QeqT (cos_tail (Datatypes.S n) (Datatypes.S n) x) (0).
Proof.
  intros n x.
  apply qeq_imp_qeqT.
  apply qeqT_imp_qeq. apply (sc_cos_tail_le_m (Datatypes.S n) (Datatypes.S n) x). lia.
Qed.

Lemma sc_sin_diff_tail : forall m n x, (m <= n)%nat ->QeqT (sin_partial n x - sin_partial m x) (sin_tail (Datatypes.S m) (Datatypes.S n) x).
Proof.
  intros m n x Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - apply qeq_imp_qeqT. assert (Hm0 : (m = 0)%nat) by lia. subst m.
    rewrite (qeqT_imp_qeq _ _ (sc_sin_tail_self 0 x)). ring.
  - apply qeq_imp_qeqT. destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      change (sin_partial n x + sin_term (Datatypes.S n) x - sin_partial m x ==
              sin_tail (Datatypes.S m) (Datatypes.S n) x +
              (if Nat.leb (Datatypes.S m) (Datatypes.S n) then sin_term (Datatypes.S n) x else 0)).
      assert (Hring : sin_partial n x + sin_term (Datatypes.S n) x - sin_partial m x ==
                      (sin_partial n x - sin_partial m x) + sin_term (Datatypes.S n) x).
      { ring. }
      rewrite Hring.
      rewrite (qeqT_imp_qeq _ _ (IH E)).
      assert (Hg : Nat.leb (Datatypes.S m) (Datatypes.S n) = true) by (apply Nat.leb_le; lia).
      rewrite Hg. reflexivity.
    + apply Nat.leb_gt in E.
      assert (Hm : (m = Datatypes.S n)%nat) by lia. subst m.
      (* 左 = sin_partial (S n) x - sin_partial (S n) x == 0；右 = sin_tail (S(S n)) (S(S n)) x == 0 *)
      change (sin_partial n x + sin_term (Datatypes.S n) x -
              (sin_partial n x + sin_term (Datatypes.S n) x) ==
              sin_tail (Datatypes.S (Datatypes.S n)) (Datatypes.S (Datatypes.S n)) x).
      rewrite (qeqT_imp_qeq _ _ (sc_sin_tail_le_m (Datatypes.S (Datatypes.S n)) (Datatypes.S (Datatypes.S n)) x
                                (Nat.le_refl (Datatypes.S (Datatypes.S n))))).
      ring.
Qed.

Lemma sc_cos_diff_tail : forall m n x, (m <= n)%nat ->QeqT (cos_partial n x - cos_partial m x) (cos_tail (Datatypes.S m) (Datatypes.S n) x).
Proof.
  intros m n x Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - apply qeq_imp_qeqT. assert (Hm0 : (m = 0)%nat) by lia. subst m.
    rewrite (qeqT_imp_qeq _ _ (sc_cos_tail_self 0 x)). ring.
  - apply qeq_imp_qeqT. destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      change (cos_partial n x + cos_term (Datatypes.S n) x - cos_partial m x ==
              cos_tail (Datatypes.S m) (Datatypes.S n) x +
              (if Nat.leb (Datatypes.S m) (Datatypes.S n) then cos_term (Datatypes.S n) x else 0)).
      assert (Hring : cos_partial n x + cos_term (Datatypes.S n) x - cos_partial m x ==
                      (cos_partial n x - cos_partial m x) + cos_term (Datatypes.S n) x).
      { ring. }
      rewrite Hring.
      rewrite (qeqT_imp_qeq _ _ (IH E)).
      assert (Hg : Nat.leb (Datatypes.S m) (Datatypes.S n) = true) by (apply Nat.leb_le; lia).
      rewrite Hg. reflexivity.
    + apply Nat.leb_gt in E.
      assert (Hm : (m = Datatypes.S n)%nat) by lia. subst m.
      change (cos_partial n x + cos_term (Datatypes.S n) x -
              (cos_partial n x + cos_term (Datatypes.S n) x) ==
              cos_tail (Datatypes.S (Datatypes.S n)) (Datatypes.S (Datatypes.S n)) x).
      rewrite (qeqT_imp_qeq _ _ (sc_cos_tail_le_m (Datatypes.S (Datatypes.S n)) (Datatypes.S (Datatypes.S n)) x
                                (Nat.le_refl (Datatypes.S (Datatypes.S n))))).
      ring.
Qed.

(* ---- 三角不等式：|tail| ≤ tail_abs ---- *)
Lemma sc_sin_tail_abs_le : forall m n x,
  QleT' (Qabs (sin_tail m n x)) (sin_tail_abs m n (Qabs x)).
Proof.
  intros m n x. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply (Qle_trans _ (Qabs (sin_tail m n x) + Qabs (sin_term n x)) _).
      * apply Qabs_triangle.
      * apply Qplus_le_compat; [exact (QleT'_to_Qle _ _ IH) | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; (apply qeqT_imp_qeq; apply (sc_abs_sin_term n x))].
    + setoid_rewrite (Qplus_0_r (sin_tail_abs m n (Qabs x))).
      apply (Qle_trans _ (Qabs (sin_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (sin_tail m n x + 0) (sin_tail m n x)). ring.
      * exact (QleT'_to_Qle _ _ IH).
Qed.

Lemma sc_cos_tail_abs_le : forall m n x,
  QleT' (Qabs (cos_tail m n x)) (cos_tail_abs m n (Qabs x)).
Proof.
  intros m n x. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply (Qle_trans _ (Qabs (cos_tail m n x) + Qabs (cos_term n x)) _).
      * apply Qabs_triangle.
      * apply Qplus_le_compat; [exact (QleT'_to_Qle _ _ IH) | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; (apply qeqT_imp_qeq; apply (sc_abs_cos_term n x))].
    + setoid_rewrite (Qplus_0_r (cos_tail_abs m n (Qabs x))).
      apply (Qle_trans _ (Qabs (cos_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (cos_tail m n x + 0) (cos_tail m n x)). ring.
      * exact (QleT'_to_Qle _ _ IH).
Qed.

(* ---- 尾和绝对版非负、单调（第二参数）---- *)
Lemma sc_sin_tail_abs_nonneg : forall m n A, Qle 0 A -> QleT' 0 (sin_tail_abs m n A).
Proof.
  intros m n A HA. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply (Qle_trans _ (sin_tail_abs m n A) _).
      * exact (QleT'_to_Qle _ _ IH).
      * apply (Qle_plus_nonneg_r (sin_tail_abs m n A) (q_pow A (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n)))).
        apply QleT'_to_Qle; apply q_pow_fact_nonneg; apply Qle_to_QleT'. exact HA.
    + setoid_replace (sin_tail_abs m n A + 0) with (sin_tail_abs m n A) by ring.
      exact (QleT'_to_Qle _ _ IH).
Qed.

Lemma sc_cos_tail_abs_nonneg : forall m n A, Qle 0 A -> QleT' 0 (cos_tail_abs m n A).
Proof.
  intros m n A HA. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply (Qle_trans _ (cos_tail_abs m n A) _).
      * exact (QleT'_to_Qle _ _ IH).
      * apply (Qle_plus_nonneg_r (cos_tail_abs m n A) (q_pow A (2 * n) / q_fact (2 * n))).
        apply QleT'_to_Qle; apply q_pow_fact_nonneg; apply Qle_to_QleT'. exact HA.
    + setoid_replace (cos_tail_abs m n A + 0) with (cos_tail_abs m n A) by ring.
      exact (QleT'_to_Qle _ _ IH).
Qed.

(* ---- 逐项支配：sin/cos 尾和（奇/偶次）⊆ exp 尾和（全次）----
   sin_tail_abs (S m) (S n) A：j ∈ [S m, S n)，t = 2j+1 ∈ [2m+3, 2n+1]
   exp_tail_abs (S(2m)) (S(2n)) A：t ∈ [2m+2, 2n+1] ⊇ 奇 t ✓
   cos_tail_abs (S m) (S n) A：j ∈ [S m, S n)，t = 2j ∈ [2m+2, 2n]
   exp_tail_abs (S(2m)) (S(2n)) A：t ∈ [2m+2, 2n+1] ⊇ 偶 t ✓ *)

(* exp_tail_abs 单步展开 *)
Lemma sc_exp_tail_abs_step : forall m0 n A, QeqT (exp_tail_abs m0 (Datatypes.S n) A) (exp_tail_abs m0 n A +
  (if Nat.leb m0 n then q_pow A (Datatypes.S n) / q_fact (Datatypes.S n) else 0)).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* exp_tail_abs 两步行展开（与 sin 每步一个奇次项配对：偶次项多余非负） *)
Lemma sc_exp_tail_abs_two : forall m0 n A, QeqT (exp_tail_abs m0 (Datatypes.S (Datatypes.S n)) A) (exp_tail_abs m0 n A +
  (if Nat.leb m0 n then q_pow A (Datatypes.S n) / q_fact (Datatypes.S n) else 0) +
  (if Nat.leb m0 (Datatypes.S n) then q_pow A (Datatypes.S (Datatypes.S n)) / q_fact (Datatypes.S (Datatypes.S n)) else 0)).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* sin_tail_abs 单步展开 *)
Lemma sc_sin_tail_abs_step : forall m0 n A, QeqT (sin_tail_abs m0 (Datatypes.S n) A) (sin_tail_abs m0 n A +
  (if Nat.leb m0 n then q_pow A (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n)) else 0)).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma sc_cos_tail_abs_step : forall m0 n A, QeqT (cos_tail_abs m0 (Datatypes.S n) A) (cos_tail_abs m0 n A +
  (if Nat.leb m0 n then q_pow A (2 * n) / q_fact (2 * n) else 0)).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma sc_sin_tail_abs_mono : forall m n A B, Qle 0 A -> Qle A B ->
  QleT' (sin_tail_abs m n A) (sin_tail_abs m n B).
Proof.
  intros m n A B HA HAB. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply Qplus_le_compat; [exact (QleT'_to_Qle _ _ IH) | apply QleT'_to_Qle; apply (Qle_div_same_denom (q_pow A (Datatypes.S (2 * n))) (q_pow B (Datatypes.S (2 * n))) (q_fact (Datatypes.S (2 * n))))].
      * apply q_fact_pos.
      * apply (q_pow_mono _ _ _ (Qle_to_QleT' _ _ HA) (Qle_to_QleT' _ _ HAB)).
    + setoid_replace (sin_tail_abs m n A + 0) with (sin_tail_abs m n A) by ring.
      setoid_replace (sin_tail_abs m n B + 0) with (sin_tail_abs m n B) by ring.
      exact (QleT'_to_Qle _ _ IH).
Qed.

Lemma sc_cos_tail_abs_mono : forall m n A B, Qle 0 A -> Qle A B ->
  QleT' (cos_tail_abs m n A) (cos_tail_abs m n B).
Proof.
  intros m n A B HA HAB. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply Qplus_le_compat; [exact (QleT'_to_Qle _ _ IH) | apply QleT'_to_Qle; apply (Qle_div_same_denom (q_pow A (2 * n)) (q_pow B (2 * n)) (q_fact (2 * n)))].
      * apply q_fact_pos.
      * apply (q_pow_mono _ _ _ (Qle_to_QleT' _ _ HA) (Qle_to_QleT' _ _ HAB)).
    + setoid_replace (cos_tail_abs m n A + 0) with (cos_tail_abs m n A) by ring.
      setoid_replace (cos_tail_abs m n B + 0) with (cos_tail_abs m n B) by ring.
      exact (QleT'_to_Qle _ _ IH).
Qed.

(* sin 尾和 ≤ exp 尾和（窗 [2m+2, 2n+1] 覆盖奇次 t = 2j+1） *)
Lemma sc_sin_tail_abs_le_exp : forall (m n : nat) (A : Q),
  Qle 0 A -> QleT' (sin_tail_abs (Datatypes.S m) (Datatypes.S n) A)
                 (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A).
Proof.
  intros m n A HA.
  induction n as [| n IH].
  - apply Qle_to_QleT'. (* n = 0：sin_tail_abs (S m) (S 0) == 0 == exp_tail_abs (2m+1) (S(2·0)) *)
    rewrite (qeqT_imp_qeq _ _ (sc_sin_tail_abs_step (Datatypes.S m) 0 A)).
    destruct (Nat.leb (Datatypes.S m) 0) eqn:E1; simpl.
    + exfalso. apply Nat.leb_le in E1. lia.
    + rewrite (qeqT_imp_qeq _ _ (sc_exp_tail_abs_step (Datatypes.S (2 * m)) 0 A)).
      destruct (Nat.leb (Datatypes.S (2 * m)) 0) eqn:E2; simpl.
      * exfalso. apply Nat.leb_le in E2. lia.
      * unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. (* 步：sin(S(S n)) ≤ exp(S(2(S n)))；换形 2(S n) → S(S(2n))（S 形，可与 IH 转换）
       sin 顶项 t = S(S(S(2n))) == exp 第二新增项 Y；guard 均 ⟺ m ≤ n *)
    rewrite (qeqT_imp_qeq _ _ (sc_sin_tail_abs_step (Datatypes.S m) (Datatypes.S n) A)).
    replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_exp_tail_abs_two (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A)).
    destruct (Nat.leb (Datatypes.S m) (Datatypes.S n)) eqn:E1.
    + destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (2 * n))) eqn:E2.
      * destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (Datatypes.S (2 * n)))) eqn:E3.
        -- (* (T,T,T)：sin(n) + Y ≤ (exp(2n+1) + X) + Y；X ≥ 0 *)
           apply (Qle_trans _ (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A +
                                (q_pow A (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))) _).
           ++ apply Qplus_le_compat.
              ** exact (QleT'_to_Qle _ _ IH).
              ** apply Qle_refl.
           ++ apply Qplus_le_compat.
              ** apply (Qle_plus_nonneg_r (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A)
                     (q_pow A (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n))))).
                 apply QleT'_to_Qle; apply q_pow_fact_nonneg; apply Qle_to_QleT'. exact HA.
              ** apply Qle_refl.
        -- exfalso. apply Nat.leb_le in E1. apply Nat.leb_gt in E3. lia.
      * exfalso. apply Nat.leb_le in E1. apply Nat.leb_gt in E2. lia.
    + destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (2 * n))) eqn:E2.
      * exfalso. apply Nat.leb_gt in E1. apply Nat.leb_le in E2. lia.
      * destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (Datatypes.S (2 * n)))) eqn:E3.
        -- exfalso. apply Nat.leb_gt in E1. apply Nat.leb_le in E3. lia.
        -- (* (F,F,F)：sin(n) + 0 ≤ (exp(2n+1) + 0) + 0 *)
           setoid_replace (sin_tail_abs (Datatypes.S m) (Datatypes.S n) A + 0)
             with (sin_tail_abs (Datatypes.S m) (Datatypes.S n) A) by ring.
           setoid_replace (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A + 0 + 0)
             with (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A) by ring.
           exact (QleT'_to_Qle _ _ IH).
Qed.

(* cos 尾和 ≤ exp 尾和（窗 [2m+2, 2n+1] 覆盖偶次 t = 2j；顶项 t = 2n+2 == exp 第一新增项） *)
Lemma sc_cos_tail_abs_le_exp : forall (m n : nat) (A : Q),
  Qle 0 A -> QleT' (cos_tail_abs (Datatypes.S m) (Datatypes.S n) A)
                 (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A).
Proof.
  intros m n A HA.
  induction n as [| n IH].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (sc_cos_tail_abs_step (Datatypes.S m) 0 A)).
    destruct (Nat.leb (Datatypes.S m) 0) eqn:E1; simpl.
    + exfalso. apply Nat.leb_le in E1. lia.
    + rewrite (qeqT_imp_qeq _ _ (sc_exp_tail_abs_step (Datatypes.S (2 * m)) 0 A)).
      destruct (Nat.leb (Datatypes.S (2 * m)) 0) eqn:E2; simpl.
      * exfalso. apply Nat.leb_le in E2. lia.
      * unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. (* cos 顶项 t = 2(S n) = S(S(2n)) == exp 第一新增项 X；Y 多余非负 *)
    rewrite (qeqT_imp_qeq _ _ (sc_cos_tail_abs_step (Datatypes.S m) (Datatypes.S n) A)).
    replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_exp_tail_abs_two (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A)).
    destruct (Nat.leb (Datatypes.S m) (Datatypes.S n)) eqn:E1.
    + destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (2 * n))) eqn:E2.
      * destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (Datatypes.S (2 * n)))) eqn:E3.
        -- (* (T,T,T)：cos(n) + X ≤ (exp(2n+1) + X) + Y；Y ≥ 0 *)
           apply (Qle_trans _ (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A +
                                (q_pow A (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n))))) _).
           ++ apply Qplus_le_compat.
              ** exact (QleT'_to_Qle _ _ IH).
              ** apply Qle_refl.
           ++ apply (Qle_plus_nonneg_r
                      (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A +
                       (q_pow A (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n)))))
                      (q_pow A (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))).
              apply QleT'_to_Qle; apply q_pow_fact_nonneg; apply Qle_to_QleT'. exact HA.
        -- exfalso. apply Nat.leb_le in E1. apply Nat.leb_gt in E3. lia.
      * exfalso. apply Nat.leb_le in E1. apply Nat.leb_gt in E2. lia.
    + destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (2 * n))) eqn:E2.
      * exfalso. apply Nat.leb_gt in E1. apply Nat.leb_le in E2. lia.
      * destruct (Nat.leb (Datatypes.S (2 * m)) (Datatypes.S (Datatypes.S (2 * n)))) eqn:E3.
        -- exfalso. apply Nat.leb_gt in E1. apply Nat.leb_le in E3. lia.
        -- (* (F,F,F) *)
           setoid_replace (cos_tail_abs (Datatypes.S m) (Datatypes.S n) A + 0)
             with (cos_tail_abs (Datatypes.S m) (Datatypes.S n) A) by ring.
           setoid_replace (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A + 0 + 0)
             with (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) A) by ring.
           exact (QleT'_to_Qle _ _ IH).
Qed.

(* ---- 主界：m ≤ n、|y| ≤ B ⟹ |sin_partial n y − sin_partial m y| ≤ (B^{2m+1}/(2m+1)!)·2·C0 ---- *)
(* 直接版：sin 尾 ≤ exp 尾窗 [S(2m), S(2n)]（A := |y| 本身即可） *)
Lemma sc_sin_diff_bound2 : forall (y B : Q) (m n : nat),
  Qle 0 B -> Qle (Qabs y) B ->
  (forall t : nat, (Datatypes.S (2 * m) <= t)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (Qabs (sin_partial n y - sin_partial m y))
      ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q).
Proof.
  intros y B m n HB Hy Hgeom Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sin_tail_abs (Datatypes.S m) (Datatypes.S n) B) _).
  - apply (Qle_trans _ (sin_tail_abs (Datatypes.S m) (Datatypes.S n) (Qabs y)) _).
    + apply (Qle_trans _ (Qabs (sin_tail (Datatypes.S m) (Datatypes.S n) y)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        apply (Qabs_wd (sin_partial n y - sin_partial m y) (sin_tail (Datatypes.S m) (Datatypes.S n) y)).
        apply qeqT_imp_qeq. apply sc_sin_diff_tail. exact Hmn.
      * apply QleT'_to_Qle. apply sc_sin_tail_abs_le.
    + apply QleT'_to_Qle. apply sc_sin_tail_abs_mono; [apply Qabs_nonneg | exact Hy].
  - apply (Qle_trans _ (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) B) _).
    + apply QleT'_to_Qle. apply sc_sin_tail_abs_le_exp. exact HB.
    + apply QleT'_to_Qle.
      apply (exp_tail_abs_geom2 B (Datatypes.S (2 * m)) (Datatypes.S (2 * n))
               (Qle_to_QleT' _ _ HB)
               (fun t Ht => Qle_to_QleT' _ _ (Hgeom t (NatLe_drop _ _ Ht)))).
      * lia.
Qed.

Lemma sc_cos_diff_bound2 : forall (y B : Q) (m n : nat),
  Qle 0 B -> Qle (Qabs y) B ->
  (forall t : nat, (Datatypes.S (2 * m) <= t)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (Qabs (cos_partial n y - cos_partial m y))
      ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q).
Proof.
  intros y B m n HB Hy Hgeom Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (cos_tail_abs (Datatypes.S m) (Datatypes.S n) B) _).
  - apply (Qle_trans _ (cos_tail_abs (Datatypes.S m) (Datatypes.S n) (Qabs y)) _).
    + apply (Qle_trans _ (Qabs (cos_tail (Datatypes.S m) (Datatypes.S n) y)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        apply (Qabs_wd (cos_partial n y - cos_partial m y) (cos_tail (Datatypes.S m) (Datatypes.S n) y)).
        apply qeqT_imp_qeq. apply sc_cos_diff_tail. exact Hmn.
      * apply QleT'_to_Qle. apply sc_cos_tail_abs_le.
    + apply QleT'_to_Qle. apply sc_cos_tail_abs_mono; [apply Qabs_nonneg | exact Hy].
  - apply (Qle_trans _ (exp_tail_abs (Datatypes.S (2 * m)) (Datatypes.S (2 * n)) B) _).
    + apply QleT'_to_Qle. apply sc_cos_tail_abs_le_exp. exact HB.
    + apply QleT'_to_Qle.
      apply (exp_tail_abs_geom2 B (Datatypes.S (2 * m)) (Datatypes.S (2 * n))
               (Qle_to_QleT' _ _ HB)
               (fun t Ht => Qle_to_QleT' _ _ (Hgeom t (NatLe_drop _ _ Ht)))).
      * lia.
Qed.

(* ---- 一致柯西模：|y| ≤ B ⟹ sin_partial m y 与 sin_partial n y 的模统一（m,n ≥ N）---- *)
Lemma sc_sin_partial_cauchy_bounded : forall (B : Q) (eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    forall y : Q, QleT' (Qabs y) B ->
      QltT (Qabs (sin_partial m y - sin_partial n y)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  (* 基指标取 S(2·N0)（偶窗起点的几何条件从 N0 起已满足） *)
  set (N0' := Datatypes.S (2 * N0)).
  assert (HN0' : forall t : nat, (N0' <= t)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
  { intros t Ht. apply QleT'_to_Qle. apply (HN0 t). apply NatLe_lift. unfold N0'. lia. }
  set (C := (q_pow B N0' / q_fact N0') * (1 + 1)%Q).
  assert (HC : QleT' 0 C) by (unfold C; apply q_pow_fact2_nonneg; exact HB).
  destruct (arch_decay C eps HC Hep) as [t Hdec].
  exists (N0' + Datatypes.S t)%nat.
  intros m n Hm Hn y Hy.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - assert (Hmn : (m <= n)%nat) by (apply Nat.leb_le; exact Emn).
    (* 需要 |sin_partial n y − sin_partial m y| ≤ (B^{S(2m)}/(S(2m))!)·2 *)
    assert (Hbound : Qle (Qabs (sin_partial n y - sin_partial m y))
                         ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q)).
    { apply QleT'_to_Qle. apply (sc_sin_diff_bound2 y B m n (QleT'_to_Qle _ _ HB) (QleT'_to_Qle _ _ Hy)).
      - intros u Hu. apply (HN0' u). lia.
      - exact Hmn. }
    assert (Hlt : Qlt ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q) eps).
    { (* 由 exp_tail_arch：b := S(2m) ≥ N0' + S t ⟹ (B^b/b!)·2 < eps *)
      apply QltT_to_Qlt. apply (exp_tail_arch B N0' t (Datatypes.S (2 * m)) eps HB (fun u Hu => Qle_to_QleT' _ _ (HN0' u (NatLe_drop _ _ Hu))) Hep Hdec).
      unfold N0'. lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (sin_partial n y - sin_partial m y)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (Qabs_Qminus (sin_partial m y) (sin_partial n y)). reflexivity.
    + exact (Qle_lt_trans _ ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q) _ Hbound Hlt).
  - assert (Hnm : (n <= m)%nat) by (apply Nat.leb_gt in Emn; lia).
    assert (Hbound : Qle (Qabs (sin_partial m y - sin_partial n y))
                         ((q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))) * (1 + 1)%Q)).
    { apply QleT'_to_Qle. apply (sc_sin_diff_bound2 y B n m (QleT'_to_Qle _ _ HB) (QleT'_to_Qle _ _ Hy)).
      - intros u Hu. apply (HN0' u). lia.
      - exact Hnm. }
    assert (Hlt : Qlt ((q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))) * (1 + 1)%Q) eps).
    { apply QltT_to_Qlt. apply (exp_tail_arch B N0' t (Datatypes.S (2 * n)) eps HB (fun u Hu => Qle_to_QleT' _ _ (HN0' u (NatLe_drop _ _ Hu))) Hep Hdec).
      unfold N0'. lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))) * (1 + 1)%Q) _ Hbound Hlt).
Qed.

Lemma sc_cos_partial_cauchy_bounded : forall (B : Q) (eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    forall y : Q, QleT' (Qabs y) B ->
      QltT (Qabs (cos_partial m y - cos_partial n y)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (N0' := Datatypes.S (2 * N0)).
  assert (HN0' : forall t : nat, (N0' <= t)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
  { intros t Ht. apply QleT'_to_Qle. apply (HN0 t). apply NatLe_lift. unfold N0'. lia. }
  set (C := (q_pow B N0' / q_fact N0') * (1 + 1)%Q).
  assert (HC : QleT' 0 C) by (unfold C; apply q_pow_fact2_nonneg; exact HB).
  destruct (arch_decay C eps HC Hep) as [t Hdec].
  exists (N0' + Datatypes.S t)%nat.
  intros m n Hm Hn y Hy.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - assert (Hmn : (m <= n)%nat) by (apply Nat.leb_le; exact Emn).
    assert (Hbound : Qle (Qabs (cos_partial n y - cos_partial m y))
                         ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q)).
    { apply QleT'_to_Qle. apply (sc_cos_diff_bound2 y B m n (QleT'_to_Qle _ _ HB) (QleT'_to_Qle _ _ Hy)).
      - intros u Hu. apply (HN0' u). lia.
      - exact Hmn. }
    assert (Hlt : Qlt ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q) eps).
    { apply QltT_to_Qlt. apply (exp_tail_arch B N0' t (Datatypes.S (2 * m)) eps HB (fun u Hu => Qle_to_QleT' _ _ (HN0' u (NatLe_drop _ _ Hu))) Hep Hdec).
      unfold N0'. lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (cos_partial n y - cos_partial m y)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (Qabs_Qminus (cos_partial m y) (cos_partial n y)). reflexivity.
    + exact (Qle_lt_trans _ ((q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) * (1 + 1)%Q) _ Hbound Hlt).
  - assert (Hnm : (n <= m)%nat) by (apply Nat.leb_gt in Emn; lia).
    assert (Hbound : Qle (Qabs (cos_partial m y - cos_partial n y))
                         ((q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))) * (1 + 1)%Q)).
    { apply QleT'_to_Qle. apply (sc_cos_diff_bound2 y B n m (QleT'_to_Qle _ _ HB) (QleT'_to_Qle _ _ Hy)).
      - intros u Hu. apply (HN0' u). lia.
      - exact Hnm. }
    assert (Hlt : Qlt ((q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))) * (1 + 1)%Q) eps).
    { apply QltT_to_Qlt. apply (exp_tail_arch B N0' t (Datatypes.S (2 * n)) eps HB (fun u Hu => Qle_to_QleT' _ _ (HN0' u (NatLe_drop _ _ Hu))) Hep Hdec).
      unfold N0'. lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))) * (1 + 1)%Q) _ Hbound Hlt).
Qed.

(* ---- Lipschitz：sin/cos 部分和（S 形）：|x|,|y| ≤ B ⟹
   |sin_partial n x − sin_partial n y| ≤ |x−y|·sc_cos_series n B（导数式级数 Σ_{j≤n} B^{2j}/(2j)!）
   |cos_partial n x − cos_partial n y| ≤ |x−y|·sc_sin_deriv_series n B（Σ_{j≤n} B^{2j+1}/(2j+1)!）
   其中两导数式级数 ≤ exp_series (2n+1) B ≤ exp_series_arch 一致界。 ---- *)
Fixpoint sc_cos_series (n : nat) (B : Q) : Q :=
  match n with
  | 0%nat => q_pow B 0 / q_fact 0
  | Datatypes.S m => sc_cos_series m B +
                     q_pow B (Datatypes.S (Datatypes.S (2 * m))) / q_fact (Datatypes.S (Datatypes.S (2 * m)))
  end.

Fixpoint sc_sin_deriv_series (n : nat) (B : Q) : Q :=
  match n with
  | 0%nat => q_pow B 1 / q_fact 1
  | Datatypes.S m => sc_sin_deriv_series m B +
                     q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))
  end.

(* cos 导数式级数 ≤ exp_series (2n) B：偶次项 ⊆ exp 前 2n 项 *)
Lemma sc_cos_series_le_exp : forall n B, QleT' 0 B ->
  QleT' (sc_cos_series n B) (exp_series (2 * n) B).
Proof.
  intros n B HB.
  induction n as [| n IH].
  - apply Qle_to_QleT'. (* sc_cos_series 0 == 1；exp_series 0 == 1 *)
    unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. (* cos_series (S n) = cos(n) + T（T := B^{S(S(2n))}/(S(S(2n)))!，定义性）；
       exp_series (2(S n)) B ≡ exp_series (S(S(2n))) B = (exp_series (2n) + U) + T，U := B^{S(2n)}/(S(2n))! ≥ 0 *)
    change (sc_cos_series n B +
            (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n)))) <=
            exp_series (2 * Datatypes.S n) B).
    replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    apply (Qle_trans _ (exp_series (2 * n) B +
                         (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n))))) _).
    + apply Qplus_le_compat; [exact (QleT'_to_Qle _ _ IH) | apply Qle_refl].
    + change (exp_series (2 * n) B +
              (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n)))) <=
              exp_series (Datatypes.S (2 * n)) B +
              (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n))))).
      apply Qplus_le_compat.
      * apply QleT'_to_Qle; apply exp_series_step_mono; apply Qle_to_QleT'. exact (QleT'_to_Qle _ _ HB).
      * apply Qle_refl.
Qed.

(* sin 导数式级数 ≤ exp_series (S(2n)) B：奇次项 ⊆ exp 前 2n+1 项 *)
Lemma sc_sin_deriv_series_le_exp : forall n B, QleT' 0 B ->
  QleT' (sc_sin_deriv_series n B) (exp_series (Datatypes.S (2 * n)) B).
Proof.
  intros n B HB.
  induction n as [| n IH].
  - apply Qle_to_QleT'. (* n = 0：B^1/1! ≤ exp_series 1 B = 1 + B^1/1! *)
    change (q_pow B 1 / q_fact 1 <= 1 + (q_pow B 1 / q_fact 1)).
    setoid_replace (1 + (q_pow B 1 / q_fact 1)) with ((q_pow B 1 / q_fact 1) + 1) by ring.
    apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1.
  - apply Qle_to_QleT'. (* SDS (S n) = SDS(n) + Y（Y := B^{S(S(S(2n)))}/(S(S(S(2n))))!，定义性）；
       exp_series (S(2(S n))) B ≡ exp_series (S(S(S(2n)))) B = (exp_series (S(S(2n))) + Y)，exp_series (S(S(2n))) = exp_series (S(2n)) + U' *)
    change (sc_sin_deriv_series n B +
            (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))) <=
            exp_series (Datatypes.S (2 * Datatypes.S n)) B).
    replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    apply (Qle_trans _ (exp_series (Datatypes.S (2 * n)) B +
                         (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))) _).
    + apply Qplus_le_compat; [exact (QleT'_to_Qle _ _ IH) | apply Qle_refl].
    + change (exp_series (Datatypes.S (2 * n)) B +
              (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))) <=
              exp_series (Datatypes.S (Datatypes.S (2 * n))) B +
              (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))).
      apply Qplus_le_compat.
      * apply QleT'_to_Qle; apply exp_series_step_mono; apply Qle_to_QleT'. exact (QleT'_to_Qle _ _ HB).
      * apply Qle_refl.
Qed.




(* ============================================================ *)
(* 批 2（轮 2）：逐项差分界 + Lipschitz + 零点/壹值/奇偶       *)
(* ============================================================ *)

(* sin 项差分：|Δsin_term j| ≤ |x−y|·B^{2j}/(2j)! *)
Lemma sc_sin_term_diff : forall (x y B : Q) (j : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (sin_term j x - sin_term j y))
      (Qmult (Qabs (x - y)) (q_pow B (2 * j) / q_fact (2 * j))).
Proof.
  intros x y B j HB Hx Hy.
  apply Qle_to_QleT'.
  unfold sin_term.
  (* sign·(x^{S(2j)}·inv f) − sign·(y^{S(2j)}·inv f) == sign·((x^{S(2j)}−y^{S(2j)})·inv f) *)
  assert (Halg : q_pow (-1) j * (q_pow x (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) -
                  q_pow (-1) j * (q_pow y (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) ==
                  q_pow (-1) j * ((q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))) *
                    Qinv (q_fact (Datatypes.S (2 * j))))).
  { unfold Qdiv. ring. }
  setoid_rewrite Halg.
  apply (Qle_trans _ (Qabs ((q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))) *
                            Qinv (q_fact (Datatypes.S (2 * j))))) _).
  - (* |sign·t| ≤ |t|（|sign| == 1，先等式再 ≤） *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    rewrite Qabs_Qmult.
    rewrite (qeqT_imp_qeq _ _ (sc_abs_sign j)).
    ring.
  - apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                              (Qabs (Qinv (q_fact (Datatypes.S (2 * j)))))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
    + apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                                (Qinv (q_fact (Datatypes.S (2 * j))))) _).
      * apply (Qmult_le_compat_nonneg
                 (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                 (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                 (Qabs (Qinv (q_fact (Datatypes.S (2 * j)))))
                 (Qinv (q_fact (Datatypes.S (2 * j))))).
        -- split; [apply Qabs_nonneg | apply Qle_refl].
        -- split.
           ++ apply Qabs_nonneg.
           ++ assert (Hinvpos : Qlt 0 (Qinv (q_fact (Datatypes.S (2 * j))))).
              { apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos. }
              apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
              apply (Qabs_pos (Qinv (q_fact (Datatypes.S (2 * j))))
                              (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * j)))) Hinvpos)).
      * apply (Qle_trans _ (Qmult (Qmult (Qabs (x - y))
                                         (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j))))
                                  (Qinv (q_fact (Datatypes.S (2 * j))))) _).
        -- apply (Qmult_le_compat_r
                   (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                   (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j))))
                   (Qinv (q_fact (Datatypes.S (2 * j))))).
           ++ apply QleT'_to_Qle; apply (q_pow_diff_bound x y B (2 * j) (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ Hx) (Qle_to_QleT' _ _ Hy)).
           ++ apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * j))))).
              apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
        -- (* (|x−y|·((S(2j))#1·B^{2j}))·/((S(2j))!) == |x−y|·B^{2j}·/((2j)!) *)
           setoid_replace (Qmult (Qmult (Qabs (x - y))
                                        (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j))))
                                 (Qinv (q_fact (Datatypes.S (2 * j)))))
             with (Qmult (Qabs (x - y))
                         (Qmult (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j)))
                                (Qinv (q_fact (Datatypes.S (2 * j)))))) by ring.
           rewrite (qeqT_imp_qeq _ _ (q_ratio_cancel_succ B (2 * j))).
           apply Qle_refl.
Qed.

(* cos 项差分（j = S m ≥ 1）：|Δcos_term (S m)| ≤ |x−y|·B^{S(2m)}/(S(2m))! *)
Lemma sc_cos_term_diff : forall (x y B : Q) (m : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (cos_term (Datatypes.S m) x - cos_term (Datatypes.S m) y))
      (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))).
Proof.
  intros x y B m HB Hx Hy.
  apply Qle_to_QleT'.
  unfold cos_term.
  (* 幂指标换形：2(S m) → S(2m+1) *)
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (2 * m + 1))%nat by lia.
  assert (Halg : q_pow (-1) (Datatypes.S m) * (q_pow x (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1))) -
                  q_pow (-1) (Datatypes.S m) * (q_pow y (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1))) ==
                  q_pow (-1) (Datatypes.S m) * ((q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))) *
                    Qinv (q_fact (Datatypes.S (2 * m + 1))))).
  { unfold Qdiv. ring. }
  setoid_rewrite Halg.
  apply (Qle_trans _ (Qabs ((q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))) *
                            Qinv (q_fact (Datatypes.S (2 * m + 1))))) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    rewrite Qabs_Qmult.
    rewrite (qeqT_imp_qeq _ _ (sc_abs_sign (Datatypes.S m))).
    ring.
  - apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                              (Qabs (Qinv (q_fact (Datatypes.S (2 * m + 1)))))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
    + apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                                (Qinv (q_fact (Datatypes.S (2 * m + 1))))) _).
      * apply (Qmult_le_compat_nonneg
                 (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                 (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                 (Qabs (Qinv (q_fact (Datatypes.S (2 * m + 1)))))
                 (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
        -- split; [apply Qabs_nonneg | apply Qle_refl].
        -- split.
           ++ apply Qabs_nonneg.
           ++ assert (Hinvpos : Qlt 0 (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
              { apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos. }
              apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
              apply (Qabs_pos (Qinv (q_fact (Datatypes.S (2 * m + 1))))
                              (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * m + 1)))) Hinvpos)).
      * apply (Qle_trans _ (Qmult (Qmult (Qabs (x - y))
                                         (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1))))
                                  (Qinv (q_fact (Datatypes.S (2 * m + 1))))) _).
        -- apply (Qmult_le_compat_r
                   (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                   (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1))))
                   (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
           ++ apply QleT'_to_Qle; apply (q_pow_diff_bound x y B (2 * m + 1) (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ Hx) (Qle_to_QleT' _ _ Hy)).
           ++ apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
              apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
        -- (* 重组使 ratio-cancel 模式成为直接子项，再指标换形 *)
           setoid_replace (Qmult (Qmult (Qabs (x - y))
                                (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1))))
                         (Qinv (q_fact (Datatypes.S (2 * m + 1)))))
             with (Qmult (Qabs (x - y))
                         (Qmult (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1)))
                                (Qinv (q_fact (Datatypes.S (2 * m + 1)))))) by ring.
           rewrite (qeqT_imp_qeq _ _ (q_ratio_cancel_succ B (2 * m + 1))).
           replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
           apply Qle_refl.
Qed.

(* sin 部分和 Lipschitz：|Δsin_partial n| ≤ |x−y|·sc_cos_series n B *)
Lemma sc_sin_partial_lipschitz : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sin_partial n x - sin_partial n y))
      (Qmult (Qabs (x - y)) (sc_cos_series n B)).
Proof.
  intros x y B n HB Hx Hy.
  induction n as [| n IH].
  - apply Qle_to_QleT'. (* n = 0：Δ == x − y；cos_series 0 B == 1 *)
    assert (Hd : sin_partial 0 x - sin_partial 0 y == x - y).
    { change (sin_term 0 x - sin_term 0 y == x - y).
      unfold sin_term.
      assert (Hc : q_pow (-1) 0 == 1) by reflexivity.
      assert (Hx1 : q_pow x (Datatypes.S (2 * 0)) == x * 1).
      { change (q_pow x 1 == x * 1). rewrite (qeqT_imp_qeq _ _ (q_pow_succ x 0)). reflexivity. }
      assert (Hy1 : q_pow y (Datatypes.S (2 * 0)) == y * 1).
      { change (q_pow y 1 == y * 1). rewrite (qeqT_imp_qeq _ _ (q_pow_succ y 0)). reflexivity. }
      assert (Hf : q_fact (Datatypes.S (2 * 0)) == 1).
      { change (q_fact 1 == 1). reflexivity. }
      rewrite Hc. rewrite Hx1. rewrite Hy1. rewrite Hf.
      change (1 * ((x * 1) / 1) - 1 * ((y * 1) / 1) == x - y).
      unfold Qdiv.
      assert (Hi : Qinv 1 == 1) by reflexivity.
      rewrite Hi.
      assert (Hlx : 1 * ((x * 1) * 1) == x).
      { eapply Qeq_trans.
        - apply Qmult_1_l.
        - eapply Qeq_trans.
          + apply Qmult_1_r.
          + apply Qmult_1_r. }
      assert (Hly : 1 * ((y * 1) * 1) == y).
      { eapply Qeq_trans.
        - apply Qmult_1_l.
        - eapply Qeq_trans.
          + apply Qmult_1_r.
          + apply Qmult_1_r. }
      rewrite Hlx. rewrite Hly. reflexivity. }
    apply (Qle_trans _ (Qabs (x - y)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (sin_partial 0 x - sin_partial 0 y) (x - y)). exact Hd.
    + change (Qabs (x - y) <= Qabs (x - y) * (q_pow B 0 / q_fact 0)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hcs : q_pow B 0 / q_fact 0 == 1).
      { change (1 / 1 == 1). unfold Qdiv. reflexivity. }
      rewrite Hcs.
      rewrite Qmult_1_r. reflexivity.
  - apply Qle_to_QleT'. (* 步：Δ(S n) = Δ(n) + Δterm_{S n}；cos_series (S n) = cos_series n + B^{S(S(2n))}/(S(S(2n)))! *)
    assert (Hsplit : sin_partial (Datatypes.S n) x - sin_partial (Datatypes.S n) y ==
                     (sin_partial n x - sin_partial n y) + (sin_term (Datatypes.S n) x - sin_term (Datatypes.S n) y)).
    { change (sin_partial n x + sin_term (Datatypes.S n) x - (sin_partial n y + sin_term (Datatypes.S n) y) ==
              (sin_partial n x - sin_partial n y) + (sin_term (Datatypes.S n) x - sin_term (Datatypes.S n) y)).
      ring. }
    rewrite Hsplit.
    apply (Qle_trans _ (Qabs (sin_partial n x - sin_partial n y) +
                         Qabs (sin_term (Datatypes.S n) x - sin_term (Datatypes.S n) y)) _).
    + apply Qabs_triangle.
    + (* 项界换形：sc_sin_term_diff 给 B^{2(S n)}/(2(S n))!，换 S(S(2n)) 形 *)
      assert (Hterm : Qle (Qabs (sin_term (Datatypes.S n) x - sin_term (Datatypes.S n) y))
                          (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n)))))).
      { apply (Qle_trans _ (Qmult (Qabs (x - y)) (q_pow B (2 * Datatypes.S n) / q_fact (2 * Datatypes.S n))) _).
        - apply QleT'_to_Qle. apply (sc_sin_term_diff x y B (Datatypes.S n));
            [ exact (QleT'_to_Qle _ _ HB)
            | exact (QleT'_to_Qle _ _ Hx)
            | exact (QleT'_to_Qle _ _ Hy) ].
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia. reflexivity. }
      apply (Qle_trans _ (Qplus (Qmult (Qabs (x - y)) (sc_cos_series n B))
                                  (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n)))))) _).
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _ IH).
        -- exact Hterm.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        change (sc_cos_series (Datatypes.S n) B)
          with (sc_cos_series n B + q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n)))).
        ring.
Qed.


(* cos 部分和 Lipschitz（S 形）：|Δcos_partial (S n)| ≤ |x−y|·sc_sin_deriv_series n B *)
Lemma sc_cos_partial_lipschitz_succ : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y))
      (Qmult (Qabs (x - y)) (sc_sin_deriv_series n B)).
Proof.
  intros x y B n HB Hx Hy.
  induction n as [| n IH].
  - apply Qle_to_QleT'. (* n = 0：Δcos_partial 1 == Δcos_term 1；SDS 0 == B^1/1! *)
    assert (Hd : cos_partial 1 x - cos_partial 1 y == cos_term 1 x - cos_term 1 y).
    { change (cos_term 0 x + cos_term 1 x - (cos_term 0 y + cos_term 1 y) ==
              cos_term 1 x - cos_term 1 y).
      assert (Hc0x : cos_term 0 x == 1).
      { unfold cos_term. reflexivity. }
      assert (Hc0y : cos_term 0 y == 1).
      { unfold cos_term. reflexivity. }
      rewrite Hc0x. rewrite Hc0y. ring. }
    apply (Qle_trans _ (Qabs (cos_term 1 x - cos_term 1 y)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (cos_partial 1 x - cos_partial 1 y) (cos_term 1 x - cos_term 1 y)). exact Hd.
    + apply (Qle_trans _ (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (2 * 0)) / q_fact (Datatypes.S (2 * 0)))) _).
      * apply QleT'_to_Qle. apply (sc_cos_term_diff x y B 0);
          [ exact (QleT'_to_Qle _ _ HB)
          | exact (QleT'_to_Qle _ _ Hx)
          | exact (QleT'_to_Qle _ _ Hy) ].
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
  - apply Qle_to_QleT'. (* 步：Δ(S(S n)) = Δ(S n) + Δterm_{S(S n)}；SDS (S n) = SDS n + B^{S(S(S(2n)))}/(S(S(S(2n))))! *)
    assert (Hsplit : cos_partial (Datatypes.S (Datatypes.S n)) x - cos_partial (Datatypes.S (Datatypes.S n)) y ==
                     (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y) +
                     (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y)).
    { change (cos_partial (Datatypes.S n) x + cos_term (Datatypes.S (Datatypes.S n)) x -
              (cos_partial (Datatypes.S n) y + cos_term (Datatypes.S (Datatypes.S n)) y) ==
              (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y) +
              (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y)).
      ring. }
    rewrite Hsplit.
    apply (Qle_trans _ (Qabs (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y) +
                         Qabs (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y)) _).
    + apply Qabs_triangle.
    + (* 项界换形：sc_cos_term_diff (S n) 给 B^{S(2(S n))}/(S(2(S n)))!，换 S(S(S(2n))) 形 *)
      assert (Hterm : Qle (Qabs (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y))
                          (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))))).
      { apply (Qle_trans _ (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (2 * Datatypes.S n)) / q_fact (Datatypes.S (2 * Datatypes.S n)))) _).
        - apply QleT'_to_Qle. apply (sc_cos_term_diff x y B (Datatypes.S n));
            [ exact (QleT'_to_Qle _ _ HB)
            | exact (QleT'_to_Qle _ _ Hx)
            | exact (QleT'_to_Qle _ _ Hy) ].
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia. reflexivity. }
      apply (Qle_trans _ (Qplus (Qmult (Qabs (x - y)) (sc_sin_deriv_series n B))
                                  (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))))) _).
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _ IH).
        -- exact Hterm.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        change (sc_sin_deriv_series (Datatypes.S n) B)
          with (sc_sin_deriv_series n B + q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))).
        ring.
Qed.


(* ---- 零点 / 壹值 ---- *)
Lemma sc_q_pow_zero_ge1 : forall k : nat, (1 <= k)%nat ->QeqT (q_pow 0 k) (0).
Proof.
  intros k Hk. destruct k as [| k'].
  - apply qeq_imp_qeqT. exfalso. lia.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (q_pow_succ 0 k')). rewrite (Qmult_0_l (q_pow 0 k')). reflexivity.
Qed.

Lemma sc_sin_partial_zero : forall n : nat, QeqT (sin_partial n 0) (0).
Proof.
  induction n as [| n IH].
  - apply qeq_imp_qeqT. change (sin_term 0 0 == 0).
    unfold sin_term.
    assert (Hpow : q_pow 0 (Datatypes.S (2 * 0)) == 0).
    { change (q_pow 0 1 == 0).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ 0 0)).
      rewrite (Qmult_0_l (q_pow 0 0)). reflexivity. }
    rewrite Hpow.
    unfold Qdiv.
    rewrite (Qmult_0_l (Qinv (q_fact (Datatypes.S (2 * 0))))).
    rewrite (Qmult_0_r (q_pow (-1) 0)).
    reflexivity.
  - apply qeq_imp_qeqT. change (sin_partial n 0 + sin_term (Datatypes.S n) 0 == 0).
    unfold sin_term.
    assert (Hpow : q_pow 0 (Datatypes.S (2 * Datatypes.S n)) == 0).
    { rewrite (qeqT_imp_qeq _ _ (q_pow_succ 0 (2 * Datatypes.S n))).
      rewrite (Qmult_0_l (q_pow 0 (2 * Datatypes.S n))). reflexivity. }
    rewrite Hpow.
    unfold Qdiv.
    rewrite (Qmult_0_l (Qinv (q_fact (Datatypes.S (2 * Datatypes.S n))))).
    rewrite (qeqT_imp_qeq _ _ IH).
    rewrite (Qmult_0_r (q_pow (-1) (Datatypes.S n))).
    reflexivity.
Qed.


Lemma sc_cos_partial_one : forall n : nat, QeqT (cos_partial n 0) (1).
Proof.
  induction n as [| n IH].
  - apply qeq_imp_qeqT. change (cos_term 0 0 == 1).
    unfold cos_term. reflexivity.
  - apply qeq_imp_qeqT. change (cos_partial n 0 + cos_term (Datatypes.S n) 0 == 1).
    unfold cos_term.
    assert (Hpow : q_pow 0 (2 * Datatypes.S n) == 0).
    { replace (2 * Datatypes.S n)%nat with (Datatypes.S (2 * n + 1))%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ 0 (2 * n + 1))).
      rewrite (Qmult_0_l (q_pow 0 (2 * n + 1))). reflexivity. }
    rewrite Hpow.
    unfold Qdiv.
    rewrite (Qmult_0_l (Qinv (q_fact (2 * Datatypes.S n)))).
    rewrite (qeqT_imp_qeq _ _ IH).
    rewrite (Qmult_0_r (q_pow (-1) (Datatypes.S n))).
    reflexivity.
Qed.



(* ---- 奇偶（Q 层）---- *)
Lemma sc_sin_term_neg : forall (j : nat) (x : Q), QeqT (sin_term j (- x)) (- sin_term j x).
Proof.
  intros j x.
  apply qeq_imp_qeqT.
  unfold sin_term.
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd x j)).
  unfold Qdiv. ring.
Qed.

Lemma sc_cos_term_neg : forall (j : nat) (x : Q), QeqT (cos_term j (- x)) (cos_term j x).
Proof.
  intros j x.
  apply qeq_imp_qeqT.
  unfold cos_term.
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even x j)).
  reflexivity.
Qed.

Lemma sc_sin_partial_neg : forall (n : nat) (x : Q), QeqT (sin_partial n (- x)) (- sin_partial n x).
Proof.
  intros n x.
  induction n as [| n IH]; simpl.
  - apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply sc_sin_term_neg.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IH). rewrite (qeqT_imp_qeq _ _ (sc_sin_term_neg (Datatypes.S n) x)). ring.
Qed.

Lemma sc_cos_partial_neg : forall (n : nat) (x : Q), QeqT (cos_partial n (- x)) (cos_partial n x).
Proof.
  intros n x.
  induction n as [| n IH]; simpl.
  - apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply sc_cos_term_neg.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IH). rewrite (qeqT_imp_qeq _ _ (sc_cos_term_neg (Datatypes.S n) x)). ring.
Qed.

(* ============================================================ *)
(* 批 3（轮 2）：Real 层 cauchy_real_sin / cauchy_real_cos      *)
(* 副本 cauchy_real_exp（主文件 L7690-7772）：对角定义 +        *)
(*   eps/2 尾项（sc_*_partial_cauchy_bounded）+ eps/(2C) 输入项 *)
(*   （Lipschitz + 导数式级数 ≤ exp_series ≤ C）。              *)
(* ============================================================ *)

(* cos 项零指标 == 1（任意 x，纯计算） *)
Lemma sc_cos_term_zero : forall x : Q, QeqT (cos_term 0 x) (1).
Proof. intro x. apply qeq_imp_qeqT. unfold cos_term. reflexivity. Qed.

(* cos_partial 0 == 1（任意 x） *)
Lemma sc_cos_partial_zero_const : forall x : Q, QeqT (cos_partial 0 x) (1).
Proof. intro x. apply qeq_imp_qeqT. change (cos_term 0 x == 1). apply qeqT_imp_qeq. apply sc_cos_term_zero. Qed.

(* 导数式级数非负（非负项和） *)
Lemma sc_cos_series_nonneg : forall n B, QleT' 0 B -> QleT' 0 (sc_cos_series n B).
Proof.
  intros n B HB. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. change (Qle 0 (q_pow B 0 / q_fact 0)).
    apply QleT'_to_Qle; apply (q_pow_fact_nonneg B 0). exact HB.
  - apply Qle_to_QleT'. apply (Qle_trans _ (sc_cos_series n B) _).
    + exact (QleT'_to_Qle _ _ IH).
    + apply (Qle_plus_nonneg_r (sc_cos_series n B)
             (q_pow B (Datatypes.S (Datatypes.S (2 * n))) / q_fact (Datatypes.S (Datatypes.S (2 * n))))).
      apply QleT'_to_Qle; apply q_pow_fact_nonneg. exact HB.
Qed.

Lemma sc_sin_deriv_series_nonneg : forall n B, QleT' 0 B -> QleT' 0 (sc_sin_deriv_series n B).
Proof.
  intros n B HB. induction n as [| n IH]; simpl.
  - apply Qle_to_QleT'. change (Qle 0 (q_pow B 1 / q_fact 1)).
    apply QleT'_to_Qle; apply (q_pow_fact_nonneg B 1). exact HB.
  - apply Qle_to_QleT'. apply (Qle_trans _ (sc_sin_deriv_series n B) _).
    + exact (QleT'_to_Qle _ _ IH).
    + apply (Qle_plus_nonneg_r (sc_sin_deriv_series n B)
             (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))).
      apply QleT'_to_Qle; apply q_pow_fact_nonneg. exact HB.
Qed.

(* ---- real_sin 定义（副本 cauchy_real_exp） ---- *)
Definition cauchy_real_sin (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n : nat => sin_partial n (u n)).
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (Hu (eps / (2 * C))%Q) as [N1 HN1].
  { apply Qlt_to_QltT.
    assert (H2C : Qlt 0 (2 * C)).
    { apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | exact HCpos]. }
    unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv (2 * C))).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. exact H2C. }
  destruct (sc_sin_partial_cauchy_bounded M (eps / 2)%Q (qltT_leT' 0 M HMpos)) as [N2 HN2].
  { apply (qltT_div_pos eps 2).
    - exact Heps.
    - exact qltT_0_2. }
  exists (Nat.max N1 N2).
  intros m n Hm Hn.
  assert (Hsplit : sin_partial m (u m) - sin_partial n (u n) ==
                   (sin_partial m (u m) - sin_partial m (u n)) + (sin_partial m (u n) - sin_partial n (u n))).
  { ring. }
  assert (Habs : Qeq (Qabs (sin_partial m (u m) - sin_partial n (u n)))
                     (Qabs ((sin_partial m (u m) - sin_partial m (u n)) +
                            (sin_partial m (u n) - sin_partial n (u n))))).
  { apply (Qabs_wd (sin_partial m (u m) - sin_partial n (u n))
                   ((sin_partial m (u m) - sin_partial m (u n)) + (sin_partial m (u n) - sin_partial n (u n)))).
    exact Hsplit. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (sin_partial m (u m) - sin_partial m (u n)) +
                         Qabs (sin_partial m (u n) - sin_partial n (u n))) _).
  { apply (Qle_trans _ (Qabs ((sin_partial m (u m) - sin_partial m (u n)) +
                               (sin_partial m (u n) - sin_partial n (u n)))) _).
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs. }
    { apply Qabs_triangle. } }
  { apply (Qle_lt_trans _ (Qplus (Qmult (Qabs (u m - u n)) C) (eps / 2)) _).
    { apply Qplus_le_compat.
      { (* 输入项：Lipschitz + cos_series ≤ exp ≤ C *)
        assert (Hin : Qle (Qabs (sin_partial m (u m) - sin_partial m (u n)))
                          (Qmult (Qabs (u m - u n)) C)).
        { apply (Qle_trans _ (Qmult (Qabs (u m - u n)) (sc_cos_series m M)) _).
          - apply QleT'_to_Qle. apply (sc_sin_partial_lipschitz (u m) (u n) M m (qltT_leT' 0 M HMpos) (HM m) (HM n)).
          - apply (Qmult_le_compat_nonneg (Qabs (u m - u n)) (Qabs (u m - u n))
                                          (sc_cos_series m M) C).
            + split; [apply Qabs_nonneg | apply Qle_refl].
            + split.
              * apply QleT'_to_Qle. apply sc_cos_series_nonneg. exact (qltT_leT' 0 M HMpos).
              * apply (Qle_trans _ (exp_series (2 * m) M) _).
                -- apply QleT'_to_Qle. apply sc_cos_series_le_exp. exact (qltT_leT' 0 M HMpos).
                 -- apply QleT'_to_Qle. apply (HC (2 * m)%nat). }
        exact Hin. }
      { apply (Qlt_le_weak (Qabs (sin_partial m (u n) - sin_partial n (u n))) (eps / 2)).
        apply QltT_to_Qlt.
        apply (HN2 m n).
        { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)]. }
        { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)]. }
        { apply (HM n). } } }
    { apply (Qlt_le_trans _ (Qplus (eps / 2) (eps / 2)) _).
      { apply (Qplus_lt_le_compat (Qmult (Qabs (u m - u n)) C) (eps / 2) (eps / 2) (eps / 2)).
        { apply (Qlt_le_trans _ (Qmult (eps / (2 * C)) C) _).
          { apply (Qmult_lt_compat_r (Qabs (u m - u n)) (eps / (2 * C)) C).
            { exact HCpos. }
            { apply QltT_to_Qlt.
              apply (HN1 m n).
              { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)]. }
              { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)]. } } }
          { assert (Hc : Qmult (eps / (2 * C)) C == eps / 2).
            { unfold Qdiv. field.
              all: try (intro HzneA; exact (match (q_neq_of_lt _ (Qlt_to_QltT _ _ (Qmult_lt_0_compat 2 C (QltT_to_Qlt _ _ qltT_0_2) HCpos)) (qeq_imp_qeqT _ _ HzneA)) with end)).
              all: try (unfold Qlt; simpl; lia).
              all: try (exact HCpos).
              all: try (unfold Qeq; simpl; lia).
              all: try (intro HzneA; exact (match (q_neq_of_lt _ (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ HzneA)) with end)). }
            apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hc. } }
        { apply Qle_refl. } }
      { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        unfold Qdiv. field.
        all: try (unfold Qeq; simpl; lia). } } }
Defined.

(* ---- real_cos 定义（输入项按 m 分支：m=0 恒 1；m=S m' 走 succ-Lipschitz） ---- *)
Definition cauchy_real_cos (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n : nat => cos_partial n (u n)).
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (Hu (eps / (2 * C))%Q) as [N1 HN1].
  { apply Qlt_to_QltT.
    assert (H2C : Qlt 0 (2 * C)).
    { apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | exact HCpos]. }
    unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv (2 * C))).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. exact H2C. }
  destruct (sc_cos_partial_cauchy_bounded M (eps / 2)%Q (qltT_leT' 0 M HMpos)) as [N2 HN2].
  { apply (qltT_div_pos eps 2).
    - exact Heps.
    - exact qltT_0_2. }
  exists (Nat.max N1 N2).
  intros m n Hm Hn.
  assert (Hsplit : cos_partial m (u m) - cos_partial n (u n) ==
                   (cos_partial m (u m) - cos_partial m (u n)) + (cos_partial m (u n) - cos_partial n (u n))).
  { ring. }
  assert (Habs : Qeq (Qabs (cos_partial m (u m) - cos_partial n (u n)))
                     (Qabs ((cos_partial m (u m) - cos_partial m (u n)) +
                            (cos_partial m (u n) - cos_partial n (u n))))).
  { apply (Qabs_wd (cos_partial m (u m) - cos_partial n (u n))
                   ((cos_partial m (u m) - cos_partial m (u n)) + (cos_partial m (u n) - cos_partial n (u n)))).
    exact Hsplit. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (cos_partial m (u m) - cos_partial m (u n)) +
                         Qabs (cos_partial m (u n) - cos_partial n (u n))) _).
  { apply (Qle_trans _ (Qabs ((cos_partial m (u m) - cos_partial m (u n)) +
                               (cos_partial m (u n) - cos_partial n (u n)))) _).
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs. }
    { apply Qabs_triangle. } }
  { apply (Qle_lt_trans _ (Qplus (Qmult (Qabs (u m - u n)) C) (eps / 2)) _).
    { apply Qplus_le_compat.
      { (* 输入项：m 分支 *)
        destruct m as [| m'].
        - (* m = 0：cos_partial 0 == 1 两侧，差 0 *)
          assert (Ha : cos_partial 0 (u 0%nat) == 1) by (apply qeqT_imp_qeq; apply sc_cos_partial_zero_const).
          assert (Hb : cos_partial 0 (u n) == 1) by (apply qeqT_imp_qeq; apply sc_cos_partial_zero_const).
          assert (Hz : cos_partial 0 (u 0%nat) - cos_partial 0 (u n) == 0).
          { rewrite Ha. rewrite Hb. ring. }
          apply (Qle_trans _ 0 _).
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (cos_partial 0 (u 0%nat) - cos_partial 0 (u n)) 0). exact Hz.
          + apply (Qmult_le_0_compat (Qabs (u 0%nat - u n)) C).
            * apply Qabs_nonneg.
            * apply (Qlt_le_weak 0 C). exact HCpos.
        - (* m = S m'：succ-Lipschitz + SDS ≤ exp ≤ C *)
          assert (Hin : Qle (Qabs (cos_partial (Datatypes.S m') (u (Datatypes.S m')) - cos_partial (Datatypes.S m') (u n)))
                            (Qmult (Qabs (u (Datatypes.S m') - u n)) C)).
          { apply (Qle_trans _ (Qmult (Qabs (u (Datatypes.S m') - u n)) (sc_sin_deriv_series m' M)) _).
            + apply QleT'_to_Qle. apply (sc_cos_partial_lipschitz_succ (u (Datatypes.S m')) (u n) M m' (qltT_leT' 0 M HMpos) (HM (Datatypes.S m')) (HM n)).
            + apply (Qmult_le_compat_nonneg (Qabs (u (Datatypes.S m') - u n)) (Qabs (u (Datatypes.S m') - u n))
                                            (sc_sin_deriv_series m' M) C).
              * split; [apply Qabs_nonneg | apply Qle_refl].
              * split.
                -- apply QleT'_to_Qle. apply sc_sin_deriv_series_nonneg. exact (qltT_leT' 0 M HMpos).
                -- apply (Qle_trans _ (exp_series (Datatypes.S (2 * m')) M) _).
                   ++ apply QleT'_to_Qle. apply sc_sin_deriv_series_le_exp. exact (qltT_leT' 0 M HMpos).
                   ++ apply QleT'_to_Qle. apply (HC (Datatypes.S (2 * m'))%nat). }
          exact Hin. }
      { apply (Qlt_le_weak (Qabs (cos_partial m (u n) - cos_partial n (u n))) (eps / 2)).
        apply QltT_to_Qlt.
        apply (HN2 m n).
        { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)]. }
        { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)]. }
        { apply (HM n). } } }
    { apply (Qlt_le_trans _ (Qplus (eps / 2) (eps / 2)) _).
      { apply (Qplus_lt_le_compat (Qmult (Qabs (u m - u n)) C) (eps / 2) (eps / 2) (eps / 2)).
        { apply (Qlt_le_trans _ (Qmult (eps / (2 * C)) C) _).
          { apply (Qmult_lt_compat_r (Qabs (u m - u n)) (eps / (2 * C)) C).
            { exact HCpos. }
            { apply QltT_to_Qlt.
              apply (HN1 m n).
              { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)]. }
              { apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)]. } } }
          { assert (Hc : Qmult (eps / (2 * C)) C == eps / 2).
            { unfold Qdiv. field.
              all: try (intro HzneA; exact (match (q_neq_of_lt _ (Qlt_to_QltT _ _ (Qmult_lt_0_compat 2 C (QltT_to_Qlt _ _ qltT_0_2) HCpos)) (qeq_imp_qeqT _ _ HzneA)) with end)).
              all: try (unfold Qlt; simpl; lia).
              all: try (exact HCpos).
              all: try (unfold Qeq; simpl; lia).
              all: try (intro HzneA; exact (match (q_neq_of_lt _ (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ HzneA)) with end)). }
            apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hc. } }
        { apply Qle_refl. } }
      { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        unfold Qdiv. field.
        all: try (unfold Qeq; simpl; lia). } } }
Defined.

(* ---- 投影引理 ---- *)
Lemma real_sin_proj : forall (h : Real) (n : nat),
  QeqT (projT1 (cauchy_real_sin h) n) (sin_partial n (projT1 h n)).
Proof.
  intros h n. apply qeq_imp_qeqT. destruct h as [u Hu]. reflexivity.
Qed.

Lemma real_cos_proj : forall (h : Real) (n : nat), QeqT (projT1 (cauchy_real_cos h) n) (cos_partial n (projT1 h n)).
Proof.
  intros h n. apply qeq_imp_qeqT. destruct h as [u Hu]. reflexivity.
Qed.

(* ---- sin 0 == 0 / cos 0 == 1 ---- *)
Lemma real_sin_zero : real_eq (cauchy_real_sin real_zero) real_zero.
Proof.
  intro eps. intro Heps.
  exists 0%nat.
  intros n Hn.
  simpl.
  assert (H1 : sin_partial n 0 - 0 == 0).
  { rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_zero n)). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd (sin_partial n 0 - 0) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

Lemma real_cos_one : real_eq (cauchy_real_cos real_zero) real_one.
Proof.
  intro eps. intro Heps.
  exists 0%nat.
  intros n Hn.
  simpl.
  assert (H1 : cos_partial n 0 - 1 == 0).
  { rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_one n)). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd (cos_partial n 0 - 1) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* ---- 奇偶（Real 层）---- *)
Lemma real_sin_opp : forall x : Real,
  real_eq (cauchy_real_sin (real_opp x)) (real_opp (cauchy_real_sin x)).
Proof.
  intros x. intro eps. intro Heps.
  destruct x as [u Hu].
  exists 0%nat.
  intros n Hn.
  simpl.
  assert (H1 : sin_partial n (- u n) - (- sin_partial n (u n)) == 0).
  { rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_neg n (u n))). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd (sin_partial n (- u n) - (- sin_partial n (u n))) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

Lemma real_cos_opp : forall x : Real,
  real_eq (cauchy_real_cos (real_opp x)) (cauchy_real_cos x).
Proof.
  intros x. intro eps. intro Heps.
  destruct x as [u Hu].
  exists 0%nat.
  intros n Hn.
  simpl.
  assert (H1 : cos_partial n (- u n) - cos_partial n (u n) == 0).
  { rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_neg n (u n))). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd (cos_partial n (- u n) - cos_partial n (u n)) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.
(* ============================================================ *)
(* 批 4（轮 3）：cos 变号证据（π 路线第一块）                 *)
(*   cos_partial n 2 < −1/10（n ≥ 3）→ real_cos_two_neg        *)
(*   （cos(real_const 2) < 0：cos 在 (0,2) 变号的可验证证据）   *)
(* ============================================================ *)

(* Q 层：cos_partial n 2 < −1/10，n ≥ 3
   链：cos n ≤ cos 3 + |Δ| ≤ cos 3 + (2^7/7!)·2 == −13/35 < −1/10 *)
Lemma sc_cos_partial_ge3_lt_minus_tenth : forall n : nat, (3 <= n)%nat ->
  QltT (cos_partial n 2) (- (1/10)).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  (* 界 1：|cos_partial n 2 − cos_partial 3 2| ≤ (2^7/7!)·2 *)
  assert (Hbound : Qle (Qabs (cos_partial n 2 - cos_partial 3 2))
                       ((q_pow 2 7 / q_fact 7) * (1 + 1))).
  { assert (Habs2eq : Qabs 2 == 2).
    { unfold Qabs. simpl. reflexivity. }
    apply QleT'_to_Qle. apply (sc_cos_diff_bound2 2 2 3 n).
    - unfold Qle; simpl; lia.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs2eq.
    - intros t Ht. unfold Qle; simpl; lia.
    - lia. }
  (* 界 2：cos n ≤ cos 3 + |Δ| *)
  assert (Hle1 : Qle (cos_partial n 2)
                    (cos_partial 3 2 + Qabs (cos_partial n 2 - cos_partial 3 2))).
  { apply (Qle_trans _ (cos_partial 3 2 + (cos_partial n 2 - cos_partial 3 2)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qle_Qabs. }
  (* 界 3：cos 3 + (2^7/7!)·2 == −13/35（具体求值） *)
  assert (Hval : cos_partial 3 2 + (q_pow 2 7 / q_fact 7) * (1 + 1) == - (13 # 35)).
  { unfold Qeq. simpl. lia. }
  (* 组装 *)
  apply (Qle_lt_trans _ (cos_partial 3 2 + (q_pow 2 7 / q_fact 7) * (1 + 1)) _).
  - apply (Qle_trans _ (cos_partial 3 2 + Qabs (cos_partial n 2 - cos_partial 3 2)) _).
    + exact Hle1.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Hbound.
  - rewrite Hval.
    unfold Qlt. simpl. lia.
Qed.
(* Real 层：cos(2) < 0（cos 在 [0,2] 变号的可验证证据） *)
Lemma real_cos_two_neg : real_lt (cauchy_real_cos (real_const 2)) real_zero.
Proof.
  unfold real_lt.
  exists (1 / 10).
  split.
  - (* 0 < 1/10 *)
    apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 3%nat.
    intros n Hn.
    simpl.
    (* 目标：QltT (1/10) (0 − cos_partial n 2)（投影归约后） *)
    apply Qlt_to_QltT.
    assert (Heq : 0 - cos_partial n 2 == - cos_partial n 2) by ring.
    rewrite Heq.
    (* cos_partial n 2 < −1/10 ⟹ 1/10 < −cos_partial n 2 *)
    assert (Hlt : Qlt (cos_partial n 2) (- (1/10))).
    { apply QltT_to_Qlt. apply sc_cos_partial_ge3_lt_minus_tenth. apply NatLe_drop in Hn. lia. }
    (* Hlt ⟹ 0 < −(1/10) − cos n（Qlt_minus_iff）；换形为 0 < −cos n − 1/10 *)
    pose proof (proj1 (Qlt_minus_iff (cos_partial n 2) (- (1/10))) Hlt) as Hm.
    assert (Hr : (- (1/10)) - cos_partial n 2 == (- cos_partial n 2) - (1/10)) by ring.
    rewrite Hr in Hm.
    exact (proj2 (Qlt_minus_iff (1/10) (- cos_partial n 2)) Hm).
Qed.
(* 批 5（轮 4）：cos(1) > 1/10 与 sin(1) > 1/10（点态正性）     *)
(*   cos(1) > 0 ∧ cos(2) < 0 ⟹ cos 在 (1,2) 变号括号收窄        *)
(*   模板同批 4：Hval（具体求值）+ Hbound（diff 界）+ 组装       *)
(* ============================================================ *)

(* Q 层辅助：−|x| ≤ x *)
Lemma sc_q_neg_abs_le : forall x : Q, QleT' (- Qabs x) x.
Proof.
  intro x.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (- (- x)) _).
  - apply Qopp_le_compat.
    apply (Qle_trans _ (Qabs (- x)) _).
    + apply Qle_Qabs.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* cos(1) 余量下界：n ≥ 2 ⟹ 1/10 < cos_partial n 1（cos n ≥ 13/24 − 1/60 == 21/40） *)
Lemma sc_cos_partial_ge2_one_margin : forall n : nat, (2 <= n)%nat ->
  QltT (1/10) (cos_partial n 1).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hbound : Qle (Qabs (cos_partial n 1 - cos_partial 2 1))
                       ((q_pow 1 5 / q_fact 5) * (1 + 1))).
  { assert (Habs1eq : Qabs 1 == 1).
    { unfold Qabs. simpl. reflexivity. }
    apply QleT'_to_Qle. apply (sc_cos_diff_bound2 1 1 2 n).
    - unfold Qle; simpl; lia.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs1eq.
    - intros t Ht. unfold Qle; simpl; lia.
    - lia. }
  assert (Hle2 : Qle (cos_partial 2 1 + (- Qabs (cos_partial n 1 - cos_partial 2 1)))
                     (cos_partial n 1)).
  { apply (Qle_trans _ (cos_partial 2 1 + (cos_partial n 1 - cos_partial 2 1)) _).
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply QleT'_to_Qle. apply sc_q_neg_abs_le.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  apply (Qlt_le_trans _ (cos_partial 2 1 + (- ((q_pow 1 5 / q_fact 5) * (1 + 1)))) _).
  - (* 1/10 < cos 2 1 − 1/60 == 13/24 − 1/60 == 21/40 *)
    assert (Hval : cos_partial 2 1 == 13 / 24).
    { unfold Qeq. simpl. lia. }
    rewrite Hval.
    assert (Hv2 : (q_pow 1 5 / q_fact 5) * (1 + 1) == 1 / 60).
    { unfold Qeq. simpl. lia. }
    rewrite Hv2.
    unfold Qlt. simpl. lia.
  - apply (Qle_trans _ (cos_partial 2 1 + (- Qabs (cos_partial n 1 - cos_partial 2 1))) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hbound.
    + exact Hle2.
Qed.

(* sin(1) 余量下界：n ≥ 2 ⟹ 1/10 < sin_partial n 1（sin n ≥ 101/120 − 1/60 == 33/40） *)
Lemma sc_sin_partial_ge2_one_margin : forall n : nat, (2 <= n)%nat ->
  QltT (1/10) (sin_partial n 1).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hbound : Qle (Qabs (sin_partial n 1 - sin_partial 2 1))
                       ((q_pow 1 5 / q_fact 5) * (1 + 1))).
  { assert (Habs1eq : Qabs 1 == 1).
    { unfold Qabs. simpl. reflexivity. }
    apply QleT'_to_Qle. apply (sc_sin_diff_bound2 1 1 2 n).
    - unfold Qle; simpl; lia.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs1eq.
    - intros t Ht. unfold Qle; simpl; lia.
    - lia. }
  assert (Hle2 : Qle (sin_partial 2 1 + (- Qabs (sin_partial n 1 - sin_partial 2 1)))
                     (sin_partial n 1)).
  { apply (Qle_trans _ (sin_partial 2 1 + (sin_partial n 1 - sin_partial 2 1)) _).
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply QleT'_to_Qle. apply sc_q_neg_abs_le.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  apply (Qlt_le_trans _ (sin_partial 2 1 + (- ((q_pow 1 5 / q_fact 5) * (1 + 1)))) _).
  - assert (Hval : sin_partial 2 1 == 101 / 120).
    { unfold Qeq. simpl. lia. }
    rewrite Hval.
    assert (Hv2 : (q_pow 1 5 / q_fact 5) * (1 + 1) == 1 / 60).
    { unfold Qeq. simpl. lia. }
    rewrite Hv2.
    unfold Qlt. simpl. lia.
  - apply (Qle_trans _ (sin_partial 2 1 + (- Qabs (sin_partial n 1 - sin_partial 2 1))) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hbound.
    + exact Hle2.
Qed.

(* Real 层：cos(1) > 0 *)
Lemma real_cos_one_pos : real_lt real_zero (cauchy_real_cos (real_const 1)).
Proof.
  unfold real_lt.
  exists (1 / 10).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Heq : cos_partial n 1 - 0 == cos_partial n 1) by ring.
    rewrite Heq.
    apply QltT_to_Qlt. apply sc_cos_partial_ge2_one_margin. apply NatLe_drop in Hn. lia.
Qed.

(* Real 层：sin(1) > 0 *)
Lemma real_sin_one_pos : real_lt real_zero (cauchy_real_sin (real_const 1)).
Proof.
  unfold real_lt.
  exists (1 / 10).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Heq : sin_partial n 1 - 0 == sin_partial n 1) by ring.
    rewrite Heq.
    apply QltT_to_Qlt. apply sc_sin_partial_ge2_one_margin. apply NatLe_drop in Hn. lia.
Qed.
(* ============================================================ *)
(* 批 6（轮 5）：Leibniz π——偶数配对、奇数子列（递增）路线     *)
(*   lp_odd m = Σ_{j=0}^{m} (a_{2j} − a_{2j+1}) = S_{2m+1} ↑ π/4 *)
(*   a_k = 1/(2k+1)；π := Cauchy(4·lp_odd)；夹逼 3 < π < 4      *)
(* ============================================================ *)

Definition lp_a (k : nat) : Q := Qdiv 1 (Qmake (Z.of_nat (2 * k + 1)) 1).

Definition lp_pair (j : nat) : Q := lp_a (2 * j) - lp_a (2 * j + 1).

Fixpoint lp_odd (m : nat) : Q :=
  match m with
  | 0%nat => lp_pair 0
  | Datatypes.S p => lp_odd p + lp_pair (Datatypes.S p)
  end.

Definition lp_four : Q := 1 + 1 + 1 + 1.

(* a 反单调（≤ 版）：k ≤ j ⟹ a_j ≤ a_k *)
Lemma sc_lpa_decr_le : forall k j : nat, (k <= j)%nat -> QleT' (lp_a j) (lp_a k).
Proof.
  intros k j Hkj.
  unfold lp_a.
  apply (q_le_div_le 1 (Qmake (Z.of_nat (2 * j + 1)) 1)
                       1 (Qmake (Z.of_nat (2 * k + 1)) 1)).
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qle_to_QleT'.
    setoid_replace (1 * (Z.of_nat (2 * k + 1) # 1)) with (Z.of_nat (2 * k + 1) # 1) by (apply Qmult_1_l).
    setoid_replace (1 * (Z.of_nat (2 * j + 1) # 1)) with (Z.of_nat (2 * j + 1) # 1) by (apply Qmult_1_l).
    unfold Qle; simpl; lia.
Qed.

Lemma sc_lpa_nonneg : forall k : nat, QleT' 0 (lp_a k).
Proof.
  intro k.
  unfold lp_a.
  apply (q_le_div_le 0 1 1 (Qmake (Z.of_nat (2 * k + 1)) 1)).
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qle_to_QleT'. unfold Qle; simpl; lia.
Qed.

Lemma sc_lp_pair_nonneg : forall j : nat, QleT' 0 (lp_pair j).
Proof.
  intro j.
  apply Qle_to_QleT'.
  unfold lp_pair.
  apply (proj1 (Qle_minus_iff (lp_a (2 * j + 1)) (lp_a (2 * j)))).
  apply QleT'_to_Qle. apply sc_lpa_decr_le. lia.
Qed.

Lemma sc_lp_odd_mono : forall m : nat, QleT' (lp_odd m) (lp_odd (Datatypes.S m)).
Proof.
intro m. apply Qle_to_QleT'. change (Qle (lp_odd m) (lp_odd m + lp_pair (Datatypes.S m))). exact (Qle_plus_nonneg_r (lp_odd m) (lp_pair (Datatypes.S m)) (QleT'_to_Qle _ _ (sc_lp_pair_nonneg (Datatypes.S m)))).
Qed.

Lemma sc_lp_odd_chain : forall m n : nat, (m <= n)%nat ->
  QleT' (lp_odd m) (lp_odd n).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - apply Qle_to_QleT'. assert (Hm0 : (m = 0)%nat) by lia. subst m. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n)) as [Heq | Hne].
    + subst m. apply Qle_to_QleT'. apply Qle_refl.
    + apply Qle_to_QleT'. apply (Qle_trans _ (lp_odd n) _).
      * apply QleT'_to_Qle. apply IH. lia.
      * apply QleT'_to_Qle. apply sc_lp_odd_mono.
Qed.

Lemma sc_lp_odd_diff_step : forall m n : nat, QeqT (lp_odd (Datatypes.S n) - lp_odd m) ((lp_odd n - lp_odd m) + lp_pair (Datatypes.S n)).
Proof.
  intros m n.
  apply qeq_imp_qeqT.
  change (lp_odd n + lp_pair (Datatypes.S n) - lp_odd m ==
          (lp_odd n - lp_odd m) + lp_pair (Datatypes.S n)).
  ring.
Qed.

(* 两段界：m ≤ n ⟹ lp_odd n − lp_odd m ≤ a_{2m+2} − a_{2n+2} *)
Lemma sc_lp_odd_diff2 : forall m n : nat, (m <= n)%nat ->
  QleT' (lp_odd n - lp_odd m) (lp_a (2 * m + 2) - lp_a (2 * n + 2)).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - apply Qle_to_QleT'. assert (Hm0 : (m = 0)%nat) by lia. subst m.
    unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      rewrite (qeqT_imp_qeq _ _ (sc_lp_odd_diff_step m n)).
      replace (2 * Datatypes.S n)%nat with (2 * n + 2)%nat by lia.
      replace (2 * Datatypes.S n + 2)%nat with (2 * n + 4)%nat by lia.
      apply (Qle_trans _ ((lp_a (2 * m + 2) - lp_a (2 * n + 2)) +
                          (lp_a (2 * n + 2) - lp_a (2 * n + 3))) _).
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _ (IH m E)).
        -- unfold lp_pair.
           replace (2 * Datatypes.S n)%nat with (2 * n + 2)%nat by lia.
           replace (2 * n + 2 + 1)%nat with (2 * n + 3)%nat by lia.
           apply Qle_refl.
      * apply (Qle_trans _ (lp_a (2 * m + 2) - lp_a (2 * n + 3)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qopp_le_compat.
              apply QleT'_to_Qle. apply sc_lpa_decr_le. lia.
    + apply Nat.leb_gt in E.
      assert (Hm : (m = Datatypes.S n)%nat) by lia. subst m.
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 尾界：m ≤ n ⟹ lp_odd n − lp_odd m ≤ a_{2m+2} *)
Lemma sc_lp_odd_diff_bound : forall m n : nat, (m <= n)%nat ->
  QleT' (lp_odd n - lp_odd m) (lp_a (2 * m + 2)).
Proof.
  intros m n Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (lp_a (2 * m + 2) - lp_a (2 * n + 2)) _).
  - apply QleT'_to_Qle. apply sc_lp_odd_diff2. exact Hmn.
  - apply (Qle_trans _ (lp_a (2 * m + 2) + 0) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply (Qopp_le_compat 0 (lp_a (2 * n + 2))).
        apply QleT'_to_Qle. apply sc_lpa_nonneg.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 偶段（S_{2m+2}）递减：lp_odd (S m) + a_{2(S m)+2} ≤ lp_odd m + a_{2m+2} *)
Lemma sc_lp_ev_decr : forall m : nat,
  QleT' (lp_odd (Datatypes.S m) + lp_a (2 * Datatypes.S m + 2))
      (lp_odd m + lp_a (2 * m + 2)).
Proof.
  intro m.
  apply Qle_to_QleT'.
  change (Qle (lp_odd m + lp_pair (Datatypes.S m) + lp_a (2 * Datatypes.S m + 2))
              (lp_odd m + lp_a (2 * m + 2))).
  replace (2 * Datatypes.S m + 2)%nat with (2 * m + 4)%nat by lia.
  replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat by lia.
  apply (Qle_trans _ (lp_odd m + lp_a (2 * m + 2) + (lp_a (2 * m + 4) - lp_a (2 * m + 3))) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    unfold lp_pair.
    replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat by lia.
    replace (2 * m + 2 + 1)%nat with (2 * m + 3)%nat by lia.
    ring.
  - apply (Qle_trans _ (lp_odd m + lp_a (2 * m + 2) + 0) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * (* a_{2m+4} − a_{2m+3} ≤ 0 *)
        apply (Qle_trans _ (- (lp_a (2 * m + 3) - lp_a (2 * m + 4))) _).
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          -- apply (Qopp_le_compat 0 (lp_a (2 * m + 3) - lp_a (2 * m + 4))).
             apply (proj1 (Qle_minus_iff (lp_a (2 * m + 4)) (lp_a (2 * m + 3)))).
             apply QleT'_to_Qle. apply sc_lpa_decr_le. lia.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma sc_lp_ev_le_s2 : forall n : nat,
  QleT' (lp_odd n + lp_a (2 * n + 2)) (13 / 15).
Proof.
  induction n as [| n IH].
  - apply Qle_to_QleT'. change (Qle (lp_odd 0 + lp_a 2) (13 / 15)).
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    unfold lp_odd, lp_pair, lp_a. unfold Qeq. simpl. lia.
  - apply Qle_to_QleT'. apply (Qle_trans _ (lp_odd n + lp_a (2 * n + 2)) _).
    + apply QleT'_to_Qle. apply sc_lp_ev_decr.
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* 上界：lp_odd n ≤ 13/15 *)
Lemma sc_lp_odd_le_s2 : forall n : nat, QleT' (lp_odd n) (13 / 15).
Proof.
  intro n.
  apply Qle_to_QleT'.
  exact (Qle_trans (lp_odd n) (lp_odd n + lp_a (2 * n + 2)) (13 / 15)
    (Qle_plus_nonneg_r (lp_odd n) (lp_a (2 * n + 2))
      (QleT'_to_Qle _ _ (sc_lpa_nonneg (2 * n + 2))))
    (QleT'_to_Qle _ _ (sc_lp_ev_le_s2 n))).
Qed.

(* 下界（n ≥ 3）：lp_odd 3 ≤ lp_odd n *)
Lemma sc_lp_three_le : forall n : nat, (3 <= n)%nat ->
  QleT' (lp_odd 3) (lp_odd n).
Proof.
  intros n Hn.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply sc_lp_odd_chain. lia.
Qed.

(* 具体值 1：4·lp_odd 3 == 8/3 + 8/35 + 8/99 + 8/195 *)
Lemma sc_lp_three_value : QeqT (lp_four * lp_odd 3) (8 / 3 + 8 / 35 + 8 / 99 + 8 / 195).
Proof.
  apply qeq_imp_qeqT.
  unfold lp_four, lp_odd, lp_pair, lp_a.
  unfold Qeq. simpl. lia.
Qed.

(* 具体比较：3 + 1/100 < 4·lp_odd 3 *)
Lemma sc_lp_three_margin : QltT (3 + 1 / 100) (lp_four * lp_odd 3).
Proof.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (sc_lp_three_value)).
  unfold Qlt. simpl. lia.
Qed.

(* 具体比较：4·(13/15) < 4（52/15 < 4） *)
Lemma sc_lp_s2_margin : QltT (lp_four * (13 / 15)) 4.
Proof.
  apply Qlt_to_QltT.
  unfold lp_four. unfold Qlt. simpl. lia.
Qed.
(* 批 6b（轮 6）：Leibniz π Real 层——定义 + 夹逼 3 < π < 4     *)
(* ============================================================ *)

Lemma sc_lp_four_pos : QltT 0 lp_four.
Proof. apply Qlt_to_QltT. unfold lp_four. unfold Qlt; simpl; lia. Qed.

Lemma sc_lp_four_nonneg : QleT' 0 lp_four.
Proof.
  apply Qle_to_QleT'.
  (* ToyR 替换：Z 层直构（消 Qlt_le_weak→sc_lp_four_pos 转发链）：
     lp_four 定义展开为字面和，Qle 展开 = 交叉积 Z.le，线性判定闭合 *)
  unfold Qle, lp_four.
  simpl.
  lia.
Qed.

(* 差分归约：m ≤ n ⟹ lp_odd n − lp_odd m ≥ 0 *)
Lemma sc_lp_odd_diff_nonneg : forall m n : nat, (m <= n)%nat ->
  QleT' 0 (lp_odd n - lp_odd m).
Proof.  intros m n Hmn.
  apply Qle_to_QleT'.
  exact (proj1 (Qle_minus_iff (lp_odd m) (lp_odd n)) (QleT'_to_Qle _ _ (sc_lp_odd_chain m n Hmn))).
Qed.

(* |4(x−y)| == 4(y−x)（x ≤ y） *)
Lemma sc_lp_abs_four : forall x y : Q, Qle x y ->QeqT (Qabs (lp_four * x - lp_four * y)) (lp_four * (y - x)).
Proof.
  intros x y Hxy.
  apply qeq_imp_qeqT.
  (* A − B == 4(x−y)；4(x−y) == −(4(y−x))；|−t| == |t|；|4(y−x)| == 4(y−x)（非负） *)
  assert (Halg : lp_four * x - lp_four * y == lp_four * (x - y)).
  { ring. }
  assert (Hneg : lp_four * (x - y) == - (lp_four * (y - x))).
  { ring. }
  assert (Hnonneg : Qle 0 (lp_four * (y - x))).
  { apply Qmult_le_0_compat.
    - apply QleT'_to_Qle. apply sc_lp_four_nonneg.
    - apply (proj1 (Qle_minus_iff x y)). exact Hxy. }
  apply (Qeq_trans _ (Qabs (lp_four * (x - y))) _).
  - apply (Qabs_wd (lp_four * x - lp_four * y) (lp_four * (x - y))). exact Halg.
  - apply (Qeq_trans _ (Qabs (- (lp_four * (y - x)))) _).
    + apply (Qabs_wd (lp_four * (x - y)) (- (lp_four * (y - x)))). exact Hneg.
    + apply (Qeq_trans _ (Qabs (lp_four * (y - x))) _).
      * apply Qabs_opp.
      * apply (Qabs_pos (lp_four * (y - x))). exact Hnonneg.
Qed.

(* 尾界 ≤ 阿基米德形：m ≥ N ⟹ lp_a (2m+2) ≤ 1/(N+2)#1 *)
Lemma sc_lp_a_arch_le : forall m N : nat, (N <= m)%nat ->
  QleT' (lp_a (2 * m + 2)) (Qdiv 1 (Qmake (Z.of_nat (N + 2)) 1)).
Proof.
  intros m N HNm.
  unfold lp_a.
  replace (2 * (2 * m + 2) + 1)%nat with (4 * m + 5)%nat by lia.
  apply (q_le_div_le 1 (Qmake (Z.of_nat (4 * m + 5)) 1)
                       1 (Qmake (Z.of_nat (N + 2)) 1)).
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qle_to_QleT'.
    rewrite (Qmult_1_l (Qmake (Z.of_nat (N + 2)) 1)).
    rewrite (Qmult_1_l (Qmake (Z.of_nat (4 * m + 5)) 1)).
    unfold Qle; simpl; lia.
Qed.

(* 4·(1/(N+2)#1) < eps：arch 链（1/(N+2) < eps/4 乘 4） *)
Lemma sc_lp_four_arch_lt : forall (eps : Q) (N : nat),
  Qlt 0 eps -> Qlt (1 / (Z.of_nat (N + 2) # 1)) (eps / lp_four) ->
  QltT (lp_four * (1 / (Z.of_nat (N + 2) # 1))) eps.
Proof.
  intros eps N Heps Harch.
  apply Qlt_to_QltT.
  (* 4·(1/(N+2)) == (1/(N+2))·4 < (eps/4)·4 == eps *)
  apply (Qle_lt_trans _ ((1 / (Z.of_nat (N + 2) # 1)) * lp_four) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_le_trans _ ((eps / lp_four) * lp_four) _).
    + apply (Qmult_lt_compat_r (1 / (Z.of_nat (N + 2) # 1)) (eps / lp_four) lp_four).
      * exact (QltT_to_Qlt _ _ (sc_lp_four_pos)).
      * exact Harch.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hnz : ~ lp_four == 0) by (intro Hzne; exact (match (q_neq_of_lt _ sc_lp_four_pos (qeq_imp_qeqT _ _ Hzne)) with end)).
      unfold Qdiv. field. exact Hnz.
Qed.

(* 对称分支太繁：直接用 |a − b| == |b − a|（q_abs_minus_sym 思路内联） *)
Lemma sc_lp_abs_sym : forall a b : Q, QeqT (Qabs (a - b)) (Qabs (b - a)).
Proof.
  intros a b.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (- (b - a))) _).
  - apply (Qabs_wd (a - b) (- (b - a))). ring.
  - rewrite (Qabs_opp (b - a)). reflexivity.
Qed.

Definition cauchy_real_pi_leibniz : Real.
Proof.
  exists (fun n : nat => lp_four * lp_odd n).
  intros eps Heps.
  assert (Hq : Qlt 0 (eps / lp_four)).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv lp_four)).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (sc_lp_four_pos)). }
  destruct (q_arch_inv (eps / lp_four) (Qlt_to_QltT _ _ Hq)) as [N1 HN1].
  exists N1.
  intros m n Hm Hn.
  destruct (Nat.leb m n) eqn:E.
  - apply Nat.leb_le in E.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (lp_four * (lp_odd n - lp_odd m)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply qeqT_imp_qeq. apply sc_lp_abs_four.
      apply QleT'_to_Qle. apply sc_lp_odd_chain. exact E.
    + apply (Qle_lt_trans _ (lp_four * lp_a (2 * m + 2)) _).
      * setoid_replace (lp_four * (lp_odd n - lp_odd m)) with ((lp_odd n - lp_odd m) * lp_four) by ring.
        setoid_replace (lp_four * lp_a (2 * m + 2)) with (lp_a (2 * m + 2) * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd n - lp_odd m) (lp_a (2 * m + 2)) lp_four).
        -- apply QleT'_to_Qle. apply sc_lp_odd_diff_bound. exact E.
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
      * apply (Qle_lt_trans _ (lp_four * (1 / (Z.of_nat (N1 + 2) # 1))) _).
        -- setoid_replace (lp_four * (1 / (Z.of_nat (N1 + 2) # 1))) with ((1 / (Z.of_nat (N1 + 2) # 1)) * lp_four) by ring.
           setoid_replace (lp_four * lp_a (2 * m + 2)) with (lp_a (2 * m + 2) * lp_four) by ring.
           apply (Qmult_le_compat_r (lp_a (2 * m + 2)) (1 / (Z.of_nat (N1 + 2) # 1)) lp_four).
           ++ apply QleT'_to_Qle. apply sc_lp_a_arch_le. apply NatLe_drop in Hm. lia.
           ++ apply QleT'_to_Qle. apply sc_lp_four_nonneg.
        -- apply QltT_to_Qlt. apply sc_lp_four_arch_lt.
           ++ apply QltT_to_Qlt. exact Heps.
           ++ apply QltT_to_Qlt. exact HN1.
  - apply Nat.leb_gt in E.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (lp_four * (lp_odd m - lp_odd n)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply (Qeq_trans _ (Qabs (lp_four * lp_odd n - lp_four * lp_odd m)) _).
      * apply qeqT_imp_qeq. apply sc_lp_abs_sym.
      * apply qeqT_imp_qeq. apply sc_lp_abs_four.
        apply QleT'_to_Qle. apply sc_lp_odd_chain. lia.
    + apply (Qle_lt_trans _ (lp_four * lp_a (2 * n + 2)) _).
      * setoid_replace (lp_four * (lp_odd m - lp_odd n)) with ((lp_odd m - lp_odd n) * lp_four) by ring.
        setoid_replace (lp_four * lp_a (2 * n + 2)) with (lp_a (2 * n + 2) * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd m - lp_odd n) (lp_a (2 * n + 2)) lp_four).
        -- apply QleT'_to_Qle. apply sc_lp_odd_diff_bound. lia.
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
      * apply (Qle_lt_trans _ (lp_four * (1 / (Z.of_nat (N1 + 2) # 1))) _).
        -- setoid_replace (lp_four * (1 / (Z.of_nat (N1 + 2) # 1))) with ((1 / (Z.of_nat (N1 + 2) # 1)) * lp_four) by ring.
           setoid_replace (lp_four * lp_a (2 * n + 2)) with (lp_a (2 * n + 2) * lp_four) by ring.
           apply (Qmult_le_compat_r (lp_a (2 * n + 2)) (1 / (Z.of_nat (N1 + 2) # 1)) lp_four).
           ++ apply QleT'_to_Qle. apply sc_lp_a_arch_le. apply NatLe_drop in Hn. lia.
           ++ apply QleT'_to_Qle. apply sc_lp_four_nonneg.
        -- apply QltT_to_Qlt. apply sc_lp_four_arch_lt.
           ++ apply QltT_to_Qlt. exact Heps.
           ++ apply QltT_to_Qlt. exact HN1.
Defined.

(* 投影引理 *)
Lemma real_pi_leibniz_proj : forall n : nat, QeqT (projT1 (cauchy_real_pi_leibniz) n) (lp_four * lp_odd n).
Proof.
  intro n. apply qeq_imp_qeqT. reflexivity.
Qed.

(* ---- 夹逼：3 < π（余量：v n ≥ 4·lp_odd 3 > 3 + 1/100，n ≥ 3） ---- *)
Lemma real_pi_leibniz_gt_three : real_lt (real_const 3) cauchy_real_pi_leibniz.
Proof.
  unfold real_lt.
  exists (1 / 100).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 3%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Heq : lp_four * lp_odd n - 3 == (lp_four * lp_odd n) + (- 3)) by ring.
    (* 目标：1/100 < lp_four·lp_odd n − 3：链自 4·lp_odd 3 − 3 > 1/100 *)
    apply (Qlt_le_trans _ (lp_four * lp_odd 3 - 3) _).
    + apply (proj2 (Qlt_minus_iff (1 / 100) (lp_four * lp_odd 3 - 3))).
      setoid_replace ((lp_four * lp_odd 3 - 3) - (1 / 100))
        with (lp_four * lp_odd 3 - (3 + 1 / 100)) by ring.
      apply (proj1 (Qlt_minus_iff (3 + 1 / 100) (lp_four * lp_odd 3))).
      exact (QltT_to_Qlt _ _ (sc_lp_three_margin)).
    + (* 4·lp_odd 3 − 3 ≤ 4·lp_odd n − 3 *)
      apply Qplus_le_compat.
      * setoid_replace (lp_four * lp_odd 3) with (lp_odd 3 * lp_four) by ring.
        setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd 3) (lp_odd n) lp_four).
        -- apply QleT'_to_Qle. apply sc_lp_odd_chain. apply NatLe_drop in Hn. lia.
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
      * apply Qle_refl.
Qed.

(* ---- 夹逼：π < 4（余量：v n ≤ 52/15 < 4 − 1/10，n ≥ 0） ---- *)
Lemma real_pi_leibniz_lt_four : real_lt cauchy_real_pi_leibniz (real_const 4).
Proof.
  unfold real_lt.
  exists (1 / 10).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 0%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    (* 目标：1/10 < 4 − lp_four·lp_odd n：链自 4 − 52/15 > 1/10 *)
    apply (Qlt_le_trans _ (4 - lp_four * (13 / 15)) _).
    + (* 1/10 < 4 − 52/15：具体求值（lp_four·(13/15) == 52/15，4 − 52/15 == 8/15 > 1/10） *)
      assert (Hm : lp_four * (13 / 15) == 52 / 15).
      { unfold lp_four. unfold Qeq. simpl. lia. }
      rewrite Hm.
      unfold Qlt. simpl. lia.
    + (* 4 − 52/15 ≤ 4 − lp_four·lp_odd n *)
      apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat.
        setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
        setoid_replace (lp_four * (13 / 15)) with ((13 / 15) * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd n) (13 / 15) lp_four).
        -- apply QleT'_to_Qle. apply sc_lp_odd_le_s2.
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
Qed.
(* 批 7（轮 7）：cos 单调首证——cos(1) < 1 = cos(0) 与           *)
(*   cos(2) < cos(1)（π 几何化需 cos 在 (0,2) 递减的证据起点）   *)
(* ============================================================ *)

(* Q 层上界余量：n ≥ 2 ⟹ cos_partial n 1 < 1 − 1/10（cos n ≤ 13/24 + 1/60 == 67/120） *)
Lemma sc_cos_partial_ge2_one_upper : forall n : nat, (2 <= n)%nat ->
  QleT' (cos_partial n 1) (13 / 24 + 1 / 60).
Proof.
  intros n Hn.
  apply Qle_to_QleT'.
  assert (Hbound : Qle (Qabs (cos_partial n 1 - cos_partial 2 1))
                       ((q_pow 1 5 / q_fact 5) * (1 + 1))).
  { assert (Habs1eq : Qabs 1 == 1).
    { unfold Qabs. simpl. reflexivity. }
    apply QleT'_to_Qle. apply (sc_cos_diff_bound2 1 1 2 n).
    - unfold Qle; simpl; lia.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs1eq.
    - intros t Ht. unfold Qle; simpl; lia.
    - lia. }
  (* cos n ≤ cos 2 + |Δ|（Δ == cos n − cos 2） *)
  assert (Hle1 : Qle (cos_partial n 1)
                    (cos_partial 2 1 + Qabs (cos_partial n 1 - cos_partial 2 1))).
  { apply (Qle_trans _ (cos_partial 2 1 + (cos_partial n 1 - cos_partial 2 1)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qle_Qabs. }
  apply (Qle_trans _ (cos_partial 2 1 + ((q_pow 1 5 / q_fact 5) * (1 + 1))) _).
  - apply (Qle_trans _ (cos_partial 2 1 + Qabs (cos_partial n 1 - cos_partial 2 1)) _).
    + exact Hle1.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Hbound.
  - (* cos 2 1 + 1/60 == 13/24 + 1/60：具体值后 refl *)
    assert (Hval : cos_partial 2 1 == 13 / 24).
    { unfold Qeq. simpl. lia. }
    rewrite Hval.
    assert (Hv2 : (q_pow 1 5 / q_fact 5) * (1 + 1) == 1 / 60).
    { unfold Qeq. simpl. lia. }
    rewrite Hv2.
    apply Qle_refl.
Qed.

(* Real 层：cos(1) < 1 = cos(0) *)
Lemma real_cos_one_lt_one : real_lt (cauchy_real_cos (real_const 1)) real_one.
Proof.
  unfold real_lt.
  exists (1 / 10).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    (* 目标：1/10 < 1 − cos_partial n 1：链自 1 − (13/24 + 1/60) == 53/120 > 1/10 *)
    apply (Qlt_le_trans _ (1 - (13 / 24 + 1 / 60)) _).
    + (* 1/10 < 1 − 67/120 == 53/120：具体 *)
      unfold Qlt. simpl. lia.
    + (* 1 − 67/120 ≤ 1 − cos_partial n 1：cos n < 67/120 *)
      apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat.
        apply QleT'_to_Qle. apply sc_cos_partial_ge2_one_upper. apply NatLe_drop in Hn. lia.
Qed.

(* Real 层：cos(2) < cos(1)（经 real_zero 传递：cos 2 < 0 < cos 1） *)
Lemma real_cos_two_lt_one : real_lt (cauchy_real_cos (real_const 2)) (cauchy_real_cos (real_const 1)).
Proof.
  apply (real_lt_trans (cauchy_real_cos (real_const 2)) real_zero (cauchy_real_cos (real_const 1))).
  - exact real_cos_two_neg.
  - exact real_cos_one_pos.
Qed.
(* 批 8（轮 8）：π 推论束——π > 0、3 < π < 4 合取              *)
(* ============================================================ *)

Lemma real_zero_lt_three : real_lt real_zero (real_const 3).
Proof.
  unfold real_lt.
  exists (1 / 10).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 0%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    unfold Qlt. simpl. lia.
Qed.

(* π > 0（经 0 < 3 < π） *)
Lemma real_pi_leibniz_pos : real_lt real_zero cauchy_real_pi_leibniz.
Proof.
  apply (real_lt_trans real_zero (real_const 3) cauchy_real_pi_leibniz).
  - exact real_zero_lt_three.
  - exact real_pi_leibniz_gt_three.
Qed.

(* 夹逼合取：3 < π < 4（And := A*B，Set 层） *)
Lemma real_pi_leibniz_between : And (real_lt (real_const 3) cauchy_real_pi_leibniz)
                                    (real_lt cauchy_real_pi_leibniz (real_const 4)).
Proof.
  exact (real_pi_leibniz_gt_three, real_pi_leibniz_lt_four).
Qed.
(* 批 9（轮 9）：π/2 零点夹逼细化——cos(3/2) > 0 ∧ cos(5/3) < 0 *)
(*   cos 零点（π/2）变号括号 (1,2) → (3/2, 5/3)（宽 1/6）       *)
(*   模板：批 4/5 margin（diff_bound2 + 具体求值 + 组装）*)
(*   手算：cos(3/2) ≈ 0.0705 > 1/20；cos(5/3) ≈ −0.0951 < −1/100 *)
(* ============================================================ *)

Lemma sc_q_abs_3h : QeqT (Qabs (3 / 2)) (3 / 2).
Proof. apply qeq_imp_qeqT. apply Qabs_pos. unfold Qle; simpl; lia. Qed.

Lemma sc_q_abs_5t : QeqT (Qabs (5 / 3)) (5 / 3).
Proof. apply qeq_imp_qeqT. apply Qabs_pos. unfold Qle; simpl; lia. Qed.

(* Q 层：n ≥ 4 ⟹ 1/20 < cos_partial n (3/2)（cos(3/2) > 0 的余量） *)
Lemma sc_cos_partial_ge4_pos_3h : forall n : nat, (4 <= n)%nat ->
  QltT (1 / 20) (cos_partial n (3 / 2)).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  (* 界 1：|cos n (3/2) − cos 4 (3/2)| ≤ (3/2)^9/9!·2 *)
  assert (Hbound : Qle (Qabs (cos_partial n (3 / 2) - cos_partial 4 (3 / 2)))
                       ((q_pow (3 / 2) 9 / q_fact 9) * (1 + 1))).
  { apply QleT'_to_Qle. apply (sc_cos_diff_bound2 (3 / 2) (3 / 2) 4 n).
    - unfold Qle; simpl; lia.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_q_abs_3h)).
    - intros t Ht. unfold Qle; simpl; lia.
    - lia. }
  (* 界 2：cos 4 − |Δ| ≤ cos n *)
  assert (Hle2 : Qle (cos_partial 4 (3 / 2) + (- Qabs (cos_partial n (3 / 2) - cos_partial 4 (3 / 2))))
                     (cos_partial n (3 / 2))).
  { apply (Qle_trans _ (cos_partial 4 (3 / 2) + (cos_partial n (3 / 2) - cos_partial 4 (3 / 2))) _).
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply QleT'_to_Qle. apply sc_q_neg_abs_le.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  (* 组装：1/20 < cos 4 − 尾 ≤ cos n *)
  apply (Qlt_le_trans _ (cos_partial 4 (3 / 2) + (- ((q_pow (3 / 2) 9 / q_fact 9) * (1 + 1)))) _).
  - (* 1/20 < cos 4 (3/2) − (3/2)^9/9!·2（具体求值 == 40451/573440） *)
    unfold Qlt. simpl. lia.
  - apply (Qle_trans _ (cos_partial 4 (3 / 2) + (- Qabs (cos_partial n (3 / 2) - cos_partial 4 (3 / 2)))) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hbound.
    + exact Hle2.
Qed.

(* Q 层：n ≥ 4 ⟹ cos_partial n (5/3) < −1/100（cos(5/3) < 0 的余量） *)
Lemma sc_cos_partial_ge4_neg_5t : forall n : nat, (4 <= n)%nat ->
  QltT (cos_partial n (5 / 3)) (- (1 / 100)).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  (* 界 1：|cos n (5/3) − cos 4 (5/3)| ≤ (5/3)^9/9!·2 *)
  assert (Hbound : Qle (Qabs (cos_partial n (5 / 3) - cos_partial 4 (5 / 3)))
                       ((q_pow (5 / 3) 9 / q_fact 9) * (1 + 1))).
  { apply QleT'_to_Qle. apply (sc_cos_diff_bound2 (5 / 3) (5 / 3) 4 n).
    - unfold Qle; simpl; lia.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_q_abs_5t)).
    - intros t Ht. unfold Qle; simpl; lia.
    - lia. }
  (* 界 2：cos n ≤ cos 4 + |Δ| *)
  assert (Hle1 : Qle (cos_partial n (5 / 3))
                     (cos_partial 4 (5 / 3) + Qabs (cos_partial n (5 / 3) - cos_partial 4 (5 / 3)))).
  { apply (Qle_trans _ (cos_partial 4 (5 / 3) + (cos_partial n (5 / 3) - cos_partial 4 (5 / 3))) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qle_Qabs. }
  (* 组装：cos n ≤ cos 4 + 尾 < −1/100 *)
  apply (Qle_lt_trans _ (cos_partial 4 (5 / 3) + ((q_pow (5 / 3) 9 / q_fact 9) * (1 + 1))) _).
  - apply (Qle_trans _ (cos_partial 4 (5 / 3) + Qabs (cos_partial n (5 / 3) - cos_partial 4 (5 / 3))) _).
    + exact Hle1.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Hbound.
  - (* cos 4 (5/3) + (5/3)^9/9!·2 < −1/100（具体求值） *)
    unfold Qlt. simpl. lia.
Qed.

(* Real 层：cos(3/2) > 0 *)
Lemma real_cos_three_halves_pos : real_lt real_zero (cauchy_real_cos (real_const (3 / 2))).
Proof.
  unfold real_lt.
  exists (1 / 20).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 4%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Heq : cos_partial n (3 / 2) - 0 == cos_partial n (3 / 2)) by ring.
    rewrite Heq.
    apply QltT_to_Qlt. apply sc_cos_partial_ge4_pos_3h. apply NatLe_drop in Hn. lia.
Qed.

(* Real 层：cos(5/3) < 0 *)
Lemma real_cos_five_thirds_neg : real_lt (cauchy_real_cos (real_const (5 / 3))) real_zero.
Proof.
  unfold real_lt.
  exists (1 / 100).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 4%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Heq : 0 - cos_partial n (5 / 3) == - cos_partial n (5 / 3)) by ring.
    rewrite Heq.
    assert (Hlt : Qlt (cos_partial n (5 / 3)) (- (1 / 100))).
    { apply QltT_to_Qlt. apply sc_cos_partial_ge4_neg_5t. apply NatLe_drop in Hn. lia. }
    pose proof (proj1 (Qlt_minus_iff (cos_partial n (5 / 3)) (- (1 / 100))) Hlt) as Hm.
    assert (Hr : (- (1 / 100)) - cos_partial n (5 / 3) == (- cos_partial n (5 / 3)) - (1 / 100)) by ring.
    rewrite Hr in Hm.
    exact (proj2 (Qlt_minus_iff (1 / 100) (- cos_partial n (5 / 3))) Hm).
Qed.
(* ============================================================ *)
(* 批 10（轮 10）：sin/cos 交错余项夹逼（Q 层一阶界）           *)
(*   sin：0 ≤ x ≤ 1 ⟹ x − x³/6 ≤ sin_partial n x ≤ x            *)
(*   cos：0 ≤ x ≤ 1 ⟹ 1 − x²/2 ≤ cos_partial n x ≤ 1            *)
(*   路线：绝对项递减（pow_fact_mono 复用）→ 符号恒等 → 子列    *)
(*   单调（偶 ↓ 奇 ↑ / 偶 ↓ 奇 ↑ 配对）→ sc_nat_split 奇偶拆分  *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* ---- 绝对项：c_j := x^{2j+1}/(2j+1)!、c'_j := x^{2j}/(2j)! ---- *)
Definition sc_sin_alt (j : nat) (x : Q) : Q :=
  q_pow x (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)).

Definition sc_cos_alt (j : nat) (x : Q) : Q :=
  q_pow x (2 * j) / q_fact (2 * j).

(* ---- nat 奇偶拆分（Set 层信息性归纳） ---- *)
Inductive sc_parity (n : nat) : Set :=
| sc_par_even : forall m : nat, n = (2 * m)%nat -> sc_parity n
| sc_par_odd  : forall m : nat, n = Datatypes.S (2 * m)%nat -> sc_parity n.

Arguments sc_par_even {n} m pf.
Arguments sc_par_odd {n} m pf.

Lemma sc_double_succ : forall m : nat, Datatypes.S (Datatypes.S (2 * m)%nat) = (2 * Datatypes.S m)%nat.
Proof. intros m. lia. Qed.

Fixpoint sc_nat_split (n : nat) : sc_parity n :=
  match n with
  | 0%nat => sc_par_even 0%nat eq_refl
  | Datatypes.S p =>
      match sc_nat_split p with
      | sc_par_even m Hm => sc_par_odd m (f_equal Datatypes.S Hm)
      | sc_par_odd m Hm => sc_par_even (Datatypes.S m) (eq_trans (f_equal Datatypes.S Hm) (sc_double_succ m))
      end
  end.

(* ---- 2x ≤ 2 与 2x < 2j+2 / 2x < 2j+1（x ≤ 1 推论） ---- *)
Lemma sc_two_x_le_two : forall x : Q, Qle x 1 -> QleT' (Qmult (1 + 1)%Q x) (1 + 1).
Proof.
  intros x Hx1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (x * (1 + 1)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ ((1 + 1) * 1) _).
    + apply (Qmult_le_compat_r x 1 (1 + 1)).
      * exact Hx1.
      * unfold Qle; simpl; lia.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma sc_sin_alt_hlt : forall (x : Q) (j : nat), Qle x 1 -> (1 <= j)%nat ->
  QltT (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * j + 2)) 1).
Proof.
  intros x j Hx1 Hj.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (1 + 1) _).
  - apply QleT'_to_Qle. apply sc_two_x_le_two. exact Hx1.
  - unfold Qlt. simpl. lia.
Qed.

Lemma sc_cos_alt_hlt : forall (x : Q) (j : nat), Qle x 1 -> (1 <= j)%nat ->
  QltT (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * j + 1)) 1).
Proof.
  intros x j Hx1 Hj.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (1 + 1) _).
  - apply QleT'_to_Qle. apply sc_two_x_le_two. exact Hx1.
  - unfold Qlt. simpl. lia.
Qed.

(* ---- 绝对项递减（j ≥ 1）：c_{j+1} ≤ c_j ---- *)
Lemma sc_sin_alt_decr : forall (x : Q) (j : nat),
  Qle 0 x -> (1 <= j)%nat ->
  Qlt (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * j + 2)) 1) ->
  QleT' (sc_sin_alt (Datatypes.S j) x) (sc_sin_alt j x).
Proof.
  intros x j Hx0 Hj Hlt.
  apply Qle_to_QleT'.
  unfold sc_sin_alt.
  apply (Qle_trans _ (q_pow x (2 * Datatypes.S j) / q_fact (2 * Datatypes.S j)) _).
  - (* t_{S(2·S j)} ≤ t_{2·S j}：pow_fact_mono k = 2·S j *)
    apply QleT'_to_Qle; apply (pow_fact_mono x (2 * Datatypes.S j) (Qle_to_QleT' _ _ Hx0)).
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (Qmake (Z.of_nat (2 * j + 2)) 1) _).
    + exact Hlt.
    + unfold Qle. simpl. lia.
  - (* t_{2·S j} == t_{S(S(2j))} ≤ t_{S(2j)}：pow_fact_mono k = S(2j) *)
    replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j))) by lia.
    apply QleT'_to_Qle; apply (pow_fact_mono x (Datatypes.S (2 * j)) (Qle_to_QleT' _ _ Hx0)).
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (Qmake (Z.of_nat (2 * j + 2)) 1) _).
    + exact Hlt.
    + unfold Qle. simpl. lia.
Qed.

Lemma sc_cos_alt_decr : forall (x : Q) (j : nat),
  Qle 0 x -> (1 <= j)%nat ->
  Qlt (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * j + 1)) 1) ->
  QleT' (sc_cos_alt (Datatypes.S j) x) (sc_cos_alt j x).
Proof.
  intros x j Hx0 Hj Hlt.
  apply Qle_to_QleT'.
  unfold sc_cos_alt.
  apply (Qle_trans _ (q_pow x (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) _).
  - (* t_{2·S j} == t_{S(S(2j))} ≤ t_{S(2j)}：pow_fact_mono k = S(2j)（需 2x < 2j+2） *)
    replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j))) by lia.
    apply QleT'_to_Qle; apply (pow_fact_mono x (Datatypes.S (2 * j)) (Qle_to_QleT' _ _ Hx0)).
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (Qmake (Z.of_nat (2 * j + 1)) 1) _).
    + exact Hlt.
    + unfold Qle. simpl. lia.
  - (* t_{S(2j)} ≤ t_{2j}：pow_fact_mono k = 2·j（需 2x < 2j+1） *)
    apply QleT'_to_Qle; apply (pow_fact_mono x (2 * j) (Qle_to_QleT' _ _ Hx0)).
    apply Qlt_to_QltT. exact Hlt.
Qed.

(* ---- 绝对项非负 ---- *)
Lemma sc_sin_alt_nonneg : forall (j : nat) (x : Q), Qle 0 x -> QleT' 0 (sc_sin_alt j x).
Proof.  intros j x Hx0. unfold sc_sin_alt.
  exact (q_div_nonneg (q_pow x (Datatypes.S (2 * j))) (q_fact (Datatypes.S (2 * j)))
    (q_pow_nonneg x (Datatypes.S (2 * j)) (Qle_to_QleT' _ _ Hx0)) (q_fact_pos (Datatypes.S (2 * j)))).
Qed.

Lemma sc_cos_alt_nonneg : forall (j : nat) (x : Q), Qle 0 x -> QleT' 0 (sc_cos_alt j x).
Proof.  intros j x Hx0. unfold sc_cos_alt.
  exact (q_div_nonneg (q_pow x (2 * j)) (q_fact (2 * j))
    (q_pow_nonneg x (2 * j) (Qle_to_QleT' _ _ Hx0)) (q_fact_pos (2 * j))).
Qed.

(* ---- 符号因子辅助：q_pow (−1) 在奇/偶指标 ---- *)
Lemma sc_qpow_odd_neg_m : forall m : nat, QeqT (q_pow (-1) (Datatypes.S (2 * m)%nat)) (-1).
Proof.
  intros m.
  replace (Datatypes.S (2 * m)%nat) with (2 * m + 1)%nat by lia.
  exact (q_pow_neg1_odd m).
Qed.

Lemma sc_qpow_even_pos_m : forall m : nat, QeqT (q_pow (-1) (Datatypes.S (Datatypes.S (2 * m)%nat))) (1).
Proof.
  intros m.
  replace (Datatypes.S (Datatypes.S (2 * m)%nat)) with (2 * Datatypes.S m)%nat by lia.
  exact (q_pow_neg1_even (Datatypes.S m)).
Qed.

(* ---- sin_term 符号恒等：奇负偶正 ---- *)
Lemma sc_sin_term_odd_neg : forall (m : nat) (x : Q), QeqT (sin_term (Datatypes.S (2 * m)) x) (- sc_sin_alt (Datatypes.S (2 * m)) x).
Proof.
  intros m x. apply qeq_imp_qeqT. unfold sin_term, sc_sin_alt.
  rewrite (qeqT_imp_qeq _ _ (sc_qpow_odd_neg_m m)).
  ring.
Qed.

Lemma sc_sin_term_even_pos : forall (m : nat) (x : Q), QeqT (sin_term (Datatypes.S (Datatypes.S (2 * m))) x) (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x. apply qeq_imp_qeqT. unfold sin_term, sc_sin_alt.
  rewrite (qeqT_imp_qeq _ _ (sc_qpow_even_pos_m m)).
  ring.
Qed.

(* ---- cos_term 符号恒等 ---- *)
Lemma sc_cos_term_odd_neg : forall (m : nat) (x : Q), QeqT (cos_term (Datatypes.S (2 * m)) x) (- sc_cos_alt (Datatypes.S (2 * m)) x).
Proof.
  intros m x. apply qeq_imp_qeqT. unfold cos_term, sc_cos_alt.
  rewrite (qeqT_imp_qeq _ _ (sc_qpow_odd_neg_m m)).
  ring.
Qed.

Lemma sc_cos_term_even_pos : forall (m : nat) (x : Q), QeqT (cos_term (Datatypes.S (Datatypes.S (2 * m))) x) (sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x. apply qeq_imp_qeqT. unfold cos_term, sc_cos_alt.
  rewrite (qeqT_imp_qeq _ _ (sc_qpow_even_pos_m m)).
  ring.
Qed.

(* ---- 两步步进展开 ---- *)
Lemma sc_sin_partial_step2 : forall (n : nat) (x : Q), QeqT (sin_partial (Datatypes.S (Datatypes.S n)) x) (sin_partial n x + sin_term (Datatypes.S n) x + sin_term (Datatypes.S (Datatypes.S n)) x).
Proof.
  intros n x. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma sc_cos_partial_step2 : forall (n : nat) (x : Q), QeqT (cos_partial (Datatypes.S (Datatypes.S n)) x) (cos_partial n x + cos_term (Datatypes.S n) x + cos_term (Datatypes.S (Datatypes.S n)) x).
Proof.
  intros n x. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* ---- 端点值 ---- *)
Lemma sc_qinv_one : QeqT (Qinv 1) (1).
Proof. apply qeq_imp_qeqT. unfold Qinv. simpl. reflexivity. Qed.

Lemma sc_sin_partial_0_x : forall x : Q, QeqT (sin_partial 0 x) (x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  change (sin_term 0%nat x == x).
  unfold sin_term.
  simpl.
  unfold Qdiv.
  rewrite (Qmult_1_l ((x * 1) * Qinv (1 * 1))).
  rewrite (Qmult_1_r x).
  rewrite (Qmult_1_l 1).
  rewrite (qeqT_imp_qeq _ _ (sc_qinv_one)).
  rewrite (Qmult_1_r x).
  reflexivity.
Qed.

Lemma sc_sin_term1_x : forall x : Q, QeqT (sin_term 1 x) (- sc_sin_alt 1 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  exact (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg 0 x)).
Qed.

Lemma sc_cos_term1_x : forall x : Q, QeqT (cos_term 1 x) (- sc_cos_alt 1 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  exact (qeqT_imp_qeq _ _ (sc_cos_term_odd_neg 0 x)).
Qed.

Lemma sc_sin_partial_1_x : forall x : Q, QeqT (sin_partial 1 x) (x - sc_sin_alt 1 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  assert (Hstep : sin_partial 1 x == sin_partial 0 x + sin_term 1 x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_0_x x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term1_x x)).
  ring.
Qed.

Lemma sc_cos_partial_1_x : forall x : Q, QeqT (cos_partial 1 x) (1 - sc_cos_alt 1 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  assert (Hstep : cos_partial 1 x == cos_partial 0 x + cos_term 1 x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_zero_const x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term1_x x)).
  ring.
Qed.

(* ---- 子列单调：sin 偶 ↓ ---- *)
Lemma sc_sin_even_decr : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 ->
  QleT' (sin_partial (2 * Datatypes.S m) x) (sin_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_step2 (2 * m) x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg m x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_even_pos m x)).
  apply (proj2 (Qle_minus_iff (sin_partial (2 * m) x + (- sc_sin_alt (Datatypes.S (2 * m)) x) + sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x)
                              (sin_partial (2 * m) x))).
  assert (Heq : sin_partial (2 * m) x - (sin_partial (2 * m) x + (- sc_sin_alt (Datatypes.S (2 * m)) x) + sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x) ==
                sc_sin_alt (Datatypes.S (2 * m)) x - sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x) by ring.
  rewrite Heq.
  apply (proj1 (Qle_minus_iff (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x)
                              (sc_sin_alt (Datatypes.S (2 * m)) x))).
  apply QleT'_to_Qle. apply (sc_sin_alt_decr x (Datatypes.S (2 * m)) Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_sin_alt_hlt x (Datatypes.S (2 * m)) Hx1). lia.
Qed.

(* ---- 子列单调：sin 奇 ↑ ---- *)
Lemma sc_sin_odd_incr : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 ->
  QleT' (sin_partial (Datatypes.S (2 * m)) x) (sin_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_step2 (Datatypes.S (2 * m)) x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_even_pos m x)).
  replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat with (Datatypes.S (2 * Datatypes.S m))%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg (Datatypes.S m) x)).
  assert (Heq : sin_partial (Datatypes.S (2 * m)) x + sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x +
                (- sc_sin_alt (Datatypes.S (2 * Datatypes.S m)) x) ==
                sin_partial (Datatypes.S (2 * m)) x +
                (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x - sc_sin_alt (Datatypes.S (2 * Datatypes.S m)) x)) by ring.
  rewrite Heq.
  apply Qle_plus_nonneg_r.
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
  apply (proj1 (Qle_minus_iff (sc_sin_alt (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x)
                              (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x))).
  apply QleT'_to_Qle. apply (sc_sin_alt_decr x (Datatypes.S (Datatypes.S (2 * m))) Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_sin_alt_hlt x (Datatypes.S (Datatypes.S (2 * m))) Hx1). lia.
Qed.

(* ---- 混合：sin S(2m) ≤ sin 2m（奇在偶下）---- *)
Lemma sc_sin_mix_le : forall (m : nat) (x : Q),
  Qle 0 x -> QleT' (sin_partial (Datatypes.S (2 * m)) x) (sin_partial (2 * m) x).
Proof.
  intros m x Hx0.
  apply Qle_to_QleT'.
  assert (Hstep : sin_partial (Datatypes.S (2 * m)) x == sin_partial (2 * m) x + sin_term (Datatypes.S (2 * m)) x).
  { simpl. ring. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg m x)).
  apply (proj2 (Qle_minus_iff (sin_partial (2 * m) x + (- sc_sin_alt (Datatypes.S (2 * m)) x))
                              (sin_partial (2 * m) x))).
  assert (Heq : sin_partial (2 * m) x - (sin_partial (2 * m) x + (- sc_sin_alt (Datatypes.S (2 * m)) x)) ==
                sc_sin_alt (Datatypes.S (2 * m)) x) by ring.
  rewrite Heq.
  apply QleT'_to_Qle. apply sc_sin_alt_nonneg. exact Hx0.
Qed.

(* ---- 混合：sin S(S(2m)) ≥ sin S(2m)（偶在奇上） ---- *)
Lemma sc_sin_mix_ge : forall (m : nat) (x : Q),
  Qle 0 x -> QleT' (sin_partial (Datatypes.S (2 * m)) x) (sin_partial (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x Hx0.
  apply Qle_to_QleT'.
  assert (Hstep : sin_partial (Datatypes.S (Datatypes.S (2 * m))) x ==
                  sin_partial (Datatypes.S (2 * m)) x + sin_term (Datatypes.S (Datatypes.S (2 * m))) x).
  { simpl. ring. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_even_pos m x)).
  apply Qle_plus_nonneg_r.
  apply QleT'_to_Qle. apply sc_sin_alt_nonneg. exact Hx0.
Qed.

(* ---- 子列单调：cos 偶 ↓ ---- *)
Lemma sc_cos_even_decr : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 ->
  QleT' (cos_partial (2 * Datatypes.S m) x) (cos_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_step2 (2 * m) x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term_odd_neg m x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term_even_pos m x)).
  apply (proj2 (Qle_minus_iff (cos_partial (2 * m) x + (- sc_cos_alt (Datatypes.S (2 * m)) x) + sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x)
                              (cos_partial (2 * m) x))).
  assert (Heq : cos_partial (2 * m) x - (cos_partial (2 * m) x + (- sc_cos_alt (Datatypes.S (2 * m)) x) + sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x) ==
                sc_cos_alt (Datatypes.S (2 * m)) x - sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x) by ring.
  rewrite Heq.
  apply (proj1 (Qle_minus_iff (sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x)
                              (sc_cos_alt (Datatypes.S (2 * m)) x))).
  apply QleT'_to_Qle. apply (sc_cos_alt_decr x (Datatypes.S (2 * m)) Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_cos_alt_hlt x (Datatypes.S (2 * m)) Hx1). lia.
Qed.

(* ---- 子列单调：cos 奇 ↑ ---- *)
Lemma sc_cos_odd_incr : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 ->
  QleT' (cos_partial (Datatypes.S (2 * m)) x) (cos_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_step2 (Datatypes.S (2 * m)) x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term_even_pos m x)).
  replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat with (Datatypes.S (2 * Datatypes.S m))%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term_odd_neg (Datatypes.S m) x)).
  assert (Heq : cos_partial (Datatypes.S (2 * m)) x + sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x +
                (- sc_cos_alt (Datatypes.S (2 * Datatypes.S m)) x) ==
                cos_partial (Datatypes.S (2 * m)) x +
                (sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x - sc_cos_alt (Datatypes.S (2 * Datatypes.S m)) x)) by ring.
  rewrite Heq.
  apply Qle_plus_nonneg_r.
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
  apply (proj1 (Qle_minus_iff (sc_cos_alt (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x)
                              (sc_cos_alt (Datatypes.S (Datatypes.S (2 * m))) x))).
  apply QleT'_to_Qle. apply (sc_cos_alt_decr x (Datatypes.S (Datatypes.S (2 * m))) Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_cos_alt_hlt x (Datatypes.S (Datatypes.S (2 * m))) Hx1). lia.
Qed.

(* ---- 混合：cos S(2m) ≤ cos 2m（奇在偶下） ---- *)
Lemma sc_cos_mix_le : forall (m : nat) (x : Q),
  Qle 0 x -> QleT' (cos_partial (Datatypes.S (2 * m)) x) (cos_partial (2 * m) x).
Proof.
  intros m x Hx0.
  apply Qle_to_QleT'.
  assert (Hstep : cos_partial (Datatypes.S (2 * m)) x == cos_partial (2 * m) x + cos_term (Datatypes.S (2 * m)) x).
  { simpl. ring. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term_odd_neg m x)).
  apply (proj2 (Qle_minus_iff (cos_partial (2 * m) x + (- sc_cos_alt (Datatypes.S (2 * m)) x))
                              (cos_partial (2 * m) x))).
  assert (Heq : cos_partial (2 * m) x - (cos_partial (2 * m) x + (- sc_cos_alt (Datatypes.S (2 * m)) x)) ==
                sc_cos_alt (Datatypes.S (2 * m)) x) by ring.
  rewrite Heq.
  apply QleT'_to_Qle. apply sc_cos_alt_nonneg. exact Hx0.
Qed.

(* ---- 混合：cos S(S(2m)) ≥ cos S(2m)（偶在奇上） ---- *)
Lemma sc_cos_mix_ge : forall (m : nat) (x : Q),
  Qle 0 x -> QleT' (cos_partial (Datatypes.S (2 * m)) x) (cos_partial (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x Hx0.
  apply Qle_to_QleT'.
  assert (Hstep : cos_partial (Datatypes.S (Datatypes.S (2 * m))) x ==
                  cos_partial (Datatypes.S (2 * m)) x + cos_term (Datatypes.S (Datatypes.S (2 * m))) x).
  { simpl. ring. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term_even_pos m x)).
  apply Qle_plus_nonneg_r.
  apply QleT'_to_Qle. apply sc_cos_alt_nonneg. exact Hx0.
Qed.

(* ==================== 归纳链 ==================== *)
(* sin 偶子列 ≤ x *)
Lemma sc_sin_even_le_x : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (sin_partial (2 * m) x) x.
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (2 * 0)%nat with 0%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_0_x x)).
    apply Qle_refl.
  - apply Qle_to_QleT'. apply (Qle_trans _ (sin_partial (2 * m') x) _).
    + apply QleT'_to_Qle. apply sc_sin_even_decr. exact Hx0. exact Hx1.
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* sin 奇子列 ≥ x − c1 *)
Lemma sc_sin_odd_ge_c1 : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (x - sc_sin_alt 1 x) (sin_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (Datatypes.S (2 * 0)) with 1%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_1_x x)).
    apply Qle_refl.
  - apply Qle_to_QleT'. replace (Datatypes.S (2 * Datatypes.S m'))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))%nat by lia.
    apply (Qle_trans _ (sin_partial (Datatypes.S (2 * m')) x) _).
    + exact (QleT'_to_Qle _ _ IH).
    + apply QleT'_to_Qle. apply sc_sin_odd_incr. exact Hx0. exact Hx1.
Qed.

(* cos 偶子列 ≤ 1 *)
Lemma sc_cos_even_le_one : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (cos_partial (2 * m) x) 1.
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (2 * 0)%nat with 0%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_zero_const x)).
    apply Qle_refl.
  - apply Qle_to_QleT'. apply (Qle_trans _ (cos_partial (2 * m') x) _).
    + apply QleT'_to_Qle. apply sc_cos_even_decr. exact Hx0. exact Hx1.
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* cos 奇子列 ≥ 1 − c'_1 *)
Lemma sc_cos_odd_ge_c1 : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (1 - sc_cos_alt 1 x) (cos_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (Datatypes.S (2 * 0)) with 1%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_1_x x)).
    apply Qle_refl.
  - apply Qle_to_QleT'. replace (Datatypes.S (2 * Datatypes.S m'))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))%nat by lia.
    apply (Qle_trans _ (cos_partial (Datatypes.S (2 * m')) x) _).
    + exact (QleT'_to_Qle _ _ IH).
    + apply QleT'_to_Qle. apply sc_cos_odd_incr. exact Hx0. exact Hx1.
Qed.

(* ==================== 最终夹逼（∀n） ==================== *)
(* sin：sin_partial n x ≤ x *)
Lemma sc_sin_partial_upper_x : forall (n : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (sin_partial n x) x.
Proof.
  intros n x Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. rewrite Hm. apply QleT'_to_Qle. apply sc_sin_even_le_x. exact Hx0. exact Hx1.
  - apply Qle_to_QleT'. apply (Qle_trans _ (sin_partial (2 * m) x) _).
    + rewrite Hm. apply QleT'_to_Qle. apply sc_sin_mix_le. exact Hx0.
    + apply QleT'_to_Qle. apply sc_sin_even_le_x. exact Hx0. exact Hx1.
Qed.

(* sin：x − x³/6 ≤ sin_partial n x *)
Lemma sc_sin_partial_lower_c1 : forall (n : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (x - sc_sin_alt 1 x) (sin_partial n x).
Proof.
  intros n x Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. destruct m as [| m'].
    + rewrite Hm.
      replace (2 * 0)%nat with 0%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_0_x x)).
      apply (proj2 (Qle_minus_iff (x - sc_sin_alt 1 x) x)).
      assert (Heq : x - (x - sc_sin_alt 1 x) == sc_sin_alt 1 x) by ring.
      rewrite Heq.
      apply QleT'_to_Qle. apply sc_sin_alt_nonneg. exact Hx0.
    + apply (Qle_trans _ (sin_partial (Datatypes.S (2 * m')) x) _).
      * apply QleT'_to_Qle. apply sc_sin_odd_ge_c1. exact Hx0. exact Hx1.
      * rewrite Hm.
        replace (2 * Datatypes.S m')%nat with (Datatypes.S (Datatypes.S (2 * m'))) by lia.
        apply QleT'_to_Qle. apply sc_sin_mix_ge. exact Hx0.
  - apply Qle_to_QleT'. rewrite Hm. apply QleT'_to_Qle. apply sc_sin_odd_ge_c1. exact Hx0. exact Hx1.
Qed.

(* cos：cos_partial n x ≤ 1 *)
Lemma sc_cos_partial_upper_one : forall (n : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (cos_partial n x) 1.
Proof.
  intros n x Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. rewrite Hm. apply QleT'_to_Qle. apply sc_cos_even_le_one. exact Hx0. exact Hx1.
  - apply Qle_to_QleT'. apply (Qle_trans _ (cos_partial (2 * m) x) _).
    + rewrite Hm. apply QleT'_to_Qle. apply sc_cos_mix_le. exact Hx0.
    + apply QleT'_to_Qle. apply sc_cos_even_le_one. exact Hx0. exact Hx1.
Qed.

(* cos：1 − x²/2 ≤ cos_partial n x *)
Lemma sc_cos_partial_lower_c1 : forall (n : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (1 - sc_cos_alt 1 x) (cos_partial n x).
Proof.
  intros n x Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. destruct m as [| m'].
    + rewrite Hm.
      replace (2 * 0)%nat with 0%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_zero_const x)).
      apply (proj2 (Qle_minus_iff (1 - sc_cos_alt 1 x) 1)).
      assert (Heq : 1 - (1 - sc_cos_alt 1 x) == sc_cos_alt 1 x) by ring.
      rewrite Heq.
      apply QleT'_to_Qle. apply sc_cos_alt_nonneg. exact Hx0.
    + apply (Qle_trans _ (cos_partial (Datatypes.S (2 * m')) x) _).
      * apply QleT'_to_Qle. apply sc_cos_odd_ge_c1. exact Hx0. exact Hx1.
      * rewrite Hm.
        replace (2 * Datatypes.S m')%nat with (Datatypes.S (Datatypes.S (2 * m'))) by lia.
        apply QleT'_to_Qle. apply sc_cos_mix_ge. exact Hx0.
  - apply Qle_to_QleT'. rewrite Hm. apply QleT'_to_Qle. apply sc_cos_odd_ge_c1. exact Hx0. exact Hx1.
Qed.

(* ============================================================ *)
(* 批 11（轮 11）：Q 层差分一阶界族——Real 层一阶界前置        *)
(*   sin ≤ S_2、cos ≤ C_2（n ≥ 2）→ 差分下界：                  *)
(*   x − sin_partial n x ≥ x³/6 − x⁵/120（n ≥ 2）               *)
(*   1 − cos_partial n x ≥ x²/2 − x⁴/24（n ≥ 2）                *)
(*   另：q_pow 三次严格单调（Real 组装用）                       *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* ---- 二阶部分和求值 ---- *)
Lemma sc_sin_term2_x : forall x : Q, QeqT (sin_term 2 x) (sc_sin_alt 2 x).
Proof.
  intro x. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_sin_term_even_pos 0 x)).
Qed.

Lemma sc_cos_term2_x : forall x : Q, QeqT (cos_term 2 x) (sc_cos_alt 2 x).
Proof.
  intro x. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_cos_term_even_pos 0 x)).
Qed.

Lemma sc_sin_partial_2_val : forall x : Q, QeqT (sin_partial 2 x) (x - sc_sin_alt 1 x + sc_sin_alt 2 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  assert (Hstep : sin_partial 2 x == sin_partial 1 x + sin_term 2 x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_1_x x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term2_x x)).
  ring.
Qed.

Lemma sc_cos_partial_2_val : forall x : Q, QeqT (cos_partial 2 x) (1 - sc_cos_alt 1 x + sc_cos_alt 2 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  assert (Hstep : cos_partial 2 x == cos_partial 1 x + cos_term 2 x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_1_x x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term2_x x)).
  ring.
Qed.

(* ---- c 项二阶 ≤ 一阶（decr 直接） ---- *)
Lemma sc_sin_c2_le_c1 : forall x : Q, Qle 0 x -> Qle x 1 -> QleT' (sc_sin_alt 2 x) (sc_sin_alt 1 x).
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (sc_sin_alt_decr x 1 Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_sin_alt_hlt x 1 Hx1). lia.
Qed.

Lemma sc_cos_c2_le_c1 : forall x : Q, Qle 0 x -> Qle x 1 -> QleT' (sc_cos_alt 2 x) (sc_cos_alt 1 x).
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (sc_cos_alt_decr x 1 Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_cos_alt_hlt x 1 Hx1). lia.
Qed.

(* ---- 偶子列 ≤ 二阶部分和（链） ---- *)
Lemma sc_sin_even_le2_aux : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (sin_partial (2 * Datatypes.S m) x) (sin_partial 2 x).
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (2 * Datatypes.S 0)%nat with 2%nat by lia.
    apply Qle_refl.
  - apply Qle_to_QleT'. apply (Qle_trans _ (sin_partial (2 * Datatypes.S m') x) _).
    + apply QleT'_to_Qle. apply sc_sin_even_decr. exact Hx0. exact Hx1.
    + exact (QleT'_to_Qle _ _ IH).
Qed.

Lemma sc_cos_even_le2_aux : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> QleT' (cos_partial (2 * Datatypes.S m) x) (cos_partial 2 x).
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (2 * Datatypes.S 0)%nat with 2%nat by lia.
    apply Qle_refl.
  - apply Qle_to_QleT'. apply (Qle_trans _ (cos_partial (2 * Datatypes.S m') x) _).
    + apply QleT'_to_Qle. apply sc_cos_even_decr. exact Hx0. exact Hx1.
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* ---- 全局（n ≥ 2）≤ 二阶部分和 ---- *)
Lemma sc_sin_le_s2_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 -> QleT' (sin_partial n x) (sin_partial 2 x).
Proof.
  intros n x Hn Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + rewrite Hm.
      apply QleT'_to_Qle. apply (sc_sin_even_le2_aux m' x Hx0 Hx1).
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + rewrite Hm.
      apply (Qle_trans _ (sin_partial (2 * Datatypes.S m') x) _).
      * apply QleT'_to_Qle. apply sc_sin_mix_le. exact Hx0.
      * apply QleT'_to_Qle. apply (sc_sin_even_le2_aux m' x Hx0 Hx1).
Qed.

Lemma sc_cos_le_c2_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 -> QleT' (cos_partial n x) (cos_partial 2 x).
Proof.
  intros n x Hn Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + rewrite Hm.
      apply QleT'_to_Qle. apply (sc_cos_even_le2_aux m' x Hx0 Hx1).
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + rewrite Hm.
      apply (Qle_trans _ (cos_partial (2 * Datatypes.S m') x) _).
      * apply QleT'_to_Qle. apply sc_cos_mix_le. exact Hx0.
      * apply QleT'_to_Qle. apply (sc_cos_even_le2_aux m' x Hx0 Hx1).
Qed.

(* ---- 差分下界：x − sin ≥ c1 − c2（n ≥ 2） ---- *)
Lemma sc_sin_diff_lower_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' (sc_sin_alt 1 x - sc_sin_alt 2 x) (x - sin_partial n x).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (proj2 (Qle_minus_iff (sc_sin_alt 1 x - sc_sin_alt 2 x) (x - sin_partial n x))).
  assert (Hle : Qle (sin_partial n x) (sin_partial 2 x)).
  { apply QleT'_to_Qle. apply sc_sin_le_s2_ge2. exact Hn. exact Hx0. exact Hx1. }
  pose proof (proj1 (Qle_minus_iff (sin_partial n x) (sin_partial 2 x)) Hle) as Hm.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_2_val x)) in Hm.
  assert (Heq2 : (x - sc_sin_alt 1 x + sc_sin_alt 2 x) - sin_partial n x ==
                 (x - sin_partial n x) - (sc_sin_alt 1 x - sc_sin_alt 2 x)) by ring.
  rewrite Heq2 in Hm.
  exact Hm.
Qed.

(* ---- 差分下界：1 − cos ≥ c'_1 − c'_2（n ≥ 2） ---- *)
Lemma sc_cos_diff_lower_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' (sc_cos_alt 1 x - sc_cos_alt 2 x) (1 - cos_partial n x).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (proj2 (Qle_minus_iff (sc_cos_alt 1 x - sc_cos_alt 2 x) (1 - cos_partial n x))).
  assert (Hle : Qle (cos_partial n x) (cos_partial 2 x)).
  { apply QleT'_to_Qle. apply sc_cos_le_c2_ge2. exact Hn. exact Hx0. exact Hx1. }
  pose proof (proj1 (Qle_minus_iff (cos_partial n x) (cos_partial 2 x)) Hle) as Hm.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_2_val x)) in Hm.
  assert (Heq2 : (1 - sc_cos_alt 1 x + sc_cos_alt 2 x) - cos_partial n x ==
                 (1 - cos_partial n x) - (sc_cos_alt 1 x - sc_cos_alt 2 x)) by ring.
  rewrite Heq2 in Hm.
  exact Hm.
Qed.

(* ---- q_pow 三次严格单调：0 < a < b → a³ < b³ ---- *)
Lemma sc_qmul_lt_l : forall x y z : Q, Qlt 0 x -> Qlt y z -> QltT (x * y) (x * z).
Proof.
intros x y z Hx Hyz. apply Qlt_to_QltT. rewrite (Qmult_comm x y). rewrite (Qmult_comm x z). exact (Qmult_lt_compat_r y z x Hx Hyz).
Qed.

Lemma sc_qpow3_lt : forall a b : Q, Qlt 0 a -> Qlt a b -> QltT (q_pow a 3) (q_pow b 3).
Proof.
  intros a b Ha0 Hab.
  apply Qlt_to_QltT.
  assert (Ha3 : q_pow a 3 == a * a * a) by (unfold q_pow; simpl; ring).
  assert (Hb3 : q_pow b 3 == b * b * b) by (unfold q_pow; simpl; ring).
  rewrite Ha3, Hb3.
  assert (Hb0 : Qlt 0 b) by (apply (Qlt_trans _ a _); [exact Ha0 | exact Hab]).
  assert (Haa_bb : Qlt (a * a) (b * b)).
  { apply (Qlt_trans _ (b * a) _).
    - apply (Qmult_lt_compat_r a b a). exact Ha0. exact Hab.
    - apply QltT_to_Qlt. apply (sc_qmul_lt_l b a b Hb0). exact Hab. }
  assert (Hbb0 : Qlt 0 (b * b)) by (apply Qmult_lt_0_compat; [exact Hb0 | exact Hb0]).
  apply (Qlt_trans _ ((b * b) * a) _).
  - apply (Qmult_lt_compat_r (a * a) (b * b) a). exact Ha0. exact Haa_bb.
  - apply QltT_to_Qlt. apply (sc_qmul_lt_l (b * b) a b Hbb0). exact Hab.
Qed.
(* ============================================================ *)
(* 批 12（轮 12）：sin Real 层一阶界——Q 层差分补充 + Real 组装 *)
(*   Q：q_pow 降幂/升幂单调、S_3 求值与链、三次/五次差分下界     *)
(*   Real：0 < X < 1 → sin X < X、X − X³/6 < sin X               *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Lemma sc_qpow_dec : forall (x : Q) (m : nat), Qle 0 x -> Qle x 1 ->
  QleT' (q_pow x (Datatypes.S m)) (q_pow x m).
Proof.
intros x m Hx0 Hx1. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (q_pow_succ x m)). exact (Qle_trans (x * q_pow x m) (1 * q_pow x m) (q_pow x m) (Qmult_le_compat_r x 1 (q_pow x m) Hx1 (QleT'_to_Qle _ _ (q_pow_nonneg x m (Qle_to_QleT' _ _ Hx0)))) (QleT'_to_Qle _ _ (qeq_le (1 * q_pow x m) (q_pow x m) (qeq_imp_qeqT _ _ (Qmult_1_l (q_pow x m)))))).
Qed.

(* ---- q_pow 正 ---- *)
Lemma sc_qpow_pos : forall (n : nat) (y : Q), Qlt 0 y -> QltT 0 (q_pow y n).
Proof.
  intros n y Hy0.
  induction n as [| n' IH].
  - apply Qlt_to_QltT. replace (q_pow y 0) with 1%Q by reflexivity.
    unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. rewrite (qeqT_imp_qeq _ _ (q_pow_succ y n')).
    apply Qmult_lt_0_compat; [exact Hy0 | exact (QltT_to_Qlt _ _ IH)].
Qed.

(* ---- q_pow 严格升幂（0 ≤ x < y，n ≥ 1）：x^n < y^n ---- *)
Lemma sc_qpow_lt : forall (n : nat) (x y : Q),
  Qle 0 x -> Qlt x y -> (1 <= n)%nat -> QltT (q_pow x n) (q_pow y n).
Proof.
  intros n x y Hx0 Hxy Hn.
  induction n as [| n' IH].
  - apply Qlt_to_QltT. lia.
  - apply Qlt_to_QltT. destruct n' as [| n''].
    + assert (Hx1 : q_pow x 1 == x) by (unfold q_pow; simpl; ring).
      assert (Hy1 : q_pow y 1 == y) by (unfold q_pow; simpl; ring).
      rewrite Hx1, Hy1.
      exact Hxy.
    + rewrite (qeqT_imp_qeq _ _ (q_pow_succ x (Datatypes.S n''))).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ y (Datatypes.S n''))).
      assert (Hmid : Qlt (q_pow x (Datatypes.S n'')) (q_pow y (Datatypes.S n''))).
        { rewrite (qeqT_imp_qeq _ _ (q_pow_succ x n'')). rewrite (qeqT_imp_qeq _ _ (q_pow_succ y n'')).
        apply QltT_to_Qlt. apply IH. lia. }
      assert (Hy0 : Qlt 0 y) by (apply (Qle_lt_trans 0 x y Hx0 Hxy)).
      apply (Qle_lt_trans _ (x * q_pow y (Datatypes.S n'')) _).
      * rewrite (Qmult_comm x (q_pow x (Datatypes.S n''))).
        rewrite (Qmult_comm x (q_pow y (Datatypes.S n''))).
        apply (Qmult_le_compat_r (q_pow x (Datatypes.S n'')) (q_pow y (Datatypes.S n'')) x).
        -- apply (Qlt_le_weak (q_pow x (Datatypes.S n'')) (q_pow y (Datatypes.S n''))). exact Hmid.
        -- exact Hx0.
      * apply (Qmult_lt_compat_r x y (q_pow y (Datatypes.S n''))).
        -- apply QltT_to_Qlt. apply sc_qpow_pos. exact Hy0.
        -- exact Hxy.
Qed.

(* ---- S_3 求值：sin_term 3 与 sin_partial 3 ---- *)
Lemma sc_sin_term3_x : forall x : Q, QeqT (sin_term 3 x) (- sc_sin_alt 3 x).
Proof.
  intro x. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg 1 x)).
Qed.

Lemma sc_sin_partial_3_val : forall x : Q, QeqT (sin_partial 3 x) (x - sc_sin_alt 1 x + sc_sin_alt 2 x - sc_sin_alt 3 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  assert (Hstep : sin_partial 3 x == sin_partial 2 x + sin_term 3 x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_2_val x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term3_x x)).
  ring.
Qed.

(* ---- S_3 ≤ S_2 ---- *)
Lemma sc_sin_s3_le_s2 : forall x : Q, Qle 0 x -> QleT' (sin_partial 3 x) (sin_partial 2 x).
Proof.
  intros x Hx0.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_3_val x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_2_val x)).
  apply (proj2 (Qle_minus_iff (x - sc_sin_alt 1 x + sc_sin_alt 2 x - sc_sin_alt 3 x)
                              (x - sc_sin_alt 1 x + sc_sin_alt 2 x))).
  assert (Heq : (x - sc_sin_alt 1 x + sc_sin_alt 2 x) -
                (x - sc_sin_alt 1 x + sc_sin_alt 2 x - sc_sin_alt 3 x) ==
                sc_sin_alt 3 x) by ring.
  rewrite Heq.
  apply QleT'_to_Qle. apply sc_sin_alt_nonneg. exact Hx0.
Qed.

(* ---- 奇子列 ≥ S_3（m ≥ 1） ---- *)
Lemma sc_sin_odd_ge3 : forall (m : nat) (x : Q),
  (1 <= m)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' (sin_partial 3 x) (sin_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hm Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. lia.
  - apply Qle_to_QleT'. destruct m' as [| m''].
    + replace (Datatypes.S (2 * Datatypes.S 0))%nat with 3%nat by lia.
      apply Qle_refl.
    + apply (Qle_trans _ (sin_partial (Datatypes.S (2 * Datatypes.S m'')) x) _).
      * apply QleT'_to_Qle. apply IH. lia.
      * replace (Datatypes.S (2 * Datatypes.S (Datatypes.S m'')))%nat with
                 (Datatypes.S (Datatypes.S (Datatypes.S (2 * Datatypes.S m''))))%nat by lia.
        apply QleT'_to_Qle. apply sc_sin_odd_incr. exact Hx0. exact Hx1.
Qed.

(* ---- n ≥ 2 → sin_partial n x ≥ S_3 ---- *)
Lemma sc_sin_ge_s3_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 -> QleT' (sin_partial 3 x) (sin_partial n x).
Proof.
  intros n x Hn Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + destruct m' as [| m''].
      * rewrite Hm.
        replace (2 * Datatypes.S 0)%nat with 2%nat by lia.
        apply QleT'_to_Qle. apply sc_sin_s3_le_s2. exact Hx0.
      * rewrite Hm.
        apply (Qle_trans _ (sin_partial (Datatypes.S (2 * Datatypes.S m'')) x) _).
        -- apply QleT'_to_Qle. apply sc_sin_odd_ge3. lia. exact Hx0. exact Hx1.
        -- replace (2 * Datatypes.S (Datatypes.S m''))%nat with
                   (Datatypes.S (Datatypes.S (2 * Datatypes.S m'')))%nat by lia.
           apply QleT'_to_Qle. apply sc_sin_mix_ge. exact Hx0.
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + rewrite Hm.
      apply QleT'_to_Qle. apply sc_sin_odd_ge3. lia. exact Hx0. exact Hx1.
Qed.

(* ---- 下界差分：sin − (x − c1) ≥ c2 − c3（n ≥ 2） ---- *)
Lemma sc_sin_lower_diff_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' (sc_sin_alt 2 x - sc_sin_alt 3 x) (sin_partial n x - (x - sc_sin_alt 1 x)).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (proj2 (Qle_minus_iff (sc_sin_alt 2 x - sc_sin_alt 3 x)
                              (sin_partial n x - (x - sc_sin_alt 1 x)))).
  assert (Hge : Qle (sin_partial 3 x) (sin_partial n x)).
  { apply QleT'_to_Qle. apply sc_sin_ge_s3_ge2. exact Hn. exact Hx0. exact Hx1. }
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_3_val x)) in Hge.
  pose proof (proj1 (Qle_minus_iff (x - sc_sin_alt 1 x + sc_sin_alt 2 x - sc_sin_alt 3 x)
                                   (sin_partial n x)) Hge) as Hm.
  assert (Heq2 : sin_partial n x - (x - sc_sin_alt 1 x + sc_sin_alt 2 x - sc_sin_alt 3 x) ==
                 (sin_partial n x - (x - sc_sin_alt 1 x)) - (sc_sin_alt 2 x - sc_sin_alt 3 x)) by ring.
  rewrite Heq2 in Hm.
  exact Hm.
Qed.

(* ---- c 求值：c1 == x³/6、c2 == x⁵/120、c3 == x⁷/5040 ---- *)
Lemma sc_sin_alt1_cube : forall x : Q, QeqT (sc_sin_alt 1 x) (q_pow x 3 / 6).
Proof.
  intro x. apply qeq_imp_qeqT. unfold sc_sin_alt.
  replace (Datatypes.S (2 * 1))%nat with 3%nat by lia.
  assert (Hf : q_fact 3 == 6) by (unfold Qeq; simpl; lia).
  rewrite Hf. reflexivity.
Qed.

Lemma sc_sin_alt2_five : forall x : Q, QeqT (sc_sin_alt 2 x) (q_pow x 5 / 120).
Proof.
  intro x. apply qeq_imp_qeqT. unfold sc_sin_alt.
  replace (Datatypes.S (2 * 2))%nat with 5%nat by lia.
  assert (Hf : q_fact 5 == 120) by (unfold Qeq; simpl; lia).
  rewrite Hf. reflexivity.
Qed.

Lemma sc_sin_alt3_seven : forall x : Q, QeqT (sc_sin_alt 3 x) (q_pow x 7 / 5040).
Proof.
  intro x. apply qeq_imp_qeqT. unfold sc_sin_alt.
  replace (Datatypes.S (2 * 3))%nat with 7%nat by lia.
  assert (Hf : q_fact 7 == 5040) by (unfold Qeq; simpl; lia).
  rewrite Hf. reflexivity.
Qed.

(* ---- 上界差分三次下界：x − sin ≥ x³·19/120（n ≥ 2） ---- *)
Lemma sc_sin_upper_diff_cube_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' ((q_pow x 3) * (19 / 120)) (x - sin_partial n x).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  assert (Hd : Qle (sc_sin_alt 1 x - sc_sin_alt 2 x) (x - sin_partial n x)).
  { apply QleT'_to_Qle. apply sc_sin_diff_lower_ge2. exact Hn. exact Hx0. exact Hx1. }
  rewrite (qeqT_imp_qeq _ _ (sc_sin_alt1_cube x)) in Hd.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_alt2_five x)) in Hd.
  assert (Hx5 : Qle (q_pow x 5) (q_pow x 3)).
  { apply (Qle_trans _ (q_pow x 4) _).
    - apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1.
    - apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1. }
  assert (Hd2 : Qle (q_pow x 5 / 120) (q_pow x 3 / 120)).
  { apply QleT'_to_Qle; apply (Qle_div_same_denom (q_pow x 5) (q_pow x 3) 120).
    - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
    - apply Qle_to_QleT'. exact Hx5. }
  assert (Heq : q_pow x 3 / 6 - q_pow x 3 / 120 == (q_pow x 3) * (19 / 120)).
  { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
  apply (Qle_trans _ (q_pow x 3 / 6 - q_pow x 5 / 120) _).
  - apply (Qle_trans _ (q_pow x 3 / 6 - q_pow x 3 / 120) _).
    + rewrite <- Heq. apply Qle_refl.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hd2.
  - exact Hd.
Qed.

(* ---- 下界差分五次：sin − (x − x³/6) ≥ x⁵·41/5040（n ≥ 2） ---- *)
Lemma sc_sin_lower_diff_q5_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' ((q_pow x 5) * (41 / 5040)) (sin_partial n x - (x - q_pow x 3 / 6)).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  assert (Hs : sin_partial n x - (x - q_pow x 3 / 6) ==
               sin_partial n x - (x - sc_sin_alt 1 x)).
  { rewrite (qeqT_imp_qeq _ _ (sc_sin_alt1_cube x)). ring. }
  rewrite Hs.
  assert (Hd : Qle (sc_sin_alt 2 x - sc_sin_alt 3 x)
                   (sin_partial n x - (x - sc_sin_alt 1 x))).
  { apply QleT'_to_Qle. apply sc_sin_lower_diff_ge2. exact Hn. exact Hx0. exact Hx1. }
  assert (Hc23 : sc_sin_alt 2 x - sc_sin_alt 3 x ==
                 q_pow x 5 / 120 - q_pow x 7 / 5040).
  { rewrite (qeqT_imp_qeq _ _ (sc_sin_alt2_five x)). rewrite (qeqT_imp_qeq _ _ (sc_sin_alt3_seven x)). reflexivity. }
  rewrite Hc23 in Hd.
  apply (Qle_trans _ (q_pow x 5 / 120 - q_pow x 7 / 5040) _).
  - assert (Hx7 : Qle (q_pow x 7) (q_pow x 5)).
    { apply (Qle_trans _ (q_pow x 6) _).
      - apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1.
      - apply (Qle_trans _ (q_pow x 5) _).
        + apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1.
        + apply Qle_refl. }
    assert (Hd2 : Qle (q_pow x 7 / 5040) (q_pow x 5 / 5040)).
    { apply QleT'_to_Qle; apply (Qle_div_same_denom (q_pow x 7) (q_pow x 5) 5040).
      - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
      - apply Qle_to_QleT'. exact Hx7. }
    assert (Heq : q_pow x 5 / 120 - q_pow x 5 / 5040 == (q_pow x 5) * (41 / 5040)).
    { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
    apply (Qle_trans _ (q_pow x 5 / 120 - q_pow x 5 / 5040) _).
    + rewrite <- Heq. apply Qle_refl.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hd2.
  - exact Hd.
Qed.

(* ---- x³/6 与 x·(x·x)·(1/6) 形态桥 ---- *)
Lemma sc_qpow3_6form : forall x : Q, QeqT (q_pow x 3 / 6) ((x * (x * x)) * (1 / 6)).
Proof.
  intros x.
  apply qeq_imp_qeqT.
  assert (Hp : q_pow x 3 == x * (x * x)) by (unfold q_pow; simpl; ring).
  rewrite Hp.
  field. all: try (unfold Qeq; simpl; lia).
Qed.

(* ==================== Real 层：sin 一阶界（0 < X < 1） ==================== *)
(* sin X < X *)
Lemma real_sin_lt_x : forall X : Real,
  real_lt real_zero X -> real_lt X (real_const 1) ->
  real_lt (cauchy_real_sin X) X.
Proof.
  intros X H0 H1.
  destruct H0 as [eps0 [Heps0 [N0 HN0]]].
  destruct H1 as [eps1 [Heps1 [N1 HN1]]].
  destruct X as [u Hu].
  set (eps := (q_pow eps0 3) * (19 / 120)).
  assert (Heps_pos : QltT 0 eps).
  { unfold eps.
    apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0 (q_pow eps0 3)).
      apply Qlt_to_QltT.
      apply QltT_to_Qlt. apply sc_qpow_pos. apply QltT_to_Qlt. exact Heps0.
    - unfold Qlt; simpl; lia. }
  exists eps.
  split.
  - exact Heps_pos.
  - exists (Nat.max 2 (Nat.max N0 N1)).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_l | apply Nat.le_max_r] | exact (NatLe_drop _ _ Hn)]).
    assert (Hn1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]).
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as He0.
    pose proof (HN1 n (NatLe_lift _ _ Hn1)) as He1.
    assert (Hupos : Qlt eps0 (u n)).
    { apply QltT_to_Qlt in He0.
      assert (Hz : u n - 0 == u n) by ring.
      rewrite Hz in He0. exact He0. }
    assert (Hu1 : Qlt (u n) 1).
    { apply QltT_to_Qlt in He1.
      apply (proj2 (Qlt_minus_iff (u n) 1)).
      apply (Qlt_trans 0 eps1 (1 - u n)).
      - apply QltT_to_Qlt. exact Heps1.
      - exact He1. }
    assert (Hu0 : Qle 0 (u n)) by (apply (Qlt_le_weak 0 (u n)); apply (Qle_lt_trans 0 eps0 (u n)); [apply (Qlt_le_weak 0 eps0); apply QltT_to_Qlt; exact Heps0 | exact Hupos]).
    assert (Hu1le : Qle (u n) 1) by (apply Qlt_le_weak; exact Hu1).
    (* 目标：QltT eps (u n − sin_partial n (u n)) *)
    assert (Hd : Qle ((q_pow (u n) 3) * (19 / 120)) (u n - sin_partial n (u n))).
    { apply QleT'_to_Qle. apply sc_sin_upper_diff_cube_ge2. exact Hn2. exact Hu0. exact Hu1le. }
    apply (Qlt_le_trans _ ((q_pow (u n) 3) * (19 / 120)) _).
    + unfold eps.
      apply (Qmult_lt_compat_r (q_pow eps0 3) (q_pow (u n) 3) (19 / 120)).
      * unfold Qlt; simpl; lia.
      * apply QltT_to_Qlt. apply sc_qpow_lt. apply (Qlt_le_weak 0 eps0). apply QltT_to_Qlt. exact Heps0.
        exact Hupos. lia.
    + exact Hd.
Qed.

(* X − X³/6 < sin X *)
Lemma real_x_minus_cube_lt_sin : forall X : Real,
  real_lt real_zero X -> real_lt X (real_const 1) ->
  real_lt (real_plus X (real_opp (real_mult (real_mult X (real_mult X X)) (real_const (1 / 6)))))
          (cauchy_real_sin X).
Proof.
  intros X H0 H1.
  destruct H0 as [eps0 [Heps0 [N0 HN0]]].
  destruct H1 as [eps1 [Heps1 [N1 HN1]]].
  destruct X as [u Hu].
  set (eps := (q_pow eps0 5) * (41 / 5040)).
  assert (Heps_pos : QltT 0 eps).
  { unfold eps.
    apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0 (q_pow eps0 5)).
      apply Qlt_to_QltT.
      apply QltT_to_Qlt. apply sc_qpow_pos. apply QltT_to_Qlt. exact Heps0.
    - unfold Qlt; simpl; lia. }
  exists eps.
  split.
  - exact Heps_pos.
  - exists (Nat.max 2 (Nat.max N0 N1)).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_l | apply Nat.le_max_r] | exact (NatLe_drop _ _ Hn)]).
    assert (Hn1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]).
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as He0.
    pose proof (HN1 n (NatLe_lift _ _ Hn1)) as He1.
    assert (Hupos : Qlt eps0 (u n)).
    { apply QltT_to_Qlt in He0.
      assert (Hz : u n - 0 == u n) by ring.
      rewrite Hz in He0. exact He0. }
    assert (Hu1 : Qlt (u n) 1).
    { apply QltT_to_Qlt in He1.
      apply (proj2 (Qlt_minus_iff (u n) 1)).
      apply (Qlt_trans 0 eps1 (1 - u n)).
      - apply QltT_to_Qlt. exact Heps1.
      - exact He1. }
    assert (Hu0 : Qle 0 (u n)) by (apply (Qlt_le_weak 0 (u n)); apply (Qle_lt_trans 0 eps0 (u n)); [apply (Qlt_le_weak 0 eps0); apply QltT_to_Qlt; exact Heps0 | exact Hupos]).
    assert (Hu1le : Qle (u n) 1) by (apply Qlt_le_weak; exact Hu1).
    (* 目标：QltT eps (sin_partial n (u n) − (u n − (u n·(u n·u n))·(1/6))) *)
    simpl.
    assert (Hform : (u n * (u n * u n)) * (1 / 6) == q_pow (u n) 3 / 6).
    { rewrite (qeqT_imp_qeq _ _ (sc_qpow3_6form (u n))). ring. }
    assert (Hdiff : Qle ((q_pow (u n) 5) * (41 / 5040))
                        (sin_partial n (u n) - (u n - q_pow (u n) 3 / 6))).
    { apply QleT'_to_Qle. apply sc_sin_lower_diff_q5_ge2. exact Hn2. exact Hu0. exact Hu1le. }
    assert (Heq : sin_partial n (u n) - (u n - (u n * (u n * u n)) * (1 / 6)) ==
                  sin_partial n (u n) - (u n - q_pow (u n) 3 / 6)).
    { rewrite Hform. reflexivity. }
    rewrite Heq.
    apply (Qlt_le_trans _ ((q_pow (u n) 5) * (41 / 5040)) _).
    + unfold eps.
      apply (Qmult_lt_compat_r (q_pow eps0 5) (q_pow (u n) 5) (41 / 5040)).
      * unfold Qlt; simpl; lia.
      * apply QltT_to_Qlt. apply sc_qpow_lt. apply (Qlt_le_weak 0 eps0). apply QltT_to_Qlt. exact Heps0.
        exact Hupos. lia.
    + exact Hdiff.
Qed.
(* ============================================================ *)
(* 批 13（轮 13）：cos Real 层一阶界——对偶批 12               *)
(*   Q：cos ≥ C_3 链 + 二次/四次差分下界 + c' 求值             *)
(*   Real：0 < X < 1 → cos X < 1、1 − X²/2 < cos X             *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Lemma sc_cos_term3_x : forall x : Q, QeqT (cos_term 3 x) (- sc_cos_alt 3 x).
Proof.
  intro x. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_cos_term_odd_neg 1 x)).
Qed.

Lemma sc_cos_partial_3_val : forall x : Q, QeqT (cos_partial 3 x) (1 - sc_cos_alt 1 x + sc_cos_alt 2 x - sc_cos_alt 3 x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  assert (Hstep : cos_partial 3 x == cos_partial 2 x + cos_term 3 x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_2_val x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_term3_x x)).
  ring.
Qed.

(* ---- C_3 ≤ C_2 ---- *)
Lemma sc_cos_s3_le_s2 : forall x : Q, Qle 0 x -> QleT' (cos_partial 3 x) (cos_partial 2 x).
Proof.
  intros x Hx0.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_3_val x)).
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_2_val x)).
  apply (proj2 (Qle_minus_iff (1 - sc_cos_alt 1 x + sc_cos_alt 2 x - sc_cos_alt 3 x)
                              (1 - sc_cos_alt 1 x + sc_cos_alt 2 x))).
  assert (Heq : (1 - sc_cos_alt 1 x + sc_cos_alt 2 x) -
                (1 - sc_cos_alt 1 x + sc_cos_alt 2 x - sc_cos_alt 3 x) ==
                sc_cos_alt 3 x) by ring.
  rewrite Heq.
  apply QleT'_to_Qle. apply sc_cos_alt_nonneg. exact Hx0.
Qed.

(* ---- 奇子列 ≥ C_3（m ≥ 1） ---- *)
Lemma sc_cos_odd_ge3 : forall (m : nat) (x : Q),
  (1 <= m)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' (cos_partial 3 x) (cos_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hm Hx0 Hx1.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. lia.
  - apply Qle_to_QleT'. destruct m' as [| m''].
    + replace (Datatypes.S (2 * Datatypes.S 0))%nat with 3%nat by lia.
      apply Qle_refl.
    + apply (Qle_trans _ (cos_partial (Datatypes.S (2 * Datatypes.S m'')) x) _).
      * apply QleT'_to_Qle. apply IH. lia.
      * replace (Datatypes.S (2 * Datatypes.S (Datatypes.S m'')))%nat with
                 (Datatypes.S (Datatypes.S (Datatypes.S (2 * Datatypes.S m''))))%nat by lia.
        apply QleT'_to_Qle. apply sc_cos_odd_incr. exact Hx0. exact Hx1.
Qed.

(* ---- n ≥ 2 → cos_partial n x ≥ C_3 ---- *)
Lemma sc_cos_ge_c3_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 -> QleT' (cos_partial 3 x) (cos_partial n x).
Proof.
  intros n x Hn Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + destruct m' as [| m''].
      * rewrite Hm.
        replace (2 * Datatypes.S 0)%nat with 2%nat by lia.
        apply QleT'_to_Qle. apply sc_cos_s3_le_s2. exact Hx0.
      * rewrite Hm.
        apply (Qle_trans _ (cos_partial (Datatypes.S (2 * Datatypes.S m'')) x) _).
        -- apply QleT'_to_Qle. apply sc_cos_odd_ge3. lia. exact Hx0. exact Hx1.
        -- replace (2 * Datatypes.S (Datatypes.S m''))%nat with
                   (Datatypes.S (Datatypes.S (2 * Datatypes.S m'')))%nat by lia.
           apply QleT'_to_Qle. apply sc_cos_mix_ge. exact Hx0.
  - apply Qle_to_QleT'. rewrite Hm in Hn.
    destruct m as [| m'].
    + lia.
    + rewrite Hm.
      apply QleT'_to_Qle. apply sc_cos_odd_ge3. lia. exact Hx0. exact Hx1.
Qed.

(* ---- 下界差分：cos − (1 − c'_1) ≥ c'_2 − c'_3（n ≥ 2） ---- *)
Lemma sc_cos_lower_diff_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' (sc_cos_alt 2 x - sc_cos_alt 3 x) (cos_partial n x - (1 - sc_cos_alt 1 x)).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (proj2 (Qle_minus_iff (sc_cos_alt 2 x - sc_cos_alt 3 x)
                              (cos_partial n x - (1 - sc_cos_alt 1 x)))).
  assert (Hge : Qle (cos_partial 3 x) (cos_partial n x)).
  { apply QleT'_to_Qle. apply sc_cos_ge_c3_ge2. exact Hn. exact Hx0. exact Hx1. }
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_3_val x)) in Hge.
  pose proof (proj1 (Qle_minus_iff (1 - sc_cos_alt 1 x + sc_cos_alt 2 x - sc_cos_alt 3 x)
                                   (cos_partial n x)) Hge) as Hm.
  assert (Heq2 : cos_partial n x - (1 - sc_cos_alt 1 x + sc_cos_alt 2 x - sc_cos_alt 3 x) ==
                 (cos_partial n x - (1 - sc_cos_alt 1 x)) - (sc_cos_alt 2 x - sc_cos_alt 3 x)) by ring.
  rewrite Heq2 in Hm.
  exact Hm.
Qed.

(* ---- c' 求值 ---- *)
Lemma sc_cos_alt1_half : forall x : Q, QeqT (sc_cos_alt 1 x) (q_pow x 2 / 2).
Proof.
  intro x. apply qeq_imp_qeqT. unfold sc_cos_alt.
  replace (2 * 1)%nat with 2%nat by lia.
  assert (Hf : q_fact 2 == 2) by (unfold Qeq; simpl; lia).
  rewrite Hf. reflexivity.
Qed.

Lemma sc_cos_alt2_quar : forall x : Q, QeqT (sc_cos_alt 2 x) (q_pow x 4 / 24).
Proof.
  intro x. apply qeq_imp_qeqT. unfold sc_cos_alt.
  replace (2 * 2)%nat with 4%nat by lia.
  assert (Hf : q_fact 4 == 24) by (unfold Qeq; simpl; lia).
  rewrite Hf. reflexivity.
Qed.

Lemma sc_cos_alt3_720 : forall x : Q, QeqT (sc_cos_alt 3 x) (q_pow x 6 / 720).
Proof.
  intro x. apply qeq_imp_qeqT. unfold sc_cos_alt.
  replace (2 * 3)%nat with 6%nat by lia.
  assert (Hf : q_fact 6 == 720) by (unfold Qeq; simpl; lia).
  rewrite Hf. reflexivity.
Qed.

(* ---- 上界差分二次下界：1 − cos ≥ x²·11/24（n ≥ 2） ---- *)
Lemma sc_cos_upper_diff_sq_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' ((q_pow x 2) * (11 / 24)) (1 - cos_partial n x).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  assert (Hd : Qle (sc_cos_alt 1 x - sc_cos_alt 2 x) (1 - cos_partial n x)).
  { apply QleT'_to_Qle. apply sc_cos_diff_lower_ge2. exact Hn. exact Hx0. exact Hx1. }
  rewrite (qeqT_imp_qeq _ _ (sc_cos_alt1_half x)) in Hd.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_alt2_quar x)) in Hd.
  assert (Hx4 : Qle (q_pow x 4) (q_pow x 2)).
  { apply (Qle_trans _ (q_pow x 3) _).
    - apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1.
    - apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1. }
  assert (Hd2 : Qle (q_pow x 4 / 24) (q_pow x 2 / 24)).
  { apply QleT'_to_Qle; apply (Qle_div_same_denom (q_pow x 4) (q_pow x 2) 24).
    - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
    - apply Qle_to_QleT'. exact Hx4. }
  assert (Heq : q_pow x 2 / 2 - q_pow x 2 / 24 == (q_pow x 2) * (11 / 24)).
  { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
  apply (Qle_trans _ (q_pow x 2 / 2 - q_pow x 4 / 24) _).
  - apply (Qle_trans _ (q_pow x 2 / 2 - q_pow x 2 / 24) _).
    + rewrite <- Heq. apply Qle_refl.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hd2.
  - exact Hd.
Qed.

(* ---- 下界差分四次：cos − (1 − x²/2) ≥ x⁴·29/720（n ≥ 2） ---- *)
Lemma sc_cos_lower_diff_q4_ge2 : forall (n : nat) (x : Q),
  (2 <= n)%nat -> Qle 0 x -> Qle x 1 ->
  QleT' ((q_pow x 4) * (29 / 720)) (cos_partial n x - (1 - q_pow x 2 / 2)).
Proof.
  intros n x Hn Hx0 Hx1.
  apply Qle_to_QleT'.
  assert (Hs : cos_partial n x - (1 - q_pow x 2 / 2) ==
               cos_partial n x - (1 - sc_cos_alt 1 x)).
  { rewrite (qeqT_imp_qeq _ _ (sc_cos_alt1_half x)). ring. }
  rewrite Hs.
  assert (Hd : Qle (sc_cos_alt 2 x - sc_cos_alt 3 x)
                   (cos_partial n x - (1 - sc_cos_alt 1 x))).
  { apply QleT'_to_Qle. apply sc_cos_lower_diff_ge2. exact Hn. exact Hx0. exact Hx1. }
  assert (Hc23 : sc_cos_alt 2 x - sc_cos_alt 3 x ==
                 q_pow x 4 / 24 - q_pow x 6 / 720).
  { rewrite (qeqT_imp_qeq _ _ (sc_cos_alt2_quar x)). rewrite (qeqT_imp_qeq _ _ (sc_cos_alt3_720 x)). reflexivity. }
  rewrite Hc23 in Hd.
  apply (Qle_trans _ (q_pow x 4 / 24 - q_pow x 6 / 720) _).
  - assert (Hx6 : Qle (q_pow x 6) (q_pow x 4)).
    { apply (Qle_trans _ (q_pow x 5) _).
      - apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1.
      - apply (Qle_trans _ (q_pow x 4) _).
        + apply QleT'_to_Qle. apply sc_qpow_dec. exact Hx0. exact Hx1.
        + apply Qle_refl. }
    assert (Hd2 : Qle (q_pow x 6 / 720) (q_pow x 4 / 720)).
    { apply QleT'_to_Qle; apply (Qle_div_same_denom (q_pow x 6) (q_pow x 4) 720).
      - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
      - apply Qle_to_QleT'. exact Hx6. }
    assert (Heq : q_pow x 4 / 24 - q_pow x 4 / 720 == (q_pow x 4) * (29 / 720)).
    { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
    apply (Qle_trans _ (q_pow x 4 / 24 - q_pow x 4 / 720) _).
    + rewrite <- Heq. apply Qle_refl.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Hd2.
  - exact Hd.
Qed.

(* ---- 形态桥：x⁴ == (x·x)·(x·x)、x²/2 与 x⁴/24 序列形态 ---- *)
Lemma sc_qpow2_2form : forall x : Q, QeqT (q_pow x 2 / 2) ((x * x) * (1 / 2)).
Proof.
  intros x.
  apply qeq_imp_qeqT.
  assert (Hp : q_pow x 2 == x * x) by (unfold q_pow; simpl; ring).
  rewrite Hp.
  field. all: try (unfold Qeq; simpl; lia).
Qed.

Lemma sc_qpow4_24form : forall x : Q, QeqT (q_pow x 4 / 24) (((x * x) * (x * x)) * (1 / 24)).
Proof.
  intros x.
  apply qeq_imp_qeqT.
  assert (Hp : q_pow x 4 == (x * x) * (x * x)) by (unfold q_pow; simpl; ring).
  rewrite Hp.
  field. all: try (unfold Qeq; simpl; lia).
Qed.

(* ==================== Real 层：cos 一阶界（0 < X < 1） ==================== *)
(* cos X < 1 *)
Lemma real_cos_lt_one : forall X : Real,
  real_lt real_zero X -> real_lt X (real_const 1) ->
  real_lt (cauchy_real_cos X) (real_const 1).
Proof.
  intros X H0 H1.
  destruct H0 as [eps0 [Heps0 [N0 HN0]]].
  destruct H1 as [eps1 [Heps1 [N1 HN1]]].
  destruct X as [u Hu].
  set (eps := (q_pow eps0 2) * (11 / 24)).
  assert (Heps_pos : QltT 0 eps).
  { unfold eps.
    apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0 (q_pow eps0 2)).
      apply Qlt_to_QltT.
      apply QltT_to_Qlt. apply sc_qpow_pos. apply QltT_to_Qlt. exact Heps0.
    - unfold Qlt; simpl; lia. }
  exists eps.
  split.
  - exact Heps_pos.
  - exists (Nat.max 2 (Nat.max N0 N1)).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_l | apply Nat.le_max_r] | exact (NatLe_drop _ _ Hn)]).
    assert (Hn1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]).
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as He0.
    pose proof (HN1 n (NatLe_lift _ _ Hn1)) as He1.
    assert (Hupos : Qlt eps0 (u n)).
    { apply QltT_to_Qlt in He0.
      assert (Hz : u n - 0 == u n) by ring.
      rewrite Hz in He0. exact He0. }
    assert (Hu1 : Qlt (u n) 1).
    { apply QltT_to_Qlt in He1.
      apply (proj2 (Qlt_minus_iff (u n) 1)).
      apply (Qlt_trans 0 eps1 (1 - u n)).
      - apply QltT_to_Qlt. exact Heps1.
      - exact He1. }
    assert (Hu0 : Qle 0 (u n)) by (apply (Qlt_le_weak 0 (u n)); apply (Qle_lt_trans 0 eps0 (u n)); [apply (Qlt_le_weak 0 eps0); apply QltT_to_Qlt; exact Heps0 | exact Hupos]).
    assert (Hu1le : Qle (u n) 1) by (apply Qlt_le_weak; exact Hu1).
    (* 目标：QltT eps (1 − cos_partial n (u n)) *)
    assert (Hd : Qle ((q_pow (u n) 2) * (11 / 24)) (1 - cos_partial n (u n))).
    { apply QleT'_to_Qle. apply sc_cos_upper_diff_sq_ge2. exact Hn2. exact Hu0. exact Hu1le. }
    apply (Qlt_le_trans _ ((q_pow (u n) 2) * (11 / 24)) _).
    + unfold eps.
      apply (Qmult_lt_compat_r (q_pow eps0 2) (q_pow (u n) 2) (11 / 24)).
      * unfold Qlt; simpl; lia.
      * apply QltT_to_Qlt. apply sc_qpow_lt. apply (Qlt_le_weak 0 eps0). apply QltT_to_Qlt. exact Heps0.
        exact Hupos. lia.
    + exact Hd.
Qed.

(* 1 − X²/2 < cos X *)
Lemma real_one_minus_half_lt_cos : forall X : Real,
  real_lt real_zero X -> real_lt X (real_const 1) ->
  real_lt (real_plus (real_const 1)
                     (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
          (cauchy_real_cos X).
Proof.
  intros X H0 H1.
  destruct H0 as [eps0 [Heps0 [N0 HN0]]].
  destruct H1 as [eps1 [Heps1 [N1 HN1]]].
  destruct X as [u Hu].
  set (eps := (q_pow eps0 4) * (29 / 720)).
  assert (Heps_pos : QltT 0 eps).
  { unfold eps.
    apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0 (q_pow eps0 4)).
      apply Qlt_to_QltT.
      apply QltT_to_Qlt. apply sc_qpow_pos. apply QltT_to_Qlt. exact Heps0.
    - unfold Qlt; simpl; lia. }
  exists eps.
  split.
  - exact Heps_pos.
  - exists (Nat.max 2 (Nat.max N0 N1)).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_l | apply Nat.le_max_r] | exact (NatLe_drop _ _ Hn)]).
    assert (Hn1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 N1)) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]).
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as He0.
    pose proof (HN1 n (NatLe_lift _ _ Hn1)) as He1.
    assert (Hupos : Qlt eps0 (u n)).
    { apply QltT_to_Qlt in He0.
      assert (Hz : u n - 0 == u n) by ring.
      rewrite Hz in He0. exact He0. }
    assert (Hu1 : Qlt (u n) 1).
    { apply QltT_to_Qlt in He1.
      apply (proj2 (Qlt_minus_iff (u n) 1)).
      apply (Qlt_trans 0 eps1 (1 - u n)).
      - apply QltT_to_Qlt. exact Heps1.
      - exact He1. }
    assert (Hu0 : Qle 0 (u n)) by (apply (Qlt_le_weak 0 (u n)); apply (Qle_lt_trans 0 eps0 (u n)); [apply (Qlt_le_weak 0 eps0); apply QltT_to_Qlt; exact Heps0 | exact Hupos]).
    assert (Hu1le : Qle (u n) 1) by (apply Qlt_le_weak; exact Hu1).
    (* 目标：QltT eps (cos_partial n (u n) − (1 − (u n·u n)·(1/2))) *)
    simpl.
    assert (Hform : (u n * u n) * (1 / 2) == q_pow (u n) 2 / 2).
    { rewrite (qeqT_imp_qeq _ _ (sc_qpow2_2form (u n))). ring. }
    assert (Hdiff : Qle ((q_pow (u n) 4) * (29 / 720))
                        (cos_partial n (u n) - (1 - q_pow (u n) 2 / 2))).
    { apply QleT'_to_Qle. apply sc_cos_lower_diff_q4_ge2. exact Hn2. exact Hu0. exact Hu1le. }
    assert (Heq : cos_partial n (u n) - (1 - (u n * u n) * (1 / 2)) ==
                  cos_partial n (u n) - (1 - q_pow (u n) 2 / 2)).
    { rewrite Hform. reflexivity. }
    rewrite Heq.
    apply (Qlt_le_trans _ ((q_pow (u n) 4) * (29 / 720)) _).
    + unfold eps.
      apply (Qmult_lt_compat_r (q_pow eps0 4) (q_pow (u n) 4) (29 / 720)).
      * unfold Qlt; simpl; lia.
      * apply QltT_to_Qlt. apply sc_qpow_lt. apply (Qlt_le_weak 0 eps0). apply QltT_to_Qlt. exact Heps0.
        exact Hupos. lia.
    + exact Hdiff.
Qed.
(* ============================================================ *)
(* 批 14（轮 14）：sin/cos real_eq 兼容 + 端点常数定理          *)
(*   real_sin_eq_compat/real_cos_eq_compat（一阶界闭区间前置）  *)
(*   sin(1) < 1、5/6 < sin(1)、cos(1) > 1/2（常数差端点）        *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Lemma real_sin_eq_compat : forall x y : Real,
  real_eq x y -> real_eq (cauchy_real_sin x) (cauchy_real_sin y).
Proof.
  intros x y Hxy.
  destruct x as [u Hu]. destruct y as [v Hv].
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mx [HMxpos HMx]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [My [HMypos HMy]].
  set (B := Mx + My).
  assert (HBT : QleT' 0 B).
  { unfold B. apply qltT_leT'. apply (qltT_plus_pos_r Mx My).
    - exact HMxpos.
    - exact HMypos. }
  assert (HBxT : forall n : nat, QleT' (Qabs (u n)) B).
  { intro n. unfold B. apply (qleT'_trans (Qabs (u n)) Mx (Mx + My)).
    - apply (HMx n).
    - apply (qleT'_plus_nonneg_rT Mx My). apply qltT_leT'. exact HMypos. }
  assert (HByT : forall n : nat, QleT' (Qabs (v n)) B).
  { intro n. unfold B. apply (qleT'_trans (Qabs (v n)) My (Mx + My)).
    - apply (HMy n).
    - apply (qleT'_trans My (My + Mx) (Mx + My)).
      + apply (qleT'_plus_nonneg_rT My Mx). apply qltT_leT'. exact HMxpos.
      + apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  destruct (exp_series_arch B HBT) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1 _); [unfold Qlt; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (Hxy (eps / C)) as [N0 HN0].
  { apply Qlt_to_QltT.
    unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv C)).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. exact HCpos. }
  exists N0.
  intros n Hn.
  apply Qlt_to_QltT.
  pose proof (HN0 n Hn) as He.
  assert (Hle : Qle (Qabs (sin_partial n (u n) - sin_partial n (v n)))
                    (Qmult (Qabs (u n - v n)) C)).
  { apply (Qle_trans _ (Qmult (Qabs (u n - v n)) (sc_cos_series n B)) _).
    - apply QleT'_to_Qle. apply (sc_sin_partial_lipschitz (u n) (v n) B n HBT (HBxT n) (HByT n)).
    - apply (Qmult_le_compat_nonneg (Qabs (u n - v n)) (Qabs (u n - v n))
                                    (sc_cos_series n B) C).
      + split; [apply Qabs_nonneg | apply Qle_refl].
      + split.
        * apply QleT'_to_Qle. apply sc_cos_series_nonneg. exact HBT.
        * apply (Qle_trans _ (exp_series (2 * n) B) _).
          -- apply QleT'_to_Qle. apply sc_cos_series_le_exp. exact HBT.
          -- apply QleT'_to_Qle. exact (HC (2 * n)%nat). }
  apply (Qle_lt_trans _ (Qmult (Qabs (u n - v n)) C) _).
  - exact Hle.
  - apply (Qlt_le_trans _ (Qmult (eps / C) C) _).
    + apply (Qmult_lt_compat_r (Qabs (u n - v n)) (eps / C) C).
      * exact HCpos.
      * apply QltT_to_Qlt. exact He.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      unfold Qdiv. field.
      all: try (intro HzneA; exact (match (q_neq_of_lt _ (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ HzneA)) with end)).
Qed.

(* ---- cos 的 real_eq 兼容 ---- *)
Lemma real_cos_eq_compat : forall x y : Real,
  real_eq x y -> real_eq (cauchy_real_cos x) (cauchy_real_cos y).
Proof.
  intros x y Hxy.
  destruct x as [u Hu]. destruct y as [v Hv].
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mx [HMxpos HMx]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [My [HMypos HMy]].
  set (B := Mx + My).
  assert (HBT : QleT' 0 B).
  { unfold B. apply qltT_leT'. apply (qltT_plus_pos_r Mx My).
    - exact HMxpos.
    - exact HMypos. }
  assert (HBxT : forall n : nat, QleT' (Qabs (u n)) B).
  { intro n. unfold B. apply (qleT'_trans (Qabs (u n)) Mx (Mx + My)).
    - apply (HMx n).
    - apply (qleT'_plus_nonneg_rT Mx My). apply qltT_leT'. exact HMypos. }
  assert (HByT : forall n : nat, QleT' (Qabs (v n)) B).
  { intro n. unfold B. apply (qleT'_trans (Qabs (v n)) My (Mx + My)).
    - apply (HMy n).
    - apply (qleT'_trans My (My + Mx) (Mx + My)).
      + apply (qleT'_plus_nonneg_rT My Mx). apply qltT_leT'. exact HMxpos.
      + apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  destruct (exp_series_arch B HBT) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans _ 1 _); [unfold Qlt; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (Hxy (eps / C)) as [N0 HN0].
  { apply Qlt_to_QltT.
    unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv C)).
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. exact HCpos. }
  exists N0.
  intros n Hn.
  apply Qlt_to_QltT.
  pose proof (HN0 n Hn) as He.
  destruct n as [| n'].
  - (* n = 0：cos_partial 0 == 1 双侧 *)
    assert (Hsmall : Qlt (Qabs (cos_partial 0%nat (u 0%nat) - cos_partial 0%nat (v 0%nat))) eps).
    { assert (Hc0x : cos_partial 0%nat (u 0%nat) == 1) by (apply qeqT_imp_qeq; apply sc_cos_partial_zero_const).
      assert (Hc0y : cos_partial 0%nat (v 0%nat) == 1) by (apply qeqT_imp_qeq; apply sc_cos_partial_zero_const).
      assert (Heq0 : cos_partial 0%nat (u 0%nat) == cos_partial 0%nat (v 0%nat)).
      { rewrite Hc0x. rewrite <- Hc0y. reflexivity. }
      rewrite Heq0.
      assert (Hd : cos_partial 0%nat (v 0%nat) - cos_partial 0%nat (v 0%nat) == 0) by ring.
      rewrite Hd.
      assert (Hz : Qabs 0 == 0) by (unfold Qabs; simpl; reflexivity).
      rewrite Hz.
      exact (QltT_to_Qlt 0 eps Heps). }
    exact Hsmall.
  - assert (Hle : Qle (Qabs (cos_partial (Datatypes.S n') (u (Datatypes.S n')) - cos_partial (Datatypes.S n') (v (Datatypes.S n'))))
                      (Qmult (Qabs (u (Datatypes.S n') - v (Datatypes.S n'))) C)).
    { apply (Qle_trans _ (Qmult (Qabs (u (Datatypes.S n') - v (Datatypes.S n'))) (sc_sin_deriv_series n' B)) _).
      - apply QleT'_to_Qle. apply (sc_cos_partial_lipschitz_succ (u (Datatypes.S n')) (v (Datatypes.S n')) B n' HBT (HBxT (Datatypes.S n')) (HByT (Datatypes.S n'))).
      - apply (Qmult_le_compat_nonneg (Qabs (u (Datatypes.S n') - v (Datatypes.S n'))) (Qabs (u (Datatypes.S n') - v (Datatypes.S n')))
                                      (sc_sin_deriv_series n' B) C).
        + split; [apply Qabs_nonneg | apply Qle_refl].
        + split.
          * apply QleT'_to_Qle. apply sc_sin_deriv_series_nonneg. exact HBT.
          * apply (Qle_trans _ (exp_series (Datatypes.S (2 * n')) B) _).
            -- apply QleT'_to_Qle. apply sc_sin_deriv_series_le_exp. exact HBT.
            -- apply QleT'_to_Qle. exact (HC (Datatypes.S (2 * n'))%nat). }
    apply (Qle_lt_trans _ (Qmult (Qabs (u (Datatypes.S n') - v (Datatypes.S n'))) C) _).
    + exact Hle.
    + apply (Qlt_le_trans _ (Qmult (eps / C) C) _).
      * apply (Qmult_lt_compat_r (Qabs (u (Datatypes.S n') - v (Datatypes.S n'))) (eps / C) C).
        -- exact HCpos.
        -- apply QltT_to_Qlt. exact He.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        unfold Qdiv. field.
        all: try (intro HzneA; exact (match (q_neq_of_lt _ (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ HzneA)) with end)).
Qed.

(* ---- 端点：sin(1) < 1（差 ≥ 19/120，eps := 19/240） ---- *)
Lemma real_sin_one_lt_one : real_lt (cauchy_real_sin (real_const 1)) (real_const 1).
Proof.
  unfold real_lt.
  exists (19 / 240).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply NatLe_drop in Hn; lia).
    assert (Hd : Qle (19 / 120) (1 - sin_partial n 1)).
    { apply (Qle_trans _ ((q_pow 1 3) * (19 / 120)) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        assert (Hp : q_pow 1 3 == 1) by (apply qeqT_imp_qeq; apply sc_q_pow_one).
        rewrite Hp. ring.
      - apply QleT'_to_Qle. apply (sc_sin_upper_diff_cube_ge2 n 1 Hn2).
        + unfold Qle; simpl; lia.
        + unfold Qle; simpl; lia. }
    apply (Qlt_le_trans _ (19 / 120) _).
    + unfold Qlt; simpl; lia.
    + exact Hd.
Qed.

(* ---- 端点：5/6 < sin(1)（差 ≥ 41/5040，eps := 41/10080） ---- *)
Lemma real_sin_one_gt_five_six : real_lt (real_const (5 / 6)) (cauchy_real_sin (real_const 1)).
Proof.
  unfold real_lt.
  exists (41 / 10080).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply NatLe_drop in Hn; lia).
    assert (Hv : 1 - 1 / 6 == 5 / 6).
    { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
    assert (Hd : Qle (41 / 5040) (sin_partial n 1 - 5 / 6)).
    { apply (Qle_trans _ ((q_pow 1 5) * (41 / 5040)) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        assert (Hp : q_pow 1 5 == 1) by (apply qeqT_imp_qeq; apply sc_q_pow_one).
        rewrite Hp. ring.
      - apply (Qle_trans _ (sin_partial n 1 - (1 - q_pow 1 3 / 6)) _).
        + apply QleT'_to_Qle. apply (sc_sin_lower_diff_q5_ge2 n 1 Hn2).
          * unfold Qle; simpl; lia.
          * unfold Qle; simpl; lia.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          assert (Hp3 : q_pow 1 3 == 1) by (apply qeqT_imp_qeq; apply sc_q_pow_one).
          rewrite Hp3.
          assert (Hv2 : (1 - 1 / 6) == 5 / 6).
          { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
          rewrite Hv2. ring. }
    apply (Qlt_le_trans _ (41 / 5040) _).
    + unfold Qlt; simpl; lia.
    + exact Hd.
Qed.

(* ---- 端点：cos(1) > 1/2（差 ≥ 29/720，eps := 29/1440） ---- *)
Lemma real_cos_one_gt_half : real_lt (real_const (1 / 2)) (cauchy_real_cos (real_const 1)).
Proof.
  unfold real_lt.
  exists (29 / 1440).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    assert (Hn2 : (2 <= n)%nat) by (apply NatLe_drop in Hn; lia).
    assert (Hv : 1 - 1 / 2 == 1 / 2).
    { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
    assert (Hd : Qle (29 / 720) (cos_partial n 1 - 1 / 2)).
    { apply (Qle_trans _ ((q_pow 1 4) * (29 / 720)) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        assert (Hp : q_pow 1 4 == 1) by (apply qeqT_imp_qeq; apply sc_q_pow_one).
        rewrite Hp. ring.
      - apply (Qle_trans _ (cos_partial n 1 - (1 - q_pow 1 2 / 2)) _).
        + apply QleT'_to_Qle. apply (sc_cos_lower_diff_q4_ge2 n 1 Hn2).
          * unfold Qle; simpl; lia.
          * unfold Qle; simpl; lia.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          assert (Hp2 : q_pow 1 2 == 1) by (apply qeqT_imp_qeq; apply sc_q_pow_one).
          rewrite Hp2.
          assert (Hv2 : (1 - 1 / 2) == 1 / 2).
          { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
          rewrite Hv2. ring. }
    apply (Qlt_le_trans _ (29 / 720) _).
    + unfold Qlt; simpl; lia.
    + exact Hd.
Qed.

(* ============================================================ *)
(* 批 15（轮 15）：一阶界闭区间版（0 ≤ X ≤ 1）                  *)
(*   real_sin_le_x / real_x_minus_cube_le_sin / real_cos_le_one *)
(*   / real_one_minus_half_le_cos：real_le = Or lt eq 三分支     *)
(*   组装（0<X<1 严格定理；X==0 eq 链；X==1 外延链）。           *)
(* 关键结论：real_eq 未注册为 Coq setoid rewrite 关系（无 Proper *)
(*   实例——Stdlib Proper/Setoid 依赖 Prop 层 relation，与 Set 层 *)
(*   real_eq 不适配；RealSetoid 模块（L31453-32263）只提供手工   *)
(*   兼容引理 RealSetoid.real_eq_*_compat），故替换一律走手写    *)
(*   通道：poly-ext（real_eq X Y ⟹ 多项式表达式 real_eq）+ 端点  *)
(*   求值（X==real_const 1 / X==real_zero，逐点 proj + ring/     *)
(*   field）+ lt/le 桥（real_lt_le_iff_req / real_eq_le /        *)
(*   real_lt_eq_lt / real_eq_lt_lt）+ real_one ≈ real_const 1 桥。*)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
(* ---- 桥：real_one ≈ real_const 1（逐点相等，N = 0） ---- *)
Lemma real_one_req_const_one : real_eq real_one (real_const 1).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
  assert (Ho : projT1 real_one n == 1) by reflexivity.
  rewrite Ho. ring.
Qed.

(* ---- 外延：X ≈ Y ⟹ (X − X·(X·X)·(1/6)) ≈ (Y − Y·(Y·Y)·(1/6)) ---- *)
Lemma real_x_cube_poly_ext : forall X Y : Real,
  real_eq X Y ->
  real_eq (real_plus X (real_opp (real_mult (real_mult X (real_mult X X)) (real_const (1 / 6)))))
          (real_plus Y (real_opp (real_mult (real_mult Y (real_mult Y Y)) (real_const (1 / 6))))).
Proof.
intros X Y Hxy.
  apply RealSetoid.real_eq_plus_compat.
  - exact Hxy.
  - apply RealSetoid.real_eq_opp_compat.
    apply RealSetoid.real_eq_mult_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * exact Hxy.
      * apply RealSetoid.real_eq_mult_compat; exact Hxy.
    + exact (real_eq_refl (real_const (1 / 6))).
Qed.

(* ---- 外延：X ≈ Y ⟹ (1 − X·X·(1/2)) ≈ (1 − Y·Y·(1/2)) ---- *)
Lemma real_half_sq_poly_ext : forall X Y : Real,
  real_eq X Y ->
  real_eq (real_plus (real_const 1) (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
          (real_plus (real_const 1) (real_opp (real_mult (real_mult Y Y) (real_const (1 / 2))))).
Proof.
  intros X Y Hxy.
  exact (RealSetoid.real_eq_plus_compat (real_const 1)
    (real_opp (real_mult (real_mult X X) (real_const (1 / 2))))
    (real_const 1)
    (real_opp (real_mult (real_mult Y Y) (real_const (1 / 2))))
    (real_eq_refl (real_const 1))
    (RealSetoid.real_eq_opp_compat
      (real_mult (real_mult X X) (real_const (1 / 2)))
      (real_mult (real_mult Y Y) (real_const (1 / 2)))
      (RealSetoid.real_eq_mult_compat (real_mult X X)
        (real_const (1 / 2)) (real_mult Y Y) (real_const (1 / 2))
        (RealSetoid.real_eq_mult_compat X X Y Y Hxy Hxy)
        (real_eq_refl (real_const (1 / 2)))))).
Qed.

(* ---- 求值：X³/6 型多项式在 X := real_const 1 处 == 5/6 ---- *)
Lemma real_x_cube_poly_const1_eval :
  real_eq (real_plus (real_const 1) (real_opp (real_mult (real_mult (real_const 1) (real_mult (real_const 1) (real_const 1))) (real_const (1 / 6)))))
          (real_const (5 / 6)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const 1) (real_opp (real_mult (real_mult (real_const 1) (real_mult (real_const 1) (real_const 1))) (real_const (1 / 6)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult (real_mult (real_const 1) (real_mult (real_const 1) (real_const 1))) (real_const (1 / 6))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult (real_const 1) (real_mult (real_const 1) (real_const 1))) (real_const (1 / 6)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) (real_mult (real_const 1) (real_const 1)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) (real_const 1) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)). rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 6) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (5 / 6) n)).
  assert (Hz : (1 + -((1 * (1 * 1)) * (1 / 6))) - (5 / 6) == 0).
  { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
  rewrite Hz. reflexivity.
Qed.

(* ---- 求值：X³/6 型多项式在 X := real_zero 处 == real_zero ---- *)
Lemma real_x_cube_poly_zero_eval :
  real_eq (real_plus real_zero (real_opp (real_mult (real_mult real_zero (real_mult real_zero real_zero)) (real_const (1 / 6)))))
          real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero (real_opp (real_mult (real_mult real_zero (real_mult real_zero real_zero)) (real_const (1 / 6)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult (real_mult real_zero (real_mult real_zero real_zero)) (real_const (1 / 6))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult real_zero (real_mult real_zero real_zero)) (real_const (1 / 6)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero (real_mult real_zero real_zero) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero real_zero n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 6) n)).
  assert (Hrz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hrz.
  assert (Hz : (0 + -((0 * (0 * 0)) * (1 / 6))) - 0 == 0).
  { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
  rewrite Hz. reflexivity.
Qed.

(* ---- 求值：X²/2 型多项式在 X := real_const 1 处 == 1/2 ---- *)
Lemma real_half_sq_poly_const1_eval :
  real_eq (real_plus (real_const 1) (real_opp (real_mult (real_mult (real_const 1) (real_const 1)) (real_const (1 / 2)))))
          (real_const (1 / 2)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const 1) (real_opp (real_mult (real_mult (real_const 1) (real_const 1)) (real_const (1 / 2)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult (real_mult (real_const 1) (real_const 1)) (real_const (1 / 2))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult (real_const 1) (real_const 1)) (real_const (1 / 2)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) (real_const 1) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)). rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
  assert (Hz : (1 + -((1 * 1) * (1 / 2))) - (1 / 2) == 0).
  { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
  rewrite Hz. reflexivity.
Qed.

(* ---- 求值：X²/2 型多项式在 X := real_zero 处 == real_const 1 ---- *)
Lemma real_half_sq_poly_zero_eval :
  real_eq (real_plus (real_const 1) (real_opp (real_mult (real_mult real_zero real_zero) (real_const (1 / 2)))))
          (real_const 1).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const 1) (real_opp (real_mult (real_mult real_zero real_zero) (real_const (1 / 2)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult (real_mult real_zero real_zero) (real_const (1 / 2))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult real_zero real_zero) (real_const (1 / 2)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero real_zero n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
  assert (Hrz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hrz.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
  assert (Hz : (1 + -((0 * 0) * (1 / 2))) - 1 == 0).
  { unfold Qdiv. field. all: try (unfold Qeq; simpl; lia). }
  rewrite Hz. reflexivity.
Qed.

(* ==================== Real 层：一阶界闭区间版（0 ≤ X ≤ 1） ==================== *)
(* sin X ≤ X *)
Lemma real_sin_le_x : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le (cauchy_real_sin X) X.
Proof.
  intros X H0 H1.
  destruct H0 as [H0l | H0e].
  - destruct H1 as [H1l | H1e].
    + (* 0 < X < 1：严格定理直接给出 real_lt ⟹ real_le *)
      apply RealSetoid.real_lt_le_iff_req. left.
      exact (real_sin_lt_x X H0l H1l).
    + (* X == 1：外延链 sin X == sin(1) < 1 == X *)
      apply RealSetoid.real_lt_le_iff_req. left.
      apply (real_lt_eq_lt (cauchy_real_sin X) (real_const 1) X).
      * apply (real_eq_lt_lt (cauchy_real_sin X) (cauchy_real_sin (real_const 1)) (real_const 1)).
        -- apply real_sin_eq_compat. exact H1e.
        -- exact real_sin_one_lt_one.
      * apply real_eq_sym. exact H1e.
  - (* X == 0：eq 链 sin X == sin 0 == real_zero == X *)
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (cauchy_real_sin X) real_zero X).
    + apply (real_eq_trans (cauchy_real_sin X) (cauchy_real_sin real_zero) real_zero).
      * apply real_sin_eq_compat. apply real_eq_sym. exact H0e.
      * exact real_sin_zero.
    + exact H0e.
Qed.

(* X − X³/6 ≤ sin X *)
Lemma real_x_minus_cube_le_sin : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le (real_plus X (real_opp (real_mult (real_mult X (real_mult X X)) (real_const (1 / 6)))))
          (cauchy_real_sin X).
Proof.
  intros X H0 H1.
  destruct H0 as [H0l | H0e].
  - destruct H1 as [H1l | H1e].
    + apply RealSetoid.real_lt_le_iff_req. left.
      exact (real_x_minus_cube_lt_sin X H0l H1l).
    + (* X == 1：外延 + 求值 == 5/6 + 5/6 < sin(1) == sin X *)
      apply RealSetoid.real_lt_le_iff_req. left.
      apply (real_eq_lt_lt (real_plus X (real_opp (real_mult (real_mult X (real_mult X X)) (real_const (1 / 6)))))
                           (real_const (5 / 6))
                           (cauchy_real_sin X)).
      * apply (real_eq_trans _ (real_plus (real_const 1) (real_opp (real_mult (real_mult (real_const 1) (real_mult (real_const 1) (real_const 1))) (real_const (1 / 6))))) _).
        -- apply real_x_cube_poly_ext. exact H1e.
        -- exact real_x_cube_poly_const1_eval.
      * apply (real_lt_eq_lt (real_const (5 / 6)) (cauchy_real_sin (real_const 1)) (cauchy_real_sin X)).
        -- exact real_sin_one_gt_five_six.
        -- apply real_sin_eq_compat. apply real_eq_sym. exact H1e.
  - (* X == 0：LHS == real_zero == sin X *)
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (real_plus X (real_opp (real_mult (real_mult X (real_mult X X)) (real_const (1 / 6)))))
                         real_zero
                         (cauchy_real_sin X)).
    + apply (real_eq_trans _ (real_plus real_zero (real_opp (real_mult (real_mult real_zero (real_mult real_zero real_zero)) (real_const (1 / 6))))) _).
      * apply real_x_cube_poly_ext. apply real_eq_sym. exact H0e.
      * exact real_x_cube_poly_zero_eval.
    + apply real_eq_sym.
      apply (real_eq_trans (cauchy_real_sin X) (cauchy_real_sin real_zero) real_zero).
      * apply real_sin_eq_compat. apply real_eq_sym. exact H0e.
      * exact real_sin_zero.
Qed.

(* cos X ≤ 1 *)
Lemma real_cos_le_one : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le (cauchy_real_cos X) (real_const 1).
Proof.
  intros X H0 H1.
  destruct H0 as [H0l | H0e].
  - destruct H1 as [H1l | H1e].
    + apply RealSetoid.real_lt_le_iff_req. left.
      exact (real_cos_lt_one X H0l H1l).
    + (* X == 1：cos X == cos(1) < real_one ≈ real_const 1 *)
      apply RealSetoid.real_lt_le_iff_req. left.
      apply (real_eq_lt_lt (cauchy_real_cos X) (cauchy_real_cos (real_const 1)) (real_const 1)).
      * apply real_cos_eq_compat. exact H1e.
      * apply (real_lt_eq_lt (cauchy_real_cos (real_const 1)) real_one (real_const 1)).
        -- exact real_cos_one_lt_one.
        -- exact real_one_req_const_one.
  - (* X == 0：cos X == cos 0 == real_one ≈ real_const 1 *)
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (cauchy_real_cos X) real_one (real_const 1)).
    + apply (real_eq_trans (cauchy_real_cos X) (cauchy_real_cos real_zero) real_one).
      * apply real_cos_eq_compat. apply real_eq_sym. exact H0e.
      * exact real_cos_one.
    + exact real_one_req_const_one.
Qed.

(* 1 − X²/2 ≤ cos X *)
Lemma real_one_minus_half_le_cos : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le (real_plus (real_const 1) (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
          (cauchy_real_cos X).
Proof.
  intros X H0 H1.
  destruct H0 as [H0l | H0e].
  - destruct H1 as [H1l | H1e].
    + apply RealSetoid.real_lt_le_iff_req. left.
      exact (real_one_minus_half_lt_cos X H0l H1l).
    + (* X == 1：外延 + 求值 == 1/2 + 1/2 < cos(1) == cos X *)
      apply RealSetoid.real_lt_le_iff_req. left.
      apply (real_eq_lt_lt (real_plus (real_const 1) (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
                           (real_const (1 / 2))
                           (cauchy_real_cos X)).
      * apply (real_eq_trans _ (real_plus (real_const 1) (real_opp (real_mult (real_mult (real_const 1) (real_const 1)) (real_const (1 / 2))))) _).
        -- apply real_half_sq_poly_ext. exact H1e.
        -- exact real_half_sq_poly_const1_eval.
      * apply (real_lt_eq_lt (real_const (1 / 2)) (cauchy_real_cos (real_const 1)) (cauchy_real_cos X)).
        -- exact real_cos_one_gt_half.
        -- apply real_cos_eq_compat. apply real_eq_sym. exact H1e.
  - (* X == 0：LHS == real_const 1 ≈ real_one == cos X *)
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (real_plus (real_const 1) (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
                         (real_const 1)
                         (cauchy_real_cos X)).
    + apply (real_eq_trans _ (real_plus (real_const 1) (real_opp (real_mult (real_mult real_zero real_zero) (real_const (1 / 2))))) _).
      * apply real_half_sq_poly_ext. apply real_eq_sym. exact H0e.
      * exact real_half_sq_poly_zero_eval.
    + apply real_eq_sym.
      apply (real_eq_trans (cauchy_real_cos X) real_one (real_const 1)).
      * apply (real_eq_trans (cauchy_real_cos X) (cauchy_real_cos real_zero) real_one).
        -- apply real_cos_eq_compat. apply real_eq_sym. exact H0e.
        -- exact real_cos_one.
      * exact real_one_req_const_one.
Qed.

(* ============================================================ *)
(* 批 16（轮 16）：cos²+sin²−1 的 Q 层度向机器与精确分解        *)
(*   A：部分和 == sum_upto 桥 ×2                                  *)
(*   B：偶/奇原形和相等（altf_zero (2m) + 偶奇拆分，q_pow_neg1  *)
(*       奇偶归约）+ cos/sin 度向配对项形（单 Qinv 分母）+        *)
(*       度向消去 sc_cs_deg_van（(−1)^m + (−1)^{m−1} == 0 消号）  *)
(*   C：行尾拆分 sc_sum_tail_split + 矩形==三角+上带（泛型）      *)
(*       + cos/sin 平方双侧拆分（cos 三角 i+j ≤ n / sin 三角      *)
(*       i+j ≤ n−1——度向配对的关键不对称）+ exp_cauchy_swap 对角  *)
(*       化 + 度向 X 形消去 sc_cs_deg_van_x + 三角求值 +          *)
(*   D（最终定理）：sc_cs_tri_sq_one（tri_c + tri_d == 1：        *)
(*       cos²+sin² 系数按度 2m 完全对消，m=0 项 == c₀² == 1）      *)
(*       + sc_cs_sq_err_decomp（E == band_c + band_d 精确：        *)
(*       c_n²+s_n²−1 == cos 上带 + sin 上带，零近似误差）          *)
(* 路线：cos²+sin²==1（Real 层）的代数核心；配套：                *)
(*   |band| 尾界（exp_tail_abs）+ 模量引理 + Real 层              *)
(*   real_cos_sq_plus_sin_sq_one（real_eq_of_zero_diff 型组装）。  *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
(* 桥：部分和 == sum_upto 形式 *)
Lemma sc_sin_partial_upto : forall (n : nat) (x : Q), QeqT (sin_partial n x) (sum_upto (Datatypes.S n) (fun j : nat => sin_term j x)).
Proof.
  intros n x. induction n as [| n' IH]; simpl.
  - apply qeq_imp_qeqT. ring.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

Lemma sc_cos_partial_upto : forall (n : nat) (x : Q), QeqT (cos_partial n x) (sum_upto (Datatypes.S n) (fun j : nat => cos_term j x)).
Proof.
  intros n x. induction n as [| n' IH]; simpl.
  - apply qeq_imp_qeqT. ring.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

(* ---- B 部分（检验 16a 成果，原样复用） ---- *)
Lemma sc_cs_eo_raw : forall (m : nat), (1 <= m)%nat ->QeqT (sum_upto (m + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i)))) (sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1)))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hz : altf (2 * m) == 0).
  { apply qeqT_imp_qeq. apply altf_zero. lia. }
  rewrite (qeqT_imp_qeq _ _ (altf_as_sum_upto (2 * m))) in Hz.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split_odd m
            (fun u : nat => q_pow (-1) u / (q_fact u * q_fact (2 * m - u))))) in Hz.
  assert (HextA : forall j : nat, QeqT
    (q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (2 * m - 2 * j)))
    (Qinv (q_fact (2 * j) * q_fact (2 * m - 2 * j)))).
  { intro j. apply qeq_imp_qeqT. unfold Qdiv.
    rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even j)). ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m + 1)
    (fun j : nat => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (2 * m - 2 * j)))
    (fun j : nat => Qinv (q_fact (2 * j) * q_fact (2 * m - 2 * j))) HextA)) in Hz.
  assert (HextB : forall j : nat, QeqT
    (q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (2 * m - (2 * j + 1))))
    (- Qinv (q_fact (2 * j + 1) * q_fact (2 * m - 2 * j - 1)))).
  { intro j. apply qeq_imp_qeqT. unfold Qdiv.
    rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_odd j)).
    assert (Hfeq : (2 * m - (2 * j + 1) = 2 * m - 2 * j - 1)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (q_fact_nat_eq (2 * m - (2 * j + 1)) (2 * m - 2 * j - 1) Hfeq)).
    ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m
    (fun j : nat => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (2 * m - (2 * j + 1))))
    (fun j : nat => - Qinv (q_fact (2 * j + 1) * q_fact (2 * m - 2 * j - 1))) HextB)) in Hz.
  assert (Hneg : sum_upto m (fun j : nat => - Qinv (q_fact (2 * j + 1) * q_fact (2 * m - 2 * j - 1))) ==
                 - sum_upto m (fun j : nat => Qinv (q_fact (2 * j + 1) * q_fact (2 * m - 2 * j - 1)))).
  { apply qeqT_imp_qeq. apply sum_upto_neg. }
  rewrite Hneg in Hz.
  assert (Hring : sum_upto (m + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i))) ==
                  sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))) +
                  (sum_upto (m + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i))) +
                   - sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))))).
  { ring. }
  rewrite Hz in Hring.
  rewrite (Qplus_0_r _) in Hring.
  exact Hring.
Qed.

Lemma sc_cs_cpair_form : forall (t : Q) (m i : nat), (i <= m)%nat ->QeqT (cos_term i t * cos_term (m - i)%nat t) ((q_pow (-1) m * q_pow t (2 * m)) *
    Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i))).
Proof.
  intros t m i Hi.
  apply qeq_imp_qeqT.
  unfold cos_term. unfold Qdiv.
  assert (Hre : (q_pow (-1) i * (q_pow t (2 * i) * Qinv (q_fact (2 * i)))) *
                (q_pow (-1) (m - i) * (q_pow t (2 * (m - i)) * Qinv (q_fact (2 * (m - i))))) ==
                (q_pow (-1) i * q_pow (-1) (m - i)) *
                (q_pow t (2 * i) * q_pow t (2 * (m - i)) *
                 (Qinv (q_fact (2 * i)) * Qinv (q_fact (2 * (m - i)))))).
  { ring. }
  rewrite Hre.
  assert (Hsi : q_pow (-1) i * q_pow (-1) (m - i) == q_pow (-1) m).
  { assert (Hadd : (i + (m - i) = m)%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (q_pow_add (-1) i (m - i))).
    rewrite Hadd. reflexivity. }
  rewrite Hsi.
  assert (Hti : q_pow t (2 * i) * q_pow t (2 * (m - i)) == q_pow t (2 * m)).
  { assert (Hadd2 : (2 * i + 2 * (m - i) = 2 * m)%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (q_pow_add t (2 * i) (2 * (m - i)))).
    rewrite Hadd2. reflexivity. }
  rewrite Hti.
  rewrite <- (Qinv_mult_distr (q_fact (2 * i)) (q_fact (2 * (m - i)))) by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hf1 : (2 * (m - i) = 2 * m - 2 * i)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (q_fact_nat_eq (2 * (m - i)) (2 * m - 2 * i) Hf1)).
  ring.
Qed.

Lemma sc_cs_dpair_form : forall (t : Q) (m i : nat), (1 <= m)%nat -> (i <= m - 1)%nat ->QeqT (sin_term i t * sin_term (m - 1 - i)%nat t) ((q_pow (-1) (m - 1) * q_pow t (2 * m)) *
    Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))).
Proof.
  intros t m i Hm1 Hi.
  apply qeq_imp_qeqT.
  unfold sin_term. unfold Qdiv.
  assert (Hre : (q_pow (-1) i * (q_pow t (Datatypes.S (2 * i)) * Qinv (q_fact (Datatypes.S (2 * i))))) *
                (q_pow (-1) (m - 1 - i) * (q_pow t (Datatypes.S (2 * (m - 1 - i))) * Qinv (q_fact (Datatypes.S (2 * (m - 1 - i)))))) ==
                (q_pow (-1) i * q_pow (-1) (m - 1 - i)) *
                (q_pow t (Datatypes.S (2 * i)) * q_pow t (Datatypes.S (2 * (m - 1 - i))) *
                 (Qinv (q_fact (Datatypes.S (2 * i))) * Qinv (q_fact (Datatypes.S (2 * (m - 1 - i))))))).
  { ring. }
  rewrite Hre.
  assert (Hsi : q_pow (-1) i * q_pow (-1) (m - 1 - i) == q_pow (-1) (m - 1)).
  { assert (Hadd : (i + (m - 1 - i) = m - 1)%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (q_pow_add (-1) i (m - 1 - i))).
    rewrite Hadd. reflexivity. }
  rewrite Hsi.
  assert (Hti : q_pow t (Datatypes.S (2 * i)) * q_pow t (Datatypes.S (2 * (m - 1 - i))) == q_pow t (2 * m)).
  { assert (Hadd2 : (Datatypes.S (2 * i) + Datatypes.S (2 * (m - 1 - i)) = 2 * m)%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (q_pow_add t (Datatypes.S (2 * i)) (Datatypes.S (2 * (m - 1 - i))))).
    rewrite Hadd2. reflexivity. }
  rewrite Hti.
  rewrite <- (Qinv_mult_distr (q_fact (Datatypes.S (2 * i))) (q_fact (Datatypes.S (2 * (m - 1 - i))))) by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hf1 : (Datatypes.S (2 * (m - 1 - i)) = 2 * m - 2 * i - 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (q_fact_nat_eq (Datatypes.S (2 * (m - 1 - i))) (2 * m - 2 * i - 1) Hf1)).
  assert (Hf0 : (2 * i + 1 = Datatypes.S (2 * i))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (q_fact_nat_eq (2 * i + 1) (Datatypes.S (2 * i)) Hf0)).
  ring.
Qed.

Lemma sc_cs_cdeg_sum : forall (t : Q) (m : nat), QeqT (sum_upto (m + 1) (fun i : nat => cos_term i t * cos_term (m - i)%nat t)) ((q_pow (-1) m * q_pow t (2 * m)) *
    sum_upto (m + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i)))).
Proof.
  intros t m.
  apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale (m + 1) (q_pow (-1) m * q_pow t (2 * m))
            (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i))))).
  apply qeqT_imp_qeq.
  apply (sum_upto_ext_below (m + 1)
    (fun i : nat => cos_term i t * cos_term (m - i)%nat t)
    (fun i : nat => (q_pow (-1) m * q_pow t (2 * m)) * Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i)))).
  intro i. intro Hi.
  apply qeq_imp_qeqT.
  pose proof (NatLe_drop (Datatypes.S i) (m + 1) Hi) as Hinm.
  assert (Him : (i <= m)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_cs_cpair_form t m i Him)).
  reflexivity.
Qed.

Lemma sc_cs_ddeg_sum : forall (t : Q) (m : nat), (1 <= m)%nat ->QeqT (sum_upto m (fun i : nat => sin_term i t * sin_term (m - 1 - i)%nat t)) ((q_pow (-1) (m - 1) * q_pow t (2 * m)) *
    sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1)))).
Proof.
  intros t m Hm.
  apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale m (q_pow (-1) (m - 1) * q_pow t (2 * m))
            (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))))).
  apply qeqT_imp_qeq.
  apply (sum_upto_ext_below m
    (fun i : nat => sin_term i t * sin_term (m - 1 - i)%nat t)
    (fun i : nat => (q_pow (-1) (m - 1) * q_pow t (2 * m)) * Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1)))).
  intro i. intro Hi.
  apply qeq_imp_qeqT.
  pose proof (NatLe_drop (Datatypes.S i) m Hi) as Hinm.
  assert (Him : (i <= m - 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_cs_dpair_form t m i Hm Him)).
  reflexivity.
Qed.

Lemma sc_cs_deg_van : forall (t : Q) (m : nat), (1 <= m)%nat ->QeqT (sum_upto (m + 1) (fun i : nat => cos_term i t * cos_term (m - i)%nat t) +
  sum_upto m (fun i : nat => sin_term i t * sin_term (m - 1 - i)%nat t)) (0).
Proof.
  intros t m Hm.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_cs_cdeg_sum t m)).
  rewrite (qeqT_imp_qeq _ _ (sc_cs_ddeg_sum t m Hm)).
  pose proof (qeqT_imp_qeq _ _ (sc_cs_eo_raw m Hm)) as Heq.
  rewrite Heq.
  assert (Hfac : (q_pow (-1) m * q_pow t (2 * m)) *
                   sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))) +
                 (q_pow (-1) (m - 1) * q_pow t (2 * m)) *
                   sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))) ==
                 q_pow t (2 * m) *
                   (sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))) *
                    (q_pow (-1) m + q_pow (-1) (m - 1)))).
  { ring. }
  rewrite Hfac.
  assert (Halt : q_pow (-1) m + q_pow (-1) (m - 1) == 0).
  { assert (Hpred : (m = Datatypes.S (m - 1))%nat) by lia.
    rewrite Hpred at 1.
    apply (Qeq_trans _ (q_pow (-1) (m - 1) + q_pow (-1) (Datatypes.S (m - 1))) _).
    - exact (Qplus_comm (q_pow (-1) (Datatypes.S (m - 1))) (q_pow (-1) (m - 1))).
    - exact (qeqT_imp_qeq _ _ (q_pow_neg_alt (m - 1))). }
  rewrite Halt.
  rewrite (Qmult_0_r (sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1))))).
  rewrite (Qmult_0_r (q_pow t (2 * m))). reflexivity.
Qed.

(* ---- C0：行拆分（检验 16b 成果） ---- *)
Lemma sc_sum_tail_split : forall (n m : nat) (h : nat -> Q), (m <= n)%nat ->QeqT (sum_upto (Datatypes.S n) h) (sum_upto (Datatypes.S (n - m)) h +
  sum_upto m (fun k : nat => h (Datatypes.S (n - m) + k)%nat)).
Proof.
  intros n m h Hm.
  apply qeq_imp_qeqT.
  assert (Hadd : (Datatypes.S n = Datatypes.S (n - m) + m)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n) (Datatypes.S (n - m) + m) h Hadd)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_add (Datatypes.S (n - m)) m h)).
  reflexivity.
Qed.

Lemma sc_sq_rect_split : forall (a : nat -> Q) (n : nat), QeqT (sum_upto (Datatypes.S n) a * sum_upto (Datatypes.S n) a) (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S (n - j)) (fun i : nat => a j * a i)) +
  sum_upto (Datatypes.S n) (fun j : nat => sum_upto j (fun k : nat => a j * a (Datatypes.S (n - j) + k)%nat))).
Proof.
  intros a n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_prod n n a a)).
  rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S n)
    (fun j : nat => sum_upto (Datatypes.S (n - j)) (fun i : nat => a j * a i))
    (fun j : nat => sum_upto j (fun k : nat => a j * a (Datatypes.S (n - j) + k)%nat)))).
  apply Qeq_sym.
  apply qeqT_imp_qeq.
  apply (sum_upto_ext_below (Datatypes.S n)
    (fun j : nat => sum_upto (Datatypes.S (n - j)) (fun i : nat => a j * a i) +
                    sum_upto j (fun k : nat => a j * a (Datatypes.S (n - j) + k)%nat))
    (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => a j * a i))).
  intros j Hj.
  pose proof (NatLe_drop (Datatypes.S j) (Datatypes.S n) Hj) as Hjn.
  apply qeq_imp_qeqT.
  apply Qeq_sym.
  apply qeqT_imp_qeq. apply (sc_sum_tail_split n j (fun i : nat => a j * a i)).
  lia.
Qed.

Lemma sc_cos_sq_split : forall (t : Q) (n : nat), QeqT (cos_partial n t * cos_partial n t) (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S (n - j)) (fun i : nat => cos_term j t * cos_term i t)) +
  sum_upto (Datatypes.S n) (fun j : nat => sum_upto j (fun k : nat => cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t))).
Proof.
intros t n. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n t)). exact (qeqT_imp_qeq _ _ (sc_sq_rect_split (fun j : nat => cos_term j t) n)).
Qed.

Lemma sc_sin_sq_split : forall (t : Q) (n : nat), QeqT (sin_partial n t * sin_partial n t) (sum_upto n (fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t)) +
  sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t))).
Proof.
  intros t n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n t)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun j : nat => sin_term j t) (fun i : nat => sin_term i t))).
  assert (Hbsp : sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t)) ==
                 sum_upto n (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t)) +
                 sum_upto (Datatypes.S n) (fun k : nat => sin_term n t * sin_term (n - n + k)%nat t)).
  { reflexivity. }
  rewrite Hbsp.
  assert (Hrsp : sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => sin_term j t * sin_term i t)) ==
                 sum_upto n (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => sin_term j t * sin_term i t)) +
                 sum_upto (Datatypes.S n) (fun i : nat => sin_term n t * sin_term i t)).
  { reflexivity. }
  rewrite Hrsp.
  assert (Hrows : sum_upto n (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => sin_term j t * sin_term i t)) ==
                  sum_upto n (fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t) +
                                             sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t))).
  { apply qeqT_imp_qeq.
    apply (sum_upto_ext_below n
      (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => sin_term j t * sin_term i t))
      (fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t) +
                      sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t))).
    intros j Hj.
    apply qeq_imp_qeqT.
    assert (Hjn : (Datatypes.S j <= n)%nat) by (exact (NatLe_drop _ _ Hj)).
    assert (Hidx : forall k : nat, (Datatypes.S (n - Datatypes.S j) + k = n - j + k)%nat) by (intro k; lia).
    assert (Hbrid : (Datatypes.S (n - Datatypes.S j) = Datatypes.S (n - 1 - j))%nat) by lia.
    set (h := fun i : nat => sin_term j t * sin_term i t).
    transitivity (sum_upto (Datatypes.S (n - Datatypes.S j)) h +
                  sum_upto (Datatypes.S j) (fun k : nat => h (Datatypes.S (n - Datatypes.S j) + k)%nat)).
    - exact (qeqT_imp_qeq _ _ (sc_sum_tail_split n (Datatypes.S j) h Hjn)).
    - rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (n - Datatypes.S j)) (Datatypes.S (n - 1 - j)) h Hbrid)).
      assert (H2 : sum_upto (Datatypes.S j) (fun k : nat => h (Datatypes.S (n - Datatypes.S j) + k)%nat) ==
                   sum_upto (Datatypes.S j) (fun k : nat => h (n - j + k)%nat)).
      { apply qeqT_imp_qeq.
        apply (sum_upto_ext_below (Datatypes.S j)
          (fun k : nat => h (Datatypes.S (n - Datatypes.S j) + k)%nat)
          (fun k : nat => h (n - j + k)%nat)).
        intros k Hk. apply qeq_imp_qeqT. unfold h. rewrite (Hidx k). reflexivity. }
      rewrite H2. reflexivity. }
  rewrite Hrows.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus n
    (fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t))
    (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t)))).
  assert (Hrn : sum_upto (Datatypes.S n) (fun k : nat => sin_term n t * sin_term (n - n + k)%nat t) ==
                sum_upto (Datatypes.S n) (fun i : nat => sin_term n t * sin_term i t)).
  { apply qeqT_imp_qeq.
    apply (sum_upto_ext (Datatypes.S n)
      (fun k : nat => sin_term n t * sin_term (n - n + k)%nat t)
      (fun i : nat => sin_term n t * sin_term i t)).
    intro k.
    apply qeq_imp_qeqT.
    assert (Hnn : (n - n = 0)%nat) by lia.
    rewrite Hnn. reflexivity. }
  rewrite Hrn.
  ring.
Qed.

(* ============ C3：三角平方和 == 1 ============ *)

(* C3.1 度向 X 形消去：X_c(m)E(m) + X_d(m)O(m) == 0（m ≥ 1） *)
Lemma sc_cs_deg_van_x : forall (t : Q) (m : nat), (1 <= m)%nat ->QeqT ((q_pow (-1) m * q_pow t (2 * m)) *
    sum_upto (m + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * m - 2 * i))) +
  (q_pow (-1) (m - 1) * q_pow t (2 * m)) *
    sum_upto m (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * m - 2 * i - 1)))) (0).
Proof.
intros t m Hm. apply qeq_imp_qeqT. rewrite <- (qeqT_imp_qeq _ _ (sc_cs_cdeg_sum t m)). rewrite <- (qeqT_imp_qeq _ _ (sc_cs_ddeg_sum t m Hm)). exact (qeqT_imp_qeq _ _ (sc_cs_deg_van t m Hm)).
Qed.

(* C3.2 三角 cos 侧 == 对角和：tri_c == Σ_{k=0}^{n} X_c(k)·E_raw(k) *)
Lemma sc_cs_tri_c_eval : forall (t : Q) (n : nat), QeqT (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S (n - j)) (fun i : nat => cos_term j t * cos_term i t))) (sum_upto (Datatypes.S n) (fun k : nat =>
    (q_pow (-1) k * q_pow t (2 * k)) *
      sum_upto (k + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * k - 2 * i))))).
Proof.
  intros t n.
  apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (exp_cauchy_swap n (fun j : nat => cos_term j t) (fun j : nat => cos_term j t))).
  apply qeqT_imp_qeq.
  apply (sum_upto_ext_below (Datatypes.S n)
    (fun k : nat => sum_upto (Datatypes.S k) (fun j : nat => cos_term j t * cos_term (k - j)%nat t))
    (fun k : nat => (q_pow (-1) k * q_pow t (2 * k)) *
        sum_upto (k + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * k - 2 * i))))).
  intros k Hk.
  apply qeq_imp_qeqT.
  assert (Hsk : (Datatypes.S k = k + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S k) (k + 1)
            (fun j : nat => cos_term j t * cos_term (k - j)%nat t) Hsk)).
  rewrite (qeqT_imp_qeq _ _ (sc_cs_cdeg_sum t k)).
  reflexivity.
Qed.

(* C3.3 三角 sin 侧 == 对角和（m := S k 移标）：tri_d == Σ_{k=0}^{n−1} X_d(S k)·O_raw(S k)，n ≥ 1 *)
Lemma sc_cs_tri_d_eval : forall (t : Q) (n : nat), (1 <= n)%nat ->QeqT (sum_upto n (fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t))) (sum_upto n (fun k : nat =>
    (q_pow (-1) (Datatypes.S k - 1) * q_pow t (2 * (Datatypes.S k))) *
      sum_upto (Datatypes.S k) (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * (Datatypes.S k) - 2 * i - 1))))).
Proof.
  intros t n Hn.
  apply qeq_imp_qeqT.
  set (Sd := fun k : nat =>
        (q_pow (-1) (Datatypes.S k - 1) * q_pow t (2 * (Datatypes.S k))) *
          sum_upto (Datatypes.S k) (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * (Datatypes.S k) - 2 * i - 1)))).
  (* 目标 RHS 外指标 n 桥到 S(n−1)（swap 尺度一致） *)
  assert (Houter : (n = Datatypes.S (n - 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq n (Datatypes.S (n - 1)) Sd Houter)).
  (* tri_d 的嵌套和 == swap (n−1) 的 RHS（同函数 g，外指标桥） *)
  set (g := fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t)).
  assert (Ht1 : sum_upto n g == sum_upto (Datatypes.S (n - 1)) g).
  { apply qeqT_imp_qeq. apply (sum_upto_nat_eq n (Datatypes.S (n - 1)) g). exact Houter. }
  assert (Hswap := qeqT_imp_qeq _ _ (exp_cauchy_swap (n - 1) (fun j : nat => sin_term j t) (fun j : nat => sin_term j t))).
  (* 目标：tri_d == Σ Sd：transitivity 到 swap-LHS *)
  transitivity (sum_upto (Datatypes.S (n - 1))
    (fun k : nat => sum_upto (Datatypes.S k) (fun j : nat => sin_term j t * sin_term (k - j)%nat t))).
  - (* tri_d == swap-LHS：tri_d == swap-RHS（Ht1）再经 Hswap（RHS == LHS） *)
    apply (Qeq_trans _ (sum_upto (Datatypes.S (n - 1)) g) _).
    + unfold g. exact Ht1.
    + apply Qeq_sym. exact Hswap.
  - (* swap-LHS == Σ Sd：逐 k（k ≤ n−1）用 ddeg_sum (S k) 的 RHS 形态 *)
    apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S (n - 1))
      (fun k : nat => sum_upto (Datatypes.S k) (fun j : nat => sin_term j t * sin_term (k - j)%nat t))
      Sd).
    intros k Hk.
    apply qeq_imp_qeqT.
    assert (Hm1 : (1 <= Datatypes.S k)%nat) by lia.
    unfold Sd.
    rewrite <- (qeqT_imp_qeq _ _ (sc_cs_ddeg_sum t (Datatypes.S k) Hm1)).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S k)
      (fun j : nat => sin_term j t * sin_term (k - j)%nat t)
      (fun j : nat => sin_term j t * sin_term (Datatypes.S k - 1 - j)%nat t)).
    intros j Hj.
    apply qeq_imp_qeqT.
    assert (Hsb : (Datatypes.S k - 1 - j = k - j)%nat) by lia.
    rewrite Hsb. reflexivity.
Qed.

(* ============ C4：三角平方和 == 1 + 误差精确分解 ============ *)

(* C4.1 三角平方和：tri_c(n) + tri_d(n) == 1 *)
Lemma sc_cs_tri_sq_one : forall (t : Q) (n : nat), QeqT (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S (n - j)) (fun i : nat => cos_term j t * cos_term i t)) +
  sum_upto n (fun j : nat => sum_upto (Datatypes.S (n - 1 - j)) (fun i : nat => sin_term j t * sin_term i t))) (1).
Proof.
  intros t n.
  destruct n as [| n'].
  - apply qeq_imp_qeqT. (* n = 0：tri_c == c_0·c_0 == 1，tri_d == 0 *)
    simpl.
    rewrite (qeqT_imp_qeq _ _ (sc_cos_term_zero t)).
    ring.
  - apply qeq_imp_qeqT. (* n = S n' ≥ 1 *)
    assert (Hn1 : (1 <= Datatypes.S n')%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_cs_tri_c_eval t (Datatypes.S n'))).
    rewrite (qeqT_imp_qeq _ _ (sc_cs_tri_d_eval t (Datatypes.S n') Hn1)).
    set (A := fun k : nat => (q_pow (-1) k * q_pow t (2 * k)) *
                sum_upto (k + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * k - 2 * i)))).
    set (Sd := fun k : nat =>
        (q_pow (-1) (Datatypes.S k - 1) * q_pow t (2 * (Datatypes.S k))) *
          sum_upto (Datatypes.S k) (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * (Datatypes.S k) - 2 * i - 1)))).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (Datatypes.S n') A)).
    rewrite <- (Qplus_assoc (A 0%nat) (sum_upto (Datatypes.S n') (fun i : nat => A (Datatypes.S i))) (sum_upto (Datatypes.S n') Sd)).
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S n') (fun i : nat => A (Datatypes.S i)) Sd)).
    assert (Hsum : sum_upto (Datatypes.S n') (fun i : nat => A (Datatypes.S i) + Sd i) == 0).
    { assert (Hext : sum_upto (Datatypes.S n') (fun i : nat => A (Datatypes.S i) + Sd i) ==
                    sum_upto (Datatypes.S n') (fun _ : nat => 0)).
      { apply qeqT_imp_qeq.
        apply (sum_upto_ext_below (Datatypes.S n')
          (fun i : nat => A (Datatypes.S i) + Sd i)
          (fun _ : nat => 0)).
        intros i Hi.
        unfold A. unfold Sd.
        apply (sc_cs_deg_van_x t (Datatypes.S i)).
        lia. }
      rewrite (qeqT_imp_qeq _ _ (sum_upto_zero (Datatypes.S n'))) in Hext.
      exact Hext. }
    rewrite Hsum.
    assert (HA0 : A 0%nat == 1).
    { unfold A.
      rewrite <- (qeqT_imp_qeq _ _ (sc_cs_cdeg_sum t 0)).
      simpl.
      rewrite (qeqT_imp_qeq _ _ (sc_cos_term_zero t)).
      rewrite (qeqT_imp_qeq _ _ (sc_cos_term_zero t)).
      reflexivity. }
    rewrite HA0. ring.
Qed.

(* C4.2 主分解：cos_partial n t² + sin_partial n t² − 1 == band_c(n) + band_d(n)（精确） *)
Lemma sc_cs_sq_err_decomp : forall (t : Q) (n : nat), QeqT (cos_partial n t * cos_partial n t + sin_partial n t * sin_partial n t - 1) (sum_upto (Datatypes.S n) (fun j : nat => sum_upto j (fun k : nat => cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t)) +
  sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t))).
Proof.
  intros t n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_sq_split t n)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_sq_split t n)).
  rewrite <- (qeqT_imp_qeq _ _ (sc_cs_tri_sq_one t n)).
  ring.
Qed.

(* ============================================================ *)
(* 批 17（轮 17）：cos²+sin²==1 模量地基——求和泛型 + 偶奇配对  *)
(*   恒等 + |c_i|/|d_i| 支配 + 全和/尾和的 exp 差分界             *)
(*   A：求和泛型（非负和、移位块子和 ≤ 全和、尾部块拆分、偶奇   *)
(*       配对和 == exp_series (2n+1)、配对尾差分 == exp 差）      *)
(*   B：|c_i|/|d_i| ≤ G_{2i} + G_{2i+1}（sc_abs_*_term +         *)
(*       q_abs_pow_fact/le；S(2i) 与 2i+1 的 nat-Leibniz 桥）     *)
(*   C：Σ|c|/Σ|d| ≤ exp_series (2n+1)（全和）；c 尾（自 d+1）    *)
(*       ≤ exp(2n+1) − exp(2d+1)；d 尾（自 d，d ≥ 1）            *)
(*       ≤ exp(2n+1) − exp(2d−1)（尾差分 = exp_tail 差分）        *)
(* 路线：本件为 |c_n²+s_n²−1| 模量引理的地基；后续：           *)
(*   band_c/band_d 绝对界（j 分组：j ≤ d 内带 ⊆ [d+1, n] 尾、    *)
(*   j > d 外和 = 同尾）→ |E| ≤ 8·exp_series·尾 → 模量引理        *)
(*   sc_cs_sq_err_bound（exp_tail_arch + arch_decay 配方）→       *)
(*   Real 层 real_cos_sq_plus_sin_sq_one。                        *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
(* A1：非负逐项 ⟹ 和 ≥ 0 *)
Lemma sc_sum_nonneg : forall (n : nat) (f : nat -> Q),
  (forall m : nat, Qle 0 (f m)) -> QleT' 0 (sum_upto n f).
Proof.
  intros n f Hf.
  induction n as [| n' IH]; simpl.
  - apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - apply Qle_to_QleT'. apply (Qle_trans _ (0 + 0) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_le_compat 0 (sum_upto n' f) 0 (f n')).
      * exact (QleT'_to_Qle _ _ IH).
      * exact (Hf n').
Qed.

(* A2：移位块子和 ≤ 全和：a+j ≤ M 且 g 非负 ⟹ Σ_{k<j} g(a+k) ≤ Σ_{m<M} g m *)
Lemma sc_sum_shift_sub_le : forall (a j M : nat) (g : nat -> Q),
  (forall m : nat, Qle 0 (g m)) -> (a + j <= M)%nat ->
  QleT' (sum_upto j (fun k : nat => g (a + k)%nat)) (sum_upto M g).
Proof.
  intros a j M g Hg Hle.
  apply Qle_to_QleT'.
  assert (Hsp : (M = a + j + (M - a - j))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq M (a + j + (M - a - j)) g Hsp)).
  assert (Hsp2 : (a + j + (M - a - j) = a + (j + (M - a - j)))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (a + j + (M - a - j)) (a + (j + (M - a - j))) g Hsp2)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_add a (j + (M - a - j)) g)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_add j (M - a - j) (fun k : nat => g (a + k)%nat))).
  (* 目标：Σ_j g(a+·) ≤ Σ_a g + (Σ_j g(a+·) + Σ_rest)（Σ_rest ≥ 0、Σ_a ≥ 0） *)
  apply (Qle_trans _ (sum_upto j (fun k : nat => g (a + k)%nat) +
                      sum_upto (M - a - j) (fun i : nat => g (a + (j + i))%nat)) _).
  - apply (Qle_plus_nonneg_r (sum_upto j (fun k : nat => g (a + k)%nat))
            (sum_upto (M - a - j) (fun i : nat => g (a + (j + i))%nat))).
    apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. exact (Hg (a + (j + m))%nat).
  - apply (Qle_trans _ ((sum_upto j (fun k : nat => g (a + k)%nat) +
                         sum_upto (M - a - j) (fun i : nat => g (a + (j + i))%nat)) +
                        sum_upto a g) _).
    + apply (Qle_plus_nonneg_r (sum_upto j (fun k : nat => g (a + k)%nat) +
                                sum_upto (M - a - j) (fun i : nat => g (a + (j + i))%nat))
              (sum_upto a g)).
      apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. exact (Hg m).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* A3：尾部块拆分：a ≤ n ⟹ Σ_{0..n} X == Σ_{0..a} X + Σ_{a+1..n} X（第二和 m ↦ X (S a + m)） *)
Lemma sc_sum_after_split : forall (a n : nat) (X : nat -> Q), (a <= n)%nat ->QeqT (sum_upto (Datatypes.S n) X) (sum_upto (Datatypes.S a) X + sum_upto (n - a) (fun m : nat => X (Datatypes.S a + m)%nat)).
Proof.
  intros a n X Ha.
  apply qeq_imp_qeqT.
  assert (Hadd : (Datatypes.S n = Datatypes.S a + (n - a))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n) (Datatypes.S a + (n - a)) X Hadd)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_add (Datatypes.S a) (n - a) X)).
  reflexivity.
Qed.

(* A4：偶奇配对和 == exp_series (2n+1) B：Σ_{j=0}^{n} (G_{2j}+G_{2j+1}) == exp_series (2n+1) B *)
Lemma sc_cs_evenodd_exp : forall (B : Q) (n : nat), QeqT (sum_upto (n + 1) (fun j : nat => q_pow B (2 * j) / q_fact (2 * j) +
                                   q_pow B (2 * j + 1) / q_fact (2 * j + 1))) (exp_series (2 * n + 1) B).
Proof.
  intros B n.
  apply qeq_imp_qeqT.
  exact (Qeq_trans _ _ _
    (qeqT_imp_qeq _ _ (sum_upto_plus (n + 1)
      (fun j : nat => q_pow B (2 * j) / q_fact (2 * j))
      (fun j : nat => q_pow B (2 * j + 1) / q_fact (2 * j + 1))))
    (Qeq_trans _ _ _
      (Qeq_sym _ _ (qeqT_imp_qeq _ _ (sum_upto_even_split (n + 1) (fun k : nat => q_pow B k / q_fact k))))
      (Qeq_trans _ _ _
        (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * (n + 1)) (Datatypes.S (2 * n + 1))
           (fun k : nat => q_pow B k / q_fact k) (ltac: (lia))))
        (Qeq_trans _ _ _
          (Qeq_sym _ _ (qeqT_imp_qeq _ _ (exp_partial_sum (2 * n + 1) B)))
          (qeqT_imp_qeq _ _ (exp_partial_eq_series (2 * n + 1) B)))))).
Qed.

(* A5：偶奇配对尾差分（下界 a）：a ≤ n ⟹ Σ_{i=a+1}^{n} (G_{2i}+G_{2i+1}) == exp_series(2n+1) − exp_series(2a+1) *)
Lemma sc_cs_evenodd_tail_diff : forall (B : Q) (a n : nat), (a <= n)%nat ->QeqT (sum_upto (n - a) (fun m : nat => q_pow B (2 * (Datatypes.S a + m)) / q_fact (2 * (Datatypes.S a + m)) +
                                   q_pow B (2 * (Datatypes.S a + m) + 1) / q_fact (2 * (Datatypes.S a + m) + 1))) (exp_series (2 * n + 1) B - exp_series (2 * a + 1) B).
Proof.
  intros B a n Han.
  apply qeq_imp_qeqT.
  pose proof (sc_sum_after_split a n (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) +
                                                      q_pow B (2 * i + 1) / q_fact (2 * i + 1)) Han) as Hsplit.
  pose proof (qeqT_imp_qeq _ _ (sc_cs_evenodd_exp B n)) as Hen.
  pose proof (qeqT_imp_qeq _ _ (sc_cs_evenodd_exp B a)) as Hea.
  transitivity (sum_upto (Datatypes.S n) (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) +
                                                          q_pow B (2 * i + 1) / q_fact (2 * i + 1)) -
                sum_upto (Datatypes.S a) (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) +
                                                          q_pow B (2 * i + 1) / q_fact (2 * i + 1))).
  - apply Qeq_sym.
    rewrite (qeqT_imp_qeq _ _ Hsplit).
    ring.
  - (* 桥 S n == n+1、S a == a+1（rewrite 语法匹配盲区）后 rewrite Hen/Hea *)
    assert (Hn : (Datatypes.S n = n + 1)%nat) by lia.
    assert (Ha : (Datatypes.S a = a + 1)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n) (n + 1)
              (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) + q_pow B (2 * i + 1) / q_fact (2 * i + 1)) Hn)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S a) (a + 1)
              (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) + q_pow B (2 * i + 1) / q_fact (2 * i + 1)) Ha)).
    rewrite Hen. rewrite Hea. reflexivity.
Qed.

(* ============ B：|c_i|/|d_i| 支配到 G 对 ============ *)


(* B0：偶幂绝对值：q_pow (|x|) (2i)/q_fact (2i) == |q_pow x (2i)/q_fact (2i)| *)
Lemma sc_qabs_pow_even : forall (x : Q) (i : nat), QeqT (q_pow (Qabs x) (2 * i) / q_fact (2 * i)) (Qabs (q_pow x (2 * i) / q_fact (2 * i))).
Proof.
  intros x i.
  apply qeq_imp_qeqT.
  unfold Qdiv.
  rewrite Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (q_pow_abs x (2 * i))).
  rewrite (Qabs_pos (Qinv (q_fact (2 * i)))).
  2: { apply (Qlt_le_weak 0 (Qinv (q_fact (2 * i)))).
       apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos. }
  reflexivity.
Qed.
(* B1：0 ≤ B ∧ |t| ≤ B ⟹ |cos_term i t| ≤ G_{2i} + G_{2i+1}（i 任意） *)
Lemma sc_cs_cabs_pair : forall (t B : Q) (i : nat),
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (Qabs (cos_term i t)) (q_pow B (2 * i) / q_fact (2 * i) +
                              q_pow B (2 * i + 1) / q_fact (2 * i + 1)).
Proof.
  intros t B i HB HtB.
  apply Qle_to_QleT'.
  exact (Qle_trans (Qabs (cos_term i t))
    (q_pow B (2 * i) / q_fact (2 * i))
    (q_pow B (2 * i) / q_fact (2 * i) +
     q_pow B (2 * i + 1) / q_fact (2 * i + 1))
    (Qle_trans (Qabs (cos_term i t))
      (q_pow (Qabs t) (2 * i) / q_fact (2 * i))
      (q_pow B (2 * i) / q_fact (2 * i))
      (QleT'_to_Qle _ _
        (qeq_le (Qabs (cos_term i t))
          (q_pow (Qabs t) (2 * i) / q_fact (2 * i))
          (sc_abs_cos_term i t)))
      (Qle_trans (q_pow (Qabs t) (2 * i) / q_fact (2 * i))
        (Qabs (q_pow t (2 * i) / q_fact (2 * i)))
        (q_pow B (2 * i) / q_fact (2 * i))
        (QleT'_to_Qle _ _
          (qeq_le (q_pow (Qabs t) (2 * i) / q_fact (2 * i))
            (Qabs (q_pow t (2 * i) / q_fact (2 * i)))
            (sc_qabs_pow_even t i)))
        (QleT'_to_Qle _ _ (q_abs_pow_fact_le t B (2 * i) (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ HtB)))))
    (Qle_plus_nonneg_r (q_pow B (2 * i) / q_fact (2 * i))
      (q_pow B (2 * i + 1) / q_fact (2 * i + 1))
      (QleT'_to_Qle _ _ (q_pow_fact_nonneg B (2 * i + 1) (Qle_to_QleT' _ _ HB))))).
Qed.

(* B2：0 ≤ B ∧ |t| ≤ B ⟹ |sin_term i t| ≤ G_{2i} + G_{2i+1} *)
Lemma sc_cs_dabs_pair : forall (t B : Q) (i : nat),
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (Qabs (sin_term i t)) (q_pow B (2 * i) / q_fact (2 * i) +
                              q_pow B (2 * i + 1) / q_fact (2 * i + 1)).
Proof.
  intros t B i HB HtB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow B (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * i))) _).
  - apply (Qle_trans _ (q_pow (Qabs t) (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * i))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_abs_sin_term i t)).
    + apply (Qle_trans _ (Qabs (q_pow t (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * i)))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (qeqT_imp_qeq _ _ (q_abs_pow_fact t (2 * i))).
      * apply QleT'_to_Qle. apply (q_abs_pow_fact_le t B (Datatypes.S (2 * i)) (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ HtB)).
  - (* G_{S(2i)} ≤ G_{2i} + G_{2i+1}：先 nat-Leibniz 桥 (2i+1) → S(2i) *)
    assert (Hsi : (2 * i + 1 = Datatypes.S (2 * i))%nat) by lia.
    rewrite Hsi.
    apply (Qle_trans _ (q_pow B (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * i)) +
                        q_pow B (2 * i) / q_fact (2 * i)) _).
    + apply (Qle_plus_nonneg_r (q_pow B (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * i)))
            (q_pow B (2 * i) / q_fact (2 * i))).
      apply QleT'_to_Qle. apply (q_pow_fact_nonneg B (2 * i)). apply Qle_to_QleT'. exact HB.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (Qplus_comm (q_pow B (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * i)))
                        (q_pow B (2 * i) / q_fact (2 * i))).
Qed.

(* ============ C：全和与尾和 ============ *)

(* C1：Σ_{i=0}^{n}|c_i| ≤ exp_series (2n+1) B *)
Lemma sc_cs_c_full_le : forall (t B : Q) (n : nat),
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t)))
      (exp_series (2 * n + 1) B).
Proof.
  intros t B n HB HtB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) +
                                                               q_pow B (2 * i + 1) / q_fact (2 * i + 1))) _).
  - apply QleT'_to_Qle.
    apply (sum_upto_le_ext (Datatypes.S n)
      (fun i : nat => Qabs (cos_term i t))
      (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) + q_pow B (2 * i + 1) / q_fact (2 * i + 1))).
    intros k Hk. apply (sc_cs_cabs_pair t B k HB HtB).
  - assert (Hn : (Datatypes.S n = n + 1)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n) (n + 1)
      (fun j : nat => q_pow B (2 * j) / q_fact (2 * j) + q_pow B (2 * j + 1) / q_fact (2 * j + 1)) Hn)).
    rewrite (qeqT_imp_qeq _ _ (sc_cs_evenodd_exp B n)). apply Qle_refl.
Qed.

(* C2：Σ_{i=0}^{n}|d_i| ≤ exp_series (2n+1) B *)
Lemma sc_cs_d_full_le : forall (t B : Q) (n : nat),
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t)))
      (exp_series (2 * n + 1) B).
Proof.
  intros t B n HB HtB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) +
                                                               q_pow B (2 * i + 1) / q_fact (2 * i + 1))) _).
  - apply QleT'_to_Qle.
    apply (sum_upto_le_ext (Datatypes.S n)
      (fun i : nat => Qabs (sin_term i t))
      (fun i : nat => q_pow B (2 * i) / q_fact (2 * i) + q_pow B (2 * i + 1) / q_fact (2 * i + 1))).
    intros k Hk. apply (sc_cs_dabs_pair t B k HB HtB).
  - assert (Hn : (Datatypes.S n = n + 1)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n) (n + 1)
      (fun j : nat => q_pow B (2 * j) / q_fact (2 * j) + q_pow B (2 * j + 1) / q_fact (2 * j + 1)) Hn)).
    rewrite (qeqT_imp_qeq _ _ (sc_cs_evenodd_exp B n)). apply Qle_refl.
Qed.

(* C3：c 尾（自 d+1）：Σ_{m<n−d}|c_{S d + m}| ≤ exp_series(2n+1) − exp_series(2d+1)（d ≤ n） *)
Lemma sc_cs_c_tail_diff_le : forall (t B : Q) (d n : nat),
  Qle 0 B -> Qle (Qabs t) B -> (d <= n)%nat ->
  QleT' (sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t)))
      (exp_series (2 * n + 1) B - exp_series (2 * d + 1) B).
Proof.
  intros t B d n HB HtB Hdn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (n - d) (fun m : nat => q_pow B (2 * (Datatypes.S d + m)) / q_fact (2 * (Datatypes.S d + m)) +
                                                       q_pow B (2 * (Datatypes.S d + m) + 1) / q_fact (2 * (Datatypes.S d + m) + 1))) _).
  - apply QleT'_to_Qle.
    apply (sum_upto_le_ext (n - d)
      (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))
      (fun m : nat => q_pow B (2 * (Datatypes.S d + m)) / q_fact (2 * (Datatypes.S d + m)) +
                      q_pow B (2 * (Datatypes.S d + m) + 1) / q_fact (2 * (Datatypes.S d + m) + 1))).
    intros k Hk.
    apply Qle_to_QleT'.
    assert (Habs : Qle (Qabs (cos_term (Datatypes.S d + k)%nat t))
                       (q_pow B (2 * (Datatypes.S d + k)) / q_fact (2 * (Datatypes.S d + k)) +
                        q_pow B (2 * (Datatypes.S d + k) + 1) / q_fact (2 * (Datatypes.S d + k) + 1))).
    { apply QleT'_to_Qle. apply (sc_cs_cabs_pair t B (Datatypes.S d + k) HB HtB). }
    exact Habs.
  - rewrite (qeqT_imp_qeq _ _ (sc_cs_evenodd_tail_diff B d n Hdn)). apply Qle_refl.
Qed.



(* C5：exp_series 指标桥 *)
Lemma sc_exp_series_idx : forall (n m : nat) (B : Q), n = m ->QeqT (exp_series n B) (exp_series m B).
Proof.
  intros n m B H.
  apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (exp_partial_eq_series n B)).
  rewrite <- (qeqT_imp_qeq _ _ (exp_partial_eq_series m B)).
  rewrite H. reflexivity.
Qed.
(* C4：d 尾（自 d，d ≥ 1）：Σ_{m<S(n−d)}|d_{d+m}| ≤ exp_series(2n+1) − exp_series(2d−1) *)
Lemma sc_cs_d_tail_diff_le : forall (t B : Q) (d n : nat),
  Qle 0 B -> Qle (Qabs t) B -> (1 <= d)%nat -> (d <= n)%nat ->
  QleT' (sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t)))
      (exp_series (2 * n + 1) B - exp_series (2 * d - 1) B).
Proof.
  intros t B d n HB HtB Hd1 Hdn.
  apply Qle_to_QleT'.
  (* 指标 m ↦ d+m == S(d−1)+m *)
  assert (Hd : (d = Datatypes.S (d - 1))%nat) by lia.
  assert (HliftA : forall m : nat, NatLe (Datatypes.S m) (Datatypes.S (n - d)) -> QeqT
    (Qabs (sin_term (d + m)%nat t))
    (Qabs (sin_term (Datatypes.S (d - 1) + m)%nat t))).
  { intros m Hm. apply qeq_imp_qeqT.
    assert (Hdm : (d + m = Datatypes.S (d - 1) + m)%nat) by lia.
    rewrite Hdm. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (Datatypes.S (n - d))
    (fun m : nat => Qabs (sin_term (d + m)%nat t))
    (fun m : nat => Qabs (sin_term (Datatypes.S (d - 1) + m)%nat t))
    HliftA)).
  apply (Qle_trans _ (sum_upto (Datatypes.S (n - d))
      (fun m : nat => q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
                      q_pow B (Datatypes.S (2 * (Datatypes.S (d - 1) + m))) / q_fact (Datatypes.S (2 * (Datatypes.S (d - 1) + m))))) _).
  - apply QleT'_to_Qle.
    apply (sum_upto_le_ext (Datatypes.S (n - d))
      (fun m : nat => Qabs (sin_term (Datatypes.S (d - 1) + m)%nat t))
      (fun m : nat => q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
                      q_pow B (Datatypes.S (2 * (Datatypes.S (d - 1) + m))) / q_fact (Datatypes.S (2 * (Datatypes.S (d - 1) + m))))).
    intros k Hk.
    apply Qle_to_QleT'.
    (* per-term：|d_j| ≤ G_{2j} + G_{S(2j)}，j := S(d−1)+k：先经 sc_cs_dabs_pair 的 S(2j) 形 *)
    apply (Qle_trans _ (q_pow B (2 * (Datatypes.S (d - 1) + k)) / q_fact (2 * (Datatypes.S (d - 1) + k)) +
                        q_pow B (Datatypes.S (2 * (Datatypes.S (d - 1) + k))) / q_fact (Datatypes.S (2 * (Datatypes.S (d - 1) + k)))) _).
    2: { apply Qle_refl. }
    set (j := (Datatypes.S (d - 1) + k)%nat).
    assert (Hj : (2 * j + 1 = Datatypes.S (2 * j))%nat) by lia.
    (* 借助 sc_cs_dabs_pair t B j：|d_j| ≤ G_{2j} + G_{S(2j)} 直接形式（sc_abs_sin_term 即 S 形） *)
    apply (Qle_trans _ (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)) +
                        q_pow B (2 * j) / q_fact (2 * j)) _).
    + (* |d_j| ≤ G_{S(2j)}（经 sc_abs_sin_term 直接） *)
      apply (Qle_trans _ (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) _).
      * apply (Qle_trans _ (q_pow (Qabs t) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (sc_abs_sin_term j t)).
        -- apply (Qle_trans _ (Qabs (q_pow t (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply (qeqT_imp_qeq _ _ (q_abs_pow_fact t (2 * j))).
           ++ apply QleT'_to_Qle. apply (q_abs_pow_fact_le t B (Datatypes.S (2 * j)) (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ HtB)).
      * apply (Qle_plus_nonneg_r (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
              (q_pow B (2 * j) / q_fact (2 * j))).
        apply QleT'_to_Qle. apply (q_pow_fact_nonneg B (2 * j)). apply Qle_to_QleT'. exact HB.
    + (* G_{S(2j)} + G_{2j} == G_{2j} + G_{S(2j)}（目标函数的第二项是 G_{2j} + G_{S(2j)} 序）
       这里目标顺序已是 G_{2j} + G_{S(2j)}，直接 comm 反向 *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (Qplus_comm (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
                        (q_pow B (2 * j) / q_fact (2 * j))).
  - (* 配对尾和 == 尾差分（a := d−1，指标 2(d−1+m)+1 的 (2m+1) 形桥） *)
    assert (Hlen : (Datatypes.S (n - d) = n - (d - 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (n - d)) (n - (d - 1))
      (fun m : nat => q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
                      q_pow B (Datatypes.S (2 * (Datatypes.S (d - 1) + m))) / q_fact (Datatypes.S (2 * (Datatypes.S (d - 1) + m)))) Hlen)).
    (* 奇项桥回 (2x+1) 形（nat-Leibniz per-m） *)
    assert (HliftB : forall m : nat, NatLe (Datatypes.S m) (n - (d - 1)) -> QeqT
      (q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
       q_pow B (Datatypes.S (2 * (Datatypes.S (d - 1) + m))) / q_fact (Datatypes.S (2 * (Datatypes.S (d - 1) + m))))
      (q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
       q_pow B (2 * (Datatypes.S (d - 1) + m) + 1) / q_fact (2 * (Datatypes.S (d - 1) + m) + 1))).
    { intros m Hm. apply qeq_imp_qeqT.
      assert (Hodd : (Datatypes.S (2 * (Datatypes.S (d - 1) + m)) = 2 * (Datatypes.S (d - 1) + m) + 1)%nat) by lia.
      rewrite Hodd. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n - (d - 1))
      (fun m : nat => q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
                      q_pow B (Datatypes.S (2 * (Datatypes.S (d - 1) + m))) / q_fact (Datatypes.S (2 * (Datatypes.S (d - 1) + m))))
      (fun m : nat => q_pow B (2 * (Datatypes.S (d - 1) + m)) / q_fact (2 * (Datatypes.S (d - 1) + m)) +
                      q_pow B (2 * (Datatypes.S (d - 1) + m) + 1) / q_fact (2 * (Datatypes.S (d - 1) + m) + 1))
      HliftB)).
    assert (H1616dn : (d - 1 <= n)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_cs_evenodd_tail_diff B (d - 1) n H1616dn)).
    assert (Hidx : (2 * (d - 1) + 1 = 2 * d - 1)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_exp_series_idx (2 * (d - 1) + 1) (2 * d - 1) B Hidx)).
    apply Qle_refl.
Qed.

(* ---- band_c 界：|Σ_{j≤n} Σ_{k<j} c_j·c_{S(n−j)+k}| ≤ 2·F_c·T_c ---- *)
Lemma sc_cs_band_c_le : forall (t : Q) (n d : nat), (2 * d <= n)%nat ->
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto j (fun k : nat => cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t))))
      ((1 + 1) *
       (sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))) *
       (sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t)))).
Proof.
  intros t n d H2d.
  apply Qle_to_QleT'.
  assert (Hdn : (d <= n)%nat) by lia.
  set (F := sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))).
  set (T := sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))).
  set (G := fun j : nat => sum_upto j (fun k : nat => cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t)).
  (* 1. |Σ_j G j| ≤ Σ_j |G j| *)
  assert (Htri : Qle (Qabs (sum_upto (Datatypes.S n) G)) (sum_upto (Datatypes.S n) (fun j : nat => Qabs (G j)))).
  { unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le. }
  (* 2. 逐 j：|G j| ≤ |c_j|·W_j（W_j := Σ_{k<j}|c_{S(n−j)+k}|） *)
  assert (Hper : forall j : nat, (j <= n)%nat ->
    Qle (Qabs (G j))
        (Qabs (cos_term j t) *
         sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t)))).
  { intros j Hj.
    apply (Qle_trans _ (sum_upto j (fun k : nat => Qabs (cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t))) _).
    - unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      transitivity (sum_upto j (fun k : nat => Qabs (cos_term j t) * Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))).
      + apply qeqT_imp_qeq.
        apply (sum_upto_ext j
          (fun k : nat => Qabs (cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t))
          (fun k : nat => Qabs (cos_term j t) * Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))).
        intro k. apply qeq_imp_qeqT. apply Qabs_Qmult.
      + apply qeqT_imp_qeq.
        apply (sum_upto_scale j (Qabs (cos_term j t))
          (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))). }
  (* 3. W_j ≤ T（j ≤ d：内带指标 ⊆ [d+1, n]） *)
  assert (HwT : forall j : nat, (j <= d)%nat ->
    Qle (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))) T).
  { intros j Hjd.
    assert (Ha : forall k : nat, (Datatypes.S (n - j) + k = Datatypes.S d + ((n - j - d) + k))%nat) by (intro k; lia).
    assert (HliftC : forall k : nat, NatLe (Datatypes.S k) j -> QeqT
      (Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))
      (Qabs (cos_term (Datatypes.S d + ((n - j - d) + k))%nat t))).
    { intros k Hk. apply qeq_imp_qeqT. rewrite (Ha k). reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below j
      (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))
      (fun k : nat => Qabs (cos_term (Datatypes.S d + ((n - j - d) + k))%nat t))
      HliftC)).
    apply (Qle_trans _ (sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))) _).
    - apply QleT'_to_Qle. apply (sc_sum_shift_sub_le (n - j - d) j (n - d)
        (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))).
      + intro m. apply Qabs_nonneg.
      + lia.
    - apply Qle_refl. }
  (* 4. W_j ≤ F（j ≤ n：内带 ⊆ [0, n]） *)
  assert (HwF : forall j : nat, (j <= n)%nat ->
    Qle (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))) F).
  { intros j Hjn.
    apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))) _).
    - apply QleT'_to_Qle. apply (sc_sum_shift_sub_le (Datatypes.S (n - j)) j (Datatypes.S n)
        (fun i : nat => Qabs (cos_term i t))).
      + intro m. apply Qabs_nonneg.
      + lia.
    - apply Qle_refl. }
  (* 5. Σ_j |G j| ≤ T·(Σ_{j≤d}|c_j|) + F·T（after_split at d + 逐项） *)
  assert (Hsplit := sc_sum_after_split d n (fun j : nat => Qabs (G j)) Hdn).
  apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j : nat => Qabs (G j))) _).
  - exact Htri.
  - rewrite (qeqT_imp_qeq _ _ Hsplit).
    apply (Qle_trans _ (sum_upto (Datatypes.S d) (fun j : nat => Qabs (cos_term j t) * T) +
                        sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t) * F)) _).
    + apply Qplus_le_compat.
      * apply QleT'_to_Qle.
        apply (sum_upto_le_ext (Datatypes.S d)
          (fun j : nat => Qabs (G j))
          (fun j : nat => Qabs (cos_term j t) * T)).
        intros j Hj.
        pose proof (NatLe_drop (Datatypes.S j) (Datatypes.S d) Hj) as Hjdd.
        apply Qle_to_QleT'.
        apply (Qle_trans _ (Qabs (cos_term j t) *
                sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))) _).
        2: { apply (Qle_trans _ (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t)) * Qabs (cos_term j t)) _).
             2: { apply (Qle_trans _ (T * Qabs (cos_term j t)) _).
                  2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                       exact (Qeq_sym _ _ (Qmult_comm (Qabs (cos_term j t)) T)). }
                  apply (Qmult_le_compat_r (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))) T (Qabs (cos_term j t))).
                  - apply (HwT j). lia.
                  - apply Qabs_nonneg. }
             apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
             exact (Qmult_comm (Qabs (cos_term j t))
                (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t)))). }
        apply (Hper j). lia.
      * apply QleT'_to_Qle.
        apply (sum_upto_le_ext (n - d)
          (fun m : nat => Qabs (G ((Datatypes.S d + m)%nat)))
          (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t) * F)).
        intros m Hm.
        apply Qle_to_QleT'.
        set (j := (Datatypes.S d + m)%nat).
        pose proof (NatLe_drop (Datatypes.S m) (n - d) Hm) as Hmd.
        assert (Hjn : (j <= n)%nat) by (unfold j; lia).
        apply (Qle_trans _ (Qabs (cos_term j t) *
                sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))) _).
        2: { apply (Qle_trans _ (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t)) *
                              Qabs (cos_term j t)) _).
             2: { apply (Qle_trans _ (F * Qabs (cos_term j t)) _).
                  2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                       exact (Qeq_sym _ _ (Qmult_comm (Qabs (cos_term j t)) F)). }
                  apply (Qmult_le_compat_r (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t))) F (Qabs (cos_term j t))).
                  - apply (HwF j). exact Hjn.
                  - apply Qabs_nonneg. }
             apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
             exact (Qmult_comm (Qabs (cos_term j t))
                (sum_upto j (fun k : nat => Qabs (cos_term (Datatypes.S (n - j) + k)%nat t)))). }
        apply (Hper j). exact Hjn.
    + apply (Qle_trans _ (T * F + F * T) _).
      2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      1: { apply Qplus_le_compat.
           2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                transitivity (sum_upto (n - d) (fun m : nat => F * Qabs (cos_term (Datatypes.S d + m)%nat t))).
                2: { apply qeqT_imp_qeq.
                     apply (sum_upto_scale (n - d) F (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))). }
                1: { apply qeqT_imp_qeq.
                     apply (sum_upto_ext (n - d)
                      (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t) * F)
                      (fun m : nat => F * Qabs (cos_term (Datatypes.S d + m)%nat t))).
                     intro j.
                     apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (cos_term (Datatypes.S d + j)%nat t)) F). } }
           1: { apply (Qle_trans _ (T * sum_upto (Datatypes.S d) (fun j : nat => Qabs (cos_term j t))) _).
                2: { apply (Qle_trans _ (F * T) _).
                     2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm F T). }
                     1: { apply (Qle_trans _ (sum_upto (Datatypes.S d) (fun j : nat => Qabs (cos_term j t)) * T) _).
                          2: { apply (Qmult_le_compat_r (sum_upto (Datatypes.S d) (fun j : nat => Qabs (cos_term j t))) F T).
                               2: { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
                               1: { apply QleT'_to_Qle. apply (sc_sum_shift_sub_le 0 (Datatypes.S d) (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))).
                                    2: { lia. }
                                    1: { intro m. apply Qabs_nonneg. } } }
                          1: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                               exact (Qmult_comm T (sum_upto (Datatypes.S d) (fun j : nat => Qabs (cos_term j t)))). } } }
                1: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                     transitivity (sum_upto (Datatypes.S d) (fun j : nat => T * Qabs (cos_term j t))).
                     2: { apply qeqT_imp_qeq.
                          apply (sum_upto_scale (Datatypes.S d) T (fun j : nat => Qabs (cos_term j t))). }
                     1: { apply qeqT_imp_qeq.
                          apply (sum_upto_ext (Datatypes.S d)
                           (fun j : nat => Qabs (cos_term j t) * T)
                           (fun j : nat => T * Qabs (cos_term j t))).
                          intro j.
                          apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (cos_term j t)) T). } } } }
Qed.

(* ---- band_d 界：|Σ_{j≤n} Σ_{k≤j} d_j·d_{n−j+k}| ≤ 2·F_d·T_d ---- *)
Lemma sc_cs_band_d_le : forall (t : Q) (n d : nat), (2 * d <= n)%nat ->
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t))))
      ((1 + 1) *
       (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))) *
       (sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t)))).
Proof.
  intros t n d H2d.
  apply Qle_to_QleT'.
  assert (Hdn : (d <= n)%nat) by lia.
  set (F := sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))).
  set (T := sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t))).
  set (G := fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t)).
  assert (Htri : Qle (Qabs (sum_upto (Datatypes.S n) G)) (sum_upto (Datatypes.S n) (fun j : nat => Qabs (G j)))).
  { unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le. }
  assert (Hper : forall j : nat, (j <= n)%nat ->
    Qle (Qabs (G j))
        (Qabs (sin_term j t) *
         sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t)))).
  { intros j Hj.
    apply (Qle_trans _ (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term j t * sin_term (n - j + k)%nat t))) _).
    - unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      transitivity (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term j t) * Qabs (sin_term (n - j + k)%nat t))).
      + apply qeqT_imp_qeq.
        apply (sum_upto_ext (Datatypes.S j)
          (fun k : nat => Qabs (sin_term j t * sin_term (n - j + k)%nat t))
          (fun k : nat => Qabs (sin_term j t) * Qabs (sin_term (n - j + k)%nat t))).
        intro k. apply qeq_imp_qeqT. apply Qabs_Qmult.
      + apply qeqT_imp_qeq.
        apply (sum_upto_scale (Datatypes.S j) (Qabs (sin_term j t))
          (fun k : nat => Qabs (sin_term (n - j + k)%nat t))). }
  assert (HwT : forall j : nat, (j <= d)%nat ->
    Qle (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t))) T).
  { intros j Hjd.
    assert (Ha : forall k : nat, (n - j + k = d + ((n - j - d) + k))%nat) by (intro k; lia).
    assert (HliftD : forall k : nat, NatLe (Datatypes.S k) (Datatypes.S j) -> QeqT
      (Qabs (sin_term (n - j + k)%nat t))
      (Qabs (sin_term (d + ((n - j - d) + k))%nat t))).
    { intros k Hk. apply qeq_imp_qeqT. rewrite (Ha k). reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (Datatypes.S j)
      (fun k : nat => Qabs (sin_term (n - j + k)%nat t))
      (fun k : nat => Qabs (sin_term (d + ((n - j - d) + k))%nat t))
      HliftD)).
    apply (Qle_trans _ (sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t))) _).
    - apply QleT'_to_Qle. apply (sc_sum_shift_sub_le (n - j - d) (Datatypes.S j) (Datatypes.S (n - d))
        (fun m : nat => Qabs (sin_term (d + m)%nat t))).
      + intro m. apply Qabs_nonneg.
      + lia.
    - apply Qle_refl. }
  assert (HwF : forall j : nat, (j <= n)%nat ->
    Qle (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t))) F).
  { intros j Hjn.
    apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))) _).
    - apply QleT'_to_Qle. apply (sc_sum_shift_sub_le (n - j) (Datatypes.S j) (Datatypes.S n)
        (fun i : nat => Qabs (sin_term i t))).
      + intro m. apply Qabs_nonneg.
      + lia.
    - apply Qle_refl. }
  assert (HperT : forall j : nat, (j <= d)%nat -> Qle (Qabs (G j)) (Qabs (sin_term j t) * T)).
  { intros j Hjd.
    apply (Qle_trans _ (Qabs (sin_term j t) *
            sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t))) _).
    - apply (Hper j). lia.
    - apply (Qle_trans _ (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t)) * Qabs (sin_term j t)) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        exact (Qmult_comm (Qabs (sin_term j t))
          (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t)))).
      + apply (Qle_trans _ (T * Qabs (sin_term j t)) _).
        * apply (Qmult_le_compat_r (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t))) T (Qabs (sin_term j t))).
          -- apply (HwT j). exact Hjd.
          -- apply Qabs_nonneg.
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          exact (Qeq_sym _ _ (Qmult_comm (Qabs (sin_term j t)) T)). }
  assert (HperF : forall j : nat, (j <= n)%nat -> Qle (Qabs (G j)) (Qabs (sin_term j t) * F)).
  { intros j Hjn.
    apply (Qle_trans _ (Qabs (sin_term j t) *
            sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t))) _).
    - apply (Hper j). exact Hjn.
    - apply (Qle_trans _ (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t)) * Qabs (sin_term j t)) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        exact (Qmult_comm (Qabs (sin_term j t))
          (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t)))).
      + apply (Qle_trans _ (F * Qabs (sin_term j t)) _).
        * apply (Qmult_le_compat_r (sum_upto (Datatypes.S j) (fun k : nat => Qabs (sin_term (n - j + k)%nat t))) F (Qabs (sin_term j t))).
          -- apply (HwF j). exact Hjn.
          -- apply Qabs_nonneg.
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          exact (Qeq_sym _ _ (Qmult_comm (Qabs (sin_term j t)) F)). }
  assert (Hsplit := sc_sum_after_split d n (fun j : nat => Qabs (G j)) Hdn).
  assert (H1 : Qle (sum_upto (Datatypes.S d) (fun j : nat => Qabs (G j)))
                 (sum_upto (Datatypes.S d) (fun j : nat => Qabs (sin_term j t) * T))).
  { apply QleT'_to_Qle.
    apply (sum_upto_le_ext (Datatypes.S d)
      (fun j : nat => Qabs (G j))
      (fun j : nat => Qabs (sin_term j t) * T)).
    intros j Hj. pose proof (NatLe_drop (Datatypes.S j) (Datatypes.S d) Hj) as Hjdd.
    apply Qle_to_QleT'. apply (HperT j). lia. }
  assert (H2 : Qle (sum_upto (n - d) (fun m : nat => Qabs (G ((Datatypes.S d + m)%nat))))
                   (sum_upto (n - d) (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t) * F))).
  { apply QleT'_to_Qle.
    apply (sum_upto_le_ext (n - d)
      (fun m : nat => Qabs (G ((Datatypes.S d + m)%nat)))
      (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t) * F)).
    intros m Hm.
    pose proof (NatLe_drop (Datatypes.S m) (n - d) Hm) as Hmd.
    apply Qle_to_QleT'.
    apply (HperF ((Datatypes.S d + m)%nat)). lia. }
  apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j : nat => Qabs (G j))) _).
  - exact Htri.
  - rewrite (qeqT_imp_qeq _ _ Hsplit).
    apply (Qle_trans _ (sum_upto (Datatypes.S d) (fun j : nat => Qabs (sin_term j t) * T) +
                        sum_upto (n - d) (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t) * F)) _).
    + apply Qplus_le_compat; assumption.
    + apply (Qle_trans _ (T * F + F * T) _).
      * apply Qplus_le_compat.
        2: { apply (Qle_trans _ (F * sum_upto (n - d) (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t))) _).
             2: { apply (Qle_trans _ (sum_upto (n - d) (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t)) * F) _).
                  2: { apply (Qle_trans _ (T * F) _).
                       2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm T F). }
                       1: { apply (Qmult_le_compat_r (sum_upto (n - d) (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t))) T F).
                            2: { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
                            1: { apply (Qle_trans _ (sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t))) _).
                                 2: { apply Qle_refl. }
                                 1: { assert (HliftE : forall m0 : nat, NatLe (Datatypes.S m0) (n - d) -> QeqT
                                       (Qabs (sin_term (Datatypes.S d + m0)%nat t))
                                       (Qabs (sin_term (d + (1 + m0))%nat t))).
                                      { intros m0 Hm0. apply qeq_imp_qeqT.
                                        assert (Hio : (Datatypes.S d + m0 = d + (1 + m0))%nat) by lia.
                                        rewrite Hio. reflexivity. }
                                      rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n - d)
                                       (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t))
                                       (fun m : nat => Qabs (sin_term (d + (1 + m))%nat t))
                                       HliftE)).
                                      apply QleT'_to_Qle. apply (sc_sum_shift_sub_le 1 (n - d) (Datatypes.S (n - d))
                                           (fun m : nat => Qabs (sin_term (d + m)%nat t))).
                                      2: { lia. }
                                      1: { intro m. apply Qabs_nonneg. } } } } }
                  1: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                       exact (Qmult_comm F (sum_upto (n - d) (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t)))). } }
             1: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                  transitivity (sum_upto (n - d) (fun m : nat => F * Qabs (sin_term (Datatypes.S d + m)%nat t))).
                  2: { apply qeqT_imp_qeq.
                       apply (sum_upto_scale (n - d) F (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t))). }
                  1: { apply qeqT_imp_qeq.
                       apply (sum_upto_ext (n - d)
                        (fun m : nat => Qabs (sin_term (Datatypes.S d + m)%nat t) * F)
                        (fun m : nat => F * Qabs (sin_term (Datatypes.S d + m)%nat t))).
                       intro j.
                       apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (sin_term (Datatypes.S d + j)%nat t)) F). } } }
        1: { apply (Qle_trans _ (T * sum_upto (Datatypes.S d) (fun j : nat => Qabs (sin_term j t))) _).
             2: { apply (Qle_trans _ (F * T) _).
                  2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm F T). }
                  1: { apply (Qle_trans _ (sum_upto (Datatypes.S d) (fun j : nat => Qabs (sin_term j t)) * T) _).
                       2: { apply (Qmult_le_compat_r (sum_upto (Datatypes.S d) (fun j : nat => Qabs (sin_term j t))) F T).
                            2: { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
                            1: { apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))) _).
                                 2: { apply Qle_refl. }
                                 1: { apply QleT'_to_Qle. apply (sc_sum_shift_sub_le 0 (Datatypes.S d) (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))).
                                      2: { lia. }
                                      1: { intro m. apply Qabs_nonneg. } } } }
                       1: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                            exact (Qmult_comm T (sum_upto (Datatypes.S d) (fun j : nat => Qabs (sin_term j t)))). } } }
             1: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                  transitivity (sum_upto (Datatypes.S d) (fun j : nat => T * Qabs (sin_term j t))).
                  2: { apply qeqT_imp_qeq.
                       apply (sum_upto_scale (Datatypes.S d) T (fun j : nat => Qabs (sin_term j t))). }
                  1: { apply qeqT_imp_qeq.
                       apply (sum_upto_ext (Datatypes.S d)
                        (fun j : nat => Qabs (sin_term j t) * T)
                        (fun j : nat => T * Qabs (sin_term j t))).
                       intro j.
                       apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (sin_term j t)) T). } } }      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ---- Qeq→Qabs 桥：x == y 时 |x| ≤ B ⟸ |y| ≤ B ---- *)
Lemma sc_qabs_qeq_le : forall (x y B : Q),
  x == y -> Qle (Qabs y) B -> QleT' (Qabs x) B.
Proof.
  intros x y B Heq Hy.
  apply Qle_to_QleT'.
  assert (Hy' : Qle (- B) y /\ Qle y B).
  { apply (proj1 (Qabs_Qle_condition y B)). exact Hy. }
  destruct Hy' as [Hy1 Hy2].
  apply Qabs_Qle_condition.
  split.
  - apply (Qle_trans _ y _).
    + exact Hy1.
    + apply (QleT'_to_Qle _ _ (qeq_le y x (qeq_imp_qeqT _ _ (Qeq_sym _ _ Heq)))).
  - apply (Qle_trans _ y _).
    + apply (QleT'_to_Qle _ _ (qeq_le x y (qeq_imp_qeqT _ _ Heq))).
    + exact Hy2.
Qed.

(* ---- |E| 带界：|c_n²+s_n²−1| ≤ 2F_cT_c + 2F_dT_d（经 decomp + 三角 + 带界） ---- *)
Lemma sc_cs_sq_err_le : forall (t : Q) (n d : nat), (2 * d <= n)%nat ->
  QleT' (Qabs (cos_partial n t * cos_partial n t + sin_partial n t * sin_partial n t - 1))
      ((1 + 1) *
       (sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))) *
       (sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))) +
       (1 + 1) *
       (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))) *
       (sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t)))).
Proof.
  intros t n d H2d.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (sc_qabs_qeq_le
    (cos_partial n t * cos_partial n t + sin_partial n t * sin_partial n t - 1)
    (sum_upto (Datatypes.S n) (fun j : nat => sum_upto j (fun k : nat => cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t)) +
     sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t)))
    ((1 + 1) *
     (sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))) *
     (sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))) +
     (1 + 1) *
     (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))) *
     (sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t))))).
  - exact (qeqT_imp_qeq _ _ (sc_cs_sq_err_decomp t n)).
  - apply (Qle_trans _ (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto j (fun k : nat => cos_term j t * cos_term (Datatypes.S (n - j) + k)%nat t))) +
                         Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (Datatypes.S j) (fun k : nat => sin_term j t * sin_term (n - j + k)%nat t)))) _).
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * exact (QleT'_to_Qle _ _ (sc_cs_band_c_le t n d H2d)).
      * exact (QleT'_to_Qle _ _ (sc_cs_band_d_le t n d H2d)).
Qed.

(* ---- L1：|E| ≤ 4·exp_series(2n+1)·exp_tail_abs(2d−1)(2n+1)（d := div2 n 用；1≤d、2d≤n） ---- *)
Lemma sc_cs_sq_err_tail_le : forall (t B : Q) (d n : nat),
  Qle 0 B -> Qle (Qabs t) B -> (1 <= d)%nat -> (2 * d <= n)%nat ->
  QleT' (Qabs (cos_partial n t * cos_partial n t + sin_partial n t * sin_partial n t - 1))
      (((1 + 1) * (1 + 1)) *
       (exp_series (2 * n + 1)%nat B * exp_tail_abs (2 * d - 1)%nat (2 * n + 1)%nat B)).
Proof.
  intros t B d n HB HtB Hd1 H2d.
  apply Qle_to_QleT'.
  assert (Hdn : (d <= n)%nat) by lia.
  set (Fc := sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i t))).
  set (Tc := sum_upto (n - d) (fun m : nat => Qabs (cos_term (Datatypes.S d + m)%nat t))).
  set (Fd := sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i t))).
  set (Td := sum_upto (Datatypes.S (n - d)) (fun m : nat => Qabs (sin_term (d + m)%nat t))).
  set (Bc := (1 + 1) * Fc * Tc).
  set (Bd := (1 + 1) * Fd * Td).
  set (En := exp_series (2 * n + 1)%nat B).
  set (Dc := exp_series (2 * n + 1)%nat B - exp_series (2 * d + 1)%nat B).
  set (Dd := exp_series (2 * n + 1)%nat B - exp_series (2 * d - 1)%nat B).
  set (G := exp_tail_abs (2 * d - 1)%nat (2 * n + 1)%nat B).
  assert (H0 : Qle (Qabs (cos_partial n t * cos_partial n t + sin_partial n t * sin_partial n t - 1)) (Bc + Bd)).
  { unfold Bc, Bd, Fc, Tc, Fd, Td. exact (QleT'_to_Qle _ _ (sc_cs_sq_err_le t n d H2d)). }
  assert (HcF : Qle Fc En). { unfold Fc, En. apply QleT'_to_Qle. apply (sc_cs_c_full_le t B n HB HtB). }
  assert (HdF : Qle Fd En). { unfold Fd, En. apply QleT'_to_Qle. apply (sc_cs_d_full_le t B n HB HtB). }
  assert (HcT : Qle Tc Dc). { unfold Tc, Dc. apply QleT'_to_Qle. apply (sc_cs_c_tail_diff_le t B d n HB HtB Hdn). }
  assert (HdT : Qle Td Dd). { unfold Td, Dd. apply QleT'_to_Qle. apply (sc_cs_d_tail_diff_le t B d n HB HtB Hd1 Hdn). }
  assert (Hdc : Qle Dc Dd).
  { apply (proj2 (Qle_minus_iff Dc Dd)).
    apply (Qle_trans _ (exp_series (2 * d + 1)%nat B - exp_series (2 * d - 1)%nat B) _).
    - apply (proj1 (Qle_minus_iff (exp_series (2 * d - 1)%nat B) (exp_series (2 * d + 1)%nat B))).
      apply QleT'_to_Qle. apply exp_series_mono; [exact (Qle_to_QleT' _ _ HB) | lia].
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Dd, Dc, Qdiv. ring. }
  assert (HG : Qle Dd G).
  { unfold Dd, G. apply QleT'_to_Qle. apply (exp_series_tail_le B (2 * d - 1)%nat (2 * n + 1)%nat (Qle_to_QleT' _ _ HB)). lia. }
  assert (Htwo0 : Qle 0 (1 + 1)) by (apply QleT'_to_Qle; apply Q2_nonneg).
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1))) by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  assert (HEn0 : Qle 0 En) by (unfold En; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HTwoEn0 : Qle 0 ((1 + 1) * En)) by (apply Qmult_le_0_compat; [exact Htwo0 | exact HEn0]).
  assert (HTc0 : Qle 0 Tc) by (unfold Tc; (apply QleT'_to_Qle; apply sc_sum_nonneg); intro m; apply Qabs_nonneg).
  assert (HTd0 : Qle 0 Td) by (unfold Td; (apply QleT'_to_Qle; apply sc_sum_nonneg); intro m; apply Qabs_nonneg).
  assert (H1c : Qle Bc (((1 + 1) * En) * Dc)).
  { unfold Bc.
    apply (Qle_trans _ (((1 + 1) * En) * Tc) _).
    - apply (Qmult_le_compat_r ((1 + 1) * Fc) ((1 + 1) * En) Tc).
      + apply (Qle_trans _ (Fc * (1 + 1)) _).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm (1 + 1) Fc).
        * apply (Qle_trans _ (En * (1 + 1)) _).
          -- apply (Qmult_le_compat_r Fc En (1 + 1)); [exact HcF | exact Htwo0].
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + exact HTc0.
    - apply (Qle_trans _ (Tc * ((1 + 1) * En)) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply (Qle_trans _ (Dc * ((1 + 1) * En)) _).
        * apply (Qmult_le_compat_r Tc Dc ((1 + 1) * En)); [exact HcT | exact HTwoEn0].
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (H1d : Qle Bd (((1 + 1) * En) * Dd)).
  { unfold Bd.
    apply (Qle_trans _ (((1 + 1) * En) * Td) _).
    - apply (Qmult_le_compat_r ((1 + 1) * Fd) ((1 + 1) * En) Td).
      + apply (Qle_trans _ (Fd * (1 + 1)) _).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm (1 + 1) Fd).
        * apply (Qle_trans _ (En * (1 + 1)) _).
          -- apply (Qmult_le_compat_r Fd En (1 + 1)); [exact HdF | exact Htwo0].
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + exact HTd0.
    - apply (Qle_trans _ (Td * ((1 + 1) * En)) _).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply (Qle_trans _ (Dd * ((1 + 1) * En)) _).
        * apply (Qmult_le_compat_r Td Dd ((1 + 1) * En)); [exact HdT | exact HTwoEn0].
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (H3 : Qle (((1 + 1) * En) * Dc) (((1 + 1) * En) * Dd)).
  { apply (Qle_trans _ (Dc * ((1 + 1) * En)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ (Dd * ((1 + 1) * En)) _).
      + apply (Qmult_le_compat_r Dc Dd ((1 + 1) * En)); [exact Hdc | exact HTwoEn0].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (HED : Qle (En * Dd) (En * G)).
  { apply (Qle_trans _ (Dd * En) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ (G * En) _).
      + apply (Qmult_le_compat_r Dd G En); [exact HG | exact HEn0].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  apply (Qle_trans _ (Bc + Bd) _).
  - exact H0.
  - apply (Qle_trans _ (((1 + 1) * En) * Dc + ((1 + 1) * En) * Dd) _).
    + apply Qplus_le_compat; [exact H1c | exact H1d].
    + apply (Qle_trans _ (((1 + 1) * En) * Dd + ((1 + 1) * En) * Dd) _).
      * apply Qplus_le_compat; [exact H3 | apply Qle_refl].
      * apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (En * Dd)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ ((En * Dd) * ((1 + 1) * (1 + 1))) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ apply (Qle_trans _ ((En * G) * ((1 + 1) * (1 + 1))) _).
              ** apply (Qmult_le_compat_r (En * Dd) (En * G) ((1 + 1) * (1 + 1))); [exact HED | exact Hfour0].
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.
(* ---- 辅助：div2 基本界（lt_wf_ind；div2 0=0、div2 1=0、div2 (S(S m)) = S(div2 m)） ---- *)
Lemma sc_div2_le : forall n : nat, NatLe (2 * Nat.div2 n) n.
Proof.
  induction n as [n IH] using lt_wf_rec.
  destruct n as [| [| m]].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. assert (H : NatLe (2 * Nat.div2 m) m) by (apply IH; lia).
    apply NatLe_lift. apply NatLe_drop in H. simpl. lia.
Qed.

Lemma sc_div2_ge : forall (M n : nat), (2 * M <= n)%nat -> NatLe M (Nat.div2 n).
Proof.
  intros M n. revert M.
  induction n as [n IH] using lt_wf_rec.
  intros M HMn. destruct n as [| [| m]].
  - simpl. destruct M as [| M'].
    + apply id_refl.
    + simpl in HMn. exfalso. lia.
  - simpl. destruct M as [| M'].
    + apply id_refl.
    + simpl in HMn. exfalso. lia.
  - simpl. destruct M as [| M'].
    + apply id_refl.
    + simpl in HMn.
      assert (Hd : NatLe M' (Nat.div2 m)) by (apply (IH m); lia).
      apply NatLe_lift. apply NatLe_drop in Hd. simpl. lia.
Qed.

(* ---- 辅助：左乘单调（Qmult_le_compat_r 只给右乘；此经 comm 双跳） ---- *)
Lemma sc_qmult_le_l : forall (a b c : Q), Qle a b -> Qle 0 c -> QleT' (c * a) (c * b).
Proof.
intros a b c Hab Hc0. apply Qle_to_QleT'. exact (Qle_trans (c * a) (a * c) (c * b) (QleT'_to_Qle _ _ (qeq_le (c * a) (a * c) (qeq_imp_qeqT _ _ (Qmult_comm c a)))) (Qle_trans (a * c) (b * c) (c * b) (Qmult_le_compat_r a b c Hab Hc0) (QleT'_to_Qle _ _ (qeq_le (b * c) (c * b) (qeq_imp_qeqT _ _ (Qmult_comm b c)))))).
Qed.

(* ---- 模量：∀eps ∃N，n ≥ N、|t| ≤ B ⟹ |c_n²+s_n²−1| < eps ---- *)
Lemma sc_cs_sq_err_bound : forall (B : Q) (eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall (t : Q) (n : nat), NatLe N n -> QleT' (Qabs t) B ->
    QltT (Qabs (cos_partial n t * cos_partial n t + sin_partial n t * sin_partial n t - 1)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  destruct (exp_series_arch B HB) as [C [HC1 HC]].
  assert (HC0 : Qle 0 C) by (apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1)) by (apply QleT'_to_Qle; apply Q2_nonneg).
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1))) by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  set (P := ((1 + 1) * (1 + 1)) * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply Qmult_le_0_compat.
    - exact Hfour0.
    - apply (Qmult_le_0_compat C ((q_pow B N0 / q_fact N0) * (1 + 1))).
      + exact HC0.
      + apply QleT'_to_Qle. apply q_pow_fact2_nonneg. exact HB. }
  destruct (arch_decay P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists (2 * (N0 + Datatypes.S t + 1))%nat.
  intros t0 n HNn HtB0.
  set (d := Nat.div2 n).
  assert (Hd : (N0 + Datatypes.S t + 1 <= d)%nat).
  { unfold d. apply NatLe_drop. apply sc_div2_ge. exact (NatLe_drop _ _ HNn). }
  assert (Hd1 : (1 <= d)%nat) by lia.
  assert (H2d : (2 * d <= n)%nat).
  { unfold d. exact (NatLe_drop _ _ (sc_div2_le n)). }
  set (X := q_pow B (2 * d - 1) / q_fact (2 * d - 1)).
  set (G := exp_tail_abs (2 * d - 1)%nat (2 * n + 1)%nat B).
  assert (Hj : (Datatypes.S t <= 2 * d - 1 - N0)%nat) by lia.
  assert (HG2 : Qle G (X * (1 + 1))).
  { unfold G, X.
    apply QleT'_to_Qle. apply (exp_tail_abs_geom2 B (2 * d - 1)%nat (2 * n + 1)%nat HB).
    - intros u Hu. apply (HN0 u). apply NatLe_lift. pose proof (NatLe_drop _ _ Hu). lia.
    - lia. }
  assert (HXY : Qle X ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * d - 1 - N0))).
  { unfold X. apply QleT'_to_Qle. apply (pow_fact_decay B N0 (2 * d - 1)%nat HB (fun u Hu => HN0 u Hu)). lia. }
  assert (HEnC : Qle (exp_series (2 * n + 1)%nat B) C) by (apply QleT'_to_Qle; exact (HC (2 * n + 1)%nat)).
  assert (HG0 : Qle 0 G) by (unfold G; apply QleT'_to_Qle; apply exp_tail_abs_nonneg; exact HB).
  assert (HL1 := sc_cs_sq_err_tail_le t0 B d n (QleT'_to_Qle _ _ HB) (QleT'_to_Qle _ _ HtB0) Hd1 H2d).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (P * q_pow (1 / 2)%Q (Datatypes.S t)) _).
  - apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (exp_series (2 * n + 1)%nat B * G)) _).
    + apply QleT'_to_Qle. exact HL1.
    + apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (C * G)) _).
      * apply QleT'_to_Qle. apply (sc_qmult_le_l (exp_series (2 * n + 1)%nat B * G) (C * G) ((1 + 1) * (1 + 1))).
        -- apply (Qmult_le_compat_r (exp_series (2 * n + 1)%nat B) C G); [exact HEnC | exact HG0].
        -- exact Hfour0.
      * apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (C * (X * (1 + 1)))) _).
        -- apply QleT'_to_Qle. apply (sc_qmult_le_l (C * G) (C * (X * (1 + 1))) ((1 + 1) * (1 + 1))).
           ++ apply QleT'_to_Qle. apply (sc_qmult_le_l G (X * (1 + 1)) C); [exact HG2 | exact HC0].
           ++ exact Hfour0.
        -- apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (C * (((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * d - 1 - N0)) * (1 + 1)))) _).
           ++ apply QleT'_to_Qle. apply (sc_qmult_le_l (C * (X * (1 + 1)))
                                   (C * (((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * d - 1 - N0)) * (1 + 1)))
                                   ((1 + 1) * (1 + 1))).
              ** apply QleT'_to_Qle. apply (sc_qmult_le_l (X * (1 + 1))
                                      (((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * d - 1 - N0)) * (1 + 1))
                                      C).
                 --- apply (Qmult_le_compat_r X ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * d - 1 - N0)) (1 + 1));
                     [exact HXY | exact Htwo0].
                 --- exact HC0.
              ** exact Hfour0.
           ++ apply (Qle_trans _ (P * q_pow (1 / 2)%Q (2 * d - 1 - N0)) _).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold P. ring.
              ** apply QleT'_to_Qle. apply (sc_qmult_le_l (q_pow (1 / 2)%Q (2 * d - 1 - N0)) (q_pow (1 / 2)%Q (Datatypes.S t)) P).
                 --- apply QleT'_to_Qle. apply (q_half_pow_mono (2 * d - 1 - N0) (Datatypes.S t)). exact Hj.
                 --- exact HP0.
  - exact (QltT_to_Qlt _ _ Ht).
Qed.

(* ---- 恒等式：cos X·cos X + sin X·sin X == real_one ---- *)
Lemma real_cos_sq_plus_sin_sq_one : forall X : Real,
  real_eq (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                     (real_mult (cauchy_real_sin X) (cauchy_real_sin X)))
          real_one.
Proof.
  intro X.
  unfold real_eq.
  intros eps Heps.
  destruct (real_norm_bounded X) as [M [HMpos HM]].
  destruct (sc_cs_sq_err_bound M eps (qltT_leT' 0 M HMpos) Heps) as [N HN].
  exists N.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (cos_partial n (projT1 X n) * cos_partial n (projT1 X n) +
                              sin_partial n (projT1 X n) * sin_partial n (projT1 X n) - 1)) _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                                      (real_mult (cauchy_real_sin X) (cauchy_real_sin X))) n - projT1 real_one n)
                   (cos_partial n (projT1 X n) * cos_partial n (projT1 X n) +
                    sin_partial n (projT1 X n) * sin_partial n (projT1 X n) - 1)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_cos_proj _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_sin_proj _ _)).
    reflexivity.
  - apply QltT_to_Qlt.
    exact (HN (projT1 X n) n Hn (HM n)).
Qed.

(* ---- 桥：x < 2 ⟹ 2x < 4 ---- *)
Lemma sc_two_x_lt_four : forall x : Q, Qlt x 2 -> QltT (Qmult (1 + 1) x) ((1 + 1) * (1 + 1)).
Proof.
  intros x Hx2.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (x * (1 + 1)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qmult_lt_compat_r x 2 (1 + 1)).
    + change (Qlt 0 (1 + 1)). compute. reflexivity.
    + exact Hx2.
Qed.

(* ---- sin 侧 hlt 的 x<2 版：x < 2、j ≥ 1 ⟹ 2x < 2j+2 ---- *)
Lemma sc_sin_alt_hlt2 : forall (x : Q) (j : nat), Qlt x 2 -> (1 <= j)%nat ->
  QltT (Qmult (1 + 1) x) (Qmake (Z.of_nat (2 * j + 2)) 1).
Proof.
  intros x j Hx2 Hj.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ ((1 + 1) * (1 + 1)) _).
  - apply QltT_to_Qlt. apply sc_two_x_lt_four. exact Hx2.
  - unfold Qle. simpl. lia.
Qed.

(* ---- 子列单调（x<2 版）：sin 偶 ↓ ---- *)
Lemma sc_sin_even_decr2 : forall (m : nat) (x : Q),
  Qle 0 x -> Qlt x 2 ->
  QleT' (sin_partial (2 * Datatypes.S m) x) (sin_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx2.
  apply Qle_to_QleT'.
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_step2 (2 * m) x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg m x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_even_pos m x)).
  apply (proj2 (Qle_minus_iff (sin_partial (2 * m) x + (- sc_sin_alt (Datatypes.S (2 * m)) x) + sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x)
                              (sin_partial (2 * m) x))).
  assert (Heq : sin_partial (2 * m) x - (sin_partial (2 * m) x + (- sc_sin_alt (Datatypes.S (2 * m)) x) + sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x) ==
                sc_sin_alt (Datatypes.S (2 * m)) x - sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x) by ring.
  rewrite Heq.
  apply (proj1 (Qle_minus_iff (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x)
                              (sc_sin_alt (Datatypes.S (2 * m)) x))).
  apply QleT'_to_Qle. apply (sc_sin_alt_decr x (Datatypes.S (2 * m)) Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_sin_alt_hlt2 x (Datatypes.S (2 * m)) Hx2). lia.
Qed.

(* ---- 子列单调（x<2 版）：sin 奇 ↑ ---- *)
Lemma sc_sin_odd_incr2 : forall (m : nat) (x : Q),
  Qle 0 x -> Qlt x 2 ->
  QleT' (sin_partial (Datatypes.S (2 * m)) x) (sin_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x).
Proof.
  intros m x Hx0 Hx2.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_step2 (Datatypes.S (2 * m)) x)).
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_even_pos m x)).
  replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat with (Datatypes.S (2 * Datatypes.S m))%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_term_odd_neg (Datatypes.S m) x)).
  assert (Heq : sin_partial (Datatypes.S (2 * m)) x + sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x +
                (- sc_sin_alt (Datatypes.S (2 * Datatypes.S m)) x) ==
                sin_partial (Datatypes.S (2 * m)) x +
                (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x - sc_sin_alt (Datatypes.S (2 * Datatypes.S m)) x)) by ring.
  rewrite Heq.
  apply Qle_plus_nonneg_r.
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
  apply (proj1 (Qle_minus_iff (sc_sin_alt (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x)
                              (sc_sin_alt (Datatypes.S (Datatypes.S (2 * m))) x))).
  apply QleT'_to_Qle. apply (sc_sin_alt_decr x (Datatypes.S (Datatypes.S (2 * m))) Hx0).
  - lia.
  - apply QltT_to_Qlt. apply (sc_sin_alt_hlt2 x (Datatypes.S (Datatypes.S (2 * m))) Hx2). lia.
Qed.

(* ---- 奇子列 ≥ x − c1（x<2 版） ---- *)
Lemma sc_sin_odd_ge_c1_2 : forall (m : nat) (x : Q),
  Qle 0 x -> Qlt x 2 -> QleT' (x - sc_sin_alt 1 x) (sin_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hx0 Hx2.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (Datatypes.S (2 * 0)) with 1%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_1_x x)).
    apply Qle_refl.
  - apply Qle_to_QleT'. replace (Datatypes.S (2 * Datatypes.S m'))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))%nat by lia.
    apply (Qle_trans _ (sin_partial (Datatypes.S (2 * m')) x) _).
    + exact (QleT'_to_Qle _ _ IH).
    + apply QleT'_to_Qle. apply sc_sin_odd_incr2. exact Hx0. exact Hx2.
Qed.

(* ---- sin：x − x³/6 ≤ sin_partial n x（x<2 版） ---- *)
Lemma sc_sin_partial_lower_c1_2 : forall (n : nat) (x : Q),
  Qle 0 x -> Qlt x 2 -> QleT' (x - sc_sin_alt 1 x) (sin_partial n x).
Proof.
  intros n x Hx0 Hx2.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - apply Qle_to_QleT'. destruct m as [| m'].
    + rewrite Hm.
      replace (2 * 0)%nat with 0%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_0_x x)).
      apply (proj2 (Qle_minus_iff (x - sc_sin_alt 1 x) x)).
      assert (Heq : x - (x - sc_sin_alt 1 x) == sc_sin_alt 1 x) by ring.
      rewrite Heq.
      apply QleT'_to_Qle. apply sc_sin_alt_nonneg. exact Hx0.
    + apply (Qle_trans _ (sin_partial (Datatypes.S (2 * m')) x) _).
      * apply QleT'_to_Qle. apply sc_sin_odd_ge_c1_2. exact Hx0. exact Hx2.
      * rewrite Hm.
        replace (2 * Datatypes.S m')%nat with (Datatypes.S (Datatypes.S (2 * m'))) by lia.
        apply QleT'_to_Qle. apply sc_sin_mix_ge. exact Hx0.
  - apply Qle_to_QleT'. rewrite Hm. apply QleT'_to_Qle. apply sc_sin_odd_ge_c1_2. exact Hx0. exact Hx2.
Qed.

(* ---- 严格下界：0 < x < 2 ⟹ x/3 < sin_partial n x ---- *)
Lemma sc_sin_partial_gt_third : forall (n : nat) (x : Q),
  Qlt 0 x -> Qlt x 2 -> QltT (x / 3) (sin_partial n x).
Proof.
  intros n x Hx0 Hx2.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (x - sc_sin_alt 1 x) _).
  - (* x/3 < x − x³/6：差 x·(4−x²)/6 > 0 *)
    rewrite (qeqT_imp_qeq _ _ (sc_sin_alt1_cube x)).
    rewrite (qeqT_imp_qeq _ _ (sc_qpow3_6form x)).
    apply (proj2 (Qlt_minus_iff (x / 3) (x - (x * (x * x)) * (1 / 6)))).
    assert (Hring : (x - (x * (x * x)) * (1 / 6)) - x / 3 == x * (4 - x * x) * (1 / 6)).
    { field. all: try (unfold Qeq; simpl; lia). }
    rewrite Hring.
    apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat.
      * exact Hx0.
      * (* 4 − x² > 0：x² ≤ 2x < 4 *)
        apply (proj1 (Qlt_minus_iff (x * x) 4)).
        apply (Qle_lt_trans _ (2 * x) _).
        -- apply (Qmult_le_compat_r x 2 x).
           ++ apply (Qlt_le_weak x 2). exact Hx2.
           ++ apply (Qlt_le_weak 0 x). exact Hx0.
        -- apply (Qle_lt_trans _ (x * 2) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ apply (Qmult_lt_compat_r x 2 2).
              ** change (Qlt 0 2). compute. reflexivity.
              ** exact Hx2.
    + change (Qlt 0 (1 / 6)). unfold Qdiv. compute. reflexivity.
  - apply QleT'_to_Qle. apply sc_sin_partial_lower_c1_2.
    + apply (Qlt_le_weak 0 x). exact Hx0.
    + exact Hx2.
Qed.

(* ---- Real 层：0 < X < 2 ⟹ 0 < sin X（margin eps0/3） ---- *)
Lemma real_sin_pos_lt_two : forall X : Real,
  real_lt real_zero X -> real_lt X (real_const 2) ->
  real_lt real_zero (cauchy_real_sin X).
Proof.
  intros X H0 H2.
  destruct H0 as [eps0 [Heps0 [N0 HN0]]].
  destruct H2 as [eps1 [Heps1 [N1 HN1]]].
  destruct X as [u Hu].
  set (eps := eps0 / 3).
  assert (HepsQ : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  assert (Heps_pos : QltT 0 eps).
  { unfold eps. apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - exact HepsQ.
    - apply Qinv_lt_0_compat. change (Qlt 0 3). compute. reflexivity. }
  exists eps.
  split.
  - exact Heps_pos.
  - exists (Nat.max N0 N1).
    intros n Hn.
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as He0.
    pose proof (HN1 n (NatLe_lift _ _ Hn1)) as He1.
    assert (Hupos : Qlt eps0 (u n)).
    { apply QltT_to_Qlt in He0.
      assert (Hz : u n - 0 == u n) by ring.
      rewrite Hz in He0. exact He0. }
    assert (Hu0 : Qlt 0 (u n)) by (apply (Qlt_trans _ eps0 _); [exact HepsQ | exact Hupos]).
    assert (Hu2m : Qlt (u n) (2 - eps1)).
    { apply (proj2 (Qlt_minus_iff (u n) (2 - eps1))).
      assert (Hd : (2 - eps1) - u n == (2 - u n) - eps1) by ring.
      rewrite Hd.
      apply (proj1 (Qlt_minus_iff eps1 (2 - u n))).
      exact (QltT_to_Qlt eps1 (2 - u n) He1). }
    assert (Hu2 : Qlt (u n) 2).
    { apply (Qlt_le_trans _ (2 - eps1) _); [exact Hu2m | ].
      apply (Qlt_le_weak (2 - eps1) 2).
      apply (proj2 (Qlt_minus_iff (2 - eps1) 2)).
      assert (Hr : 2 - (2 - eps1) == eps1) by ring.
      rewrite Hr.
      exact (QltT_to_Qlt 0 eps1 Heps1). }
    apply Qlt_to_QltT.
    apply (Qlt_trans _ ((u n) / 3) _).
    + unfold eps.
      apply (Qmult_lt_compat_r eps0 (u n) (Qinv 3)).
      * apply Qinv_lt_0_compat. change (Qlt 0 3). compute. reflexivity.
      * exact Hupos.
    + simpl.
      assert (Hz0 : sin_partial n (u n) - 0 == sin_partial n (u n)) by ring.
      rewrite Hz0.
      apply QltT_to_Qlt. apply (sc_sin_partial_gt_third n (u n)); [exact Hu0 | exact Hu2].
Qed.

(* ============================================================ *)
(* SC-1 检验（批 19b-1，轮 20/21）：cos 单调差级数路线·代数地基 *)
(*   cos y − cos x = (y²−x²)·Σ_{k≥1} (−1)^{k−1} A_k/(2k)!       *)
(*   本件：B0 平方幂桥、(q−p) 幂差分因子、q_pow 单调、常和       *)
(*   续作：A_k 递减链 → 交替部分和 ≥ 1/2−(p+q)/24 ≥ 1/6          *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* B0：(x·x)^k == x^{2k} *)
Lemma sc_qpow_sq : forall (x : Q) (k : nat), QeqT (q_pow (x * x) k) (q_pow x (2 * k)).
Proof.
  intros x k.
  induction k as [| k' IH].
  - apply qeq_imp_qeqT. simpl. reflexivity.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). rewrite (qeqT_imp_qeq _ _ IH).
    assert (H : (2 * Datatypes.S k' = Datatypes.S (Datatypes.S (2 * k')))%nat) by lia.
    rewrite H.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)).
    ring.
Qed.

(* B1：0 ≤ p ≤ q ⟹ p^k ≤ q^k *)
Lemma sc_qpow_le : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle p q -> QleT' (q_pow p k) (q_pow q k).
Proof.
  intros p q k Hp0 Hpq.
  induction k as [| k' IH].
  - apply Qle_to_QleT'. simpl. apply Qle_refl.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)).
    assert (Hq0 : Qle 0 q) by (apply (Qle_trans _ p _); [exact Hp0 | exact Hpq]).
    apply (Qle_trans _ (p * q_pow q k') _).
    + apply QleT'_to_Qle. apply (sc_qmult_le_l (q_pow p k') (q_pow q k') p).
      * exact (QleT'_to_Qle _ _ IH).
      * exact Hp0.
    + apply (Qmult_le_compat_r p q (q_pow q k')).
      * exact Hpq.
      * apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hq0.
Qed.

(* B2：常和：Σ_{i<n} c == (n#1)·c *)
Lemma sc_sum_const : forall (n : nat) (c : Q), QeqT (sum_upto n (fun _ : nat => c)) ((Z.of_nat n # 1) * c).
Proof.
  intros n c.
  induction n as [| n' IH].
  - apply qeq_imp_qeqT. simpl. ring.
  - apply qeq_imp_qeqT. simpl. rewrite (qeqT_imp_qeq _ _ IH).
    assert (Hplus : (Z.of_nat (Datatypes.S n') # 1) == (Z.of_nat n' # 1) + 1).
    { unfold Qeq. simpl. lia. }
    rewrite Hplus. ring.
Qed.

(* B3：幂差分因子（对称形）：q^k − p^k == (q−p)·Σ_{i<k} q^{k−1−i}·p^i *)
Lemma sc_qpow_diff_factor : forall (p q : Q) (k : nat), QeqT (q_pow q k - q_pow p k) ((q - p) * sum_upto k (fun i : nat => q_pow q (k - 1 - i) * q_pow p i)).
Proof.
  intros p q k.
  induction k as [| k' IH].
  - apply qeq_imp_qeqT. simpl. ring.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)).
    transitivity (q * q_pow q k' - p * q_pow p k').
    + reflexivity.
    + assert (Hsum : sum_upto (Datatypes.S k') (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i) ==
                     q_pow p k' + q * sum_upto k' (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i)).
      { change (sum_upto (Datatypes.S k') (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i))
          with (sum_upto k' (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i) +
                (q_pow q (Datatypes.S k' - 1 - k') * q_pow p k')).
        assert (H0 : q_pow q (Datatypes.S k' - 1 - k') * q_pow p k' == q_pow p k').
        { assert (Hz : (Datatypes.S k' - 1 - k' = 0)%nat) by lia.
          rewrite Hz. simpl. ring. }
        rewrite H0.
        assert (Hpre : forall i : nat, NatLe (Datatypes.S i) k' -> QeqT (q_pow q (Datatypes.S k' - 1 - i) * q_pow p i) (q * (q_pow q (k' - 1 - i) * q_pow p i))).
        { intros i Hi. apply NatLe_drop in Hi.
          assert (Hidx : (Datatypes.S k' - 1 - i = Datatypes.S (k' - 1 - i))%nat) by lia.
          rewrite Hidx. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). ring. }
        rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below k'
          (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i)
          (fun i : nat => q * (q_pow q (k' - 1 - i) * q_pow p i)) Hpre)).
        rewrite (qeqT_imp_qeq _ _ (sum_upto_scale k' q (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i))).
        ring. }
      rewrite Hsum.
      assert (Hdist : (q - p) * (q_pow p k' + q * sum_upto k' (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i)) ==
                      (q - p) * q_pow p k' + q * ((q - p) * sum_upto k' (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i))).
      { ring. }
      rewrite Hdist. rewrite <- (qeqT_imp_qeq _ _ IH). ring.
Qed.


(* A_k := Σ_{i<k} q^{k−1−i}·p^i *)
Definition sc_A (p q : Q) (k : nat) : Q :=
  sum_upto k (fun i : nat => q_pow q (k - 1 - i) * q_pow p i).

(* C0：0 ≤ p、0 ≤ q ⟹ 0 ≤ A_k *)
Lemma sc_A_nonneg : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> QleT' 0 (sc_A p q k).
Proof.
  intros p q k Hp0 Hq0. apply Qle_to_QleT'. unfold sc_A. apply QleT'_to_Qle. apply sc_sum_nonneg. intro m.
  exact (Qmult_le_0_compat (q_pow q (k - 1 - m)) (q_pow p m)
    (QleT'_to_Qle _ _ (q_pow_nonneg q (k - 1 - m) (Qle_to_QleT' _ _ Hq0))) (QleT'_to_Qle _ _ (q_pow_nonneg p m (Qle_to_QleT' _ _ Hp0)))).
Qed.

(* 辅助：sum_upto 1 (fun k => g (a+k)) == g a *)
Lemma sc_sum_upto1_shift : forall (a : nat) (g : nat -> Q), QeqT (sum_upto 1 (fun k : nat => g ((a + k)%nat))) (g a).
Proof.
  intros a g.
  apply qeq_imp_qeqT.
  change (sum_upto 1 (fun k : nat => g ((a + k)%nat))) with
    (sum_upto 0 (fun k : nat => g ((a + k)%nat)) + g ((a + 0)%nat)).
  simpl. rewrite (Qplus_0_l (g ((a + 0)%nat))). rewrite (Nat.add_0_r a). reflexivity.
Qed.

(* C1：k ≥ 1 ⟹ A_k ≥ q^{k−1}（i=0 项） *)
Lemma sc_A_ge_q : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> (1 <= k)%nat -> QleT' (q_pow q (k - 1)) (sc_A p q k).
Proof.
  intros p q k Hp0 Hq0 Hk.
  apply Qle_to_QleT'.
  unfold sc_A.
  apply (Qle_trans _ (q_pow q (k - 1) * q_pow p 0) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl (q_pow p 0). ring.
  - apply (Qle_trans _ (sum_upto 1 (fun k0 : nat => q_pow q (k - 1 - (0 + k0)) * q_pow p (0 + k0))) _).
    + assert (He : q_pow q (k - 1) * q_pow p 0 == q_pow q (k - 1 - 0) * q_pow p 0).
      { assert (Hn0 : (k - 1 - 0 = k - 1)%nat) by lia. rewrite Hn0. reflexivity. }
      apply (Qle_trans _ (q_pow q (k - 1 - 0) * q_pow p 0) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact He.
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (sc_sum_upto1_shift 0 (fun i : nat => q_pow q (k - 1 - i) * q_pow p i)))).
    + apply QleT'_to_Qle. apply (sc_sum_shift_sub_le 0 1 k (fun i : nat => q_pow q (k - 1 - i) * q_pow p i)).
      * intro m. apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hq0.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hp0.
      * lia.
Qed.

(* C1'：k ≥ 1 ⟹ A_k ≥ p^{k−1}（i=k−1 项） *)
Lemma sc_A_ge_p : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> (1 <= k)%nat -> QleT' (q_pow p (k - 1)) (sc_A p q k).
Proof.
  intros p q k Hp0 Hq0 Hk.
  apply Qle_to_QleT'.
  unfold sc_A.
  apply (Qle_trans _ (q_pow q 0 * q_pow p (k - 1)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl (q_pow q 0). ring.
  - apply (Qle_trans _ (sum_upto 1 (fun k0 : nat => q_pow q (k - 1 - ((k - 1) + k0)) * q_pow p ((k - 1) + k0))) _).
    + assert (He : q_pow q 0 * q_pow p (k - 1) == q_pow q (k - 1 - (k - 1)) * q_pow p (k - 1)).
      { assert (Hn0 : (k - 1 - (k - 1) = 0)%nat) by lia. rewrite Hn0. reflexivity. }
      apply (Qle_trans _ (q_pow q (k - 1 - (k - 1)) * q_pow p (k - 1)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact He.
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (sc_sum_upto1_shift (k - 1) (fun i : nat => q_pow q (k - 1 - i) * q_pow p i)))).
    + apply QleT'_to_Qle. apply (sc_sum_shift_sub_le (k - 1) 1 k (fun i : nat => q_pow q (k - 1 - i) * q_pow p i)).
      * intro m. apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hq0.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hp0.
      * lia.
Qed.

(* C3：递推 A (S k) == q·A_k + p^k *)
Lemma sc_A_succ : forall (p q : Q) (k : nat), QeqT (sc_A p q (Datatypes.S k)) (q * sc_A p q k + q_pow p k).
Proof.
  intros p q k.
  apply qeq_imp_qeqT.
  unfold sc_A.
  change (sum_upto (Datatypes.S k) (fun i : nat => q_pow q (Datatypes.S k - 1 - i) * q_pow p i))
    with (sum_upto k (fun i : nat => q_pow q (Datatypes.S k - 1 - i) * q_pow p i) +
          (q_pow q (Datatypes.S k - 1 - k) * q_pow p k)).
  assert (H0 : q_pow q (Datatypes.S k - 1 - k) * q_pow p k == q_pow p k).
  { assert (Hz : (Datatypes.S k - 1 - k = 0)%nat) by lia.
    rewrite Hz. simpl. ring. }
  rewrite H0.
  assert (Hpre : forall i : nat, NatLe (Datatypes.S i) k -> QeqT (q_pow q (Datatypes.S k - 1 - i) * q_pow p i) (q * (q_pow q (k - 1 - i) * q_pow p i))).
  { intros i Hi. apply NatLe_drop in Hi.
    assert (Hidx : (Datatypes.S k - 1 - i = Datatypes.S (k - 1 - i))%nat) by lia.
    rewrite Hidx. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below k
    (fun i : nat => q_pow q (Datatypes.S k - 1 - i) * q_pow p i)
    (fun i : nat => q * (q_pow q (k - 1 - i) * q_pow p i)) Hpre)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_scale k q (fun i : nat => q_pow q (k - 1 - i) * q_pow p i))).
  ring.
Qed.

(* C4a：8 ≤ (2k+1)(2k+2)（k ≥ 1） *)
Lemma sc_M_ge8 : forall (k : nat), (1 <= k)%nat ->
  QleT' 8 ((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1).
Proof.
  intros k Hk. apply Qle_to_QleT'. unfold Qle. simpl.
  change (8 <= Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2) * 1)%Z.
  rewrite (Z.mul_1_r (Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2))).
  apply (Z.le_trans _ 12 _); [lia | ].
  apply (Z.mul_le_mono_nonneg 3 (Z.of_nat (2 * k + 1)) 4 (Z.of_nat (2 * k + 2))).
  all: lia.
Qed.

(* C4b：q_fact 双跳（S 形） *)
Lemma sc_qfact_2succ : forall (k : nat), QeqT (q_fact (2 * Datatypes.S k)) ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) *
  (Z.of_nat (Datatypes.S (2 * k)) # 1) * q_fact (2 * k)).
Proof.
  intro k.
  apply qeq_imp_qeqT.
  assert (Hn : (2 * Datatypes.S k = Datatypes.S (Datatypes.S (2 * k)))%nat) by lia.
  rewrite Hn.
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ _)). rewrite (qeqT_imp_qeq _ _ (q_fact_succ _)).
  ring.
Qed.

Lemma sc_M_qmult : forall (k : nat), QeqT ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) *
  (Z.of_nat (Datatypes.S (2 * k)) # 1)) ((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1).
Proof.
  intro k.
  apply qeq_imp_qeqT.
  assert (Ha : (Datatypes.S (Datatypes.S (2 * k)) = 2 * k + 2)%nat) by lia.
  assert (Hb : (Datatypes.S (2 * k) = 2 * k + 1)%nat) by lia.
  rewrite Ha. rewrite Hb.
  unfold Qeq. simpl. ring.
Qed.

(* 除式交叉：0<c、0<d、a·d ≤ b·c ⟹ a/c ≤ b/d *)
Lemma sc_qle_div_cross : forall (a b c d : Q), Qlt 0 c -> Qlt 0 d ->
  Qle (a * d) (b * c) -> QleT' (a / c) (b / d).
Proof.
  intros a b c d Hc Hd H.
  apply Qle_to_QleT'.
  apply (Qle_shift_div_r a c (b / d)).
  - exact Hc.
  - apply (Qle_trans _ ((b * c) / d) _).
    + apply (Qle_shift_div_l a (b * c) d).
      * exact Hd.
      * exact H.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

(* C4c：q·A_k + p^k ≤ M_k·A_k *)
Lemma sc_A_succ_bound : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle p q -> Qle q 4 -> (1 <= k)%nat ->
  QleT' (q * sc_A p q k + q_pow p k)
      (((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1) * sc_A p q k).
Proof.
  intros p q k Hp0 Hpq Hq4 Hk.
  apply Qle_to_QleT'.
  set (M := (Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1).
  assert (Hq0 : Qle 0 q) by (apply (Qle_trans _ p _); [exact Hp0 | exact Hpq]).
  assert (HM8 : Qle 8 M) by (unfold M; (apply QleT'_to_Qle; apply sc_M_ge8); exact Hk).
  assert (HpqM : Qle (p + q) M).
  { apply (Qle_trans _ (4 + 4) _).
    - apply Qplus_le_compat.
      + apply (Qle_trans _ q _); [exact Hpq | exact Hq4].
      + exact Hq4.
    - unfold Qle. simpl. lia. }
  assert (HpMq : Qle p (M - q)).
  { apply (proj2 (Qle_minus_iff p (M - q))).
    assert (Hr : (M - q) - p == M - (p + q)) by ring.
    rewrite Hr.
    apply (proj1 (Qle_minus_iff (p + q) M)). exact HpqM. }
  assert (HqM : Qle q M) by (apply (Qle_trans _ 4 _); [exact Hq4 | apply (Qle_trans _ 8 _); [unfold Qle; simpl; lia | exact HM8]]).
  assert (H1 : Qle (q * sc_A p q k) (M * sc_A p q k)).
  { apply (Qmult_le_compat_r q M (sc_A p q k)).
    - exact HqM.
    - apply QleT'_to_Qle. apply (sc_A_nonneg p q k Hp0 Hq0). }
  assert (H2 : Qle (q_pow p k) ((M - q) * sc_A p q k)).
  { assert (Hk1 : (k = Datatypes.S (k - 1))%nat) by lia.
    rewrite Hk1. rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)).
    apply (Qle_trans _ ((M - q) * q_pow p (k - 1)) _).
    - apply (Qmult_le_compat_r p (M - q) (q_pow p (k - 1))).
      + exact HpMq.
      + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hp0.
    - apply QleT'_to_Qle. apply (sc_qmult_le_l (q_pow p (k - 1)) (sc_A p q (Datatypes.S (k - 1))) (M - q)).
      + assert (He : q_pow p (k - 1) == q_pow p (Datatypes.S (k - 1) - 1)).
        { assert (Hn : (Datatypes.S (k - 1) - 1 = k - 1)%nat) by lia. rewrite Hn. reflexivity. }
        apply (Qle_trans _ (q_pow p (Datatypes.S (k - 1) - 1)) _).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact He.
        * apply QleT'_to_Qle. apply (sc_A_ge_p p q (Datatypes.S (k - 1)) Hp0 Hq0). lia.
      + apply (proj1 (Qle_minus_iff q M)).
        apply (Qle_trans _ 4 _); [exact Hq4 | apply (Qle_trans _ 8 _); [unfold Qle; simpl; lia | exact HM8]]. }
  apply (Qle_trans _ (q * sc_A p q k + (M - q) * sc_A p q k) _).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact H2.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold M. ring.
Qed.

(* C4 主：t_{k+1} ≤ t_k *)
Lemma sc_t_dec : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle p q -> Qle q 4 -> (1 <= k)%nat ->
  QleT' (sc_A p q (Datatypes.S k) / q_fact (2 * Datatypes.S k))
      (sc_A p q k / q_fact (2 * k)).
Proof.
  intros p q k Hp0 Hpq Hq4 Hk.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_A_succ p q k)).
  apply QleT'_to_Qle. apply (sc_qle_div_cross (q * sc_A p q k + q_pow p k) (sc_A p q k)
                          (q_fact (2 * Datatypes.S k)) (q_fact (2 * k))).
  - apply QltT_to_Qlt. apply q_fact_pos.
  - apply QltT_to_Qlt. apply q_fact_pos.
  - assert (Hsb := sc_A_succ_bound p q k Hp0 Hpq Hq4 Hk).
    apply (Qle_trans _ (((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1) *
                        sc_A p q k * q_fact (2 * k)) _).
    + apply (Qmult_le_compat_r (q * sc_A p q k + q_pow p k)
             (((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1) * sc_A p q k)
             (q_fact (2 * k))).
      * apply QleT'_to_Qle. exact Hsb.
      * apply (Qlt_le_weak 0 (q_fact (2 * k))). apply QltT_to_Qlt. apply q_fact_pos.
    + rewrite (qeqT_imp_qeq _ _ (sc_qfact_2succ k)).
      rewrite (qeqT_imp_qeq _ _ (sc_M_qmult k)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

(* ---- P_N := Σ_{k<N} (−1)^{k−1}·A_k/(2k)!（t_0 项为 0 无害） ---- *)
Definition sc_P (p q : Q) (N : nat) : Q :=
  sum_upto N (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))).

(* t_k ≥ 0 *)
Lemma sc_t_nonneg : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> QleT' 0 (sc_A p q k / q_fact (2 * k)).
Proof.
  intros p q k Hp0 Hq0.
  apply Qle_to_QleT'.
  unfold Qdiv.
  exact (Qmult_le_0_compat (sc_A p q k) (Qinv (q_fact (2 * k)))
    (QleT'_to_Qle _ _ (sc_A_nonneg p q k Hp0 Hq0))
    (Qlt_le_weak 0 (Qinv (q_fact (2 * k)))
      (Qinv_lt_0_compat (q_fact (2 * k)) (QltT_to_Qlt 0 (q_fact (2 * k)) (q_fact_pos (2 * k)))))).
Qed.

(* 单步恒等 *)
Lemma sc_P_step1 : forall (p q : Q) (N : nat), QeqT (sc_P p q (Datatypes.S N)) (sc_P p q N + q_pow (-1) (N - 1) * (sc_A p q N / q_fact (2 * N))).
Proof.
  intros p q N.
  apply qeq_imp_qeqT.
  unfold sc_P.
  set (f := fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))).
  change (sum_upto (Datatypes.S N) f) with (sum_upto N f + f N).
  unfold f. reflexivity.
Qed.

(* 双步恒等 *)
Lemma sc_P_step2 : forall (p q : Q) (N : nat), QeqT (sc_P p q (Datatypes.S (Datatypes.S N))) (sc_P p q N +
  q_pow (-1) (N - 1) * (sc_A p q N / q_fact (2 * N)) +
  q_pow (-1) (Datatypes.S N - 1) * (sc_A p q (Datatypes.S N) / q_fact (2 * Datatypes.S N))).
Proof.
  intros p q N.
  apply qeq_imp_qeqT.
  unfold sc_P.
  set (f := fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))).
  change (sum_upto (Datatypes.S (Datatypes.S N)) f) with (sum_upto (Datatypes.S N) f + f (Datatypes.S N)).
  change (sum_upto (Datatypes.S N) f) with (sum_upto N f + f N).
  unfold f. reflexivity.
Qed.

(* 增量：P(S(S(S(2m)))) ≥ P(S(2m))（+t_{S(2m)} − t_{S(S(2m))} ≥ 0） *)
Lemma sc_P_inc : forall (p q : Q) (m : nat),
  Qle 0 p -> Qle 0 q -> Qle p q -> Qle q 4 ->
  QleT' (sc_P p q (Datatypes.S (2 * m)))
      (sc_P p q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
Proof.
  intros p q m Hp0 Hq0 Hpq Hq4.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_P_step2 p q (Datatypes.S (2 * m)))).
  assert (Ha : (Datatypes.S (2 * m) - 1 = 2 * m)%nat) by lia.
  rewrite Ha.
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even m)).
  assert (Ho : q_pow (-1) (Datatypes.S (Datatypes.S (2 * m)) - 1) == -1).
  { assert (Hbo : (Datatypes.S (Datatypes.S (2 * m)) - 1 = Datatypes.S (2 * m))%nat) by lia.
    rewrite Hbo.
    assert (Hbo2 : (Datatypes.S (2 * m) = 2 * m + 1)%nat) by lia.
    rewrite Hbo2. exact (qeqT_imp_qeq _ _ (q_pow_neg1_odd m)). }
  rewrite Ho.
  set (T1 := sc_A p q (Datatypes.S (2 * m)) / q_fact (2 * Datatypes.S (2 * m))).
  set (T2 := sc_A p q (Datatypes.S (Datatypes.S (2 * m))) / q_fact (2 * Datatypes.S (Datatypes.S (2 * m)))).
  apply (Qle_trans _ (sc_P p q (Datatypes.S (2 * m)) + (T1 - T2)) _).
  - apply (Qle_plus_nonneg_r (sc_P p q (Datatypes.S (2 * m))) (T1 - T2)).
    apply (proj1 (Qle_minus_iff T2 T1)).
    unfold T1, T2.
    apply QleT'_to_Qle. apply (sc_t_dec p q (Datatypes.S (2 * m)) Hp0 Hpq Hq4). lia.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold T1, T2, Qdiv. ring.
Qed.

(* 奇延伸：P(S(S(2m))) ≥ P(S(2m))（+t_{S(2m)} ≥ 0） *)
Lemma sc_P_odd_ge : forall (p q : Q) (m : nat),
  Qle 0 p -> Qle 0 q ->
  QleT' (sc_P p q (Datatypes.S (2 * m)))
      (sc_P p q (Datatypes.S (Datatypes.S (2 * m)))).
Proof.
  intros p q m Hp0 Hq0.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_P_step1 p q (Datatypes.S (2 * m)))).
  assert (Ha : (Datatypes.S (2 * m) - 1 = 2 * m)%nat) by lia.
  rewrite Ha.
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even m)).
  rewrite (Qmult_1_l (sc_A p q (Datatypes.S (2 * m)) / q_fact (2 * Datatypes.S (2 * m)))).
  apply (Qle_plus_nonneg_r (sc_P p q (Datatypes.S (2 * m)))
          (sc_A p q (Datatypes.S (2 * m)) / q_fact (2 * Datatypes.S (2 * m)))).
  apply QleT'_to_Qle. apply (sc_t_nonneg p q (Datatypes.S (2 * m)) Hp0 Hq0).
Qed.

(* 偶子列：P_{2m} ≥ P_2（sc_P (S(2m)) ≥ sc_P 3，m ≥ 1） *)
Lemma sc_P_even_ge : forall (p q : Q) (m : nat),
  Qle 0 p -> Qle 0 q -> Qle p q -> Qle q 4 ->
  QleT' (sc_P p q 3) (sc_P p q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
Proof.
  intros p q m Hp0 Hq0 Hpq Hq4.
  induction m as [| m' IH].
  - apply Qle_to_QleT'. replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * 0)))) with 3%nat by lia.
    apply Qle_refl.
  - apply Qle_to_QleT'. apply (Qle_trans _ (sc_P p q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))) _).
    + exact (QleT'_to_Qle _ _ IH).
    + replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m')))) with (Datatypes.S (2 * Datatypes.S m')) by lia.
      apply QleT'_to_Qle. apply (sc_P_inc p q (Datatypes.S m') Hp0 Hq0 Hpq Hq4).
Qed.

(* 总下界：N ≥ 3 ⟹ P_2 ≤ P_N *)
Lemma sc_P_ge_P2 : forall (p q : Q) (N : nat),
  Qle 0 p -> Qle 0 q -> Qle p q -> Qle q 4 -> (3 <= N)%nat ->
  QleT' (sc_P p q 3) (sc_P p q N).
Proof.
  intros p q N Hp0 Hq0 Hpq Hq4 HN.
  destruct (sc_nat_split (N - 1)) as [m Hm | m Hm].
  - apply Qle_to_QleT'. (* N−1 = 2m：N = S(2m) = S(S(S(2m'')))（m = S m''，N ≥ 3 ⟹ m'' 存在） *)
    destruct m as [| m''].
    + assert (Hz : (3 <= Datatypes.S (2 * 0))%nat -> False) by lia.
      exfalso. apply Hz. lia.
    + assert (HN' : (N = Datatypes.S (2 * Datatypes.S m''))%nat) by lia.
      rewrite HN'.
      replace (Datatypes.S (2 * Datatypes.S m'')) with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'')))) by lia.
      apply QleT'_to_Qle. apply (sc_P_even_ge p q m'' Hp0 Hq0 Hpq Hq4).
  - apply Qle_to_QleT'. (* N−1 = S(2m)：N = S(S(2m))，m ≥ 1（N ≥ 4） *)
    assert (Hm1 : (1 <= m)%nat) by lia.
    assert (HN' : (N = Datatypes.S (Datatypes.S (2 * m)))%nat) by lia.
    rewrite HN'.
    apply (Qle_trans _ (sc_P p q (Datatypes.S (2 * m))) _).
    + destruct m as [| m''].
      * assert (Hz : (3 <= Datatypes.S (Datatypes.S (2 * 0)))%nat -> False) by lia.
        exfalso. apply Hz. lia.
      * replace (Datatypes.S (2 * Datatypes.S m'')) with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'')))) by lia.
        apply QleT'_to_Qle. apply (sc_P_even_ge p q m'' Hp0 Hq0 Hpq Hq4).
    + apply QleT'_to_Qle. apply (sc_P_odd_ge p q m Hp0 Hq0).
Qed.

(* A_1 == 1、A_2 == p+q *)
Lemma sc_A_1 : forall (p q : Q), QeqT (sc_A p q 1) (1).
Proof.
  intros p q. apply qeq_imp_qeqT. unfold sc_A.
  change (sum_upto 1 (fun i : nat => q_pow q (1 - 1 - i) * q_pow p i)) with
         (sum_upto 0 (fun i : nat => q_pow q (1 - 1 - i) * q_pow p i) + q_pow q (1 - 1 - 0) * q_pow p 0).
  simpl. ring.
Qed.

Lemma sc_A_2 : forall (p q : Q), QeqT (sc_A p q 2) (p + q).
Proof.
  intros p q. apply qeq_imp_qeqT. unfold sc_A.
  change (sum_upto 2 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i)) with
         (sum_upto 1 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i) + q_pow q (2 - 1 - 1) * q_pow p 1).
  change (sum_upto 1 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i)) with
         (sum_upto 0 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i) + q_pow q (2 - 1 - 0) * q_pow p 0).
  simpl. ring.
Qed.

(* P_2 == 1/2 − (p+q)/24 *)
Lemma sc_P2_val : forall (p q : Q), QeqT (sc_P p q 3) (1 / 2 - (p + q) / 24).
Proof.
  intros p q. apply qeq_imp_qeqT. unfold sc_P.
  change (sum_upto 3 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k)))) with
         (sum_upto 2 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))) + q_pow (-1) 1 * (sc_A p q 2 / q_fact 4)).
  change (sum_upto 2 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k)))) with
         (sum_upto 1 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))) + q_pow (-1) 0 * (sc_A p q 1 / q_fact 2)).
  change (sum_upto 1 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k)))) with
         (sum_upto 0 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))) + q_pow (-1) 0 * (sc_A p q 0 / q_fact 0)).
  simpl.
  rewrite (qeqT_imp_qeq _ _ (sc_A_1 p q)). rewrite (qeqT_imp_qeq _ _ (sc_A_2 p q)).
  assert (Hf2 : q_fact 2 == 2) by (vm_compute; reflexivity).
  assert (Hf4 : q_fact 4 == 24) by (vm_compute; reflexivity).
  rewrite Hf2. rewrite Hf4.
  assert (H0 : sc_A p q 0 == 0) by (unfold sc_A; simpl; ring).
  rewrite H0.
  unfold Qdiv. ring.
Qed.

(* P_2 ≥ 1/6 *)
Lemma sc_P2_ge_sixth : forall (p q : Q),
  Qle 0 p -> Qle p q -> Qle q 4 -> QleT' (1 / 6) (sc_P p q 3).
Proof.
  intros p q Hp0 Hpq Hq4.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_P2_val p q)).
  apply (proj2 (Qle_minus_iff (1 / 6) (1 / 2 - (p + q) / 24))).
  assert (Hpq8 : Qle (p + q) 8).
  { apply (Qle_trans _ (4 + 4) _).
    - apply Qplus_le_compat.
      + apply (Qle_trans _ q _); [exact Hpq | exact Hq4].
      + exact Hq4.
    - unfold Qle. simpl. lia. }
  apply (proj1 (Qle_minus_iff (p + q) 8)) in Hpq8.
  assert (He : (1 / 2 - (p + q) / 24) - 1 / 6 == (8 - (p + q)) / 24).
  { field. all: try (unfold Qeq; simpl; lia). }
  rewrite He.
  unfold Qdiv.
  apply Qmult_le_0_compat.
  - exact Hpq8.
  - apply (Qlt_le_weak 0 (Qinv 24)).
    apply Qinv_lt_0_compat. change (Qlt 0 24). compute. reflexivity.
Qed.

(* 幂差分因子（桥到 x^{2k} 形，p := x·x、q := y·y） *)
Lemma sc_qpow2_diff : forall (x y : Q) (k : nat), QeqT (q_pow x (2 * k) - q_pow y (2 * k)) (- ((y * y - x * x) * sum_upto k (fun i : nat => q_pow (y * y) (k - 1 - i) * q_pow (x * x) i))).
Proof.
  intros x y k.
  apply qeq_imp_qeqT.
  assert (H1 : q_pow x (2 * k) == q_pow (x * x) k) by (apply Qeq_sym; (apply qeqT_imp_qeq; apply (sc_qpow_sq x k))).
  assert (H2 : q_pow y (2 * k) == q_pow (y * y) k) by (apply Qeq_sym; (apply qeqT_imp_qeq; apply (sc_qpow_sq y k))).
  rewrite H1. rewrite H2.
  rewrite <- (qeqT_imp_qeq _ _ (sc_qpow_diff_factor (x * x) (y * y) k)).
  ring.
Qed.

(* 符号桥：k ≥ 1 ⟹ (−1)^k·(−1) == (−1)^{k−1} *)
Lemma sc_q_pow_pred : forall (k : nat), (1 <= k)%nat ->QeqT (q_pow (-1) k * -1) (q_pow (-1) (k - 1)).
Proof.
  intros k Hk.
  destruct k as [| k'].
  - apply qeq_imp_qeqT. lia.
  - apply qeq_imp_qeqT. assert (Hn : (Datatypes.S k' - 1 = k')%nat) by lia.
    rewrite Hn.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ _ _)). ring.
Qed.

(* 逐项：cos_term k x − cos_term k y == (y²−x²)·(−1)^{k−1}·A_k/(2k)!（∀k） *)
Lemma sc_cos_diff_term : forall (x y : Q) (k : nat), QeqT (cos_term k x - cos_term k y) ((y * y - x * x) * (q_pow (-1) (k - 1) * (sc_A (x * x) (y * y) k / q_fact (2 * k)))).
Proof.
  intros x y k.
  destruct k as [| k'].
  - apply qeq_imp_qeqT. (* k = 0：两侧均 0（A_0 = 0） *)
    unfold sc_A, cos_term. simpl. unfold Qdiv.
    field. all: try (unfold Qeq; simpl; lia).
    all: try (unfold Qeq; simpl; discriminate).
  - apply qeq_imp_qeqT. (* k = S k' ≥ 1：主路径 *)
    unfold cos_term, sc_A.
    (* 1. 同分母合成 *)
    assert (Hc : q_pow (-1) (Datatypes.S k') * (q_pow x (2 * Datatypes.S k') / q_fact (2 * Datatypes.S k')) -
                 q_pow (-1) (Datatypes.S k') * (q_pow y (2 * Datatypes.S k') / q_fact (2 * Datatypes.S k')) ==
                 q_pow (-1) (Datatypes.S k') * (q_pow x (2 * Datatypes.S k') - q_pow y (2 * Datatypes.S k')) / q_fact (2 * Datatypes.S k')).
    { unfold Qdiv. field. intro Hc. exact (match q_neq_of_lt _ (q_fact_pos (2 * Datatypes.S k')) (qeq_imp_qeqT _ _ Hc) with end). }
    rewrite Hc.
    (* 2. 幂差分因子 *)
    rewrite (qeqT_imp_qeq _ _ (sc_qpow2_diff x y (Datatypes.S k'))).
    (* 3. 符号桥提负号 *)
    set (X := (y * y - x * x) * sum_upto (Datatypes.S k') (fun i : nat => q_pow (y * y) (Datatypes.S k' - 1 - i) * q_pow (x * x) i)).
    assert (Hsg : q_pow (-1) (Datatypes.S k') * - X == q_pow (-1) (Datatypes.S k' - 1) * X).
    { assert (Hneg : - X == -1 * X) by ring.
      rewrite Hneg.
      assert (H1616 : (1 <= Datatypes.S k')%nat) by lia.
      rewrite <- (qeqT_imp_qeq _ _ (sc_q_pow_pred (Datatypes.S k') H1616)); [ring]. }
    rewrite Hsg.
    unfold X. unfold Qdiv. ring.
Qed.
(* 和恒等：cos_partial n x − cos_partial n y == (y²−x²)·sc_P (x·x) (y·y) (S n) *)
Lemma sc_cos_partial_diff_eq : forall (n : nat) (x y : Q), QeqT (cos_partial n x - cos_partial n y) ((y * y - x * x) * sc_P (x * x) (y * y) (Datatypes.S n)).
Proof.
  intros n x y.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n x)). rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n y)).
  rewrite <- (qeqT_imp_qeq _ _ (sum_upto_minus (Datatypes.S n) (fun j : nat => cos_term j x) (fun j : nat => cos_term j y))).
  assert (Hpre : forall j : nat, QeqT (cos_term j x - cos_term j y) ((y * y - x * x) * (q_pow (-1) (j - 1) * (sc_A (x * x) (y * y) j / q_fact (2 * j))))).
  { intro j. exact (sc_cos_diff_term x y j). }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (Datatypes.S n)
    (fun j : nat => cos_term j x - cos_term j y)
    (fun j : nat => (y * y - x * x) * (q_pow (-1) (j - 1) * (sc_A (x * x) (y * y) j / q_fact (2 * j)))) Hpre)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S n) (y * y - x * x)
            (fun j : nat => q_pow (-1) (j - 1) * (sc_A (x * x) (y * y) j / q_fact (2 * j))))).
  unfold sc_P. reflexivity.
Qed.

(* 主引理：0 ≤ x ≤ y ≤ 2、n ≥ 2 ⟹ cos_partial n y ≤ cos_partial n x − (y²−x²)/6 *)
Lemma sc_cos_partial_diff_le : forall (n : nat) (x y : Q),
  Qle 0 x -> Qle x y -> Qle y 2 -> (2 <= n)%nat ->
  QleT' (cos_partial n y) (cos_partial n x - (y * y - x * x) * (1 / 6)).
Proof.
  intros n x y Hx0 Hxy Hy2 Hn.
  apply Qle_to_QleT'.
  set (p := x * x). set (q := y * y).
  assert (Hp0 : Qle 0 p) by (unfold p; apply Qmult_le_0_compat; [exact Hx0 | exact Hx0]).
  assert (Hq0 : Qle 0 q).
  { unfold q. apply Qmult_le_0_compat.
    - apply (Qle_trans _ x _); [exact Hx0 | exact Hxy].
    - apply (Qle_trans _ x _); [exact Hx0 | exact Hxy]. }
  assert (Hy0 : Qle 0 y) by (apply (Qle_trans _ x _); [exact Hx0 | exact Hxy]).
  assert (Hpq : Qle p q).
  { unfold p, q.
    apply (Qle_trans _ (y * x) _).
    - apply (Qmult_le_compat_r x y x).
      + exact Hxy.
      + exact Hx0.
    - apply QleT'_to_Qle. apply (sc_qmult_le_l x y y).
      + exact Hxy.
      + exact Hy0. }
  assert (Hq4 : Qle q 4).
  { unfold q.
    apply (Qle_trans _ (2 * y) _).
    - apply (Qmult_le_compat_r y 2 y).
      + exact Hy2.
      + exact Hy0.
    - apply (Qle_trans _ (2 * 2) _).
      + apply QleT'_to_Qle. apply (sc_qmult_le_l y 2 2).
        * exact Hy2.
        * unfold Qle. simpl. lia.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hpq0 : Qle 0 (q - p)).
  { apply (proj1 (Qle_minus_iff p q)). exact Hpq. }
  assert (Hsix : Qle (1 / 6) (sc_P p q (Datatypes.S n))).
  { apply (Qle_trans _ (sc_P p q 3) _).
    - apply QleT'_to_Qle. apply (sc_P2_ge_sixth p q Hp0 Hpq Hq4).
    - apply QleT'_to_Qle. apply (sc_P_ge_P2 p q (Datatypes.S n) Hp0 Hq0 Hpq Hq4).
      lia. }
  assert (Hge : Qle ((q - p) * (1 / 6)) (cos_partial n x - cos_partial n y)).
  { rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_diff_eq n x y)).
    apply QleT'_to_Qle. apply (sc_qmult_le_l (1 / 6) (sc_P p q (Datatypes.S n)) (q - p)).
    - exact Hsix.
    - exact Hpq0. }
  apply (proj2 (Qle_minus_iff (cos_partial n y) (cos_partial n x - (q - p) * (1 / 6)))).
  assert (Hr : (cos_partial n x - (q - p) * (1 / 6)) + - cos_partial n y ==
               (cos_partial n x - cos_partial n y) - (q - p) * (1 / 6)) by ring.
  rewrite Hr.
  apply (proj1 (Qle_minus_iff ((q - p) * (1 / 6)) (cos_partial n x - cos_partial n y))).
  exact Hge.
Qed.

(* ============================================================ *)
(* SC-1 批 19c（轮 23）：Real 层 cos 严格递减 (0,2)              *)
(*   real_cos_strict_decr：0 < X < Y < 2 ⟹ cos Y < cos X       *)
(* 依赖：Q 层主引理 sc_cos_partial_diff_le（批 19b-2c 已并入，  *)
(*       备份 178）；本件 margin eps := eps0²/6 + 差积分解组装   *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* Real 层：cos 严格递减（0 < X < Y < 2 ⟹ cos Y < cos X） *)
Lemma real_cos_strict_decr : forall X Y : Real,
  real_lt real_zero X -> real_lt X Y -> real_lt Y (real_const 2) ->
  real_lt (cauchy_real_cos Y) (cauchy_real_cos X).
Proof.
  intros X Y H0 HXY H2.
  destruct H0 as [eps2 [Heps2 [N2 HN2]]].
  destruct HXY as [eps0 [Heps0 [N0 HN0]]].
  destruct H2 as [eps1 [Heps1 [N1 HN1]]].
  destruct X as [u Hu]. destruct Y as [v Hv].
  (* margin：eps := eps0²/6（eps0 来自 0 < Y − X 的分离模） *)
  set (eps := q_pow eps0 2 * (1 / 6)).
  assert (Heps0Q : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  assert (Heps_pos : QltT 0 eps).
  { unfold eps. apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply sc_qpow_pos. exact Heps0Q.
    - change (Qlt 0 (1 / 6)). unfold Qdiv. compute. reflexivity. }
  exists eps.
  split.
  - exact Heps_pos.
  - exists (Nat.max 2 (Nat.max N0 (Nat.max N2 N1))).
    intros n Hn.
    assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 (Nat.max N2 N1))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn0 : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 (Nat.max N2 N1)) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 (Nat.max N2 N1))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]).
    assert (Hn2b : (N2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N2 N1) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max N0 (Nat.max N2 N1)) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 (Nat.max N2 N1))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]]).
    assert (Hn1 : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N2 N1) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max N0 (Nat.max N2 N1)) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max N0 (Nat.max N2 N1))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]]]).
    pose proof (HN2 n (NatLe_lift _ _ Hn2b)) as He2.
    pose proof (HN0 n (NatLe_lift _ _ Hn0)) as He0.
    pose proof (HN1 n (NatLe_lift _ _ Hn1)) as He1.
    (* 点态事实：0 ≤ un、eps0 < vn−un、vn ≤ 2、un ≤ vn *)
    assert (Hupos : Qlt eps2 (u n)).
    { apply QltT_to_Qlt in He2.
      assert (Hz : u n - 0 == u n) by ring.
      rewrite Hz in He2. exact He2. }
    assert (Hu0 : Qle 0 (u n)) by (apply (Qlt_le_weak 0 (u n)); apply (Qlt_trans _ eps2 _); [apply QltT_to_Qlt; exact Heps2 | exact Hupos]).
    assert (Hd0 : Qlt eps0 (v n - u n)).
    { apply QltT_to_Qlt in He0. exact He0. }
    assert (Hd0le : Qle eps0 (v n - u n)) by (apply (Qlt_le_weak eps0 (v n - u n)); exact Hd0).
    assert (Hd0pos : Qlt 0 (v n - u n)) by (apply (Qlt_trans _ eps0 _); [exact Heps0Q | exact Hd0]).
    assert (Hv2m : Qlt (v n) (2 - eps1)).
    { apply (proj2 (Qlt_minus_iff (v n) (2 - eps1))).
      assert (Hd : (2 - eps1) - v n == (2 - v n) - eps1) by ring.
      rewrite Hd.
      apply (proj1 (Qlt_minus_iff eps1 (2 - v n))).
      exact (QltT_to_Qlt eps1 (2 - v n) He1). }
    assert (Hv2 : Qle (v n) 2).
    { apply (Qlt_le_weak (v n) 2).
      apply (Qlt_le_trans _ (2 - eps1) _); [exact Hv2m | ].
      apply (Qlt_le_weak (2 - eps1) 2).
      apply (proj2 (Qlt_minus_iff (2 - eps1) 2)).
      assert (Hr : 2 - (2 - eps1) == eps1) by ring.
      rewrite Hr. exact (QltT_to_Qlt 0 eps1 Heps1). }
    assert (Huv : Qle (u n) (v n)).
    { apply (Qlt_le_weak (u n) (v n)).
      apply (Qlt_le_trans _ (v n - eps0) _).
      - apply (proj2 (Qlt_minus_iff (u n) (v n - eps0))).
        assert (Hr : (v n - eps0) - u n == (v n - u n) - eps0) by ring.
        rewrite Hr.
        apply (proj1 (Qlt_minus_iff eps0 (v n - u n))). exact Hd0.
      - apply (proj2 (Qle_minus_iff (v n - eps0) (v n))).
        assert (Hr : v n - (v n - eps0) == eps0) by ring.
        rewrite Hr. apply (Qlt_le_weak 0 eps0). exact Heps0Q. }
    (* 主界（Q 层主引理，n ≥ 2）：
       cos_partial n (v n) ≤ cos_partial n (u n) − ((v n)²−(u n)²)/6 *)
    assert (Hmain := sc_cos_partial_diff_le n (u n) (v n) Hu0 Huv Hv2 Hn2).
    (* (v n)² − (u n)² > eps0²（差积分解 + 双因子下界） *)
    assert (Hq2 : q_pow eps0 2 == eps0 * eps0) by (unfold q_pow; simpl; ring).
    assert (Hsq : Qlt (q_pow eps0 2) ((v n) * (v n) - (u n) * (u n))).
    { rewrite Hq2.
      assert (Hprod : (v n - u n) * (v n + u n) == (v n) * (v n) - (u n) * (u n)) by ring.
      rewrite <- Hprod.
      (* 0 ≤ un + un（0 ≤ un 两跳：Qle_trans + Qle_minus_iff + ring） *)
      assert (Hun2 : Qle 0 (u n + u n)).
      { apply (Qle_trans _ (u n) _); [exact Hu0 | ].
        apply (proj2 (Qle_minus_iff (u n) (u n + u n))).
        assert (Hr : u n + u n - u n == u n) by ring.
        rewrite Hr. exact Hu0. }
      (* vn − un ≤ vn + un ⟺ 0 ≤ (vn+un) − (vn−un) == un + un *)
      assert (Hge : Qle (v n - u n) (v n + u n)).
      { apply (proj2 (Qle_minus_iff (v n - u n) (v n + u n))).
        assert (Hr : (v n + u n) - (v n - u n) == u n + u n) by ring.
        rewrite Hr. exact Hun2. }
      (* 0 < vn + un、eps0 < vn + un（经 vn − un 中转） *)
      assert (Hsu : Qlt 0 (v n + u n)).
      { apply (Qlt_le_trans 0 (v n - u n) (v n + u n)); [exact Hd0pos | exact Hge]. }
      assert (Hesu : Qlt eps0 (v n + u n)).
      { apply (Qlt_le_trans eps0 (v n - u n) (v n + u n)); [exact Hd0 | exact Hge]. }
      (* eps0² < eps0·(vn+un) < (vn−un)·(vn+un) *)
      apply (Qlt_trans _ (eps0 * (v n + u n)) _).
      - apply QltT_to_Qlt. apply (sc_qmul_lt_l eps0 eps0 (v n + u n)); [exact Heps0Q | exact Hesu].
      - apply (Qmult_lt_compat_r eps0 (v n - u n) (v n + u n)); [exact Hsu | exact Hd0]. }
    (* eps < cos_partial n (u n) − cos_partial n (v n)：
       Q 层主界（右端 ≥ (vn²−un²)/6）接 Hsq 放大 *)
    assert (Hgt : Qlt eps (cos_partial n (u n) - cos_partial n (v n))).
    { apply (Qlt_le_trans _ (((v n) * (v n) - (u n) * (u n)) * (1 / 6)) _).
      - unfold eps.
        apply (Qmult_lt_compat_r (q_pow eps0 2) ((v n) * (v n) - (u n) * (u n)) (1 / 6)).
        + change (Qlt 0 (1 / 6)). unfold Qdiv. compute. reflexivity.
        + exact Hsq.
      - apply (proj2 (Qle_minus_iff (((v n) * (v n) - (u n) * (u n)) * (1 / 6))
                    (cos_partial n (u n) - cos_partial n (v n)))).
        assert (Hr : (cos_partial n (u n) - cos_partial n (v n)) -
                     ((v n) * (v n) - (u n) * (u n)) * (1 / 6) ==
                     (cos_partial n (u n) - ((v n) * (v n) - (u n) * (u n)) * (1 / 6)) -
                     cos_partial n (v n)) by ring.
        rewrite Hr.
        apply (proj1 (Qle_minus_iff (cos_partial n (v n))
                      (cos_partial n (u n) - ((v n) * (v n) - (u n) * (u n)) * (1 / 6)))).
        apply QleT'_to_Qle. exact Hmain. }
    (* 目标：QltT eps (cos_partial n (u n) − cos_partial n (v n))（投影已定义性归约） *)
    apply Qlt_to_QltT.
    exact Hgt.
Qed.

(* ============================================================ *)
(* SC-1 批 19d-1（轮 24）：cos 零点二分·测试机械               *)
(*   cos 在 (3/2, 5/3) 变号 → 副本 log 论证 Chunk 5 approx_root *)
(*   测试（目标 real_zero 精确，r 侧恒 0 简化）：cos_testA       *)
(*   （cos m < 0）/cos_testB（0 < cos m）/双假缺陷              *)
(*   （|cos m| ≤ 3·d4 == 3eps/16）——cos 零点 π/2 二分论证地基   *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* cos 点模量（副本 exp_partial_cauchy；经 sc_cos_partial_cauchy_bounded + 平凡界 |x| ≤ |x|） *)
Lemma cos_partial_cauchy : forall (x : Q) (eps : Q), Qlt 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT (Qabs (cos_partial m x - cos_partial n x)) eps).
Proof.
  intros x eps Hep.
  destruct (sc_cos_partial_cauchy_bounded (Qabs x) eps (Qle_to_QleT' _ _ (Qabs_nonneg x)) (Qlt_to_QltT _ _ Hep)) as [N HN].
  exists N.
  intros m n Hm Hn.
  apply (HN m n Hm Hn x). apply Qle_to_QleT'. apply Qle_refl.
Qed.

(* 测试常量（d4 := eps/16 常数；K1 := cos 在 m 的模量点；q := cos_partial K1 m ≈ cos m 误差 < d4） *)
Definition cos_K1_eps (m : Q) (eps : Q) (Heps : Qlt 0 eps) : nat :=
  projT1 (cos_partial_cauchy m (eps / 16) (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps)))).
Definition cos_q_eps (m : Q) (eps : Q) (Heps : Qlt 0 eps) : Q :=
  cos_partial (cos_K1_eps m eps Heps) m.

(* 决定测试（目标 0 精确）：cos m < 0（A）/ 0 < cos m（B）/ 双假 ⟹ |cos m| ≤ 3·d4 缺陷 *)
Definition cos_testA_eps (m : Q) (eps : Q) (Heps : Qlt 0 eps) : bool :=
  let d4 := eps / 16 in
  let K1 := projT1 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps)))) in
  Qlt_bool (cos_partial K1 m + 2 * d4) 0.

Definition cos_testB_eps (m : Q) (eps : Q) (Heps : Qlt 0 eps) : bool :=
  let d4 := eps / 16 in
  let K1 := projT1 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps)))) in
  Qlt_bool (2 * d4) (cos_partial K1 m).

(* 决策 A 真 ⟹ cos m < 0：见证 0 − q − 2d4 == −q − 2d4 *)
Lemma cos_testA_eps_true_lt : forall (m : Q) (eps : Q) (Heps : Qlt 0 eps),
  cos_testA_eps m eps Heps = true ->
  real_lt (cauchy_real_cos (real_const m)) real_zero.
Proof.
  intros m eps Heps HA.
  unfold cos_testA_eps in HA.
  cbn in HA.
  pose (d4 := eps / 16).
  pose (K1 := projT1 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps))))).
  pose (q := cos_partial K1 m).
  assert (Hlt : Qlt (q + 2 * d4) 0).
  { apply QltT_to_Qlt.
    apply RealSetoid.eq_Id.
    exact HA. }
  assert (Hd0 : Qlt 0 d4) by (unfold d4; apply QltT_to_Qlt; apply q_eps16_pos; exact (Qlt_to_QltT _ _ Heps)).
  assert (Heps4 : QltT 0 (- q - 2 * d4)).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (0 + - (q + 2 * d4)) _).
    - apply (proj1 (Qlt_minus_iff (q + 2 * d4) 0)). exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  exists (- q - 2 * d4).
  split.
  - exact Heps4.
  - exists K1.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hem : Qlt (Qabs (projT1 (cauchy_real_cos (real_const m)) n - q)) d4).
    { apply QltT_to_Qlt.
      cbn [projT1].
      apply (projT2 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps)))) n K1).
      - exact Hn.
      - apply NatLe_lift. apply Nat.le_refl. }
    assert (Hr0 : Qlt (Qabs (projT1 real_zero n - 0)) d4).
    { assert (Hz : Qabs (projT1 real_zero n - 0) == Qabs 0).
      { apply Qabs_wd. change (0 - 0 == 0). ring. }
      assert (Hz2 : Qabs 0 == 0) by reflexivity.
      rewrite Hz, Hz2. exact Hd0. }
    apply (Qle_lt_trans _ ((0 - d4) - (q + d4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_lt_compat (0 - d4) (projT1 real_zero n)
                             (Qopp (q + d4)) (Qopp (projT1 (cauchy_real_cos (real_const m)) n))).
      * apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 real_zero n) 0 d4). apply Qlt_to_QltT. exact Hr0.
      * apply (Qopp_lt_compat (projT1 (cauchy_real_cos (real_const m)) n) (q + d4)).
        apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 (cauchy_real_cos (real_const m)) n) q d4). apply Qlt_to_QltT. exact Hem.
Qed.

(* 决策 B 真 ⟹ 0 < cos m：见证 q − 0 − 2d4 == q − 2d4 *)
Lemma cos_testB_eps_true_gt : forall (m : Q) (eps : Q) (Heps : Qlt 0 eps),
  cos_testB_eps m eps Heps = true ->
  real_lt real_zero (cauchy_real_cos (real_const m)).
Proof.
  intros m eps Heps HB.
  unfold cos_testB_eps in HB.
  cbn in HB.
  pose (d4 := eps / 16).
  pose (K1 := projT1 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps))))).
  pose (q := cos_partial K1 m).
  assert (Hlt : Qlt (2 * d4) q).
  { apply QltT_to_Qlt.
    apply RealSetoid.eq_Id.
    exact HB. }
  assert (Hd0 : Qlt 0 d4) by (unfold d4; apply QltT_to_Qlt; apply q_eps16_pos; exact (Qlt_to_QltT _ _ Heps)).
  assert (Heps4 : QltT 0 (q - 0 - 2 * d4)).
  { apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (q + - (2 * d4)) _).
    - apply (proj1 (Qlt_minus_iff (2 * d4) q)). exact Hlt.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  exists (q - 0 - 2 * d4).
  split.
  - exact Heps4.
  - exists K1.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hem : Qlt (Qabs (projT1 (cauchy_real_cos (real_const m)) n - q)) d4).
    { apply QltT_to_Qlt.
      cbn [projT1].
      apply (projT2 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps)))) n K1).
      - exact Hn.
      - apply NatLe_lift. apply Nat.le_refl. }
    assert (Hr0 : Qlt (Qabs (projT1 real_zero n - 0)) d4).
    { assert (Hz : Qabs (projT1 real_zero n - 0) == Qabs 0).
      { apply Qabs_wd. change (0 - 0 == 0). ring. }
      assert (Hz2 : Qabs 0 == 0) by reflexivity.
      rewrite Hz, Hz2. exact Hd0. }
    apply (Qle_lt_trans _ ((q - d4) - (0 + d4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qplus_lt_compat (q - d4) (projT1 (cauchy_real_cos (real_const m)) n)
                             (Qopp (0 + d4)) (Qopp (projT1 real_zero n))).
      * apply QltT_to_Qlt. apply (q_abs_lt_minus (projT1 (cauchy_real_cos (real_const m)) n) q d4). apply Qlt_to_QltT. exact Hem.
      * apply (Qopp_lt_compat (projT1 real_zero n) (0 + d4)).
        apply QltT_to_Qlt. apply (q_abs_lt_lower (projT1 real_zero n) 0 d4). apply Qlt_to_QltT. exact Hr0.
Qed.

(* 双假 ⟹ |cos m − 0| ≤ 3·d4（逐点，k ≥ K1；目标 0 精确故无 4·d4 的 r 侧项） *)
Lemma cos_test_mid_bound : forall (m : Q) (eps : Q) (Heps : Qlt 0 eps),
  cos_testA_eps m eps Heps = false -> cos_testB_eps m eps Heps = false ->
  forall n : nat, (cos_K1_eps m eps Heps <= n)%nat ->
    QleT' (Qabs (projT1 (cauchy_real_cos (real_const m)) n - projT1 real_zero n))
        (3 * (eps / 16)).
Proof.
  intros m eps Heps HA HB n Hn.
  apply Qle_to_QleT'.
  unfold cos_testA_eps in HA. unfold cos_testB_eps in HB. cbn in HA, HB.
  pose (d4 := eps / 16).
  pose (K1 := projT1 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps))))).
  pose (q := cos_partial K1 m).
  change (Qlt_bool (q + 2 * d4) 0 = false) in HA.
  change (Qlt_bool (2 * d4) q = false) in HB.
  pose (HnA := qlt_bool_false_not (q + 2 * d4) 0 HA).
  pose (HnB := qlt_bool_false_not (2 * d4) q HB).
  assert (Hqle : Qle q (2 * d4)) by (apply Qnot_lt_le; intro Hl; exact (match HnB (Qlt_to_QltT _ _ Hl) with end)).
  assert (Hql : Qle (- q) (2 * d4)).
  { apply (proj2 (Qle_minus_iff (- q) (2 * d4))).
    assert (Hc : 2 * d4 - - q == q + 2 * d4) by ring.
    rewrite Hc.
    apply Qnot_lt_le. intro Hl. exact (match HnA (Qlt_to_QltT _ _ Hl) with end). }
  assert (Hqr : Qle (Qabs q) (2 * d4)).
  { apply (proj2 (Qabs_Qle_condition q (2 * d4))).
    split.
    - apply (proj2 (Qle_minus_iff (- (2 * d4)) q)).
      assert (Hc : q - - (2 * d4) == q + 2 * d4) by ring.
      rewrite Hc.
      apply Qnot_lt_le. intro Hl. exact (match HnA (Qlt_to_QltT _ _ Hl) with end).
    - exact Hqle. }
  assert (Hem : Qlt (Qabs (projT1 (cauchy_real_cos (real_const m)) n - q)) d4).
  { apply QltT_to_Qlt.
    cbn [projT1].
    apply (projT2 (cos_partial_cauchy m d4 (QltT_to_Qlt _ _ (q_eps16_pos eps (Qlt_to_QltT _ _ Heps)))) n K1).
    - apply NatLe_lift. apply (Nat.le_trans _ (cos_K1_eps m eps Heps) _); [apply Nat.le_refl | exact Hn].
    - apply NatLe_lift. apply Nat.le_refl. }
  apply (Qle_trans _ (Qabs (projT1 (cauchy_real_cos (real_const m)) n - q) + Qabs q) _).
  - assert (Hsum : projT1 (cauchy_real_cos (real_const m)) n - projT1 real_zero n ==
                   (projT1 (cauchy_real_cos (real_const m)) n - q) + q).
    { change (projT1 (cauchy_real_cos (real_const m)) n - 0 ==
              (projT1 (cauchy_real_cos (real_const m)) n - q) + q).
      ring. }
    apply (Qle_trans _ (Qabs ((projT1 (cauchy_real_cos (real_const m)) n - q) + q)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. exact Hsum.
    + apply Qabs_triangle.
  - apply (Qle_trans _ (d4 + 2 * d4) _).
    + apply (Qplus_le_compat (Qabs (projT1 (cauchy_real_cos (real_const m)) n - q))
                             d4 (Qabs q) (2 * d4)).
      * apply Qlt_le_weak. exact Hem.
      * exact Hqr.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold d4. ring.
Qed.

(* ============================================================ *)
(* SC-1 批 19d-2（轮 24）：cos_scan 扫描 + 正确性               *)
(*   cos 递减（批 19c）故分支与 log_scan（exp 递增）相反：       *)
(*   A（cos m < 0）真 → 零点在 (a, m)；B（0 < cos m）真 → (m, b) *)
(*   双假 → 冻结分支（中点缺陷 |cos m| ≤ 3·d4 之退化情形）       *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* 扫描 Fixpoint：A 真（cos m < 0）→ 左半 (a,m)；B 真（0 < cos m）→ 右半 (m,b)；
   双假 → 冻结（返回当前区间 + false）——cos 严格递减故与 log_scan 分支相反 *)
Fixpoint cos_scan (a b : Q) (Hab : Qlt a b) (eps : Q) (Heps : Qlt 0 eps) (n : nat) :
  (sigT (fun ab : Q * Q => QltT (fst ab) (snd ab))) * bool :=
  match n with
  | O => (existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) (Qlt_to_QltT a b Hab), true)
  | Datatypes.S n' =>
      let m := log_m_eps a b in
      if cos_testA_eps m eps Heps then
        cos_scan a m (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT a b Hab))) eps Heps n'
      else if cos_testB_eps m eps Heps then
        cos_scan m b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT a b Hab))) eps Heps n'
      else (existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) (Qlt_to_QltT a b Hab), false)
  end.

(* 单步归约等式：S 步 = if A then 左半 else if B then 右半 else 冻结 *)
Lemma cos_scan_S : forall (a b : Q) (Hab : Qlt a b) (eps : Q) (Heps : Qlt 0 eps) (n : nat),
  cos_scan a b Hab eps Heps (Datatypes.S n) =
  (if cos_testA_eps (log_m_eps a b) eps Heps then
     cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT a b Hab))) eps Heps n
   else if cos_testB_eps (log_m_eps a b) eps Heps then
     cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT a b Hab))) eps Heps n
   else (existT (fun ab : Q * Q => QltT (fst ab) (snd ab)) (a, b) (Qlt_to_QltT a b Hab), false)).
Proof. intros. reflexivity. Qed.

(* 扫描正确性：true ⟹ 区间夹逼 0（cos a > 0 ∧ cos b < 0）且长度 == (b−a)·(1/2)^n；
   false ⟹ 冻结区间中点 |cos m − 0| ≤ 3·d4（缺陷直达） *)
Lemma cos_scan_spec : forall (a b : Q) (Hab : Qlt a b) (eps : Q) (Heps : Qlt 0 eps) (n : nat),
  real_lt real_zero (cauchy_real_cos (real_const a)) ->
  real_lt (cauchy_real_cos (real_const b)) real_zero ->
  Or
    (And (Id (snd (cos_scan a b Hab eps Heps n)) true)
         (And (real_lt real_zero (cauchy_real_cos (real_const (fst (projT1 (fst (cos_scan a b Hab eps Heps n)))))))
              (And (real_lt (cauchy_real_cos (real_const (snd (projT1 (fst (cos_scan a b Hab eps Heps n)))))) real_zero)
                   (QeqT (snd (projT1 (fst (cos_scan a b Hab eps Heps n))) - fst (projT1 (fst (cos_scan a b Hab eps Heps n))))
                         ((b - a) * q_pow (1 / 2) n)))))
    (And (Id (snd (cos_scan a b Hab eps Heps n)) false)
         (forall k : nat,
           NatLe (cos_K1_eps (log_m_eps (fst (projT1 (fst (cos_scan a b Hab eps Heps n))))
                                   (snd (projT1 (fst (cos_scan a b Hab eps Heps n))))) eps Heps) k ->
            QleT' (Qabs (projT1 (cauchy_real_cos (real_const
              (log_m_eps (fst (projT1 (fst (cos_scan a b Hab eps Heps n))))
                         (snd (projT1 (fst (cos_scan a b Hab eps Heps n))))))) k - projT1 real_zero k))
                (3 * log_d4_eps eps))).
Proof.
  intros a b Hab eps Heps n.
  revert a b Hab eps Heps.
  induction n as [| n IH]; intros a b Hab eps Heps Hla Hrb.
  - left. simpl. split; [reflexivity | ].
    split; [exact Hla | ].
    split; [exact Hrb | ].
    apply qeq_imp_qeqT. simpl. ring.
  - destruct (cos_testA_eps (log_m_eps a b) eps Heps) eqn:EA.
    + rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA.
      assert (Hmb : real_lt (cauchy_real_cos (real_const (log_m_eps a b))) real_zero)
        by (apply (cos_testA_eps_true_lt (log_m_eps a b) eps Heps); exact EA).
      assert (HIH : Or
        (And (Id (snd (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n)) true)
             (And (real_lt real_zero (cauchy_real_cos (real_const (fst (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n)))))))
                  (And (real_lt (cauchy_real_cos (real_const (snd (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n)))))) real_zero)
                       (QeqT (snd (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n))) -
                         fst (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))
                         ((log_m_eps a b - a) * q_pow (1 / 2) n)))))
        (And (Id (snd (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n)) false)
             (forall k : nat,
               NatLe (cos_K1_eps (log_m_eps (fst (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))
                                       (snd (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))) eps Heps) k ->
                QleT' (Qabs (projT1 (cauchy_real_cos (real_const
                  (log_m_eps (fst (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))
                             (snd (projT1 (fst (cos_scan a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))))) k - projT1 real_zero k))
                    (3 * log_d4_eps eps))))
        by (apply (IH a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps); [exact Hla | exact Hmb]).
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
          { unfold log_m_eps. apply qeqT_imp_qeq. apply log_step_len_am. exact (Qlt_to_QltT _ _ Hab). }
          rewrite Ha.
          unfold Qdiv.
          cbn [q_pow].
          ring. } }
      { right. exact Hdef. }
    + destruct (cos_testB_eps (log_m_eps a b) eps Heps) eqn:EB.
      * rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA. rewrite EB.
        assert (Ham : real_lt real_zero (cauchy_real_cos (real_const (log_m_eps a b))))
          by (apply (cos_testB_eps_true_gt (log_m_eps a b) eps Heps); exact EB).
        assert (HIH : Or
          (And (Id (snd (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n)) true)
               (And (real_lt real_zero (cauchy_real_cos (real_const (fst (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n)))))))
                    (And (real_lt (cauchy_real_cos (real_const (snd (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n)))))) real_zero)
                         (QeqT (snd (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n))) -
                           fst (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))
                           ((b - log_m_eps a b) * q_pow (1 / 2) n)))))
          (And (Id (snd (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n)) false)
               (forall k : nat,
                 NatLe (cos_K1_eps (log_m_eps (fst (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))
                                         (snd (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))) eps Heps) k ->
                  QleT' (Qabs (projT1 (cauchy_real_cos (real_const
                    (log_m_eps (fst (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))
                               (snd (projT1 (fst (cos_scan (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps n))))))) k - projT1 real_zero k))
                      (3 * log_d4_eps eps))))
          by (apply (IH (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps); [exact Ham | exact Hrb]).
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
            { unfold log_m_eps. apply qeqT_imp_qeq. apply log_step_len_mb. exact (Qlt_to_QltT _ _ Hab). }
            rewrite Hb.
            unfold Qdiv.
            cbn [q_pow].
            ring. } }
        { right. exact Hdef. }
      * rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA. rewrite EB.
        right. split; [reflexivity | ].
        intros k Hk.
        apply Qle_to_QleT'.
        apply QleT'_to_Qle. apply (cos_test_mid_bound (log_m_eps a b) eps Heps); [exact EA | exact EB | exact (NatLe_drop _ _ Hk)].
Qed.

(* 嵌套：扫描区间始终 ⊆ [a, b] *)
Lemma cos_scan_nested : forall (a b : Q) (Hab : Qlt a b) (eps : Q) (Heps : Qlt 0 eps) (n : nat),
  And (QleT' a (fst (projT1 (fst (cos_scan a b Hab eps Heps n)))))
      (QleT' (snd (projT1 (fst (cos_scan a b Hab eps Heps n)))) b).
Proof.
  intros a b Hab eps Heps n.
  revert a b Hab eps Heps.
  induction n as [| n IH]; intros a b Hab eps Heps.
  - simpl. split; apply Qle_to_QleT'; apply Qle_refl.
  - destruct (cos_testA_eps (log_m_eps a b) eps Heps) eqn:EA.
    + destruct (IH a (log_m_eps a b) (QltT_to_Qlt _ _ (log_a_lt_mid a b (Qlt_to_QltT _ _ Hab))) eps Heps) as [H1 H2].
      split.
      * rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA. exact H1.
      * apply Qle_to_QleT'.
        apply (Qle_trans _ (log_m_eps a b) _).
        -- rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA.
           apply QleT'_to_Qle in H2. exact H2.
        -- apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply log_mid_lt_b. exact (Qlt_to_QltT _ _ Hab).
    + destruct (cos_testB_eps (log_m_eps a b) eps Heps) eqn:EB.
      * destruct (IH (log_m_eps a b) b (QltT_to_Qlt _ _ (log_mid_lt_b a b (Qlt_to_QltT _ _ Hab))) eps Heps) as [H1 H2].
        split.
        -- apply Qle_to_QleT'.
           apply (Qle_trans _ (log_m_eps a b) _).
           ++ apply (Qlt_le_weak _ _). apply QltT_to_Qlt. apply log_a_lt_mid. exact (Qlt_to_QltT _ _ Hab).
           ++ rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA. rewrite EB.
              apply QleT'_to_Qle in H1. exact H1.
        -- rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA. rewrite EB. exact H2.
      * rewrite (cos_scan_S a b Hab eps Heps n). rewrite EA. rewrite EB.
        simpl. split; apply Qle_to_QleT'; apply Qle_refl.
Qed.

(* ============================================================ *)
(* SC-1 批 19d-3（轮 24）：cos 跨度界 + approx_root_cos         *)
(*   cos_span_lipschitz（Q 层 cos 部分和跨段 Lipschitz）         *)
(*   + approx_span_pt_cos（全判定终点中点逐点界：cos 严格递减    *)
(*     夹逼 cos b < cos m < cos a，批 19c）                      *)
(*   + approx_root_cos：∀eps ∃x ∈ (3/2, 5/3) |cos x − 0| < eps  *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* Q 层 cos 部分和跨段 Lipschitz：a ≤ b、|a|,|b| ≤ B、exp_series ≤ C
   ⟹ |cos_partial n b − cos_partial n a| ≤ (b−a)·C（n = 0 恒 1 分支） *)
Lemma cos_span_lipschitz : forall (a b B C : Q) (n : nat),
  Qle a b -> Qle 0 B -> Qle (Qabs a) B -> Qle (Qabs b) B ->
  (forall n : nat, QleT' (exp_series n B) C) ->
  QleT' (Qabs (projT1 (cauchy_real_cos (real_const b)) n - projT1 (cauchy_real_cos (real_const a)) n))
      ((b - a) * C).
Proof.
  intros a b B C n Hab HB Ha Hb HC.
  destruct n as [| m].
  - apply Qle_to_QleT'. (* n = 0：cos_partial 0 == 1 两侧 ⟹ 差 0 *)
    change (Qle (Qabs (cos_partial 0 b - cos_partial 0 a)) ((b - a) * C)).
    assert (Hba : cos_partial 0 b == 1) by (apply qeqT_imp_qeq; apply sc_cos_partial_zero_const).
    assert (Haa : cos_partial 0 a == 1) by (apply qeqT_imp_qeq; apply sc_cos_partial_zero_const).
    rewrite Hba, Haa.
    assert (Hz : Qabs (1 - 1) == 0).
    { assert (H1 : 1 - 1 == 0) by ring.
      rewrite H1. reflexivity. }
    rewrite Hz.
    assert (Hbma : Qle 0 (b - a)).
    { apply (proj1 (Qle_minus_iff a b)). exact Hab. }
    assert (HC0 : Qle 0 C).
    { apply (Qle_trans _ 1 _); [change (Qle 0 1); unfold Qle; simpl; lia | ].
      apply QleT'_to_Qle. apply (HC 0%nat). }
    apply (Qmult_le_0_compat (b - a) C); [exact Hbma | exact HC0].
  - apply Qle_to_QleT'. (* n = S m：sc_cos_partial_lipschitz_succ + SDS ≤ exp_series ≤ C *)
    change (Qle (Qabs (cos_partial (Datatypes.S m) b - cos_partial (Datatypes.S m) a)) ((b - a) * C)).
    apply (Qle_trans _ (Qmult (Qabs (b - a)) C) _).
    + apply (Qle_trans _ (Qmult (Qabs (b - a)) (sc_sin_deriv_series m B)) _).
      * apply QleT'_to_Qle. apply (sc_cos_partial_lipschitz_succ b a B m (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ Hb) (Qle_to_QleT' _ _ Ha)).
      * apply (Qmult_le_compat_nonneg (Qabs (b - a)) (Qabs (b - a)) (sc_sin_deriv_series m B) C).
        -- split; [apply Qabs_nonneg | apply Qle_refl].
        -- split.
           ++ apply QleT'_to_Qle. apply sc_sin_deriv_series_nonneg. apply Qle_to_QleT'. exact HB.
           ++ apply (Qle_trans _ (exp_series (Datatypes.S (2 * m)) B) _).
              ** apply QleT'_to_Qle. apply sc_sin_deriv_series_le_exp. apply Qle_to_QleT'. exact HB.
              ** apply QleT'_to_Qle. apply (HC (Datatypes.S (2 * m))).
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      assert (Hbma : Qabs (b - a) == b - a).
      { apply Qabs_pos. apply (proj1 (Qle_minus_iff a b)). exact Hab. }
      rewrite Hbma. reflexivity.
Qed.

(* 全判定核心：a<b、cos a > 0 > cos b、0 < a、b < 2（cos 严格递减定义域）
   ⟹ ∃N0, ∀k≥N0, |cos m_k − 0_k| ≤ (b−a)·C（逐点；cos m ∈ (cos b, cos a) 夹逼） *)
Lemma approx_span_pt_cos : forall (a b : Q) (HaNbN : Qlt a b) (B C : Q)
  (Hla : real_lt real_zero (cauchy_real_cos (real_const a)))
  (Hrb : real_lt (cauchy_real_cos (real_const b)) real_zero),
  Qle 0 B -> Qle (Qabs a) B -> Qle (Qabs b) B ->
  (forall n : nat, QleT' (exp_series n B) C) ->
  real_lt real_zero (real_const a) ->
  real_lt (real_const b) (real_const 2) ->
  sigT (fun N0 : nat => forall k : nat, (N0 <= k)%nat ->
    QleT' (Qabs (projT1 (cauchy_real_cos (real_const (log_m_eps a b))) k - projT1 real_zero k))
        ((b - a) * C)).
Proof.
  intros a b HaNbN B C Hla Hrb HB HaB HbB HC Hpos Hlt2.
  set (m := log_m_eps a b).
  destruct (log_mid_strict a b (Qlt_to_QltT _ _ HaNbN)) as [Ham Hmb].
  apply QltT_to_Qlt in Ham. apply QltT_to_Qlt in Hmb.
  (* cos m < cos a（严格递减 (a,m)）；cos b < cos m（严格递减 (m,b)） *)
  assert (Hm2 : real_lt (real_const (log_m_eps a b)) (real_const 2)).
  { apply (real_lt_trans (real_const (log_m_eps a b)) (real_const b) (real_const 2)).
    - apply real_const_lt. exact (Qlt_to_QltT _ _ Hmb).
    - exact Hlt2. }
  assert (Hcm : real_lt (cauchy_real_cos (real_const (log_m_eps a b)))
                        (cauchy_real_cos (real_const a))).
  { unfold m. apply (real_cos_strict_decr (real_const a) (real_const (log_m_eps a b))).
    - exact Hpos.
    - apply real_const_lt. exact (Qlt_to_QltT _ _ Ham).
    - exact Hm2. }
  assert (H0m : real_lt real_zero (real_const (log_m_eps a b))).
  { unfold m. apply (real_lt_trans real_zero (real_const a) (real_const (log_m_eps a b))).
    - exact Hpos.
    - apply real_const_lt. exact (Qlt_to_QltT _ _ Ham). }
  assert (Hcb : real_lt (cauchy_real_cos (real_const b))
                        (cauchy_real_cos (real_const (log_m_eps a b)))).
  { unfold m. apply (real_cos_strict_decr (real_const (log_m_eps a b)) (real_const b)).
    - exact H0m.
    - apply real_const_lt. exact (Qlt_to_QltT _ _ Hmb).
    - exact Hlt2. }
  destruct (real_lt_pt_lt real_zero (cauchy_real_cos (real_const a)) Hla) as [N1 HN1].
  destruct (real_lt_pt_lt (cauchy_real_cos (real_const b)) real_zero Hrb) as [N2 HN2].
  destruct (real_lt_pt_lt (cauchy_real_cos (real_const (log_m_eps a b))) (cauchy_real_cos (real_const a)) Hcm) as [N3 HN3].
  destruct (real_lt_pt_lt (cauchy_real_cos (real_const b)) (cauchy_real_cos (real_const (log_m_eps a b))) Hcb) as [N4 HN4].
  exists (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)).
  intros k Hk.
  assert (Hk12 : (Nat.max N1 N2 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)) _); [apply Nat.le_max_l | exact Hk]).
  assert (Hk34 : (Nat.max N3 N4 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)) _); [apply Nat.le_max_r | exact Hk]).
  assert (Hk1 : (N1 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_l | exact Hk12]).
  assert (Hk2 : (N2 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_r | exact Hk12]).
  assert (Hk3 : (N3 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N3 N4) _); [apply Nat.le_max_l | exact Hk34]).
  assert (Hk4 : (N4 <= k)%nat) by (apply (Nat.le_trans _ (Nat.max N3 N4) _); [apply Nat.le_max_r | exact Hk34]).
  set (ca := projT1 (cauchy_real_cos (real_const a)) k).
  set (cb := projT1 (cauchy_real_cos (real_const b)) k).
  set (cm := projT1 (cauchy_real_cos (real_const (log_m_eps a b))) k).
  set (zk := projT1 real_zero k).
  assert (Hcbca : Qlt cb ca).
  { apply (Qlt_trans cb cm ca).
    - exact (QltT_to_Qlt _ _ (HN4 k (NatLe_lift _ _ Hk4))).
    - exact (QltT_to_Qlt _ _ (HN3 k (NatLe_lift _ _ Hk3))). }
  assert (Hspan : Qle (Qabs (cm - zk)) (ca - cb)).
  { apply QleT'_to_Qle. apply (q_abs_le_span cb ca cm zk).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). exact (QltT_to_Qlt _ _ (HN4 k (NatLe_lift _ _ Hk4))).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). exact (QltT_to_Qlt _ _ (HN3 k (NatLe_lift _ _ Hk3))).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). exact (QltT_to_Qlt _ _ (HN2 k (NatLe_lift _ _ Hk2))).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _). exact (QltT_to_Qlt _ _ (HN1 k (NatLe_lift _ _ Hk1))). }
  assert (Hspan2 : Qle (ca - cb) ((b - a) * C)).
  { apply (Qle_trans _ (Qabs (ca - cb)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos.
      apply (proj1 (Qle_minus_iff cb ca)). apply (Qlt_le_weak _ _). exact Hcbca.
    - rewrite (Qabs_Qminus ca cb).
      apply QleT'_to_Qle. apply (cos_span_lipschitz a b B C k (Qlt_le_weak a b HaNbN) HB HaB HbB HC). }
  apply Qle_to_QleT'.
  apply (Qle_trans _ (ca - cb) _).
  - exact Hspan.
  - exact Hspan2.
Qed.

(* cos 版逐点提升：|cos m_k − 0_k| ≤ M（k ≥ N0）⟹ real_lt |cos m − 0| (real_const (M+γ)) *)
Lemma cos_abs_lift : forall (m : Q) (M γ : Q) (N0 : nat),
  Qlt 0 γ ->
  (forall k : nat, (N0 <= k)%nat -> Qle (Qabs (projT1 (cauchy_real_cos (real_const m)) k - projT1 real_zero k)) M) ->
  real_lt (real_abs (real_plus (cauchy_real_cos (real_const m)) (real_opp real_zero)))
          (real_const (M + γ)).
Proof.  intros m M γ N0 Hγ Hpt.
  exact (real_abs_diff_le_lift (cauchy_real_cos (real_const m)) real_zero M γ N0 Hγ Hpt).
Qed.

(* 缺陷分支：逐点 |cos m_k − 0_k| ≤ 3·d4（k ≥ N0）⟹ real_lt |cos m − 0| (real_const eps)
   （3·d4 == 3eps/16 < eps） *)
Lemma approx_def_test_cos : forall (mN : Q) (eps : Q) (Heps : Qlt 0 eps) (N0 : nat),
  (forall k : nat, (N0 <= k)%nat ->
     Qle (Qabs (projT1 (cauchy_real_cos (real_const mN)) k - projT1 real_zero k)) (3 * log_d4_eps eps)) ->
  real_lt (real_abs (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero))) (real_const eps).
Proof.
  intros mN eps Heps N0 Hpt.
  assert (Hγ4 : Qlt 0 (eps / 4)).
  { apply (Qlt_shift_div_l 0 eps 4).
    - change (Qlt 0 4). compute. reflexivity.
    - simpl. exact Heps. }
  assert (Hlift : real_lt (real_abs (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero)))
                          (real_const (3 * log_d4_eps eps + eps / 4))).
  { apply (cos_abs_lift mN (3 * log_d4_eps eps) (eps / 4) N0 Hγ4).
    intros k Hk. apply (Hpt k). exact Hk. }
  apply (real_lt_trans (real_abs (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero)))
                       (real_const (3 * log_d4_eps eps + eps / 4))
                       (real_const eps)).
  - exact Hlift.
  - apply real_const_lt. apply Qlt_to_QltT.
    apply (proj2 (Qlt_minus_iff (3 * log_d4_eps eps + eps / 4) eps)).
    apply (Qlt_le_trans 0 ((9 / 16) * eps) (eps - (3 * log_d4_eps eps + eps / 4))).
    + apply (Qmult_lt_0_compat (9 / 16) eps).
      * change (Qlt 0 (9 / 16)). unfold Qdiv. compute. reflexivity.
      * exact Heps.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold log_d4_eps. field.
Qed.

(* 主定理：approx_root_cos——∀eps>0, ∃x:Q（3/2 < x < 5/3）|cos x − 0| < eps
   （cos 于 (3/2, 5/3) 变号的构造性近似根：全判定 → 夹逼+跨度界；缺陷 → 直达） *)
Lemma approx_root_cos : forall (eps : Q) (Heps : Qlt 0 eps),
  sigT (fun x : Q => And (QltT (3 / 2) x)
                    (And (QltT x (5 / 3))
                         (real_lt (real_abs (real_plus (cauchy_real_cos (real_const x)) (real_opp real_zero))) (real_const eps)))).
Proof.
  intros eps Heps.
  set (a0 := 3 / 2).
  set (b0 := 5 / 3).
  assert (Ha0b0 : Qlt a0 b0).
  { unfold a0, b0. change (Qlt (3 / 2) (5 / 3)). unfold Qdiv. compute. reflexivity. }
  assert (Ha0_y : real_lt real_zero (cauchy_real_cos (real_const a0))).
  { unfold a0. exact real_cos_three_halves_pos. }
  assert (Hy_b0 : real_lt (cauchy_real_cos (real_const b0)) real_zero).
  { unfold b0. exact real_cos_five_thirds_neg. }
  set (B := Qabs a0 + Qabs b0).
  assert (HB : Qle 0 B).
  { unfold B. apply (Qplus_le_compat 0 (Qabs a0) 0 (Qabs b0)); apply Qabs_nonneg. }
  assert (Ha0B : Qle (Qabs a0) B) by (unfold B; apply QleT'_to_Qle; apply q_abs_sum_bound).
  assert (Hb0B : Qle (Qabs b0) B) by (unfold B; apply QleT'_to_Qle; apply q_abs_sum_bound_r).
  destruct (exp_series_arch B (Qle_to_QleT' _ _ HB)) as [C [HC1 HC]].
  set (D := (b0 - a0) * C).
  assert (HD : Qle 0 D).
  { unfold D. apply Qmult_le_0_compat.
    - apply QleT'_to_Qle. apply (q_le_minus a0 b0). apply Qle_to_QleT'. apply (Qlt_le_weak a0 b0). exact Ha0b0.
    - apply (Qle_trans _ 1 _); [change (Qle 0 1); unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]. }
  destruct (q_pow_arch D eps (Qle_to_QleT' _ _ HD) (Qlt_to_QltT _ _ Heps)) as [N HN].
  destruct (cos_scan_spec a0 b0 Ha0b0 eps Heps N Ha0_y Hy_b0) as [Hfull | Hdef].
  - destruct Hfull as [Hfl [HlaN [HrbN Hlen]]].
    set (abN := projT1 (fst (cos_scan a0 b0 Ha0b0 eps Heps N))).
    set (aN := fst abN).
    set (bN := snd abN).
    set (mN := log_m_eps aN bN).
    assert (HaNbN : Qlt aN bN) by (unfold aN, bN, abN; exact (QltT_to_Qlt _ _ (projT2 (fst (cos_scan a0 b0 Ha0b0 eps Heps N))))).
    destruct (cos_scan_nested a0 b0 Ha0b0 eps Heps N) as [Ha0aN HbN_b0].
    apply QleT'_to_Qle in Ha0aN. apply QleT'_to_Qle in HbN_b0.
    assert (HaNb0 : Qle aN b0).
    { apply (Qle_trans _ bN _).
      - apply (Qlt_le_weak _ _). exact HaNbN.
      - exact HbN_b0. }
    assert (HaN_B : Qle (Qabs aN) B).
    { unfold B. apply QleT'_to_Qle. apply (q_interval_abs_bound a0 aN b0).
      - exact (Qle_to_QleT' _ _ Ha0aN).
      - exact (Qle_to_QleT' _ _ HaNb0). }
    assert (HbN_B : Qle (Qabs bN) B).
    { unfold B. apply QleT'_to_Qle. apply (q_interval_abs_bound a0 bN b0).
      - apply Qle_to_QleT'. apply (Qle_trans _ aN _).
        + exact Ha0aN.
        + apply (Qlt_le_weak _ _). exact HaNbN.
      - exact (Qle_to_QleT' _ _ HbN_b0). }
    assert (Hpos_aN : real_lt real_zero (real_const aN)).
    { exists 1.
      split.
      - apply Qlt_to_QltT. change (Qlt 0 1). compute. reflexivity.
      - exists 0%nat.
        intros n Hn.
        apply Qlt_to_QltT.
        assert (Hz : projT1 (real_const aN) n - projT1 real_zero n == aN).
        { cbn [projT1 real_const real_zero]. ring. }
        rewrite Hz.
        apply (Qlt_le_trans 1 (3 / 2) aN).
        + change (Qlt 1 (3 / 2)). unfold Qdiv. compute. reflexivity.
        + exact Ha0aN. }
    assert (Hlt2_bN : real_lt (real_const bN) (real_const 2)).
    { apply real_const_lt. apply Qlt_to_QltT.
      apply (Qle_lt_trans bN (5 / 3) 2).
      - exact HbN_b0.
      - change (Qlt (5 / 3) 2). unfold Qdiv. compute. reflexivity. }
    destruct (approx_span_pt_cos aN bN HaNbN B C HlaN HrbN HB HaN_B HbN_B HC Hpos_aN Hlt2_bN) as [N0 HN0].
    exists mN.
    split.
    + (* 3/2 < mN：a0 ≤ aN < mN *)
      unfold a0, mN.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans (3 / 2) aN (log_m_eps aN bN)).
      * exact Ha0aN.
      * apply (QltT_to_Qlt aN (log_m_eps aN bN) (fst (log_mid_strict aN bN (Qlt_to_QltT _ _ HaNbN)))).
    + split.
      * (* mN < 5/3：mN < bN ≤ b0 *)
        unfold b0, mN.
        apply Qlt_to_QltT.
        apply (Qlt_le_trans (log_m_eps aN bN) bN (5 / 3)).
        -- apply (QltT_to_Qlt (log_m_eps aN bN) bN (snd (log_mid_strict aN bN (Qlt_to_QltT _ _ HaNbN)))).
        -- exact HbN_b0.
      * assert (Hγ : Qlt 0 ((eps - D * q_pow (1 / 2) N) / 2)).
        { apply (Qlt_shift_div_l 0 (eps - D * q_pow (1 / 2) N) 2).
          - change (Qlt 0 2). compute. reflexivity.
          - simpl. apply (proj1 (Qlt_minus_iff (D * q_pow (1 / 2) N) eps)). exact (QltT_to_Qlt _ _ HN). }
        assert (Hlift : real_lt (real_abs (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero)))
                                (real_const ((bN - aN) * C + (eps - D * q_pow (1 / 2) N) / 2))).
        { apply (cos_abs_lift mN ((bN - aN) * C) ((eps - D * q_pow (1 / 2) N) / 2) N0 Hγ).
          intros k Hk. apply QleT'_to_Qle. exact (HN0 k Hk). }
        apply (real_lt_trans (real_abs (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero)))
                             (real_const ((bN - aN) * C + (eps - D * q_pow (1 / 2) N) / 2))
                             (real_const eps)).
        -- exact Hlift.
        -- apply real_const_lt.
           apply (approx_const_lt bN aN D C ((eps - D * q_pow (1 / 2) N) / 2) eps N HN).
           ** unfold aN, bN, abN in Hlen. apply (len_mul_D bN aN b0 a0 C N). exact Hlen.
           ** apply qeq_imp_qeqT. reflexivity.
  - destruct Hdef as [Hdf Hpt].
    set (abN := projT1 (fst (cos_scan a0 b0 Ha0b0 eps Heps N))).
    set (mN := log_m_eps (fst abN) (snd abN)).
    set (N0 := cos_K1_eps (log_m_eps (fst abN) (snd abN)) eps Heps).
    exists mN.
    split.
    + (* 3/2 < mN：a0 ≤ fst abN < mN *)
      unfold a0, mN.
      assert (HabN : Qlt (fst abN) (snd abN)) by (unfold abN; exact (QltT_to_Qlt _ _ (projT2 (fst (cos_scan a0 b0 Ha0b0 eps Heps N))))).
      apply Qlt_to_QltT.
      apply (Qle_lt_trans (3 / 2) (fst abN) (log_m_eps (fst abN) (snd abN))).
      * apply (QleT'_to_Qle a0 (fst abN)).
        exact (fst (cos_scan_nested a0 b0 Ha0b0 eps Heps N)).
      * apply (QltT_to_Qlt (fst abN) (log_m_eps (fst abN) (snd abN)) (fst (log_mid_strict (fst abN) (snd abN) (Qlt_to_QltT _ _ HabN)))).
    + split.
      * (* mN < 5/3：mN < snd abN ≤ b0 *)
        unfold b0, mN.
        assert (HabN' : Qlt (fst abN) (snd abN)) by (unfold abN; exact (QltT_to_Qlt _ _ (projT2 (fst (cos_scan a0 b0 Ha0b0 eps Heps N))))).
        apply Qlt_to_QltT.
        apply (Qlt_le_trans (log_m_eps (fst abN) (snd abN)) (snd abN) (5 / 3)).
        -- apply (QltT_to_Qlt (log_m_eps (fst abN) (snd abN)) (snd abN) (snd (log_mid_strict (fst abN) (snd abN) (Qlt_to_QltT _ _ HabN')))).
        -- apply (QleT'_to_Qle (snd abN) b0).
           exact (snd (cos_scan_nested a0 b0 Ha0b0 eps Heps N)).
      * assert (HptN0 : forall k : nat, (N0 <= k)%nat ->
          Qle (Qabs (projT1 (cauchy_real_cos (real_const mN)) k - projT1 real_zero k)) (3 * log_d4_eps eps)).
        { intros k Hk. unfold mN, N0 in Hpt, Hk. apply QleT'_to_Qle. apply (Hpt k). apply NatLe_lift. exact Hk. }
        apply (approx_def_test_cos mN eps Heps N0). exact HptN0.
Qed.

(* ============================================================ *)
(* SC-1 批 19d-4（轮 24）：cos 零点序列 + 柯西性                *)
(*   z_n := approx_root_cos (log_eps n)（|cos z_n| < log_eps n） *)
(*   柯西：Q 层主引理 sc_cos_partial_diff_le 逆界               *)
(*     （v²−u²)/6 ≤ cos u − cos v ⟹ v − u < 2(du+dv)（免 sin）  *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* cos 零点序列：z_n := approx_root_cos (log_eps n) 的返回值（Q 层） *)
Definition cos_zero_seq (n : nat) : Q :=
  projT1 (approx_root_cos (log_eps n) (QltT_to_Qlt _ _ (log_eps_pos n))).

(* 下界：3/2 < cos_zero_seq n（approx_root_cos 区间界） *)
Lemma cos_zero_lower : forall n : nat, QltT (3 / 2) (cos_zero_seq n).
Proof.
  intros n. apply Qlt_to_QltT. unfold cos_zero_seq.
  destruct (approx_root_cos (log_eps n) (QltT_to_Qlt _ _ (log_eps_pos n))) as [x [Hlow [Hup Hpt]]].
  apply QltT_to_Qlt. exact Hlow.
Qed.

(* 上界：cos_zero_seq n < 5/3 *)
Lemma cos_zero_upper : forall n : nat, QltT (cos_zero_seq n) (5 / 3).
Proof.
  intros n. apply Qlt_to_QltT. unfold cos_zero_seq.
  destruct (approx_root_cos (log_eps n) (QltT_to_Qlt _ _ (log_eps_pos n))) as [x [Hlow [Hup Hpt]]].
  apply QltT_to_Qlt. exact Hup.
Qed.

(* 推论：0 ≤ z_n、z_n ≤ 2（diff-le 前提） *)
Lemma cos_zero_nonneg : forall n : nat, QleT' 0 (cos_zero_seq n).
Proof.
  intros n.
  apply (qleT'_trans 0 (3 / 2) (cos_zero_seq n)).
  - apply Qle_to_QleT'. change (Qle 0 (3 / 2)). unfold Qle, Qdiv. simpl. lia.
  - apply qltT_leT'. apply cos_zero_lower.
Qed.

Lemma cos_zero_le_two : forall n : nat, QleT' (cos_zero_seq n) 2.
Proof.
  intros n.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply (Qle_lt_trans (cos_zero_seq n) (5 / 3) 2).
  - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_upper.
  - change (Qlt (5 / 3) 2). unfold Qdiv. compute. reflexivity.
Qed.

(* 逐点：approx_root_cos 界逐点化 ⟹ ∀k ≥ N_n：|cos z_n_k − 0_k| < log_eps n *)
Lemma cos_root_pt_bound : forall (n : nat),
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    QltT (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) k - projT1 real_zero k))
        (log_eps n)).
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos (log_eps n) (QltT_to_Qlt _ _ (log_eps_pos n))) as [x [Hlow [Hup Hpt]]].
  destruct (real_lt_pt_lt (real_abs (real_plus (cauchy_real_cos (real_const x)) (real_opp real_zero)))
                          (real_const (log_eps n)) Hpt) as [N HN].
  exists N.
  intros k Hk.
  assert (Hp : projT1 (real_abs (real_plus (cauchy_real_cos (real_const x)) (real_opp real_zero))) k ==
                Qabs (projT1 (cauchy_real_cos (real_const x)) k - projT1 real_zero k)).
  { rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (cauchy_real_cos (real_const x)) (real_opp real_zero)) k)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_cos (real_const x)) (real_opp real_zero) k)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_zero k)). reflexivity. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const x)) k - projT1 real_zero k))
                      (projT1 (real_abs (real_plus (cauchy_real_cos (real_const x)) (real_opp real_zero))) k)
                      (log_eps n)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
  - apply (Qlt_le_trans _ (projT1 (real_const (log_eps n)) k) _).
    + apply QltT_to_Qlt. exact (HN k Hk).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (real_const_proj (log_eps n) k)).
Qed.

(* 逐点逆界核心：k ≥ 2、0 ≤ u ≤ v ≤ 2、|cos u_k − 0| < du、|cos v_k − 0| < dv
   ⟹ (v²−u²)/6 < du + dv（Q 层主引理 sc_cos_partial_diff_le 逐点直用） *)
Lemma cos_inv_pt : forall (u v : Q) (k : nat) (du dv : Q),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  QltT ((v * v - u * u) * (1 / 6)) (du + dv).
Proof.
  intros u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv.
  apply Qlt_to_QltT.
  change (Qlt ((v * v - u * u) * (1 / 6))
              (du + dv)).
  assert (Hmain : Qle (cos_partial k v) (cos_partial k u - (v * v - u * u) * (1 / 6))).
  { apply QleT'_to_Qle. apply (sc_cos_partial_diff_le k u v Hu0 Huv Hv2 Hk). }
  (* (v²−u²)/6 ≤ cos u_k − cos v_k *)
  assert (Hd : Qle ((v * v - u * u) * (1 / 6)) (cos_partial k u - cos_partial k v)).
  { apply (proj2 (Qle_minus_iff ((v * v - u * u) * (1 / 6)) (cos_partial k u - cos_partial k v))).
    assert (Hr : (cos_partial k u - cos_partial k v) - (v * v - u * u) * (1 / 6) ==
                 (cos_partial k u - (v * v - u * u) * (1 / 6)) - cos_partial k v) by ring.
    rewrite Hr.
    apply (proj1 (Qle_minus_iff (cos_partial k v)
                                (cos_partial k u - (v * v - u * u) * (1 / 6)))).
    exact Hmain. }
  (* cos u_k − cos v_k ≤ |cos u_k − 0| + |0 − cos v_k| < du + dv *)
  apply (Qle_lt_trans ((v * v - u * u) * (1 / 6))
                      (cos_partial k u - cos_partial k v)
                      (du + dv)).
  - exact Hd.
  - assert (Hzu : Qabs (cos_partial k u - projT1 real_zero k) == Qabs (cos_partial k u)).
    { apply Qabs_wd. cbn [projT1 real_zero]. ring. }
    assert (Hzv : Qabs (cos_partial k v - projT1 real_zero k) == Qabs (cos_partial k v)).
    { apply Qabs_wd. cbn [projT1 real_zero]. ring. }
    apply (Qle_lt_trans (cos_partial k u - cos_partial k v)
                        (Qabs (cos_partial k u - projT1 real_zero k) + Qabs (projT1 real_zero k - cos_partial k v))
                        (du + dv)).
    + apply (Qle_trans _ (Qabs (cos_partial k u - cos_partial k v)) _).
      * apply Qle_Qabs.
      * assert (Hsum : Qabs (cos_partial k u - cos_partial k v) ==
                       Qabs ((cos_partial k u - projT1 real_zero k) + (projT1 real_zero k - cos_partial k v))).
        { apply Qabs_wd. cbn [projT1 real_zero]. ring. }
        apply (Qle_trans _ (Qabs ((cos_partial k u - projT1 real_zero k) +
                                  (projT1 real_zero k - cos_partial k v))) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hsum.
        -- apply Qabs_triangle.
    + apply (Qplus_lt_compat (Qabs (cos_partial k u - projT1 real_zero k))
                             du (Qabs (projT1 real_zero k - cos_partial k v)) dv).
      * exact Hdu.
      * assert (Hdv' : Qlt (Qabs (cos_partial k v - projT1 real_zero k)) dv).
        { apply (Qle_lt_trans (Qabs (cos_partial k v - projT1 real_zero k))
                              (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k))
                              dv).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
            assert (Heq : projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k ==
                          cos_partial k v - projT1 real_zero k).
            { cbn [projT1 cauchy_real_cos real_const real_zero]. ring. }
            apply Qeq_sym. exact Heq.
          - exact Hdv. }
        rewrite (Qabs_Qminus (projT1 real_zero k) (cos_partial k v)). exact Hdv'.
Qed.

(* 逆界（距离形）：3/2 ≤ u ≤ v ≤ 5/3、逐点 |cos u_k − 0| < du、|cos v_k − 0| < dv
   ⟹ v − u < 2·(du + dv)（(v²−u²) == (v−u)(v+u) 且 v+u ≥ 3） *)
Lemma cos_inv_dist : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle (3 / 2) u -> Qle u v -> Qle v (5 / 3) ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  QltT (v - u) (2 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu0 Huv Hv2 Hdu Hdv.
  apply Qlt_to_QltT.
  (* 0 ≤ u、v ≤ 2（cos_inv_pt 前提） *)
  assert (Hu0' : Qle 0 u) by (apply (Qle_trans _ (3 / 2) _); [change (Qle 0 (3 / 2)); unfold Qle, Qdiv; simpl; lia | exact Hu0]).
  assert (Hv2' : Qle v 2) by (apply (Qle_trans _ (5 / 3) _); [exact Hv2 | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia]).
  (* (v²−u²)/6 < du + dv *)
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { apply QltT_to_Qlt. apply (cos_inv_pt u v k du dv Hk Hu0' Huv Hv2' Hdu Hdv). }
  (* v²−u² == (v−u)(v+u) 且 v+u ≥ 3：3(v−u) ≤ v²−u² *)
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (Hvu3 : Qle ((v - u) * 3) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) 3 (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split; [change (Qle 0 3); unfold Qle; simpl; lia | ].
      assert (H3 : Qle 3 (v + u)).
      { apply (Qle_trans _ (3 / 2 + 3 / 2) _).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        - apply (Qplus_le_compat (3 / 2) v (3 / 2) u).
          + apply (Qle_trans _ u _); [exact Hu0 | exact Huv].
          + exact Hu0. }
      exact H3. }
  (* 链：3(v−u) ≤ v²−u² ⟹ (v−u) ≤ (v²−u²)/3；Hq 乘 2 ⟹ (v²−u²)/3 < 2(du+dv) *)
  assert (Hq2 : Qlt (v - u) (2 * (du + dv))).
  { apply (Qle_lt_trans (v - u) ((v * v - u * u) * (1 / 3)) (2 * (du + dv))).
    - (* v−u ≤ (v²−u²)/3：v−u == (v−u)·3·(1/3) ≤ (v²−u²)·(1/3) *)
      apply (Qle_trans _ (((v - u) * 3) * (1 / 3)) _).
      + apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        assert (Hr3 : ((v - u) * 3) * (1 / 3) == v - u) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
        apply Qeq_sym. exact Hr3.
      + apply (Qmult_le_compat_r ((v - u) * 3) (v * v - u * u) (1 / 3)).
        * apply (Qle_trans _ ((v - u) * (v + u)) _).
          -- exact Hvu3.
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hprod.
        * apply (Qlt_le_weak 0 (1 / 3)). change (Qlt 0 (1 / 3)). unfold Qdiv. compute. reflexivity.
    - (* (v²−u²)/3 < 2(du+dv) *)
      assert (Hm : (v * v - u * u) * (1 / 3) == ((v * v - u * u) * (1 / 6)) * 2) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      assert (Hm2 : (du + dv) * 2 == 2 * (du + dv)) by ring.
      apply (Qlt_le_trans ((v * v - u * u) * (1 / 3)) ((du + dv) * 2) (2 * (du + dv))).
      * apply (Qle_lt_trans ((v * v - u * u) * (1 / 3)) (((v * v - u * u) * (1 / 6)) * 2) ((du + dv) * 2)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) 2).
           ++ change (Qlt 0 2). compute. reflexivity.
           ++ exact Hq.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm2. }
  exact Hq2.
Qed.

(* 柯西性：|z_m − z_n| → 0（逆界 cos_inv_dist + log_eps → 0） *)
Lemma cos_seq_cauchy : forall (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT (Qabs (cos_zero_seq m - cos_zero_seq n)) eps).
Proof.
  intros eps Heps.
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact (QltT_to_Qlt _ _ Heps). }
  destruct (q_pow_arch 1 (eps / 8) (qltT_leT' 0 1 qltT_0_1) (Qlt_to_QltT _ _ Heps8)) as [t Ht].
  exists (Datatypes.S t).
  intros m n Hm Hn.
  assert (Heps_m_lt : Qlt (log_eps m) (eps / 8)).
  { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps / 8) t m).
    - exact Ht.
    - exact (NatLe_drop _ _ Hm). }
  assert (Heps_n_lt : Qlt (log_eps n) (eps / 8)).
  { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps / 8) t n).
    - exact Ht.
    - exact (NatLe_drop _ _ Hn). }
  (* 尾链：2·(eps_n + eps_m) < eps（eps_n, eps_m < eps/8） *)
  assert (Htail : Qlt (2 * (log_eps n + log_eps m)) eps).
  { assert (Hcom : 2 * (log_eps n + log_eps m) == (log_eps n + log_eps m) * 2) by ring.
    rewrite Hcom.
    assert (Hsum : Qlt (log_eps n + log_eps m) (eps / 4)).
    { apply (Qlt_le_trans (log_eps n + log_eps m) (eps / 8 + eps / 8) (eps / 4)).
      - apply (Qplus_lt_compat (log_eps n) (eps / 8) (log_eps m) (eps / 8)); [exact Heps_n_lt | exact Heps_m_lt].
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field. }
    apply (Qle_lt_trans ((log_eps n + log_eps m) * 2) ((eps / 4) * 2) eps).
    - apply (Qmult_le_compat_r (log_eps n + log_eps m) (eps / 4) 2).
      + apply Qlt_le_weak. exact Hsum.
      + apply Qlt_le_weak. change (Qlt 0 2). compute. reflexivity.
    - assert (He : (eps / 4) * 2 == eps / 2) by (unfold Qdiv; field).
      apply (Qle_lt_trans ((eps / 4) * 2) (eps / 2) eps).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact He.
      + apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
        apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
        * apply (Qlt_shift_div_l 0 eps 2).
          -- change (Qlt 0 2). compute. reflexivity.
          -- simpl. exact (QltT_to_Qlt _ _ Heps).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field. }
  destruct (Qlt_le_dec (cos_zero_seq n) (cos_zero_seq m)) as [Hnm_lt | Hmn].
  - (* z_n < z_m：u := z_n、v := z_m *)
    destruct (cos_root_pt_bound n) as [Nn HNn].
    destruct (cos_root_pt_bound m) as [Nm HMm].
    set (k0 := Nat.max 2 (Nat.max Nn Nm)).
    assert (Hk0n : (Nn <= k0)%nat) by (unfold k0; apply (Nat.le_trans _ (Nat.max Nn Nm) _); [apply Nat.le_max_l | apply Nat.le_max_r]).
    assert (Hk0m : (Nm <= k0)%nat) by (unfold k0; apply (Nat.le_trans _ (Nat.max Nn Nm) _); [apply Nat.le_max_r | apply Nat.le_max_r]).
    assert (Hd : Qlt (cos_zero_seq m - cos_zero_seq n) (2 * (log_eps n + log_eps m))).
    { apply QltT_to_Qlt. apply (cos_inv_dist (cos_zero_seq n) (cos_zero_seq m) (log_eps n) (log_eps m) k0).
      - unfold k0. apply Nat.le_max_l.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lower.
      - apply Qlt_le_weak. exact Hnm_lt.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_upper.
      - apply QltT_to_Qlt. apply (HNn k0). exact (NatLe_lift _ _ Hk0n).
      - apply QltT_to_Qlt. apply (HMm k0). exact (NatLe_lift _ _ Hk0m). }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (cos_zero_seq m - cos_zero_seq n)) (cos_zero_seq m - cos_zero_seq n) eps).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq n) (cos_zero_seq m))). apply Qlt_le_weak. exact Hnm_lt.
    + apply (Qle_lt_trans (cos_zero_seq m - cos_zero_seq n) (2 * (log_eps n + log_eps m)) eps).
      * apply Qlt_le_weak. exact Hd.
      * exact Htail.
  - (* z_m ≤ z_n：u := z_m、v := z_n（对称） *)
    destruct (cos_root_pt_bound m) as [Nm HMm].
    destruct (cos_root_pt_bound n) as [Nn HNn].
    set (k0 := Nat.max 2 (Nat.max Nm Nn)).
    assert (Hk0m : (Nm <= k0)%nat) by (unfold k0; apply (Nat.le_trans _ (Nat.max Nm Nn) _); [apply Nat.le_max_l | apply Nat.le_max_r]).
    assert (Hk0n : (Nn <= k0)%nat) by (unfold k0; apply (Nat.le_trans _ (Nat.max Nm Nn) _); [apply Nat.le_max_r | apply Nat.le_max_r]).
    assert (Hd : Qlt (cos_zero_seq n - cos_zero_seq m) (2 * (log_eps m + log_eps n))).
    { apply QltT_to_Qlt. apply (cos_inv_dist (cos_zero_seq m) (cos_zero_seq n) (log_eps m) (log_eps n) k0).
      - unfold k0. apply Nat.le_max_l.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lower.
      - exact Hmn.
      - apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_upper.
      - apply QltT_to_Qlt. apply (HMm k0). exact (NatLe_lift _ _ Hk0m).
      - apply QltT_to_Qlt. apply (HNn k0). exact (NatLe_lift _ _ Hk0n). }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (cos_zero_seq m - cos_zero_seq n)) (cos_zero_seq n - cos_zero_seq m) eps).
    + rewrite (Qabs_Qminus (cos_zero_seq m) (cos_zero_seq n)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq m) (cos_zero_seq n))). exact Hmn.
    + apply (Qle_lt_trans (cos_zero_seq n - cos_zero_seq m) (2 * (log_eps m + log_eps n)) eps).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hcom : 2 * (log_eps m + log_eps n) == 2 * (log_eps n + log_eps m)) by ring.
        rewrite Hcom. exact Htail.
Qed.

(* ============================================================ *)
(* SC-1 批 19d-5（轮 24）：cos 零点 π/2 完结                   *)
(*   cos_pi_half : Real（existT cos_seq_cauchyT）               *)
(*   real_cos_pi_half_zero：cos(cos_pi_half) == 0               *)
(*   装配：柯西 + exp-arch Lipschitz + 根逐点界 的 eps 分割      *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* cos 零点（π/2）：z := 柯西序列 cos_zero_seq 的实数值 *)
(* cauchy 前提是 QltT 形：cos_seq_cauchy 的 Qlt 形经 QltT_to_Qlt 包装 *)
Lemma cos_seq_cauchyT : forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT (Qabs (cos_zero_seq m - cos_zero_seq n)) eps).
Proof.
  intros eps HepsT.
  destruct (cos_seq_cauchy eps HepsT) as [N HN].
  exists N. intros m n Hm Hn. exact (HN m n Hm Hn).
Qed.

Definition cos_pi_half : Real :=
  existT _ cos_zero_seq cos_seq_cauchyT.

(* 投影：projT1 cos_pi_half n == z_n *)
Lemma cos_pi_half_proj : forall n : nat, QeqT (projT1 cos_pi_half n) (cos_zero_seq n).
Proof.
  intros n. apply qeq_imp_qeqT. reflexivity.
Qed.

(* |z_n| ≤ 2（Lipschitz 界 B := 2 用） *)
Lemma cos_zero_abs_le_two : forall n : nat, QleT' (Qabs (cos_zero_seq n)) 2.
Proof.
  intros n.
  apply Qle_to_QleT'.
  apply (proj2 (Qabs_Qle_condition (cos_zero_seq n) 2)).
  split.
  - apply (Qle_trans _ 0 _).
    + change (Qle (- 2) 0). unfold Qle; simpl. lia.
    + apply QleT'_to_Qle. apply cos_zero_nonneg.
  - apply QleT'_to_Qle. apply cos_zero_le_two.
Qed.

(* 主定理：cos(cos_pi_half) == 0（逐 eps：柯西 + Lipschitz + 根逐点界） *)
Lemma real_cos_pi_half_zero : real_eq (cauchy_real_cos cos_pi_half) real_zero.
Proof.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  (* C := exp_series_arch 2：Lipschitz 界（|z| ≤ 2） *)
  destruct (exp_series_arch 2 (qltT_leT' 0 2 qltT_0_2)) as [C [HC1 HC]].
  assert (HCpos : Qlt 0 C) by (apply (Qlt_le_trans 0 1 C); [change (Qlt 0 1); compute; reflexivity | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Heps2 : Qlt 0 (eps / 2)).
  { apply (Qlt_shift_div_l 0 eps 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. exact HepsQ. }
  assert (Heps2C : Qlt 0 (eps / (2 * C))).
  { assert (H2C : Qlt 0 (2 * C)).
    { apply Qmult_lt_0_compat; [change (Qlt 0 2); compute; reflexivity | exact HCpos]. }
    unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv (2 * C))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. exact H2C. }
  (* N0 := max（柯西点 Nc）(S t)（t：log_eps (S t) < eps/2）——固定配对点 *)
  destruct (cos_seq_cauchy (eps / (2 * C)) (Qlt_to_QltT _ _ Heps2C)) as [Nc HNc].
  destruct (q_pow_arch 1 (eps / 2) (qltT_leT' 0 1 qltT_0_1) (Qlt_to_QltT _ _ Heps2)) as [t Ht].
  set (N0 := Nat.max Nc (Datatypes.S t)).
  assert (HN0c : (Nc <= N0)%nat) by (unfold N0; apply Nat.le_max_l).
  assert (HN0t : (Datatypes.S t <= N0)%nat) by (unfold N0; apply Nat.le_max_r).
  assert (HepsN0 : Qlt (log_eps N0) (eps / 2)).
  { apply QltT_to_Qlt. apply (log_eps_lt_delta (eps / 2) t N0).
    - exact Ht.
    - exact HN0t. }
  destruct ((cos_root_pt_bound N0)) as [N2 HN2].
  (* 逐点根界：|cos n (z_{N0}) − 0| < log_eps N0（n ≥ N2） *)
  assert (HptN0 : forall n : nat, (N2 <= n)%nat ->
    Qlt (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq N0))) n - projT1 real_zero n)) (log_eps N0)).
  { intros n Hn. apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn)). }
  exists (Nat.max 2 (Nat.max Nc N2)).
  intros n Hn.
  apply NatLe_drop in Hn.
  apply Qlt_to_QltT.
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nc N2)) _); [apply Nat.le_max_l | exact Hn]).
  assert (HnNc : (Nc <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Nc N2) _); [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nc N2)) _); [apply Nat.le_max_r | exact Hn]]).
  assert (HnN2 : (N2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max Nc N2) _); [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nc N2)) _); [apply Nat.le_max_r | exact Hn]]).
  (* 投影归约：projT1 (cos cos_pi_half) n == cos_partial n (z_n) *)
  assert (Hproj : projT1 (cauchy_real_cos cos_pi_half) n == cos_partial n (cos_zero_seq n)).
  { cbn [projT1 cauchy_real_cos cos_pi_half]. reflexivity. }
  rewrite Hproj.
  (* 柯西：|z_n − z_{N0}| < eps/(2C) *)
  assert (Hcauchy : Qlt (Qabs (cos_zero_seq n - cos_zero_seq N0)) (eps / (2 * C))).
  { apply QltT_to_Qlt. apply (HNc n N0 (NatLe_lift _ _ HnNc) (NatLe_lift _ _ HN0c)). }
  (* 三角链 *)
  assert (Hsum : cos_partial n (cos_zero_seq n) - projT1 real_zero n ==
                  (cos_partial n (cos_zero_seq n) - cos_partial n (cos_zero_seq N0)) +
                  (cos_partial n (cos_zero_seq N0) - projT1 real_zero n)) by ring.
  apply (Qle_lt_trans (Qabs (cos_partial n (cos_zero_seq n) - projT1 real_zero n))
                      (Qabs (cos_partial n (cos_zero_seq n) - cos_partial n (cos_zero_seq N0)) +
                       Qabs (cos_partial n (cos_zero_seq N0) - projT1 real_zero n))
                      eps).
  - apply (Qle_trans _ (Qabs ((cos_partial n (cos_zero_seq n) - cos_partial n (cos_zero_seq N0)) +
                              (cos_partial n (cos_zero_seq N0) - projT1 real_zero n))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. exact Hsum.
    + apply Qabs_triangle.
  - apply (Qlt_le_trans _ (eps / 2 + eps / 2) _).
    + apply (Qplus_lt_compat (Qabs (cos_partial n (cos_zero_seq n) - cos_partial n (cos_zero_seq N0)))
                             (eps / 2)
                             (Qabs (cos_partial n (cos_zero_seq N0) - projT1 real_zero n))
                             (eps / 2)).
      * apply (Qle_lt_trans (Qabs (cos_partial n (cos_zero_seq n) - cos_partial n (cos_zero_seq N0)))
                            (Qmult (Qabs (cos_zero_seq n - cos_zero_seq N0)) C)
                            (eps / 2)).
        -- (* Lipschitz：n = S m'、|z| ≤ 2、SDS m' 2 ≤ exp_series ≤ C *)
           destruct n as [| m'].
           ++ exfalso. lia.
           ++ apply (Qle_trans _ (Qmult (Qabs (cos_zero_seq (Datatypes.S m') - cos_zero_seq N0))
                                        (sc_sin_deriv_series m' 2)) _).
              ** apply QleT'_to_Qle. apply (sc_cos_partial_lipschitz_succ (cos_zero_seq (Datatypes.S m')) (cos_zero_seq N0) 2 m').
                 --- apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl. lia.
                 --- apply Qle_to_QleT'. apply QleT'_to_Qle. apply cos_zero_abs_le_two.
                 --- apply Qle_to_QleT'. apply QleT'_to_Qle. apply cos_zero_abs_le_two.
              ** apply (Qmult_le_compat_nonneg (Qabs (cos_zero_seq (Datatypes.S m') - cos_zero_seq N0))
                                               (Qabs (cos_zero_seq (Datatypes.S m') - cos_zero_seq N0))
                                               (sc_sin_deriv_series m' 2) C).
                 --- split; [apply Qabs_nonneg | apply Qle_refl].
                 --- split.
                     +++ apply QleT'_to_Qle. apply sc_sin_deriv_series_nonneg. apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl. lia.
                     +++ apply (Qle_trans _ (exp_series (Datatypes.S (2 * m')) 2) _).
                         *** apply QleT'_to_Qle. apply sc_sin_deriv_series_le_exp. apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl. lia.
                         *** apply QleT'_to_Qle. apply (HC (Datatypes.S (2 * m'))).
        -- (* C·|diff| < eps/2：C·|diff| < C·(eps/(2C)) == eps/2 *)
           apply (Qlt_le_trans (Qmult (Qabs (cos_zero_seq n - cos_zero_seq N0)) C)
                               (C * (eps / (2 * C)))
                               (eps / 2)).
           ++ assert (Hcom : Qabs (cos_zero_seq n - cos_zero_seq N0) * C ==
                             C * Qabs (cos_zero_seq n - cos_zero_seq N0)) by ring.
              rewrite Hcom.
              apply QltT_to_Qlt. apply (sc_qmul_lt_l C (Qabs (cos_zero_seq n - cos_zero_seq N0)) (eps / (2 * C))).
              ** exact HCpos.
              ** apply (Qle_lt_trans (Qabs (cos_zero_seq n - cos_zero_seq N0)) (Qabs (cos_zero_seq N0 - cos_zero_seq n)) (eps / (2 * C))).
                 --- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (Qabs_Qminus (cos_zero_seq n) (cos_zero_seq N0)). reflexivity.
                 --- rewrite (Qabs_Qminus (cos_zero_seq n) (cos_zero_seq N0)) in Hcauchy. exact Hcauchy.
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              assert (He : C * (eps / (2 * C)) == eps / 2).
               { unfold Qdiv. field.
                 all: try (unfold Qeq; simpl; lia).
                 intro Hz.
                 exact (Qlt_not_eq 0 C HCpos (Qeq_sym C 0 Hz)). }
              exact He.
      * apply (Qlt_trans (Qabs (cos_partial n (cos_zero_seq N0) - projT1 real_zero n))
                         (log_eps N0)
                         (eps / 2)).
        -- exact (HptN0 n HnN2).
        -- exact HepsN0.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      assert (He : eps / 2 + eps / 2 == eps) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      exact He.
Qed.
(* 几何 π：π := 2·(cos 零点 cos_pi_half) *)
Definition real_pi_geom : Real := real_mult (real_const 2) cos_pi_half.

(* ============================================================ *)
(* SC-1 批 19e-1（轮 25）：cos 零点唯一性                      *)
(*   cos_pi_half_unique：w ∈ (3/2, 5/3) ∧ cos w == 0            *)
(*     ⟹ real_eq w cos_pi_half                                  *)
(*   逐点逆界装配（cos w==0 与 cos z==0 对角界 + cos_inv_dist）  *)
(*   ——Leibniz π 与几何 π 等同的零点唯一桥                      *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)

(* cos w == 0 的对角逐点界：∀δ ∃N，∀n ≥ N：|cos_partial n (w_n) − 0| < δ *)
Lemma cos_eq_zero_diag_bound : forall (w : Real) (Hw : real_eq (cauchy_real_cos w) real_zero)
  (delta : Q) (Hdelta : Qlt 0 delta),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) delta).
Proof.
  intros w Hw delta Hdelta.
  destruct (Hw delta (Qlt_to_QltT 0 delta Hdelta)) as [N HN].
  exists N.
  intros n Hn.
  apply (HN n (NatLe_lift _ _ Hn)).
Qed.

(* 端点逐点下界：real_const a < w ⟹ 逐点 a < w_n *)
Lemma real_lt_lower_pt : forall (a : Q) (w : Real) (Haw : real_lt (real_const a) w),
  sigT (fun N : nat => forall k : nat, (N <= k)%nat -> Qlt a (projT1 w k)).
Proof.
  intros a w Haw.
  destruct Haw as [eps [Heps [N HN]]].
  exists N.
  intros k Hk.
  apply (Qlt_le_trans a (a + eps) (projT1 w k)).
  - apply (proj2 (Qlt_minus_iff a (a + eps))).
    apply (Qlt_le_trans 0 eps ((a + eps) - a)).
    + apply QltT_to_Qlt. exact Heps.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_le_weak _ _).
    apply (proj2 (Qlt_minus_iff (a + eps) (projT1 w k))).
    apply (Qlt_le_trans 0 (projT1 w k - a - eps) ((projT1 w k) - (a + eps))).
    + apply (proj1 (Qlt_minus_iff eps (projT1 w k - a))).
      apply QltT_to_Qlt. apply (HN k (NatLe_lift _ _ Hk)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 端点逐点上界：w < real_const b ⟹ 逐点 w_n < b *)
Lemma real_lt_upper_pt : forall (b : Q) (w : Real) (Hwb : real_lt w (real_const b)),
  sigT (fun N : nat => forall k : nat, (N <= k)%nat -> Qlt (projT1 w k) b).
Proof.
  intros b w Hwb.
  destruct Hwb as [eps [Heps [N HN]]].
  exists N.
  intros k Hk.
  apply (Qlt_le_trans (projT1 w k) (b - eps) b).
  - apply (proj2 (Qlt_minus_iff (projT1 w k) (b - eps))).
    assert (Hr : (b - eps) - projT1 w k == (b - projT1 w k) - eps) by ring.
    rewrite Hr.
    apply (proj1 (Qlt_minus_iff eps (b - projT1 w k))).
    apply QltT_to_Qlt. apply (HN k (NatLe_lift _ _ Hk)).
  - apply (proj2 (Qle_minus_iff (b - eps) b)).
    assert (Hr : b - (b - eps) == eps) by ring.
    rewrite Hr.
    apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps.
Qed.

(* 主定理：cos 在 (3/2, 5/3) 的零点唯一 == cos_pi_half *)
Lemma cos_pi_half_unique : forall (w : Real),
  real_lt (real_const (3 / 2)) w -> real_lt w (real_const (5 / 3)) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact HepsQ. }
  (* 逐点界来源：w 侧（端点 + cos w == 0 对角）、z 侧（cos_zero_lower/upper + cos z == 0 对角） *)
  destruct (real_lt_lower_pt (3 / 2) w Hlow) as [Nlo HNlo].
  destruct (real_lt_upper_pt (5 / 3) w Hup) as [Nup HNup].
  destruct ((cos_eq_zero_diag_bound w Hw0 (eps / 8) Heps8)) as [Nwd Hwd].
  destruct ((cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero (eps / 8) Heps8)) as [Nzd Hzd].
  destruct (q_pow_arch 1 (eps / 8) (qltT_leT' 0 1 qltT_0_1) (Qlt_to_QltT _ _ Heps8)) as [t Ht].
  set (A := Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))).
  exists (Nat.max 2 (Nat.max A (Datatypes.S t))).
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (HnAt : (Nat.max A (Datatypes.S t) <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (HnA : (A <= n)%nat) by (apply (Nat.le_trans _ (Nat.max A (Datatypes.S t)) _); [apply Nat.le_max_l | exact HnAt]).
  assert (Hnlo : (Nlo <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))) _); [apply Nat.le_max_l | ].
    unfold A in HnA. exact HnA. }
  assert (Hnup : (Nup <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnwd : (Nwd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnzd : (Nzd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  (* w_n ∈ (3/2, 5/3)、z_n ∈ (3/2, 5/3)（Q 层） *)
  assert (Hwlo : Qle (3 / 2) (projT1 w n)) by (apply Qlt_le_weak; apply (HNlo n); exact Hnlo).
  assert (Hwup : Qle (projT1 w n) (5 / 3)) by (apply Qlt_le_weak; apply (HNup n); exact Hnup).
  assert (Hzlo : Qle (3 / 2) (cos_zero_seq n)) by (apply Qlt_le_weak; (apply QltT_to_Qlt; apply cos_zero_lower)).
  assert (Hzup : Qle (cos_zero_seq n) (5 / 3)) by (apply Qlt_le_weak; (apply QltT_to_Qlt; apply cos_zero_upper)).
  (* cos w_n 与 cos z_n 的对角界 < eps/8 *)
  assert (Hwpt : Qlt (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 8)).
  { apply QltT_to_Qlt. apply (Hwd n). exact Hnwd. }
  assert (Hzpt : Qlt (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n)) (eps / 8)).
  { apply QltT_to_Qlt. apply (Hzd n). exact Hnzd. }
  (* 分支：|w_n − z_n| ≤ eps/2 < eps（逆界，u := 小者） *)
  destruct (Qlt_le_dec (cos_zero_seq n) (projT1 w n)) as [Hzw | Hwz].
  - (* z_n < w_n：u := z_n、v := w_n *)
    assert (Hd : Qlt (projT1 w n - cos_zero_seq n) (2 * (eps / 8 + eps / 8))).
    { apply QltT_to_Qlt. apply (cos_inv_dist (cos_zero_seq n) (projT1 w n) (eps / 8) (eps / 8) n).
      - exact Hn2.
      - exact Hzlo.
      - apply Qlt_le_weak. exact Hzw.
      - exact Hwup.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 8)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt.
      - assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
        { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                              (eps / 8)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
            assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
            { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)). rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
            rewrite Hq. reflexivity.
          - exact Hwpt. }
        exact Hwpt'.
    }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (projT1 w n - cos_zero_seq n) eps).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). apply Qlt_le_weak. exact Hzw.
    + apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
        apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
           apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
           ++ apply (Qlt_shift_div_l 0 eps 2).
              ** change (Qlt 0 2). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
  - (* w_n ≤ z_n：u := w_n、v := z_n（对称） *)
    assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
    { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                          (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                          (eps / 8)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
        assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
        { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)). rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
        rewrite Hq. reflexivity.
      - exact Hwpt. }
    assert (Hd : Qlt (cos_zero_seq n - projT1 w n) (2 * (eps / 8 + eps / 8))).
    { apply QltT_to_Qlt. apply (cos_inv_dist (projT1 w n) (cos_zero_seq n) (eps / 8) (eps / 8) n).
      - exact Hn2.
      - exact Hwlo.
      - exact Hwz.
      - exact Hzup.
      - exact Hwpt'.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 8)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt. }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (cos_zero_seq n - projT1 w n) eps).
    + rewrite (Qabs_Qminus (projT1 w n) (cos_zero_seq n)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 w n) (cos_zero_seq n))). exact Hwz.
    + apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
        apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
           apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
           ++ apply (Qlt_shift_div_l 0 eps 2).
              ** change (Qlt 0 2). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
Qed.

(* ============================================================ *)
(* T-π2b：Leibniz π 上界收紧 4 → 10/3（191 追加） *)
(*   目标：real_pi_leibniz_lt_ten_thirds（π_L < 10/3）           *)
(*   意义：与几何 π 同括 (3, 10/3)，为 T-π3（π_geom == π_L）铺路；*)
(*         充实论文 3 数值章节（3 < π_geom < 10/3 ∧ 3 < π_L < 10/3）*)
(*   路线：偶数部分和 E_n := lp_odd n + a_{2n+2} 随 n 递减（      *)
(*         sc_lp_ev_decr），故 ∀n≥2：lp_odd n ≤ E_n ≤ E_2 = S6；  *)
(*         S6 := lp_odd 2 + lp_a 6，4·S6 = 147916/45045 < 10/3    *)
(*         余量 2234/45045 > 1/60。                              *)
(*   纪律：纯构造性 Set 层、NatLe/QltT、零公理面、非平凡实现。    *)
(* ============================================================ *)

(* E_n 的 S6 上界（n ≥ 2）：E_{2+k} ≤ E_2（E 递减链下降至 E_2） *)
Lemma sc_lp_ev_le_s6 : forall n : nat, (2 <= n)%nat ->
  QleT' (lp_odd n + lp_a (2 * n + 2)) (lp_odd 2 + lp_a 6).
Proof.
  induction n as [| n IH]; intros Hn.
  - apply Qle_to_QleT'. exfalso. lia.
  - apply Qle_to_QleT'. destruct n as [| n'].
    + exfalso. lia.
    + destruct n' as [| n''].
      * (* n = 2：E_2 ≤ E_2 *)
        apply Qle_refl.
      * (* n = S (Datatypes.S (Datatypes.S n''))：E_n ≤ E_{S(Datatypes.S n'')} ≤ E_2 *)
        apply (Qle_trans _ (lp_odd (Datatypes.S (Datatypes.S n'')) + lp_a (2 * Datatypes.S (Datatypes.S n'') + 2)) _).
        -- apply QleT'_to_Qle. apply (sc_lp_ev_decr (Datatypes.S (Datatypes.S n''))).
        -- apply QleT'_to_Qle. apply IH. simpl in Hn. lia.
Qed.

(* 全 n 上界：lp_odd n ≤ S6（n≤2 经单调 + 非负尾；n≥2 经 E_n ≤ E_2） *)
Lemma sc_lp_odd_le_s6 : forall n : nat, QleT' (lp_odd n) (lp_odd 2 + lp_a 6).
Proof.
  intro n.
  destruct (Nat.leb 2 n) eqn:E2n.
  - apply Qle_to_QleT'. apply Nat.leb_le in E2n.
    apply (Qle_trans _ (lp_odd n + lp_a (2 * n + 2)) _).
    + apply (Qle_plus_nonneg_r (lp_odd n) (lp_a (2 * n + 2))).
      apply QleT'_to_Qle. apply sc_lpa_nonneg.
    + apply QleT'_to_Qle. apply sc_lp_ev_le_s6. exact E2n.
  - apply Qle_to_QleT'. apply Nat.leb_gt in E2n.
    assert (Hn2 : (n <= 2)%nat) by lia.
    apply (Qle_trans _ (lp_odd 2) _).
    + apply QleT'_to_Qle. apply sc_lp_odd_chain. exact Hn2.
    + apply (Qle_plus_nonneg_r (lp_odd 2) (lp_a 6)).
      apply QleT'_to_Qle. apply sc_lpa_nonneg.
Qed.

(* 具体比较：4·S6 == 147916/45045（S6 := lp_odd 2 + lp_a 6） *)
Lemma sc_lp_six_value : QeqT (lp_four * (lp_odd 2 + lp_a 6)) (147916 / 45045).
Proof.
  apply qeq_imp_qeqT.
  unfold lp_four, lp_odd, lp_pair, lp_a.
  unfold Qeq. simpl. lia.
Qed.

(* 余量：1/60 < 10/3 − 4·S6（10/3 − 147916/45045 == 2234/45045 > 1/60） *)
Lemma sc_lp_six_margin : QltT (1 / 60) ((10 / 3) - lp_four * (lp_odd 2 + lp_a 6)).
Proof.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (sc_lp_six_value)).
  unfold Qlt. simpl. lia.
Qed.

(* Real 层：π_L < 10/3（余量链：π_n ≤ 4·S6 < 10/3 − 1/60，n ≥ 2） *)
Lemma real_pi_leibniz_lt_ten_thirds : real_lt cauchy_real_pi_leibniz (real_const (10 / 3)).
Proof.
  unfold real_lt.
  exists (1 / 60).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 2%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ ((10 / 3) - lp_four * (lp_odd 2 + lp_a 6)) _).
    + exact (QltT_to_Qlt _ _ (sc_lp_six_margin)).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat.
        setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
        setoid_replace (lp_four * (lp_odd 2 + lp_a 6)) with ((lp_odd 2 + lp_a 6) * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd n) (lp_odd 2 + lp_a 6) lp_four).
        -- apply QleT'_to_Qle. apply sc_lp_odd_le_s6.
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
Qed.

(* 上界合取（供论文/下游引用）：3 < π_L < 10/3 *)
Lemma real_pi_leibniz_between_tenthirds :
  And (real_lt (real_const 3) cauchy_real_pi_leibniz)
      (real_lt cauchy_real_pi_leibniz (real_const (10 / 3))).
Proof.
  split. - exact real_pi_leibniz_gt_three. - exact real_pi_leibniz_lt_ten_thirds.
Qed.

(* ============================================================ *)
(* SC-2 批 1（并入 192）：sin(π/2)==1 及配套（与 191 批 T-π2b 并行并入）*)
(* ============================================================ *)

(* ---- 1a Q 层：0 ≤ q ⟹ |q−1| ≤ |q²−1|（正平方根==1 桥的 Q 内核） ---- *)
Lemma sc_q_abs_minus_one_le_sq : forall q : Q, Qle 0 q ->
  QleT' (Qabs (q - 1)) (Qabs (q * q - 1)).
Proof.
  intros q Hq0.
  apply Qle_to_QleT'.
  (* q² − 1 == (q−1)·(q+1) *)
  assert (Hring : q * q - 1 == (q - 1) * (q + 1)) by ring.
  rewrite Hring.
  (* |(q−1)(q+1)| == |q−1|·|q+1|（Qabs_Qmult） *)
  rewrite Qabs_Qmult.
  (* q ≥ 0 ⟹ q+1 ≥ 1 ≥ 0 ⟹ |q+1| == q+1 *)
  assert (Hq1 : Qle 1 (q + 1)).
  { apply (proj2 (Qle_minus_iff 1 (q + 1))).
    setoid_replace (q + 1 + - 1) with q by ring.
    exact Hq0. }
  assert (Hq10 : Qle 0 (q + 1)) by (apply (Qle_trans _ 1 _); [change (Qle 0 1); apply Qlt_le_weak; change (Qlt 0 1); compute; reflexivity | exact Hq1]).
  rewrite (Qabs_pos (q + 1) Hq10).
  (* |q−1| == |q−1|·1 ≤ |q−1|·(q+1)（1 ≤ q+1，乘 |q−1| ≥ 0） *)
  apply (Qle_trans _ (Qabs (q - 1) * 1) _).
  - rewrite (Qmult_1_r (Qabs (q - 1))). apply Qle_refl.
  - apply (Qmult_le_compat_nonneg (Qabs (q - 1)) (Qabs (q - 1)) 1 (q + 1)).
    + split; [apply Qabs_nonneg | apply Qle_refl].
    + split; [change (Qle 0 1); apply Qlt_le_weak; change (Qlt 0 1); compute; reflexivity | exact Hq1].
Qed.

(* ---- 1b：cos_pi_half 的 Real 层界（点态 cos_zero_lower/upper 提升，N=0） ---- *)
(* 0 < π/2：z_n > 3/2 > 1 点态 ∀n（eps := 1，N := 0） *)
Lemma real_lt_zero_cos_pi_half : real_lt real_zero cos_pi_half.
Proof.
  unfold real_lt.
  exists 1.
  split.
  - apply Qlt_to_QltT. change (Qlt 0 1). compute. reflexivity.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 cos_pi_half real_zero].
    apply Qlt_to_QltT.
    setoid_replace (cos_zero_seq n - 0) with (cos_zero_seq n) by ring.
    apply (Qlt_trans 1 (3 / 2) (cos_zero_seq n)).
    + change (Qlt 1 (3 / 2)). compute. reflexivity.
    + exact (QltT_to_Qlt _ _ (cos_zero_lower n)).
Qed.

(* π/2 < 2：z_n < 5/3 == 2 − 1/3 点态 ∀n（eps := 1/3，N := 0） *)
Lemma real_lt_cos_pi_half_two : real_lt cos_pi_half (real_const 2).
Proof.
  unfold real_lt.
  exists (1 / 3).
  split.
  - apply Qlt_to_QltT. change (Qlt 0 (1 / 3)). compute. reflexivity.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 cos_pi_half].
    apply Qlt_to_QltT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)).
    (* 目标：Qlt (1/3) (2 − z_n) ⟺ z_n < 2 − 1/3 == 5/3（cos_zero_upper） *)
    apply (proj2 (Qlt_minus_iff (1 / 3) (2 - cos_zero_seq n))).
    assert (Heq : (2 - cos_zero_seq n) + - (1 / 3) == (5 / 3) - cos_zero_seq n).
    { unfold Qminus. field. }
    rewrite Heq.
    apply (proj1 (Qlt_minus_iff (cos_zero_seq n) (5 / 3))).
    exact (QltT_to_Qlt _ _ (cos_zero_upper n)).
Qed.

(* ---- 1c：sin(π/2) > 0（real_sin_pos_lt_two 于 X := cos_pi_half） ---- *)
Lemma real_sin_pi_half_pos : real_lt real_zero (cauchy_real_sin cos_pi_half).
Proof.  exact (real_sin_pos_lt_two cos_pi_half real_lt_zero_cos_pi_half
    real_lt_cos_pi_half_two).
Qed.

(* ---- 1d：正平方根 == 1 桥：x² == 1 ∧ 0 < x ⟹ x == 1 ---- *)
Lemma real_sq_eq_one_pos : forall x : Real,
  real_eq (real_mult x x) real_one -> real_lt real_zero x -> real_eq x real_one.
Proof.
  intros x Hsq Hpos.
  unfold real_eq.
  intros eps Heps.
  destruct Hpos as [m [Hmpos [N0 HN0]]].
  destruct (Hsq eps Heps) as [N1 HN1].
  exists (Nat.max N0 N1).
  intros n Hn.
  assert (Hn0nat : (N0 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (Hn1nat : (N1 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max N0 N1) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (Hn0 : NatLe N0 n) by (apply NatLe_lift; exact Hn0nat).
  assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; exact Hn1nat).
  apply Qlt_to_QltT.
  assert (Hm0q : Qlt 0 m) by (apply QltT_to_Qlt; exact Hmpos).
  (* 点态正性：m < x_n（N0 起），故 0 ≤ x_n *)
  assert (Hxn : Qlt m (projT1 x n)).
  { assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hlt : Qlt m (projT1 x n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HN0 n Hn0). }
    rewrite Hz in Hlt.
    assert (Heq : projT1 x n - 0 == projT1 x n) by (unfold Qminus; ring).
    rewrite Heq in Hlt. exact Hlt. }
  assert (Hxn0 : Qle 0 (projT1 x n)).
  { apply Qlt_le_weak. apply (Qlt_trans _ m _); [exact Hm0q | exact Hxn]. }
  (* |x_n − 1| ≤ |x_n² − 1|（Q 层，1a 内核） *)
  assert (Hq : Qle (Qabs (projT1 x n - 1)) (Qabs (projT1 x n * projT1 x n - 1))).
  { apply QleT'_to_Qle. apply (sc_q_abs_minus_one_le_sq (projT1 x n)). exact Hxn0. }
  (* |x_n² − 1| < eps（N1 起，real_eq (x·x) real_one 的点态） *)
  assert (Hsqn : Qlt (Qabs (projT1 (real_mult x x) n - projT1 real_one n)) eps).
  { apply QltT_to_Qlt. exact (HN1 n Hn1). }
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)) in Hsqn.
  assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
  rewrite Ho in Hsqn.
  apply (Qle_lt_trans _ (Qabs (projT1 x n * projT1 x n - 1)) _).
  - exact Hq.
  - exact Hsqn.
Qed.

(* ---- 1e：主定理 sin(π/2) == 1 ---- *)
Lemma real_sin_pi_half_one : real_eq (cauchy_real_sin cos_pi_half) real_one.
Proof.
  (* X := cos_pi_half；s := sin X；c := cos X *)
  set (X := cos_pi_half).
  (* Pythagorean at X：cos²X + sin²X == 1 *)
  pose proof (real_cos_sq_plus_sin_sq_one X) as Hpyth.
  (* cos X == 0（X := cos_pi_half） *)
  assert (Hc0 : real_eq (cauchy_real_cos X) real_zero).
  { subst X. exact real_cos_pi_half_zero. }
  (* cos²X == real_zero == 0（real_mult_zero real_zero + compat） *)
  assert (Hc2 : real_eq (real_mult (cauchy_real_cos X) (cauchy_real_cos X)) real_zero).
  { apply (real_eq_trans _ (real_mult real_zero real_zero) _).
    - apply (RealSetoid.real_eq_mult_compat (cauchy_real_cos X) (cauchy_real_cos X) real_zero real_zero Hc0 Hc0).
    - apply real_mult_zero. }
  (* 链：sin²X == 0 + sin²X == cos²X + sin²X == 1（cos²X == 0） *)
  assert (Hs2 : real_eq (real_mult (cauchy_real_sin X) (cauchy_real_sin X)) real_one).
  { apply (real_eq_trans _ (real_plus real_zero (real_mult (cauchy_real_sin X) (cauchy_real_sin X))) _).
    - (* sin²X == real_zero + sin²X：left-zero（comm + real_plus_zero 反向） *)
      apply real_eq_sym.
      apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_sin X)) real_zero) _).
      + apply (real_plus_comm real_zero (real_mult (cauchy_real_sin X) (cauchy_real_sin X))).
      + apply real_plus_zero.
    - (* real_zero + sin²X == cos²X + sin²X == 1 *)
      apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                                       (real_mult (cauchy_real_sin X) (cauchy_real_sin X))) _).
      + apply real_eq_sym.
        apply (RealSetoid.real_eq_plus_compat (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                                              (real_mult (cauchy_real_sin X) (cauchy_real_sin X))
                                              real_zero
                                              (real_mult (cauchy_real_sin X) (cauchy_real_sin X))).
        * exact Hc2.
        * apply real_eq_refl.
      + exact Hpyth. }
  (* sin X == 1：sin²X == 1 ∧ 0 < sin X *)
  apply (real_sq_eq_one_pos (cauchy_real_sin X)).
  - exact Hs2.
  - subst X. exact real_sin_pi_half_pos.
Qed.

(* ============================================================ *)
(* SC-2 批 2（并入 193）：T-π2 real_pi_geom_between          *)
(* ============================================================ *)

(* ---------- 通用：0 < c → a < c·b → a/c < b ---------- *)
Lemma sc_qdiv_lt_rcancel : forall (a c b : Q), Qlt 0 c -> Qlt a (c * b) -> QltT (a / c) b.
Proof.
  intros a c b Hc Hab.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (a / c) b)).
  assert (Hm : b - a / c == (c * b - a) / c) by (unfold Qdiv; field; intro Hz; exact (Qlt_not_eq 0 c Hc (Qeq_sym c 0 Hz))).
  rewrite Hm.
  apply (Qlt_shift_div_l 0 (c * b - a) c).
  - exact Hc.
  - rewrite (Qmult_0_l c). apply (proj1 (Qlt_minus_iff a (c * b))). exact Hab.
Qed.

(* ---------- A1：a > 1/20 ∧ b < 1/80 ⟹ 3/80 < a − b ---------- *)
Lemma sc_q_gap_pos : forall (a b : Q),
  Qlt (1 / 20) a -> Qlt b (1 / 80) ->
  QltT (3 / 80) (a - b).
Proof.
  intros a b Ha Hb.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (3 / 80) (a - b))).
  assert (H3 : 3 / 80 == 1 / 20 - 1 / 80) by (unfold Qeq; simpl; lia).
  assert (Hm : a - b + - (3 / 80) == (a - 1 / 20) + (1 / 80 - b)).
  { rewrite H3. ring. }
  rewrite Hm.
  apply (Qlt_le_trans 0 ((a - 1 / 20) + (1 / 80 - b)) _).
  - apply (Qplus_lt_compat 0 (a - 1 / 20) 0 (1 / 80 - b)).
    + apply (proj1 (Qlt_minus_iff (1 / 20) a)). exact Ha.
    + apply (proj1 (Qlt_minus_iff b (1 / 80))). exact Hb.
  - apply Qle_refl.
Qed.

(* ---------- A2：|3/2| ≤ 2 ---------- *)
Lemma sc_q_abs_three_halves_le_two_T : QleT' (Qabs (3 / 2)) 2.
Proof.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (3 / 2) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_pos (3 / 2)). unfold Qle; simpl; lia.
  - unfold Qle; simpl; lia.
Qed.

(* ---------- A3：Lipschitz（k := S m）|cos(3/2)_k − cos(z)_k| ≤ |3/2 − z|·C ---------- *)
Lemma sc_cos_partial_lip_arch : forall (C : Q) (m : nat) (z : Q),
  (forall mm : nat, QleT' (exp_series mm 2) C) ->
  QleT' (Qabs z) 2 ->
  QleT' (Qabs (cos_partial (Datatypes.S m) (3 / 2) - cos_partial (Datatypes.S m) z))
      (Qabs (3 / 2 - z) * C).
Proof.
  intros C m z HC Hz.
  apply Qle_to_QleT'.
  assert (Hl : Qle (Qabs (cos_partial (Datatypes.S m) (3 / 2) - cos_partial (Datatypes.S m) z))
                   (Qabs (3 / 2 - z) * sc_sin_deriv_series m 2)).
  { apply QleT'_to_Qle. apply (sc_cos_partial_lipschitz_succ (3 / 2) z 2 m).
    - apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl; lia.
    - exact sc_q_abs_three_halves_le_two_T.
    - exact Hz. }
  apply (Qle_trans _ (Qabs (3 / 2 - z) * sc_sin_deriv_series m 2) _).
  - exact Hl.
  - assert (Hle : Qle (sc_sin_deriv_series m 2) C).
    { apply (Qle_trans _ (exp_series (Datatypes.S (2 * m)) 2) _).
      - apply QleT'_to_Qle. apply (sc_sin_deriv_series_le_exp m 2). apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl; lia.
      - apply QleT'_to_Qle. apply HC. }
    setoid_rewrite (Qmult_comm (Qabs (3 / 2 - z)) (sc_sin_deriv_series m 2)).
    setoid_rewrite (Qmult_comm (Qabs (3 / 2 - z)) C).
    apply (Qmult_le_compat_r (sc_sin_deriv_series m 2) C (Qabs (3 / 2 - z))).
    + exact Hle.
    + apply Qabs_nonneg.
Qed.

(* ---------- A3b：Lipschitz（k := S m）|cos(z)_k − cos(5/3)_k| ≤ |z − 5/3|·C ---------- *)
Lemma sc_cos_partial_lip_arch53 : forall (C : Q) (m : nat) (z : Q),
  (forall mm : nat, QleT' (exp_series mm 2) C) ->
  QleT' (Qabs z) 2 ->
  QleT' (Qabs (cos_partial (Datatypes.S m) z - cos_partial (Datatypes.S m) (5 / 3)))
      (Qabs (z - 5 / 3) * C).
Proof.
  intros C m z HC Hz.
  apply Qle_to_QleT'.
  assert (H53T : QleT' (Qabs (5 / 3)) 2).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (5 / 3) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_pos (5 / 3)). unfold Qle; simpl; lia.
    - unfold Qle; simpl; lia. }
  assert (Hl : Qle (Qabs (cos_partial (Datatypes.S m) z - cos_partial (Datatypes.S m) (5 / 3)))
                   (Qabs (z - 5 / 3) * sc_sin_deriv_series m 2)).
  { apply QleT'_to_Qle. apply (sc_cos_partial_lipschitz_succ z (5 / 3) 2 m).
    - apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl; lia.
    - exact Hz.
    - exact H53T. }
  apply (Qle_trans _ (Qabs (z - 5 / 3) * sc_sin_deriv_series m 2) _).
  - exact Hl.
  - assert (Hle : Qle (sc_sin_deriv_series m 2) C).
    { apply (Qle_trans _ (exp_series (Datatypes.S (2 * m)) 2) _).
      - apply QleT'_to_Qle. apply (sc_sin_deriv_series_le_exp m 2). apply Qle_to_QleT'. change (Qle 0 2). unfold Qle; simpl; lia.
      - apply QleT'_to_Qle. apply HC. }
    setoid_rewrite (Qmult_comm (Qabs (z - 5 / 3)) (sc_sin_deriv_series m 2)).
    setoid_rewrite (Qmult_comm (Qabs (z - 5 / 3)) C).
    apply (Qmult_le_compat_r (sc_sin_deriv_series m 2) C (Qabs (z - 5 / 3))).
    + exact Hle.
    + apply Qabs_nonneg.
Qed.

(* ---------- B：Q 层逐点严格下界（单指标 k 形态） ----------
   k ≥ 4（cos(3/2)_k > 1/20）、|z| ≤ 2、log_eps n < 1/80、
   |cos_partial k z − 0| < log_eps n、3/2 < z
   ⟹ (3/80)/C < z − 3/2                                     *)
Lemma sc_cos_zero_lower_margin_gen : forall (C : Q) (n k : nat) (z : Q),
  (4 <= k)%nat ->
  QleT' 1 C ->
  (forall mm : nat, QleT' (exp_series mm 2) C) ->
  Qlt (log_eps n) (1 / 80) ->
  QleT' (Qabs z) 2 ->
  Qlt (Qabs (cos_partial k z - 0)) (log_eps n) ->
  Qlt (3 / 2) z ->
  QltT ((3 / 80) / C) (z - 3 / 2).
Proof.
  intros C n k z Hk4 HC1 HC Hlog Hz Hroot H32z.
  apply Qlt_to_QltT.
  destruct k as [|[|k'']]; [lia | lia |].
  assert (Hc32 : Qlt (1 / 20) (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2)))
    by (apply QltT_to_Qlt; apply sc_cos_partial_ge4_pos_3h; lia).
  (* cos_partial z < log_eps n：|x−0|<e ⟹ x<e *)
  assert (Hczlog : Qlt (cos_partial (Datatypes.S (Datatypes.S k'')) z) (log_eps n)).
  { setoid_replace (cos_partial (Datatypes.S (Datatypes.S k'')) z - 0)
                   with (cos_partial (Datatypes.S (Datatypes.S k'')) z) in Hroot by ring.
    assert (Hc : Qlt (- log_eps n) (cos_partial (Datatypes.S (Datatypes.S k'')) z) /\
                Qlt (cos_partial (Datatypes.S (Datatypes.S k'')) z) (log_eps n))
      by (apply (proj1 (Qabs_Qlt_condition (cos_partial (Datatypes.S (Datatypes.S k'')) z) (log_eps n))); exact Hroot).
    exact (proj2 Hc). }
  assert (Hcz : Qlt (cos_partial (Datatypes.S (Datatypes.S k'')) z) (1 / 80))
    by (apply (Qlt_trans _ (log_eps n) _); [exact Hczlog | exact Hlog]).
  assert (Hgap : Qlt (3 / 80)
                       (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2) - cos_partial (Datatypes.S (Datatypes.S k'')) z))
    by (apply QltT_to_Qlt; apply sc_q_gap_pos; [exact Hc32 | exact Hcz]).
  (* S m = S(S k'') ⟹ m := S k''：Lipschitz *)
  assert (Hlip : Qle (Qabs (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2) -
                               cos_partial (Datatypes.S (Datatypes.S k'')) z))
                      (Qabs (3 / 2 - z) * C)).
  { apply QleT'_to_Qle. apply (sc_cos_partial_lip_arch C (Datatypes.S k'') z); [exact HC | exact Hz]. }
  assert (Habs : Qle (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2) -
                        cos_partial (Datatypes.S (Datatypes.S k'')) z)
                     (Qabs (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2) -
                            cos_partial (Datatypes.S (Datatypes.S k'')) z)))
    by (apply Qle_Qabs).
  assert (HltC : Qlt (3 / 80) (Qabs (3 / 2 - z) * C)).
  { apply (Qlt_le_trans (3 / 80)
                        (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2) - cos_partial (Datatypes.S (Datatypes.S k'')) z)
                        (Qabs (3 / 2 - z) * C)).
    - exact Hgap.
    - apply (Qle_trans _ (Qabs (cos_partial (Datatypes.S (Datatypes.S k'')) (3 / 2) -
                                cos_partial (Datatypes.S (Datatypes.S k'')) z)) _).
      + exact Habs.
      + exact Hlip. }
  (* |3/2 − z| == z − 3/2（z > 3/2） *)
  assert (Habsz : Qabs (3 / 2 - z) == z - 3 / 2).
  { rewrite (Qabs_Qminus (3 / 2) z).
    rewrite (Qabs_pos (z - 3 / 2)).
    - reflexivity.
    - apply Qlt_le_weak. apply (proj1 (Qlt_minus_iff (3 / 2) z)). exact H32z. }
  assert (Hm : Qabs (3 / 2 - z) * C == C * (z - 3 / 2)).
  { apply Qeq_sym.
    rewrite Habsz.
    rewrite (Qmult_comm C (z - 3 / 2)).
    reflexivity. }
  rewrite Hm in HltC.
  apply QltT_to_Qlt. apply (sc_qdiv_lt_rcancel (3 / 80) C (z - 3 / 2)).
  + apply (Qlt_le_trans _ 1 _).
    * change (Qlt 0 1). compute. reflexivity.
    * apply QleT'_to_Qle. exact HC1.
  + exact HltC.
Qed.

(* ---------- C：Real 层 3/2 < cos_pi_half（π/2 下括号） ----------
   证明核心：∀n ≥ N：z_n − 3/2 > (3/80)/C
   - z_n := cos_zero_seq n（projT1 cos_pi_half n）
   - 取 k := 满足 cos_root_pt_bound n 的模（∃k ≥ 4 且 |cos_partial k (z_n)| < log_eps n）——
     但 margin 引理要求同一 k 同时有 cos(3/2)_k > 1/20（k ≥ 4）与根界。
     cos_root_pt_bound n 的 k 独立于 n 的任意大 k：直接取 k := Nat.max 4 (projT1 ((cos_root_pt_bound n)))。
   - log_eps n < 1/80 需 n ≥ N₂（q_pow_arch）。 *)
Lemma real_lt_three_halves_cos_pi_half : real_lt (real_const (3 / 2)) cos_pi_half.
Proof.
  destruct (exp_series_arch 2 (qltT_leT' 0 2 qltT_0_2)) as [C [HC1 HC]].
  assert (Hq80 : Qlt 0 (1 / 80)) by (change (Qlt 0 (1 / 80)); compute; reflexivity).
  destruct (q_pow_arch 1 (1 / 80) (qltT_leT' 0 1 qltT_0_1) (Qlt_to_QltT _ _ Hq80)) as [t Ht].
  assert (HlogN : forall n : nat, (Datatypes.S t <= n)%nat -> Qlt (log_eps n) (1 / 80)).
  { intros n Hn. apply QltT_to_Qlt. apply (log_eps_lt_delta (1 / 80) t n). exact Ht. exact Hn. }
  unfold real_lt.
  exists ((1 / 80) / C).
  split.
  - apply Qlt_to_QltT.
    apply (Qlt_shift_div_l 0 (1 / 80) C).
    + apply (Qlt_le_trans _ 1 _); [change (Qlt 0 1); compute; reflexivity | apply QleT'_to_Qle; exact HC1].
    + simpl. unfold Qlt; simpl; lia.
  - exists (Datatypes.S t).
    intros n Hn.
    assert (Hlog : Qlt (log_eps n) (1 / 80)) by (apply HlogN; exact (NatLe_drop _ _ Hn)).
    destruct ((cos_root_pt_bound n)) as [N1 HN1].
    set (k := Nat.max 4 N1).
    assert (Hk4 : (4 <= k)%nat) by (unfold k; apply Nat.le_max_l).
    assert (HkN1 : (N1 <= k)%nat) by (unfold k; apply Nat.le_max_r).
    (* |cos_partial k (cos_zero_seq n) − 0| < log_eps n：投影展开 cos(real_const z) == cos_partial k z *)
    assert (Hroot : Qlt (Qabs (cos_partial k (cos_zero_seq n) - 0)) (log_eps n)).
    { apply QltT_to_Qlt. apply (HN1 k (NatLe_lift _ _ HkN1)). }
    (* 逐点 3/2 < z_n *)
    assert (Hz32 : Qlt (3 / 2) (cos_zero_seq n)) by (apply QltT_to_Qlt; apply cos_zero_lower).
    (* |z_n| ≤ 2（QleT'） *)
    assert (HzT : QleT' (Qabs (cos_zero_seq n)) 2) by (apply Qle_to_QleT'; (apply QleT'_to_Qle; apply cos_zero_abs_le_two)).
    (* margin 引理：(3/80)/C < z_n − 3/2 *)
    assert (Hmgn : Qlt ((3 / 80) / C) (cos_zero_seq n - 3 / 2)).
    { apply QltT_to_Qlt. apply (sc_cos_zero_lower_margin_gen C n k (cos_zero_seq n) Hk4 HC1 HC Hlog HzT Hroot Hz32). }
    (* (1/80)/C < (3/80)/C：差 == (1/40)/C，Qlt_shift_div_l *)
    assert (HCpos : Qlt 0 C) by (apply (Qlt_le_trans 0 1 C); [change (Qlt 0 1); compute; reflexivity | apply QleT'_to_Qle; exact HC1]).
    assert (Hlt_eps : Qlt ((1 / 80) / C) ((3 / 80) / C)).
    { apply (proj2 (Qlt_minus_iff ((1 / 80) / C) ((3 / 80) / C))).
      assert (Hm : (3 / 80) / C + - ((1 / 80) / C) == (1 / 40) / C) by (unfold Qdiv; field; intro Hz; exact (Qlt_not_eq 0 C HCpos (Qeq_sym C 0 Hz))).
      rewrite Hm.
      apply (Qlt_shift_div_l 0 (1 / 40) C).
      + apply (Qlt_le_trans _ 1 _); [change (Qlt 0 1); compute; reflexivity | apply QleT'_to_Qle; exact HC1].
      + simpl. unfold Qlt; simpl; lia. }
    apply Qlt_to_QltT.
    assert (Hfinal : Qlt ((1 / 80) / C) (cos_zero_seq n - 3 / 2)).
    { apply (Qlt_trans _ ((3 / 80) / C) _).
      + exact Hlt_eps.
      + exact Hmgn. }
    setoid_replace (projT1 cos_pi_half n - projT1 (real_const (3 / 2)) n)
      with (cos_zero_seq n - 3 / 2).
    + exact Hfinal.
    + apply Qeq_sym.
      assert (Hp : projT1 cos_pi_half n == cos_zero_seq n) by (apply qeqT_imp_qeq; apply cos_pi_half_proj).
      assert (Hc : projT1 (real_const (3 / 2)) n == 3 / 2) by (apply (qeqT_imp_qeq _ _ (real_const_proj (3 / 2) n))).
      rewrite Hp. rewrite Hc. reflexivity.
Qed.

(* ---------- B2：Q 层逐点严格上界（cos(5/3) < −1/100 侧）
   |cos_partial k z| < log_eps n ⟹ cos z > −log_eps n > −1/400（log_eps < 1/400）
   cos(5/3)_k < −1/100（k ≥ 4）⟹ cos z − cos(5/3) > 1/100 − 1/400 = 3/400
   ⟹ 3/400 < |cos(5/3)_k − cos z_k| ≤ C·|z − 5/3| = C·(5/3 − z)（z < 5/3）
   ⟹ (3/400)/C < 5/3 − z                                       *)
Lemma sc_cos_zero_upper_margin_gen : forall (C : Q) (n k : nat) (z : Q),
  (4 <= k)%nat ->
  QleT' 1 C ->
  (forall mm : nat, QleT' (exp_series mm 2) C) ->
  Qlt (log_eps n) (1 / 400) ->
  QleT' (Qabs z) 2 ->
  Qlt (Qabs (cos_partial k z - 0)) (log_eps n) ->
  Qlt z (5 / 3) ->
  QltT ((3 / 400) / C) (5 / 3 - z).
Proof.
  intros C n k z Hk4 HC1 HC Hlog Hz Hroot H53z.
  apply Qlt_to_QltT.
  assert (Hc53 : Qlt (cos_partial k (5 / 3)) (- (1 / 100))) by (apply QltT_to_Qlt; apply sc_cos_partial_ge4_neg_5t; exact Hk4).
  (* cos z > −log_eps n（|x−0|<e 的左半） *)
  assert (Hczlog : Qlt (- log_eps n) (cos_partial k z)).
  { setoid_replace (cos_partial k z - 0) with (cos_partial k z) in Hroot by ring.
    assert (Hc : Qlt (- log_eps n) (cos_partial k z) /\
                Qlt (cos_partial k z) (log_eps n))
      by (apply (proj1 (Qabs_Qlt_condition (cos_partial k z) (log_eps n))); exact Hroot).
    exact (proj1 Hc). }
  assert (Hcz : Qlt (- (1 / 400)) (cos_partial k z)).
  { apply (Qlt_le_trans (- (1 / 400)) (- log_eps n) (cos_partial k z)).
    - apply Qopp_lt_compat. exact Hlog.
    - apply Qlt_le_weak. exact Hczlog. }
  (* 3/400 < cos z − cos(5/3)：cos z > −1/400、cos(5/3) < −1/100 *)
  assert (Hgap : Qlt (3 / 400) (cos_partial k z - cos_partial k (5 / 3))).
  { apply (proj2 (Qlt_minus_iff (3 / 400) (cos_partial k z - cos_partial k (5 / 3)))).
    assert (Hc400 : 3 / 400 == 1 / 100 - 1 / 400) by (unfold Qeq; simpl; lia).
    assert (Hm : cos_partial k z - cos_partial k (5 / 3) + - (3 / 400) ==
                 (cos_partial k z + 1 / 400) + (- (1 / 100) - cos_partial k (5 / 3)))
      by (rewrite Hc400; ring).
    rewrite Hm.
    apply (Qplus_lt_compat 0 (cos_partial k z + 1 / 400) 0 (- (1 / 100) - cos_partial k (5 / 3))).
    - (* 0 < cos z + 1/400 *)
      apply (proj1 (Qlt_minus_iff (- (1 / 400)) (cos_partial k z))). exact Hcz.
    - (* 0 < −1/100 − cos(5/3)：cos(5/3) < −1/100 *)
      apply (proj1 (Qlt_minus_iff (cos_partial k (5 / 3)) (- (1 / 100)))). exact Hc53. }
  destruct k as [|[|k'']]; [lia | lia |].
  assert (Hlip : Qle (Qabs (cos_partial (Datatypes.S (Datatypes.S k'')) z -
                               cos_partial (Datatypes.S (Datatypes.S k'')) (5 / 3)))
                      (Qabs (z - 5 / 3) * C)).
  { apply QleT'_to_Qle. apply (sc_cos_partial_lip_arch53 C (Datatypes.S k'') z); [exact HC | exact Hz]. }
  assert (Habs : Qle (cos_partial (Datatypes.S (Datatypes.S k'')) z - cos_partial (Datatypes.S (Datatypes.S k'')) (5 / 3))
                     (Qabs (cos_partial (Datatypes.S (Datatypes.S k'')) z - cos_partial (Datatypes.S (Datatypes.S k'')) (5 / 3))))
    by (apply Qle_Qabs).
  assert (HltC : Qlt (3 / 400) (Qabs (z - 5 / 3) * C)).
  { apply (Qlt_le_trans (3 / 400)
                        (cos_partial (Datatypes.S (Datatypes.S k'')) z - cos_partial (Datatypes.S (Datatypes.S k'')) (5 / 3))
                        (Qabs (z - 5 / 3) * C)).
    - exact Hgap.
    - apply (Qle_trans _ (Qabs (cos_partial (Datatypes.S (Datatypes.S k'')) z - cos_partial (Datatypes.S (Datatypes.S k'')) (5 / 3))) _).
      + exact Habs.
      + exact Hlip. }
  (* z < 5/3 ⟹ |z − 5/3| == 5/3 − z *)
  assert (Habsz : Qabs (z - 5 / 3) == 5 / 3 - z).
  { rewrite (Qabs_Qminus z (5 / 3)).
    rewrite (Qabs_pos (5 / 3 - z)).
    - reflexivity.
    - apply Qlt_le_weak. apply (proj1 (Qlt_minus_iff z (5 / 3))). exact H53z. }
  assert (Hm : Qabs (z - 5 / 3) * C == C * (5 / 3 - z)).
  { apply Qeq_sym.
    rewrite Habsz.
    rewrite (Qmult_comm C (5 / 3 - z)).
    reflexivity. }
  rewrite Hm in HltC.
  apply QltT_to_Qlt. apply (sc_qdiv_lt_rcancel (3 / 400) C (5 / 3 - z)).
  + apply (Qlt_le_trans _ 1 _).
    * change (Qlt 0 1). compute. reflexivity.
    * apply QleT'_to_Qle. exact HC1.
  + exact HltC.
Qed.

(* ---------- C2：Real 层 cos_pi_half < 5/3（上括号） ----------
   同下括号副本：eps := (1/400)/C、N := S t₂（log_eps n < 1/400） *)
Lemma real_lt_cos_pi_half_five_thirds : real_lt cos_pi_half (real_const (5 / 3)).
Proof.
  destruct (exp_series_arch 2 (qltT_leT' 0 2 qltT_0_2)) as [C [HC1 HC]].
  assert (Hq400 : Qlt 0 (1 / 400)) by (change (Qlt 0 (1 / 400)); compute; reflexivity).
  destruct (q_pow_arch 1 (1 / 400) (qltT_leT' 0 1 qltT_0_1) (Qlt_to_QltT _ _ Hq400)) as [t Ht].
  assert (HlogN : forall n : nat, (Datatypes.S t <= n)%nat -> Qlt (log_eps n) (1 / 400)).
  { intros n Hn. apply QltT_to_Qlt. apply (log_eps_lt_delta (1 / 400) t n). exact Ht. exact Hn. }
  unfold real_lt.
  exists ((1 / 400) / C).
  split.
  - apply Qlt_to_QltT.
    apply (Qlt_shift_div_l 0 (1 / 400) C).
    + apply (Qlt_le_trans _ 1 _); [change (Qlt 0 1); compute; reflexivity | apply QleT'_to_Qle; exact HC1].
    + simpl. unfold Qlt; simpl; lia.
  - exists (Datatypes.S t).
    intros n Hn.
    assert (Hlog : Qlt (log_eps n) (1 / 400)) by (apply HlogN; exact (NatLe_drop _ _ Hn)).
    destruct ((cos_root_pt_bound n)) as [N1 HN1].
    set (k := Nat.max 4 N1).
    assert (Hk4 : (4 <= k)%nat) by (unfold k; apply Nat.le_max_l).
    assert (HkN1 : (N1 <= k)%nat) by (unfold k; apply Nat.le_max_r).
    assert (Hroot : Qlt (Qabs (cos_partial k (cos_zero_seq n) - 0)) (log_eps n)).
    { apply QltT_to_Qlt. apply (HN1 k (NatLe_lift _ _ HkN1)). }
    assert (Hz53 : Qlt (cos_zero_seq n) (5 / 3)) by (apply QltT_to_Qlt; apply cos_zero_upper).
    assert (HzT : QleT' (Qabs (cos_zero_seq n)) 2) by (apply Qle_to_QleT'; (apply QleT'_to_Qle; apply cos_zero_abs_le_two)).
    assert (Hmgn : Qlt ((3 / 400) / C) (5 / 3 - cos_zero_seq n)).
    { apply QltT_to_Qlt. apply (sc_cos_zero_upper_margin_gen C n k (cos_zero_seq n) Hk4 HC1 HC Hlog HzT Hroot Hz53). }
    assert (HCpos : Qlt 0 C) by (apply (Qlt_le_trans 0 1 C); [change (Qlt 0 1); compute; reflexivity | apply QleT'_to_Qle; exact HC1]).
    assert (Hlt_eps : Qlt ((1 / 400) / C) ((3 / 400) / C)).
    { apply (proj2 (Qlt_minus_iff ((1 / 400) / C) ((3 / 400) / C))).
      assert (Hm : (3 / 400) / C + - ((1 / 400) / C) == (1 / 200) / C) by (unfold Qdiv; field; intro Hz; exact (Qlt_not_eq 0 C HCpos (Qeq_sym C 0 Hz))).
      rewrite Hm.
      apply (Qlt_shift_div_l 0 (1 / 200) C).
      + apply (Qlt_le_trans _ 1 _); [change (Qlt 0 1); compute; reflexivity | apply QleT'_to_Qle; exact HC1].
      + simpl. unfold Qlt; simpl; lia. }
    apply Qlt_to_QltT.
    assert (Hfinal : Qlt ((1 / 400) / C) (5 / 3 - cos_zero_seq n)).
    { apply (Qlt_trans _ ((3 / 400) / C) _).
      + exact Hlt_eps.
      + exact Hmgn. }
    setoid_replace (projT1 (real_const (5 / 3)) n - projT1 cos_pi_half n)
      with (5 / 3 - cos_zero_seq n).
    + exact Hfinal.
    + apply Qeq_sym.
      assert (Hp : projT1 cos_pi_half n == cos_zero_seq n) by (apply qeqT_imp_qeq; apply cos_pi_half_proj).
      assert (Hc : projT1 (real_const (5 / 3)) n == 5 / 3) by (apply (qeqT_imp_qeq _ _ (real_const_proj (5 / 3) n))).
      rewrite Hc. rewrite Hp. reflexivity.
Qed.

(* ---------- D：real_pi_geom_between ----------
   π_geom := real_mult (real_const 2) cos_pi_half
   3 < π_geom < 10/3 ⟸ 3/2 < cos_pi_half < 5/3 乘 2（real_lt_mult_compat，c := real_const 2）
   + 常数乘恒等：real_const 2 · real_const (3/2) == real_const 3（逐点 ring） *)
Lemma real_pi_geom_gt_three : real_lt (real_const 3) real_pi_geom.
Proof.
  unfold real_pi_geom.
  (* 3 == 2·(3/2)；由 3/2 < π/2 乘 2：2·(3/2) < 2·π/2 *)
  apply (real_eq_lt_lt (real_const 3) (real_mult (real_const 2) (real_const (3 / 2))) _).
  - (* 3 == 2·(3/2)：等价常数 real_eq（sym 后逐点 field） *)
    apply real_eq_sym.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 2) (real_const (3 / 2)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)). rewrite (qeqT_imp_qeq _ _ (real_const_proj (3 / 2) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 3 n)). field.
  - apply (real_lt_mult_compat (real_const (3 / 2)) cos_pi_half (real_const 2)).
    + (* 0 < 2 *)
      apply real_const_lt. exact qltT_0_2.
    + exact real_lt_three_halves_cos_pi_half.
Qed.

Lemma real_pi_geom_lt_ten_thirds : real_lt real_pi_geom (real_const (10 / 3)).
Proof.
  unfold real_pi_geom.
  (* 2·π/2 < 2·(5/3) == 10/3 *)
  apply (real_lt_eq_lt _ (real_mult (real_const 2) (real_const (5 / 3))) _).
  - apply (real_lt_mult_compat cos_pi_half (real_const (5 / 3)) (real_const 2)).
    + apply real_const_lt. exact qltT_0_2.
    + exact real_lt_cos_pi_half_five_thirds.
  - apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 2) (real_const (5 / 3)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)). rewrite (qeqT_imp_qeq _ _ (real_const_proj (5 / 3) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (10 / 3) n)). field.
Qed.

Lemma real_pi_geom_between :
  And (real_lt (real_const 3) real_pi_geom)
      (real_lt real_pi_geom (real_const (10 / 3))).
Proof.
  split. - exact real_pi_geom_gt_three. - exact real_pi_geom_lt_ten_thirds.
Qed.

(* ============================================================ *)
(* SC-2 批 3（并入 194）：cos 零点唯一桥拓宽 (3/2,5/3)→(3/2,2) *)
(*   子代理 sB 产出（评审并入）——T-π3 前置 *)
(* ============================================================ *)

(* ---- 1. 逆界（距离形，v ≤ 2 版）----
   3/2 ≤ u ≤ v ≤ 2、逐点 |cos u_k − 0| < du、|cos v_k − 0| < dv
   ⟹ v − u < 2·(du + dv)。
   与既有 cos_inv_dist（v ≤ 5/3）同证：内部只需 0 ≤ u（3/2 ≤ u 给）
   与 v ≤ 2（cos_inv_pt 域 [0,2]），以及 v+u ≥ 3（u ≥ 3/2 给）。 *)
Lemma cos_inv_dist_le2 : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle (3 / 2) u -> Qle u v -> Qle v 2 ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  QltT (v - u) (2 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu0 Huv Hv2 Hdu Hdv.
  apply Qlt_to_QltT.
  (* 0 ≤ u、v ≤ 2（cos_inv_pt 前提） *)
  assert (Hu0' : Qle 0 u) by (apply (Qle_trans _ (3 / 2) _); [change (Qle 0 (3 / 2)); unfold Qle, Qdiv; simpl; lia | exact Hu0]).
  assert (Hv2' : Qle v 2) by exact Hv2.
  (* (v²−u²)/6 < du + dv *)
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { apply QltT_to_Qlt. apply (cos_inv_pt u v k du dv Hk Hu0' Huv Hv2' Hdu Hdv). }
  (* v²−u² == (v−u)(v+u) 且 v+u ≥ 3：3(v−u) ≤ v²−u² *)
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (Hvu3 : Qle ((v - u) * 3) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) 3 (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split; [change (Qle 0 3); unfold Qle; simpl; lia | ].
      assert (H3 : Qle 3 (v + u)).
      { apply (Qle_trans _ (3 / 2 + 3 / 2) _).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
        - apply (Qplus_le_compat (3 / 2) v (3 / 2) u).
          + apply (Qle_trans _ u _); [exact Hu0 | exact Huv].
          + exact Hu0. }
      exact H3. }
  (* 链：3(v−u) ≤ v²−u² ⟹ (v−u) ≤ (v²−u²)/3；Hq 乘 2 ⟹ (v²−u²)/3 < 2(du+dv) *)
  assert (Hq2 : Qlt (v - u) (2 * (du + dv))).
  { apply (Qle_lt_trans (v - u) ((v * v - u * u) * (1 / 3)) (2 * (du + dv))).
    - (* v−u ≤ (v²−u²)/3：v−u == (v−u)·3·(1/3) ≤ (v²−u²)·(1/3) *)
      apply (Qle_trans _ (((v - u) * 3) * (1 / 3)) _).
      + apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        assert (Hr3 : ((v - u) * 3) * (1 / 3) == v - u) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
        apply Qeq_sym. exact Hr3.
      + apply (Qmult_le_compat_r ((v - u) * 3) (v * v - u * u) (1 / 3)).
        * apply (Qle_trans _ ((v - u) * (v + u)) _).
          -- exact Hvu3.
          -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hprod.
        * apply (Qlt_le_weak 0 (1 / 3)). change (Qlt 0 (1 / 3)). unfold Qdiv. compute. reflexivity.
    - (* (v²−u²)/3 < 2(du+dv) *)
      assert (Hm : (v * v - u * u) * (1 / 3) == ((v * v - u * u) * (1 / 6)) * 2) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      assert (Hm2 : (du + dv) * 2 == 2 * (du + dv)) by ring.
      apply (Qlt_le_trans ((v * v - u * u) * (1 / 3)) ((du + dv) * 2) (2 * (du + dv))).
      * apply (Qle_lt_trans ((v * v - u * u) * (1 / 3)) (((v * v - u * u) * (1 / 6)) * 2) ((du + dv) * 2)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) 2).
           ++ change (Qlt 0 2). compute. reflexivity.
           ++ exact Hq.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm2. }
  exact Hq2.
Qed.

(* ---- 2. 主目标：cos 在 (3/2, 2) 的零点唯一 == cos_pi_half ----
   副本既有 cos_pi_half_unique（61618 区）的 eps 装配：
   w 侧上端点 5/3 → 2（real_lt_upper_pt 2）、w 逐点上界 Qle w_n 2、
   z 侧逐点上界经 Qle (5/3) 2 传递、逆界换 cos_inv_dist_le2。   *)
Lemma cos_pi_half_unique_widened : forall (w : Real),
  real_lt (real_const (3 / 2)) w -> real_lt w (real_const 2) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact HepsQ. }
  (* 逐点界来源：w 侧（端点 + cos w == 0 对角）、z 侧（cos_zero_lower/upper + cos z == 0 对角） *)
  destruct ((real_lt_lower_pt (3 / 2) w Hlow)) as [Nlo HNlo].
  destruct ((real_lt_upper_pt 2 w Hup)) as [Nup HNup].
  destruct ((cos_eq_zero_diag_bound w Hw0 (eps / 8) Heps8)) as [Nwd Hwd].
  destruct ((cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero (eps / 8) Heps8)) as [Nzd Hzd].
  destruct (q_pow_arch 1 (eps / 8) (qltT_leT' 0 1 qltT_0_1) (Qlt_to_QltT _ _ Heps8)) as [t Ht].
  set (A := Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))).
  exists (Nat.max 2 (Nat.max A (Datatypes.S t))).
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (HnAt : (Nat.max A (Datatypes.S t) <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (HnA : (A <= n)%nat) by (apply (Nat.le_trans _ (Nat.max A (Datatypes.S t)) _); [apply Nat.le_max_l | exact HnAt]).
  assert (Hnlo : (Nlo <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))) _); [apply Nat.le_max_l | ].
    unfold A in HnA. exact HnA. }
  assert (Hnup : (Nup <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnwd : (Nwd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnzd : (Nzd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  (* w_n ∈ (3/2, 2)、z_n ∈ (3/2, 5/3)（Q 层） *)
  assert (Hwlo : Qle (3 / 2) (projT1 w n)) by (apply Qlt_le_weak; apply (HNlo n); exact Hnlo).
  assert (Hwup : Qle (projT1 w n) 2) by (apply Qlt_le_weak; apply (HNup n); exact Hnup).
  assert (Hzlo : Qle (3 / 2) (cos_zero_seq n)) by (apply Qlt_le_weak; (apply QltT_to_Qlt; apply cos_zero_lower)).
  assert (Hzup : Qle (cos_zero_seq n) (5 / 3)) by (apply Qlt_le_weak; (apply QltT_to_Qlt; apply cos_zero_upper)).
  (* z 侧 v ≤ 2（5/3 ≤ 2 传递，cos_inv_dist_le2 前提） *)
  assert (Hzup2 : Qle (cos_zero_seq n) 2).
  { apply (Qle_trans _ (5 / 3) _); [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia]. }
  (* cos w_n 与 cos z_n 的对角界 < eps/8 *)
  assert (Hwpt : Qlt (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 8)).
  { apply QltT_to_Qlt. apply (Hwd n). exact Hnwd. }
  assert (Hzpt : Qlt (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n)) (eps / 8)).
  { apply QltT_to_Qlt. apply (Hzd n). exact Hnzd. }
  (* 分支：|w_n − z_n| ≤ eps/2 < eps（逆界，u := 小者） *)
  destruct (Qlt_le_dec (cos_zero_seq n) (projT1 w n)) as [Hzw | Hwz].
  - (* z_n < w_n：u := z_n、v := w_n *)
    assert (Hd : Qlt (projT1 w n - cos_zero_seq n) (2 * (eps / 8 + eps / 8))).
    { apply QltT_to_Qlt. apply (cos_inv_dist_le2 (cos_zero_seq n) (projT1 w n) (eps / 8) (eps / 8) n).
      - exact Hn2.
      - exact Hzlo.
      - apply Qlt_le_weak. exact Hzw.
      - exact Hwup.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 8)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt.
      - assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
        { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                              (eps / 8)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
            assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
            { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)). rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
            rewrite Hq. reflexivity.
          - exact Hwpt. }
        exact Hwpt'.
    }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (projT1 w n - cos_zero_seq n) eps).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). apply Qlt_le_weak. exact Hzw.
    + apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
        apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
           apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
           ++ apply (Qlt_shift_div_l 0 eps 2).
              ** change (Qlt 0 2). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
  - (* w_n ≤ z_n：u := w_n、v := z_n（对称） *)
    assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
    { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                          (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                          (eps / 8)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
        assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
        { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)). rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
        rewrite Hq. reflexivity.
      - exact Hwpt. }
    assert (Hd : Qlt (cos_zero_seq n - projT1 w n) (2 * (eps / 8 + eps / 8))).
    { apply QltT_to_Qlt. apply (cos_inv_dist_le2 (projT1 w n) (cos_zero_seq n) (eps / 8) (eps / 8) n).
      - exact Hn2.
      - exact Hwlo.
      - exact Hwz.
      - exact Hzup2.
      - exact Hwpt'.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 8)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt. }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (cos_zero_seq n - projT1 w n) eps).
    + rewrite (Qabs_Qminus (projT1 w n) (cos_zero_seq n)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 w n) (cos_zero_seq n))). exact Hwz.
    + apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
        apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
           apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
           ++ apply (Qlt_shift_div_l 0 eps 2).
              ** change (Qlt 0 2). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
Qed.

(* ============================================================ *)
(* SC-2 批 4（并入 195）：exp 可微且导数即自身（显式可引）    *)
(*   子代理 sC 产出（评审并入）——exp_deriv 显式陈述          *)
(* ============================================================ *)

(* exp 在 x>0 处可微、且导数即 exp 自身（Bishop 显式形式）。
   deriv 项显式写为 cauchy_real_exp x（而非 RealDifferentiable 记录中不可见的 rdf 见证）。
   论文可引为：「exp' = exp：对任意 x>0 与 eps>0，存在 δ>0，使
   |exp(x+h) − exp x − exp x·h| ≤ eps·|h| + eps' 对所有 |h|<δ、x+h>0、eps'>0 成立」。 *)
Lemma real_exp_deriv_eq_self :
  forall (x : Real) (Hx : real_lt real_zero x),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall h : Real, real_lt (real_abs h) delta ->
          forall (Hxh : real_lt real_zero (real_plus x h)),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                                       (real_opp (real_plus (cauchy_real_exp x)
                                                  (real_mult (cauchy_real_exp x) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x Hx eps Heps.
(* ---- 证明体转录自基座 ConstructiveWorld.v L47872–L48000（real_exp_differentiable 的
        rdf_correct 论证；此处 rdf 已显式取为 cauchy_real_exp）---- *)

  set (eps0 := real_mult eps (real_inv_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x)))).
  assert (Heps0 : real_lt real_zero eps0).
  { unfold eps0. apply real_mult_positive.
    - exact Heps.
    - apply (real_inv_pos_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x))). }
  destruct (exp_minus_one_linear eps0 Heps0) as [delta0 [Hdelta0 Hlin0]].
  exists delta0.
  split.
  - exact Hdelta0.
  - intros h Hh Hxh eps' Heps'.
    set (eps0' := real_mult eps' (real_inv_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x)))).
    assert (Heps0' : real_lt real_zero eps0').
    { unfold eps0'. apply real_mult_positive.
      - exact Heps'.
      - apply (real_inv_pos_pos (real_plus real_one (real_abs (cauchy_real_exp x))) (real_abs_plus_one_pos (cauchy_real_exp x))). }
    assert (Hlin : real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                           (real_plus (real_mult eps0 (real_abs h)) eps0')).
    { apply (Hlin0 h Hh eps0' Heps0'). }
    assert (Habs0 : real_le real_zero (real_abs (cauchy_real_exp x))).
    { left. apply real_abs_exp_pos. }
    (* D == exp x·(exp h − 1 − h)：exp_diff_factor + 减法提因子 *)
    assert (Hxxh : real_eq (real_plus (real_plus x h) (real_opp x)) h).
    { apply real_eq_of_zero_diff. intro n.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus x h) (real_opp x) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj x h n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
      simpl. ring. }
    assert (Hmain_eq : real_eq (real_plus (cauchy_real_exp (real_plus x h))
                      (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h))))
                      (real_mult (cauchy_real_exp x)
                         (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))).
    { apply (real_eq_trans _ (real_plus (real_plus (cauchy_real_exp (real_plus x h)) (real_opp (cauchy_real_exp x)))
                                        (real_opp (real_mult (cauchy_real_exp x) h))) _).
      - apply (real_eq_trans _ (real_plus (cauchy_real_exp (real_plus x h))
                       (real_plus (real_opp (cauchy_real_exp x)) (real_opp (real_mult (cauchy_real_exp x) h)))) _).
        + apply (RealSetoid.real_eq_plus_compat (cauchy_real_exp (real_plus x h))
                 (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))
                 (cauchy_real_exp (real_plus x h))
                 (real_plus (real_opp (cauchy_real_exp x)) (real_opp (real_mult (cauchy_real_exp x) h)))).
          * apply real_eq_refl.
          * apply (real_opp_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)).
        + apply (real_plus_assoc (cauchy_real_exp (real_plus x h))
                                 (real_opp (cauchy_real_exp x))
                                 (real_opp (real_mult (cauchy_real_exp x) h))).
      - apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_exp x)
                   (real_plus (cauchy_real_exp h) (real_opp real_one)))
                   (real_opp (real_mult (cauchy_real_exp x) h))) _).
        + apply (RealSetoid.real_eq_plus_compat
                 (real_plus (cauchy_real_exp (real_plus x h)) (real_opp (cauchy_real_exp x)))
                 (real_opp (real_mult (cauchy_real_exp x) h))
                 (real_mult (cauchy_real_exp x) (real_plus (cauchy_real_exp h) (real_opp real_one)))
                 (real_opp (real_mult (cauchy_real_exp x) h))).
          * apply (real_eq_trans _ (real_mult (cauchy_real_exp x)
                 (real_plus (cauchy_real_exp (real_plus (real_plus x h) (real_opp x))) (real_opp real_one))) _).
            -- apply (exp_diff_factor (real_plus x h) x).
            -- apply (RealSetoid.real_eq_mult_compat (cauchy_real_exp x)
                       (real_plus (cauchy_real_exp (real_plus (real_plus x h) (real_opp x))) (real_opp real_one))
                       (cauchy_real_exp x)
                       (real_plus (cauchy_real_exp h) (real_opp real_one))).
               ++ apply real_eq_refl.
               ++ apply (RealSetoid.real_eq_plus_compat
                          (cauchy_real_exp (real_plus (real_plus x h) (real_opp x)))
                          (real_opp real_one)
                          (cauchy_real_exp h)
                          (real_opp real_one)).
                  ** apply cauchy_real_exp_wd. exact Hxxh.
                  ** apply real_eq_refl.
          * apply real_eq_refl.
        + apply real_mult_sub_factor. }
    (* |D| == |exp x|·|exp h − 1 − h| *)
    assert (HabsD : real_le (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                      (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))))
                      (real_mult (real_abs (cauchy_real_exp x))
                         (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))).
    { apply RealSetoid.real_eq_le.
      apply (real_eq_trans (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                             (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))))
             (real_abs (real_mult (cauchy_real_exp x)
                (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
             (real_mult (real_abs (cauchy_real_exp x))
                (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))).
      - apply real_abs_eq_compat. exact Hmain_eq.
      - apply (real_abs_mult_req (cauchy_real_exp x)
                 (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))). }
    (* 乘 |exp x|：real_le_mult_compat_weak（0 ≤ |exp x| 由 0 < exp x 直构） *)
    assert (Hmul0 : real_le (real_mult (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                                       (real_abs (cauchy_real_exp x)))
                            (real_mult (real_plus (real_mult eps0 (real_abs h)) eps0')
                                       (real_abs (cauchy_real_exp x)))).
    { apply (real_le_mult_compat_weak (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                                      (real_plus (real_mult eps0 (real_abs h)) eps0')
                                      (real_abs (cauchy_real_exp x))).
      - exact Habs0.
      - exact Hlin. }
    assert (Hmul : real_le (real_mult (real_abs (cauchy_real_exp x))
                          (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
                          (real_mult (real_abs (cauchy_real_exp x))
                             (real_plus (real_mult eps0 (real_abs h)) eps0'))).
    { apply (real_le_trans (real_mult (real_abs (cauchy_real_exp x))
                            (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
             (real_mult (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                        (real_abs (cauchy_real_exp x)))
             (real_mult (real_abs (cauchy_real_exp x))
                (real_plus (real_mult eps0 (real_abs h)) eps0'))).
      - apply RealSetoid.real_eq_le.
        apply (real_mult_comm (real_abs (cauchy_real_exp x))
               (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))).
      - apply (real_le_trans _ (real_mult (real_plus (real_mult eps0 (real_abs h)) eps0')
                                          (real_abs (cauchy_real_exp x))) _).
        + exact Hmul0.
        + apply RealSetoid.real_eq_le.
          apply (real_mult_comm (real_plus (real_mult eps0 (real_abs h)) eps0')
                                (real_abs (cauchy_real_exp x))). }
    (* 最终缩放（Q 层逐点） *)
    assert (Hfinal : real_le (real_mult (real_abs (cauchy_real_exp x))
                            (real_plus (real_mult eps0 (real_abs h)) eps0'))
                            (real_plus (real_mult eps (real_abs h)) eps')).
    { unfold eps0, eps0'.
      apply (real_abs_scaling_le (cauchy_real_exp x) eps eps' h Heps Heps'). }
    apply (real_le_trans (real_abs (real_plus (cauchy_real_exp (real_plus x h))
                   (real_opp (real_plus (cauchy_real_exp x) (real_mult (cauchy_real_exp x) h)))))
             (real_mult (real_abs (cauchy_real_exp x))
                (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))))
             (real_plus (real_mult eps (real_abs h)) eps')).
    { exact HabsD. }
    { apply (real_le_trans _ (real_mult (real_abs (cauchy_real_exp x))
                               (real_plus (real_mult eps0 (real_abs h)) eps0')) _).
      { exact Hmul. }
      { exact Hfinal. } }
Qed.

(* 配套实例：exp ∈ RealDifferentiable，且（构造性地）导函数显式取为 exp 自身。
   由 real_exp_deriv_eq_self 直接证得；rdf_correct 即上述 Bishop 界。 *)
Lemma real_exp_diff_with_deriv_self :
  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) => cauchy_real_exp x).
Proof.
  exists (fun (x : Real) (Hx : real_lt real_zero x) => cauchy_real_exp x).
  intros x Hx eps Heps.
  exact (real_exp_deriv_eq_self x Hx eps Heps).
Qed.

(* ============================================================ *)
(* SC-2 批 5（并入 196）：T-π3 Phase 1 外围                  *)
(*   π_L·(1/2) ∈ (3/2, 5/3) 严格 Real 括号 + 常数/回代工具    *)
(*   子代理 sD 检验改名并入（零 crux 依赖；crux 版留模板）      *)
(* ============================================================ *)

Definition w_leibniz : Real := real_mult cauchy_real_pi_leibniz (real_const (1 / 2)).



(* ============ 常数环恒等（逐点 ring 桥） ============ *)
Lemma real_half_const_three : real_eq (real_mult (real_const (1 / 2)) (real_const 3))
                                     (real_const (3 / 2)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite !(qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2)) (real_const 3) n)).
  rewrite !(qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj 3 n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (3 / 2) n)). field.
Qed.

Lemma real_half_const_ten_thirds : real_eq (real_mult (real_const (1 / 2)) (real_const (10 / 3)))
                                         (real_const (5 / 3)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite !(qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2)) (real_const (10 / 3)) n)).
  rewrite !(qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj (10 / 3) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (5 / 3) n)). field.
Qed.

Lemma real_half_pos : real_lt real_zero (real_const (1 / 2)).
Proof.
  apply real_const_lt. apply Qlt_to_QltT. change (Qlt 0 (1 / 2)). compute. reflexivity.
Qed.

(* (1/2)·π_L == π_L·(1/2)（w 的换序） *)
Lemma real_half_pi_leibniz_comm : real_eq (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
                                (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))).
Proof. apply real_mult_comm. Qed.

(* ============ π_L/2 ∈ (3/2, 5/3)（Real 层严格括号） ============ *)
Lemma real_pi_leibniz_half_lower : real_lt (real_const (3 / 2)) w_leibniz.
Proof.
  unfold w_leibniz.
  exact (real_eq_lt_lt (real_const (3 / 2))
    (real_mult (real_const (1 / 2)) (real_const 3))
    (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
    (real_eq_sym (real_mult (real_const (1 / 2)) (real_const 3))
      (real_const (3 / 2)) real_half_const_three)
    (real_lt_eq_lt (real_mult (real_const (1 / 2)) (real_const 3))
      (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
      (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
      (real_lt_mult_compat (real_const 3) cauchy_real_pi_leibniz
        (real_const (1 / 2)) real_half_pos real_pi_leibniz_gt_three)
      real_half_pi_leibniz_comm)).
Qed.

Lemma real_pi_leibniz_half_upper : real_lt w_leibniz (real_const (5 / 3)).
Proof.
  unfold w_leibniz.
  exact (real_eq_lt_lt
    (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
    (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
    (real_const (5 / 3))
    (real_eq_sym (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
      (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
      real_half_pi_leibniz_comm)
    (real_lt_eq_lt (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
      (real_mult (real_const (1 / 2)) (real_const (10 / 3)))
      (real_const (5 / 3))
      (real_lt_mult_compat cauchy_real_pi_leibniz
        (real_const (10 / 3)) (real_const (1 / 2)) real_half_pos
        real_pi_leibniz_lt_ten_thirds)
      real_half_const_ten_thirds)).
Qed.

(* ============ 乘 2 回代：2·(π_L·(1/2)) == π_L ============ *)
Lemma real_two_half_one : real_eq (real_mult (real_const 2) (real_const (1 / 2))) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite !(qeqT_imp_qeq _ _ (real_mult_proj (real_const 2) (real_const (1 / 2)) n)).
  rewrite !(qeqT_imp_qeq _ _ (real_const_proj 2 n)). rewrite !(qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
  cbn [projT1 real_one]. field.
Qed.

Lemma real_double_half_cancel : forall x : Real,
  real_eq (real_mult (real_const 2) (real_mult x (real_const (1 / 2)))) x.
Proof.
  intro x.
  (* 链：2·(x·(1/2)) == (2·x)·(1/2) == (x·2)·(1/2) == x·(2·(1/2)) == x·1 == x *)
  apply (real_eq_trans _ (real_mult (real_mult (real_const 2) x) (real_const (1 / 2))) _).
  - apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult (real_mult x (real_const 2)) (real_const (1 / 2))) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult (real_const 2) x) (real_const (1 / 2))
                                 (real_mult x (real_const 2)) (real_const (1 / 2))).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult x (real_mult (real_const 2) (real_const (1 / 2)))) _).
      * apply real_eq_sym. apply real_mult_assoc.
      * apply (real_eq_trans _ (real_mult x real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat x (real_mult (real_const 2) (real_const (1 / 2)))
                                                 x real_one).
           ++ apply real_eq_refl.
           ++ exact real_two_half_one.
        -- (* x·1 == x（逐点 ring） *)
           apply real_eq_of_zero_diff. intro n.
           apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _ (real_mult_proj x real_one n)).
           cbn [projT1 real_one]. ring.
Qed.

(* ============================================================ *)
(* SC-2 批 6（并入 197）：sin/cos 加法定理 Q 层论证           *)
(*   sA 恒等地基 15 条 + sF 度向机 9 条（子代理产出）          *)
(*   Real 层装配前置（sE 续作）                              *)
(* ============================================================ *)

Lemma sc_add_q_pow_ext : forall (x : Q) (n m : nat), n = m ->QeqT (q_pow x n) (q_pow x m).
Proof.
  intros x n m H. apply qeq_imp_qeqT. rewrite H. reflexivity.
Qed.

(* ============================================================ *)
(* A：cos_term i x · sin_term k y 的「组合分母」形式            *)
(*   == (−1)^{i+k} · x^{2i} · y^{S(2k)} · /((2i)!·(S(2k))!)     *)
(* ============================================================ *)
Lemma sc_add_csin_pair : forall (x y : Q) (i k : nat), QeqT (cos_term i x * sin_term k y) (q_pow (-1) (i + k) * (q_pow x (2 * i) * q_pow y (Datatypes.S (2 * k))) *
    Qinv (q_fact (2 * i) * q_fact (Datatypes.S (2 * k)))).
Proof.
  intros x y i k.
  apply qeq_imp_qeqT.
  unfold cos_term, sin_term. unfold Qdiv.
  assert (Hre : (q_pow (-1) i * (q_pow x (2 * i) * Qinv (q_fact (2 * i)))) *
                (q_pow (-1) k * (q_pow y (Datatypes.S (2 * k)) * Qinv (q_fact (Datatypes.S (2 * k))))) ==
                (q_pow (-1) i * q_pow (-1) k) *
                (q_pow x (2 * i) * q_pow y (Datatypes.S (2 * k)) *
                 (Qinv (q_fact (2 * i)) * Qinv (q_fact (Datatypes.S (2 * k)))))).
  { ring. }
  rewrite Hre.
  rewrite <- (Qinv_mult_distr (q_fact (2 * i)) (q_fact (Datatypes.S (2 * k)))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite <- (qeqT_imp_qeq _ _ (q_pow_add (-1) i k)).
  ring.
Qed.

(* ============================================================ *)
(* B：sin_term i x · cos_term k y == (−1)^{i+k} x^{S(2i)} y^{2k} *)
(*    / ((S(2i))!·(2k)!)                                        *)
(* ============================================================ *)
Lemma sc_add_sinc_pair : forall (x y : Q) (i k : nat), QeqT (sin_term i x * cos_term k y) (q_pow (-1) (i + k) * (q_pow x (Datatypes.S (2 * i)) * q_pow y (2 * k)) *
    Qinv (q_fact (Datatypes.S (2 * i)) * q_fact (2 * k))).
Proof.
  intros x y i k.
  apply qeq_imp_qeqT.
  unfold sin_term, cos_term. unfold Qdiv.
  assert (Hre : (q_pow (-1) i * (q_pow x (Datatypes.S (2 * i)) * Qinv (q_fact (Datatypes.S (2 * i))))) *
                (q_pow (-1) k * (q_pow y (2 * k) * Qinv (q_fact (2 * k)))) ==
                (q_pow (-1) i * q_pow (-1) k) *
                (q_pow x (Datatypes.S (2 * i)) * q_pow y (2 * k) *
                 (Qinv (q_fact (Datatypes.S (2 * i))) * Qinv (q_fact (2 * k))))).
  { ring. }
  rewrite Hre.
  rewrite <- (Qinv_mult_distr (q_fact (Datatypes.S (2 * i))) (q_fact (2 * k))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite <- (qeqT_imp_qeq _ _ (q_pow_add (-1) i k)).
  ring.
Qed.

(* ============================================================ *)
(* C：cos_term i x · cos_term k y == (−1)^{i+k} x^{2i} y^{2k}    *)
(*    / ((2i)!·(2k)!)                                           *)
(* ============================================================ *)
Lemma sc_add_cc_pair : forall (x y : Q) (i k : nat), QeqT (cos_term i x * cos_term k y) (q_pow (-1) (i + k) * (q_pow x (2 * i) * q_pow y (2 * k)) *
    Qinv (q_fact (2 * i) * q_fact (2 * k))).
Proof.
  intros x y i k.
  apply qeq_imp_qeqT.
  unfold cos_term. unfold Qdiv.
  assert (Hre : (q_pow (-1) i * (q_pow x (2 * i) * Qinv (q_fact (2 * i)))) *
                (q_pow (-1) k * (q_pow y (2 * k) * Qinv (q_fact (2 * k)))) ==
                (q_pow (-1) i * q_pow (-1) k) *
                (q_pow x (2 * i) * q_pow y (2 * k) *
                 (Qinv (q_fact (2 * i)) * Qinv (q_fact (2 * k))))).
  { ring. }
  rewrite Hre.
  rewrite <- (Qinv_mult_distr (q_fact (2 * i)) (q_fact (2 * k))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite <- (qeqT_imp_qeq _ _ (q_pow_add (-1) i k)).
  ring.
Qed.

(* ============================================================ *)
(* D：sin_term i x · sin_term k y == (−1)^{i+k} x^{S(2i)} y^{S(2k)} *)
(*    / ((S(2i))!·(S(2k))!)                                     *)
(* ============================================================ *)
Lemma sc_add_ss_pair : forall (x y : Q) (i k : nat), QeqT (sin_term i x * sin_term k y) (q_pow (-1) (i + k) * (q_pow x (Datatypes.S (2 * i)) * q_pow y (Datatypes.S (2 * k))) *
    Qinv (q_fact (Datatypes.S (2 * i)) * q_fact (Datatypes.S (2 * k)))).
Proof.
  intros x y i k.
  apply qeq_imp_qeqT.
  unfold sin_term. unfold Qdiv.
  assert (Hre : (q_pow (-1) i * (q_pow x (Datatypes.S (2 * i)) * Qinv (q_fact (Datatypes.S (2 * i))))) *
                (q_pow (-1) k * (q_pow y (Datatypes.S (2 * k)) * Qinv (q_fact (Datatypes.S (2 * k))))) ==
                (q_pow (-1) i * q_pow (-1) k) *
                (q_pow x (Datatypes.S (2 * i)) * q_pow y (Datatypes.S (2 * k)) *
                 (Qinv (q_fact (Datatypes.S (2 * i))) * Qinv (q_fact (Datatypes.S (2 * k)))))).
  { ring. }
  rewrite Hre.
  rewrite <- (Qinv_mult_distr (q_fact (Datatypes.S (2 * i))) (q_fact (Datatypes.S (2 * k)))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite <- (qeqT_imp_qeq _ _ (q_pow_add (-1) i k)).
  ring.
Qed.

(* ============================================================ *)
(* Real 层投影形状（加法定理 RHS 的逐点展开）                    *)
(* sin(x+y) == sinX·cosY + cosX·sinY 的 RHS proj n ==            *)
(*   sin_partial n (X n)·cos_partial n (Y n) +                   *)
(*   cos_partial n (X n)·sin_partial n (Y n)                     *)
(* ============================================================ *)
Lemma rs_add_sin_rhs_proj : forall (X Y : Real) (n : nat), QeqT (projT1 (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos Y))
                     (real_mult (cauchy_real_cos X) (cauchy_real_sin Y))) n) (sin_partial n (projT1 X n) * cos_partial n (projT1 Y n) +
  cos_partial n (projT1 X n) * sin_partial n (projT1 Y n)).
Proof.
  intros X Y n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_sin X) (cauchy_real_cos Y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_cos X) (cauchy_real_sin Y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_cos_proj Y n)).
  rewrite (qeqT_imp_qeq _ _ (real_sin_proj X n)).
  rewrite (qeqT_imp_qeq _ _ (real_cos_proj X n)).
  rewrite (qeqT_imp_qeq _ _ (real_sin_proj Y n)).
  reflexivity.
Qed.

(* ============================================================ *)
(* cos(x+y) == cosX·cosY − sinX·sinY 的 RHS proj n ==            *)
(*   cos_partial n (X n)·cos_partial n (Y n) −                   *)
(*   sin_partial n (X n)·sin_partial n (Y n)                     *)
(* ============================================================ *)
Lemma rs_add_cos_rhs_proj : forall (X Y : Real) (n : nat), QeqT (projT1 (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos Y))
                     (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin Y)))) n) (cos_partial n (projT1 X n) * cos_partial n (projT1 Y n) -
  sin_partial n (projT1 X n) * sin_partial n (projT1 Y n)).
Proof.
  intros X Y n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_cos X) (cauchy_real_cos Y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_sin X) (cauchy_real_sin Y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_cos_proj X n)).
  rewrite (qeqT_imp_qeq _ _ (real_cos_proj Y n)).
  rewrite (qeqT_imp_qeq _ _ (real_sin_proj X n)).
  rewrite (qeqT_imp_qeq _ _ (real_sin_proj Y n)).
  reflexivity.
Qed.

Lemma sc_add_neg_sign : forall (j : nat), (1 <= j)%nat ->QeqT (q_pow (-1) j) (- q_pow (-1) (j - 1)).
Proof.
  intros j Hj.
  apply qeq_imp_qeqT.
  assert (HjS : (j = Datatypes.S (j - 1))%nat) by lia.
  rewrite HjS at 1.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (j - 1))).
  ring.
Qed.

(* ============================================================ *)
(* sin 偶片：j ≥ i ⟹  (x+y)^{S(2j)} 展开中 a = 2i 的系数片      *)
(*   == (cos_term i x)·(sin_term (j−i) y)                        *)
(*   (−1)^j·C(S(2j),2i)·x^{2i}·y^{S(2j)−2i} / (S(2j))!           *)
(* ============================================================ *)
Lemma sc_add_sin_even_piece : forall (x y : Q) (j i : nat), (i <= j)%nat ->QeqT (q_pow (-1) j * ((q_choose (Datatypes.S (2 * j)) (2 * i) * q_pow x (2 * i) *
                  q_pow y (Nat.sub (Datatypes.S (2 * j)) (2 * i))) / q_fact (Datatypes.S (2 * j)))) (cos_term i x * sin_term (j - i) y).
Proof.
  intros x y j i Hij.
  apply qeq_imp_qeqT.
  (* LHS：把 C/F 从乘积中抽出（q_choose_div_fact 落点·/ 形对齐世界 S07:1398） *)
  assert (Hr : q_pow (-1) j * ((q_choose (Datatypes.S (2 * j)) (2 * i) * q_pow x (2 * i) *
                               q_pow y (Nat.sub (Datatypes.S (2 * j)) (2 * i))) / q_fact (Datatypes.S (2 * j))) ==
               q_pow (-1) j * (q_pow x (2 * i) * q_pow y (Nat.sub (Datatypes.S (2 * j)) (2 * i))) *
               (q_choose (Datatypes.S (2 * j)) (2 * i) / q_fact (Datatypes.S (2 * j)))).
  { unfold Qdiv. ring. }
  rewrite Hr.
  rewrite (qeqT_imp_qeq _ _ (q_choose_div_fact (Datatypes.S (2 * j)) (2 * i))).
  rewrite <- (Qinv_mult_distr (q_fact (2 * i)) (q_fact (Nat.sub (Datatypes.S (2 * j)) (2 * i)))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite (qeqT_imp_qeq _ _ (sc_add_csin_pair x y i (j - i))).
  assert (Hnat : (Nat.sub (Datatypes.S (2 * j)) (2 * i) = Datatypes.S (2 * (j - i)))%nat) by lia.
  rewrite Hnat.
  assert (Hexp : (i + (j - i) = j)%nat) by lia.
  rewrite Hexp.
  ring.
Qed.

(* ============================================================ *)
(* sin 奇片：j ≥ i ⟹ (x+y)^{S(2j)} 展开中 a = 2i+1 的系数片      *)
(*   == (sin_term i x)·(cos_term (j−i) y)                        *)
(* ============================================================ *)
Lemma sc_add_sin_odd_piece : forall (x y : Q) (j i : nat), (i <= j)%nat ->QeqT (q_pow (-1) j * ((q_choose (Datatypes.S (2 * j)) (Datatypes.S (2 * i)) * q_pow x (Datatypes.S (2 * i)) *
                  q_pow y (Nat.sub (Datatypes.S (2 * j)) (Datatypes.S (2 * i)))) / q_fact (Datatypes.S (2 * j)))) (sin_term i x * cos_term (j - i) y).
Proof.
  intros x y j i Hij.
  apply qeq_imp_qeqT.
  assert (Hr : q_pow (-1) j * ((q_choose (Datatypes.S (2 * j)) (Datatypes.S (2 * i)) * q_pow x (Datatypes.S (2 * i)) *
                               q_pow y (Nat.sub (Datatypes.S (2 * j)) (Datatypes.S (2 * i)))) / q_fact (Datatypes.S (2 * j))) ==
               q_pow (-1) j * (q_pow x (Datatypes.S (2 * i)) * q_pow y (Nat.sub (Datatypes.S (2 * j)) (Datatypes.S (2 * i)))) *
               (q_choose (Datatypes.S (2 * j)) (Datatypes.S (2 * i)) / q_fact (Datatypes.S (2 * j)))).
  { unfold Qdiv. ring. }
  rewrite Hr.
  rewrite (qeqT_imp_qeq _ _ (q_choose_div_fact (Datatypes.S (2 * j)) (Datatypes.S (2 * i)))).
  rewrite <- (Qinv_mult_distr (q_fact (Datatypes.S (2 * i))) (q_fact (Nat.sub (Datatypes.S (2 * j)) (Datatypes.S (2 * i))))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite (qeqT_imp_qeq _ _ (sc_add_sinc_pair x y i (j - i))).
  assert (Hnat : (Nat.sub (Datatypes.S (2 * j)) (Datatypes.S (2 * i)) = 2 * (j - i))%nat) by lia.
  rewrite Hnat.
  assert (Hexp : (i + (j - i) = j)%nat) by lia.
  rewrite Hexp.
  ring.
Qed.

(* ============================================================ *)
(* cos 偶片：j ≥ i ⟹ (x+y)^{2j} 展开中 a = 2i 的系数片           *)
(*   == (cos_term i x)·(cos_term (j−i) y)                        *)
(*   (−1)^j·C(2j,2i)·x^{2i}·y^{2j−2i} / (2j)!                    *)
(* ============================================================ *)
Lemma sc_add_cos_cc_piece : forall (x y : Q) (j i : nat), (i <= j)%nat ->QeqT (q_pow (-1) j * ((q_choose (2 * j) (2 * i) * q_pow x (2 * i) *
                  q_pow y (Nat.sub (2 * j) (2 * i))) / q_fact (2 * j))) (cos_term i x * cos_term (j - i) y).
Proof.
  intros x y j i Hij.
  apply qeq_imp_qeqT.
  assert (Hr : q_pow (-1) j * ((q_choose (2 * j) (2 * i) * q_pow x (2 * i) *
                               q_pow y (Nat.sub (2 * j) (2 * i))) / q_fact (2 * j)) ==
               q_pow (-1) j * (q_pow x (2 * i) * q_pow y (Nat.sub (2 * j) (2 * i))) *
               (q_choose (2 * j) (2 * i) / q_fact (2 * j))).
  { unfold Qdiv. ring. }
  rewrite Hr.
  rewrite (qeqT_imp_qeq _ _ (q_choose_div_fact (2 * j) (2 * i))).
  rewrite <- (Qinv_mult_distr (q_fact (2 * i)) (q_fact (Nat.sub (2 * j) (2 * i)))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite (qeqT_imp_qeq _ _ (sc_add_cc_pair x y i (j - i))).
  assert (Hnat : (Nat.sub (2 * j) (2 * i) = 2 * (j - i))%nat) by lia.
  rewrite Hnat.
  assert (Hexp : (i + (j - i) = j)%nat) by lia.
  rewrite Hexp.
  ring.
Qed.

(* ============================================================ *)
(* cos 奇片：i < j ⟹ (x+y)^{2j} 展开中 a = 2i+1 的系数片         *)
(*   == −(sin_term i x)·(sin_term (j−1−i) y)（负号来自          *)
(*      (−1)^j 与 (−1)^{j−1} 差一个负号）                        *)
(* ============================================================ *)
Lemma sc_add_cos_ss_piece : forall (x y : Q) (j i : nat), (i < j)%nat ->QeqT (q_pow (-1) j * ((q_choose (2 * j) (Datatypes.S (2 * i)) * q_pow x (Datatypes.S (2 * i)) *
                  q_pow y (Nat.sub (2 * j) (Datatypes.S (2 * i)))) / q_fact (2 * j))) (- (sin_term i x * sin_term (j - 1 - i) y)).
Proof.
  intros x y j i Hij.
  apply qeq_imp_qeqT.
  assert (Hr : q_pow (-1) j * ((q_choose (2 * j) (Datatypes.S (2 * i)) * q_pow x (Datatypes.S (2 * i)) *
                               q_pow y (Nat.sub (2 * j) (Datatypes.S (2 * i)))) / q_fact (2 * j)) ==
               q_pow (-1) j * (q_pow x (Datatypes.S (2 * i)) * q_pow y (Nat.sub (2 * j) (Datatypes.S (2 * i)))) *
               (q_choose (2 * j) (Datatypes.S (2 * i)) / q_fact (2 * j))).
  { unfold Qdiv. ring. }
  rewrite Hr.
  rewrite (qeqT_imp_qeq _ _ (q_choose_div_fact (2 * j) (Datatypes.S (2 * i)))).
  rewrite <- (Qinv_mult_distr (q_fact (Datatypes.S (2 * i))) (q_fact (Nat.sub (2 * j) (Datatypes.S (2 * i))))) by (apply q_neq_of_lt; apply q_fact_pos).
  rewrite (qeqT_imp_qeq _ _ (sc_add_ss_pair x y i (j - 1 - i))).
  assert (Hnat : (Nat.sub (2 * j) (Datatypes.S (2 * i)) = Datatypes.S (2 * (j - 1 - i)))%nat) by lia.
  rewrite Hnat.
  assert (Hexp : (i + (j - 1 - i) = j - 1)%nat) by lia.
  rewrite Hexp.
  (* 左符号 (−1)^j == −(−1)^{j−1}：改写左侧（1 ≤ j 由 i < j 推出） *)
  assert (Hj1 : (1 <= j)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sc_add_neg_sign j Hj1)).
  ring.
Qed.

Lemma sc_add_sin_diag_term : forall (x y : Q) (j : nat), QeqT (sin_term j (x + y)) (sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * sin_term (Nat.sub j i) y) +
  sum_upto (Datatypes.S j) (fun i : nat => sin_term i x * cos_term (Nat.sub j i) y)).
Proof.
  intros x y j.
  apply qeq_imp_qeqT.
  unfold sin_term.
  rewrite (qeqT_imp_qeq _ _ (q_binom x y (Datatypes.S (Nat.mul 2 j)))).
  set (F := fun a : nat =>
        q_choose (Datatypes.S (Nat.mul 2 j)) a * q_pow x a *
        q_pow y (Nat.sub (Datatypes.S (Nat.mul 2 j)) a)).
  (* 把 (−1)^j 与 /(2j+1)! 分配进和号 *)
  assert (Hdist : q_pow (-1) j * (sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) F /
                                  q_fact (Datatypes.S (Nat.mul 2 j))) ==
                  sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j)))
                    (fun a : nat => q_pow (-1) j * (F a / q_fact (Datatypes.S (Nat.mul 2 j))))).
  { unfold Qdiv.
    assert (Ha : q_pow (-1) j * (sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) F *
                                 Qinv (q_fact (Datatypes.S (Nat.mul 2 j)))) ==
                 (q_pow (-1) j * sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) F) *
                 Qinv (q_fact (Datatypes.S (Nat.mul 2 j)))). { ring. }
    rewrite Ha.
    assert (Hb : q_pow (-1) j * sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) F ==
                 sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) (fun a : nat => q_pow (-1) j * F a)).
    { rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S (Datatypes.S (Nat.mul 2 j))) (q_pow (-1) j) F)). reflexivity. }
    rewrite Hb.
    assert (Hc : sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) (fun a : nat => q_pow (-1) j * F a) *
                 Qinv (q_fact (Datatypes.S (Nat.mul 2 j))) ==
                 Qinv (q_fact (Datatypes.S (Nat.mul 2 j))) *
                 sum_upto (Datatypes.S (Datatypes.S (Nat.mul 2 j))) (fun a : nat => q_pow (-1) j * F a)).
    { ring. }
    rewrite Hc.
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S (Datatypes.S (Nat.mul 2 j)))
                 (Qinv (q_fact (Datatypes.S (Nat.mul 2 j))))
                 (fun a : nat => q_pow (-1) j * F a))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S (Datatypes.S (Nat.mul 2 j)))
      (fun a : nat => Qinv (q_fact (Datatypes.S (Nat.mul 2 j))) * (q_pow (-1) j * F a))
      (fun a : nat => q_pow (-1) j * (F a * Qinv (q_fact (Datatypes.S (Nat.mul 2 j)))))).
    intros k Hk. apply qeq_imp_qeqT. ring. }
  rewrite Hdist.
  set (G := fun a : nat => q_pow (-1) j * (F a / q_fact (Datatypes.S (Nat.mul 2 j)))).
  (* 偶/奇拆分：Σ_{a=0}^{2j+1} == Σ_{i=0}^{j} 偶 + Σ_{i=0}^{j} 奇 *)
  assert (Hidx : (Datatypes.S (Datatypes.S (Nat.mul 2 j)) = Nat.mul 2 (Datatypes.S j))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (Datatypes.S (Nat.mul 2 j))) (Nat.mul 2 (Datatypes.S j)) G Hidx)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split (Datatypes.S j) G)).
  (* 偶片：G(2i) == cos i x · sin (j−i) y *)
  assert (Heven : sum_upto (Datatypes.S j) (fun i : nat => G (Nat.mul 2 i)) ==
                  sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * sin_term (Nat.sub j i) y)).
  { apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S j)
      (fun i : nat => G (Nat.mul 2 i))
      (fun i : nat => cos_term i x * sin_term (Nat.sub j i) y)).
    intros i Hi. apply NatLe_drop in Hi.
    unfold G, F.
    apply (sc_add_sin_even_piece x y j i). lia. }
  (* 奇片：G(2i+1) == sin i x · cos (j−i) y *)
  assert (Hodd : sum_upto (Datatypes.S j) (fun i : nat => G (Nat.add (Nat.mul 2 i) 1)) ==
                 sum_upto (Datatypes.S j) (fun i : nat => sin_term i x * cos_term (Nat.sub j i) y)).
  { apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S j)
      (fun i : nat => G (Nat.add (Nat.mul 2 i) 1))
      (fun i : nat => sin_term i x * cos_term (Nat.sub j i) y)).
    intros i Hi. apply NatLe_drop in Hi.
    unfold G, F.
    assert (Hrew : (Nat.add (Nat.mul 2 i) 1 = Datatypes.S (Nat.mul 2 i))%nat) by lia.
    rewrite Hrew.
    apply (sc_add_sin_odd_piece x y j i). lia. }
  rewrite Heven. rewrite Hodd. reflexivity.
Qed.

(* ============================================================ *)
(* cos 项对角恒等式：                                          *)
(* cos_term j (x+y) ==                                          *)
(*   Σ_{i=0}^{j} (cos_term i x)·(cos_term (j−i) y) −            *)
(*   Σ_{i=0}^{j−1} (sin_term i x)·(sin_term (j−1−i) y)          *)
(* ============================================================ *)
Lemma sc_add_cos_diag_term : forall (x y : Q) (j : nat), QeqT (cos_term j (x + y)) (sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y) -
  sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y)).
Proof.
  intros x y j.
  apply qeq_imp_qeqT.
  unfold cos_term.
  rewrite (qeqT_imp_qeq _ _ (q_binom x y (Nat.mul 2 j))).
  set (F := fun a : nat =>
        q_choose (Nat.mul 2 j) a * q_pow x a *
        q_pow y (Nat.sub (Nat.mul 2 j) a)).
  (* 把 (−1)^j 与 /(2j)! 分配进和号 *)
  assert (Hdist : q_pow (-1) j * (sum_upto (Datatypes.S (Nat.mul 2 j)) F / q_fact (Nat.mul 2 j)) ==
                  sum_upto (Datatypes.S (Nat.mul 2 j))
                    (fun a : nat => q_pow (-1) j * (F a / q_fact (Nat.mul 2 j)))).
  { unfold Qdiv.
    assert (Ha : q_pow (-1) j * (sum_upto (Datatypes.S (Nat.mul 2 j)) F *
                                 Qinv (q_fact (Nat.mul 2 j))) ==
                 (q_pow (-1) j * sum_upto (Datatypes.S (Nat.mul 2 j)) F) *
                 Qinv (q_fact (Nat.mul 2 j))). { ring. }
    rewrite Ha.
    assert (Hb : q_pow (-1) j * sum_upto (Datatypes.S (Nat.mul 2 j)) F ==
                 sum_upto (Datatypes.S (Nat.mul 2 j)) (fun a : nat => q_pow (-1) j * F a)).
    { rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S (Nat.mul 2 j)) (q_pow (-1) j) F)). reflexivity. }
    rewrite Hb.
    assert (Hc : sum_upto (Datatypes.S (Nat.mul 2 j)) (fun a : nat => q_pow (-1) j * F a) *
                 Qinv (q_fact (Nat.mul 2 j)) ==
                 Qinv (q_fact (Nat.mul 2 j)) *
                 sum_upto (Datatypes.S (Nat.mul 2 j)) (fun a : nat => q_pow (-1) j * F a)).
    { ring. }
    rewrite Hc.
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S (Nat.mul 2 j))
                 (Qinv (q_fact (Nat.mul 2 j)))
                 (fun a : nat => q_pow (-1) j * F a))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S (Nat.mul 2 j))
      (fun a : nat => Qinv (q_fact (Nat.mul 2 j)) * (q_pow (-1) j * F a))
      (fun a : nat => q_pow (-1) j * (F a * Qinv (q_fact (Nat.mul 2 j))))).
    intros k Hk. apply qeq_imp_qeqT. ring. }
  rewrite Hdist.
  set (G := fun a : nat => q_pow (-1) j * (F a / q_fact (Nat.mul 2 j))).
  (* 偶/奇拆分（奇数项数）：Σ_{a=0}^{2j} == Σ_{i=0}^{j} 偶 + Σ_{i=0}^{j−1} 奇 *)
  assert (Hidx : (Datatypes.S (Nat.mul 2 j) = Nat.add (Nat.mul 2 j) 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (Nat.mul 2 j)) (Nat.add (Nat.mul 2 j) 1) G Hidx)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split_odd j G)).
  (* 偶片：G(2i) == cos i x · cos (j−i) y *)
  assert (Heven : sum_upto (j + 1) (fun i : nat => G (Nat.mul 2 i)) ==
                  sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y)).
  { assert (Hidx2 : (j + 1 = Datatypes.S j)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (j + 1) (Datatypes.S j) (fun i : nat => G (Nat.mul 2 i)) Hidx2)).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S j)
      (fun i : nat => G (Nat.mul 2 i))
      (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y)).
    intros i Hi. apply NatLe_drop in Hi.
    unfold G, F.
    apply (sc_add_cos_cc_piece x y j i). lia. }
  (* 奇片：G(2i+1) == −(sin i x · sin (j−1−i) y) *)
  assert (Hodd : sum_upto j (fun i : nat => G (Nat.add (Nat.mul 2 i) 1)) ==
                 - sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y)).
  { rewrite <- (qeqT_imp_qeq _ _ (sum_upto_neg j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext_below j
      (fun i : nat => G (Nat.add (Nat.mul 2 i) 1))
      (fun i : nat => - (sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y))).
    intros i Hi. apply NatLe_drop in Hi.
    unfold G, F.
    assert (Hrew : (Nat.add (Nat.mul 2 i) 1 = Datatypes.S (Nat.mul 2 i))%nat) by lia.
    rewrite Hrew.
    apply (sc_add_cos_ss_piece x y j i). lia. }
  rewrite Heven. rewrite Hodd.
  (* RHS 形状：Σ_even + (−Σ_odd') vs Σ_even − Σ_odd' *)
  assert (Hsub : sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y) +
                 (- sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y)) ==
                 sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y) -
                 sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y)).
  { ring. }
  exact Hsub.
Qed.

(* ============================================================ *)
(* sin 部分和三角展开（三角形双和，指标 j' ≤ J、i ≤ j'）：      *)
(* sin_partial J (x+y) ==                                        *)
(*   Σ_{j'≤J} Σ_{i≤j'} (cos i x)(sin (j'−i) y) +                *)
(*   Σ_{j'≤J} Σ_{i≤j'} (sin i x)(cos (j'−i) y)                  *)
(* ============================================================ *)
Lemma sc_add_sin_partial_diag : forall (x y : Q) (J : nat), QeqT (sin_partial J (x + y)) (sum_upto (Datatypes.S J) (fun j' : nat =>
    sum_upto (Datatypes.S j') (fun i : nat => cos_term i x * sin_term (Nat.sub j' i) y)) +
  sum_upto (Datatypes.S J) (fun j' : nat =>
    sum_upto (Datatypes.S j') (fun i : nat => sin_term i x * cos_term (Nat.sub j' i) y))).
Proof.
  intros x y J.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto J (x + y))).
  rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S J)
    (fun j' : nat => sum_upto (Datatypes.S j') (fun i : nat => cos_term i x * sin_term (Nat.sub j' i) y))
    (fun j' : nat => sum_upto (Datatypes.S j') (fun i : nat => sin_term i x * cos_term (Nat.sub j' i) y)))).
  apply qeqT_imp_qeq.
  apply (sum_upto_ext_below (Datatypes.S J)
    (fun j' : nat => sin_term j' (x + y))
    (fun j' : nat => sum_upto (Datatypes.S j') (fun i : nat => cos_term i x * sin_term (Nat.sub j' i) y) +
                     sum_upto (Datatypes.S j') (fun i : nat => sin_term i x * cos_term (Nat.sub j' i) y))).
  intros j' Hj'.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_add_sin_diag_term x y j')).
  reflexivity.
Qed.

Lemma sc_add_sin_partial_swap : forall (x y : Q) (J : nat), QeqT (sin_partial J (x + y)) (sum_upto (Datatypes.S J) (fun j : nat =>
    sum_upto (Datatypes.S (J - j)) (fun i : nat => cos_term j x * sin_term i y)) +
  sum_upto (Datatypes.S J) (fun j : nat =>
    sum_upto (Datatypes.S (J - j)) (fun i : nat => sin_term j x * cos_term i y))).
Proof.
  intros x y J.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_add_sin_partial_diag x y J)).
  (* 第一族（cos·sin）对角双和 == 三角分离形态 *)
  assert (H1 : sum_upto (Datatypes.S J)
                 (fun j' : nat => sum_upto (Datatypes.S j')
                   (fun i : nat => cos_term i x * sin_term (Nat.sub j' i) y)) ==
               sum_upto (Datatypes.S J)
                 (fun j : nat => sum_upto (Datatypes.S (J - j))
                   (fun i : nat => cos_term j x * sin_term i y))).
  { exact (qeqT_imp_qeq _ _ (exp_cauchy_swap J (fun j : nat => cos_term j x) (fun j : nat => sin_term j y))). }
  (* 第二族（sin·cos）同构 *)
  assert (H2 : sum_upto (Datatypes.S J)
                 (fun j' : nat => sum_upto (Datatypes.S j')
                   (fun i : nat => sin_term i x * cos_term (Nat.sub j' i) y)) ==
               sum_upto (Datatypes.S J)
                 (fun j : nat => sum_upto (Datatypes.S (J - j))
                   (fun i : nat => sin_term j x * cos_term i y))).
  { exact (qeqT_imp_qeq _ _ (exp_cauchy_swap J (fun j : nat => sin_term j x) (fun j : nat => cos_term j y))). }
  rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma sc_add_sin_prod_decomp : forall (x y : Q) (n : nat), QeqT (sin_partial (2 * n) (x + y)) ((sin_partial n x * cos_partial n y + cos_partial n x * sin_partial n y) +
  (sum_upto (Datatypes.S n) (fun j : nat =>
      sum_upto (n - j) (fun k : nat => cos_term j x * sin_term (Datatypes.S n + k)%nat y)) +
   sum_upto n (fun j : nat =>
      sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term (Datatypes.S n + j)%nat x * sin_term i y)) +
   sum_upto (Datatypes.S n) (fun j : nat =>
      sum_upto (n - j) (fun k : nat => sin_term j x * cos_term (Datatypes.S n + k)%nat y)) +
   sum_upto n (fun j : nat =>
      sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term (Datatypes.S n + j)%nat x * cos_term i y)))).
Proof.
  intros x y n.
  apply qeq_imp_qeqT.
  (* 1. LHS → 三角分离双和（q1） *)
  rewrite (qeqT_imp_qeq _ _ (sc_add_sin_partial_swap x y (2 * n))).
  (* 2a. cos·sin 族：tri1 == sq1 + top1 + right1（exp_trunc_decomp 实例） *)
  assert (HT1 :
    sum_upto (Datatypes.S (2 * n)) (fun j : nat =>
      sum_upto (Datatypes.S (2 * n - j)) (fun i : nat => cos_term j x * sin_term i y)) ==
    sum_upto (Datatypes.S n) (fun j : nat =>
      sum_upto (Datatypes.S n) (fun i : nat => cos_term j x * sin_term i y)) +
    (sum_upto (Datatypes.S n) (fun j : nat =>
       sum_upto (n - j) (fun k : nat => cos_term j x * sin_term (Datatypes.S n + k)%nat y)) +
     sum_upto n (fun j : nat =>
       sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term (Datatypes.S n + j)%nat x * sin_term i y)))).
  { pose proof (exp_trunc_decomp n (fun j : nat => cos_term j x) (fun j : nat => sin_term j y)) as Hd.
    transitivity (sum_upto (Datatypes.S (2 * n)) (fun j : nat =>
                    sum_upto (Datatypes.S (2 * n - j)) (fun i : nat => cos_term j x * sin_term i y)) -
                  sum_upto (Datatypes.S n) (fun j : nat =>
                    sum_upto (Datatypes.S n) (fun i : nat => cos_term j x * sin_term i y)) +
                  sum_upto (Datatypes.S n) (fun j : nat =>
                    sum_upto (Datatypes.S n) (fun i : nat => cos_term j x * sin_term i y))).
    - ring.
    - rewrite (qeqT_imp_qeq _ _ Hd). ring. }
  (* 2b. sin·cos 族：tri2 == sq2 + top2 + right2 *)
  assert (HT2 :
    sum_upto (Datatypes.S (2 * n)) (fun j : nat =>
      sum_upto (Datatypes.S (2 * n - j)) (fun i : nat => sin_term j x * cos_term i y)) ==
    sum_upto (Datatypes.S n) (fun j : nat =>
      sum_upto (Datatypes.S n) (fun i : nat => sin_term j x * cos_term i y)) +
    (sum_upto (Datatypes.S n) (fun j : nat =>
       sum_upto (n - j) (fun k : nat => sin_term j x * cos_term (Datatypes.S n + k)%nat y)) +
     sum_upto n (fun j : nat =>
       sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term (Datatypes.S n + j)%nat x * cos_term i y)))).
  { pose proof (exp_trunc_decomp n (fun j : nat => sin_term j x) (fun j : nat => cos_term j y)) as Hd.
    transitivity (sum_upto (Datatypes.S (2 * n)) (fun j : nat =>
                    sum_upto (Datatypes.S (2 * n - j)) (fun i : nat => sin_term j x * cos_term i y)) -
                  sum_upto (Datatypes.S n) (fun j : nat =>
                    sum_upto (Datatypes.S n) (fun i : nat => sin_term j x * cos_term i y)) +
                  sum_upto (Datatypes.S n) (fun j : nat =>
                    sum_upto (Datatypes.S n) (fun i : nat => sin_term j x * cos_term i y))).
    - ring.
    - rewrite (qeqT_imp_qeq _ _ Hd). ring. }
  rewrite HT1. rewrite HT2.
  (* 3. 方块 == 乘积（sum_upto_prod + partial_upto 桥） *)
  assert (HsqA :
    sum_upto (Datatypes.S n) (fun j : nat =>
      sum_upto (Datatypes.S n) (fun i : nat => cos_term j x * sin_term i y)) ==
    cos_partial n x * sin_partial n y).
  { apply Qeq_sym.
    rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n x)).
    rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n y)).
    exact (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun j : nat => cos_term j x) (fun j : nat => sin_term j y))). }
  assert (HsqB :
    sum_upto (Datatypes.S n) (fun j : nat =>
      sum_upto (Datatypes.S n) (fun i : nat => sin_term j x * cos_term i y)) ==
    sin_partial n x * cos_partial n y).
  { apply Qeq_sym.
    rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n x)).
    rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n y)).
    exact (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun j : nat => sin_term j x) (fun j : nat => cos_term j y))). }
  rewrite <- HsqB. rewrite <- HsqA.
  ring.
Qed.

Lemma sc_band_top_FT : forall (f g : nat -> Q) (n : nat),
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => f j * g (Datatypes.S n + k)%nat))))
      ((sum_upto (Datatypes.S n) (fun i : nat => Qabs (f i))) *
       (sum_upto n (fun m : nat => Qabs (g (Datatypes.S n + m)%nat)))).
Proof.
  intros f g n.
  apply Qle_to_QleT'.
  set (F := sum_upto (Datatypes.S n) (fun i : nat => Qabs (f i))).
  set (T := sum_upto n (fun m : nat => Qabs (g (Datatypes.S n + m)%nat))).
  set (G := fun j : nat => sum_upto (n - j) (fun k : nat => f j * g (Datatypes.S n + k)%nat)).
  change (Qle (Qabs (sum_upto (Datatypes.S n) G)) (F * T)).
  assert (Htri : Qle (Qabs (sum_upto (Datatypes.S n) G))
                    (sum_upto (Datatypes.S n) (fun j => Qabs (G j)))).
  { unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le. }
  assert (Hper : forall j : nat, (j <= n)%nat ->
    Qle (Qabs (G j)) (Qabs (f j) * sum_upto (n - j) (fun k => Qabs (g (Datatypes.S n + k)%nat)))).
  { intros j Hj.
    apply (Qle_trans _ (sum_upto (n - j) (fun k => Qabs (f j * g (Datatypes.S n + k)%nat))) _).
    - unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le.
    - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      transitivity (sum_upto (n - j) (fun k => Qabs (f j) * Qabs (g (Datatypes.S n + k)%nat))).
      + apply qeqT_imp_qeq.
        apply (sum_upto_ext (n - j)
          (fun k => Qabs (f j * g (Datatypes.S n + k)%nat))
          (fun k => Qabs (f j) * Qabs (g (Datatypes.S n + k)%nat))).
        intro k. apply qeq_imp_qeqT. apply Qabs_Qmult.
      + apply qeqT_imp_qeq.
        apply (sum_upto_scale (n - j) (Qabs (f j))
          (fun k => Qabs (g (Datatypes.S n + k)%nat))). }
  assert (HwT : forall j : nat, (j <= n)%nat ->
    Qle (sum_upto (n - j) (fun k => Qabs (g (Datatypes.S n + k)%nat))) T).
  { intros j Hj. unfold T.
    apply QleT'_to_Qle. apply (sc_sum_shift_sub_le 0 (n - j) n (fun m => Qabs (g (Datatypes.S n + m)%nat))).
    - intro m. apply Qabs_nonneg.
    - lia. }
  apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j => Qabs (G j))) _).
  - exact Htri.
  - apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j => Qabs (f j) * T)) _).
    + apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S n) (fun j => Qabs (G j)) (fun j => Qabs (f j) * T)).
      intros j Hj. apply NatLe_drop in Hj. apply Qle_to_QleT'.
      apply (Qle_trans _ (Qabs (f j) * sum_upto (n - j) (fun k => Qabs (g (Datatypes.S n + k)%nat))) _).
      2: { apply (Qle_trans _ (sum_upto (n - j) (fun k => Qabs (g (Datatypes.S n + k)%nat)) * Qabs (f j)) _).
           2: { apply (Qle_trans _ (T * Qabs (f j)) _).
                2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qeq_sym _ _ (Qmult_comm (Qabs (f j)) T)). }
                apply (Qmult_le_compat_r (sum_upto (n - j) (fun k => Qabs (g (Datatypes.S n + k)%nat))) T (Qabs (f j))).
                - apply (HwT j). lia.
                - apply Qabs_nonneg. }
           apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (f j))
              (sum_upto (n - j) (fun k => Qabs (g (Datatypes.S n + k)%nat)))). }
      apply (Hper j). lia.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      transitivity (T * sum_upto (Datatypes.S n) (fun i => Qabs (f i))).
      * transitivity (sum_upto (Datatypes.S n) (fun j => T * Qabs (f j))).
        -- apply qeqT_imp_qeq.
           apply (sum_upto_ext (Datatypes.S n) (fun j => Qabs (f j) * T) (fun j => T * Qabs (f j))).
           intro j. apply qeq_imp_qeqT. apply Qmult_comm.
        -- exact (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S n) T (fun i => Qabs (f i)))).
      * unfold F. apply Qmult_comm.
Qed.

(* ---- 泛型右带界：|Σ_{j<n}Σ_{i≤2n−Sn−j} f(Sn+j)·g i| ≤ Fr·U ---- *)
Lemma sc_band_right_FT : forall (f g : nat -> Q) (n : nat),
  QleT' (Qabs (sum_upto n (fun j : nat =>
        sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => f (Datatypes.S n + j)%nat * g i))))
      ((sum_upto n (fun m : nat => Qabs (f (Datatypes.S n + m)%nat))) *
       (sum_upto n (fun i : nat => Qabs (g i)))).
Proof.
  intros f g n.
  apply Qle_to_QleT'.
  set (Fr := sum_upto n (fun m : nat => Qabs (f (Datatypes.S n + m)%nat))).
  set (U := sum_upto n (fun i : nat => Qabs (g i))).
  set (G := fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j))
                  (fun i : nat => f (Datatypes.S n + j)%nat * g i)).
  change (Qle (Qabs (sum_upto n G)) (Fr * U)).
  assert (Htri : Qle (Qabs (sum_upto n G)) (sum_upto n (fun j => Qabs (G j)))).
  { unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le. }
  assert (Hper : forall j : nat, (j < n)%nat ->
    Qle (Qabs (G j)) (Qabs (f (Datatypes.S n + j)%nat) * sum_upto (Datatypes.S (2 * n - Datatypes.S n - j))
                        (fun i => Qabs (g i)))).
  { intros j Hj.
    apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j))
                        (fun i => Qabs (f (Datatypes.S n + j)%nat * g i))) _).
    - unfold G. apply QleT'_to_Qle. apply sum_upto_abs_le.
    - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      transitivity (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j))
                      (fun i => Qabs (f (Datatypes.S n + j)%nat) * Qabs (g i))).
      + apply qeqT_imp_qeq.
        apply (sum_upto_ext (Datatypes.S (2 * n - Datatypes.S n - j))
          (fun i => Qabs (f (Datatypes.S n + j)%nat * g i))
          (fun i => Qabs (f (Datatypes.S n + j)%nat) * Qabs (g i))).
        intro i. apply qeq_imp_qeqT. apply Qabs_Qmult.
      + apply (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S (2 * n - Datatypes.S n - j))
          (Qabs (f (Datatypes.S n + j)%nat)) (fun i => Qabs (g i)))). }
  assert (HwU : forall j : nat, (j < n)%nat ->
    Qle (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => Qabs (g i))) U).
  { intros j Hj. unfold U.
    assert (Hcnt : (Datatypes.S (2 * n - Datatypes.S n - j) = n - j)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (2 * n - Datatypes.S n - j)) (n - j) (fun i => Qabs (g i)) Hcnt)).
    apply QleT'_to_Qle. apply (sc_sum_shift_sub_le 0 (n - j) n (fun m => Qabs (g m))).
    - intro m. apply Qabs_nonneg.
    - lia. }
  apply (Qle_trans _ (sum_upto n (fun j => Qabs (G j))) _).
  - exact Htri.
  - apply (Qle_trans _ (sum_upto n (fun j => Qabs (f (Datatypes.S n + j)%nat) * U)) _).
    + apply QleT'_to_Qle. apply (sum_upto_le_ext n (fun j => Qabs (G j)) (fun j => Qabs (f (Datatypes.S n + j)%nat) * U)).
      intros j Hj. apply NatLe_drop in Hj. apply Qle_to_QleT'.
      apply (Qle_trans _ (Qabs (f (Datatypes.S n + j)%nat) *
                          sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => Qabs (g i))) _).
      2: { apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => Qabs (g i)) *
                              Qabs (f (Datatypes.S n + j)%nat)) _).
           2: { apply (Qle_trans _ (U * Qabs (f (Datatypes.S n + j)%nat)) _).
                2: { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qeq_sym _ _ (Qmult_comm (Qabs (f (Datatypes.S n + j)%nat)) U)). }
                apply (Qmult_le_compat_r (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => Qabs (g i)))
                                         U (Qabs (f (Datatypes.S n + j)%nat))).
                - apply (HwU j). exact Hj.
                - apply Qabs_nonneg. }
           apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (f (Datatypes.S n + j)%nat))
              (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i => Qabs (g i)))). }
      apply (Hper j). lia.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      transitivity (U * sum_upto n (fun m => Qabs (f (Datatypes.S n + m)%nat))).
      * transitivity (sum_upto n (fun m => U * Qabs (f (Datatypes.S n + m)%nat))).
        -- apply qeqT_imp_qeq.
           apply (sum_upto_ext n (fun m => Qabs (f (Datatypes.S n + m)%nat) * U)
                                (fun m => U * Qabs (f (Datatypes.S n + m)%nat))).
           intro m. apply qeq_imp_qeqT. apply Qmult_comm.
        -- exact (qeqT_imp_qeq _ _ (sum_upto_scale n U (fun m => Qabs (f (Datatypes.S n + m)%nat)))).
      * unfold Fr. apply Qmult_comm.
Qed.

(* ---- 实例化：q2 分解的四条带 ---- *)
(* 上带 cos·sin *)
Lemma sc_add_band_top_cs_le : forall (x y : Q) (n : nat),
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => cos_term j x * sin_term (Datatypes.S n + k)%nat y))))
      ((sum_upto (Datatypes.S n) (fun i : nat => Qabs (cos_term i x))) *
       (sum_upto n (fun m : nat => Qabs (sin_term (Datatypes.S n + m)%nat y)))).
Proof.
  intros x y n.
  apply Qle_to_QleT'.
  exact (QleT'_to_Qle _ _ (sc_band_top_FT (fun j : nat => cos_term j x) (fun j : nat => sin_term j y) n)).
Qed.

(* 上带 sin·cos *)
Lemma sc_add_band_top_sc_le : forall (x y : Q) (n : nat),
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => sin_term j x * cos_term (Datatypes.S n + k)%nat y))))
      ((sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i x))) *
       (sum_upto n (fun m : nat => Qabs (cos_term (Datatypes.S n + m)%nat y)))).
Proof.
  intros x y n.
  apply Qle_to_QleT'.
  exact (QleT'_to_Qle _ _ (sc_band_top_FT (fun j : nat => sin_term j x) (fun j : nat => cos_term j y) n)).
Qed.

(* 右带 cos·sin *)
Lemma sc_add_band_right_cs_le : forall (x y : Q) (n : nat),
  QleT' (Qabs (sum_upto n (fun j : nat =>
        sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term (Datatypes.S n + j)%nat x * sin_term i y))))
      ((sum_upto n (fun m : nat => Qabs (cos_term (Datatypes.S n + m)%nat x))) *
       (sum_upto n (fun i : nat => Qabs (sin_term i y)))).
Proof.
  intros x y n.
  apply Qle_to_QleT'.
  exact (QleT'_to_Qle _ _ (sc_band_right_FT (fun j : nat => cos_term j x) (fun j : nat => sin_term j y) n)).
Qed.

(* 右带 sin·cos *)
Lemma sc_add_band_right_sc_le : forall (x y : Q) (n : nat),
  QleT' (Qabs (sum_upto n (fun j : nat =>
        sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term (Datatypes.S n + j)%nat x * cos_term i y))))
      ((sum_upto n (fun m : nat => Qabs (sin_term (Datatypes.S n + m)%nat x))) *
       (sum_upto n (fun i : nat => Qabs (cos_term i y)))).
Proof.
  intros x y n.
  apply Qle_to_QleT'.
  exact (QleT'_to_Qle _ _ (sc_band_right_FT (fun j : nat => sin_term j x) (fun j : nat => cos_term j y) n)).
Qed.

Lemma sc_add_sin_err_band_le : forall (x y : Q) (n : nat),
  QleT' (Qabs (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y -
             cos_partial n x * sin_partial n y))
      ((((sum_upto (Datatypes.S n) (fun i => Qabs (cos_term i x))) *
         (sum_upto n (fun m => Qabs (sin_term (Datatypes.S n + m)%nat y)))) +
        ((sum_upto n (fun m => Qabs (cos_term (Datatypes.S n + m)%nat x))) *
         (sum_upto n (fun i => Qabs (sin_term i y))))) +
       (((sum_upto (Datatypes.S n) (fun i => Qabs (sin_term i x))) *
         (sum_upto n (fun m => Qabs (cos_term (Datatypes.S n + m)%nat y)))) +
        ((sum_upto n (fun m => Qabs (sin_term (Datatypes.S n + m)%nat x))) *
         (sum_upto n (fun i => Qabs (cos_term i y)))))).
Proof.
  intros x y n.
  apply Qle_to_QleT'.
  (* 1. 误差 == 4 带（q2 分解 + ring 对消 P） *)
  assert (Hqq :
    (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y -
     cos_partial n x * sin_partial n y) ==
    ((sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => cos_term j x * sin_term (Datatypes.S n + k)%nat y)) +
      sum_upto n (fun j : nat =>
        sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term (Datatypes.S n + j)%nat x * sin_term i y))) +
     sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => sin_term j x * cos_term (Datatypes.S n + k)%nat y))) +
    sum_upto n (fun j : nat =>
      sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term (Datatypes.S n + j)%nat x * cos_term i y))).
  { rewrite (qeqT_imp_qeq _ _ (sc_add_sin_prod_decomp x y n)). ring. }
  apply QleT'_to_Qle. apply (sc_qabs_qeq_le _ _ _ Hqq).
  (* 2. 命名四带与四界（set；body 与 q3/q2 文本一致，转换即可） *)
  set (b1 := sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => cos_term j x * sin_term (Datatypes.S n + k)%nat y))).
  set (b2 := sum_upto n (fun j : nat =>
        sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term (Datatypes.S n + j)%nat x * sin_term i y))).
  set (b3 := sum_upto (Datatypes.S n) (fun j : nat =>
        sum_upto (n - j) (fun k : nat => sin_term j x * cos_term (Datatypes.S n + k)%nat y))).
  set (b4 := sum_upto n (fun j : nat =>
        sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term (Datatypes.S n + j)%nat x * cos_term i y))).
  set (F1 := sum_upto (Datatypes.S n) (fun i => Qabs (cos_term i x))).
  set (T1 := sum_upto n (fun m => Qabs (sin_term (Datatypes.S n + m)%nat y))).
  set (F2 := sum_upto n (fun m => Qabs (cos_term (Datatypes.S n + m)%nat x))).
  set (U2 := sum_upto n (fun i => Qabs (sin_term i y))).
  set (F3 := sum_upto (Datatypes.S n) (fun i => Qabs (sin_term i x))).
  set (T3 := sum_upto n (fun m => Qabs (cos_term (Datatypes.S n + m)%nat y))).
  set (F4 := sum_upto n (fun m => Qabs (sin_term (Datatypes.S n + m)%nat x))).
  set (U4 := sum_upto n (fun i => Qabs (cos_term i y))).
  change (Qle (Qabs ((((b1 + b2) + b3) + b4))) ((F1 * T1 + F2 * U2) + (F3 * T3 + F4 * U4))).
  (* 3. |Σ4带| ≤ Σ|带| *)
  assert (Ht1 : Qle (Qabs (((b1 + b2) + b3) + b4)) (Qabs ((b1 + b2) + b3) + Qabs b4)) by (apply Qabs_triangle).
  assert (Ht2 : Qle (Qabs ((b1 + b2) + b3)) (Qabs (b1 + b2) + Qabs b3)) by (apply Qabs_triangle).
  assert (Ht3 : Qle (Qabs (b1 + b2)) (Qabs b1 + Qabs b2)) by (apply Qabs_triangle).
  assert (Htri : Qle (Qabs (((b1 + b2) + b3) + b4)) (((Qabs b1 + Qabs b2) + Qabs b3) + Qabs b4)).
  { apply (Qle_trans _ (Qabs ((b1 + b2) + b3) + Qabs b4) _);
    [ exact Ht1 |
      apply (Qle_trans _ ((Qabs (b1 + b2) + Qabs b3) + Qabs b4) _);
      [ apply (Qplus_le_compat (Qabs ((b1 + b2) + b3)) (Qabs (b1 + b2) + Qabs b3) (Qabs b4) (Qabs b4));
        [ exact Ht2 | apply Qle_refl ] |
        apply (Qplus_le_compat (Qabs (b1 + b2) + Qabs b3) ((Qabs b1 + Qabs b2) + Qabs b3) (Qabs b4) (Qabs b4));
        [ apply (Qplus_le_compat (Qabs (b1 + b2)) (Qabs b1 + Qabs b2) (Qabs b3) (Qabs b3));
          [ exact Ht3 | apply Qle_refl ] |
          apply Qle_refl ] ] ]. }
  apply (Qle_trans _ (Qabs b1 + Qabs b2 + Qabs b3 + Qabs b4) _).
  - exact Htri.
  - (* Σ|带| ≤ Σ F·T：四条带界 *)
    assert (H1 : Qle (Qabs b1) (F1 * T1)).
    { exact (QleT'_to_Qle _ _ (sc_add_band_top_cs_le x y n)). }
    assert (H2 : Qle (Qabs b2) (F2 * U2)).
    { exact (QleT'_to_Qle _ _ (sc_add_band_right_cs_le x y n)). }
    assert (H3 : Qle (Qabs b3) (F3 * T3)).
    { exact (QleT'_to_Qle _ _ (sc_add_band_top_sc_le x y n)). }
    assert (H4 : Qle (Qabs b4) (F4 * U4)).
    { exact (QleT'_to_Qle _ _ (sc_add_band_right_sc_le x y n)). }
    apply (Qle_trans _ ((Qabs b1 + Qabs b2) + (Qabs b3 + Qabs b4)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((F1 * T1 + F2 * U2) + (F3 * T3 + F4 * U4)) _).
      * apply Qplus_le_compat.
        -- apply Qplus_le_compat; assumption.
        -- apply Qplus_le_compat; assumption.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.


(* ============================================================ *)
(* SC-2 批 7（并入 198）：sin 加法定理 Real 层（sE 论证）      *)
(*   Q 层模量链 15 条 + rs_add_sin（Real 层 sin(x+y)）        *)
(*   子代理 sE 产出（审查并入）                              *)
(* ============================================================ *)

Lemma sc_add_sin_diag_swap : forall (x y : Q) (J : nat), QeqT (sin_partial J (x + y)) (sum_upto (Datatypes.S J) (fun i : nat => sum_upto (Datatypes.S (Nat.sub J i)) (fun k : nat => cos_term i x * sin_term k y)) +
  sum_upto (Datatypes.S J) (fun i : nat => sum_upto (Datatypes.S (Nat.sub J i)) (fun k : nat => sin_term i x * cos_term k y))).
Proof.
  intros x y J.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_add_sin_partial_diag x y J)).
  setoid_rewrite (qeqT_imp_qeq _ _ (exp_cauchy_swap J (fun i : nat => cos_term i x) (fun k : nat => sin_term k y))).
  setoid_rewrite (qeqT_imp_qeq _ _ (exp_cauchy_swap J (fun i : nat => sin_term i x) (fun k : nat => cos_term k y))).
  reflexivity.
Qed.

(* ============================================================ *)
(* L2：乘积方块（sin·cos）：sp n x · cp n y == Σ_{i,k≤n} s_i c_k *)
(* ============================================================ *)
Lemma sc_add_sinc_prod_sq : forall (x y : Q) (n : nat), QeqT (sin_partial n x * cos_partial n y) (sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * cos_term k y))).
Proof.
intros x y n. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n x)). rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n y)). exact (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun i : nat => sin_term i x) (fun k : nat => cos_term k y))).
Qed.

(* ============================================================ *)
(* L3：乘积方块（cos·sin）：cp n x · sp n y == Σ_{i,k≤n} c_i s_k *)
(* ============================================================ *)
Lemma sc_add_csin_prod_sq : forall (x y : Q) (n : nat), QeqT (cos_partial n x * sin_partial n y) (sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => cos_term i x * sin_term k y))).
Proof.
intros x y n. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n x)). rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n y)). exact (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun i : nat => cos_term i x) (fun k : nat => sin_term k y))).
Qed.

(* ============================================================ *)
(* L4a：泛型族精确分解（三角 cap 2n − 方块 cap n == 上带 + 右带）*)
(*   直接 = exp_trunc_decomp（exp 论证泛型件，原样应用）          *)
(* ============================================================ *)
Lemma sc_add_fam_decomp : forall (A B : nat -> Q) (n : nat), QeqT (sum_upto (Datatypes.S (2 * n)) (fun i : nat => sum_upto (Datatypes.S (2 * n - i)) (fun k : nat => A i * B k)) -
  sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => A i * B k))) (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat))) +
  sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i))).
Proof.
  intros A B n.
  apply qeq_imp_qeqT.
  exact (qeqT_imp_qeq _ _ (exp_trunc_decomp n A B)).
Qed.

(* ============================================================ *)
(* L4：sin 误差精确分解                                         *)
(*   sin_{2n}(x+y) − sp_n cp_n − cp_n sp_n ==                   *)
(*     decomp(c(x), s(y)) + decomp(s(x), c(y))                  *)
(* ============================================================ *)
Lemma sc_add_sin_err_decomp : forall (x y : Q) (n : nat), QeqT (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y - cos_partial n x * sin_partial n y) ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
   sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * sin_term i y))) +
  (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
   sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * cos_term i y)))).
Proof.
  intros x y n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_add_sin_diag_swap x y (2 * n))).
  rewrite (qeqT_imp_qeq _ _ (sc_add_csin_prod_sq x y n)).
  rewrite (qeqT_imp_qeq _ _ (sc_add_sinc_prod_sq x y n)).
  (* 目标：(Tcs + Tsc) − Ssc − Scs == D1 + D2；重组为 (Tcs−Scs) + (Tsc−Ssc) *)
  transitivity ((sum_upto (Datatypes.S (2 * n)) (fun i : nat => sum_upto (Datatypes.S (2 * n - i)) (fun k : nat => cos_term i x * sin_term k y)) -
                 sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => cos_term i x * sin_term k y))) +
                (sum_upto (Datatypes.S (2 * n)) (fun i : nat => sum_upto (Datatypes.S (2 * n - i)) (fun k : nat => sin_term i x * cos_term k y)) -
                 sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * cos_term k y)))).
  { ring. }
  rewrite (qeqT_imp_qeq _ _ (sc_add_fam_decomp (fun i : nat => cos_term i x) (fun k : nat => sin_term k y) n)).
  rewrite (qeqT_imp_qeq _ _ (sc_add_fam_decomp (fun i : nat => sin_term i x) (fun k : nat => cos_term k y) n)).
  reflexivity.
Qed.

(* ============================================================ *)
(* L5 辅助 a：前缀和 ≤ 全和（m ≤ n、逐项非负）                  *)
(* ============================================================ *)
Lemma sc_sum_head_le : forall (m n : nat) (f : nat -> Q), (m <= n)%nat ->
  (forall i : nat, Qle 0 (f i)) -> QleT' (sum_upto m f) (sum_upto n f).
Proof.
  intros m n f Hmn Hf.
  apply Qle_to_QleT'.
  assert (Hadd : (n = m + (n - m))%nat) by lia.
  rewrite Hadd.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_add m (n - m) f)).
  apply (Qle_plus_nonneg_r (sum_upto m f) (sum_upto (n - m) (fun k : nat => f ((m + k)%nat)))).
  apply QleT'_to_Qle. apply sc_sum_nonneg.
  intro k. exact (Hf ((m + k)%nat)).
Qed.

(* ============================================================ *)
(* L5 辅助 b：上带逐行 |Σ_{k<n−j} A_j·B_{S n+k}| ≤ |A_j|·TB      *)
(* ============================================================ *)
Lemma sc_add_up_row_abs : forall (A B : nat -> Q) (n j : nat), (j <= n)%nat ->
  QleT' (Qabs (sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat))))
      (Qabs (A j) * sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat)))).
Proof.
  intros A B n j Hj.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (n - j) (fun k : nat => Qabs (A j * B ((Datatypes.S n + k)%nat)))) _).
  - apply QleT'_to_Qle. apply sum_upto_abs_le.
  - apply (Qle_trans _ (sum_upto n (fun k : nat => Qabs (A j) * Qabs (B ((Datatypes.S n + k)%nat)))) _).
    + apply (Qle_trans _ (sum_upto (n - j) (fun k : nat => Qabs (A j) * Qabs (B ((Datatypes.S n + k)%nat)))) _).
      * apply QleT'_to_Qle. apply (sum_upto_le_ext (n - j)
          (fun k : nat => Qabs (A j * B ((Datatypes.S n + k)%nat)))
          (fun k : nat => Qabs (A j) * Qabs (B ((Datatypes.S n + k)%nat)))).
        intros k Hk. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
      * apply QleT'_to_Qle. apply (sc_sum_head_le (n - j) n (fun k : nat => Qabs (A j) * Qabs (B ((Datatypes.S n + k)%nat)))).
        -- lia.
        -- intro i.
           apply (Qmult_le_0_compat (Qabs (A j)) (Qabs (B ((Datatypes.S n + i)%nat)))).
           ++ apply Qabs_nonneg.
           ++ apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (sum_upto_scale n (Qabs (A j)) (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))))).
      ring.
Qed.

(* ============================================================ *)
(* L5 辅助 c：右带逐行 |Σ_{i<Sn−j} A_{S n+j}·B_i| ≤ |A_{S n+j}|·FB *)
(* ============================================================ *)
Lemma sc_add_rb_row_abs : forall (A B : nat -> Q) (n j : nat), (j < n)%nat ->
  QleT' (Qabs (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i)))
      (Qabs (A ((Datatypes.S n + j)%nat)) * sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i))).
Proof.
  intros A B n j Hj.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => Qabs (A ((Datatypes.S n + j)%nat) * B i))) _).
  - apply QleT'_to_Qle. apply sum_upto_abs_le.
  - apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat => Qabs (A ((Datatypes.S n + j)%nat)) * Qabs (B i))) _).
    + apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j))
                            (fun i : nat => Qabs (A ((Datatypes.S n + j)%nat)) * Qabs (B i))) _).
      * apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S (2 * n - Datatypes.S n - j))
          (fun i : nat => Qabs (A ((Datatypes.S n + j)%nat) * B i))
          (fun i : nat => Qabs (A ((Datatypes.S n + j)%nat)) * Qabs (B i))).
        intros i Hi. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
      * apply QleT'_to_Qle. apply (sc_sum_head_le (Datatypes.S (2 * n - Datatypes.S n - j)) (Datatypes.S n)
                 (fun i : nat => Qabs (A ((Datatypes.S n + j)%nat)) * Qabs (B i))).
        -- lia.
        -- intro i.
           apply (Qmult_le_0_compat (Qabs (A ((Datatypes.S n + j)%nat))) (Qabs (B i))).
           ++ apply Qabs_nonneg.
           ++ apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S n) (Qabs (A ((Datatypes.S n + j)%nat))) (fun i : nat => Qabs (B i)))).
      ring.
Qed.

(* ============================================================ *)
(* L5：泛型带（上带 + 右带）绝对值界                            *)
(*   |up(A,B) + r(A,B)| ≤ FA·TB + TA·FB                          *)
(* ============================================================ *)
Lemma sc_add_band_abs : forall (A B : nat -> Q) (n : nat),
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat))) +
             sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i))))
      ((sum_upto (Datatypes.S n) (fun j : nat => Qabs (A j))) *
         (sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat)))) +
       (sum_upto n (fun j : nat => Qabs (A ((Datatypes.S n + j)%nat)))) *
         (sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)))).
Proof.
  intros A B n.
  apply Qle_to_QleT'.
  set (TB := sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat)))).
  set (FA := sum_upto (Datatypes.S n) (fun j : nat => Qabs (A j))).
  set (TA := sum_upto n (fun j : nat => Qabs (A ((Datatypes.S n + j)%nat)))).
  set (FB := sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i))).
  (* |up + r| ≤ |up| + |r| *)
  apply (Qle_trans _ (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat)))) +
                     Qabs (sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i)))) _).
  - apply Qabs_triangle.
  - unfold TB, FA, TA, FB.
    apply Qplus_le_compat.
    + (* |up| ≤ FA·TB *)
      apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j : nat =>
                 Qabs (sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat))))) _).
      * apply QleT'_to_Qle. apply sum_upto_abs_le.
      * apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun j : nat =>
                 Qabs (A j) * sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))))) _).
        -- apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S n)
             (fun j : nat => Qabs (sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat))))
             (fun j : nat => Qabs (A j) * sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))))).
           intros j Hj. apply NatLe_drop in Hj. apply (sc_add_up_row_abs A B n j). lia.
        -- apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
           assert (Hpre : forall j : nat, QeqT (Qabs (A j) * sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat)))) (sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))) * Qabs (A j))).
           { intro j. apply qeq_imp_qeqT. ring. }
           rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (Datatypes.S n)
             (fun j : nat => Qabs (A j) * sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))))
             (fun j : nat => sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))) * Qabs (A j)) Hpre)).
           rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (Datatypes.S n)
                     (sum_upto n (fun k : nat => Qabs (B ((Datatypes.S n + k)%nat))))
                     (fun j : nat => Qabs (A j)))).
           ring.
    + (* |r| ≤ TA·FB *)
      apply (Qle_trans _ (sum_upto n (fun j : nat =>
                 Qabs (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i)))) _).
      * apply QleT'_to_Qle. apply sum_upto_abs_le.
      * apply (Qle_trans _ (sum_upto n (fun j : nat =>
                 Qabs (A ((Datatypes.S n + j)%nat)) * sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)))) _).
        -- apply QleT'_to_Qle. apply (sum_upto_le_ext n
             (fun j : nat => Qabs (sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i)))
             (fun j : nat => Qabs (A ((Datatypes.S n + j)%nat)) * sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)))).
           intros j Hj. apply NatLe_drop in Hj. apply (sc_add_rb_row_abs A B n j). lia.
        -- apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
           assert (Hpre2 : forall j : nat, QeqT (Qabs (A ((Datatypes.S n + j)%nat)) * sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i))) (sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)) * Qabs (A ((Datatypes.S n + j)%nat)))).
           { intro j. apply qeq_imp_qeqT. ring. }
           rewrite (qeqT_imp_qeq _ _ (sum_upto_ext n
             (fun j : nat => Qabs (A ((Datatypes.S n + j)%nat)) * sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)))
             (fun j : nat => sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)) * Qabs (A ((Datatypes.S n + j)%nat))) Hpre2)).
           rewrite (qeqT_imp_qeq _ _ (sum_upto_scale n
                     (sum_upto (Datatypes.S n) (fun i : nat => Qabs (B i)))
                     (fun j : nat => Qabs (A ((Datatypes.S n + j)%nat))))).
           ring.
Qed.

(* ============================================================ *)
(* L6 辅助 a：cos 尾带（指标 S n 起、长 n）≤ E(4n+1) − E(2n+1)   *)
(* ============================================================ *)
Lemma sc_add_c_tail_le : forall (t B : Q) (n : nat),
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) t)))
      (exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
Proof.
  intros t B n HB HtB.
  apply Qle_to_QleT'.
  assert (Hn : (n = 2 * n - n)%nat) by lia.
  assert (Hdn : (n <= 2 * n)%nat) by lia.
  assert (Hidx : (2 * (2 * n) + 1 = 4 * n + 1)%nat) by lia.
  apply (Qle_trans _ (exp_series (2 * (2 * n) + 1) B - exp_series (2 * n + 1) B) _).
  - rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq n (2 * n - n) (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) t)) Hn)).
    exact (QleT'_to_Qle _ _ (sc_cs_c_tail_diff_le t B n (2 * n) HB HtB Hdn)).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (sc_exp_series_idx (2 * (2 * n) + 1) (4 * n + 1) B Hidx)).
    reflexivity.
Qed.

(* ============================================================ *)
(* L6 辅助 b：sin 尾带（指标 S n 起、长 n，n ≥ 1）≤ 同上          *)
(* ============================================================ *)
Lemma sc_add_d_tail_le : forall (t B : Q) (n : nat), (1 <= n)%nat ->
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) t)))
      (exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
Proof.
  intros t B n Hn1 HB HtB.
  apply Qle_to_QleT'.
  assert (Hdn : (Datatypes.S n <= 2 * n)%nat) by lia.
  assert (Hd1 : (1 <= Datatypes.S n)%nat) by lia.
  assert (Hlen : (n = Datatypes.S (2 * n - Datatypes.S n))%nat) by lia.
  assert (Hidx1 : (2 * (2 * n) + 1 = 4 * n + 1)%nat) by lia.
  assert (Hidx2 : (2 * (Datatypes.S n) - 1 = 2 * n + 1)%nat) by lia.
  apply (Qle_trans _ (exp_series (2 * (2 * n) + 1) B - exp_series (2 * (Datatypes.S n) - 1) B) _).
  - rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq n (Datatypes.S (2 * n - Datatypes.S n))
              (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) t)) Hlen)).
    exact (QleT'_to_Qle _ _ (sc_cs_d_tail_diff_le t B (Datatypes.S n) (2 * n) HB HtB Hd1 Hdn)).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (sc_exp_series_idx (2 * (2 * n) + 1) (4 * n + 1) B Hidx1)).
    rewrite (qeqT_imp_qeq _ _ (sc_exp_series_idx (2 * (Datatypes.S n) - 1) (2 * n + 1) B Hidx2)).
    reflexivity.
Qed.

(* ============================================================ *)
(* L6 辅助 c：p ≤ P、q ≤ Q（全非负）⟹ p·q ≤ P·Q                  *)
(* ============================================================ *)
Lemma sc_prod_le : forall (p q P Q : Q),
  Qle 0 p -> Qle 0 q -> Qle p P -> Qle q Q -> Qle 0 P ->
  QleT' (p * q) (P * Q).
Proof.
intros p q P Q Hp Hq HpP HqQ HP0. apply Qle_to_QleT'. exact (Qle_trans (p * q) (P * q) (P * Q) (Qmult_le_compat_r p P q HpP Hq) (QleT'_to_Qle (P * q) (P * Q) (sc_qmult_le_l q Q P HqQ HP0))).
Qed.

(* ============================================================ *)
(* L6：sin 误差绝对界（|err| ≤ 4·E(2n+1)·(E(4n+1) − E(2n+1))）  *)
(* ============================================================ *)
Lemma sc_add_sin_err_abs : forall (x y : Q) (n : nat) (B : Q),
  (1 <= n)%nat -> Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y - cos_partial n x * sin_partial n y))
      (((1 + 1) * (1 + 1)) * (exp_series (2 * n + 1) B * (exp_series (4 * n + 1) B - exp_series (2 * n + 1) B))).
Proof.
  intros x y n B Hn1 HB HxB HyB.
  apply Qle_to_QleT'.
  set (E := exp_series (2 * n + 1) B).
  set (Tail := exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HEmono : Qle (exp_series (2 * n + 1) B) (exp_series (4 * n + 1) B)).
  { apply QleT'_to_Qle. apply exp_series_mono; [exact (Qle_to_QleT' _ _ HB) | lia]. }
  assert (HTail0 : Qle 0 Tail).
  { unfold Tail. apply (proj1 (Qle_minus_iff (exp_series (2 * n + 1) B) (exp_series (4 * n + 1) B))).
    exact HEmono. }
  (* 四个 F/T 界 *)
  assert (HcFx : Qle (sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j x))) E).
  { unfold E. exact (QleT'_to_Qle _ _ (sc_cs_c_full_le x B n HB HxB)). }
  assert (HcFy : Qle (sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j y))) E).
  { unfold E. exact (QleT'_to_Qle _ _ (sc_cs_c_full_le y B n HB HyB)). }
  assert (HsFx : Qle (sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j x))) E).
  { unfold E. exact (QleT'_to_Qle _ _ (sc_cs_d_full_le x B n HB HxB)). }
  assert (HsFy : Qle (sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j y))) E).
  { unfold E. exact (QleT'_to_Qle _ _ (sc_cs_d_full_le y B n HB HyB)). }
  assert (HcTx : Qle (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) x))) Tail).
  { unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_c_tail_le x B n HB HxB)). }
  assert (HcTy : Qle (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) y))) Tail).
  { unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_c_tail_le y B n HB HyB)). }
  assert (HsTx : Qle (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x))) Tail).
  { unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_d_tail_le x B n Hn1 HB HxB)). }
  assert (HsTy : Qle (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) y))) Tail).
  { unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_d_tail_le y B n Hn1 HB HyB)). }
  (* 非负件 *)
  assert (HcF0 : forall a : Q, Qle 0 (sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j a)))).
  { intro a. apply QleT'_to_Qle. apply sc_sum_nonneg. intro j. apply Qabs_nonneg. }
  assert (HsF0 : forall a : Q, Qle 0 (sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j a)))).
  { intro a. apply QleT'_to_Qle. apply sc_sum_nonneg. intro j. apply Qabs_nonneg. }
  assert (HcT0 : forall a : Q, Qle 0 (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) a)))).
  { intro a. apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
  assert (HsT0 : forall a : Q, Qle 0 (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) a)))).
  { intro a. apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
  (* 精确分解 → 带界 *)
  assert (Hdec := sc_add_sin_err_decomp x y n).
  apply QleT'_to_Qle. apply (sc_qabs_qeq_le (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y - cos_partial n x * sin_partial n y)
                        ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
                          sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * sin_term i y))) +
                         (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
                          sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * cos_term i y))))
                        (((1 + 1) * (1 + 1)) * (E * Tail))).
  - apply qeqT_imp_qeq. exact Hdec.
  - (* |D1 + D2| ≤ 4·E·Tail：三角 + 双族带界 + 双族 F/T 乘积 *)
    apply (Qle_trans _ (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
                              sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * sin_term i y))) +
                        Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
                              sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * cos_term i y)))) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (((1 + 1) * (E * Tail)) + ((1 + 1) * (E * Tail))) _).
      * apply Qplus_le_compat.
        -- (* |D1| ≤ 2·E·Tail（cs 族） *)
           apply (Qle_trans _ ((sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j x))) *
                                 (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) y))) +
                               (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) x))) *
                                 (sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j y)))) _).
           ++ exact (QleT'_to_Qle _ _ (sc_add_band_abs (fun j : nat => cos_term j x) (fun k : nat => sin_term k y) n)).
           ++ apply (Qle_trans _ ((E * Tail) + (E * Tail)) _).
              ** apply Qplus_le_compat.
                 --- apply QleT'_to_Qle. apply (sc_prod_le (sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j x)))
                                       (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) y)))
                                       E Tail); [exact (HcF0 x) | exact (HsT0 y) | exact HcFx | exact HsTy | exact HE0].
                 --- (* 第二乘积 Tc(x)·Fs(y) ≤ E·Tail（先经 Tail·E 再 comm） *)
                     apply (Qle_trans _ (Tail * E) _).
                     { apply QleT'_to_Qle. apply (sc_prod_le (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) x)))
                                         (sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j y)))
                                         Tail E); [exact (HcT0 x) | exact (HsF0 y) | exact HcTx | exact HsFy | exact HTail0]. }
                     { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- (* |D2| ≤ 2·E·Tail（sc 族：bound = Fs(x)·Tc(y) + Ts(x)·Fc(y)） *)
           apply (Qle_trans _ ((sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j x))) *
                                 (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) y))) +
                               (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x))) *
                                 (sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j y)))) _).
           ++ exact (QleT'_to_Qle _ _ (sc_add_band_abs (fun j : nat => sin_term j x) (fun k : nat => cos_term k y) n)).
           ++ apply (Qle_trans _ ((E * Tail) + (E * Tail)) _).
              ** apply Qplus_le_compat.
                 --- apply QleT'_to_Qle. apply (sc_prod_le (sum_upto (Datatypes.S n) (fun j : nat => Qabs (sin_term j x)))
                                       (sum_upto n (fun m : nat => Qabs (cos_term ((Datatypes.S n + m)%nat) y)))
                                       E Tail); [exact (HsF0 x) | exact (HcT0 y) | exact HsFx | exact HcTy | exact HE0].
                 --- apply (Qle_trans _ (Tail * E) _).
                     { apply QleT'_to_Qle. apply (sc_prod_le (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x)))
                                         (sum_upto (Datatypes.S n) (fun j : nat => Qabs (cos_term j y)))
                                         Tail E); [exact (HsT0 x) | exact (HcF0 y) | exact HsTx | exact HcFy | exact HTail0]. }
                     { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* L7：err 尾界（|err| ≤ 4·E(2n+1)·exp_tail_abs (2n+1)(4n+1) B）*)
(* ============================================================ *)
Lemma sc_add_sin_err_tail_le : forall (x y : Q) (n : nat) (B : Q),
  (1 <= n)%nat -> Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y - cos_partial n x * sin_partial n y))
      (((1 + 1) * (1 + 1)) * (exp_series (2 * n + 1) B * exp_tail_abs (2 * n + 1) (4 * n + 1) B)).
Proof.
  intros x y n B Hn1 HB HxB HyB.
  apply Qle_to_QleT'.
  set (E := exp_series (2 * n + 1) B).
  set (Tail := exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
  set (X := exp_tail_abs (2 * n + 1) (4 * n + 1) B).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HX0 : Qle 0 X) by (unfold X; apply QleT'_to_Qle; apply exp_tail_abs_nonneg; apply Qle_to_QleT'; exact HB).
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1))) by (apply Qmult_le_0_compat; apply QleT'_to_Qle; apply Q2_nonneg).
  assert (HTX : Qle Tail X).
  { unfold Tail, X. apply QleT'_to_Qle. apply (exp_series_tail_le B (2 * n + 1) (4 * n + 1) (Qle_to_QleT' _ _ HB)). lia. }
  apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (E * Tail)) _).
  - unfold E, Tail. exact (QleT'_to_Qle _ _ (sc_add_sin_err_abs x y n B Hn1 HB HxB HyB)).
  - apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (E * X)) _).
    + apply QleT'_to_Qle. apply (sc_qmult_le_l (E * Tail) (E * X) ((1 + 1) * (1 + 1))).
      * apply QleT'_to_Qle. apply (sc_qmult_le_l Tail X E); [exact HTX | exact HE0].
      * exact Hfour0.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* L8：模量 —— sc_add_sin_err_bound                             *)
(*   ∀eps ∃N ∀n≥N ∀|x|,|y|≤B：                                *)
(*     |sin_{2n}(x+y) − sp_n cp_n − cp_n sp_n| < eps             *)
(* ============================================================ *)
Lemma sc_add_sin_err_bound : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall (x y : Q) (n : nat), NatLe N n ->
    QleT' (Qabs x) B -> QleT' (Qabs y) B ->
    QltT (Qabs (sin_partial (2 * n) (x + y) - sin_partial n x * cos_partial n y - cos_partial n x * sin_partial n y)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  destruct (exp_series_arch B HB) as [C [HC1 HC]].
  assert (HC0 : Qle 0 C) by (apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1)) by (apply QleT'_to_Qle; apply Q2_nonneg).
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1))) by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  set (P := ((1 + 1) * (1 + 1)) * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply Qmult_le_0_compat.
    - exact Hfour0.
    - apply (Qmult_le_0_compat C ((q_pow B N0 / q_fact N0) * (1 + 1))).
      + exact HC0.
      + apply QleT'_to_Qle. apply q_pow_fact2_nonneg. exact HB. }
  destruct (arch_decay P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists (N0 + Datatypes.S t)%nat.
  intros x y n HNn HxB HyB.
  apply NatLe_drop in HNn.
  assert (HBle : Qle 0 B) by exact (QleT'_to_Qle _ _ HB).
  assert (HxBe : Qle (Qabs x) B) by exact (QleT'_to_Qle _ _ HxB).
  assert (HyBe : Qle (Qabs y) B) by exact (QleT'_to_Qle _ _ HyB).
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (HN0geom : forall u : nat, (N0 <= u)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (HN0m : (N0 <= 2 * n + 1)%nat) by lia.
  assert (Hmlen : (2 * n + 1 <= 4 * n + 1)%nat) by lia.
  assert (HNgeom2 : forall u : nat, (2 * n + 1 <= u)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply HN0geom. lia. }
  assert (Hj : (Datatypes.S t <= 2 * n + 1 - N0)%nat) by lia.
  set (E := exp_series (2 * n + 1) B).
  set (X := exp_tail_abs (2 * n + 1) (4 * n + 1) B).
  set (Y := q_pow B (2 * n + 1) / q_fact (2 * n + 1)).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HBle).
  assert (HEC : Qle E C) by (unfold E; apply QleT'_to_Qle; exact (HC ((2 * n + 1)%nat))).
  assert (HX0 : Qle 0 X) by (unfold X; apply QleT'_to_Qle; apply exp_tail_abs_nonneg; apply Qle_to_QleT'; exact HBle).
  assert (HXg : Qle X (Y * (1 + 1))).
  { unfold X, Y. apply QleT'_to_Qle. apply (exp_tail_abs_geom2 B (2 * n + 1) (4 * n + 1) (Qle_to_QleT' _ _ HBle) (fun u Hu => Qle_to_QleT' _ _ (HNgeom2 u (NatLe_drop _ _ Hu))) Hmlen). }
  assert (HY0 : Qle 0 (Y * (1 + 1))) by (unfold Y; apply QleT'_to_Qle; apply q_pow_fact2_nonneg; apply Qle_to_QleT'; exact HBle).
  assert (HYdec : Qle Y ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0))).
  { unfold Y. apply QleT'_to_Qle. apply (pow_fact_decay B N0 (2 * n + 1) (Qle_to_QleT' _ _ HBle) (fun u Hu => Qle_to_QleT' _ _ (HN0geom u (NatLe_drop _ _ Hu)))). lia. }
  assert (Hq0 : Qle 0 (q_pow (1 / 2)%Q (2 * n + 1 - N0))) by (apply QleT'_to_Qle; apply q_pow_nonneg; exact Qhalf_nonneg).
  assert (HD0 : Qle 0 ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0))).
  { apply (Qmult_le_0_compat (q_pow B N0 / q_fact N0) (q_pow (1 / 2)%Q (2 * n + 1 - N0))).
    - apply QleT'_to_Qle. apply q_pow_fact_nonneg; apply Qle_to_QleT'. exact HBle.
    - exact Hq0. }
  assert (Hhalf0 : Qle 0 (q_pow (1 / 2)%Q (Datatypes.S t))) by (apply QleT'_to_Qle; apply q_pow_nonneg; exact Qhalf_nonneg).
  assert (Hdec : Qle (q_pow (1 / 2)%Q (2 * n + 1 - N0)) (q_pow (1 / 2)%Q (Datatypes.S t))).
  { apply QleT'_to_Qle. apply (q_half_pow_mono (2 * n + 1 - N0) (Datatypes.S t)). exact Hj. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (P * q_pow (1 / 2)%Q (Datatypes.S t)) _).
  - apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (E * X)) _).
    + exact (QleT'_to_Qle _ _ (sc_add_sin_err_tail_le x y n B Hn1 HBle HxBe HyBe)).
    + apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (C * X)) _).
      * apply QleT'_to_Qle. apply (sc_qmult_le_l (E * X) (C * X) ((1 + 1) * (1 + 1))).
        -- apply (Qmult_le_compat_r E C X); [exact HEC | exact HX0].
        -- exact Hfour0.
      * apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (C * (Y * (1 + 1)))) _).
        -- apply QleT'_to_Qle. apply (sc_qmult_le_l (C * X) (C * (Y * (1 + 1))) ((1 + 1) * (1 + 1))).
           ++ apply QleT'_to_Qle. apply (sc_qmult_le_l X (Y * (1 + 1)) C); [exact HXg | exact HC0].
           ++ exact Hfour0.
        -- apply (Qle_trans _ (((1 + 1) * (1 + 1)) * (C * (((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0)) * (1 + 1)))) _).
           ++ apply QleT'_to_Qle. apply (sc_qmult_le_l (C * (Y * (1 + 1)))
                                   (C * (((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0)) * (1 + 1)))
                                   ((1 + 1) * (1 + 1))).
              ** apply QleT'_to_Qle. apply (sc_qmult_le_l (Y * (1 + 1))
                                      (((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0)) * (1 + 1))
                                      C).
                 --- apply (Qmult_le_compat_r Y ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0)) (1 + 1));
                     [exact HYdec | exact Htwo0].
                 --- exact HC0.
              ** exact Hfour0.
           ++ apply (Qle_trans _ (P * q_pow (1 / 2)%Q (2 * n + 1 - N0)) _).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold P. ring.
              ** apply QleT'_to_Qle. apply (sc_qmult_le_l (q_pow (1 / 2)%Q (2 * n + 1 - N0)) (q_pow (1 / 2)%Q (Datatypes.S t)) P);
                   [exact Hdec | exact HP0].
  - exact (QltT_to_Qlt _ _ Ht).
Qed.

(* ============================================================ *)
(* rs_add_sin：Real 层 sin 加法（exp_plus eps/3 装配模板）        *)
(* ============================================================ *)
Lemma rs_add_sin : forall (X Y : Real),
  real_eq (cauchy_real_sin (real_plus X Y))
          (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos Y))
                     (real_mult (cauchy_real_cos X) (cauchy_real_sin Y))).
Proof.
  intros X Y.
  destruct X as [u Hu]. destruct Y as [v Hv].
  unfold real_eq.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mx [HMxpos HMx]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [My [HMypos HMy]].
  set (M := Mx + My).
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
      + apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  assert (HsumMT : forall n : nat, QleT' (Qabs (u n + v n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (u n + v n)) (Qabs (u n) + Qabs (v n)) (Mx + My)).
    - apply Qle_to_QleT'. apply Qabs_triangle.
    - apply (qleT'_plus_compat (Qabs (u n)) Mx (Qabs (v n)) My).
      + apply HMx.
      + apply HMy. }
  assert (Heps3T : QltT 0 (eps / 3)).
  { apply (qltT_div_pos eps 3). exact Heps. exact qltT_0_3. }
  destruct (sc_sin_partial_cauchy_bounded M (eps / 3) HMnonnegT Heps3T) as [N1 HN1].
  destruct (sc_add_sin_err_bound M (eps / 3) HMnonnegT Heps3T) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  apply NatLe_drop in Hn.
  apply Qlt_to_QltT.
  change (Qlt (Qabs (sin_partial n (u n + v n) -
                     (sin_partial n (u n) * cos_partial n (v n) + cos_partial n (u n) * sin_partial n (v n)))) eps).
  (* 代数拆分：sin_n(u+v) − (b + c) == (sin_n(u+v) − sin_{2n}(u+v)) + (sin_{2n}(u+v) − b − c) *)
  apply (Qle_lt_trans _ (Qabs (sin_partial n (u n + v n) - sin_partial (2 * n) (u n + v n)) +
                          Qabs (sin_partial (2 * n) (u n + v n) - sin_partial n (u n) * cos_partial n (v n) - cos_partial n (u n) * sin_partial n (v n))) _).
  - apply (Qle_trans _ (Qabs ((sin_partial n (u n + v n) - sin_partial (2 * n) (u n + v n)) +
                               (sin_partial (2 * n) (u n + v n) - sin_partial n (u n) * cos_partial n (v n) - cos_partial n (u n) * sin_partial n (v n)))) _).
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      apply (Qabs_wd (sin_partial n (u n + v n) -
                      (sin_partial n (u n) * cos_partial n (v n) + cos_partial n (u n) * sin_partial n (v n)))
                     ((sin_partial n (u n + v n) - sin_partial (2 * n) (u n + v n)) +
                      (sin_partial (2 * n) (u n + v n) - sin_partial n (u n) * cos_partial n (v n) - cos_partial n (u n) * sin_partial n (v n)))).
      ring.
    + apply Qabs_triangle.
  - apply (Qlt_le_trans _ (eps / 3 + eps / 3) _).
    + apply Qplus_lt_compat.
      * apply QltT_to_Qlt.
        apply (HN1 n ((2 * n)%nat)).
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact Hn].
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | lia].
        -- exact (HsumMT n).
      * apply QltT_to_Qlt.
        apply (HN2 (u n) (v n) n).
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact Hn].
        -- exact (HuMT n).
        -- exact (HvMT n).
    + apply (Qle_trans _ (Qmult (Qinv 3 + Qinv 3) eps) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
      * apply (Qle_trans _ (Qmult 1 eps) _).
        -- apply (Qmult_le_compat_r (Qinv 3 + Qinv 3) 1 eps).
           ++ unfold Qle, Qinv, Qplus. simpl. lia.
           ++ apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* SC-2 批 8（并入 199）：cos 加法定理 Real 层（sH 论证）       *)
(* Q 层模量链 24 条 + rs_add_cos：                            *)
(*   real_eq (cos(X+Y)) (cosX*cosY - sinX*sinY)               *)
(* ============================================================ *)

(* ============================================================ *)
(* sH_cos_q1.v：cos 加法定理 Q 层——部分和三角形态 + 分解骨架      *)
(* 内容：sH_add_cos（cos 加法定理；sin 侧对应件已端到端闭合）     *)
(* 纪律：零公理面、零承认件；纯构造性 Set 层。                    *)
(* ============================================================ *)

(* ============================================================ *)
(* R1：ss 双重和重标（cos 对角 ss 片带 (j−1) 内标，整体外移 1）  *)
(*   Σ_{j=0}^{J} Σ_{i=0}^{j−1} f i·g (j−1−i)                    *)
(*     == Σ_{m=0}^{J−1} Σ_{i=0}^{m} f i·g (m−i)                 *)
(* ============================================================ *)
Lemma sc_cos_add_ss_reindex : forall (J : nat) (f g : nat -> Q), QeqT (sum_upto (Datatypes.S J) (fun j : nat => sum_upto j (fun i : nat => f i * g (Nat.sub (Nat.sub j 1) i)))) (sum_upto J (fun m : nat => sum_upto (Datatypes.S m) (fun i : nat => f i * g (Nat.sub m i)))).
Proof.
  intros J.
  induction J as [| J' IH]; intros f g.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. (* 两侧各 + 同一尾块：LHS j=S J'、RHS m=J'（S J' − 1 与 J' 经 lia 桥） *)
    transitivity (sum_upto (Datatypes.S J') (fun j : nat => sum_upto j (fun i : nat => f i * g (Nat.sub (Nat.sub j 1) i))) +
                  sum_upto (Datatypes.S J') (fun i : nat => f i * g (Nat.sub (Nat.sub (Datatypes.S J') 1) i))).
    + reflexivity.
    + setoid_rewrite (qeqT_imp_qeq _ _ (IH f g)).
      transitivity (sum_upto J' (fun m : nat => sum_upto (Datatypes.S m) (fun i : nat => f i * g (Nat.sub m i))) +
                    sum_upto (Datatypes.S J') (fun i : nat => f i * g (Nat.sub J' i))).
      * (* 尾项相等：sub (sub (S J') 1) i == sub J' i（lia） *)
        assert (Ht : sum_upto (Datatypes.S J') (fun i : nat => f i * g (Nat.sub (Nat.sub (Datatypes.S J') 1) i)) ==
                     sum_upto (Datatypes.S J') (fun i : nat => f i * g (Nat.sub J' i))).
        { apply qeqT_imp_qeq.
          apply (sum_upto_ext_below (Datatypes.S J')
                   (fun i : nat => f i * g (Nat.sub (Nat.sub (Datatypes.S J') 1) i))
                   (fun i : nat => f i * g (Nat.sub J' i))).
          intros i Hi.
          assert (Hn : (Nat.sub (Nat.sub (Datatypes.S J') 1) i = Nat.sub J' i)%nat) by lia.
          rewrite Hn. apply qeq_imp_qeqT. reflexivity. }
        rewrite Ht. reflexivity.
      * reflexivity.
Qed.

(* ============================================================ *)
(* R2：三角层差（泛型）                                          *)
(*   tri(K) := Σ_{i≤K}Σ_{k≤K−i} A i·B k                        *)
(*   tri(K) − tri'(K−1) == Σ_{i=0}^{K} A i·B (K−i)             *)
(* （cos 侧 ss 三角 cap 2n−1 ⊄ 方块 n 的角点分离的代数基础）     *)
(* ============================================================ *)
Lemma sc_cos_add_tri_step : forall (K : nat) (A B : nat -> Q), QeqT (sum_upto (Datatypes.S K) (fun i : nat => sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k)) -
  sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k))) (sum_upto (Datatypes.S K) (fun i : nat => A i * B ((K - i)%nat))).
Proof.
  intros K A B.
  apply qeq_imp_qeqT.
  (* 行改写事实：i < K ⟹ row_i == sub_row_i + extra_i *)
  assert (Hrows : forall i : nat, (i < K)%nat ->
    sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k) ==
    sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k) + A i * B ((K - i)%nat)).
  { intros i Hi.
    change (sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k))
      with (sum_upto (K - i) (fun k : nat => A i * B k) + A i * B ((K - i)%nat)).
    assert (Hn : (K - i = Datatypes.S (K - 1 - i))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (K - i) (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k) Hn)).
    reflexivity. }
  (* 尾行事实：row_K == A K · B 0（K − K == 0） *)
  assert (Hlast : sum_upto (Datatypes.S (K - K)) (fun k : nat => A K * B k) == A K * B (0%nat)).
  { assert (Hcap : (Datatypes.S (K - K) = 1)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (K - K)) 1 (fun k : nat => A K * B k) Hcap)).
    simpl. ring. }
  (* 目标三角：先证 tri(K) == sub(K) + anti(K) *)
  assert (Hdec :
    sum_upto (Datatypes.S K) (fun i : nat => sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k)) ==
    sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k)) +
    sum_upto (Datatypes.S K) (fun i : nat => A i * B ((K - i)%nat))).
  {
    (* tri(K) == Σ_{i<K} row_i + row_K（外层拆尾） *)
    transitivity (sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k)) +
                  sum_upto (Datatypes.S (K - K)) (fun k : nat => A K * B k)).
    - change (sum_upto (Datatypes.S K) (fun i : nat => sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k)))
        with (sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k)) +
              sum_upto (Datatypes.S (K - K)) (fun k : nat => A K * B k)).
      reflexivity.
    - (* 逐行展开 + 尾行替换 *)
      transitivity (sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k) + A i * B ((K - i)%nat)) +
                    A K * B (0%nat)).
      + rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below K
          (fun i : nat => sum_upto (Datatypes.S (K - i)) (fun k : nat => A i * B k))
          (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k) + A i * B ((K - i)%nat)) (fun i Hi => qeq_imp_qeqT _ _ (Hrows i (NatLe_drop _ _ Hi))))).
        rewrite Hlast.
        reflexivity.
      + (* Σ(sub_row + extra) + A K B 0 == sub(K) + anti(K) *)
        transitivity (sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k)) +
                      (sum_upto K (fun i : nat => A i * B ((K - i)%nat)) + A K * B ((K - K)%nat))).
        * rewrite (qeqT_imp_qeq _ _ (sum_upto_plus K
            (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k))
            (fun i : nat => A i * B ((K - i)%nat)))).
          assert (Hkk : (K - K = 0)%nat) by lia.
          rewrite Hkk. ring.
        * transitivity (sum_upto K (fun i : nat => sum_upto (Datatypes.S (K - 1 - i)) (fun k : nat => A i * B k)) +
                        sum_upto (Datatypes.S K) (fun i : nat => A i * B ((K - i)%nat))).
          -- change (sum_upto (Datatypes.S K) (fun i : nat => A i * B ((K - i)%nat)))
               with (sum_upto K (fun i : nat => A i * B ((K - i)%nat)) + A K * B ((K - K)%nat)).
             reflexivity.
          -- reflexivity.
  }
  (* 主目标：tri − sub == anti ⟸ Hdec + ring *)
  rewrite Hdec.
  ring.
Qed.

(* ============================================================ *)
(* R3a：cc 乘积方块：cp_n(x)·cp_n(y) == Σ_{i,k≤n} c_i(x)·c_k(y) *)
(* ============================================================ *)
Lemma sc_add_cc_prod_sq : forall (x y : Q) (n : nat), QeqT (cos_partial n x * cos_partial n y) (sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => cos_term i x * cos_term k y))).
Proof.
intros x y n. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n x)). rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto n y)). exact (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun i : nat => cos_term i x) (fun k : nat => cos_term k y))).
Qed.

(* ============================================================ *)
(* R3b：ss 乘积方块：sp_n(x)·sp_n(y) == Σ_{i,k≤n} s_i(x)·s_k(y) *)
(* ============================================================ *)
Lemma sc_add_ss_prod_sq : forall (x y : Q) (n : nat), QeqT (sin_partial n x * sin_partial n y) (sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * sin_term k y))).
Proof.
intros x y n. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n x)). rewrite (qeqT_imp_qeq _ _ (sc_sin_partial_upto n y)). exact (qeqT_imp_qeq _ _ (sum_upto_prod n n (fun i : nat => sin_term i x) (fun k : nat => sin_term k y))).
Qed.

(* ============================================================ *)
(* R4a：cc 部分和对角-转置                                       *)
(*   Σ_{j≤J}Σ_{i≤j} c_i(x)·c_{j−i}(y)                           *)
(*     == Σ_{i≤J}Σ_{k≤J−i} c_i(x)·c_k(y)                       *)
(* ============================================================ *)
Lemma sc_add_cos_cc_swap : forall (x y : Q) (J : nat), QeqT (sum_upto (Datatypes.S J) (fun j : nat => sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y))) (sum_upto (Datatypes.S J) (fun i : nat => sum_upto (Datatypes.S (J - i)) (fun k : nat => cos_term i x * cos_term k y))).
Proof.
  intros x y J.
  apply qeq_imp_qeqT.
  exact (qeqT_imp_qeq _ _ (exp_cauchy_swap J (fun i : nat => cos_term i x) (fun k : nat => cos_term k y))).
Qed.

(* ============================================================ *)
(* R4b：ss 部分和对角-转置（含重标，cap J−1）                    *)
(*   Σ_{j≤J}Σ_{i≤j−1} s_i(x)·s_{j−1−i}(y)                      *)
(*     == Σ_{i≤J−1}Σ_{k≤J−1−i} s_i(x)·s_k(y)                   *)
(* ============================================================ *)
Lemma sc_add_cos_ss_swap : forall (x y : Q) (J : nat), (1 <= J)%nat ->QeqT (sum_upto (Datatypes.S J) (fun j : nat => sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y))) (sum_upto (Datatypes.S (J - 1)) (fun i : nat => sum_upto (Datatypes.S (J - 1 - i)) (fun k : nat => sin_term i x * sin_term k y))).
Proof.
  intros x y J HJ1.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_add_ss_reindex J (fun i : nat => sin_term i x) (fun i : nat => sin_term i y))).
  assert (Hcap : (J = Datatypes.S (J - 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq J (Datatypes.S (J - 1))
            (fun m : nat => sum_upto (Datatypes.S m) (fun i : nat => sin_term i x * sin_term (Nat.sub m i) y)) Hcap)).
  exact (qeqT_imp_qeq _ _ (exp_cauchy_swap (J - 1) (fun i : nat => sin_term i x) (fun k : nat => sin_term k y))).
Qed.

(* ============================================================ *)
(* R5：cos 部分和对角-转置                                       *)
(*   cos_partial J (x+y) ==                                      *)
(*     Σ_{i≤J}Σ_{k≤J−i} c_i(x)c_k(y) −                          *)
(*     Σ_{i≤J−1}Σ_{k≤J−1−i} s_i(x)s_k(y)                        *)
(* ============================================================ *)
Lemma sc_add_cos_diag_swap : forall (x y : Q) (J : nat), (1 <= J)%nat ->QeqT (cos_partial J (x + y)) ((sum_upto (Datatypes.S J) (fun i : nat => sum_upto (Datatypes.S (J - i)) (fun k : nat => cos_term i x * cos_term k y))) -
  (sum_upto (Datatypes.S (J - 1)) (fun i : nat => sum_upto (Datatypes.S (J - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)))).
Proof.
  intros x y J HJ1.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_partial_upto J (x + y))).
  (* 逐项对角恒等式：cos_term j (x+y) == cc_j − ss_j *)
  transitivity (sum_upto (Datatypes.S J) (fun j : nat =>
      sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y) -
      sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y))).
  - apply qeqT_imp_qeq.
    apply (sum_upto_ext_below (Datatypes.S J)).
    intros j Hj.
    apply (sc_add_cos_diag_term x y j).
  - (* Σ(cc_j − ss_j) == Σcc − Σss == ccT − ssT *)
    transitivity (sum_upto (Datatypes.S J) (fun j : nat => sum_upto (Datatypes.S j) (fun i : nat => cos_term i x * cos_term (Nat.sub j i) y)) -
                  sum_upto (Datatypes.S J) (fun j : nat => sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y))).
    + apply qeqT_imp_qeq. apply sum_upto_minus.
    + transitivity (sum_upto (Datatypes.S J) (fun i : nat => sum_upto (Datatypes.S (J - i)) (fun k : nat => cos_term i x * cos_term k y)) -
                    sum_upto (Datatypes.S J) (fun j : nat => sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y))).
      * (* Σcc-diag == ccT：左端改写 *)
        rewrite (qeqT_imp_qeq _ _ (sc_add_cos_cc_swap x y J)). reflexivity.
      * transitivity (sum_upto (Datatypes.S J) (fun i : nat => sum_upto (Datatypes.S (J - i)) (fun k : nat => cos_term i x * cos_term k y)) -
                      sum_upto (Datatypes.S (J - 1)) (fun i : nat => sum_upto (Datatypes.S (J - 1 - i)) (fun k : nat => sin_term i x * sin_term k y))).
        -- rewrite (qeqT_imp_qeq _ _ (sc_add_cos_ss_swap x y J HJ1)). reflexivity.
        -- reflexivity.
Qed.
(* ============================================================ *)
(* sH_cos_q2.v：cos 加法定理 Q 层——精确误差分解                  *)
(* 依赖：q1（sc_cos_add_ss_reindex / sc_cos_add_tri_step /       *)
(*       sc_add_cc_prod_sq / sc_add_ss_prod_sq /                 *)
(*       sc_add_cos_cc_swap / sc_add_cos_ss_swap /               *)
(*       sc_add_cos_diag_swap）                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* R6：cos 误差精确分解（角点分离）                              *)
(*   err := cos_{2n}(x+y) − cp_n(x)cp_n(y) + sp_n(x)sp_n(y)     *)
(*   == D_cc − D_ss + anti                                      *)
(*   D_cc := fam_decomp 带（cc 族，三角 cap 2n − 方块 n）        *)
(*   D_ss := fam_decomp 带（ss 族，三角 cap 2n − 方块 n）        *)
(*   anti := Σ_{i=0}^{2n} s_i(x)·s_{2n−i}(y)（含角点 i=n）      *)
(* ============================================================ *)
Lemma sc_add_cos_err_decomp : forall (x y : Q) (n : nat), (1 <= n)%nat ->QeqT (cos_partial (2 * n) (x + y) - cos_partial n x * cos_partial n y + sin_partial n x * sin_partial n y) ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
   sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * cos_term i y))) -
  (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
   sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * sin_term i y))) +
  sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y)).
Proof.
  intros x y n Hn1.
  apply qeq_imp_qeqT.
  assert (H2n1 : (1 <= 2 * n)%nat) by lia.
  (* 1. cos_partial 对角-转置；乘积方块 *)
  rewrite (qeqT_imp_qeq _ _ (sc_add_cos_diag_swap x y (2 * n) H2n1)).
  rewrite (qeqT_imp_qeq _ _ (sc_add_cc_prod_sq x y n)).
  rewrite (qeqT_imp_qeq _ _ (sc_add_ss_prod_sq x y n)).
  (* 目标：((ccT − ssT) − sq_cc + sq_ss) == D_cc − D_ss + anti *)
  (* 2. 重组：== (ccT − sq_cc) − (ssT(2n−1) − sq_ss) *)
  transitivity ((sum_upto (Datatypes.S (2 * n)) (fun i : nat => sum_upto (Datatypes.S (2 * n - i)) (fun k : nat => cos_term i x * cos_term k y)) -
                 sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => cos_term i x * cos_term k y))) -
                (sum_upto (Datatypes.S (2 * n - 1)) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)) -
                 sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * sin_term k y)))).
  - ring.
  - (* 3. cc 族 fam_decomp *)
    transitivity ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
                   sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * cos_term i y))) -
                  (sum_upto (Datatypes.S (2 * n - 1)) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)) -
                   sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * sin_term k y)))).
    + rewrite (qeqT_imp_qeq _ _ (sc_add_fam_decomp (fun i : nat => cos_term i x) (fun k : nat => cos_term k y) n)).
      reflexivity.
    + (* 4. ss 族：ssT(2n−1) − sq_ss == D_ss − anti（Hssb 引理辅助） *)
      transitivity ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
                     sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * cos_term i y))) -
                    ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
                      sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * sin_term i y))) -
                     sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y))).
      * assert (Hssb :
          (sum_upto (Datatypes.S (2 * n - 1)) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)) -
           sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * sin_term k y))) ==
          ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
            sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * sin_term i y))) -
           sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y))).
        { (* 4a. 三角层差（cap 桥后）给出：ssT(2n−1) == ssT(2n) − anti *)
          pose proof (qeqT_imp_qeq _ _ (sc_cos_add_tri_step (2 * n) (fun i : nat => sin_term i x) (fun k : nat => sin_term k y))) as Ht.
          assert (Hcap : (Datatypes.S (2 * n - 1) = 2 * n)%nat) by lia.
          (* HcapEq：sub(2n) 文本 == ssT(2n−1) 文本（外层 cap 桥） *)
          assert (Hsubeq :
            sum_upto (Datatypes.S (2 * n - 1)) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)) ==
            sum_upto (2 * n) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y))).
          { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S (2 * n - 1)) (2 * n)
              (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)) Hcap)).
            reflexivity. }
          (* ssT(2n−1) == ssT(2n) − anti *)
          assert (Hss1 :
            sum_upto (Datatypes.S (2 * n - 1)) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)) ==
            sum_upto (Datatypes.S (2 * n)) (fun i : nat => sum_upto (Datatypes.S (2 * n - i)) (fun k : nat => sin_term i x * sin_term k y)) -
            sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y)).
          { transitivity (sum_upto (2 * n) (fun i : nat => sum_upto (Datatypes.S (2 * n - 1 - i)) (fun k : nat => sin_term i x * sin_term k y))).
            - exact Hsubeq.
            - (* sub(2n) == ssT(2n) − anti：由 Ht（ssT(2n) − sub(2n) == anti）ring 推 *)
              rewrite <- Ht. ring. }
          (* 4b. 装配 Hssb *)
          rewrite Hss1.
          transitivity ((sum_upto (Datatypes.S (2 * n)) (fun i : nat => sum_upto (Datatypes.S (2 * n - i)) (fun k : nat => sin_term i x * sin_term k y)) -
                         sum_upto (Datatypes.S n) (fun i : nat => sum_upto (Datatypes.S n) (fun k : nat => sin_term i x * sin_term k y))) -
                        sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y)).
          * ring.
          * rewrite (qeqT_imp_qeq _ _ (sc_add_fam_decomp (fun i : nat => sin_term i x) (fun k : nat => sin_term k y) n)).
            reflexivity. }
        rewrite Hssb. reflexivity.
      * ring.
Qed.
(* ============================================================ *)
(* sH_cos_q3.v：cos 加法定理 Q 层——anti 对角带绝对界            *)
(* 依赖：q1, q2                                                    *)
(* ============================================================ *)

(* ============================================================ *)
(* B1：逐项 |sin_term j t| ≤ B^{2j+1}/(2j+1)!（|t| ≤ B）         *)
(* ============================================================ *)
Lemma sc_cos_add_sin_term_le : forall (t B : Q) (j : nat),
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (Qabs (sin_term j t)) (q_pow B (2 * j + 1) / q_fact (2 * j + 1)).
Proof.
  intros t B j HB HtB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (q_pow t (2 * j + 1) / q_fact (2 * j + 1))) _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    transitivity (q_pow (Qabs t) (2 * j + 1) / q_fact (2 * j + 1)).
    + rewrite (qeqT_imp_qeq _ _ (sc_abs_sin_term j t)).
      assert (Hn : (Datatypes.S (2 * j) = 2 * j + 1)%nat) by lia.
      rewrite Hn. reflexivity.
    + apply Qeq_sym.
      assert (Hn : (2 * j + 1 = Datatypes.S (2 * j))%nat) by lia.
      rewrite Hn.
      apply qeqT_imp_qeq. apply (q_abs_pow_fact t (2 * j)).
  - exact (QleT'_to_Qle _ _ (q_abs_pow_fact_le t B (2 * j + 1) (Qle_to_QleT' _ _ HB) (Qle_to_QleT' _ _ HtB))).
Qed.

(* ============================================================ *)
(* B2：角点 |s_n(x)·s_n(y)| ≤ (B^{2n+1}/(2n+1)!)²               *)
(* ============================================================ *)
Lemma sc_cos_add_corner_le : forall (x y B : Q) (n : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (sin_term n x * sin_term n y))
      ((q_pow B (2 * n + 1) / q_fact (2 * n + 1)) * (q_pow B (2 * n + 1) / q_fact (2 * n + 1))).
Proof.
  intros x y B n HB HxB HyB.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (sin_term n x) * Qabs (sin_term n y)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
  - set (Y := q_pow B (2 * n + 1) / q_fact (2 * n + 1)).
    apply (Qle_trans _ (Y * Qabs (sin_term n y)) _).
    + apply (Qmult_le_compat_r (Qabs (sin_term n x)) Y (Qabs (sin_term n y))).
      * unfold Y. apply QleT'_to_Qle. apply (sc_cos_add_sin_term_le x B n HB HxB).
      * apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (sin_term n y)) Y Y).
      * unfold Y. apply QleT'_to_Qle. apply (sc_cos_add_sin_term_le y B n HB HyB).
      * unfold Y. apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact (Qle_to_QleT' _ _ HB).
Qed.

(* ============================================================ *)
(* B3：非负单一项 ≤ 前缀/全和：f j ≤ Σ_{i<n} f i（j < n）       *)
(* ============================================================ *)
Lemma sc_sum_upto_single_le : forall (f : nat -> Q) (n : nat),
  (forall i : nat, Qle 0 (f i)) -> forall (j : nat), (j < n)%nat ->
  QleT' (f j) (sum_upto n f).
Proof.
  intros f n Hf j Hj.
  apply Qle_to_QleT'.
  (* sum_upto n f == sum_upto (S j) f + 尾部（n = S j + (n − S j)） *)
  apply (Qle_trans _ (sum_upto (Datatypes.S j) f) _).
  - (* f j ≤ sum_upto (S j) f = sum_upto j f + f j *)
    apply (Qle_trans (f j) (f j + sum_upto j f) (sum_upto (Datatypes.S j) f)).
    + apply (Qle_plus_nonneg_r (f j) (sum_upto j f)).
      apply QleT'_to_Qle. apply sc_sum_nonneg. intro i. apply Hf.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      change (sum_upto (Datatypes.S j) f) with (sum_upto j f + f j).
      ring.
  - (* 前缀 ≤ 全和：S j ≤ n（j < n）⟹ n = S j + (n − S j) *)
    assert (Hadd : (n = Datatypes.S j + (n - Datatypes.S j))%nat) by lia.
    rewrite Hadd.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_add (Datatypes.S j) (n - Datatypes.S j) f)).
    apply (Qle_plus_nonneg_r (sum_upto (Datatypes.S j) f)
            (sum_upto (n - Datatypes.S j) (fun k : nat => f ((Datatypes.S j + k)%nat)))).
    apply QleT'_to_Qle. apply sc_sum_nonneg. intro k. apply Hf.
Qed.

(* ============================================================ *)
(* B4：和式二分：Σ_{i=0}^{2n} == Σ_{i=0}^{n} + Σ_{m<n} (i = S n + m) *)
(* ============================================================ *)
Lemma sc_sum_upto_split2 : forall (n : nat) (f : nat -> Q), QeqT (sum_upto (Datatypes.S (2 * n)) f) (sum_upto (Datatypes.S n) f + sum_upto n (fun m : nat => f ((Datatypes.S n + m)%nat))).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  transitivity (sum_upto (Datatypes.S n + n) f).
  - apply Qeq_sym.
    apply qeqT_imp_qeq.
    apply (sum_upto_nat_eq (Datatypes.S n + n) (Datatypes.S (2 * n)) f).
    lia.
  - apply qeqT_imp_qeq.
    apply (sum_upto_add (Datatypes.S n) n f).
Qed.

(* ============================================================ *)
(* sH_cos_q4.v：anti 对角带绝对界（分组 + 单点≤和 + 尾桥）      *)
(* 依赖：q1, q2, q3                                              *)
(* ============================================================ *)

(* ============================================================ *)
(* A0：Σ_i (f i·c) == (Σ_i f i)·c（scale 换序）                 *)
(* ============================================================ *)
Lemma sc_sum_upto_scale_comm : forall (n : nat) (c : Q) (f : nat -> Q), QeqT (sum_upto n (fun i : nat => f i * c)) ((sum_upto n f) * c).
Proof.
  intros n c f.
  apply qeq_imp_qeqT.
  transitivity (c * sum_upto n f).
  - transitivity (sum_upto n (fun i : nat => c * f i)).
    + apply qeqT_imp_qeq.
      apply (sum_upto_ext n (fun i : nat => f i * c) (fun i : nat => c * f i)).
      intro i. apply qeq_imp_qeqT. apply Qmult_comm.
    + apply qeqT_imp_qeq.
      apply (sum_upto_scale n c f).
  - apply Qmult_comm.
Qed.

(* ============================================================ *)
(* A1：W := Σ_{m≤n} |s_{(n+m)} t| == |s_n t| + 尾（m≥1）        *)
(* ============================================================ *)
Lemma sc_cos_add_W_split : forall (t : Q) (n : nat), QeqT (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) t))) (Qabs (sin_term n t) +
  sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) t))).
Proof.
  intros t n.
  apply qeq_imp_qeqT.
  transitivity (Qabs (sin_term ((n + 0)%nat) t) +
                sum_upto n (fun m : nat => Qabs (sin_term ((n + Datatypes.S m)%nat) t))).
  - apply qeqT_imp_qeq.
    apply (sum_upto_rot n (fun m : nat => Qabs (sin_term ((n + m)%nat) t))).
  - transitivity (Qabs (sin_term n t) +
                  sum_upto n (fun m : nat => Qabs (sin_term ((n + Datatypes.S m)%nat) t))).
    + assert (Hn0 : (n + 0 = n)%nat) by lia.
      rewrite Hn0. reflexivity.
    + assert (Hsum : sum_upto n (fun m : nat => Qabs (sin_term ((n + Datatypes.S m)%nat) t)) ==
                     sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) t))).
      { apply qeqT_imp_qeq.
        apply (sum_upto_ext_below n
          (fun m : nat => Qabs (sin_term ((n + Datatypes.S m)%nat) t))
          (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) t))).
        intros m Hm.
        assert (HnS : (n + Datatypes.S m = Datatypes.S n + m)%nat) by lia.
        rewrite HnS. apply qeq_imp_qeqT. reflexivity. }
      rewrite Hsum. reflexivity.
Qed.

(* ============================================================ *)
(* A2：W ≤ Y + Tail（Y := B^{2n+1}/(2n+1)!，Tail := E(4n+1)−E(2n+1)） *)
(* ============================================================ *)
Lemma sc_cos_add_W_le : forall (t B : Q) (n : nat), (1 <= n)%nat ->
  Qle 0 B -> Qle (Qabs t) B ->
  QleT' (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) t)))
      (q_pow B (2 * n + 1) / q_fact (2 * n + 1) +
       (exp_series (4 * n + 1) B - exp_series (2 * n + 1) B)).
Proof.
  intros t B n Hn1 HB HtB.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_add_W_split t n)).
  apply Qplus_le_compat.
  - apply QleT'_to_Qle. apply (sc_cos_add_sin_term_le t B n HB HtB).
  - apply QleT'_to_Qle. apply (sc_add_d_tail_le t B n Hn1 HB HtB).
Qed.

(* ============================================================ *)
(* A2b：组1 逐项：i ≤ n ⟹ |s_i x|·|s (2n−i) y| ≤ |s_i x|·W     *)
(* ============================================================ *)
Lemma sc_cos_add_anti_per1 : forall (x y : Q) (n i : nat), (i <= n)%nat ->
  QleT' (Qabs (sin_term i x) * Qabs (sin_term ((2 * n - i)%nat) y))
      (Qabs (sin_term i x) *
       (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y)))).
Proof.
  intros x y n i Hi.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (sc_qmult_le_l
           (Qabs (sin_term ((2 * n - i)%nat) y))
           (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y)))
           (Qabs (sin_term i x))).
  - apply (Qle_trans _ (Qabs (sin_term ((n + (n - i))%nat) y)) _).
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      assert (Hidx : (2 * n - i = n + (n - i))%nat) by lia.
      rewrite Hidx. reflexivity.
    + apply QleT'_to_Qle. apply (sc_sum_upto_single_le
        (fun m : nat => Qabs (sin_term ((n + m)%nat) y)) (Datatypes.S n)
        (fun k : nat => Qabs_nonneg (sin_term ((n + k)%nat) y)) (n - i)).
      lia.
  - apply Qabs_nonneg.
Qed.

(* ============================================================ *)
(* A2c：组2 逐项：m < n ⟹ |s_{S n+m} x|·|s (2n−(S n+m)) y|     *)
(*                          ≤ |s_{S n+m} x|·head_y             *)
(* ============================================================ *)
Lemma sc_cos_add_anti_per2 : forall (x y : Q) (n m : nat), (m < n)%nat ->
  QleT' (Qabs (sin_term ((Datatypes.S n + m)%nat) x) *
       Qabs (sin_term ((2 * n - (Datatypes.S n + m))%nat) y))
      (Qabs (sin_term ((Datatypes.S n + m)%nat) x) *
       (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y)))).
Proof.
  intros x y n m Hm.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (sc_qmult_le_l
           (Qabs (sin_term ((2 * n - (Datatypes.S n + m))%nat) y))
           (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y)))
           (Qabs (sin_term ((Datatypes.S n + m)%nat) x))).
  - apply QleT'_to_Qle. apply (sc_sum_upto_single_le (fun i : nat => Qabs (sin_term i y)) (Datatypes.S n)
       (fun k : nat => Qabs_nonneg (sin_term k y))
       ((2 * n - (Datatypes.S n + m))%nat)).
    lia.
  - apply Qabs_nonneg.
Qed.

(* ============================================================ *)
(* A3：anti 对角带绝对界                                        *)
(*   |Σ_{i=0}^{2n} s_i(x)·s_{2n−i}(y)|                          *)
(*     ≤ E·Y + (1+1)·E·Tail                                     *)
(* ============================================================ *)
Lemma sc_add_cos_anti_le : forall (x y : Q) (n : nat) (B : Q),
  (1 <= n)%nat -> Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y)))
      (exp_series (2 * n + 1) B * (q_pow B (2 * n + 1) / q_fact (2 * n + 1)) +
       (1 + 1) * (exp_series (2 * n + 1) B * (exp_series (4 * n + 1) B - exp_series (2 * n + 1) B))).
Proof.
  intros x y n B Hn1 HB HxB HyB.
  apply Qle_to_QleT'.
  set (E := exp_series (2 * n + 1) B).
  set (Tail := exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
  set (Y := q_pow B (2 * n + 1) / q_fact (2 * n + 1)).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HEmono : Qle (exp_series (2 * n + 1) B) (exp_series (4 * n + 1) B)).
  { apply QleT'_to_Qle. apply exp_series_mono; [exact (Qle_to_QleT' _ _ HB) | lia]. }
  assert (HT0 : Qle 0 Tail).
  { unfold Tail. apply (proj1 (Qle_minus_iff (exp_series (2 * n + 1) B) (exp_series (4 * n + 1) B))).
    exact HEmono. }
  assert (HY0 : Qle 0 Y) by (unfold Y; apply QleT'_to_Qle; apply q_pow_fact_nonneg; exact (Qle_to_QleT' _ _ HB)).
  (* 求和界 *)
  assert (HxF : Qle (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i x))) E).
  { unfold E. exact (QleT'_to_Qle _ _ (sc_cs_d_full_le x B n HB HxB)). }
  assert (HyF : Qle (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y))) E).
  { unfold E. exact (QleT'_to_Qle _ _ (sc_cs_d_full_le y B n HB HyB)). }
  assert (HxT : Qle (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x))) Tail).
  { unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_d_tail_le x B n Hn1 HB HxB)). }
  assert (HWy : Qle (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y))) (Y + Tail)).
  { unfold Y, Tail. exact (QleT'_to_Qle _ _ (sc_cos_add_W_le y B n Hn1 HB HyB)). }
  (* 非负性 *)
  assert (HxF0 : Qle 0 (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i x)))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro i. apply Qabs_nonneg. }
  assert (HyF0 : Qle 0 (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y)))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro i. apply Qabs_nonneg. }
  assert (HxT0 : Qle 0 (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x)))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
  assert (HWy0 : Qle 0 (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y)))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
  (* |Σ| ≤ Σ|·| *)
  apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n)) (fun i : nat =>
      Qabs (sin_term i x * sin_term ((2 * n - i)%nat) y))) _).
  - apply QleT'_to_Qle. apply sum_upto_abs_le.
  - (* 换到 |s_i x|·|s (2n−i) y| *)
    apply (Qle_trans _ (sum_upto (Datatypes.S (2 * n)) (fun i : nat =>
        Qabs (sin_term i x) * Qabs (sin_term ((2 * n - i)%nat) y))) _).
    + apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S (2 * n))
        (fun i : nat => Qabs (sin_term i x * sin_term ((2 * n - i)%nat) y))
        (fun i : nat => Qabs (sin_term i x) * Qabs (sin_term ((2 * n - i)%nat) y))).
      intros i Hi. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
    + (* 分组：Σ_{i=0}^{2n} == Σ_{i≤n} + Σ_{m<n} *)
      set (G := fun i : nat => Qabs (sin_term i x) * Qabs (sin_term ((2 * n - i)%nat) y)).
      rewrite (qeqT_imp_qeq _ _ (sc_sum_upto_split2 n G)).
      apply (Qle_trans _
        ((sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i x))) *
           (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y))) +
         (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x))) *
           (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y)))) _).
      * apply (Qplus_le_compat
                 (sum_upto (Datatypes.S n) G)
                 ((sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i x))) *
                  (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y))))
                 (sum_upto n (fun m : nat => G ((Datatypes.S n + m)%nat)))
                 ((sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x))) *
                  (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y))))).
        -- (* 组1：Σ_{i≤n} u_i·w_{2n−i} ≤ (Σ_{i≤n} u_i)·W *)
           apply (Qle_trans _ (sum_upto (Datatypes.S n) (fun i : nat =>
               Qabs (sin_term i x) *
               (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y))))) _).
           ++ apply QleT'_to_Qle. apply (sum_upto_le_ext (Datatypes.S n) G
               (fun i : nat => Qabs (sin_term i x) *
                                (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y))))).
              intros i Hi. apply NatLe_drop in Hi.
              apply (sc_cos_add_anti_per1 x y n i). lia.
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              apply qeqT_imp_qeq. apply (sc_sum_upto_scale_comm (Datatypes.S n)
                (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y)))
                (fun i : nat => Qabs (sin_term i x))).
        -- (* 组2：Σ_{m<n} uTail_m·|s (2n−(Sn+m)) y| ≤ (Σ uTail)·head_y *)
           apply (Qle_trans _ (sum_upto n (fun m : nat =>
               Qabs (sin_term ((Datatypes.S n + m)%nat) x) *
               (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y))))) _).
           ++ apply QleT'_to_Qle. apply (sum_upto_le_ext n
               (fun m : nat => G ((Datatypes.S n + m)%nat))
               (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x) *
                                (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y))))).
              intros m Hm.
              apply (sc_cos_add_anti_per2 x y n m). exact (NatLe_drop _ _ Hm).
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              apply qeqT_imp_qeq. apply (sc_sum_upto_scale_comm n
                (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y)))
                (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x))).
      * apply (Qle_trans _
          ((E * (Y + Tail)) + (Tail * E)) _).
        -- apply Qplus_le_compat.
           ++ apply QleT'_to_Qle. apply (sc_prod_le (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i x)))
                                (sum_upto (Datatypes.S n) (fun m : nat => Qabs (sin_term ((n + m)%nat) y)))
                                E (Y + Tail));
              [exact HxF0 | exact HWy0 | exact HxF | exact HWy | exact HE0].
           ++ apply QleT'_to_Qle. apply (sc_prod_le (sum_upto n (fun m : nat => Qabs (sin_term ((Datatypes.S n + m)%nat) x)))
                                (sum_upto (Datatypes.S n) (fun i : nat => Qabs (sin_term i y)))
                                Tail E);
              [exact HxT0 | exact HyF0 | exact HxT | exact HyF | exact HT0].
        -- assert (Hfin : (E * (Y + Tail)) + (Tail * E) <= E * Y + (1 + 1) * (E * Tail))
             by (apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring).
           exact Hfin.
Qed.
(* ============================================================ *)
(* sH_cos_q5.v：cos 加法定理 Q 层——误差绝对界（err_abs/tail）  *)
(* 依赖：q1–q4                                                     *)
(* ============================================================ *)

(* ============================================================ *)
(* B2：泛型带对 ≤ 2·E·Tail（F ≤ E、T ≤ Tail）                  *)
(* ============================================================ *)
Lemma sc_cos_add_band2_le : forall (A B : nat -> Q) (n : nat) (E Tail : Q),
  Qle (sum_upto (Datatypes.S n) (fun j : nat => Qabs (A j))) E ->
  Qle (sum_upto n (fun m : nat => Qabs (B ((Datatypes.S n + m)%nat)))) Tail ->
  Qle (sum_upto n (fun m : nat => Qabs (A ((Datatypes.S n + m)%nat)))) Tail ->
  Qle (sum_upto (Datatypes.S n) (fun j : nat => Qabs (B j))) E ->
  Qle 0 E -> Qle 0 Tail ->
  QleT' (Qabs (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => A j * B ((Datatypes.S n + k)%nat))) +
             sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => A ((Datatypes.S n + j)%nat) * B i))))
      ((1 + 1) * (E * Tail)).
Proof.
  intros A B n E Tail HFA HTB HTA HFB HE0 HT0.
  apply Qle_to_QleT'.
  assert (HFA0 : Qle 0 (sum_upto (Datatypes.S n) (fun j : nat => Qabs (A j)))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro j. apply Qabs_nonneg. }
  assert (HTB0 : Qle 0 (sum_upto n (fun m : nat => Qabs (B ((Datatypes.S n + m)%nat))))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
  assert (HTA0 : Qle 0 (sum_upto n (fun m : nat => Qabs (A ((Datatypes.S n + m)%nat))))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro m. apply Qabs_nonneg. }
  assert (HFB0 : Qle 0 (sum_upto (Datatypes.S n) (fun j : nat => Qabs (B j)))).
  { apply QleT'_to_Qle. apply sc_sum_nonneg. intro j. apply Qabs_nonneg. }
  apply (Qle_trans _
    (((sum_upto (Datatypes.S n) (fun j : nat => Qabs (A j))) *
      (sum_upto n (fun m : nat => Qabs (B ((Datatypes.S n + m)%nat))))) +
     ((sum_upto n (fun m : nat => Qabs (A ((Datatypes.S n + m)%nat)))) *
      (sum_upto (Datatypes.S n) (fun j : nat => Qabs (B j))))) _).
  - apply QleT'_to_Qle. apply (sc_add_band_abs A B n).
  - apply (Qle_trans _ ((E * Tail) + (E * Tail)) _).
    + apply Qplus_le_compat.
      * apply QleT'_to_Qle. apply (sc_prod_le (sum_upto (Datatypes.S n) (fun j : nat => Qabs (A j)))
                          (sum_upto n (fun m : nat => Qabs (B ((Datatypes.S n + m)%nat))))
                          E Tail); [exact HFA0 | exact HTB0 | exact HFA | exact HTB | exact HE0].
      * apply (Qle_trans _ (Tail * E) _).
        -- apply QleT'_to_Qle. apply (sc_prod_le (sum_upto n (fun m : nat => Qabs (A ((Datatypes.S n + m)%nat))))
                             (sum_upto (Datatypes.S n) (fun j : nat => Qabs (B j)))
                             Tail E); [exact HTA0 | exact HFB0 | exact HTA | exact HFB | exact HT0].
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* E1：cos 误差绝对界                                           *)
(*   |cos_{2n}(x+y) − cp·cp + sp·sp| ≤ E·Y + 6·E·Tail          *)
(* ============================================================ *)
Lemma sc_add_cos_err_abs : forall (x y : Q) (n : nat) (B : Q),
  (1 <= n)%nat -> Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (cos_partial (2 * n) (x + y) - cos_partial n x * cos_partial n y + sin_partial n x * sin_partial n y))
      (exp_series (2 * n + 1) B * (q_pow B (2 * n + 1) / q_fact (2 * n + 1)) +
       ((1 + 1) * (1 + 1 + 1)) * (exp_series (2 * n + 1) B * (exp_series (4 * n + 1) B - exp_series (2 * n + 1) B))).
Proof.
  intros x y n B Hn1 HB HxB HyB.
  apply Qle_to_QleT'.
  set (E := exp_series (2 * n + 1) B).
  set (Tail := exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
  set (Y := q_pow B (2 * n + 1) / q_fact (2 * n + 1)).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HEmono : Qle (exp_series (2 * n + 1) B) (exp_series (4 * n + 1) B)).
  { apply QleT'_to_Qle. apply exp_series_mono; [exact (Qle_to_QleT' _ _ HB) | lia]. }
  assert (HT0 : Qle 0 Tail).
  { unfold Tail. apply (proj1 (Qle_minus_iff (exp_series (2 * n + 1) B) (exp_series (4 * n + 1) B))).
    exact HEmono. }
  (* err == D_cc − D_ss + anti（精确分解） *)
  apply QleT'_to_Qle. apply (sc_qabs_qeq_le
    (cos_partial (2 * n) (x + y) - cos_partial n x * cos_partial n y + sin_partial n x * sin_partial n y)
    ((sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
      sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * cos_term i y))) -
     (sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
      sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * sin_term i y))) +
     sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y))
    (E * Y + ((1 + 1) * (1 + 1 + 1)) * (E * Tail))).
  - exact (qeqT_imp_qeq _ _ (sc_add_cos_err_decomp x y n Hn1)).
  - set (Dc := sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S n + k)%nat) y)) +
              sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => cos_term ((Datatypes.S n + j)%nat) x * cos_term i y))).
    set (Ds := sum_upto (Datatypes.S n) (fun j : nat => sum_upto (n - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S n + k)%nat) y)) +
              sum_upto n (fun j : nat => sum_upto (Datatypes.S (2 * n - Datatypes.S n - j)) (fun i : nat => sin_term ((Datatypes.S n + j)%nat) x * sin_term i y))).
    set (An := sum_upto (Datatypes.S (2 * n)) (fun i : nat => sin_term i x * sin_term ((2 * n - i)%nat) y)).
    (* 分量界 *)
    assert (Hc2 : Qle (Qabs Dc) ((1 + 1) * (E * Tail))).
    { unfold Dc.
      apply QleT'_to_Qle. apply (sc_cos_add_band2_le (fun j : nat => cos_term j x) (fun k : nat => cos_term k y) n E Tail).
      - unfold E. exact (QleT'_to_Qle _ _ (sc_cs_c_full_le x B n HB HxB)).
      - unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_c_tail_le y B n HB HyB)).
      - unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_c_tail_le x B n HB HxB)).
      - unfold E. exact (QleT'_to_Qle _ _ (sc_cs_c_full_le y B n HB HyB)).
      - exact HE0.
      - exact HT0. }
    assert (Hs2 : Qle (Qabs Ds) ((1 + 1) * (E * Tail))).
    { unfold Ds.
      apply QleT'_to_Qle. apply (sc_cos_add_band2_le (fun j : nat => sin_term j x) (fun k : nat => sin_term k y) n E Tail).
      - unfold E. exact (QleT'_to_Qle _ _ (sc_cs_d_full_le x B n HB HxB)).
      - unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_d_tail_le y B n Hn1 HB HyB)).
      - unfold Tail. exact (QleT'_to_Qle _ _ (sc_add_d_tail_le x B n Hn1 HB HxB)).
      - unfold E. exact (QleT'_to_Qle _ _ (sc_cs_d_full_le y B n HB HyB)).
      - exact HE0.
      - exact HT0. }
    assert (Ha2 : Qle (Qabs An) (E * Y + ((1 + 1) * (E * Tail)))).
    { unfold An. unfold E, Y, Tail. exact (QleT'_to_Qle _ _ (sc_add_cos_anti_le x y n B Hn1 HB HxB HyB)). }
    (* |Dc − Ds + An| ≤ |Dc| + |Ds| + |An|（双三角） *)
    apply (Qle_trans _ (Qabs (Dc - Ds) + Qabs An) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (Qabs Dc + Qabs Ds + Qabs An) _).
      * apply (Qplus_le_compat (Qabs (Dc - Ds)) (Qabs Dc + Qabs Ds) (Qabs An) (Qabs An)).
        -- apply (Qle_trans _ (Qabs (Dc + - Ds)) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
           ++ apply (Qle_trans _ (Qabs Dc + Qabs (- Ds)) _).
              ** apply Qabs_triangle.
              ** apply (Qplus_le_compat (Qabs Dc) (Qabs Dc) (Qabs (- Ds)) (Qabs Ds)).
                 --- apply Qle_refl.
                 --- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_opp.
        -- apply Qle_refl.
      * apply (Qle_trans _
          (((1 + 1) * (E * Tail)) + ((1 + 1) * (E * Tail)) + (E * Y + ((1 + 1) * (E * Tail)))) _).
        -- apply (Qplus_le_compat (Qabs Dc + Qabs Ds)
                 (((1 + 1) * (E * Tail)) + ((1 + 1) * (E * Tail)))
                 (Qabs An) (E * Y + ((1 + 1) * (E * Tail)))).
           ++ apply (Qplus_le_compat (Qabs Dc) ((1 + 1) * (E * Tail)) (Qabs Ds) ((1 + 1) * (E * Tail))).
              ** exact Hc2.
              ** exact Hs2.
           ++ exact Ha2.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* E2：err 尾界（Tail → X := exp_tail_abs (2n+1)(4n+1) B）      *)
(* ============================================================ *)
Lemma sc_add_cos_err_tail_le : forall (x y : Q) (n : nat) (B : Q),
  (1 <= n)%nat -> Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  QleT' (Qabs (cos_partial (2 * n) (x + y) - cos_partial n x * cos_partial n y + sin_partial n x * sin_partial n y))
      (exp_series (2 * n + 1) B * (q_pow B (2 * n + 1) / q_fact (2 * n + 1)) +
       ((1 + 1) * (1 + 1 + 1)) * (exp_series (2 * n + 1) B * exp_tail_abs (2 * n + 1) (4 * n + 1) B)).
Proof.
  intros x y n B Hn1 HB HxB HyB.
  apply Qle_to_QleT'.
  set (E := exp_series (2 * n + 1) B).
  set (Tail := exp_series (4 * n + 1) B - exp_series (2 * n + 1) B).
  set (X := exp_tail_abs (2 * n + 1) (4 * n + 1) B).
  set (Y := q_pow B (2 * n + 1) / q_fact (2 * n + 1)).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HX0 : Qle 0 X) by (unfold X; apply QleT'_to_Qle; apply exp_tail_abs_nonneg; apply Qle_to_QleT'; exact HB).
  assert (HTX : Qle Tail X).
  { unfold Tail, X. apply QleT'_to_Qle. apply (exp_series_tail_le B (2 * n + 1) (4 * n + 1) (Qle_to_QleT' _ _ HB)). lia. }
  apply (Qle_trans _ (E * Y + ((1 + 1) * (1 + 1 + 1)) * (E * Tail)) _).
  - unfold E, Y, Tail. exact (QleT'_to_Qle _ _ (sc_add_cos_err_abs x y n B Hn1 HB HxB HyB)).
  - apply (Qle_trans _ (E * Y + ((1 + 1) * (1 + 1 + 1)) * (E * X)) _).
    + apply (Qplus_le_compat (E * Y) (E * Y) (((1 + 1) * (1 + 1 + 1)) * (E * Tail)) (((1 + 1) * (1 + 1 + 1)) * (E * X))).
      * apply Qle_refl.
      * assert (Hs1 : Qle 0 ((1 + 1) * (1 + 1 + 1))) by (unfold Qle; simpl; lia).
        apply QleT'_to_Qle. apply (sc_qmult_le_l (E * Tail) (E * X) ((1 + 1) * (1 + 1 + 1))).
        -- apply QleT'_to_Qle. apply (sc_qmult_le_l Tail X E); [exact HTX | exact HE0].
        -- exact Hs1.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.
(* ============================================================ *)
(* sH_cos_q6.v：cos 加法定理 Q 层——模量 sc_add_cos_err_bound     *)
(* 依赖：q1–q5                                                     *)
(* ============================================================ *)

(* ============================================================ *)
(* M1：模量                                                  *)
(*   ∀B eps（0 ≤T B、0 <T eps）∃N，∀x y n ≥ N，|x|,|y| ≤ B：  *)
(*     |cos_{2n}(x+y) − cp_n(x)cp_n(y) + sp_n(x)sp_n(y)| < eps *)
(*   链：|err| ≤ E·Y + 6·E·X（err_tail）≤ (C + 12·C)·Y ≤       *)
(*       13·C·(B^{N0}/N0!)·(1/2)^{2n+1−N0} ≤ P·(1/2)^{S t}    *)
(* ============================================================ *)
Lemma sc_add_cos_err_bound : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall (x y : Q) (n : nat), NatLe N n ->
    QleT' (Qabs x) B -> QleT' (Qabs y) B ->
    QltT (Qabs (cos_partial (2 * n) (x + y) - cos_partial n x * cos_partial n y + sin_partial n x * sin_partial n y)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  destruct (exp_series_arch B HB) as [C [HC1 HC]].
  assert (HC0 : Qle 0 C) by (apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1)) by (apply QleT'_to_Qle; apply Q2_nonneg).
  assert (Hsix0 : Qle 0 ((1 + 1) * (1 + 1 + 1))) by (unfold Qle; simpl; lia).
  (* P := 13·C·(B^{N0}/N0!)（13 = 12 + 1 = (1+1)(1+1+1+1+1+1) + 1） *)
  set (P := (((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * (C * (q_pow B N0 / q_fact N0))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply (Qmult_le_0_compat _ _).
    - unfold Qle; simpl; lia.
    - apply (Qmult_le_0_compat C (q_pow B N0 / q_fact N0)).
      + exact HC0.
      + apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HB. }
  destruct (arch_decay P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists (N0 + Datatypes.S t)%nat.
  intros x y n HNn HxB HyB.
  apply NatLe_drop in HNn.
  assert (HBle : Qle 0 B) by exact (QleT'_to_Qle _ _ HB).
  assert (HxBe : Qle (Qabs x) B) by exact (QleT'_to_Qle _ _ HxB).
  assert (HyBe : Qle (Qabs y) B) by exact (QleT'_to_Qle _ _ HyB).
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (HN0geom : forall u : nat, (N0 <= u)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (HN0m : (N0 <= 2 * n + 1)%nat) by lia.
  assert (Hmlen : (2 * n + 1 <= 4 * n + 1)%nat) by lia.
  assert (HNgeom2 : forall u : nat, (2 * n + 1 <= u)%nat -> Qle (Qmult (1 + 1)%Q B) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply HN0geom. lia. }
  assert (Hj : (Datatypes.S t <= 2 * n + 1 - N0)%nat) by lia.
  set (E := exp_series (2 * n + 1) B).
  set (X := exp_tail_abs (2 * n + 1) (4 * n + 1) B).
  set (Y := q_pow B (2 * n + 1) / q_fact (2 * n + 1)).
  assert (HE0 : Qle 0 E) by (unfold E; apply QleT'_to_Qle; apply exp_series_nonneg; apply Qle_to_QleT'; exact HBle).
  assert (HEC : Qle E C) by (unfold E; apply QleT'_to_Qle; exact (HC ((2 * n + 1)%nat))).
  assert (HX0 : Qle 0 X) by (unfold X; apply QleT'_to_Qle; apply exp_tail_abs_nonneg; apply Qle_to_QleT'; exact HBle).
  assert (HXg : Qle X (Y * (1 + 1))).
  { unfold X, Y. apply QleT'_to_Qle. apply (exp_tail_abs_geom2 B (2 * n + 1) (4 * n + 1) (Qle_to_QleT' _ _ HBle) (fun u Hu => Qle_to_QleT' _ _ (HNgeom2 u (NatLe_drop _ _ Hu))) Hmlen). }
  assert (HY0 : Qle 0 Y) by (unfold Y; apply QleT'_to_Qle; apply q_pow_fact_nonneg; exact (Qle_to_QleT' _ _ HBle)).
  assert (HY2_0 : Qle 0 (Y * (1 + 1))) by (unfold Y; apply QleT'_to_Qle; apply q_pow_fact2_nonneg; apply Qle_to_QleT'; exact HBle).
  assert (HYdec : Qle Y ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0))).
  { unfold Y. apply QleT'_to_Qle. apply (pow_fact_decay B N0 (2 * n + 1) (Qle_to_QleT' _ _ HBle) (fun u Hu => Qle_to_QleT' _ _ (HN0geom u (NatLe_drop _ _ Hu)))). lia. }
  assert (Hq0 : Qle 0 (q_pow (1 / 2)%Q (2 * n + 1 - N0))) by (apply QleT'_to_Qle; apply q_pow_nonneg; exact Qhalf_nonneg).
  assert (HD0 : Qle 0 ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0))).
  { apply (Qmult_le_0_compat (q_pow B N0 / q_fact N0) (q_pow (1 / 2)%Q (2 * n + 1 - N0))).
    - apply QleT'_to_Qle. apply q_pow_fact_nonneg; apply Qle_to_QleT'. exact HBle.
    - exact Hq0. }
  assert (Hhalf0 : Qle 0 (q_pow (1 / 2)%Q (Datatypes.S t))) by (apply QleT'_to_Qle; apply q_pow_nonneg; exact Qhalf_nonneg).
  assert (Hdec : Qle (q_pow (1 / 2)%Q (2 * n + 1 - N0)) (q_pow (1 / 2)%Q (Datatypes.S t))).
  { apply QleT'_to_Qle. apply (q_half_pow_mono (2 * n + 1 - N0) (Datatypes.S t)). exact Hj. }
  assert (H13C0 : Qle 0 ((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * C)).
  { apply (Qmult_le_0_compat (((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) C).
    - unfold Qle; simpl; lia.
    - exact HC0. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (P * q_pow (1 / 2)%Q (Datatypes.S t)) _).
  - (* |err| ≤ E·Y + 6·E·X ≤ ... ≤ P·(1/2)^{S t} *)
    apply (Qle_trans _ (E * Y + (((1 + 1) * (1 + 1 + 1)) * (E * X))) _).
    + unfold E, X, Y. exact (QleT'_to_Qle _ _ (sc_add_cos_err_tail_le x y n B Hn1 HBle HxBe HyBe)).
    + (* ≤ C·Y + 6·C·X *)
      apply (Qle_trans _ (C * Y + (((1 + 1) * (1 + 1 + 1)) * (C * X))) _).
      * apply Qplus_le_compat.
        -- apply (Qmult_le_compat_r E C Y); [exact HEC | exact HY0].
        -- apply QleT'_to_Qle. apply (sc_qmult_le_l (E * X) (C * X) ((1 + 1) * (1 + 1 + 1))).
           ++ apply (Qmult_le_compat_r E C X); [exact HEC | exact HX0].
           ++ exact Hsix0.
      * (* ≤ C·Y + 6·(C·(Y·2))，再 == 13·C·Y *)
        apply (Qle_trans _ (C * Y + (((1 + 1) * (1 + 1 + 1)) * (C * (Y * (1 + 1))))) _).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply QleT'_to_Qle. apply (sc_qmult_le_l (C * X) (C * (Y * (1 + 1))) ((1 + 1) * (1 + 1 + 1))).
              ** apply QleT'_to_Qle. apply (sc_qmult_le_l X (Y * (1 + 1)) C).
                 --- exact HXg.
                 --- exact HC0.
              ** exact Hsix0.
        -- apply (Qle_trans _ ((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * (C * Y)) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ (* 13·(C·Y) ≤ (13·C)·Y ≤ (13·C)·b ≤ P·(1/2)^w ≤ P·(1/2)^{S t} *)
              apply (Qle_trans _ (((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * C) * Y) _).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              ** apply (Qle_trans _ (((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * C) *
                                     ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0))) _).
                 --- apply QleT'_to_Qle. apply (sc_qmult_le_l Y ((q_pow B N0 / q_fact N0) * q_pow (1 / 2)%Q (2 * n + 1 - N0))
                                            ((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * C)).
                     ++++ exact HYdec.
                     ++++ exact H13C0.
                 --- apply (Qle_trans _ (P * q_pow (1 / 2)%Q (2 * n + 1 - N0)) _).
                     ++++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold P. ring.
                     ++++ apply QleT'_to_Qle. apply (sc_qmult_le_l (q_pow (1 / 2)%Q (2 * n + 1 - N0))
                                               (q_pow (1 / 2)%Q (Datatypes.S t)) P).
                          +++++ exact Hdec.
                          +++++ exact HP0.
  - exact (QltT_to_Qlt _ _ Ht).
Qed.
(* ============================================================ *)
(* sH_real.v：cos 加法定理 Real 层——rs_add_cos 装配              *)
(*   cos(x+y) == cos x·cos y − sin x·sin y（real_eq）            *)
(* 依赖：q1–q6（cos Q 层模量链）                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* rs_add_cos：Real 层 cos 加法（rs_add_sin 的 eps/3 装配模板） *)
(* ============================================================ *)
Lemma rs_add_cos : forall (X Y : Real),
  real_eq (cauchy_real_cos (real_plus X Y))
          (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos Y))
                     (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin Y)))).
Proof.
  intros X Y.
  destruct X as [u Hu]. destruct Y as [v Hv].
  unfold real_eq.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mx [HMxpos HMx]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [My [HMypos HMy]].
  set (M := Mx + My).
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
      + apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  assert (HsumMT : forall n : nat, QleT' (Qabs (u n + v n)) M).
  { intro n. unfold M. apply (qleT'_trans (Qabs (u n + v n)) (Qabs (u n) + Qabs (v n)) (Mx + My)).
    - apply Qle_to_QleT'. apply Qabs_triangle.
    - apply (qleT'_plus_compat (Qabs (u n)) Mx (Qabs (v n)) My).
      + apply HMx.
      + apply HMy. }
  assert (Heps3T : QltT 0 (eps / 3)).
  { apply (qltT_div_pos eps 3). exact Heps. exact qltT_0_3. }
  destruct (sc_cos_partial_cauchy_bounded M (eps / 3) HMnonnegT Heps3T) as [N1 HN1].
  destruct (sc_add_cos_err_bound M (eps / 3) HMnonnegT Heps3T) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  apply NatLe_drop in Hn.
  apply Qlt_to_QltT.
  change (Qlt (Qabs (cos_partial n (u n + v n) -
                     (cos_partial n (u n) * cos_partial n (v n) -
                      sin_partial n (u n) * sin_partial n (v n)))) eps).
  (* 代数拆分：cos_n(u+v) − (P − Q) == (cos_n(u+v) − cos_{2n}(u+v)) + (cos_{2n}(u+v) − P + Q) *)
  apply (Qle_lt_trans _ (Qabs (cos_partial n (u n + v n) - cos_partial (2 * n) (u n + v n)) +
                          Qabs (cos_partial (2 * n) (u n + v n) - cos_partial n (u n) * cos_partial n (v n) +
                                sin_partial n (u n) * sin_partial n (v n))) _).
  - apply (Qle_trans _ (Qabs ((cos_partial n (u n + v n) - cos_partial (2 * n) (u n + v n)) +
                               (cos_partial (2 * n) (u n + v n) - cos_partial n (u n) * cos_partial n (v n) +
                                sin_partial n (u n) * sin_partial n (v n)))) _).
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      apply (Qabs_wd (cos_partial n (u n + v n) -
                      (cos_partial n (u n) * cos_partial n (v n) -
                       sin_partial n (u n) * sin_partial n (v n)))
                     ((cos_partial n (u n + v n) - cos_partial (2 * n) (u n + v n)) +
                      (cos_partial (2 * n) (u n + v n) - cos_partial n (u n) * cos_partial n (v n) +
                       sin_partial n (u n) * sin_partial n (v n)))).
      ring.
    + apply Qabs_triangle.
  - apply (Qlt_le_trans _ (eps / 3 + eps / 3) _).
    + apply Qplus_lt_compat.
      * apply QltT_to_Qlt.
        apply (HN1 n ((2 * n)%nat)).
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact Hn].
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | lia].
        -- exact (HsumMT n).
      * apply QltT_to_Qlt.
        apply (HN2 (u n) (v n) n).
        -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact Hn].
        -- exact (HuMT n).
        -- exact (HvMT n).
    + apply (Qle_trans _ (Qmult (Qinv 3 + Qinv 3) eps) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
      * apply (Qle_trans _ (Qmult 1 eps) _).
        -- apply (Qmult_le_compat_r (Qinv 3 + Qinv 3) 1 eps).
           ++ unfold Qle, Qinv, Qplus. simpl. lia.
           ++ apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* real_sin_add：rs_add_sin 别名（sin 侧已入库名，此处补齐       *)
(* real_sin_add 命名便于对称检索）                              *)
(* ============================================================ *)
Lemma real_sin_add : forall (X Y : Real),
  real_eq (cauchy_real_sin (real_plus X Y))
          (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos Y))
                     (real_mult (cauchy_real_cos X) (cauchy_real_sin Y))).
Proof.
  exact rs_add_sin.
Qed.

(* ============================================================ *)
(* SC-2 批（并入 202）：B1 setoid 签名迁移——论文 2 头条等号簇 *)
(* 三定理迁移到 RealInterfaceEnhancedSetoid 签名（sB0/sB1，     *)
(* 用户 P0：主定理配套已完成实例 RealEnhancedReal）       *)
(* ============================================================ *)

(* ============================================================ *)
(* b1_attngibbs_setoid.v — B1：AttentionGibbsBridge 等号簇 3 头条 *)
(* 签名迁移：Id 系签名（RealInterfaceEnhanced）→ Setoid 系签名   *)
(* （RealInterfaceEnhancedSetoid，实例 RealEnhancedReal 可依存） *)
(* 沙箱：演变\.ablation\sc2_parallel\sB1_migrate\（只写沙箱）    *)
(* 契约：sB0 第 0 项迁移规范。*)
(* 路线 = 上提：以 Real 层 req 链证明（real_attention_is_gibbs     *)
(*   42359 / real_steady_state_boltzmann_attn 42450）为蓝本：      *)
(*   real_eq → req、RealSetoid.real_eq_*_compat → 接口字段          *)
(*   req_*_compat（39639-39648）、real_inv_pos_ext → inv_pos_ext    *)
(*   字段（39686）。                                                *)
(* 纪律：零公理、全件 Qed；不用 rewrite 作用于 req（无 Proper    *)
(*   注册）——证明全为显式 req 链（req_trans/req_sym + req_*_compat）。*)
(* 命名：新增名全部 _setoid 后缀（防顶层冲突）；诚实接口 Variable   *)
(*   用规范 §4 名（sum_req_over_S 等）。只增不改，不触碰 Id 系。  *)
(* ============================================================ *)

(* ============================================================ *)
(* B1-1：Section 骨架（规范 §4 模板）                          *)
(* 投影名/限定名先经 b1_00_check.v 实测：                         *)
(*   类 RealInterfaceEnhancedSetoid 以 R : Set 为参数（非字段）； *)
(*   字段投影形如 @RealInterfaceEnhancedMod.<field> R RI；         *)
(*   实例 RealInterfaceEnhancedMod.RealEnhancedReal。             *)
(* ============================================================ *)
Section AttentionGibbsBridgeSetoid.

(* 世界件 RealInterfaceEnhancedSetoid 系无参 Class（字段全用全局 Real）·
   本节原 {R : Set}{RI : ... R} 参数化形系异件误植——改为 Notation 直通全局形 *)
Notation R := Real.

(* ---- 运算投影（Let 简化书写） ---- *)
Let zero : R := @RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal.
Let one : R := @RealInterfaceEnhancedMod.one RealInterfaceEnhancedMod.RealEnhancedReal.
Let plus : R -> R -> R := @RealInterfaceEnhancedMod.plus RealInterfaceEnhancedMod.RealEnhancedReal.
Let mult : R -> R -> R := @RealInterfaceEnhancedMod.mult RealInterfaceEnhancedMod.RealEnhancedReal.
Let opp : R -> R := @RealInterfaceEnhancedMod.opp RealInterfaceEnhancedMod.RealEnhancedReal.
Let abs : R -> R := @RealInterfaceEnhancedMod.abs RealInterfaceEnhancedMod.RealEnhancedReal.
Let lt : R -> R -> Set := real_lt.
Let le : R -> R -> Set := real_le.
Let req : R -> R -> Set := real_eq.
Let inv_pos : forall x : R, lt zero x -> R := @RealInterfaceEnhancedMod.inv_pos RealInterfaceEnhancedMod.RealEnhancedReal.
Let exp_neg : R -> R := @RealInterfaceEnhancedMod.exp_neg RealInterfaceEnhancedMod.RealEnhancedReal.

(* ---- 接口字段投影（req 证明链用；Let 遮蔽全局同名投影） ---- *)
Let req_refl := @RealInterfaceEnhancedMod.req_refl RealInterfaceEnhancedMod.RealEnhancedReal.
Let req_sym := @RealInterfaceEnhancedMod.req_sym RealInterfaceEnhancedMod.RealEnhancedReal.
Let req_trans := @RealInterfaceEnhancedMod.req_trans RealInterfaceEnhancedMod.RealEnhancedReal.
Let req_mult_compat := @RealInterfaceEnhancedMod.req_mult_compat RealInterfaceEnhancedMod.RealEnhancedReal.
Let req_opp_compat := @RealInterfaceEnhancedMod.req_opp_compat RealInterfaceEnhancedMod.RealEnhancedReal.
Let mult_comm := @RealInterfaceEnhancedMod.mult_comm RealInterfaceEnhancedMod.RealEnhancedReal.
Let mult_one := @RealInterfaceEnhancedMod.mult_one RealInterfaceEnhancedMod.RealEnhancedReal.
Let mult_positive := @RealInterfaceEnhancedMod.mult_positive RealInterfaceEnhancedMod.RealEnhancedReal.
Let inv_pos_correct := @RealInterfaceEnhancedMod.inv_pos_correct RealInterfaceEnhancedMod.RealEnhancedReal.
Let inv_pos_pos := @RealInterfaceEnhancedMod.inv_pos_pos RealInterfaceEnhancedMod.RealEnhancedReal.
Let inv_pos_ext := @RealInterfaceEnhancedMod.inv_pos_ext RealInterfaceEnhancedMod.RealEnhancedReal.
Let exp_neg_pos := @RealInterfaceEnhancedMod.exp_neg_pos RealInterfaceEnhancedMod.RealEnhancedReal.
Let exp_neg_le_decr := @RealInterfaceEnhancedMod.exp_neg_le_decr RealInterfaceEnhancedMod.RealEnhancedReal.
Let le_antisym := @RealInterfaceEnhancedMod.le_antisym RealInterfaceEnhancedMod.RealEnhancedReal.
Let lt_le_iff := @RealInterfaceEnhancedMod.lt_le_iff RealInterfaceEnhancedMod.RealEnhancedReal.

(* ---- 诚实接口：抽象 S 上 req 版求和 ---- *)
(* 先例：RealAttnMain 42312-42317（sum_over_S + sum_pos_preserved）、 *)
(* RealAttnSteady 42420-42425（ext + linear）。Section 关闭后这些     *)
(* Variable 自动成为 forall 参数（零公理）。                          *)
Variable S : Type.
Variable sum_req_over_S : (S -> R) -> R.
Variable sum_req_over_S_ext : forall (f g : S -> R),
  (forall s : S, req (f s) (g s)) -> req (sum_req_over_S f) (sum_req_over_S g).
Variable sum_req_over_S_linear : forall (a : R) (f : S -> R),
  req (sum_req_over_S (fun s : S => mult a (f s))) (mult a (sum_req_over_S f)).
Variable sum_pos_preserved_req : forall (f : S -> R),
  (forall s : S, lt zero (f s)) -> lt zero (sum_req_over_S f).

(* ============================================================ *)
(* B1-2：softmax / Boltzmann 基础设施（req 版）                 *)
(*   蓝本：Id 27327-27393（结构）+ Real 42326-42355（req 链式） *)
(* ============================================================ *)

(* e^x := exp_neg(-x)（命名避免与 Stdlib exp 冲突） *)
Definition exp_pos_fn_setoid (x : R) : R := exp_neg (opp x).

Definition partition_function_setoid (z : S -> R) : R :=
  sum_req_over_S (fun s : S => exp_pos_fn_setoid (z s)).

(* 配分函数正性：Σ_s e^{z s} > 0（sum_pos_preserved_req + exp_neg_pos） *)
Lemma partition_function_pos_setoid :
  forall z : S -> R, lt zero (partition_function_setoid z).
Proof.
intros z.
  unfold partition_function_setoid, exp_pos_fn_setoid.
  apply sum_pos_preserved_req.
  intro s. apply exp_neg_pos.
Qed.

Definition softmax_setoid (z : S -> R) (s : S) : R :=
  mult (exp_pos_fn_setoid (z s))
       (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z)).

(* softmax 正性：注意力权重 > 0（exp 正 × 逆元正） *)
Lemma softmax_pos_setoid :
  forall z : S -> R, forall s : S, lt zero (softmax_setoid z s).
Proof.
intros z s.
  unfold softmax_setoid, exp_pos_fn_setoid.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* exp_neg 的 req 外延性（接口无该字段；由 exp_neg_le_decr + le_antisym
   + lt_le_iff + req_sym 派生——按规范 §7 不立诚实接口 Variable） *)
Lemma exp_neg_req_compat_setoid : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
intros x y Hxy.
  apply (le_antisym (exp_neg x) (exp_neg y)).
  - apply (exp_neg_le_decr y x).
    apply (lt_le_iff y x). right. apply (req_sym x y Hxy).
  - apply (exp_neg_le_decr x y).
    apply (lt_le_iff x y). right. exact Hxy.
Qed.

(* softmax 归一化：Σ_s softmax(z,s) == 1（概率质量守恒）
   组装：逐点 mult 交换（ext + mult_comm）→ 常数因子提取（linear）
   → Σ e^{z·} 折叠为配分函数 → inv_pos_correct 证毕（+ comm） *)
Lemma softmax_normalized_setoid :
  forall z : S -> R, req (sum_req_over_S (fun s : S => softmax_setoid z s)) one.
Proof.
intro z.
  unfold softmax_setoid.
  apply (req_trans _ (sum_req_over_S (fun s : S =>
        mult (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
             (exp_pos_fn_setoid (z s)))) _).
  - apply (sum_req_over_S_ext (fun s : S =>
        mult (exp_pos_fn_setoid (z s))
             (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z)))
                              (fun s : S =>
        mult (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
             (exp_pos_fn_setoid (z s)))).
    intro s. apply (mult_comm (exp_pos_fn_setoid (z s))
                              (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))).
  - apply (req_trans _ (mult (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
                             (sum_req_over_S (fun s : S => exp_pos_fn_setoid (z s)))) _).
    + apply (sum_req_over_S_linear (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
                                   (fun s : S => exp_pos_fn_setoid (z s))).
    + apply (req_trans _ (mult (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
                               (partition_function_setoid z)) _).
      * apply req_refl.   (* Σ e^{z·} 折叠为 partition_function_setoid（δ 转换） *)
      * apply (req_trans _ (mult (partition_function_setoid z)
                                 (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))) _).
        -- apply (mult_comm (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
                            (partition_function_setoid z)).
        -- apply (inv_pos_correct (partition_function_setoid z) (partition_function_pos_setoid z)).
Qed.

(* ============================================================ *)
(* B1-2（续）：Boltzmann 分布（温度 D > 0，能量 energy）         *)
(*   蓝本：Id 27803-27817 + Real 42343-42354                    *)
(* ============================================================ *)

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.   (* 注意力 logits（attention_is_gibbs_setoid 前提变量） *)

Definition boltzmann_factor_setoid (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo_setoid : R := sum_req_over_S boltzmann_factor_setoid.

(* Z_thermo 正性：RealAttnMain 42350 / RealAttnSteady 42430 同款诚实接口 Variable *)
Variable Z_thermo_pos : lt zero Z_thermo_setoid.

Definition boltzmann_dist_attn_setoid (s : S) : R :=
  mult (inv_pos Z_thermo_setoid Z_thermo_pos) (boltzmann_factor_setoid s).

(* ============================================================ *)
(* B1-4：单位温度 softmax = Boltzmann（主定理 1/3 迁移）           *)
(*   语句：Id 27823-27827 的 Id→req 版（Real 42359-42363 同型） *)
(*   证明：Real 42364-42404 上提：req_trans / req_mult_compat /  *)
(*   req_opp_compat 换为 exp_neg_req_compat_setoid（接口无 exp_neg *)
(*   Proper，派生引理承担）/ inv_pos_ext / mult_comm / mult_one  *)
(* ============================================================ *)
Theorem attention_is_gibbs_setoid :
  (req (inv_pos D D_pos) one) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  req Z_thermo_setoid (partition_function_setoid z) ->
  forall s : S, req (softmax_setoid z s) (boltzmann_dist_attn_setoid s).
Proof.
  intros HD Henergy HZ s.
  unfold softmax_setoid, boltzmann_dist_attn_setoid, boltzmann_factor_setoid, exp_pos_fn_setoid.
  (* 1. Boltzmann 侧指数归约：e^{−e(s)/D} == e^{z s}
        （mult (inv D) (energy s) == energy s == opp (z s)） *)
  assert (Hbf : req (exp_neg (mult (inv_pos D D_pos) (energy s)))
                    (exp_neg (opp (z s)))).
  {
    assert (Hm : req (mult (inv_pos D D_pos) (energy s)) (opp (z s))).
    {
      apply (req_trans _ (energy s) _).
      - apply (req_trans _ (mult one (energy s)) _).
        + apply (req_mult_compat (inv_pos D D_pos) one (energy s) (energy s) HD (req_refl _)).
        + apply (req_trans _ _ _ (mult_comm one (energy s)) (mult_one (energy s))).
      - exact (Henergy s).
    }
    apply exp_neg_req_compat_setoid.
    exact Hm.
  }
  (* 2. 逆元统一：inv(Z_thermo) == inv(partition_function z)（HZ + inv_pos_ext） *)
  assert (Hinv : req (inv_pos Z_thermo_setoid Z_thermo_pos)
                     (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))).
  {
    apply (inv_pos_ext Z_thermo_setoid (partition_function_setoid z) Z_thermo_pos (partition_function_pos_setoid z)).
    exact HZ.
  }
  (* 3. 组装：mult (e^{z s}) (inv Pf) == mult (inv Z) (e^{−e/D})
        （LHS 定义性 = 中间项；inv 统一（sym Hinv）→ comm → 指数替换（sym Hbf）） *)
  apply (req_trans _ (mult (exp_neg (opp (z s)))
                           (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))) _).
  - apply req_refl.
  - apply (req_trans _ (mult (exp_neg (opp (z s))) (inv_pos Z_thermo_setoid Z_thermo_pos)) _).
    + apply (req_mult_compat (exp_neg (opp (z s)))
                             (exp_neg (opp (z s)))
                             (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
                             (inv_pos Z_thermo_setoid Z_thermo_pos)
                             (req_refl _)
                             (req_sym (inv_pos Z_thermo_setoid Z_thermo_pos)
                                      (inv_pos (partition_function_setoid z) (partition_function_pos_setoid z))
                                      Hinv)).
    + apply (req_trans _ (mult (inv_pos Z_thermo_setoid Z_thermo_pos) (exp_neg (opp (z s)))) _).
      * apply (mult_comm (exp_neg (opp (z s))) (inv_pos Z_thermo_setoid Z_thermo_pos)).
      * apply (req_mult_compat (inv_pos Z_thermo_setoid Z_thermo_pos)
                               (inv_pos Z_thermo_setoid Z_thermo_pos)
                               (exp_neg (opp (z s)))
                               (exp_neg (mult (inv_pos D D_pos) (energy s)))
                               (req_refl _)
                               (req_sym (exp_neg (mult (inv_pos D D_pos) (energy s)))
                                        (exp_neg (opp (z s)))
                                        Hbf)).
Qed.

(* ============================================================ *)
(* B1-5：详细平衡 ⟹ Boltzmann 分布是稳态（主定理 3/3 迁移）        *)
(*   诚实接口：detailed_balance + transition_normalization      *)
(*   （RealAttnSteady 42437-42446 同款；Id 27886-27894 同款）    *)
(* ============================================================ *)

Variable transition : S -> S -> R.

(* 诚实接口：detailed balance（可逆核，Real 层可实例化） *)
Variable detailed_balance : forall (s s' : S),
  req (mult (boltzmann_dist_attn_setoid s') (transition s' s))
      (mult (boltzmann_dist_attn_setoid s) (transition s s')).

(* 诚实接口：行归一化 Σ_s' T(s,s') == 1（马尔可夫核标准性质） *)
Variable transition_normalization : forall s : S,
  req (sum_req_over_S (fun s' : S => transition s s')) one.

(* 稳态方程（主）：Σ_s' p(s')·T(s',s) == p(s)
   组装：detailed balance 逐点替换 → 求和外延 → 线性提取 p(s)
   → 核归一化 → mult_one 证毕（Real 层对应件上提） *)
Theorem steady_state_boltzmann_attn_setoid : forall s : S,
  req (sum_req_over_S (fun s' : S => mult (boltzmann_dist_attn_setoid s') (transition s' s)))
      (boltzmann_dist_attn_setoid s).
Proof.
intro s.
  (* 1. 逐点 detailed balance 替换：Σ (p s'·T s' s) == Σ (p s·T s s') *)
  apply (req_trans _ (sum_req_over_S (fun s' : S => mult (boltzmann_dist_attn_setoid s) (transition s s'))) _).
  - apply (sum_req_over_S_ext (fun s' : S => mult (boltzmann_dist_attn_setoid s') (transition s' s))
                              (fun s' : S => mult (boltzmann_dist_attn_setoid s) (transition s s'))).
    intro s'. apply (detailed_balance s s').
  - (* 2. 线性提取：Σ (p s·T s s') == p s·Σ (T s s') *)
    apply (req_trans _ (mult (boltzmann_dist_attn_setoid s) (sum_req_over_S (fun s' : S => transition s s'))) _).
    + apply (sum_req_over_S_linear (boltzmann_dist_attn_setoid s) (fun s' : S => transition s s')).
    + (* 3. 核归一化：Σ T == 1 ⟹ p s·1 == p s *)
      apply (req_trans _ (mult (boltzmann_dist_attn_setoid s) one) _).
      * apply (req_mult_compat (boltzmann_dist_attn_setoid s)
                               (boltzmann_dist_attn_setoid s)
                               (sum_req_over_S (fun s' : S => transition s s'))
                               one
                               (req_refl _)
                               (transition_normalization s)).
      * apply (mult_one (boltzmann_dist_attn_setoid s)).
Qed.

(* ============================================================ *)
(* B1-3：Boltzmann 分布归一化（主定理 2/3 迁移）                   *)
(*   Id 27963-27969 直证（6 行：sum linear + inv_pos_correct）；  *)
(*   Real 层无独立佐证（平凡）；此处 req 化直证                  *)
(* ============================================================ *)
Lemma boltzmann_normalized_attn_setoid :
  req (sum_req_over_S boltzmann_dist_attn_setoid) one.
Proof.
unfold boltzmann_dist_attn_setoid.
  apply (req_trans _ (mult (inv_pos Z_thermo_setoid Z_thermo_pos)
                           (sum_req_over_S boltzmann_factor_setoid)) _).
  - apply (sum_req_over_S_linear (inv_pos Z_thermo_setoid Z_thermo_pos) boltzmann_factor_setoid).
  - apply (req_trans _ (mult (inv_pos Z_thermo_setoid Z_thermo_pos) Z_thermo_setoid) _).
    + apply req_refl.   (* Σ boltzmann_factor 折叠为 Z_thermo_setoid（δ 转换） *)
    + apply (req_trans _ (mult Z_thermo_setoid (inv_pos Z_thermo_setoid Z_thermo_pos)) _).
      * apply (mult_comm (inv_pos Z_thermo_setoid Z_thermo_pos) Z_thermo_setoid).
      * apply (inv_pos_correct Z_thermo_setoid Z_thermo_pos).
Qed.

End AttentionGibbsBridgeSetoid.

(* ToyR ：替换定理假设面查证 *)
Print Assumptions sc_lp_four_nonneg.
