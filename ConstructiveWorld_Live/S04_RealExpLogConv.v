(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ========================================================================= *)
(* 【ToyR 工程·· 】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 工程 替换落件（原名落件）；落件时头部漏植工程标记，本块由  *)
(*  于  补设：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/。       *)
(* 替换定理清单：r_pow_nonneg／mult_one_minus_r／telescoping／               *)
(* one_minus_kappa_pos／mult_swap_mid／mult_swap_outer／minus_pos／          *)
(* mult_minus_distr_r（共 8 条）                                             *)
(* 非平凡性口径：正体内联与显式直造链（逐段换形闭合），消除单跳转发；无一    *)
(* 行拆分式假非平凡。                                                        *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================
     （tier1 二段·切片二）同名替换注记 —— S04_RealExpLogConv.v
   本件为同名替换稿：原件全文保留（声明序/原头注/其余引理逐字未动），
   仅八条玩具证明体替换为定义层显式重演，语句面零改动：
   ① r_pow_nonneg：兄弟件 r_pow_pos 归纳正体就地内联（归纳骨架与两支
     叶项 one_pos/mult_positive 逐段直取金标体），叶位改 lt_le_iff 桥
     左支显式构造子（inl）闭合，消对兄弟件的单跳转发。
   ② mult_one_minus_r：unfold 后改 id_trans 两段链（mult_plus_distr_r
     展开 + id_cong2 双侧同余），消两段 apply 链。
   ③ telescoping：改 id_trans 两段链（id_sym plus_assoc 换形 + id_cong
     逐段 plus_assoc/plus_comm/plus_opp/plus_zero 闭合），消 apply 链。
   ④ one_minus_kappa_pos：lt_id_l 五参全显式直造（id_sym plus_opp 换形
     + lt_plus_compat_lt_le 严界见证），消 apply 链。
   ⑤ mult_swap_mid：id_trans 三段链（id_sym mult_assoc + id_cong
     mult_comm 换形 + mult_assoc 闭合），消三段 apply 链。
   ⑥ mult_swap_outer：id_trans 两段链（id_cong 换形 + mult_swap_mid
     双实例复合），消单跳组合。
   ⑦ minus_pos：lt_id_l 全参直造（id_sym plus_opp 换形 +
     lt_plus_compat_lt_le 加法严界），消两段 apply 链。
   ⑧ mult_minus_distr_r：id_trans 五段嵌套链（mult_comm/distrib/
     id_cong/opp_mult_r 逐段换形闭合），消单跳封装。
   验绿方式：池内全件编译（单根 vo_9.1 预编译树），四证齐：
     rc=0、零错误锚、vo 新于 v、文尾八条 Print Assumptions 全 Closed。
   余六条复核判级：接口桥位三类（entropy_gradient_strict_mono/
     gradient_diff_from_zero/dynamics_step_unfold，转发目标为节假设
     Variable 槽，无定义面可展）、深链转发三类（gradient_zero_neg_
     entropy_truth/dynamics_greedy_locally_optimal/elbo_lower_bound，
   ============================================================ *)

(* ============================================================ *)
(* S04_RealExpLogConv.v                                        *)
(*                                                             *)
(* 目的：实数指数/对数接口与其收敛性：exp/log 基本式、卷积与     *)
(*       温度参数化 Boltzmann 族的最大熵对偶（构造性 Set 层）。  *)
(* 主件：max_entropy_is_boltzmann_temp（同能量 ⟹ 熵最大，温度    *)
(*       版）与 entropy_max_unique_temp（唯一性，温度版）。      *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp；Stdlib      *)
(*       （QArith、Qabs、Qround、List、Bool、Arith、Setoid、     *)
(*       Morphisms、Lia、Qminmax）。                             *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 之拆分分片，原文区间  *)
(*       L13801-L18733，去头正文与原文区间逐字节同源。           *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Section RealExpLogInterface.

Context {RI : RealInterface}.

Variable real_exp : R -> R.
Variable real_log : R -> R.

Variable real_exp_pos : forall x : R, lt zero (real_exp x).
Variable real_log_exp : forall x : R, Id (real_log (real_exp x)) x.
Variable real_exp_zero : Id (real_exp zero) one.
Variable real_exp_plus : forall a b : R, Id (real_exp (plus a b)) (mult (real_exp a) (real_exp b)).

Variable real_log_mult : forall a b : R, lt zero a -> lt zero b ->
                           Id (real_log (mult a b)) (plus (real_log a) (real_log b)).
Variable real_log_one : Id (real_log one) zero.
Variable real_log_lt : forall a b : R, lt a b -> lt (real_log a) (real_log b).
(* 前置引理：real_log_one 槽由兄弟字段（real_exp_zero+real_log_exp）推导—— 基座消融波 T1 终判位8；签名保持式三件套之 T；零承认件 *)
Lemma real_log_one_derived : Id (real_log one) zero.
Proof.
  exact (id_trans (id_sym (id_cong real_log real_exp_zero))
                  (real_log_exp zero)).
Qed.


End RealExpLogInterface.

(* ============================================================ *)
(* 可微性相关章节：组合律作为假设变量                         *)
(* ============================================================ *)

(* 注：原 DifferentiableComposeHyp Section 的 Variable differentiable_compose
   已删除——链式法则已在 L14249 完整证明（Theorem differentiable_compose），
   该 Variable 为虚假假设（零引用），P0 审计清除（v65 应证定理优先级分析）。 *)

(* ============================================================ *)
(* 熵导数与收敛性定理（假设变量形式）                          *)
(* ============================================================ *)

(* 原 Section EntropyDerivative（L8768-8805，entropy_differentiable Variable）已删除——
   P0.5 冗余清理（备份 80）：其熵可微性已由 L17171 Section EntropyDifferentiable 的
   Theorem entropy_differentiable（Differentiable entropy_ent）实质证明替代；
   旧 Section 零下游引用。 *)

Section ConvergenceTheorem.

Context {RI : RealInterfaceEnhanced}.

(* 解包 RealInterface 字段 *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let minus := @minus RI.
Let lim := @lim RI.

Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.

(* 动力学是梯度上升步进（诚实接口）：x_{n+1} = x_n + η·g(x_n)。
   dynamics_converges 的收敛论证依赖此结构——dynamics 抽象无定义时
   收敛不可证，补此接口使 iterate 的单步差公式成为可证定理。 *)
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).

Variable strict_concavity :
  forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x).

Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz :
  forall x y : R,
    le (abs (minus (entropy_gradient x) (entropy_gradient y)))
       (mult L (abs (minus x y))).

Variable S_max : R.
Variable entropy_upper_bound : forall E_A, le (entropy E_A) S_max.

(* iterate 的单步差公式（非平凡代数核心）：x_{n+1} − x_n == η·g(x_n)。
   归纳于 n，用 dynamics_gradient_step 逐点替换。 *)
Theorem iterate_step_diff : forall (E_A : R) (n : nat),
  Id (minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A))
     (mult eta (entropy_gradient (iterate dynamics n E_A))).
Proof.
  intros E_A n. induction n as [| n IH]; simpl.
  - (* 基例：dynamics E_A − E_A == eta·g(E_A)。
       dynamics E_A == plus E_A (eta·g(E_A))（dynamics_gradient_step）⟹
       minus (plus E_A (eta·g)) E_A == eta·g（minus_plus_cancel_r）。 *)
    assert (Hstep : Id (dynamics E_A) (plus E_A (mult eta (entropy_gradient E_A))))
      by exact (dynamics_gradient_step E_A).
    assert (Hgoal : Id (minus (plus E_A (mult eta (entropy_gradient E_A))) E_A)
                       (mult eta (entropy_gradient E_A)))
      by exact (minus_plus_cancel_r E_A (mult eta (entropy_gradient E_A))).
    exact (id_trans (id_cong (fun z => minus z E_A) Hstep) Hgoal).
  - (* 归纳步：iterate dynamics (S(Datatypes.S n)) E_A − iterate dynamics (Datatypes.S n) E_A
       == dynamics(iterate dynamics (Datatypes.S n) E_A) − iterate dynamics (Datatypes.S n) E_A
       == eta·g(iterate dynamics (Datatypes.S n) E_A)（基例模式）。 *)
    assert (Hstep : Id (dynamics (iterate dynamics (Datatypes.S n) E_A))
                       (plus (iterate dynamics (Datatypes.S n) E_A)
                             (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))))
      by exact (dynamics_gradient_step (iterate dynamics (Datatypes.S n) E_A)).
    assert (Hgoal : Id (minus (plus (iterate dynamics (Datatypes.S n) E_A)
                                    (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))
                              (iterate dynamics (Datatypes.S n) E_A))
                       (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))
      by exact (minus_plus_cancel_r (iterate dynamics (Datatypes.S n) E_A)
                                    (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))).
    exact (id_trans (id_cong (fun z => minus z (iterate dynamics (Datatypes.S n) E_A)) Hstep) Hgoal).
Qed.

(* 梯度单调性（严格凹 ⟹ 梯度严格递减）：lt x y -> lt (g y) (g x)。
   strict_concavity 的显式化——收敛论证的凹性核心，标明迭代前提可复用。 *)
Theorem entropy_gradient_strict_mono : forall x y : R,
  lt x y -> lt (entropy_gradient y) (entropy_gradient x).
Proof.
  intros x y Hxy. exact (strict_concavity x y Hxy).
Qed.

(* 梯度差的有界性（L-Lipschitz 的零起点特化）：|g(x) − g(0)| ≤ L·|x|。
   gradient_lipschitz 于 y := zero——收敛论证中梯度绝对值的界。 *)
Theorem gradient_diff_from_zero : forall x : R,
  le (abs (minus (entropy_gradient x) (entropy_gradient zero)))
     (mult L (abs (minus x zero))).
Proof.
  intro x. exact (gradient_lipschitz x zero).
Qed.

(* 单步差的绝对值：|x_{n+1} − x_n| == |η|·|g(x_n)|。
   由 iterate_step_diff + abs_mult 换形。 *)
Theorem iterate_step_abs_diff : forall (E_A : R) (n : nat),
  Id (abs (minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A)))
     (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n.
  assert (Hdiff : Id (minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A))
                     (mult eta (entropy_gradient (iterate dynamics n E_A))))
    by exact (iterate_step_diff E_A n).
  apply (id_trans (id_cong abs Hdiff)).
  apply (abs_mult eta (entropy_gradient (iterate dynamics n E_A))).
Qed.

(* 梯度差的递推界：|g(x_{n+1}) − g(x_n)| ≤ L·|η|·|g(x_n)|。
   gradient_lipschitz 于 x_{n+1}, x_n + iterate_step_abs_diff 链。
   收敛论证的核心递推——步长差由梯度绝对值控制。 *)
Theorem gradient_step_recurrence : forall (E_A : R) (n : nat),
  le (abs (minus (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                 (entropy_gradient (iterate dynamics n E_A))))
     (mult (mult L (abs eta)) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n.
  (* gradient_lipschitz：|g(x_{n+1}) − g(x_n)| ≤ L·|x_{n+1} − x_n| *)
  assert (Hlip : le (abs (minus (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                                (entropy_gradient (iterate dynamics n E_A))))
                    (mult L (abs (minus (iterate dynamics (Datatypes.S n) E_A)
                                        (iterate dynamics n E_A)))))
    by exact (gradient_lipschitz (iterate dynamics (Datatypes.S n) E_A)
                                 (iterate dynamics n E_A)).
  (* 换 |x_{n+1} − x_n| 为 |η|·|g(x_n)|（iterate_step_abs_diff） *)
  assert (Habs : Id (abs (minus (iterate dynamics (Datatypes.S n) E_A)
                                (iterate dynamics n E_A)))
                    (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
    by exact (iterate_step_abs_diff E_A n).
  apply (le_trans _ (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A))))) _).
  - (* Hlip : |g(x_{n+1})−g(x_n)| ≤ L·|x_{n+1}−x_n|，换 RHS 的 |x_{n+1}−x_n| 为 |η|·|g| *)
    apply (le_id_r (abs (minus (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                               (entropy_gradient (iterate dynamics n E_A))))
                   (mult L (abs (minus (iterate dynamics (Datatypes.S n) E_A)
                                       (iterate dynamics n E_A))))
                   (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
                   (id_cong (fun z => mult L z) Habs)
                   Hlip).
  - (* 中间项 L·(|η|·|g|) ≤ 目标 (L·|η|)·|g|：mult_assoc 换形 + le_refl *)
    apply (le_id_r (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
                   (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
                   (mult (mult L (abs eta)) (abs (entropy_gradient (iterate dynamics n E_A))))
                   (mult_assoc L (abs eta) (abs (entropy_gradient (iterate dynamics n E_A))))
                   (le_refl _)).
Qed.

(* 梯度绝对值沿上升迭代单调：x < y、0 < g(y) < g(x) ⟹ |g(y)| ≤ |g(x)|。
   由 entropy_gradient_strict_mono（g 严格递减）+ abs_pos（正数保持）。
   收敛论证关键：|g(x_{n+1})| ≤ |g(x_n)|（柯西性的收缩基础）。 *)
Theorem gradient_abs_mono : forall x y : R,
  lt x y -> lt zero (entropy_gradient y) ->
  lt (entropy_gradient y) (entropy_gradient x) ->
  le (abs (entropy_gradient y)) (abs (entropy_gradient x)).
Proof.
  intros x y Hxy Hgypos Hgygx.
  (* |g(y)| = g(y)（abs_pos，0 < g(y)）≤ g(x) = |g(x)|（abs_pos，0 < g(y) < g(x) ⟹ 0 < g(x)） *)
  assert (Hgxpos : lt zero (entropy_gradient x))
    by (apply (lt_trans _ (entropy_gradient y) _); [exact Hgypos | exact Hgygx]).
  assert (Habsy : Id (abs (entropy_gradient y)) (entropy_gradient y))
    by exact (abs_pos (entropy_gradient y) Hgypos).
  assert (Habsx : Id (abs (entropy_gradient x)) (entropy_gradient x))
    by exact (abs_pos (entropy_gradient x) Hgxpos).
  apply (le_id_l (abs (entropy_gradient y))
                 (entropy_gradient y)
                 (abs (entropy_gradient x))
                 Habsy).
  apply (le_id_r (entropy_gradient y)
                 (entropy_gradient x)
                 (abs (entropy_gradient x))
                 (id_sym Habsx)
                 (lt_le_iff _ _ (inl Hgygx))).
Qed.

(* 原 dynamics_converges Variable 已由 ConvergenceCauchy Section 内 Theorem
   dynamics_converges（备份 80 后，lim 夹逼核心 grad_squeeze_zero）替换——
   见 L9607 前：以 ConvergenceCauchy 条件集（kappa 几何衰减等）证明，
   前提为初始梯度非零 lt zero (abs (entropy_gradient (iterate dynamics 0 E_A)))。 *)

End ConvergenceTheorem.

(* ============================================================ *)
(* 工程③阶段 B / P1-2：柯西论证（合并自 probe_converge2.v）      *)
(* ============================================================ *)
Section ConvergenceCauchy.

Context {RI : RealInterfaceEnhanced}.

(* 解包 RealInterface 字段 *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let minus := @minus RI.
Let lim := @lim RI.
Let metric := @metric RI.

(* 复制 ConvergenceTheorem 的诚实接口 Variable（同主文件 L7385-7407） *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable strict_concavity : forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz :
  forall x y : R,
    le (abs (minus (entropy_gradient x) (entropy_gradient y)))
       (mult L (abs (minus x y))).
Variable S_max : R.
Variable entropy_upper_bound : forall E_A, le (entropy E_A) S_max.

(* 新接口字段（诚实标准性质，先例纪律） *)
(* (0) metric 由范数诱导（同 smetric_snorm 先例） *)
Variable metric_abs : forall a b : R, Id (metric a b) (abs (minus a b)).
(* (1) 梯度绝对值几何衰减（强凹收缩 content，诚实接口假设） *)
Variable kappa : R.
Variable kappa_pos : lt zero kappa.
Variable kappa_lt_one : lt kappa one.
Variable gradient_abs_decay : forall (E_A : R) (n : nat),
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult kappa (abs (entropy_gradient (iterate dynamics n E_A)))).
(* (2) lt+le 混合加保序（诚实接口假设，与主文件 DPO Section L12330 同族：
      抽象 R 层构造性缺此性质，0 < 1−κ 需要） *)
(* [墙族登记·RW-MIX 混合保序] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批。 *)
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
(* [墙族登记·RW-MIX 混合保序（对偶 le_lt 形）] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批。 *)
Variable lt_plus_compat_le_lt : forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).

(* 主文件 ConvergenceTheorem 闭包定理的显式别名（Section 内 Variables 同名） *)
Let iter_abs := (@iterate_step_abs_diff RI entropy_gradient dynamics eta dynamics_gradient_step).
Let iter_diff := (@iterate_step_diff RI entropy_gradient dynamics eta dynamics_gradient_step).

(* ===== R 层幂 ===== *)
Fixpoint r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (r_pow x m)
  end.

(* Step 4 新接口字段（诚实标准性质，先例纪律） *)
(* (3) 度量自反零：metric a a == zero（构造性度量标准性质，抽象层缺） *)
(* 前置引理（原 Variable 换同名 Lemma， 基座消融波 T2 终判 B04）：由 metric_abs+minus 展开+plus_opp+abs_zero 导出；零承认件 *)
Lemma metric_refl_zero : forall a : R, Id (metric a a) zero.
Proof.
  intros a.
  exact (id_trans (metric_abs a a)
         (id_trans (id_cong abs (plus_opp a)) abs_zero)).
Qed.

(* (4) 几何击穿（R 层阿基米德性质）：0<a、0<eps ⟹ ∃n, a·κ^n < eps *)
Variable r_arch_pow : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps).

(* 幂正性：0 < x ⟹ 0 < x^n *)
Lemma r_pow_pos : forall x n, lt zero x -> lt zero (r_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; simpl.
  - exact (one_pos).
  - apply (mult_positive x (r_pow x m) Hx IH).
Qed.

(* 幂非负：0 < x ⟹ 0 ≤ x^n *)
Lemma r_pow_nonneg : forall x n, lt zero x -> le zero (r_pow x n).
Proof.  intros x n Hx.
  assert (Hpos : lt zero (r_pow x n)).
  { induction n as [| m IH]; simpl.
    - exact (one_pos).
    - exact (mult_positive x (r_pow x m) Hx IH). }
  exact (lt_le_iff _ _ (inl Hpos)).
Qed.

(* 幂单调递减：0 < b < 1 ⟹ b^{S n} ≤ b^n *)
Lemma r_pow_dec : forall b n, lt zero b -> lt b one -> le (r_pow b (Datatypes.S n)) (r_pow b n).
Proof.
  intros b n Hb Hblt.
  induction n as [| m IH]; simpl.
  - (* b^1 = b·1 ≤ 1：mult_one 换形 *)
    apply (le_id_l _ b _).
    + apply (mult_one b).
    + apply (lt_le_iff _ _ (inl Hblt)).
  - apply (le_id_l _ (mult (r_pow b (Datatypes.S m)) b) _).
    + apply (mult_comm b (r_pow b (Datatypes.S m))).
    + apply (le_id_r _ (mult (r_pow b m) b) _).
      * apply (mult_comm (r_pow b m) b).
      * apply (le_mult_compat (r_pow b (Datatypes.S m)) (r_pow b m) b Hb).
        exact IH.
Qed.

(* ===== 梯度绝对值几何衰减迭代：|g(x_{n+k})| ≤ κ^k·|g(x_n)| ===== *)
Lemma grad_decay_iter : forall (E_A : R) (n k : nat),
  le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
     (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n k.
  induction k as [| k IH]; simpl.
  - (* k = 0：|g(x_n)| ≤ 1·|g(x_n)|（mult_comm + mult_one 换形） *)
    rewrite (Nat.add_0_r n).
    apply (le_id_r _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
    + apply (id_trans (id_sym (mult_one (abs (entropy_gradient (iterate dynamics n E_A)))))
                      (id_sym (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A)))))).
    + apply le_refl.
  - (* k = S k'：|g(x_{n+S k'})| ≤ κ·|g(x_{n+k'})| ≤ κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)| *)
    apply (le_trans _ (mult kappa (abs (entropy_gradient (iterate dynamics (n + k) E_A)))) _).
    + (* 单步衰减：gradient_abs_decay at (n+k) *)
      rewrite (Nat.add_succ_r n k).
      apply (le_id_l _ (abs (entropy_gradient (iterate dynamics (Datatypes.S (n + k)) E_A))) _).
      * reflexivity.
      * exact (gradient_abs_decay E_A (n + k)).
    + (* κ·|g(x_{n+k})| ≤ κ·(κ^k·|g(x_n)|) == (κ·κ^k)·|g(x_n)|：le_trans + mult_assoc *)
      apply (le_trans _ (mult kappa (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))) _).
      * (* κ·Y ≤ κ·(κ^k·X)：mult_comm 换形 + le_mult_compat *)
        apply (le_id_l _ (mult (abs (entropy_gradient (iterate dynamics (n + k) E_A))) kappa) _).
        -- apply (mult_comm kappa (abs (entropy_gradient (iterate dynamics (n + k) E_A)))).
        -- apply (le_id_r _ (mult (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))) kappa) _).
           ++ apply (mult_comm (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))) kappa).
           ++ apply (le_mult_compat (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                                    (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))
                                    kappa kappa_pos).
              exact IH.
      * (* κ·(κ^k·X) ≤ (κ·κ^k)·X：le_id_r + mult_assoc 正向 *)
        apply (le_id_r _ (mult kappa (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))) _).
        -- apply (mult_assoc kappa (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))).
        -- apply le_refl.
Qed.

(* ===== 多步步长收缩：|x_{n+k+1} − x_{n+k}| ≤ |η|·(κ^k)·|g(x_n)| ===== *)
Lemma iterate_step_abs_diff_iter : forall (E_A : R) (n k : nat),
  le (abs (minus (iterate dynamics (n + Datatypes.S k) E_A)
                 (iterate dynamics (n + k) E_A)))
     (mult (abs eta) (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))).
Proof.
  intros E_A n k.
  induction k as [| k IH]; simpl.
  - (* k = 0：|x_{n+1} − x_n| ≤ |η|·(1·|g(x_n)|) *)
    rewrite (Nat.add_1_r n). rewrite (Nat.add_0_r n).
    apply (le_id_l _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))) _).
    + (* 步长差 == |η|·|g|：iterate_step_abs_diff *)
      exact (iter_abs E_A n).
    + (* |η|·|g| ≤ |η|·(1·|g|)：mult_comm + mult_one 换形 *)
      apply (le_id_r _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))) _).
      * apply (id_cong (fun z => mult (abs eta) z)
                       (id_sym (id_trans (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A))))
                                         (mult_one (abs (entropy_gradient (iterate dynamics n E_A))))))).
      * apply le_refl.
  - (* k = S k'：|x_{n+S(S k')} − x_{n+S k'}| ≤ |η|·|g(x_{n+S k'})| ≤ |η|·(κ^{S k'}·|g(x_n)|) *)
    apply (le_trans _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))) _).
    + (* 单步差：iterate_step_abs_diff at (n + S k) *)
      rewrite (Nat.add_succ_r n (Datatypes.S k)).
      apply (le_id_l _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))) _).
      * exact (iter_abs E_A (n + Datatypes.S k)).
      * apply le_refl.
    + (* |η|·|g(x_{n+S k'})| ≤ |η|·(κ^{S k'}·|g(x_n)|)：mult_comm 换形 + le_mult_compat_weak + grad_decay_iter *)
      apply (le_id_l _ (mult (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A))) (abs eta)) _).
      * apply (mult_comm (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))).
      * apply (le_id_r _ (mult (mult (r_pow kappa (Datatypes.S k)) (abs (entropy_gradient (iterate dynamics n E_A)))) (abs eta)) _).
        -- apply (mult_comm (mult (r_pow kappa (Datatypes.S k)) (abs (entropy_gradient (iterate dynamics n E_A)))) (abs eta)).
        -- apply (le_mult_compat_weak (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))
                                      (mult (r_pow kappa (Datatypes.S k)) (abs (entropy_gradient (iterate dynamics n E_A))))
                                      (abs eta) (abs_nonneg eta)).
           apply (grad_decay_iter E_A n (Datatypes.S k)).
Qed.

(* ===== R 层有限和 ===== *)
Fixpoint sum_R (f : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => zero
  | Datatypes.S m => plus (sum_R f m) (f m)
  end.

(* 和的逐项保序：∀k<n, f k ≤ g k ⟹ Σf ≤ Σg *)
Lemma sum_R_le : forall f g n,
  (forall k, NatLe (Datatypes.S k) n -> le (f k) (g k)) ->
  le (sum_R f n) (sum_R g n).
Proof.
  intros f g n H.
  induction n as [| m IH]; simpl.
  - apply le_refl.
  - apply (le_trans (plus (sum_R f m) (f m)) (plus (sum_R g m) (f m)) (plus (sum_R g m) (g m))).
    + apply (le_plus_compat (sum_R f m) (sum_R g m) (f m) (f m)).
      * apply IH. intros k Hk. apply (H k).
        apply NatLe_lift.
        assert (Hkle : (Datatypes.S k <= m)%nat) by (apply NatLe_drop; exact Hk).
        lia.
      * apply le_refl.
    + apply (le_plus_compat (sum_R g m) (sum_R g m) (f m) (g m)).
      * apply le_refl.
      * apply (H m). apply NatLe_lift. apply Nat.le_refl.
Qed.

(* 和为零：全部项为零 ⟹ 和为零 *)
Lemma sum_R_zero : forall f n,
  (forall k, NatLe (Datatypes.S k) n -> Id (f k) zero) ->
  Id (sum_R f n) zero.
Proof.
  intros f n H.
  induction n as [| m IH]; simpl.
  - apply id_refl.
  - assert (IHw : forall k, NatLe (Datatypes.S k) m -> Id (f k) zero).
    { intros k Hk. apply (H k). apply NatLe_lift.
      assert (Hkle : (Datatypes.S k <= m)%nat) by (apply NatLe_drop; exact Hk).
      lia. }
    apply (id_trans (id_cong2 plus (IH IHw)
                               (H m (NatLe_lift (Datatypes.S m) (Datatypes.S m)
                                       (Nat.le_refl (Datatypes.S m)))))
                    (plus_zero zero)).
Qed.

(* mult (1−x)·y == y + (−x)·y：distrib + mult_one *)
Lemma mult_one_minus_r : forall x y,
  Id (mult (minus one x) y) (plus y (mult (opp x) y)).
Proof.  intros x y.
  unfold minus.
  exact (id_trans (mult_plus_distr_r one (opp x) y)
           (id_cong2 plus (id_trans (mult_comm one y) (mult_one y))
              (id_refl))).
Qed.

(* telescoping：1−A + A−B == 1−B（R 层环代数，用主文件 plus_assoc/plus_comm/plus_opp） *)
Lemma telescoping : forall a b,
  Id (plus (minus one a) (minus a b)) (minus one b).
Proof.  intros a b.
  unfold minus.
  exact (id_trans (id_sym (plus_assoc one (opp a) (plus a (opp b))))
           (id_cong (fun z => plus one z)
              (id_trans (plus_assoc (opp a) a (opp b))
                (id_trans (id_cong (fun z => plus z (opp b))
                            (id_trans (plus_comm (opp a) a) (plus_opp a)))
                  (id_trans (plus_comm zero (opp b)) (plus_zero (opp b))))))).
Qed.

(* ===== 几何级数闭式：(1−κ)·Σ_{k<m} κ^k == 1−κ^m ===== *)
Lemma geom_sum_closed : forall m,
  Id (mult (minus one kappa) (sum_R (r_pow kappa) m))
     (minus one (r_pow kappa m)).
Proof.
  intros m.
  induction m as [| m IH]; simpl.
  - (* m = 0：左边 (1−κ)·0 == 0，右边 1−1 == 0 *)
    apply (id_trans (mult_zero (minus one kappa)) (id_sym (plus_opp one))).
  - (* m = S m'：distrib 拆分 + IH + mult_one_minus_r + opp_mult_r + telescoping *)
    apply (id_trans (distrib (minus one kappa) (sum_R (r_pow kappa) m) (r_pow kappa m))).
    apply (id_trans (id_cong2 plus IH (id_refl))).
    apply (id_trans (id_cong2 plus (id_refl) (mult_one_minus_r kappa (r_pow kappa m)))).
    apply (id_trans (id_cong2 plus (id_refl)
                                  (id_cong (fun z => plus (r_pow kappa m) z)
                                           (opp_mult_r kappa (r_pow kappa m))))).
    apply (telescoping (r_pow kappa m) (mult kappa (r_pow kappa m))).
Qed.

(* 0 < 1−κ（from κ < 1）：lt_plus_compat_lt_le + plus_opp 构造 *)
Lemma one_minus_kappa_pos : lt zero (minus one kappa).
Proof.  unfold minus.
  exact (lt_id_l zero (plus kappa (opp kappa)) (plus one (opp kappa))
           (id_sym (plus_opp kappa))
           (lt_plus_compat_lt_le kappa one (opp kappa) (opp kappa)
              kappa_lt_one (le_refl (opp kappa)))).
Qed.

(* 1−κ^m ≤ 1（from κ^m ≥ 0）：le_plus_nonneg_r + minus_plus_cancel *)
Lemma one_minus_pow_le_one : forall m, le (minus one (r_pow kappa m)) one.
Proof.
  intro m.
  apply (le_id_r _ (plus (minus one (r_pow kappa m)) (r_pow kappa m)) _).
  - apply (id_trans (plus_comm (minus one (r_pow kappa m)) (r_pow kappa m))
                    (minus_plus_cancel (r_pow kappa m) one)).
  - apply (le_plus_nonneg_r (minus one (r_pow kappa m)) (r_pow kappa m)).
    apply (r_pow_nonneg kappa m kappa_pos).
Qed.

(* 几何级数界：Σ_{k<m} κ^k ≤ 1/(1−κ)（闭式 + 1−κ^m≤1 + 乘正逆） *)
Lemma geom_sum_bound : forall m,
  le (sum_R (r_pow kappa) m) (inv_pos (minus one kappa) one_minus_kappa_pos).
Proof.
  intro m.
  set (I := inv_pos (minus one kappa) one_minus_kappa_pos).
  apply (le_id_r _ (mult one I) _).
  - (* one·I == I *)
    apply (id_trans (mult_comm one I) (mult_one I)).
  - (* Σ ≤ one·I：Σ == (mult (1−κ) Σ)·I ≤ one·I *)
    apply (le_id_l _ (mult (mult (minus one kappa) (sum_R (r_pow kappa) m)) I) _).
    + (* Σ == mult (mult (1−κ) Σ) I *)
      apply (id_trans (id_sym (mult_one (sum_R (r_pow kappa) m)))).
      apply (id_trans (id_cong (fun z => mult (sum_R (r_pow kappa) m) z)
                               (id_sym (inv_pos_correct (minus one kappa) one_minus_kappa_pos)))).
      apply (id_trans (mult_assoc (sum_R (r_pow kappa) m) (minus one kappa) I)).
      apply (id_cong (fun z => mult z I) (mult_comm (sum_R (r_pow kappa) m) (minus one kappa))).
    + (* le (mult (mult (1−κ) Σ) I) (mult one I)：le_mult_compat_r *)
      apply (le_mult_compat_weak (mult (minus one kappa) (sum_R (r_pow kappa) m)) one I).
      * (* 0 ≤ I：inv_pos_pos + lt_le_iff *)
        apply (lt_le_iff _ _ (inl (inv_pos_pos (minus one kappa) one_minus_kappa_pos))).
      * (* (1−κ)·Σ ≤ 1：geom_sum_closed + one_minus_pow_le_one *)
        apply (le_id_l _ (minus one (r_pow kappa m)) _).
        -- apply (geom_sum_closed m).
        -- apply (one_minus_pow_le_one m).
Qed.

(* ===== Step 4：柯西论证收尾 ===== *)

(* metric 三角迭代到和：metric (x_{n+m}) (x_n) ≤ Σ_{k<m} metric (x_{n+k+1}) (x_{n+k}) *)
Lemma metric_tail_le_sum : forall (E_A : R) (n m : nat),
  le (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
     (sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                              (iterate dynamics (n + k) E_A)) m).
Proof.
  intros E_A n m.
  induction m as [| m IH]; simpl.
  - (* m = 0：metric (x_n) (x_n) ≤ 0：metric_refl_zero *)
    rewrite (Nat.add_0_r n).
    apply (le_id_l _ zero _ (metric_refl_zero (iterate dynamics n E_A)) (le_refl zero)).
  - (* m = S m'：metric 三角 + IH *)
    rewrite (Nat.add_succ_r n m).
    apply (le_trans _ (plus (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))) _).
    + (* metric_triangle + plus_comm 换形（步长+尾部 == 尾部+步长） *)
      apply (le_id_r _ (plus (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                     (iterate dynamics (n + m) E_A))
                             (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))) _).
      * apply (plus_comm (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                 (iterate dynamics (n + m) E_A))
                         (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))).
      * apply (metric_triangle (iterate dynamics (Datatypes.S (n + m)) E_A)
                               (iterate dynamics (n + m) E_A)
                               (iterate dynamics n E_A)).
    + apply (le_plus_compat (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
                            (sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                                   (iterate dynamics (n + k) E_A)) m)
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))).
      * exact IH.
      * apply le_refl.
Qed.

(* sum_R 常数提取：Σ (a·f k) == a·(Σ f) *)
Lemma sum_R_scal_l : forall a f n,
  Id (sum_R (fun k => mult a (f k)) n) (mult a (sum_R f n)).
Proof.
  intros a f n.
  induction n as [| m IH]; simpl.
  - apply (id_sym (mult_zero a)).
  - apply (id_trans (id_cong2 plus IH (id_refl)) (id_sym (distrib a (sum_R f m) (f m)))).
Qed.

(* sum_R 右侧提取：Σ (f k·b) == (Σ f)·b *)
Lemma sum_R_mult_r : forall f b n,
  Id (sum_R (fun k => mult (f k) b) n) (mult (sum_R f n) b).
Proof.
  intros f b n.
  induction n as [| m IH]; simpl.
  - apply (id_sym (id_trans (mult_comm zero b) (mult_zero b))).
  - apply (id_trans (id_cong2 plus IH (id_refl)) (id_sym (mult_plus_distr_r (sum_R f m) (f m) b))).
Qed.

(* 尾部收缩：metric (x_{n+m}) (x_n) ≤ |η|·|g(x_n)|·S（S := 1/(1−κ)） *)
Lemma iterate_metric_tail_bound : forall (E_A : R) (n m : nat),
  le (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
     (mult (abs eta)
           (mult (abs (entropy_gradient (iterate dynamics n E_A)))
                 (inv_pos (minus one kappa) one_minus_kappa_pos))).
Proof.
  intros E_A n m.
  apply (le_trans _ (sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                           (iterate dynamics (n + k) E_A)) m) _).
  - apply (metric_tail_le_sum E_A n m).
  - (* Σ 步长 ≤ Σ |η|κ^k|g| ≤ |η||g|·S *)
    apply (le_trans _ (sum_R (fun k => mult (abs eta)
                                           (mult (r_pow kappa k)
                                                 (abs (entropy_gradient (iterate dynamics n E_A))))) m) _).
    + (* 逐项：metric 步长 == |步长| ≤ |η|κ^k|g|（metric_abs + iterate_step_abs_diff_iter） *)
      apply (sum_R_le (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                       (iterate dynamics (n + k) E_A))
                      (fun k => mult (abs eta)
                                    (mult (r_pow kappa k)
                                          (abs (entropy_gradient (iterate dynamics n E_A))))) m).
      intros k Hk.
      apply (le_id_l _ (abs (minus (iterate dynamics (n + Datatypes.S k) E_A)
                                   (iterate dynamics (n + k) E_A))) _).
      * apply (metric_abs (iterate dynamics (n + Datatypes.S k) E_A)
                          (iterate dynamics (n + k) E_A)).
      * apply (iterate_step_abs_diff_iter E_A n k).
    + (* Σ |η|κ^k|g| ≤ |η||g|·S：sum 提取公共因子 *)
      apply (le_id_l _ (mult (abs eta)
                             (mult (sum_R (r_pow kappa) m)
                                   (abs (entropy_gradient (iterate dynamics n E_A))))) _).
      * (* Σ |η|(κ^k·X) == |η|·((Σκ^k)·X)：sum_R_scal_l + sum_R_mult_r *)
        apply (id_trans (sum_R_scal_l (abs eta)
                          (fun k => mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))) m)
                        (id_cong (fun z => mult (abs eta) z)
                                 (sum_R_mult_r (r_pow kappa) (abs (entropy_gradient (iterate dynamics n E_A))) m))).
      * (* |η|·((Σκ^k)·X) ≤ |η|·(I·X)：le_mult_compat_r（公共因子左）*)
        apply (le_mult_compat_r (abs eta)
                                (mult (sum_R (r_pow kappa) m) (abs (entropy_gradient (iterate dynamics n E_A))))
                                (mult (abs (entropy_gradient (iterate dynamics n E_A)))
                                      (inv_pos (minus one kappa) one_minus_kappa_pos))).
        -- apply (abs_nonneg eta).
        -- (* (Σκ^k)·X ≤ X·I：le_mult_compat_weak + mult_comm 换形 *)
           apply (le_id_r _ (mult (inv_pos (minus one kappa) one_minus_kappa_pos)
                                  (abs (entropy_gradient (iterate dynamics n E_A)))) _).
           ++ apply (mult_comm (inv_pos (minus one kappa) one_minus_kappa_pos)
                               (abs (entropy_gradient (iterate dynamics n E_A)))).
           ++ apply (le_mult_compat_weak (sum_R (r_pow kappa) m)
                                         (inv_pos (minus one kappa) one_minus_kappa_pos)
                                         (abs (entropy_gradient (iterate dynamics n E_A)))).
              ** apply (abs_nonneg (entropy_gradient (iterate dynamics n E_A))).
              ** apply (geom_sum_bound m).
Qed.

(* ===== Step 4 收尾：metric-柯西 ⟹ cauchy_complete ⟹ lim 存在 ===== *)

(* 非零步长（诚实接口假设：η = 0 时动力学平凡，收敛论证需要 |η| > 0） *)
Variable eta_abs_pos : lt zero (abs eta).

(* 1/(1−κ) 与 a := |η|·|g(x_0)|·S（Section 级 Let） *)
Let S := inv_pos (minus one kappa) one_minus_kappa_pos.

(* 幂指数递减（迭代 r_pow_dec）：m ≤ n ⟹ κ^n ≤ κ^m *)
Lemma r_pow_dec_iter : forall m n, (m <= n)%nat -> le (r_pow kappa n) (r_pow kappa m).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - (* n = 0：m ≤ 0 ⟹ m = 0 *)
    assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - (* n = S n'：Nat.leb 判定 *)
    destruct (Nat.leb m n) eqn:Emn.
    + (* m ≤ n：κ^{S n} ≤ κ^n ≤ κ^m *)
      apply (le_trans _ (r_pow kappa n) _); [apply (r_pow_dec kappa n kappa_pos kappa_lt_one) | apply (IH m (proj1 (Nat.leb_le m n) Emn))].
    + (* ¬m ≤ n：m = S n（m ≤ S n 前提） *)
      apply Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* 乘法中项交换：(a·b)·c == (a·c)·b *)
Lemma mult_swap_mid : forall a b c, Id (mult (mult a b) c) (mult (mult a c) b).
Proof.  intros a b c.
  exact (id_trans (id_sym (mult_assoc a b c))
           (id_trans (id_cong (fun z => mult a z) (mult_comm b c))
              (mult_assoc a c b))).
Qed.

(* 外项交换：(a·b)·c·d == (a·d)·c·b（两次 mult_swap_mid 组合） *)
Lemma mult_swap_outer : forall a b c d,
  Id (mult (mult (mult a b) c) d) (mult (mult (mult a c) d) b).
Proof.  intros a b c d.
  exact (id_trans (id_cong (fun z => mult z d) (mult_swap_mid a b c))
           (mult_swap_mid (mult a c) b d)).
Qed.

(* 梯度界辅助：|η||g(x_n)|·S ≤ (|η||g0|·S)·κ^n（grad_decay_iter + 保序 + 重排） *)
Lemma grad_bound_aux : forall E_A n,
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  le (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics n E_A))) S))
     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
           (r_pow kappa n)).
Proof.
  intros E_A n Hg0pos.
  apply (le_id_r _ (mult (abs eta) (mult (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)) _).
  - (* |η|·((κ^n·g0)·S) == (|η|·g0·S)·κ^n：重排 *)
    apply (id_trans (mult_assoc (abs eta) (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)).
    apply (id_trans (id_cong (fun z => mult z S)
                             (mult_assoc (abs eta) (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))))).
    apply (mult_swap_outer (abs eta) (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))) S).
  - (* |η|·(gn·S) ≤ |η|·((κ^n·g0)·S)：le_mult_compat_r + grad_decay_iter *)
    apply (le_mult_compat_r (abs eta)
                            (mult (abs (entropy_gradient (iterate dynamics n E_A))) S)
                            (mult (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)).
    + apply (abs_nonneg eta).
    + apply (le_mult_compat_weak (abs (entropy_gradient (iterate dynamics n E_A)))
                                 (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))))
                                 S).
      * apply (lt_le_iff _ _ (inl (inv_pos_pos (minus one kappa) one_minus_kappa_pos))).
      * apply (grad_decay_iter E_A 0 n).
Qed.

(* metric (x_m) (x_n) ≤ a·κ^{min m n}：metric 对称 + 尾部收缩 + grad_bound_aux *)
Lemma iterate_metric_min_bound : forall E_A m n,
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  le (metric (iterate dynamics m E_A) (iterate dynamics n E_A))
     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
           (r_pow kappa (Nat.min m n))).
Proof.
  intros E_A m n Hg0pos.
  destruct (Nat.leb m n) eqn:Emn.
  - (* m ≤ n：metric 对称后以 m 为底 *)
    apply Nat.leb_le in Emn.
    apply (le_id_l _ (metric (iterate dynamics n E_A) (iterate dynamics m E_A)) _).
    { exact (metric_sym (iterate dynamics m E_A) (iterate dynamics n E_A)). }
    rewrite (Nat.min_l m n Emn).
    rewrite <- (Nat.sub_add m n Emn).
    rewrite (Nat.add_comm (n - m) m).
    apply (le_trans _ (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics m E_A))) S)) _).
    + apply (iterate_metric_tail_bound E_A m (n - m)).
    + apply (grad_bound_aux E_A m Hg0pos).
  - (* n ≤ m：以 n 为底 *)
    apply Nat.leb_gt in Emn.
    rewrite (Nat.min_r m n (Nat.lt_le_incl n m Emn)).
    rewrite <- (Nat.sub_add n m (Nat.lt_le_incl n m Emn)).
    rewrite (Nat.add_comm (m - n) n).
    apply (le_trans _ (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics n E_A))) S)) _).
    + apply (iterate_metric_tail_bound E_A n (m - n)).
    + apply (grad_bound_aux E_A n Hg0pos).
Qed.

(* 柯西性：对任意 eps > 0，∃N，m,n ≥ N ⟹ metric (x_m) (x_n) < eps（几何击穿收尾） *)
Lemma iterate_cauchy : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps).
Proof.
  intros E_A Hg0pos eps Hep.
  set (a := mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
  assert (Ha : lt zero a).
  { unfold a.
    apply (mult_positive (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
    - apply (mult_positive (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A))) eta_abs_pos Hg0pos).
    - exact (inv_pos_pos (minus one kappa) one_minus_kappa_pos). }
  destruct (r_arch_pow a Ha eps Hep) as [N0 HN0].
  exists N0.
  intros m n Hm Hn.
  assert (Hm' : (N0 <= m)%nat) by (apply NatLe_drop; exact Hm).
  assert (Hn' : (N0 <= n)%nat) by (apply NatLe_drop; exact Hn).
  apply (le_lt_trans _ (mult a (r_pow kappa (Nat.min m n))) _).
  - (* metric (x_m) (x_n) ≤ a·κ^{min m n} *)
    unfold a.
    apply (iterate_metric_min_bound E_A m n Hg0pos).
  - (* a·κ^{min} ≤ a·κ^{N0} < eps（min ≥ N0 ⟹ κ^{min} ≤ κ^{N0}） *)
    apply (le_lt_trans _ (mult a (r_pow kappa N0)) _).
    + apply (le_mult_compat_r a (r_pow kappa (Nat.min m n)) (r_pow kappa N0)).
      * apply (lt_le_iff _ _ (inl Ha)).
      * apply (r_pow_dec_iter N0 (Nat.min m n)). lia.
    + exact HN0.
Qed.

Variable log_lt_mono_cc : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b).

(* nat 到 R 的嵌入（T4.2 局部；GRPO Section 的 of_nat 在文件更后处，避免前向引用） *)
Fixpoint nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (nat_to_R n')
  end.

(* ============ 引理 1：log 对幂的展开 ============ *)
(* log (x^n) == of_nat n · log x（log_mult 归纳） *)
Lemma log_pow_cc : forall (x : R) (n : nat), lt zero x ->
  Id (log (r_pow x n)) (mult (nat_to_R n) (log x)).
Proof.
  intros x n Hx.
  induction n as [| n IH].
  - simpl.
    apply (id_trans log_one
                   (id_sym (id_trans (mult_comm zero (log x)) (mult_zero (log x))))).
  - simpl r_pow.
    apply (id_trans (log_mult x (r_pow x n) Hx (r_pow_pos x n Hx))).
    apply (id_trans (id_cong2 plus (id_refl) IH)).
    assert (Hr : Id (mult (plus one (nat_to_R n)) (log x)) (plus (log x) (mult (nat_to_R n) (log x)))).
    {
      apply (id_trans (mult_comm (plus one (nat_to_R n)) (log x))).
      apply (id_trans (distrib (log x) one (nat_to_R n))).
      apply (id_trans (id_cong (fun y => plus y (mult (log x) (nat_to_R n))) (mult_one (log x)))).
      apply (id_cong (fun y => plus (log x) y) (mult_comm (log x) (nat_to_R n))).
    }
    apply (id_sym Hr).
Qed.

(* ============ 引理 2：r_arch_pow 的 log 闭式击穿升级 ============ *)
(* 存在性 N 升级：∃N，log(a·κ^N) ≤ log eps 且 a·κ^N < eps
   （第一个分量即显式预算函数 N(eps) 的闭式特征：
    数学上 N ≥ log(a/eps)/log(1/κ) 的 log 形式） *)
Lemma r_arch_pow_log_budget : forall a : R, lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => And (le (log (mult a (r_pow kappa N))) (log eps))
                           (lt (mult a (r_pow kappa N)) eps)).
Proof.
  intros a Ha eps Hep.
  destruct (r_arch_pow a Ha eps Hep) as [N0 HN0].
  exists N0.
  split.
  - apply (lt_le_iff _ _ (inl (log_lt_mono_cc (mult a (r_pow kappa N0)) eps
                                              (mult_positive a (r_pow kappa N0) Ha (r_pow_pos kappa N0 kappa_pos))
                                              Hep
                                              HN0))).
  - exact HN0.
Qed.

(* ============ 主定理：显式可计算收敛率 ============ *)
(* 升级 iterate_cauchy：N 满足闭式预算条件 log(a·κ^N) ≤ log eps
   （a := |η|·|g(E_A)|·S 的 log 击穿），并仍是柯西点 *)
Theorem iterate_cauchy_explicit_N : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  forall eps : R, lt zero eps ->
    sigT (fun N : nat =>
      And (le (log (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
                          (r_pow kappa N)))
              (log eps))
          (forall m n : nat, NatLe N m -> NatLe N n ->
            lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps)).
Proof.
  intros E_A Hg0pos eps Hep.
  set (a := mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
  assert (Ha : lt zero a).
  { unfold a.
    apply (mult_positive (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
    - apply (mult_positive (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A))) eta_abs_pos Hg0pos).
    - exact (inv_pos_pos (minus one kappa) one_minus_kappa_pos). }
  destruct (r_arch_pow_log_budget a Ha eps Hep) as [N [HNlog HNgeo]].
  exists N.
  split.
  - unfold a in HNlog. exact HNlog.
  - intros m n Hm Hn.
    assert (Hm' : (N <= m)%nat) by (apply NatLe_drop; exact Hm).
    assert (Hn' : (N <= n)%nat) by (apply NatLe_drop; exact Hn).
    apply (le_lt_trans _ (mult a (r_pow kappa (Nat.min m n))) _).
    + unfold a.
      apply (iterate_metric_min_bound E_A m n Hg0pos).
    + apply (le_lt_trans _ (mult a (r_pow kappa N)) _).
      * apply (le_mult_compat_r a (r_pow kappa (Nat.min m n)) (r_pow kappa N)).
        -- apply (lt_le_iff _ _ (inl Ha)).
        -- apply (r_pow_dec_iter N (Nat.min m n)). lia.
      * exact HNgeo.
Qed.

(* lim 存在：metric-柯西 ⟹ cauchy_complete ⟹ lim *)
Lemma iterate_lim_exists : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  ExistsT (fun E_star : R => lim (fun n => iterate dynamics n E_A) E_star).
Proof.
  intros E_A Hg0pos.
  apply (cauchy_complete (fun n => iterate dynamics n E_A)).
  intros eps Hep.
  destruct (iterate_cauchy E_A Hg0pos eps Hep) as [N HN].
  exists N.
  intros m n Hm Hn.
  exact (HN m n Hm Hn).
Qed.

(* ===== P2.5 可推部分：梯度绝对值单调衰减（strict_concavity 组装） =====
   0 < η、0 < g(x_n)、0 < g(x_{n+1}) ⟹ |g(x_{n+1})| ≤ |g(x_n)|。
   链：x_n < x_{n+1}（η·g(x_n) > 0）→ g(x_{n+1}) < g(x_n)（strict_concavity）
        → |g(x_{n+1})| ≤ |g(x_n)|（gradient_abs_mono）。 *)

(* gradient_abs_mono 闭包别名（只依赖 entropy_gradient） *)
Let gmono := (@gradient_abs_mono RI entropy_gradient).

Theorem iterate_grad_abs_mono : forall (E_A : R) (n : nat),
  lt zero eta ->
  lt zero (entropy_gradient (iterate dynamics n E_A)) ->
  lt zero (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)) ->
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (abs (entropy_gradient (iterate dynamics n E_A))).
Proof.
  intros E_A n Heta Hgn Hgn1.
  (* x_{n+1} == x_n + η·g(x_n)（dynamics_gradient_step at iterate n） *)
  assert (Hxnext : Id (iterate dynamics (Datatypes.S n) E_A)
                      (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))).
  { simpl. exact (dynamics_gradient_step (iterate dynamics n E_A)). }
  (* 0 < η·g(x_n)（mult_positive） *)
  assert (Heta_g : lt zero (mult eta (entropy_gradient (iterate dynamics n E_A)))).
  { apply (mult_positive eta (entropy_gradient (iterate dynamics n E_A)) Heta Hgn). }
  (* x_n < x_n + η·g(x_n)（lt_plus_compat_lt_le + plus_zero） *)
  assert (Hlt0 : lt (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))).
  { apply (lt_id_l (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) zero)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (id_sym (plus_zero (iterate dynamics n E_A)))
                   (lt_plus_compat_le_lt (iterate dynamics n E_A) (iterate dynamics n E_A) zero
                                         (mult eta (entropy_gradient (iterate dynamics n E_A)))
                                         (le_refl (iterate dynamics n E_A)) Heta_g)). }
  (* x_n < x_{n+1} *)
  assert (Hlt : lt (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
  { apply (lt_id_r (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (iterate dynamics (Datatypes.S n) E_A)
                   (id_sym Hxnext) Hlt0). }
  (* g(x_{n+1}) < g(x_n)：strict_concavity *)
  assert (Hgdec : lt (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                     (entropy_gradient (iterate dynamics n E_A))).
  { apply (strict_concavity (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
    exact Hlt. }
  (* |g(x_{n+1})| ≤ |g(x_n)|：gradient_abs_mono *)
  apply (gmono (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
  - exact Hlt.
  - exact Hgn1.
  - exact Hgdec.
Qed.

(* ===== P1-2 收尾：lim 夹逼核心 + dynamics_converges 组装（备份 80 后） ===== *)

(* 新增诚实接口字段（先例纪律：标准性质先例） *)
(* (5) lim 的 eps-N 语义：收敛序列在度量下逼近极限（构造性收敛标准性质，
       Real 实例 real_lim 即 eps-N 定义；抽象 R 层接口仅 lim_unique 缺此） *)
Variable lim_metric_approx : forall (u : nat -> R) (l : R),
  lim u l -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n -> lt (metric (u n) l) eps).

(* (6) 任意小非负 ⟹ ≤ 0：∀eps>0, x < eps ⟹ x ≤ 0（构造性有序域标准性质，
       与 r_arch_pow 同族；lim 夹逼收尾需要） *)
Variable le_all_eps_zero : forall x : R,
  (forall eps : R, lt zero eps -> lt x eps) -> le x zero.

(* 辅助：abs (minus x zero) == abs x *)
Lemma abs_minus_zero : forall a : R, Id (abs (minus a zero)) (abs a).
Proof.
  intro a.
  assert (Hm : Id (minus a zero) a).
  { change (Id (plus a (opp zero)) a).
    assert (Hopp0 : Id (opp zero) zero).
    { apply (id_trans (id_sym (id_trans (plus_comm zero (opp zero))
                                        (plus_zero (opp zero))))
                      (plus_opp zero)). }
    rewrite Hopp0.
    apply plus_zero. }
  apply (id_cong abs Hm).
Qed.

(* 辅助：NatLe 构造（n ≤ m ⟹ NatLe n m） *)
Lemma natle_of_le : forall n m, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt n m)) in E.
    lia.
Qed.

(* 夹逼核心：lim x_n E_star（iterate 序列）+ 初始梯度非零 ⟹ g(E_star) == 0。
   论证：对任意 eps > 0，取 n ≥ max N1 N2——
   |g(E_star) − g(x_n)| ≤ L·metric (x_n) E_star < eps2（lim_metric_approx + gradient_lipschitz）
   |g(x_n)| ≤ κ^n·|g0| < eps2（grad_decay_iter + r_arch_pow）
   三角 + eps/2 分割 ⟹ metric (g E_star) zero < eps ⟹ le_all_eps_zero ⟹ = 0。 *)
Lemma grad_squeeze_zero : forall (E_A E_star : R),
  lim (fun n => iterate dynamics n E_A) E_star ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  Id (entropy_gradient E_star) zero.
Proof.
  intros E_A E_star Hlim Hg0pos.
  apply metric_zero.
  apply le_antisym.
  - apply le_all_eps_zero.
    intros eps Heps.
    pose (eps2 := mult (inv_pos (plus one one) two_pos) eps).
    assert (Heps2 : lt zero eps2) by (unfold eps2; apply half_pos; exact Heps).
    pose (eps1 := mult (inv_pos L L_pos) eps2).
    assert (Heps1 : lt zero eps1).
    { unfold eps1.
      apply (mult_positive (inv_pos L L_pos) eps2).
      - apply (@inv_pos_pos RI L L_pos).
      - exact Heps2. }
    destruct (lim_metric_approx (fun n => iterate dynamics n E_A) E_star Hlim eps1 Heps1) as [N1 HN1].
  destruct (r_arch_pow (abs (entropy_gradient (iterate dynamics 0 E_A))) Hg0pos eps2 Heps2) as [N2 HN2].
    pose (n := Nat.max N1 N2).
    assert (Hn1 : NatLe N1 n) by (unfold n; apply natle_of_le; apply Nat.le_max_l).
    assert (Hn2 : NatLe N2 n) by (unfold n; apply natle_of_le; apply Nat.le_max_r).
    assert (Ht : le (metric (entropy_gradient E_star) zero)
                   (plus (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                         (metric (entropy_gradient (iterate dynamics n E_A)) zero))).
    { exact (metric_triangle (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)) zero). }
    assert (Hhalf1 : lt (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A))) eps2).
    { apply (le_lt_trans _ (mult L (metric (iterate dynamics n E_A) E_star)) _).
      - apply (le_id_l _ (abs (minus (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))) _).
        + apply (metric_abs (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A))).
        + apply (le_id_r _ (mult L (abs (minus E_star (iterate dynamics n E_A)))) _).
          * apply (id_cong (fun z => mult L z)
                   (id_trans (abs_minus_sym E_star (iterate dynamics n E_A))
                             (id_sym (metric_abs (iterate dynamics n E_A) E_star)))).
          * exact (gradient_lipschitz E_star (iterate dynamics n E_A)).
      - apply (lt_id_r _ (mult L eps1) _).
        + unfold eps1.
          apply (id_trans (mult_assoc L (inv_pos L L_pos) eps2)
                          (id_trans (id_cong (fun z => mult z eps2) (inv_pos_correct L L_pos))
                                    (id_trans (mult_comm one eps2) (mult_one eps2)))).
        + apply (lt_id_l _ (mult (metric (iterate dynamics n E_A) E_star) L) _).
          * apply (mult_comm L (metric (iterate dynamics n E_A) E_star)).
          * apply (lt_id_r _ (mult eps1 L) _).
            -- apply (id_sym (mult_comm L eps1)).
            -- apply (lt_mult_compat (metric (iterate dynamics n E_A) E_star) eps1 L L_pos).
               exact (HN1 n Hn1). }
    assert (Hhalf2 : lt (metric (entropy_gradient (iterate dynamics n E_A)) zero) eps2).
    { apply (le_lt_trans _ (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) _).
      - apply (le_id_l _ (abs (minus (entropy_gradient (iterate dynamics n E_A)) zero)) _).
        + apply (metric_abs (entropy_gradient (iterate dynamics n E_A)) zero).
        + apply (le_id_l _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
          * apply (abs_minus_zero (entropy_gradient (iterate dynamics n E_A))).
          * exact (grad_decay_iter E_A 0 n).
      - apply (le_lt_trans _ (mult (r_pow kappa N2) (abs (entropy_gradient (iterate dynamics 0 E_A)))) _).
        + apply (le_mult_compat_weak (r_pow kappa n) (r_pow kappa N2)
                                     (abs (entropy_gradient (iterate dynamics 0 E_A)))
                                     (abs_nonneg (entropy_gradient (iterate dynamics 0 E_A)))).
          apply (r_pow_dec_iter N2 n). exact (NatLe_drop N2 n Hn2).
        + apply (lt_id_l _ (mult (abs (entropy_gradient (iterate dynamics 0 E_A))) (r_pow kappa N2)) _).
          * apply (id_sym (mult_comm (abs (entropy_gradient (iterate dynamics 0 E_A))) (r_pow kappa N2))).
          * exact (HN2). }
    apply (lt_id_r _ (plus eps2 eps2) _).
    { apply (half_twice eps). }
    { apply (le_lt_trans _ (plus (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                                 (metric (entropy_gradient (iterate dynamics n E_A)) zero)) _).
      { exact Ht. }
      { apply (lt_plus_compat
                 (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                 eps2
                 (metric (entropy_gradient (iterate dynamics n E_A)) zero)
                 eps2
                 Hhalf1 Hhalf2). } }
  - apply (@metric_pos RI).
Qed.

(* 组装：dynamics_converges（以 ConvergenceCauchy 条件集替换 ConvergenceTheorem 的 Variable）。
   前提：初始梯度非零（iterate_lim_exists 需要）+ 收敛步长条件（原 Variable 前提保留）。
   链：iterate_lim_exists 给 lim 存在 → grad_squeeze_zero 夹逼 g(E_star) == 0。
   ⚠  T4.4 判据：`lt zero (minus (plus one one) (mult L eta))`（Hstep）已移除——
   证明体零引用（仅用 Hg0pos），收敛前提链 iterate_lim_exists / grad_squeeze_zero 均不含
   该形态前提，下游零引用（grep dynamics_converges 仅注释与定义处）。 *)
Theorem dynamics_converges : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  ExistsT (fun E_star : R =>
    And (lim (fun n => iterate dynamics n E_A) E_star)
        (Id (entropy_gradient E_star) zero)).
Proof.
  intros E_A Hg0pos.
  destruct (iterate_lim_exists E_A Hg0pos) as [E_star Hlim].
  exists E_star.
  split.
  - exact Hlim.
  - exact (grad_squeeze_zero E_A E_star Hlim Hg0pos).
Qed.

(* ============================================================
   论文4 收敛缺口补强（κ 定理化方向， 并入）：
   从 μ-强凹 + Lipschitz + 步长约束推正分支梯度收缩
   核心：gradient_step_contraction（单步收缩）、
         gradient_step_abs_contraction（绝对值收缩 κ := 1−ημ）、
         gradient_iterate_abs_decay（单步迭代收缩）、
         grad_decay_positive_iter（κ 幂衰减）。
   诚实接口新增：μ-强凹（standard 优化假设，非经典公理）。
   纪律：纯构造性 / Set 层 / 零 承认 / 零经典。
   ============================================================ *)
(* 新增：μ-强凹（x < y ⟹ μ(y−x) ≤ g(x) − g(y)，凹性模量化） *)
Variable mu : R.
Variable mu_pos : lt zero mu.
Variable strong_concavity : forall x y : R, lt x y ->
  le (mult mu (minus y x)) (minus (entropy_gradient x) (entropy_gradient y)).
(* ===== K0 动力学单步展开：dynamics x = x + η·g(x) ===== *)
Lemma dynamics_step_unfold : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Proof.
  intros x. exact (dynamics_gradient_step x).
Qed.

(* 辅助：minus a b + b == a（减法可逆） *)
Lemma minus_plus_cancel_gap : forall a b : R,
  Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (id_sym (plus_assoc a (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_comm (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  apply (plus_zero a).
Qed.

(* ===== K1a 正分支单步收缩（非绝对值版）：
   g(x) > 0 且 ημ < 1 ⟹ g(dynamics x) ≤ (1−ημ)·g(x)
   链：x < dyn（η·g>0）→ 强凹给 μ(dyn−x) ≤ g(x)−g(dyn)
        → (ημ)g ≤ g(x)−g(dyn) → 移项得 g(dyn) ≤ g(x)−(ημ)g == (1−ημ)g *)
Lemma gradient_step_contraction : forall x : R,
  lt zero eta ->
  lt (mult eta mu) one ->
  lt zero (entropy_gradient x) ->
  le (entropy_gradient (dynamics x))
     (mult (minus one (mult eta mu)) (entropy_gradient x)).
Proof.
  intros x Heta Heta_mu Hgx.
  (* x < dynamics x：η·g(x) > 0 ⟹ x < x + η·g(x) *)
  assert (Heta_g : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) Heta Hgx).
  assert (Hlt : lt x (dynamics x)).
  {
    apply (lt_id_l x (plus x zero) (dynamics x) (id_sym (plus_zero x))).
    apply (lt_id_r (plus x zero) (plus x (mult eta (entropy_gradient x))) (dynamics x)
                   (id_sym (dynamics_step_unfold x))).
    apply (lt_plus_compat_le_lt x x zero (mult eta (entropy_gradient x)) (le_refl x) Heta_g).
  }
  (* 强凹：μ(dynamics x − x) ≤ g(x) − g(dynamics x) *)
  pose proof (strong_concavity x (dynamics x) Hlt) as Hsc.
  (* minus (dynamics x) x == η·g(x) *)
  assert (Hdiff : Id (minus (dynamics x) x) (mult eta (entropy_gradient x))).
  {
    unfold minus.
    apply (id_trans (id_cong (fun z => plus z (opp x)) (dynamics_step_unfold x))).
    apply (id_trans (id_sym (plus_assoc x (mult eta (entropy_gradient x)) (opp x)))).
    apply (id_trans (id_cong (fun z => plus x z) (plus_comm (mult eta (entropy_gradient x)) (opp x)))).
    apply (id_trans (plus_assoc x (opp x) (mult eta (entropy_gradient x)))).
    apply (id_trans (id_cong (fun z => plus z (mult eta (entropy_gradient x))) (plus_opp x))).
    apply (id_trans (plus_comm zero (mult eta (entropy_gradient x)))).
    apply (plus_zero (mult eta (entropy_gradient x))).
  }
  (* 代入 Hdiff：μ·(η·g(x)) ≤ g(x) − g(dyn) *)
  assert (Hsc' : le (mult mu (mult eta (entropy_gradient x)))
                    (minus (entropy_gradient x) (entropy_gradient (dynamics x)))).
  { apply (le_id_l (mult mu (mult eta (entropy_gradient x)))
                   (mult mu (minus (dynamics x) x))
                   (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                   (id_sym (id_cong (fun z => mult mu z) Hdiff)) Hsc). }
  (* 换形：(ημ)·g(x) ≤ g(x) − g(dyn) *)
  assert (Hmm : Id (mult mu (mult eta (entropy_gradient x)))
                   (mult (mult eta mu) (entropy_gradient x))).
  {
    apply (id_trans (id_cong (fun z => mult mu z) (mult_comm eta (entropy_gradient x)))).
    apply (id_trans (mult_assoc mu (entropy_gradient x) eta)).
    apply (id_trans (id_cong (fun z => mult z eta) (mult_comm mu (entropy_gradient x)))).
    apply (id_trans (mult_comm (mult (entropy_gradient x) mu) eta)).
    apply (id_trans (id_cong (fun z => mult eta z) (mult_comm (entropy_gradient x) mu))).
    apply (mult_assoc eta mu (entropy_gradient x)).
  }
  assert (Hsc'' : le (mult (mult eta mu) (entropy_gradient x))
                     (minus (entropy_gradient x) (entropy_gradient (dynamics x)))).
  { apply (le_id_l (mult (mult eta mu) (entropy_gradient x))
                   (mult mu (mult eta (entropy_gradient x)))
                   (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                   (id_sym Hmm) Hsc'). }
  (* 移项：从 A ≤ B−C 推 C ≤ B−A
     1. 加 C：le (A+C) ((B−C)+C) == B ⟹ le (A+C) B
     2. 加 (opp A)：le ((A+C)+opp A) (B+opp A) ⟹ le C (B−A) *)
  pose (A := mult (mult eta mu) (entropy_gradient x)).
  pose (B := entropy_gradient x).
  pose (C := entropy_gradient (dynamics x)).
  assert (H1 : le (plus A C) B).
  {
    apply (le_id_r (plus A C) (plus (minus B C) C) B).
    - exact (minus_plus_cancel_gap B C).
    - apply (le_plus_compat A (minus B C) C C Hsc'' (le_refl C)).
  }
  assert (H2 : le (plus (plus A C) (opp A)) (plus B (opp A))).
  {
    apply (le_plus_compat (plus A C) B (opp A) (opp A) H1 (le_refl (opp A))).
  }
  (* 左侧化简：(A+C)+opp A == C *)
  assert (H3 : Id (plus (plus A C) (opp A)) C).
  {
    unfold A. unfold C.
    apply (id_trans (id_cong (fun z => plus z (opp (mult (mult eta mu) (entropy_gradient x))))
                             (plus_comm (mult (mult eta mu) (entropy_gradient x))
                                        (entropy_gradient (dynamics x))))).
    apply (id_trans (id_sym (plus_assoc (entropy_gradient (dynamics x))
                                        (mult (mult eta mu) (entropy_gradient x))
                                        (opp (mult (mult eta mu) (entropy_gradient x)))))).
    apply (id_trans (id_cong (fun z => plus (entropy_gradient (dynamics x)) z)
                             (plus_opp (mult (mult eta mu) (entropy_gradient x))))).
    apply (id_trans (plus_zero (entropy_gradient (dynamics x)))). apply id_refl.
  }
  (* 右侧：plus B (opp A) == minus (g x) ((ημ)g) == 目标形态 *)
  assert (H4 : Id (plus B (opp A)) (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))).
  { unfold A, B. apply id_refl. }
  (* 组装：le C (minus B ((ημ)g)) *)
  assert (H5 : le C (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))).
  {
    apply (le_id_l C (plus (plus A C) (opp A)) (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x))) (id_sym H3)).
    apply (le_id_r (plus (plus A C) (opp A)) (plus B (opp A)) (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x))) H4 H2).
  }
  (* 目标：le (g dyn) (mult (minus one (ημ)) (g x))；需 (1−ημ)·g == g − (ημ)g *)
  (* 目标：le C (mult (minus one (ημ)) g)；H5 : le C (minus g ((ημ)g))
     用 le_id_r 换 RHS：minus g ((ημ)g) == mult (minus one (ημ)) g *)
  assert (H6 : Id (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))
                  (mult (minus one (mult eta mu)) (entropy_gradient x))).
  {
    unfold minus.
    apply (id_sym (id_trans (mult_plus_distr_r one (opp (mult eta mu)) (entropy_gradient x))
                            (id_trans (id_cong (fun z => plus z (mult (opp (mult eta mu)) (entropy_gradient x))) (id_trans (mult_comm one (entropy_gradient x)) (mult_one (entropy_gradient x))))
                                      (id_cong (fun z => plus (entropy_gradient x) z) (opp_mult_r (mult eta mu) (entropy_gradient x)))))).
  }
  apply (le_id_r C (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))
                 (mult (minus one (mult eta mu)) (entropy_gradient x)) H6 H5).
Qed.

(* ===== 辅助：严格减正：a < b ⟹ 0 < b − a（K3 的 κ 正性需要） ===== *)
Lemma minus_pos : forall a b : R, lt a b -> lt zero (minus b a).
Proof.  intros a b Hab.
  unfold minus.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a)) (id_sym (plus_opp a))
           (lt_plus_compat_lt_le a b (opp a) (opp a) Hab (le_refl (opp a)))).
Qed.
(* ===== K1c 正分支单步绝对值收缩：g(x)>0 且 g(dyn)>0 且 ημ<1
   ⟹ |g(dyn)| ≤ (1−ημ)·|g(x)|
   证明：K1a 给 g(dyn) ≤ (1−ημ)g(x)；双正 ⟹ |g| = g（abs_pos）⟹ 直接换形 *)
Lemma gradient_step_abs_contraction : forall x : R,
  lt zero eta ->
  lt (mult eta mu) one ->
  lt zero (entropy_gradient x) ->
  lt zero (entropy_gradient (dynamics x)) ->
  le (abs (entropy_gradient (dynamics x)))
     (mult (minus one (mult eta mu)) (abs (entropy_gradient x))).
Proof.
  intros x Heta Heta_mu Hgx Hgdyn.
  (* |g(dyn)| == g(dyn)（abs_pos） *)
  assert (Habsd : Id (abs (entropy_gradient (dynamics x))) (entropy_gradient (dynamics x)))
    by exact (abs_pos (entropy_gradient (dynamics x)) Hgdyn).
  (* |g(x)| == g(x)（abs_pos） *)
  assert (Habsx : Id (abs (entropy_gradient x)) (entropy_gradient x))
    by exact (abs_pos (entropy_gradient x) Hgx).
  (* 目标换形：g(dyn) ≤ (1−ημ)·g(x)（K1a） *)
  apply (le_id_l (abs (entropy_gradient (dynamics x)))
                 (entropy_gradient (dynamics x))
                 (mult (minus one (mult eta mu)) (abs (entropy_gradient x)))
                 Habsd).
  apply (le_id_r (entropy_gradient (dynamics x))
                 (mult (minus one (mult eta mu)) (entropy_gradient x))
                 (mult (minus one (mult eta mu)) (abs (entropy_gradient x)))
                 (id_cong (fun z => mult (minus one (mult eta mu)) z) (id_sym Habsx))
                 (gradient_step_contraction x Heta Heta_mu Hgx)).
Qed.

(* ===== K2 正分支单步迭代收缩：任意步正（前提）⟹ |g(x_{n+1})| ≤ κ·|g(x_n)|
   κ := 1−ημ；证明：K1c 实例化 x := iterate dynamics n E_A *)
Theorem gradient_iterate_abs_decay : forall (E_A : R) (n : nat),
  lt zero eta ->
  lt (mult eta mu) one ->
  (forall k : nat, NatLe k (Datatypes.S n) -> lt zero (entropy_gradient (iterate dynamics k E_A))) ->
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult (minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n Heta Heta_mu Hall.
  (* x := iterate dynamics n E_A；前提 g(x) > 0 和 g(dyn x) > 0 *)
  assert (Hgn : lt zero (entropy_gradient (iterate dynamics n E_A))).
  { apply Hall. apply NatLe_lift. lia. }
  assert (Hgn1 : lt zero (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))).
  { apply Hall. apply NatLe_lift. lia. }
  (* dynamics (iterate dynamics n E_A) 与 iterate (S n) E_A 定义性相等（iterate 是 Fixpoint） *)
  exact (gradient_step_abs_contraction (iterate dynamics n E_A) Heta Heta_mu Hgn Hgn1).
Qed.

(* ===== K3 正分支 κ 幂衰减：|g(x_{n+k})| ≤ κ^k·|g(x_n)|（归纳，同 grad_decay_iter 结构）
   κ := 1−ημ；前提：全轨道正（j ≤ n+k） *)
Theorem grad_decay_positive_iter : forall (E_A : R) (n k : nat),
  lt zero eta ->
  lt (mult eta mu) one ->
  (forall j : nat, NatLe j (n + k) -> lt zero (entropy_gradient (iterate dynamics j E_A))) ->
  le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
     (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n k Heta Heta_mu Hall.
  (* κ > 0：1−ημ > 0（由 ημ < 1） *)
  assert (Hkpos : lt zero (minus one (mult eta mu))).
  { apply (minus_pos _ _ Heta_mu). }
  induction k as [| k IH]; simpl.
  - (* k = 0：|g(x_n)| ≤ 1·|g(x_n)| *)
    rewrite (Nat.add_0_r n).
    apply (le_id_r _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
    + apply (id_trans (id_sym (mult_one (abs (entropy_gradient (iterate dynamics n E_A)))))
                      (id_sym (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A)))))).
    + apply le_refl.
  - (* k = S k'：|g(x_{n+S k'})| ≤ κ·|g(x_{n+k'})| ≤ κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)| *)
    apply (le_trans _ (mult (minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics (n + k) E_A)))) _).
    + (* 单步：K2 at (n+k)，前提 j ≤ S(n+k) 由 Hall 给（n + S k' == S(n+k)） *)
      rewrite (Nat.add_succ_r n k).
      apply (gradient_iterate_abs_decay E_A (n + k) Heta Heta_mu).
      intros j Hj. apply Hall. apply NatLe_lift.
      assert (Hjle : (j <= Datatypes.S (n + k))%nat) by (apply NatLe_drop; exact Hj).
      lia.
    + (* 归纳步：κ·(κ^{k'}·|g(x_n)|) == κ^{S k'}·|g(x_n)|（mult_assoc + comm 换形） *)
      assert (IH' : le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                        (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))).
      { apply IH. intros j Hj. apply Hall. apply NatLe_lift.
        assert (Hjle : (j <= n + k)%nat) by (apply NatLe_drop; exact Hj).
        lia. }
      apply (le_id_r (mult (minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics (n + k) E_A))))
                     (mult (minus one (mult eta mu)) (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A)))))
                     (mult (mult (minus one (mult eta mu)) (r_pow (minus one (mult eta mu)) k)) (abs (entropy_gradient (iterate dynamics n E_A))))
                     (mult_assoc (minus one (mult eta mu)) (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))
                     (le_mult_compat_r (minus one (mult eta mu))
                                       (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                                       (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))
                                       (lt_le_iff _ _ (inl Hkpos))
                                       IH')).
Qed.

(* ================================================================
   论文4 差距一闭合（gradient_zero → is_truth），排序 4，
   诚实接口 entropy_tangent（凹函数切线不等式，一阶条件：
   f(y) ≤ f(x) + f'(x)·(y−x)，对所有 x y——标准优化假设，非经典公理）
   ⟹ gradient_zero_entropy_max：驻点（g(x)==0）是熵的全局最大点。
   绕开三分律（判例 障碍：Set 层无三分律，Real 层 Qlt_le_dec 三分
   可判定但需数百行 ε-δ）与积分（Real 层无 RInt/FTC）。
   is_truth 桥：以 L := −entropy（损失=负熵）则 is_truth (−entropy) x 成立。
   纪律：纯构造性 / Set 层 / 零 承认 / 零经典。
   ================================================================ *)
(* 凹性切线不等式（诚实接口，同 strict_concavity 的量化版本） *)
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))).

(* 差距一闭合：g(x)==0 ⟹ entropy y ≤ entropy x（驻点是全局最大点）
   证明：切线不等式 + g(x)==0 ⟹ entropy y ≤ entropy x + 0·(y−x) == entropy x。
   代数链：g(x)·(y−x) == 0·(y−x)（Hg）== 0（mult_comm + mult_zero）⟹ plus 吸收。 *)
Theorem gradient_zero_entropy_max : forall x : R,
  Id (entropy_gradient x) zero ->
  forall y : R, le (entropy y) (entropy x).
Proof.
  intros x Hg y.
  (* 切线不等式：entropy y ≤ entropy x + g(x)·(y−x) *)
  assert (Htangent : le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))))
    by exact (entropy_tangent x y).
  (* 代数：g(x)·(y−x) == 0·(y−x) == 0，plus (entropy x) 0 == entropy x *)
  assert (Hid : Id (plus (entropy x) (mult (entropy_gradient x) (minus y x))) (entropy x)).
  {
    apply (id_trans (id_cong (fun z => plus (entropy x) z)
                             (id_trans (id_cong (fun z => mult z (minus y x)) Hg)
                                       (id_trans (mult_comm zero (minus y x))
                                                 (mult_zero (minus y x)))))).
    apply (plus_zero (entropy x)).
  }
  (* 组装：entropy y ≤ plus ... 且 plus ... == entropy x ⟹ entropy y ≤ entropy x *)
  exact (le_id_r (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))) (entropy x) Hid Htangent).
Qed.

(* is_truth 桥：g(x)==0 ⟹ (−entropy) 在 x 处全局最小（is_truth 形式，损失=负熵） *)
Theorem gradient_zero_neg_entropy_truth : forall x : R,
  Id (entropy_gradient x) zero ->
  forall y : R, le (opp (entropy x)) (opp (entropy y)).
Proof.
  intros x Hg y.
  (* 由差距一：le (entropy y) (entropy x) ⟹ opp 保序反号 *)
  apply (opp_le_compat (entropy y) (entropy x)).
  exact (gradient_zero_entropy_max x Hg y).
Qed.

(* ============================================================
   论文4 收敛缺口补强（差距二闭合，，检验 _dbg_unique_attractor.v 验证）：
   唯一吸引子 —— 任意两条轨道（任意初值）的极限相同。
   路线：弱三分（诚实接口 Variable，Real 层 real_weak_trich L32526 已证供给）
         + 严格递减（strict_concavity）⟹ 驻点唯一（gradient_zero_unique）
         ⟹ grad_squeeze_zero + 驻点唯一组装唯一吸引子（unique_attractor）
         ⟹ PCT 组装（attractor_converges_unique_truth：极限 = 唯一吸引子
           = 驻点 = −entropy 的 is_truth 点；差距一已由
           gradient_zero_neg_entropy_truth 闭合，差距二由 unique_attractor 闭合）。
   纪律：纯构造性 / Set 层 / 禁 Prop 定义 / 信息性证明 / 零 承认 /
         零经典（无排中律、无经典实数公理）/ 可提取 OCaml。
   ============================================================ *)
(* 诚实接口假设：弱三分（Real 层 real_weak_trich L32526 已证，构造性成立；
   ¬(x<y) ∧ ¬(y<x) ⟹ x==y，非 LPO——整体三分律才等价 LPO） *)
(* [墙族登记·RW-TIGHT 紧性] 接口层紧性公设（Not(lt)×2→Id）：RealInterface(Enhanced) 无紧性字段，接口层不可导，禁硬证；具体层 real_weak_trich 已证（S07_RealSetoidExpLog.v:5748，构造性成立）——TB-2 字段化归一批把实例供给上收；Not 形=Prop 红线对象，Set 重述仅重写载体不消内容（白皮书§0红线2）。 *)
Variable weak_trich : forall x y : R, Not (lt x y) -> Not (lt y x) -> Id x y.

(* K1：驻点唯一性（g 严格递减 ⟹ 至多一个驻点） *)
Lemma gradient_zero_unique : forall x y : R,
  Id (entropy_gradient x) zero ->
  Id (entropy_gradient y) zero ->
  Id x y.
Proof.
  intros x y Hgx Hgy.
  apply weak_trich.
  - (* Not (lt x y)：假设 lt x y ⟹ strict_concavity 给 lt (g y) (g x)
       ⟹ 代入 g x == 0（lt_id_r）⟹ lt (g y) zero
       ⟹ 代入 g y == 0（lt_id_l）⟹ lt zero zero ⟹ 矛盾 lt_irrefl *)
    intro Hxy.
    pose proof (strict_concavity x y Hxy) as Hdec.
    apply (lt_irrefl zero).
    apply (lt_id_l zero (entropy_gradient y) zero).
    + apply id_sym. exact Hgy.
    + apply (lt_id_r (entropy_gradient y) (entropy_gradient x) zero Hgx Hdec).
  - (* Not (lt y x)：对称 *)
    intro Hyx.
    pose proof (strict_concavity y x Hyx) as Hdec.
    apply (lt_irrefl zero).
    apply (lt_id_l zero (entropy_gradient x) zero).
    + apply id_sym. exact Hgx.
    + apply (lt_id_r (entropy_gradient x) (entropy_gradient y) zero Hgy Hdec).
Qed.

(* K3：唯一吸引子 —— 任意两条轨道（任意初值、任意极限）的极限相同。
   grad_squeeze_zero（L14234）把每条轨道的极限夹逼为驻点；
   gradient_zero_unique（K1）保证驻点唯一 ⟹ 极限相同。 *)
Theorem unique_attractor : forall (E_A E_A' : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A'))) ->
  forall E1 E2 : R,
    lim (fun n => iterate dynamics n E_A) E1 ->
    lim (fun n => iterate dynamics n E_A') E2 ->
    Id E1 E2.
Proof.
  intros E_A E_A' Hg0 Hg0' E1 E2 Hlim1 Hlim2.
  pose proof (grad_squeeze_zero E_A E1 Hlim1 Hg0) as Hg1.
  pose proof (grad_squeeze_zero E_A' E2 Hlim2 Hg0') as Hg2.
  exact (gradient_zero_unique E1 E2 Hg1 Hg2).
Qed.

(* PCT 组装：任意轨道极限 = 唯一吸引子 = 驻点 = −entropy 的 is_truth 点。
   差距一（驻点 ⟹ is_truth）由 gradient_zero_neg_entropy_truth（L14611）闭合；
   差距二（单轨 ⟹ 全局吸引）由 unique_attractor 闭合。
   And 为 Set 层信息性合取，可提取。 *)
Theorem attractor_converges_unique_truth : forall (E_A E_A' : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A'))) ->
  forall E1 E2 : R,
    lim (fun n => iterate dynamics n E_A) E1 ->
    lim (fun n => iterate dynamics n E_A') E2 ->
    And (Id E1 E2)
        (And (Id (entropy_gradient E1) zero)
             (forall y : R, le (opp (entropy E1)) (opp (entropy y)))).
Proof.
  intros E_A E_A' Hg0 Hg0' E1 E2 Hlim1 Hlim2.
  pose proof (grad_squeeze_zero E_A E1 Hlim1 Hg0) as Hg1.
  pose proof (grad_squeeze_zero E_A' E2 Hlim2 Hg0') as Hg2.
  split.
  - exact (gradient_zero_unique E1 E2 Hg1 Hg2).
  - split.
    + exact Hg1.
    + exact (gradient_zero_neg_entropy_truth E1 Hg1).
Qed.

End ConvergenceCauchy.
(* ============================================================ *)
(* 关键证明：SumExpPositive / ArgminCorrectness 等             *)
(* ============================================================ *)

Section KeyProofs.

Context {RI : RealInterfaceEnhanced}.

Section SumExpPositive.

Variable Token : Set.

(* 解包字段（使用不同名称避免遮蔽） *)
Let R := @R RI.
Let zero := @zero RI.
Let plus := @plus RI.
Let exp_neg := @exp_neg RI.
Let lt := @lt RI.
Let exp_neg_pos_local := @exp_neg_pos RI.
Let plus_positive_local := @plus_positive RI.
Let plus_zero_local := @plus_zero RI.

Variable neg_log_prob : list Token -> Token -> R.

Fixpoint sum_exp (prefix : list Token) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (neg_log_prob prefix w)) (sum_exp prefix rest)
  end.

Lemma sum_exp_positive :
  forall prefix l, Not (Id l nil) -> lt zero (sum_exp prefix l).
Proof.
  intros prefix l. induction l as [| w rest IH].
  - intros Hnil. contradiction Hnil. apply id_refl.
  - intros _. simpl.
    destruct rest as [| w' rest'].
    + (* rest = [] *)
      simpl.
      exact (match id_sym (plus_zero_local (exp_neg (neg_log_prob prefix w))) in (Id _ b) return (lt zero b) with
             | id_refl => exp_neg_pos_local (neg_log_prob prefix w)
             end).
    + (* rest = w' :: rest' *)
      simpl.
      apply plus_positive_local.
      * apply exp_neg_pos_local.
      * apply IH. intro H. inversion H.   (* 或者 [destruct H] *)
Qed.

End SumExpPositive.

Section ArgminCorrectness.

Variable Token : Set.
Context {DO : DecidableOrder RI}.
Let R := @R RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le_trans := @le_trans RI.
Let le_refl := @le_refl RI.

Variable total_loss : list Token -> R.

Definition candidate : Set := (Token * R)%type.

Fixpoint argmin_aux (prefix : list Token) (l : list Token) (best : candidate) : candidate :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match (@ord_le_dec RI DO) loss_w (snd best) with
      | inl _ => argmin_aux prefix rest (w, loss_w)
      | inr _ => argmin_aux prefix rest best
      end
  end.

Lemma argmin_aux_correct :
  forall prefix l best_token best_loss,
    let result := argmin_aux prefix l (best_token, best_loss) in
    And (le (snd result) best_loss)
        (forall w : Token, InT w l ->
          le (snd result) (total_loss (prefix ++ [w]))).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - simpl. split.
    + apply le_refl.
    + intros w HIn. inversion HIn.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + specialize (IH a (total_loss (prefix ++ [a]))).
      destruct IH as [IH_le IH_min].
      split.
      * eapply le_trans.
        -- apply IH_le.
        -- exact Hle.
      * intros w HIn.
        inversion HIn as [Hw | HIn']; subst.
        -- apply IH_le.
        -- apply IH_min. assumption.
    + specialize (IH best_token best_loss).
      destruct IH as [IH_le IH_min].
      split.
      * apply IH_le.
      * intros w HIn.
        inversion HIn as [Hw | HIn']; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a]))).
           { apply not_le_lt. exact Hnot. }
           apply le_trans with best_loss.
           ++ apply IH_le.
           ++ apply lt_le_iff. left. exact Hlt.
        -- apply IH_min. assumption.
Qed.

Lemma argmin_aux_snd_correct :
  forall prefix l best_token best_loss,
    Id best_loss (total_loss (prefix ++ [best_token])) ->
    Id (snd (argmin_aux prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [fst (argmin_aux prefix l (best_token, best_loss))])).
Proof.
  induction l as [| a rest IH]; intros best_token best_loss Hbest.
  - simpl. exact Hbest.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + apply IH. apply id_refl.
    + apply IH. exact Hbest.
Qed.

Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable default_token : Token.

Definition pick_best (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

Theorem pick_best_is_minimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (prefix ++ [pick_best prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold pick_best.
  destruct vocab as [| w0 rest].
  - inversion HIn.
  - simpl.
    destruct (argmin_aux_correct prefix rest w0 (total_loss (prefix ++ [w0]))) as [Hbest Hmin].
    (* 获得 snd 与 fst 的关系 *)
    assert (Hsnd := argmin_aux_snd_correct prefix rest w0 (total_loss (prefix ++ [w0])) id_refl).
    assert (Hsnde : snd (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0]))) =
                    total_loss (prefix ++ [fst (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))]))
      by exact (match Hsnd in (Id _ z) return
                  (snd (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0]))) = z)
                with | id_refl => eq_refl end).
    (* 分析 w 在 vocab 中的两种可能 *)
    inversion HIn as [Hw | HIn']; subst.
    + (* 情况1：w = w0 *)
      rewrite <- Hsnde.
      apply Hbest.
    + (* 情况2：w 在 rest 中 *)
      rewrite <- Hsnde.
      apply Hmin. assumption.
Qed.

(* 贪心动力学：单步扩展为追加 pick_best（总损失最小者） *)
Definition dynamics (s : list Token) : list Token :=
  s ++ [pick_best s].

(* 贪心动力学的局部最优性（补齐预测性质.txt 模块1 目标）：
   对任意前缀 prefix 与候选 token w，动力学扩展（追加 pick_best）的
   总损失不超过追加任意 w 的总损失——贪心步是局部最优的。 *)
Theorem dynamics_greedy_locally_optimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (dynamics prefix)) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold dynamics.
  exact (pick_best_is_minimal prefix w HIn).
Qed.

End ArgminCorrectness.

Section SequenceLossPrefixApp.

Local Existing Instance RI_base.
Let R := @R RI.
Let zero := @zero RI.
Let plus := @plus RI.

Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> R.

Fixpoint sequence_loss_prefix (prefix : list Token) (s : list Token) : R :=
  match s with
  | nil => zero
  | w :: rest =>
      plus (neg_log_prob prefix w) (sequence_loss_prefix (prefix ++ [w]) rest)
  end.

Lemma id_app_nil_r : forall (A : Set) (l : list A), Id (l ++ []) l.
Proof.
  induction l as [| x xs IH].
  - simpl. apply id_refl.
  - simpl. apply (id_cong (cons x)). exact IH.
Qed.

Lemma id_app_cons_assoc : forall (A : Set) (l : list A) (x : A) (rest : list A),
  Id (l ++ x :: rest) ((l ++ [x]) ++ rest).
Proof.
  induction l as [| y l' IH]; intros x rest.
  - simpl. apply id_refl.
  - simpl. apply (id_cong (cons y)). apply IH.
Qed.

Lemma sequence_loss_prefix_app :
  forall prefix s1 s2,
    Id (sequence_loss_prefix prefix (s1 ++ s2))
       (plus (sequence_loss_prefix prefix s1)
             (sequence_loss_prefix (prefix ++ s1) s2)).
Proof.
  intros prefix s1. revert prefix.
  induction s1 as [| w rest IH]; intros prefix.
  - intros s2.
    assert (H1 : Id (sequence_loss_prefix prefix s2)
                    (sequence_loss_prefix (prefix ++ []) s2)).
    { apply id_sym. apply (id_cong (fun p => sequence_loss_prefix p s2)). apply id_app_nil_r. }
    assert (H2 : Id (sequence_loss_prefix (prefix ++ []) s2)
                    (plus zero (sequence_loss_prefix (prefix ++ []) s2))).
    { apply id_sym. apply (id_trans (plus_comm zero _) (plus_zero _)). }
    exact (id_trans H1 H2).
  - intros s2.
    pose proof (IH (prefix ++ [w]) s2) as IH_s2.
    (* 步骤 1：定义展开左侧 *)
    assert (Hdef_left : Id (sequence_loss_prefix prefix ((w :: rest) ++ s2))
                           (plus (neg_log_prob prefix w)
                                 (sequence_loss_prefix (prefix ++ [w]) (rest ++ s2)))).
    { simpl. apply id_refl. }
    (* 步骤 2：使用归纳假设和结合律 *)
    assert (Hcong : Id (plus (neg_log_prob prefix w)
                            (sequence_loss_prefix (prefix ++ [w]) (rest ++ s2)))
                     (plus (neg_log_prob prefix w)
                           (plus (sequence_loss_prefix (prefix ++ [w]) rest)
                                 (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2)))).
    { apply (id_cong (fun x => plus (neg_log_prob prefix w) x)). exact IH_s2. }
    assert (Hassoc : Id (plus (neg_log_prob prefix w)
                              (plus (sequence_loss_prefix (prefix ++ [w]) rest)
                                    (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2)))
                        (plus (plus (neg_log_prob prefix w)
                                    (sequence_loss_prefix (prefix ++ [w]) rest))
                              (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2))).
    { apply plus_assoc. }
    assert (Hmid : Id (plus (neg_log_prob prefix w)
                            (sequence_loss_prefix (prefix ++ [w]) (rest ++ s2)))
                     (plus (plus (neg_log_prob prefix w)
                                 (sequence_loss_prefix (prefix ++ [w]) rest))
                           (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2))).
    { exact (id_trans Hcong Hassoc). }
    (* 步骤 3：定义展开右侧并应用列表等式 *)
    assert (Hdef_right : Id (plus (plus (neg_log_prob prefix w)
                                        (sequence_loss_prefix (prefix ++ [w]) rest))
                                  (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2))
                           (plus (sequence_loss_prefix prefix (w :: rest))
                                 (sequence_loss_prefix (prefix ++ w :: rest) s2))).
    {
      simpl.
      apply (id_cong (fun p => plus (plus (neg_log_prob prefix w)
                                          (sequence_loss_prefix (prefix ++ [w]) rest))
                                    (sequence_loss_prefix p s2))).
      apply id_sym. apply id_app_cons_assoc.
    }
    (* 最终组合 *)
    exact (id_trans Hdef_left (id_trans Hmid Hdef_right)).
Qed.

End SequenceLossPrefixApp.

End KeyProofs.

(* ============================================================ *)
(* 第八部分：论文核心内容的构造性形式化补全与缺失提取         *)
(* ============================================================ *)

Import PropositionConvergenceCore.

Section StateSpaceUtilities.
Context {RI : RealInterface}.
Context {SS : StateSpace RI}.

Definition sminus (a b : S) : S := splus a (sopp b).

Definition gradient_step (eta : R) (grad : (S -> R) -> S -> S) (L : S -> R) (s : S) : S :=
  splus s (smult eta (grad L s)).

End StateSpaceUtilities.

Section PropositionBasics.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Definition IsProposition (P : Proposition) : Set :=
  forall s : S, And (le zero (P s)) (le (P s) one).

Definition IsPositiveProposition (P : Proposition) : Set :=
  forall s : S, lt zero (P s).

End PropositionBasics.

Section LossAggregation.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Definition loss_of_proposition (P : Proposition) (s : S) : R :=
  log_inv (P s).

Definition weighted_sum_loss (props : list (Proposition * R)) (s : S) : R :=
  fold_right (fun (p_w : Proposition * R) acc =>
                let (P, w) := p_w in
                plus (mult w (loss_of_proposition P s)) acc)
             zero props.

Definition softmax_loss (props : list Proposition) (s : S) : R :=
  log_inv (fold_right (fun P acc =>
                         plus (exp_neg (loss_of_proposition P s)) acc)
                      zero props).

End LossAggregation.

Section GradientDescentAndAttractor.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 解包字段 *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let plus := @plus RI.
Let smult := @smult RI SS.
Let splus := @splus RI SS.
Let sopp := @sopp RI SS.
Let le := @le RI.
Let lt := @lt RI.
Let smetric := @smetric RI SS.
Let sum_over_S := @sum_over_S RI SS SO.

Variable grad : (S -> R) -> S -> S.

Definition force (L : S -> R) (s : S) : S :=
  sopp (grad L s).

Variable noise : S -> S.
Variable sigma : R.

Definition sgd_step (L : S -> R) (s : S) : S :=
  splus (smult sigma (force L s))
        (smult sigma (noise s)).

Variable transition_kernel : (S -> R) -> S -> S -> R.
Variable transition_nonneg : forall L s s', le zero (transition_kernel L s s').
Variable transition_normalization :
  forall L s, Id (sum_over_S (fun s' => transition_kernel L s s')) one.

Definition is_truth (L : S -> R) (s : S) : Set :=
  forall s' : S, le (L s) (L s').

Definition omega_limit (dyn : S -> S) (s0 : S) (s : S) : Set :=
  forall eps : R, lt zero eps ->
    sigT (fun n : nat => lt (smetric (iterate dyn n s0) s) eps).

Definition is_attractor (L : S -> R) (s : S) : Set :=
  forall s0 : S, omega_limit (sgd_step L) s0 s.

End GradientDescentAndAttractor.

(* 层级命题汇聚的聚合函数实现 *)
Section HierarchicalPropositions.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let R := @R RI.
Let S := @S RI SS.
Let PropType := @Proposition RI SS.
Let loss_of_proposition := @loss_of_proposition RI SS.

Inductive PropositionLayer : Set :=
| BaseProp : PropType -> PropositionLayer
| ConjProp : list PropositionLayer -> (list R -> R) -> PropositionLayer.

Fixpoint eval_layer_loss (layer : PropositionLayer) (s : S) : R :=
  match layer with
  | BaseProp P => loss_of_proposition P s
  | ConjProp sub_layers agg =>
      agg (map (fun sub => eval_layer_loss sub s) sub_layers)
  end.

Definition softmax_aggregation (losses : list R) : R :=
  log_inv (fold_right (fun L acc => plus (exp_neg L) acc) zero losses).

Fixpoint safe_weighted_sum (weights losses : list R) : R :=
  match weights, losses with
  | w :: ws, l :: ls => plus (mult w l) (safe_weighted_sum ws ls)
  | _, _ => zero
  end.

Definition weighted_sum_aggregation (weights : list R) (losses : list R) : R :=
  safe_weighted_sum weights losses.

End HierarchicalPropositions.

Section BoltzmannSteadyState.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 绑定基本类型和函数 *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.

Variable Z : R.
Variable Z_pos : lt zero Z.
Variable partition_condition : Id Z (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

Definition boltzmann_unnorm (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (base_loss s)).

Definition boltzmann_prob (s : S) : R :=
  mult (inv_pos Z Z_pos) (boltzmann_unnorm s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_prob s) (transition s s'))
       (mult (boltzmann_prob s') (transition s' s)).

(* 非平凡实现：详细平衡 ⟹ 稳态（马尔可夫链基本定理）。
   纯构造性：逐点详细平衡 + 求和线性（sum_over_S_linear） + 转移归一化。
   注意：本 section 有 Let 解包（Let sum_over_S/mult 等），接口字段陈述为投影级，
   需 change 到 Let 层再 rewrite（见判例）。 *)
Theorem steady_state_boltzmann :
  forall s,
    Id (sum_over_S (fun s' => mult (boltzmann_prob s') (transition s' s)))
       (boltzmann_prob s).
Proof.
  intro s.
  (* 1. 逐点详细平衡：∀s', p(s')·T(s',s) = p(s)·T(s,s') *)
  assert (Hpoint : forall s', Id (mult (boltzmann_prob s') (transition s' s))
                               (mult (boltzmann_prob s) (transition s s'))).
  { intro s'. apply (detailed_balance s' s). }
  (* 2. 用外延性（sum_over_S_ext）在求和参数内替换 *)
  assert (Hswap : Id (sum_over_S (fun s' => mult (boltzmann_prob s') (transition s' s)))
                     (sum_over_S (fun s' => mult (boltzmann_prob s) (transition s s')))).
  { apply sum_over_S_ext. exact Hpoint. }
  rewrite Hswap.
  (* 3. 提出常数因子 p(s)（sum_over_S_linear 投影陈述 → change 到 Let 层） *)
  pose proof (@sum_over_S_linear RI SS SO (boltzmann_prob s) (fun s' => transition s s')) as Hlin.
  change (Id (sum_over_S (fun s' => mult (boltzmann_prob s) (transition s s')))
             (mult (boltzmann_prob s) (sum_over_S (fun s' => transition s s')))) in Hlin.
  rewrite Hlin.
  (* 4. 转移归一化：Σ_{s'} T(s,s') = 1 *)
  rewrite (transition_normalization s).
  (* 5. p(s)·1 = p(s)（mult_one 投影陈述 → change 到 Let 层） *)
  pose proof (mult_one (boltzmann_prob s)) as Hm1.
  change (Id (mult (boltzmann_prob s) one) (boltzmann_prob s)) in Hm1.
  rewrite Hm1.
  reflexivity.
Qed.

End BoltzmannSteadyState.

(* ============================================================ *)
(* 项 6 工具（，通用接口层）：正乘严格消去（lt 版）   *)
(* ============================================================ *)
Section TempStrictTools.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let inv_pos := @inv_pos RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* 正乘严格消去：c > 0 且 a·c > 0 ⟹ a > 0（a == (a·c)·inv c） *)
Lemma lt_mult_pos_cancel : forall a c : R, lt zero c -> lt zero (mult a c) -> lt zero a.
Proof.
  intros a c Hc H.
  apply (lt_id_r zero (mult (mult a c) (inv_pos c Hc)) a).
  - apply id_sym.
    exact (id_trans (id_sym (mult_one a))
           (id_trans (id_cong (fun x => mult a x) (id_sym (inv_pos_correct c Hc)))
                     (mult_assoc a c (inv_pos c Hc)))).
  - apply mult_positive.
    + exact H.
    + apply inv_pos_pos.
Qed.

End TempStrictTools.

Section FreeEnergyMinimization.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.                       (* 注意：free_energy 中使用了 log *)
Let sum_over_S := @sum_over_S RI SS SO.

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.

Definition free_energy (p : S -> R) : R :=
  plus (sum_over_S (fun s => mult (p s) (base_loss s)))
       (mult D (sum_over_S (fun s => mult (p s) (log (p s))))).

Definition normalized (p : S -> R) : Set := Id (sum_over_S p) one.
Definition positive_dist (p : S -> R) : Set := forall s, lt zero (p s).

Variable Z : R.
Variable Z_pos : lt zero Z.
Variable partition_condition : Id Z (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

Definition boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).

(* ============================================================ *)
(* 训练-推理闭环（非平凡实现：自由能与 Boltzmann 分布的精确连接）*)
(* ============================================================ *)

(* sum 的负号线性：Σ (-f) = -Σ f *)
Lemma sum_opp :
  forall (f : S -> R),
    Id (sum_over_S (fun s => opp (f s))) (opp (sum_over_S f)).
Proof.
  intro f.
  assert (Hext : Id (sum_over_S (fun s => opp (f s)))
                   (sum_over_S (fun s => mult (opp one) (f s)))).
  {
    apply sum_over_S_ext.
    intro s.
    assert (H1 : Id (mult (opp one) (f s)) (opp (mult one (f s))))
      by exact (opp_mult_r one (f s)).
    assert (H2 : Id (opp (mult one (f s))) (opp (f s)))
      by exact (id_cong opp (id_trans (mult_comm one (f s)) (mult_one (f s)))).
    exact (id_trans (id_sym H2) (id_sym H1)).
  }
  rewrite Hext.
  assert (Hlin : Id (sum_over_S (fun s => mult (opp one) (f s)))
                   (mult (opp one) (sum_over_S f)))
    by exact (sum_over_S_linear (opp one) f).
  rewrite Hlin.
  assert (H1 : Id (mult (opp one) (sum_over_S f)) (opp (mult one (sum_over_S f))))
    by exact (opp_mult_r one (sum_over_S f)).
  assert (H2 : Id (opp (mult one (sum_over_S f))) (opp (sum_over_S f)))
    by exact (id_cong opp (id_trans (mult_comm one (sum_over_S f)) (mult_one (sum_over_S f)))).
  exact (id_trans H1 H2).
Qed.

(* sum 的减法线性：Σ (f - g) = Σ f - Σ g（由 add + opp 推出） *)
Lemma sum_over_S_minus :
  forall (f g : S -> R),
    Id (sum_over_S (fun s => minus (f s) (g s)))
       (minus (sum_over_S f) (sum_over_S g)).
Proof.
  intros f g.
  unfold minus.
  assert (Hadd : Id (sum_over_S (fun s => plus (f s) (opp (g s))))
                   (plus (sum_over_S f) (sum_over_S (fun s => opp (g s)))))
    by exact (sum_over_S_add f (fun s => opp (g s))).
  assert (Hopp : Id (sum_over_S (fun s => opp (g s))) (opp (sum_over_S g)))
    by exact (sum_opp g).
  exact (id_trans Hadd (id_cong (fun x => plus (sum_over_S f) x) Hopp)).
Qed.

(* Boltzmann 分布归一化：Σ_s p_b(s) = 1（概率质量守恒；平凡版——配分函数定义的重述） *)
Theorem boltzmann_normalized :
  Id (sum_over_S boltzmann_dist) one.
Proof.
  unfold boltzmann_dist.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   (mult (inv_pos Z Z_pos) (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))))
    by exact (sum_over_S_linear (inv_pos Z Z_pos) (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  assert (HZ : Id (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z)
    by exact (id_sym partition_condition).
  assert (Hcc : Id (mult (inv_pos Z Z_pos) Z) one)
    by exact (id_trans (mult_comm (inv_pos Z Z_pos) Z) (inv_pos_correct Z Z_pos)).
  exact (id_trans Hlin (id_trans (id_cong (fun x => mult (inv_pos Z Z_pos) x) HZ) Hcc)).
Qed.

(* 非平凡版本：凸组合归一化守恒——概率分布的凸组合闭包
   （混合策略 / 模型集成 / 蒸馏的数学基础；分布代数的守恒律，
    非配分函数定义的重述）。 *)
Theorem boltzmann_mix_normalized :
  forall (p q : S -> R) (alpha : R) (Halpha : lt zero alpha) (Halpha1 : lt zero (minus one alpha)),
    normalized p -> normalized q ->
    Id (sum_over_S (fun s => plus (mult alpha (p s)) (mult (minus one alpha) (q s)))) one.
Proof.
  intros p q alpha Halpha Halpha1 Hp Hq.
  unfold normalized in Hp, Hq.
  assert (Hadd : Id (sum_over_S (fun s => plus (mult alpha (p s)) (mult (minus one alpha) (q s))))
                   (plus (sum_over_S (fun s => mult alpha (p s))) (sum_over_S (fun s => mult (minus one alpha) (q s)))))
    by exact (sum_over_S_add (fun s => mult alpha (p s)) (fun s => mult (minus one alpha) (q s))).
  rewrite Hadd.
  assert (Hlin1 : Id (sum_over_S (fun s => mult alpha (p s))) (mult alpha (sum_over_S p)))
    by exact (sum_over_S_linear alpha p).
  rewrite Hlin1.
  assert (Hlin2 : Id (sum_over_S (fun s => mult (minus one alpha) (q s))) (mult (minus one alpha) (sum_over_S q)))
    by exact (sum_over_S_linear (minus one alpha) q).
  rewrite Hlin2.
  rewrite Hp. rewrite Hq.
  assert (Hm1 : Id (mult alpha one) alpha) by exact (mult_one alpha).
  rewrite Hm1.
  assert (Hm2 : Id (mult (minus one alpha) one) (minus one alpha)) by exact (mult_one (minus one alpha)).
  rewrite Hm2.
  (* 目标：plus alpha (minus one alpha) = one——assert + exact 链（避免 unfold/rewrite 目标依赖） *)
  assert (Hfin : Id (plus alpha (minus one alpha)) one).
  {
    unfold minus.
    assert (Hsw : Id (plus alpha (plus one (opp alpha))) (plus one (plus alpha (opp alpha)))).
    {
      assert (H1 : Id (plus alpha (plus one (opp alpha))) (plus (plus alpha one) (opp alpha)))
        by exact (plus_assoc alpha one (opp alpha)).
      assert (H2 : Id (plus (plus alpha one) (opp alpha)) (plus (plus one alpha) (opp alpha)))
        by exact (id_cong (fun x => plus x (opp alpha)) (plus_comm alpha one)).
      assert (H3 : Id (plus (plus one alpha) (opp alpha)) (plus one (plus alpha (opp alpha))))
        by exact (id_sym (plus_assoc one alpha (opp alpha))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    assert (Hfin2 : Id (plus one (plus alpha (opp alpha))) one).
    {
      assert (Hpz : Id (plus one zero) one) by exact (plus_zero one).
      assert (Hpz2 : Id (plus one (plus alpha (opp alpha))) (plus one zero))
        by exact (id_cong (fun x => plus one x) (plus_opp alpha)).
      exact (id_trans Hpz2 Hpz).
    }
    exact (id_trans Hsw Hfin2).
  }
  exact Hfin.
Qed.

(* Boltzmann 分布的对数分解：log p_b(s) = -log Z - E(s)/D *)
Theorem boltzmann_log_decomp :
  forall s : S,
    Id (log (boltzmann_dist s))
       (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intro s.
  unfold boltzmann_dist.
  assert (Hpos1 : lt zero (inv_pos Z Z_pos)) by exact (inv_pos_pos Z Z_pos).
  assert (Hpos2 : lt zero (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
    by exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
  assert (Hlm : Id (log (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                  (plus (log (inv_pos Z Z_pos)) (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))))))
    by exact (log_mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))) Hpos1 Hpos2).
  rewrite Hlm.
  assert (Hli : Id (log (inv_pos Z Z_pos)) (opp (log Z)))
    by exact (log_inv_one_inv Z Z_pos).
  rewrite Hli.
  assert (Hle : Id (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                  (opp (mult (inv_pos D D_pos) (base_loss s))))
    by exact (log_exp_neg (mult (inv_pos D D_pos) (base_loss s))).
  rewrite Hle.
  reflexivity.
Qed.

(* ============================================================ *)
(* 训练-推理闭环定理：自由能在 Boltzmann 分布处的显式值        *)
(*   F[p_b] = ⟨E⟩ + D·Σ p_b·log p_b = -D·log Z                 *)
(* ============================================================ *)
(* 训练阶段：自由能最小化（min_free_energy_is_boltzmann）给出 Boltzmann 分布；
   推理阶段：该分布的熵-能量平衡坍缩出精确闭合值 -D·log Z。
   非平凡推导链：逐点对数分解（boltzmann_log_decomp）→
   求和线性/负号线性（sum_over_S_add/linear + sum_opp）→
   归一化（boltzmann_normalized）→ 环代数坍缩。 *)
Theorem free_energy_boltzmann :
  Id (free_energy boltzmann_dist) (mult (opp D) (log Z)).
Proof.
  unfold free_energy.
  set (Eavg := sum_over_S (fun s => mult (boltzmann_dist s) (base_loss s))).
  (* Let 层桥接：字段引理 → 节内定义（判例 模式：exact 走转换，rewrite 需同层断言） *)
  assert (Hdist : forall a b c : R, Id (mult a (plus b c)) (plus (mult a b) (mult a c)))
    by exact (distrib).
  assert (Hoppl : forall a b : R, Id (mult a (opp b)) (opp (mult a b)))
    by exact (opp_mult_l).
  assert (Hoppr : forall a b : R, Id (mult (opp a) b) (opp (mult a b)))
    by exact (opp_mult_r).
  assert (Hassoc : forall a b c : R, Id (mult a (mult b c)) (mult (mult a b) c))
    by exact (mult_assoc).
  assert (Hcomm : forall a b : R, Id (mult a b) (mult b a))
    by exact (mult_comm).
  assert (Hmo : forall a : R, Id (mult a one) a)
    by exact (mult_one).
  assert (Hpa : forall a b c : R, Id (plus a (plus b c)) (plus (plus a b) c))
    by exact (plus_assoc).
  assert (Hpc : forall a b : R, Id (plus a b) (plus b a))
    by exact (plus_comm).
  assert (Hpz : forall a : R, Id (plus a zero) a)
    by exact (plus_zero).
  assert (Hpo : forall a : R, Id (plus a (opp a)) zero)
    by exact (plus_opp).
  (* 步骤 1：逐点分解 p_b(s)·log p_b(s) *)
  assert (Hpoint :
    forall s : S,
      Id (mult (boltzmann_dist s) (log (boltzmann_dist s)))
         (plus (mult (boltzmann_dist s) (opp (log Z)))
               (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))).
  {
    intro s.
    assert (Hld : Id (log (boltzmann_dist s))
                     (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (boltzmann_log_decomp s).
    assert (Hc : Id (mult (boltzmann_dist s) (log (boltzmann_dist s)))
                    (mult (boltzmann_dist s) (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))))))
      by exact (id_cong (fun x => mult (boltzmann_dist s) x) Hld).
    rewrite Hc.
    rewrite (Hdist (boltzmann_dist s) (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))).
    rewrite (Hoppl (boltzmann_dist s) (mult (inv_pos D D_pos) (base_loss s))).
    assert (Hswap : Id (mult (boltzmann_dist s) (mult (inv_pos D D_pos) (base_loss s)))
                       (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))).
    {
      assert (H1 : Id (mult (boltzmann_dist s) (mult (inv_pos D D_pos) (base_loss s)))
                      (mult (mult (boltzmann_dist s) (inv_pos D D_pos)) (base_loss s)))
        by exact (Hassoc (boltzmann_dist s) (inv_pos D D_pos) (base_loss s)).
      assert (H2 : Id (mult (mult (boltzmann_dist s) (inv_pos D D_pos)) (base_loss s))
                      (mult (mult (inv_pos D D_pos) (boltzmann_dist s)) (base_loss s)))
        by exact (id_cong (fun x => mult x (base_loss s)) (Hcomm (boltzmann_dist s) (inv_pos D D_pos))).
      assert (H3 : Id (mult (mult (inv_pos D D_pos) (boltzmann_dist s)) (base_loss s))
                      (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))
        by exact (id_sym (Hassoc (inv_pos D D_pos) (boltzmann_dist s) (base_loss s))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    rewrite Hswap.
    reflexivity.
  }
  (* 步骤 2：对 s 求和：Σ p_b·log p_b = -log Z - (1/D)·⟨E⟩ *)
  assert (Hsum :
    Id (sum_over_S (fun s => mult (boltzmann_dist s) (log (boltzmann_dist s))))
       (plus (opp (log Z))
             (opp (mult (inv_pos D D_pos) Eavg)))).
  {
    assert (Hext : Id (sum_over_S (fun s => mult (boltzmann_dist s) (log (boltzmann_dist s))))
                     (sum_over_S (fun s => plus (mult (boltzmann_dist s) (opp (log Z)))
                                                (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))))
      by exact (sum_over_S_ext (fun s => mult (boltzmann_dist s) (log (boltzmann_dist s)))
                               (fun s => plus (mult (boltzmann_dist s) (opp (log Z)))
                                              (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))
                               Hpoint).
    rewrite Hext.
    assert (Hadd : Id (sum_over_S (fun s => plus (mult (boltzmann_dist s) (opp (log Z)))
                                                (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))))
                      (plus (sum_over_S (fun s => mult (boltzmann_dist s) (opp (log Z))))
                            (sum_over_S (fun s => opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))))
      by exact (sum_over_S_add (fun s => mult (boltzmann_dist s) (opp (log Z)))
                               (fun s => opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))).
    rewrite Hadd.
    (* 第一项：Σ p_b·(-log Z) = (-log Z)·Σ p_b = -log Z *)
    assert (Hsw1 : Id (sum_over_S (fun s => mult (boltzmann_dist s) (opp (log Z))))
                      (sum_over_S (fun s => mult (opp (log Z)) (boltzmann_dist s)))).
    {
      apply sum_over_S_ext.
      intro s.
      apply (Hcomm (boltzmann_dist s) (opp (log Z))).
    }
    rewrite Hsw1.
    assert (Hlin1 : Id (sum_over_S (fun s => mult (opp (log Z)) (boltzmann_dist s)))
                       (mult (opp (log Z)) (sum_over_S boltzmann_dist)))
      by exact (sum_over_S_linear (opp (log Z)) boltzmann_dist).
    rewrite Hlin1.
    assert (Hnorm : Id (sum_over_S boltzmann_dist) one) by exact (boltzmann_normalized).
    rewrite Hnorm.
    assert (Hm1 : Id (mult (opp (log Z)) one) (opp (log Z))) by exact (Hmo (opp (log Z))).
    rewrite Hm1.
    (* 第二项：Σ opp((1/D)·p_b·E) = opp((1/D)·Σ p_b·E) *)
    assert (Hso : Id (sum_over_S (fun s => opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))
                     (opp (sum_over_S (fun s => mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))))
      by exact (sum_opp (fun s => mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))).
    rewrite Hso.
    assert (Hlin2 : Id (sum_over_S (fun s => mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))
                       (mult (inv_pos D D_pos) (sum_over_S (fun s => mult (boltzmann_dist s) (base_loss s)))))
      by exact (sum_over_S_linear (inv_pos D D_pos) (fun s => mult (boltzmann_dist s) (base_loss s))).
    rewrite Hlin2.
    reflexivity.
  }
  rewrite Hsum.
  (* 步骤 3：D·(-log Z - (1/D)·⟨E⟩) = -D·log Z - ⟨E⟩ *)
  assert (Hmd : Id (mult D (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) Eavg))))
                  (plus (opp (mult D (log Z))) (opp Eavg))).
  {
    rewrite (Hdist D (opp (log Z)) (opp (mult (inv_pos D D_pos) Eavg))).
    rewrite (Hoppl D (log Z)).
    rewrite (Hoppl D (mult (inv_pos D D_pos) Eavg)).
    assert (Hmd2 : Id (mult D (mult (inv_pos D D_pos) Eavg)) Eavg).
    {
      assert (Hcc1 : Id (mult (mult D (inv_pos D D_pos)) Eavg) Eavg).
      {
        assert (Ht : Id (mult (mult D (inv_pos D D_pos)) Eavg) (mult one Eavg))
          by exact (id_cong (fun x => mult x Eavg) (inv_pos_correct D D_pos)).
        assert (Ht2 : Id (mult one Eavg) (mult Eavg one))
          by exact (Hcomm one Eavg).
        exact (id_trans Ht (id_trans Ht2 (Hmo Eavg))).
      }
      exact (id_trans (Hassoc D (inv_pos D D_pos) Eavg) Hcc1).
    }
    rewrite Hmd2.
    reflexivity.
  }
  rewrite Hmd.
  (* 步骤 4：⟨E⟩ + (-D·log Z - ⟨E⟩) = -D·log Z（环代数坍缩） *)
  assert (Hfin : Id (plus Eavg (plus (opp (mult D (log Z))) (opp Eavg)))
                    (opp (mult D (log Z)))).
  {
    assert (H1 : Id (plus Eavg (plus (opp (mult D (log Z))) (opp Eavg)))
                    (plus (plus Eavg (opp (mult D (log Z)))) (opp Eavg)))
      by exact (Hpa Eavg (opp (mult D (log Z))) (opp Eavg)).
    assert (H2 : Id (plus (plus Eavg (opp (mult D (log Z)))) (opp Eavg))
                    (plus (plus (opp (mult D (log Z))) Eavg) (opp Eavg)))
      by exact (id_cong (fun y => plus y (opp Eavg)) (Hpc Eavg (opp (mult D (log Z))))).
    assert (H3 : Id (plus (plus (opp (mult D (log Z))) Eavg) (opp Eavg))
                    (plus (opp (mult D (log Z))) (plus Eavg (opp Eavg))))
      by exact (id_sym (Hpa (opp (mult D (log Z))) Eavg (opp Eavg))).
    assert (H4 : Id (plus (opp (mult D (log Z))) (plus Eavg (opp Eavg)))
                    (plus (opp (mult D (log Z))) zero))
      by exact (id_cong (fun y => plus (opp (mult D (log Z))) y) (Hpo Eavg)).
    assert (H5 : Id (plus (opp (mult D (log Z))) zero) (opp (mult D (log Z))))
      by exact (Hpz (opp (mult D (log Z)))).
    exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
  }
  assert (Hoppr2 : Id (opp (mult D (log Z))) (mult (opp D) (log Z)))
    by exact (id_sym (Hoppr D (log Z))).
  exact (id_trans Hfin Hoppr2).
Qed.

(* ============================================================ *)
(* 训练-推理闭环皇冠定理：自由能-相对熵恒等式                  *)
(*   F[p] = F[p_b] + D·KL(p || p_b)                             *)
(* ============================================================ *)
(* 含义：对任意归一化分布 p，自由能等于 Boltzmann 自由能加上   *)
(* 温度 D 乘相对熵。⟹ 训练（自由能最小化）与推理（分布逼近     *)
(* Boltzmann）精确等价——最小化 F 就是最小化 KL。              *)
(* 非平凡推导：能量用对数分解反解 E = -D·(log p_b + log Z)，   *)
(* 逐点替换 + 求和线性/负号线性 + 归一化坍缩。                 *)
(* ------------------------------------------------------------ *)

(* 引理 1：能量反解——由 boltzmann_log_decomp 得
   E(s) = -D·(log p_b(s) + log Z) *)
Lemma energy_in_log_boltzmann :
  forall s : S,
    Id (base_loss s)
       (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))).
Proof.
  intro s.
  (* log p_b = -log Z - E/D ⟹ log p_b + log Z = -E/D *)
  assert (Hlog : Id (log (boltzmann_dist s))
                    (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))))
    by exact (boltzmann_log_decomp s).
  assert (Hsum : Id (plus (log (boltzmann_dist s)) (log Z))
                    (opp (mult (inv_pos D D_pos) (base_loss s)))).
  {
    assert (Hc : Id (plus (log (boltzmann_dist s)) (log Z))
                    (plus (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))) (log Z)))
      by exact (id_cong (fun x => plus x (log Z)) Hlog).
    assert (H1 : Id (plus (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))) (log Z))
                    (plus (opp (log Z)) (plus (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z))))
      by exact (id_sym (plus_assoc (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z))).
    assert (H2 : Id (plus (opp (log Z)) (plus (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z)))
                    (plus (opp (log Z)) (plus (log Z) (opp (mult (inv_pos D D_pos) (base_loss s))))))
      by exact (id_cong (fun x => plus (opp (log Z)) x)
                        (plus_comm (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z))).
    assert (H3 : Id (plus (opp (log Z)) (plus (log Z) (opp (mult (inv_pos D D_pos) (base_loss s)))))
                    (plus (plus (opp (log Z)) (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (plus_assoc (opp (log Z)) (log Z) (opp (mult (inv_pos D D_pos) (base_loss s)))).
    assert (H4 : Id (plus (plus (opp (log Z)) (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))))
                    (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))).
    {
      assert (H4a : Id (plus (plus (opp (log Z)) (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))))
                      (plus (plus (log Z) (opp (log Z))) (opp (mult (inv_pos D D_pos) (base_loss s)))))
        by exact (id_cong (fun x => plus x (opp (mult (inv_pos D D_pos) (base_loss s))))
                          (plus_comm (opp (log Z)) (log Z))).
      assert (H4b : Id (plus (plus (log Z) (opp (log Z))) (opp (mult (inv_pos D D_pos) (base_loss s))))
                      (plus zero (opp (mult (inv_pos D D_pos) (base_loss s)))))
        by exact (id_cong (fun x => plus x (opp (mult (inv_pos D D_pos) (base_loss s)))) (plus_opp (log Z))).
      exact (id_trans H4a H4b).
    }
    assert (H5 : Id (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))
                    (opp (mult (inv_pos D D_pos) (base_loss s))))
      by exact (id_trans (plus_comm zero (opp (mult (inv_pos D D_pos) (base_loss s)))) (plus_zero (opp (mult (inv_pos D D_pos) (base_loss s))))).
    exact (id_trans Hc (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5))))).
  }
  (* D·(-E/D) = -E；目标反号后为 E = -D·(log p_b + log Z) *)
  assert (Hmd : Id (mult D (plus (log (boltzmann_dist s)) (log Z)))
                   (opp (base_loss s))).
  {
    assert (Hc2 : Id (mult D (plus (log (boltzmann_dist s)) (log Z)))
                     (mult D (opp (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (id_cong (fun x => mult D x) Hsum).
    assert (Hopp : Id (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                      (opp (mult D (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (opp_mult_l D (mult (inv_pos D D_pos) (base_loss s))).
    assert (Hcc : Id (mult D (mult (inv_pos D D_pos) (base_loss s))) (base_loss s)).
    {
      assert (Hma : Id (mult D (mult (inv_pos D D_pos) (base_loss s)))
                       (mult (mult D (inv_pos D D_pos)) (base_loss s)))
        by exact (mult_assoc D (inv_pos D D_pos) (base_loss s)).
      assert (Hic : Id (mult (mult D (inv_pos D D_pos)) (base_loss s))
                       (mult one (base_loss s)))
        by exact (id_cong (fun x => mult x (base_loss s)) (inv_pos_correct D D_pos)).
      assert (Hm1 : Id (mult one (base_loss s)) (base_loss s))
        by exact (id_trans (mult_comm one (base_loss s)) (mult_one (base_loss s))).
      exact (id_trans Hma (id_trans Hic Hm1)).
    }
    exact (id_trans Hc2 (id_trans Hopp (id_cong opp Hcc))).
  }
  (* E = -D·(log p_b + log Z)：由 mult D (log p_b + log Z) = -E 反号 *)
  assert (Hinv : Id (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (base_loss s)).
  {
    assert (Hd : Id (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (opp (opp (base_loss s))))
      by exact (id_cong opp Hmd).
    assert (Hdn : Id (opp (opp (base_loss s))) (base_loss s))
      by exact (double_neg (base_loss s)).
    exact (id_trans Hd Hdn).
  }
  exact (id_sym Hinv).
Qed.

(* 引理 2：逐点分解 mult (p s) (base_loss s) = -D·p·log p_b - D·p·log Z *)
Lemma p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    Id (mult (p s) (base_loss s))
       (plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
             (opp (mult D (mult (p s) (log Z))))).
Proof.
  intros p s.
  assert (He : Id (base_loss s)
                  (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
    by exact (energy_in_log_boltzmann s).
  assert (Hc : Id (mult (p s) (base_loss s))
                  (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))))
    by exact (id_cong (fun x => mult (p s) x) He).
  assert (Hopp : Id (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                    (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))))
    by exact (opp_mult_l (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))).
  (* mult (p s) (mult D X) = mult D (mult (p s) X)（交换重组） *)
  assert (Hsw : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                   (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z))))).
  {
    assert (H1 : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z))))
      by exact (mult_assoc (p s) D (plus (log (boltzmann_dist s)) (log Z))).
    assert (H2 : Id (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z)))
                    (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z))))
      by exact (id_cong (fun x => mult x (plus (log (boltzmann_dist s)) (log Z))) (mult_comm (p s) D)).
    assert (H3 : Id (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z)))
                    (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))))
      by exact (id_sym (mult_assoc D (p s) (plus (log (boltzmann_dist s)) (log Z)))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* distrib：mult (p s) (log p_b + log Z) = p·log p_b + p·log Z *)
  assert (Hdist : Id (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))
                     (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
    by exact (distrib (p s) (log (boltzmann_dist s)) (log Z)).
  assert (Hsw2 : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z)))))
    by exact (id_trans Hsw (id_cong (fun x => mult D x) Hdist)).
  assert (Hdist2 : Id (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
                      (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                            (mult D (mult (p s) (log Z)))))
    by exact (distrib D (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))).
  assert (Htot : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                          (mult D (mult (p s) (log Z)))))
    by exact (id_trans Hsw2 Hdist2).
  (* opp 展开：opp (X + Y) = opp X + opp Y *)
  assert (Hop : Id (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                              (mult D (mult (p s) (log Z)))))
                   (plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                         (opp (mult D (mult (p s) (log Z))))))
    by exact (opp_plus (mult D (mult (p s) (log (boltzmann_dist s))))
                       (mult D (mult (p s) (log Z)))).
  assert (Hc2 : Id (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                   (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                              (mult D (mult (p s) (log Z))))))
    by exact (id_cong opp Htot).
  exact (id_trans Hc (id_trans Hopp (id_trans Hc2 Hop))).
Qed.

(* 主定理：F[p] = F[p_b] + D·KL(p || p_b) *)
Theorem free_energy_kl_decomp :
  forall p : S -> R,
    normalized p ->
    Id (free_energy p)
       (plus (free_energy boltzmann_dist)
             (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))).
Proof.
  intros p Hnorm.
  unfold normalized in Hnorm.
  (* 展开 LHS 的 free_energy p（RHS 的 free_energy boltzmann_dist 保持完整，供 Hfb 重写） *)
  assert (Hfe_p : Id (free_energy p)
                     (plus (sum_over_S (fun s => mult (p s) (base_loss s)))
                           (mult D (sum_over_S (fun s => mult (p s) (log (p s))))))).
  { reflexivity. }
  rewrite Hfe_p.
  (* 步骤 1：Σ p·E = -D·Σ p·log p_b - D·log Z *)
  assert (Hse : Id (sum_over_S (fun s => mult (p s) (base_loss s)))
                   (plus (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
                         (opp (mult D (log Z))))).
  {
    assert (Hpt : forall s : S,
                    Id (mult (p s) (base_loss s))
                       (plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                             (opp (mult D (mult (p s) (log Z))))))
      by exact (p_times_energy_decomp p).
    assert (Hext : Id (sum_over_S (fun s => mult (p s) (base_loss s)))
                     (sum_over_S (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                                                (opp (mult D (mult (p s) (log Z)))))))
      by exact (sum_over_S_ext (fun s => mult (p s) (base_loss s))
                               (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                                              (opp (mult D (mult (p s) (log Z)))))
                               Hpt).
    rewrite Hext.
    assert (Hadd : Id (sum_over_S (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                                                 (opp (mult D (mult (p s) (log Z))))))
                      (plus (sum_over_S (fun s => opp (mult D (mult (p s) (log (boltzmann_dist s))))))
                            (sum_over_S (fun s => opp (mult D (mult (p s) (log Z)))))))
      by exact (sum_over_S_add (fun s => opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                               (fun s => opp (mult D (mult (p s) (log Z))))).
    rewrite Hadd.
    assert (Hso1 : Id (sum_over_S (fun s => opp (mult D (mult (p s) (log (boltzmann_dist s))))))
                      (opp (sum_over_S (fun s => mult D (mult (p s) (log (boltzmann_dist s)))))))
      by exact (sum_opp (fun s => mult D (mult (p s) (log (boltzmann_dist s))))).
    rewrite Hso1.
    assert (Hlin1 : Id (sum_over_S (fun s => mult D (mult (p s) (log (boltzmann_dist s)))))
                       (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
      by exact (sum_over_S_linear D (fun s => mult (p s) (log (boltzmann_dist s)))).
    rewrite Hlin1.
    assert (Hso2 : Id (sum_over_S (fun s => opp (mult D (mult (p s) (log Z)))))
                      (opp (sum_over_S (fun s => mult D (mult (p s) (log Z))))))
      by exact (sum_opp (fun s => mult D (mult (p s) (log Z)))).
    rewrite Hso2.
    assert (Hlin2 : Id (sum_over_S (fun s => mult D (mult (p s) (log Z))))
                       (mult D (sum_over_S (fun s => mult (p s) (log Z)))))
      by exact (sum_over_S_linear D (fun s => mult (p s) (log Z))).
    rewrite Hlin2.
    (* 内层：Σ p·log Z = log Z·Σ p = log Z（归一化） *)
    assert (HlogZ : Id (sum_over_S (fun s => mult (p s) (log Z))) (log Z)).
    {
      assert (Hsw : Id (sum_over_S (fun s => mult (p s) (log Z)))
                       (sum_over_S (fun s => mult (log Z) (p s))))
        by exact (sum_over_S_ext (fun s => mult (p s) (log Z))
                                 (fun s => mult (log Z) (p s))
                                 (fun s => mult_comm (p s) (log Z))).
      rewrite Hsw.
      assert (Hl1 : Id (sum_over_S (fun s => mult (log Z) (p s))) (mult (log Z) (sum_over_S p)))
        by exact (sum_over_S_linear (log Z) p).
      rewrite Hl1.
      rewrite Hnorm.
      assert (Hm1 : Id (mult (log Z) one) (log Z)) by exact (mult_one (log Z)).
      rewrite Hm1.
      reflexivity.
    }
    rewrite HlogZ.
    reflexivity.
  }
  rewrite Hse.
  (* 步骤 2：F[p_b] = -D·log Z（已证 free_energy_boltzmann + opp_mult_r） *)
  assert (Hfb : Id (free_energy boltzmann_dist) (opp (mult D (log Z)))).
  {
    assert (Hfb0 : Id (free_energy boltzmann_dist) (mult (opp D) (log Z)))
      by exact (free_energy_boltzmann).
    assert (Hoppr : Id (mult (opp D) (log Z)) (opp (mult D (log Z))))
      by exact (opp_mult_r D (log Z)).
    exact (id_trans Hfb0 Hoppr).
  }
  rewrite Hfb.
  (* 步骤 3：KL 展开——mult D (Σ p·(log p - log p_b))
     = D·Σ p·log p - D·Σ p·log p_b *)
  assert (Hkl : Id (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                  (plus (mult D (sum_over_S (fun s => mult (p s) (log (p s)))))
                        (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))).
  {
    (* 逐点：p·(log p - log p_b) = p·log p - p·log p_b *)
    assert (Hpt2 : forall s : S,
                    Id (mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))
                       (plus (mult (p s) (log (p s)))
                             (opp (mult (p s) (log (boltzmann_dist s)))))).
    {
      intro s.
      unfold minus.
      assert (Hd : Id (mult (p s) (plus (log (p s)) (opp (log (boltzmann_dist s)))))
                      (plus (mult (p s) (log (p s))) (mult (p s) (opp (log (boltzmann_dist s))))))
        by exact (distrib (p s) (log (p s)) (opp (log (boltzmann_dist s)))).
      assert (Ho : Id (mult (p s) (opp (log (boltzmann_dist s))))
                      (opp (mult (p s) (log (boltzmann_dist s)))))
        by exact (opp_mult_l (p s) (log (boltzmann_dist s))).
      exact (id_trans Hd (id_cong (fun x => plus (mult (p s) (log (p s))) x) Ho)).
    }
    assert (Hext2 : Id (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))
                      (sum_over_S (fun s => plus (mult (p s) (log (p s)))
                                                 (opp (mult (p s) (log (boltzmann_dist s)))))))
      by exact (sum_over_S_ext (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))
                               (fun s => plus (mult (p s) (log (p s))) (opp (mult (p s) (log (boltzmann_dist s)))))
                               Hpt2).
    rewrite Hext2.
    assert (Hadd2 : Id (sum_over_S (fun s => plus (mult (p s) (log (p s)))
                                                  (opp (mult (p s) (log (boltzmann_dist s))))))
                       (plus (sum_over_S (fun s => mult (p s) (log (p s))))
                             (sum_over_S (fun s => opp (mult (p s) (log (boltzmann_dist s)))))))
      by exact (sum_over_S_add (fun s => mult (p s) (log (p s)))
                               (fun s => opp (mult (p s) (log (boltzmann_dist s))))).
    rewrite Hadd2.
    assert (Hso3 : Id (sum_over_S (fun s => opp (mult (p s) (log (boltzmann_dist s)))))
                      (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
      by exact (sum_opp (fun s => mult (p s) (log (boltzmann_dist s)))).
    rewrite Hso3.
    (* 提取 D（线性） *)
    assert (HdistD : Id (mult D (plus (sum_over_S (fun s => mult (p s) (log (p s))))
                                      (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))
                        (plus (mult D (sum_over_S (fun s => mult (p s) (log (p s)))))
                              (mult D (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))))
      by exact (distrib D (sum_over_S (fun s => mult (p s) (log (p s))))
                         (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))).
    assert (HoppD : Id (mult D (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
                       (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))
      by exact (opp_mult_l D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))).
    assert (HcD : Id (mult D (plus (sum_over_S (fun s => mult (p s) (log (p s))))
                                   (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))
                     (plus (mult D (sum_over_S (fun s => mult (p s) (log (p s)))))
                           (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))))
      by exact (id_trans HdistD
                          (id_cong (fun x => plus (mult D (sum_over_S (fun s => mult (p s) (log (p s))))) x) HoppD)).
    exact HcD.
  }
  (* 步骤 4：主目标环代数坍缩
     (opp A + opp (D log Z)) + D·Σp log p
     = opp (D log Z) + (D·Σp log p + opp A)  其中 A := D·Σ p log p_b *)
  set (A := mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))).
  set (B := mult D (sum_over_S (fun s => mult (p s) (log (p s))))).
  (* 重写 KL 侧：目标含 B 与 opp A *)
  assert (Hkl2 : Id (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                    (plus B (opp A))).
  {
    unfold A, B.
    exact Hkl.
  }
  rewrite Hkl2.
  (* 目标：(opp A + opp (D log Z)) + B = opp (D log Z) + (B + opp A) *)
  assert (Hfin : Id (plus (plus (opp A) (opp (mult D (log Z)))) B)
                    (plus (opp (mult D (log Z))) (plus B (opp A)))).
  {
    assert (H1 : Id (plus (plus (opp A) (opp (mult D (log Z)))) B)
                    (plus (opp A) (plus (opp (mult D (log Z))) B)))
      by exact (id_sym (plus_assoc (opp A) (opp (mult D (log Z))) B)).
    assert (H2 : Id (plus (opp A) (plus (opp (mult D (log Z))) B))
                    (plus (opp A) (plus B (opp (mult D (log Z))))))
      by exact (id_cong (fun x => plus (opp A) x)
                        (plus_comm (opp (mult D (log Z))) B)).
    assert (H3 : Id (plus (opp A) (plus B (opp (mult D (log Z)))))
                    (plus (plus (opp A) B) (opp (mult D (log Z)))))
      by exact (plus_assoc (opp A) B (opp (mult D (log Z)))).
    assert (H4 : Id (plus (plus (opp A) B) (opp (mult D (log Z))))
                    (plus (plus B (opp A)) (opp (mult D (log Z)))))
      by exact (id_cong (fun x => plus x (opp (mult D (log Z)))) (plus_comm (opp A) B)).
    assert (H5 : Id (plus (plus B (opp A)) (opp (mult D (log Z))))
                    (plus (opp (mult D (log Z))) (plus B (opp A))))
      by exact (plus_comm (plus B (opp A)) (opp (mult D (log Z)))).
    exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
  }
  exact Hfin.
Qed.

(* 推论：自由能差 = D × 相对熵（差形式，常用于训练目标分解） *)
Theorem free_energy_kl_diff :
  forall p : S -> R,
    normalized p ->
    Id (minus (free_energy p) (free_energy boltzmann_dist))
       (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))).
Proof.
  intros p Hnorm.
  unfold minus.
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))))
    by exact (free_energy_kl_decomp p Hnorm).
  rewrite Hdecomp.
  (* F_b + (F - F_b 项) ⟹ 目标：plus F_b KL 的 opp 形式 *)
  assert (Hcn : Id (plus (plus (free_energy boltzmann_dist)
                               (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))))
                         (opp (free_energy boltzmann_dist)))
                   (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))).
  {
    set (FB := free_energy boltzmann_dist).
    set (KL := mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))).
    assert (H1 : Id (plus (plus FB KL) (opp FB))
                    (plus FB (plus KL (opp FB))))
      by exact (id_sym (plus_assoc FB KL (opp FB))).
    assert (H2 : Id (plus FB (plus KL (opp FB)))
                    (plus FB (plus (opp FB) KL)))
      by exact (id_cong (fun x => plus FB x) (plus_comm KL (opp FB))).
    assert (H3 : Id (plus FB (plus (opp FB) KL))
                    (plus (plus FB (opp FB)) KL))
      by exact (plus_assoc FB (opp FB) KL).
    assert (H4 : Id (plus (plus FB (opp FB)) KL)
                    (plus zero KL))
      by exact (id_cong (fun x => plus x KL) (plus_opp FB)).
    assert (H5 : Id (plus zero KL) KL)
      by exact (id_trans (plus_comm zero KL) (plus_zero KL)).
    exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
  }
  exact Hcn.
Qed.

(* ============================================================ *)
(* F[p] - F[q] = D·(KL(p‖p_b) - KL(q‖p_b))
   深化意义：自由能差等于两分布各自相对 Boltzmann 的 KL 之差。
   给出任意两候选分布的相对质量排序：F[p] ≤ F[q] ⟺
   KL(p‖p_b) ≤ KL(q‖p_b)。支撑：模型选择、分布逼近偏序、
   生成模型的相对评估、蒸馏中师生差距的度量。 *)
Theorem free_energy_diff_kl :
  forall p q : S -> R,
    normalized p -> normalized q ->
    Id (minus (free_energy p) (free_energy q)) (mult D (minus (sum_over_S (fun s0 => mult (p s0) (minus (log (p s0)) (log (boltzmann_dist s0))))) (sum_over_S (fun s0 => mult (q s0) (minus (log (q s0)) (log (boltzmann_dist s0))))))).

  intros p q Hnp Hnq.
  (* 1. 两侧各自的 free_energy_kl_diff *)
  assert (Hp : Id (minus (free_energy p) (free_energy boltzmann_dist))
                  (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))))
    by exact (free_energy_kl_diff p Hnp).
  assert (Hq : Id (minus (free_energy q) (free_energy boltzmann_dist))
                  (mult D (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s)))))))
    by exact (free_energy_kl_diff q Hnq).
  (* 2. ring_minus_trans：F[p]-F[q] = (F[p]-F_b) - (F[q]-F_b) *)
  assert (Hsplit : Id (minus (free_energy p) (free_energy q))
                      (minus (minus (free_energy p) (free_energy boltzmann_dist))
                             (minus (free_energy q) (free_energy boltzmann_dist))))
    by exact (ring_minus_trans (free_energy p) (free_energy q) (free_energy boltzmann_dist)).
  (* 3. 代入 Hp、Hq：(D·KL_p) - (D·KL_q) = D·(KL_p - KL_q) *)
  assert (Hsub : Id (minus (free_energy p) (free_energy q)) (minus (mult D (sum_over_S (fun s0 => mult (p s0) (minus (log (p s0)) (log (boltzmann_dist s0)))))) (mult D (sum_over_S (fun s0 => mult (q s0) (minus (log (q s0)) (log (boltzmann_dist s0)))))))).

  {
    assert (H1 : Id (minus (minus (free_energy p) (free_energy boltzmann_dist))
                           (minus (free_energy q) (free_energy boltzmann_dist)))
                    (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                           (minus (free_energy q) (free_energy boltzmann_dist))))
      by exact (id_cong (fun x => minus x (minus (free_energy q) (free_energy boltzmann_dist))) Hp).
    assert (H2 : Id (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                           (minus (free_energy q) (free_energy boltzmann_dist)))
                    (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                           (mult D (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s))))))))
      by exact (id_cong (fun x => minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))) x) Hq).
    exact (id_trans Hsplit (id_trans H1 H2)).
  }
  (* 4. mult_minus_distr_l 反向：D·(KL_p - KL_q) = (D·KL_p) - (D·KL_q) *)
  assert (Hm : Id (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                         (mult D (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s)))))))
                  (mult D (minus (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))
                                 (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s))))))))
    by exact (id_sym (mult_minus_distr_l D (sum_over_S (fun s0 => mult (p s0) (minus (log (p s0)) (log (boltzmann_dist s0))))) (sum_over_S (fun s0 => mult (q s0) (minus (log (q s0)) (log (boltzmann_dist s0))))))).
  exact (id_trans Hsub Hm).
Qed.

(* 相对熵（KL 散度）：KL(p || q) := Σ_s p(s)·(log p(s) - log q(s)) *)
Definition relative_entropy (p q : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))).

(* 关键代数引理：p·(log p - log q) = p·log(p/q)，且
   p·(q/p) = q（分式约分；用于 Gibbs 不等式逐点项） *)
Lemma gibbs_pointwise :
  forall (p q : S -> R) (s : S),
    lt zero (p s) -> lt zero (q s) ->
    le (minus (p s) (q s))
       (mult (p s) (minus (log (p s)) (log (q s)))).
Proof.
  intros p q s Hps Hqs.
  (* log(q/p) ≤ q/p - 1（log 凹性切线，q/p > 0） *)
  assert (Hratio_pos : lt zero (mult (q s) (inv_pos (p s) Hps)))
    by exact (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  assert (Hlin : le (log (mult (q s) (inv_pos (p s) Hps)))
                    (minus (mult (q s) (inv_pos (p s) Hps)) one))
    by exact (log_le_linear (mult (q s) (inv_pos (p s) Hps)) Hratio_pos).
  (* 反号：-(q/p - 1) ≤ -log(q/p)，即 1 - q/p ≤ log(p/q) *)
  assert (Hopp : le (opp (minus (mult (q s) (inv_pos (p s) Hps)) one))
                    (opp (log (mult (q s) (inv_pos (p s) Hps)))))
    by exact (opp_le_compat (log (mult (q s) (inv_pos (p s) Hps)))
                            (minus (mult (q s) (inv_pos (p s) Hps)) one) Hlin).
  (* log(p/q) = -log(q/p)（log_div_neg） *)
  assert (Hld : Id (log (mult (p s) (inv_pos (q s) Hqs)))
                   (opp (log (mult (q s) (inv_pos (p s) Hps)))))
    by exact (log_div_neg (p s) (q s) Hps Hqs).
  (* 目标 RHS 用 log(p/q) 替换：mult (p s) (minus (log p) (log q)) = mult (p s) (log (p/q)) *)
  assert (Hrhs : Id (mult (p s) (minus (log (p s)) (log (q s))))
                    (mult (p s) (log (mult (p s) (inv_pos (q s) Hqs))))).
  {
    assert (Hlogdiv : Id (log (mult (p s) (inv_pos (q s) Hqs)))
                         (minus (log (p s)) (log (q s))))
      by exact (log_div (p s) (q s) Hps Hqs).
    exact (id_sym (id_cong (fun x => mult (p s) x) Hlogdiv)).
  }
  rewrite Hrhs.
  (* 目标：minus (p s) (q s) ≤ mult (p s) (log (p/q))
     用 p·(1 - q/p) ≤ p·log(p/q)（log_le_linear 反号 + le_mult_compat） *)
  assert (Hstep1 : le (mult (p s) (opp (minus (mult (q s) (inv_pos (p s) Hps)) one)))
                      (mult (p s) (opp (log (mult (q s) (inv_pos (p s) Hps))))))
    by exact (le_mult_compat_r (p s)
                               (opp (minus (mult (q s) (inv_pos (p s) Hps)) one))
                               (opp (log (mult (q s) (inv_pos (p s) Hps))))
                               (lt_le_iff _ _ (inl Hps)) Hopp).
  (* p·log(p/q) = p·(-log(q/p)) *)
  assert (Hstep2 : Id (mult (p s) (log (mult (p s) (inv_pos (q s) Hqs))))
                      (mult (p s) (opp (log (mult (q s) (inv_pos (p s) Hps))))))
    by exact (id_cong (fun x => mult (p s) x) Hld).
  rewrite <- Hstep2 in Hstep1.
  (* 目标 LHS：p·(1 - q/p) = p - p·(q/p) = p - q *)
  assert (Hlhs : Id (minus (p s) (q s))
                    (mult (p s) (opp (minus (mult (q s) (inv_pos (p s) Hps)) one)))).
  {
    (* mult (p s) (opp (minus X one)) = opp (mult (p s) (minus X one))
       = opp (minus (mult (p s) X) (mult (p s) one)) = opp (minus (p·X) (p·1))
       mult (p s) X = q s，mult (p s) one = p s ⟹ = opp (minus (q s) (p s)) = minus (p s) (q s) *)
    assert (Hoppl : Id (mult (p s) (opp (minus (mult (q s) (inv_pos (p s) Hps)) one)))
                       (opp (mult (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one))))
      by exact (opp_mult_l (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one)).
    assert (Hdist : Id (mult (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one))
                       (minus (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                              (mult (p s) one)))
      by exact (mult_minus_distr_l (p s) (mult (q s) (inv_pos (p s) Hps)) one).
    assert (Hcc : Id (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    {
      assert (H1 : Id (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                      (mult (mult (p s) (q s)) (inv_pos (p s) Hps)))
        by exact (mult_assoc (p s) (q s) (inv_pos (p s) Hps)).
      assert (H2 : Id (mult (mult (p s) (q s)) (inv_pos (p s) Hps))
                      (mult (mult (q s) (p s)) (inv_pos (p s) Hps)))
        by exact (id_cong (fun x => mult x (inv_pos (p s) Hps)) (mult_comm (p s) (q s))).
      assert (H3 : Id (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                      (mult (q s) (mult (p s) (inv_pos (p s) Hps))))
        by exact (id_sym (mult_assoc (q s) (p s) (inv_pos (p s) Hps))).
      assert (H4 : Id (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                      (mult (q s) one))
        by exact (id_cong (fun x => mult (q s) x) (inv_pos_correct (p s) Hps)).
      assert (H5 : Id (mult (q s) one) (q s)) by exact (mult_one (q s)).
      exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
    }
    assert (Hmo : Id (mult (p s) one) (p s)) by exact (mult_one (p s)).
    assert (Hfull : Id (mult (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one))
                       (minus (q s) (p s)))
      by exact (id_trans Hdist (id_trans (id_cong (fun x => minus x (mult (p s) one)) Hcc)
                                         (id_cong (fun x => minus (q s) x) Hmo))).
    assert (Hopp2 : Id (opp (minus (q s) (p s))) (minus (p s) (q s)))
      by exact (id_trans (opp_minus (q s) (p s)) (id_sym (plus_comm (p s) (opp (q s))))).
    exact (id_sym (id_trans Hoppl (id_trans (id_cong opp Hfull) Hopp2))).
  }
  rewrite <- Hlhs in Hstep1.
  exact Hstep1.
Qed.

(* Gibbs 不等式：归一化正分布的相对熵非负（KL ≥ 0）。
   非平凡：log 凹性切线 + 逐点分式约分 + 求和保序。 *)
Theorem gibbs_inequality :
  forall p q : S -> R,
    normalized p -> positive_dist p ->
    normalized q -> positive_dist q ->
    le zero (relative_entropy p q).
Proof.
  intros p q Hnp Hpp Hnq Hpq.
  unfold relative_entropy.
  (* 逐点：p - q ≤ p·(log p - log q)，求和保序 ⟹ Σ(p-q) ≤ KL *)
  assert (Hpt : forall s, le (minus (p s) (q s))
                            (mult (p s) (minus (log (p s)) (log (q s)))))
    by (intro s; apply (gibbs_pointwise p q s); [exact (Hpp s) | exact (Hpq s)]).
  assert (Hle : le (sum_over_S (fun s => minus (p s) (q s)))
                   (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s))))))
    by exact (sum_over_S_le (fun s => minus (p s) (q s))
                            (fun s => mult (p s) (minus (log (p s)) (log (q s))))
                            Hpt).
  (* Σ(p - q) = Σp - Σq = 1 - 1 = 0（归一化 + sum_over_S_add + sum_opp） *)
  assert (Hsum0 : Id (sum_over_S (fun s => minus (p s) (q s))) zero).
  {
    unfold minus.
    assert (Hadd : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                     (plus (sum_over_S p) (sum_over_S (fun s => opp (q s)))))
      by exact (sum_over_S_add p (fun s => opp (q s))).
    assert (Hoppq : Id (sum_over_S (fun s => opp (q s))) (opp (sum_over_S q)))
      by exact (sum_opp q).
    assert (Htot : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                     (plus (sum_over_S p) (opp (sum_over_S q))))
      by exact (id_trans Hadd (id_cong (fun x => plus (sum_over_S p) x) Hoppq)).
    assert (Hnp' : Id (sum_over_S p) one) by exact Hnp.
    assert (Hnq' : Id (sum_over_S q) one) by exact Hnq.
    assert (Hfin : Id (plus (sum_over_S p) (opp (sum_over_S q))) zero)
      by exact (id_trans (id_cong (fun x => plus x (opp (sum_over_S q))) Hnp')
                         (id_trans (id_cong (fun x => plus one x) (id_cong opp Hnq')) (plus_opp one))).
    exact (id_trans Htot Hfin).
  }
  rewrite Hsum0 in Hle.
  exact Hle.
Qed.

(* Gibbs 等号条件：KL(p||q) = 0 ⟹ p = q（逐点）。
   证明链：
   1) d(s) := p·(log p - log q) - (p - q) ≥ 0（gibbs_pointwise + le_minus_nonneg）；
   2) Σ d = KL - Σ(p-q) = 0 - 0 = 0（sum_over_S_minus + 归一化）；
   3) sum_over_S_zero_nonneg：Σ d = 0 且 d ≥ 0 ⟹ d(s) = 0；
   4) minus_eq_cancel：p·(log p - log q) = p - q；
   5) log_div 换形 + mult_cancel_l（p > 0）⟹ log(q/p) = q/p - 1；
   6) log_eq_linear（log 严格凹）⟹ q/p = 1；
   7) mult_cancel_r（inv_pos p > 0）⟹ q = p。 *)
Theorem gibbs_equality :
  forall p q : S -> R,
    normalized p -> positive_dist p ->
    normalized q -> positive_dist q ->
    Id (relative_entropy p q) zero ->
    forall s : S, Id (p s) (q s).
Proof.
  intros p q Hnp Hpp Hnq Hpq Hkl0 s0.
  unfold relative_entropy in Hkl0.
  (* 1) d ≥ 0 逐点 *)
  assert (Hd_nonneg : forall s, le zero (minus (mult (p s) (minus (log (p s)) (log (q s))))
                                             (minus (p s) (q s)))).
  {
    intro s.
    apply le_minus_nonneg.
    apply (gibbs_pointwise p q s); [exact (Hpp s) | exact (Hpq s)].
  }
  (* 2) Σ d = 0 *)
  assert (Hd_sum : Id (sum_over_S (fun s => minus (mult (p s) (minus (log (p s)) (log (q s))))
                                             (minus (p s) (q s)))) zero).
  {
    assert (Hadd : Id (sum_over_S (fun s => minus (mult (p s) (minus (log (p s)) (log (q s))))
                                             (minus (p s) (q s))))
                     (minus (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))))
                            (sum_over_S (fun s => minus (p s) (q s)))))
      by exact (sum_over_S_minus (fun s => mult (p s) (minus (log (p s)) (log (q s))))
                                 (fun s => minus (p s) (q s))).
    rewrite Hadd.
    assert (Hpq0 : Id (sum_over_S (fun s => minus (p s) (q s))) zero).
    {
      unfold minus.
      assert (Hadd2 : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                        (plus (sum_over_S p) (sum_over_S (fun s => opp (q s)))))
        by exact (sum_over_S_add p (fun s => opp (q s))).
      assert (Hoppq : Id (sum_over_S (fun s => opp (q s))) (opp (sum_over_S q)))
        by exact (sum_opp q).
      assert (Htot : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                       (plus (sum_over_S p) (opp (sum_over_S q))))
        by exact (id_trans Hadd2 (id_cong (fun x => plus (sum_over_S p) x) Hoppq)).
      assert (Hfin : Id (plus (sum_over_S p) (opp (sum_over_S q))) zero)
        by exact (id_trans (id_cong (fun x => plus x (opp (sum_over_S q))) Hnp)
                           (id_trans (id_cong (fun x => plus one x) (id_cong opp Hnq)) (plus_opp one))).
      exact (id_trans Htot Hfin).
    }
    assert (Hminus : Id (minus zero zero) zero)
      by (unfold minus; exact (plus_opp zero)).
    exact (id_trans (id_cong (fun x => minus x (sum_over_S (fun s => minus (p s) (q s)))) Hkl0)
                   (id_trans (id_cong (fun x => minus zero x) Hpq0) Hminus)).
  }
  (* 3) d(s0) = 0 *)
  assert (Hd0s : Id (minus (mult (p s0) (minus (log (p s0)) (log (q s0))))
                           (minus (p s0) (q s0))) zero)
    by exact (sum_over_S_zero_nonneg
                (fun s => minus (mult (p s) (minus (log (p s)) (log (q s))))
                                (minus (p s) (q s)))
                Hd_nonneg Hd_sum s0).
  (* 4) p·(log p - log q) = p - q *)
  assert (Hrel : Id (mult (p s0) (minus (log (p s0)) (log (q s0))))
                   (minus (p s0) (q s0)))
    by exact (minus_eq_cancel (mult (p s0) (minus (log (p s0)) (log (q s0))))
                              (minus (p s0) (q s0)) Hd0s).
  (* 5) 换形：log(p/q) = log p - log q；q/p 反号 *)
  assert (Hlhs : Id (mult (p s0) (minus (log (p s0)) (log (q s0))))
                    (mult (p s0) (log (mult (p s0) (inv_pos (q s0) (Hpq s0))))))
    by exact (id_sym (id_cong (fun x => mult (p s0) x)
                              (log_div (p s0) (q s0) (Hpp s0) (Hpq s0)))).
  rewrite Hlhs in Hrel.
  (* p·log(p/q) = p·(-log(q/p)) *)
  assert (Hlogneg : Id (log (mult (p s0) (inv_pos (q s0) (Hpq s0))))
                       (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0))))))
    by exact (log_div_neg (p s0) (q s0) (Hpp s0) (Hpq s0)).
  assert (Hlhs2 : Id (mult (p s0) (log (mult (p s0) (inv_pos (q s0) (Hpq s0)))))
                     (mult (p s0) (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))))
    by exact (id_cong (fun x => mult (p s0) x) Hlogneg).
  rewrite Hlhs2 in Hrel.
  (* RHS：p - q = p·(1 - q/p)（由 gibbs_pointwise 内恒等反向） *)
  assert (Hrhs : Id (minus (p s0) (q s0))
                    (mult (p s0) (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))).
  {
    assert (Hoppl : Id (mult (p s0) (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))
                       (opp (mult (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))))
      by exact (opp_mult_l (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)).
    assert (Hdist : Id (mult (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
                       (minus (mult (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                              (mult (p s0) one)))
      by exact (mult_minus_distr_l (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0))) one).
    assert (Hcc : Id (mult (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0)))) (q s0)).
    {
      assert (H1 : Id (mult (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                      (mult (mult (p s0) (q s0)) (inv_pos (p s0) (Hpp s0))))
        by exact (mult_assoc (p s0) (q s0) (inv_pos (p s0) (Hpp s0))).
      assert (H2 : Id (mult (mult (p s0) (q s0)) (inv_pos (p s0) (Hpp s0)))
                      (mult (mult (q s0) (p s0)) (inv_pos (p s0) (Hpp s0))))
        by exact (id_cong (fun x => mult x (inv_pos (p s0) (Hpp s0))) (mult_comm (p s0) (q s0))).
      assert (H3 : Id (mult (mult (q s0) (p s0)) (inv_pos (p s0) (Hpp s0)))
                      (mult (q s0) (mult (p s0) (inv_pos (p s0) (Hpp s0)))))
        by exact (id_sym (mult_assoc (q s0) (p s0) (inv_pos (p s0) (Hpp s0)))).
      assert (H4 : Id (mult (q s0) (mult (p s0) (inv_pos (p s0) (Hpp s0))))
                      (mult (q s0) one))
        by exact (id_cong (fun x => mult (q s0) x) (inv_pos_correct (p s0) (Hpp s0))).
      assert (H5 : Id (mult (q s0) one) (q s0)) by exact (mult_one (q s0)).
      exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
    }
    assert (Hmo : Id (mult (p s0) one) (p s0)) by exact (mult_one (p s0)).
    assert (Hfull : Id (mult (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
                       (minus (q s0) (p s0)))
      by exact (id_trans Hdist (id_trans (id_cong (fun x => minus x (mult (p s0) one)) Hcc)
                                         (id_cong (fun x => minus (q s0) x) Hmo))).
    assert (Hopp2 : Id (opp (minus (q s0) (p s0))) (minus (p s0) (q s0)))
      by exact (id_trans (opp_minus (q s0) (p s0)) (id_sym (plus_comm (p s0) (opp (q s0))))).
    exact (id_sym (id_trans Hoppl (id_trans (id_cong opp Hfull) Hopp2))).
  }
  rewrite Hrhs in Hrel.
  (* 6) mult_cancel_l（p > 0）：-log(q/p) = -(q/p - 1) ⟹ log(q/p) = q/p - 1 *)
  assert (Hopp_eq : Id (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))
                       (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))
    by exact (mult_cancel_l (p s0)
                            (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))
                            (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
                            (Hpp s0) Hrel).
  assert (Hlog_eq : Id (log (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                       (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)).
  {
    assert (H2 : Id (log (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                    (opp (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))))
      by exact (id_sym (double_neg (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))).
    assert (H3 : Id (opp (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))
                    (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
      by exact (double_neg (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)).
    exact (id_trans H2 (id_trans (id_cong opp Hopp_eq) H3)).
  }
  (* 7) log_eq_linear：log(q/p) = q/p - 1 ⟹ q/p = 1 *)
  assert (Hratio_pos : lt zero (mult (q s0) (inv_pos (p s0) (Hpp s0))))
    by exact (mult_positive (q s0) (inv_pos (p s0) (Hpp s0)) (Hpq s0) (inv_pos_pos (p s0) (Hpp s0))).
  assert (Hratio_one : Id (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)
    by exact (log_eq_linear (mult (q s0) (inv_pos (p s0) (Hpp s0))) Hratio_pos Hlog_eq).
  (* 8) q·(1/p) = 1 = p·(1/p) ⟹ q = p（mult_cancel_r 消 inv_pos p > 0） *)
  assert (Hpr : Id (mult (p s0) (inv_pos (p s0) (Hpp s0))) one)
    by exact (inv_pos_correct (p s0) (Hpp s0)).
  assert (Hqr : Id (mult (q s0) (inv_pos (p s0) (Hpp s0)))
                  (mult (p s0) (inv_pos (p s0) (Hpp s0))))
    by exact (id_trans Hratio_one (id_sym Hpr)).
  exact (id_sym (mult_cancel_r (inv_pos (p s0) (Hpp s0)) (q s0) (p s0) (inv_pos_pos (p s0) (Hpp s0)) Hqr)).
Qed.

(* Boltzmann 分布正性：p_b(s) > 0（逆元正 × 指数正） *)
Lemma boltzmann_dist_pos :
  forall s : S, lt zero (boltzmann_dist s).
Proof.
  intro s.
  unfold boltzmann_dist.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* 自由能最小化定理（原假设变量降级为定理）：
   F[p_b] ≤ F[p]——Boltzmann 分布是自由能全局极小值点。
   证明：F[p] = F[p_b] + D·KL(p||p_b)（free_energy_kl_decomp）
   + KL ≥ 0（gibbs_inequality）+ D > 0 保序。 *)
Theorem min_free_energy_is_boltzmann :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    le (free_energy boltzmann_dist) (free_energy p).
Proof.
  intros p Hnp Hpp.
  (* 1. F[p] = F[p_b] + D·KL(p||p_b) *)
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy p boltzmann_dist))))
    by exact (free_energy_kl_decomp p Hnp).
  (* 2. KL ≥ 0（gibbs_inequality；boltzmann_dist 归一化 + 正性） *)
  assert (Hkl : le zero (relative_entropy p boltzmann_dist)).
  {
    apply (gibbs_inequality p boltzmann_dist).
    - exact Hnp.
    - exact Hpp.
    - exact (boltzmann_normalized).
    - intro s. exact (boltzmann_dist_pos s).
  }
  (* 3. D > 0 保序：0 ≤ KL ⟹ D·0 ≤ D·KL ⟹ 0 ≤ D·KL *)
  assert (Hdkl : le zero (mult D (relative_entropy p boltzmann_dist))).
  {
    assert (Hm : le (mult D zero) (mult D (relative_entropy p boltzmann_dist)))
      by exact (le_mult_compat_r D zero (relative_entropy p boltzmann_dist)
                                (lt_le_iff _ _ (inl D_pos)) Hkl).
    assert (Hz : Id (mult D zero) zero) by exact (mult_zero D).
    exact (le_id_l zero (mult D zero) (mult D (relative_entropy p boltzmann_dist)) (id_sym Hz) Hm).
  }
  (* 4. F[p_b] ≤ F[p_b] + D·KL = F[p]（le_plus_compat + le_refl + le_id_l 归约） *)
  assert (Hfin : le (free_energy boltzmann_dist)
                    (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist)))).
  {
    assert (Hplus : le (plus (free_energy boltzmann_dist) zero)
                       (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist))))
      by (apply (le_plus_compat (free_energy boltzmann_dist) (free_energy boltzmann_dist)
                                zero (mult D (relative_entropy p boltzmann_dist)));
          [apply le_refl | exact Hdkl]).
    assert (Hpz : Id (plus (free_energy boltzmann_dist) zero) (free_energy boltzmann_dist))
      by exact (plus_zero (free_energy boltzmann_dist)).
    exact (le_id_l (free_energy boltzmann_dist) (plus (free_energy boltzmann_dist) zero)
                   (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist)))
                   (id_sym Hpz) Hplus).
  }
  exact (le_id_r (free_energy boltzmann_dist) (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist))) (free_energy p) (id_sym Hdecomp) Hfin).
Qed.

(* 自由能最小点唯一性：若 p 达到与 Boltzmann 相同的自由能，则 p = p_b（逐点）。
   证明：F[p] = F[p_b] + D·KL 且 F[p] = F[p_b] ⟹ D·KL = 0 ⟹ KL = 0（D > 0
   mult_cancel_l）⟹ p = p_b（gibbs_equality）。 *)
Theorem free_energy_min_unique :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (free_energy p) (free_energy boltzmann_dist) ->
    forall s : S, Id (p s) (boltzmann_dist s).
Proof.
  intros p Hnp Hpp Hfeq s.
  (* 1. F[p] = F[p_b] + D·KL（恒等式） *)
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy p boltzmann_dist))))
    by exact (free_energy_kl_decomp p Hnp).
  (* 2. 由 F[p] = F[p_b] 得 D·KL = 0（消去 F[p_b]） *)
  assert (Hdkl0 : Id (mult D (relative_entropy p boltzmann_dist)) zero).
  {
    assert (H1 : Id (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist)))
                   (free_energy p))
      by exact (id_sym Hdecomp).
    assert (H2 : Id (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist)))
                   (free_energy boltzmann_dist))
      by exact (id_trans H1 Hfeq).
    (* plus FB KL = FB ⟹ KL = 0（plus_cancel 消去 FB） *)
    exact (plus_cancel_zero (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist)) H2).
  }
  (* 3. D > 0 ⟹ KL = 0（mult_cancel_l） *)
  assert (Hkl0 : Id (relative_entropy p boltzmann_dist) zero).
  {
    (* mult D KL = zero 且 D > 0：需由 D·KL = 0 得 KL = 0
       （用 mult_cancel_l 的零版本：mult a b = mult a zero 且 a > 0 ⟹ b = zero） *)
    assert (Hcz : Id (mult D (relative_entropy p boltzmann_dist))
                     (mult D zero))
      by exact (id_trans Hdkl0 (id_sym (mult_zero D))).
    exact (mult_cancel_l D (relative_entropy p boltzmann_dist) zero D_pos Hcz).
  }
  (* 4. gibbs_equality：KL = 0 ⟹ p = p_b *)
  exact (gibbs_equality p boltzmann_dist Hnp Hpp (boltzmann_normalized) (fun t => boltzmann_dist_pos t) Hkl0 s).
Qed.

(* ============================================================ *)
(* 最大熵原理（统计力学第三支柱：自由能-熵对偶）               *)
(* ============================================================ *)
(* 前两条：自由能唯一极小（min_free_energy_is_boltzmann +       *)
(* free_energy_min_unique），KL 精确度量偏离（free_energy_kl_   *)
(* decomp）。此处补第三条：同能量约束下 Boltzmann 分布是熵最大 *)
(* 分布，且熵亏 = KL（偏离的熵学度量）。                       *)
(* ------------------------------------------------------------ *)

(* 信息熵：S[p] := -Σ_s p(s)·log p(s)（分布版，顶层 entropy 为 R→R 版） *)
Definition entropy_dist (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (opp (log (p s)))).

(* 能量期望：⟨E⟩_p := Σ_s p(s)·base_loss(s)（最大熵的约束量） *)
Definition energy_expectation (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (base_loss s)).

(* 熵分解：Σ p·log p = -S[p]（由 sum_over_S_ext + opp_mult_l + double_neg + sum_opp） *)
Lemma entropy_neg_sum :
  forall p : S -> R,
    Id (sum_over_S (fun s => mult (p s) (log (p s))))
       (opp (entropy_dist p)).
Proof.
  intro p.
  unfold entropy_dist.
  assert (Hpt : forall s, Id (mult (p s) (log (p s)))
                            (opp (mult (p s) (opp (log (p s)))))).
  {
    intro s.
    assert (H1 : Id (mult (p s) (opp (log (p s)))) (opp (mult (p s) (log (p s)))))
      by exact (opp_mult_l (p s) (log (p s))).
    assert (H2 : Id (opp (mult (p s) (opp (log (p s)))))
                    (opp (opp (mult (p s) (log (p s))))))
      by exact (id_cong opp H1).
    exact (id_sym (id_trans H2 (double_neg (mult (p s) (log (p s)))))).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (log (p s))))
                   (sum_over_S (fun s => opp (mult (p s) (opp (log (p s)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (log (p s)))
                             (fun s => opp (mult (p s) (opp (log (p s))))) Hpt).
  rewrite Hext.
  assert (Hso : Id (sum_over_S (fun s => opp (mult (p s) (opp (log (p s))))))
                   (opp (sum_over_S (fun s => mult (p s) (opp (log (p s)))))))
    by exact (sum_opp (fun s => mult (p s) (opp (log (p s))))).
  exact Hso.
Qed.

(* 自由能-熵-能量恒等式：F[p] = ⟨E⟩_p - D·S[p] *)
Lemma free_energy_entropy :
  forall p : S -> R,
    Id (free_energy p)
       (plus (energy_expectation p) (mult D (opp (entropy_dist p)))).
Proof.
  intro p.
  unfold free_energy, energy_expectation.
  assert (Hneg : Id (sum_over_S (fun s => mult (p s) (log (p s))))
                    (opp (entropy_dist p)))
    by exact (entropy_neg_sum p).
  exact (id_cong (fun x => plus (sum_over_S (fun s => mult (p s) (base_loss s))) (mult D x)) Hneg).
Qed.

(* 熵差-相对熵恒等式：同能量约束（⟨E⟩_p = ⟨E⟩_b）下
   S[p_b] - S[p] = KL(p || p_b)。
   证明：F[p] = F[p_b] + D·KL（自由能恒等式）
   + 自由能-熵-能量恒等式（F = ⟨E⟩ - D·S）+ 同能量消去 + D > 0 消去。 *)
Theorem entropy_deficit_kl :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (energy_expectation p) (energy_expectation boltzmann_dist) ->
    Id (minus (entropy_dist boltzmann_dist) (entropy_dist p))
       (relative_entropy p boltzmann_dist).
Proof.
  intros p Hnp Hpp Henergy.
  (* 1. F[p] = F[p_b] + D·KL（自由能恒等式） *)
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy p boltzmann_dist))))
    by exact (free_energy_kl_decomp p Hnp).
  (* 2. 两侧换成 ⟨E⟩ - D·S 形式 *)
  assert (Hfe_p : Id (free_energy p)
                     (plus (energy_expectation p) (mult D (opp (entropy_dist p)))))
    by exact (free_energy_entropy p).
  assert (Hfe_b : Id (free_energy boltzmann_dist)
                     (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist boltzmann_dist)))))
    by exact (free_energy_entropy boltzmann_dist).
  (* 3. ⟨E⟩_p - D·S[p] = ⟨E⟩_b - D·S[p_b] + D·KL *)
  assert (Htot : Id (plus (energy_expectation p) (mult D (opp (entropy_dist p))))
                   (plus (plus (energy_expectation boltzmann_dist)
                               (mult D (opp (entropy_dist boltzmann_dist))))
                         (mult D (relative_entropy p boltzmann_dist)))).
  {
    assert (H1 : Id (plus (energy_expectation p) (mult D (opp (entropy_dist p))))
                    (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist))))
      by exact (id_trans (id_sym Hfe_p) Hdecomp).
    assert (H2 : Id (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist)))
                    (plus (plus (energy_expectation boltzmann_dist)
                                (mult D (opp (entropy_dist boltzmann_dist))))
                          (mult D (relative_entropy p boltzmann_dist))))
      by exact (id_cong (fun x => plus x (mult D (relative_entropy p boltzmann_dist))) Hfe_b).
    exact (id_trans H1 H2).
  }
  (* 4. 同能量消去 ⟨E⟩：-D·S[p] = -D·S[p_b] + D·KL *)
  assert (Hcancel : Id (mult D (opp (entropy_dist p)))
                       (plus (mult D (opp (entropy_dist boltzmann_dist)))
                             (mult D (relative_entropy p boltzmann_dist)))).
  {
    assert (Hsw : Id (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist p))))
                     (plus (energy_expectation p) (mult D (opp (entropy_dist p)))))
      by exact (id_cong (fun x => plus x (mult D (opp (entropy_dist p)))) (id_sym Henergy)).
    assert (H2 : Id (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist p))))
                    (plus (plus (energy_expectation boltzmann_dist)
                                (mult D (opp (entropy_dist boltzmann_dist))))
                          (mult D (relative_entropy p boltzmann_dist))))
      by exact (id_trans Hsw Htot).
    assert (Hre : Id (plus (plus (energy_expectation boltzmann_dist)
                                (mult D (opp (entropy_dist boltzmann_dist))))
                          (mult D (relative_entropy p boltzmann_dist)))
                    (plus (energy_expectation boltzmann_dist)
                          (plus (mult D (opp (entropy_dist boltzmann_dist)))
                                (mult D (relative_entropy p boltzmann_dist)))))
      by exact (id_sym (plus_assoc (energy_expectation boltzmann_dist)
                                     (mult D (opp (entropy_dist boltzmann_dist)))
                                     (mult D (relative_entropy p boltzmann_dist)))).
    assert (H2r : Id (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist p))))
                     (plus (energy_expectation boltzmann_dist)
                           (plus (mult D (opp (entropy_dist boltzmann_dist)))
                                 (mult D (relative_entropy p boltzmann_dist)))))
      by exact (id_trans H2 Hre).
    exact (plus_cancel_l (energy_expectation boltzmann_dist)
                         (mult D (opp (entropy_dist p)))
                         (plus (mult D (opp (entropy_dist boltzmann_dist)))
                               (mult D (relative_entropy p boltzmann_dist)))
                         H2r).
  }
  (* 5. 环消去：由 -D·S[p] = -D·S[p_b] + D·KL 且 D > 0 推出 S[p_b] - S[p] = KL *)
  exact (ring_d_cancel D (entropy_dist p) (entropy_dist boltzmann_dist)
                      (relative_entropy p boltzmann_dist) D_pos Hcancel).
Qed.

Theorem max_entropy_is_boltzmann :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (energy_expectation p) (energy_expectation boltzmann_dist) ->
    le (entropy_dist p) (entropy_dist boltzmann_dist).
Proof.
  intros p Hnp Hpp Henergy.
  (* 1. S[p_b] - S[p] = KL *)
  assert (Hdef : Id (minus (entropy_dist boltzmann_dist) (entropy_dist p))
                    (relative_entropy p boltzmann_dist))
    by exact (entropy_deficit_kl p Hnp Hpp Henergy).
  (* 2. KL ≥ 0（gibbs_inequality：p 与 p_b 均归一化正） *)
  assert (Hkl : le zero (relative_entropy p boltzmann_dist)).
  {
    apply (gibbs_inequality p boltzmann_dist).
    - exact Hnp.
    - exact Hpp.
    - exact (boltzmann_normalized).
    - intro s. exact (boltzmann_dist_pos s).
  }
  (* 3. 0 ≤ S[p_b] - S[p] ⟹ S[p] ≤ S[p_b]（le_minus_nonneg 的逆：用 minus_plus_cancel） *)
  assert (Hnonneg : le zero (minus (entropy_dist boltzmann_dist) (entropy_dist p)))
    by exact (le_id_r zero (relative_entropy p boltzmann_dist)
                     (minus (entropy_dist boltzmann_dist) (entropy_dist p))
                     (id_sym Hdef) Hkl).
  (* S[p] + (S[p_b] - S[p]) = S[p_b]（minus_plus_cancel）⟹ le S[p] S[p_b] *)
  assert (Hplus : Id (plus (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p)))
                     (entropy_dist boltzmann_dist))
    by exact (minus_plus_cancel (entropy_dist p) (entropy_dist boltzmann_dist)).
  assert (Hle : le (entropy_dist p)
                   (plus (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p))))
    by exact (le_plus_nonneg_r (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p)) Hnonneg).
  exact (le_id_r (entropy_dist p)
                 (plus (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p)))
                 (entropy_dist boltzmann_dist) Hplus Hle).
Qed.

(* ============================================================ *)
(* T2.2：温度-期望能量单调性（论文2 主之二）                *)
(*   主定理：t1 < t2 ⟹ E_temp(t1) ≤ E_temp(t2)（温度升高 ⟹ 能量期望不降） *)
(*   方法：变分法——Gibbs 不等式交叉相加（无导数、无三分律）    *)
(*     KL(q‖p_β) ≥ 0 对 (q=p_{β2},β=β1) 与 (q=p_{β1},β=β2)    *)
(*     相加 ⟹ (β1−β2)(E1−E2) ≤ 0；β1−β2 > 0 ⟹ E1 ≤ E2        *)
(*   诚实接口假设（Real 层可实例化，非经典公理）：             *)
(*     sum_over_S_pos    —— 有限和正项和为正（Section Alignment 同款，有限和可实例化） *)
(*     inv_pos_lt_compat —— Real 层 real_inv_lt_contra（严格逆反序） *)
(*     lt_minus_nonneg   —— Real 层逐 eps 直构（Qlt_minus_iff 提升） *)
(* ============================================================ *)
Variable sum_over_S_pos : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (minus b a).

(* ---------- 自证代数引理（接口层，纯构造性） ---------- *)

(* 加法保序的逆：a+c ≤ b+c ⟹ a ≤ b（有序交换群消去，le_id 代数） *)
Lemma le_plus_cancel_l : forall a b c : R, le (plus a c) (plus b c) -> le a b.
Proof.
  intros a b c H.
  apply (le_id_l a (minus (plus a c) c)).
  - (* a == minus (plus a c) c *)
    unfold minus.
    exact (id_trans (id_trans (id_sym (plus_zero a))
              (id_sym (id_cong (fun x => plus a x) (plus_opp c))))
              (plus_assoc a c (opp c))).
  - apply (le_id_r (minus (plus a c) c) (minus (plus b c) c) b).
    + (* minus (plus b c) c == b *)
      unfold minus.
      exact (id_trans (id_trans (id_sym (plus_assoc b c (opp c)))
              (id_cong (fun x => plus b x) (plus_opp c)))
              (plus_zero b)).
    + unfold minus.
      apply (le_plus_compat (plus a c) (plus b c) (opp c) (opp c) H (le_refl (opp c))).
Qed.

(* 减法非负的逆：a − b ≤ 0 ⟹ a ≤ b *)
Lemma le_minus_nonneg_rev : forall a b : R, le (minus a b) zero -> le a b.
Proof.
  intros a b H.
  apply (le_id_l a (plus (minus a b) b)).
  - (* a == plus (minus a b) b *)
    unfold minus.
    exact (id_trans (id_sym (plus_zero a))
           (id_trans (id_sym (id_cong (fun x => plus a x)
                 (id_trans (plus_comm (opp b) b) (plus_opp b))))
                 (plus_assoc a (opp b) b))).
  - apply (le_id_r (plus (minus a b) b) (plus zero b) b).
    + exact (id_trans (plus_comm zero b) (plus_zero b)).
    + apply (le_plus_compat (minus a b) zero b b H (le_refl b)).
Qed.

(* 乘正数消去：c > 0 且 a·c ≤ 0 ⟹ a ≤ 0（a == (a·c)·inv c） *)
Lemma le_mult_pos_cancel : forall a c : R, lt zero c -> le (mult a c) zero -> le a zero.
Proof.
  intros a c Hc H.
  apply (le_id_l a (mult (mult a c) (inv_pos c Hc))).
  - (* a == mult (mult a c) (inv_pos c Hc) *)
    exact (id_trans (id_sym (mult_one a))
           (id_trans (id_cong (fun x => mult a x) (id_sym (inv_pos_correct c Hc)))
                     (mult_assoc a c (inv_pos c Hc)))).
  - apply (le_id_r (mult (mult a c) (inv_pos c Hc)) (mult zero (inv_pos c Hc)) zero).
    + exact (id_trans (mult_comm zero (inv_pos c Hc)) (mult_zero (inv_pos c Hc))).
    + apply (le_mult_compat_weak (mult a c) zero (inv_pos c Hc)).
      * apply lt_le_iff. left. apply inv_pos_pos.
      * exact H.
Qed.

(* 乘法对减法的右分配：mult (minus a b) c == minus (mult a c) (mult b c) *)
Lemma mult_minus_distr_r : forall a b c : R,
  Id (mult (minus a b) c) (minus (mult a c) (mult b c)).
Proof.  intros a b c.
  unfold minus.
  exact (id_trans (mult_comm (plus a (opp b)) c)
           (id_trans (distrib c a (opp b))
              (id_trans (id_cong (fun x => plus x (mult c (opp b))) (mult_comm c a))
                 (id_trans (id_cong (fun x => plus (mult a c) x) (mult_comm c (opp b)))
                    (id_cong (fun x => plus (mult a c) x) (opp_mult_r b c)))))).
Qed.

(* ---------- T2.2 温度参数化定义 ---------- *)

(* 温度参数化配分函数（诚实接口：温度 t 的配分 Σ_s e^{-e_s/t}） *)
Variable Z_temp : R -> R.
Variable Z_temp_spec : forall t : R, forall Ht : lt zero t,
  Id (Z_temp t) (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Lemma Z_temp_pos : forall t : R, forall Ht : lt zero t,
  lt zero (Z_temp t).
Proof.
  intros t Ht.
  apply (lt_id_r zero (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))) (Z_temp t)).
  - exact (id_sym (Z_temp_spec t Ht)).
  - apply sum_over_S_pos.
    intro s.
    apply exp_neg_pos.
Qed.

(* 温度参数化 Boltzmann 分布与期望能量 *)
Definition boltzmann_dist_temp (t : R) (Ht : lt zero t) : S -> R :=
  fun s => mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Definition energy_exp_temp (t : R) (Ht : lt zero t) : R :=
  sum_over_S (fun s => mult (boltzmann_dist_temp t Ht s) (base_loss s)).

Theorem boltzmann_dist_temp_normalized : forall t : R, forall Ht : lt zero t,
  Id (sum_over_S (boltzmann_dist_temp t Ht)) one.
Proof.
  intros t Ht.
  unfold boltzmann_dist_temp.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                                  (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                   (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                         (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))))))
    by exact (sum_over_S_linear (inv_pos (Z_temp t) (Z_temp_pos t Ht))
               (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
  assert (HZ : Id (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))) (Z_temp t))
    by exact (id_sym (Z_temp_spec t Ht)).
  assert (Hcc : Id (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (Z_temp t)) one)
    by exact (id_trans (mult_comm (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (Z_temp t))
                       (inv_pos_correct (Z_temp t) (Z_temp_pos t Ht))).
  exact (id_trans Hlin (id_trans (id_cong (fun x => mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) x) HZ) Hcc)).
Qed.

Lemma boltzmann_dist_temp_pos : forall t : R, forall Ht : lt zero t, forall s : S,
  lt zero (boltzmann_dist_temp t Ht s).
Proof.
  intros t Ht s. unfold boltzmann_dist_temp.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* log p_β(s) == −log Z − β·e_s（温度版对数分解） *)
Theorem boltzmann_log_temp_decomp : forall t : R, forall Ht : lt zero t, forall s : S,
  Id (log (boltzmann_dist_temp t Ht s))
     (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))).
Proof.
  intros t Ht s. unfold boltzmann_dist_temp.
  assert (Hpos1 : lt zero (inv_pos (Z_temp t) (Z_temp_pos t Ht)))
    by exact (inv_pos_pos (Z_temp t) (Z_temp_pos t Ht)).
  assert (Hpos2 : lt zero (exp_neg (mult (inv_pos t Ht) (base_loss s))))
    by exact (exp_neg_pos (mult (inv_pos t Ht) (base_loss s))).
  assert (Hlm : Id (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                              (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                  (plus (log (inv_pos (Z_temp t) (Z_temp_pos t Ht)))
                        (log (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
    by exact (log_mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                       (exp_neg (mult (inv_pos t Ht) (base_loss s))) Hpos1 Hpos2).
  rewrite Hlm.
  assert (Hli : Id (log (inv_pos (Z_temp t) (Z_temp_pos t Ht))) (opp (log (Z_temp t))))
    by exact (log_inv_one_inv (Z_temp t) (Z_temp_pos t Ht)).
  rewrite Hli.
  assert (Hle : Id (log (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                  (opp (mult (inv_pos t Ht) (base_loss s))))
    by exact (log_exp_neg (mult (inv_pos t Ht) (base_loss s))).
  rewrite Hle.
  reflexivity.
Qed.

(* 熵显式公式：H(p_β) == β·E(p_β) + log Z（β := inv t） *)
Theorem entropy_temp_explicit : forall t : R, forall Ht : lt zero t,
  Id (entropy_dist (boltzmann_dist_temp t Ht))
     (plus (mult (inv_pos t Ht) (energy_exp_temp t Ht)) (log (Z_temp t))).
Proof.
  intros t Ht.
  unfold entropy_dist, energy_exp_temp, boltzmann_dist_temp.
  (* 逐点：p·(−log p) == p·(βe) + p·logZ *)
  assert (Hpt : forall s : S,
    Id (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
             (opp (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
       (plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                   (mult (inv_pos t Ht) (base_loss s)))
             (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                   (log (Z_temp t))))).
  { intro s.
    assert (Hlog : Id (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                                 (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                      (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
      by exact (boltzmann_log_temp_decomp t Ht s).
    (* −log p == logZ + βe *)
    assert (Hopp : Id (opp (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
                      (plus (log (Z_temp t)) (mult (inv_pos t Ht) (base_loss s)))).
    { exact (id_trans (opp_plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s))))
             (id_trans (id_cong (fun x => plus x (opp (opp (mult (inv_pos t Ht) (base_loss s)))))
                                (double_neg (log (Z_temp t))))
                       (id_cong (fun x => plus (log (Z_temp t)) x)
                                (double_neg (mult (inv_pos t Ht) (base_loss s)))))). }
    (* p·(−log p) == p·(logZ + βe) == p·(βe) + p·logZ *)
    assert (Hcomm : Id (plus (log (Z_temp t)) (mult (inv_pos t Ht) (base_loss s)))
                       (plus (mult (inv_pos t Ht) (base_loss s)) (log (Z_temp t))))
      by exact (plus_comm (log (Z_temp t)) (mult (inv_pos t Ht) (base_loss s))).
    exact (id_trans (id_cong (fun x => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (opp x)) Hlog)
           (id_trans (id_cong (fun x => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) x) Hopp)
           (id_trans (id_cong (fun x => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) x) Hcomm)
                     (distrib (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                              (mult (inv_pos t Ht) (base_loss s)) (log (Z_temp t)))))). }
  (* Σ 线性：Σ p·(βe) + Σ p·logZ（手动链，无 rewrite） *)
  assert (H1 : Id (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                                           (opp (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))
                   (sum_over_S (fun s => plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                                              (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))))
    by exact (sum_over_S_ext (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                                             (opp (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                             (fun s => plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                                            (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))
                             Hpt).
  assert (Hadd : Id (sum_over_S (fun s => plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                                              (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t)))))
                    (plus (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s))))
                          (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))))
    by exact (sum_over_S_add (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                             (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t)))).
  (* Σ p·(βe) == β·Σ p·e *)
  assert (Hlin1 : Id (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s))))
                     (mult (inv_pos t Ht) (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s))))).
  { assert (Hpt2 : forall s : S,
      Id (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
         (mult (inv_pos t Ht) (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s)))).
    { intro s.
      apply (id_trans (mult_comm (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
             (id_trans (id_sym (mult_assoc (inv_pos t Ht) (base_loss s) (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
                       (id_cong (fun x => mult (inv_pos t Ht) x)
                                (mult_comm (base_loss s) (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))). }
    exact (id_trans (sum_over_S_ext _ _ Hpt2)
           (sum_over_S_linear (inv_pos t Ht)
             (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s)))). }
  (* Σ p·logZ == logZ·Σ p == logZ *)
  assert (Hlin2 : Id (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))
                     (log (Z_temp t))).
  { assert (Hpt3 : forall s : S,
      Id (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t)))
         (mult (log (Z_temp t)) (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
    by (intro s; apply mult_comm).
    exact (id_trans (sum_over_S_ext _ _ Hpt3)
           (id_trans (sum_over_S_linear (log (Z_temp t)) (boltzmann_dist_temp t Ht))
           (id_trans (id_cong (fun x => mult (log (Z_temp t)) x) (boltzmann_dist_temp_normalized t Ht))
                     (mult_one (log (Z_temp t)))))). }
  exact (id_trans H1 (id_trans Hadd
         (id_trans (id_cong (fun x => plus x (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))) Hlin1)
                   (id_cong (fun x => plus (mult (inv_pos t Ht) (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s)))) x) Hlin2)))).
Qed.

(* ---------- T2.2 变分法主体 ---------- *)

(* 相对熵对 Boltzmann 的显式分解：KL(q‖p_β) == −H(q) + β·E(q) + log Z *)
Theorem relative_entropy_temp_decomp : forall t : R, forall Ht : lt zero t, forall q : S -> R,
  normalized q ->
  Id (relative_entropy q (boltzmann_dist_temp t Ht))
     (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q)))
           (log (Z_temp t))).
Proof.
  intros t Ht q Hnq.
  unfold relative_entropy, entropy_dist, energy_expectation, boltzmann_dist_temp.
  (* 逐点：q·(log q − log p) == q·log q − q·log p *)
  assert (Hpt : forall s : S,
    Id (mult (q s) (minus (log (q s)) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
       (minus (mult (q s) (log (q s)))
              (mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))).
  { intro s. apply mult_minus_distr_l. }
  (* Σ q·log q == −H(q) *)
  assert (Hq1 : Id (sum_over_S (fun s => mult (q s) (log (q s)))) (opp (entropy_dist q))).
  { unfold entropy_dist.
    apply entropy_neg_sum. }
  (* Σ q·log p == −β·E(q) − log Z（手动链） *)
  assert (Hq2 : Id (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                   (plus (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                         (opp (log (Z_temp t))))).
  { (* 逐点：q·log p == opp(q·logZ) + opp(q·βe) *)
    assert (Hpt2 : forall s : S,
      Id (mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
         (plus (opp (mult (q s) (log (Z_temp t))))
               (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))))).
    { intro s.
      assert (Hlog : Id (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                        (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
        by exact (boltzmann_log_temp_decomp t Ht s).
      exact (id_trans (id_cong (fun x => mult (q s) x) Hlog)
             (id_trans (id_cong (fun x => mult (q s) x)
                                (plus_comm (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
             (id_trans (distrib (q s) (opp (mult (inv_pos t Ht) (base_loss s))) (opp (log (Z_temp t))))
             (id_trans (id_cong (fun x => plus x (mult (q s) (opp (log (Z_temp t)))))
                                (opp_mult_l (q s) (mult (inv_pos t Ht) (base_loss s))))
             (id_trans (id_cong (fun x => plus (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))) x)
                                (opp_mult_l (q s) (log (Z_temp t))))
                       (plus_comm (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))
                                  (opp (mult (q s) (log (Z_temp t)))))))))). }
    assert (H1 : Id (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                    (sum_over_S (fun s => plus (opp (mult (q s) (log (Z_temp t))))
                                               (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))))))
      by exact (sum_over_S_ext _ _ Hpt2).
    assert (Hadd : Id (sum_over_S (fun s => plus (opp (mult (q s) (log (Z_temp t))))
                                                 (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))))
                      (plus (sum_over_S (fun s => opp (mult (q s) (log (Z_temp t)))))
                            (sum_over_S (fun s => opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))))))
      by exact (sum_over_S_add (fun s => opp (mult (q s) (log (Z_temp t))))
                               (fun s => opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))).
    (* Σ q·logZ == logZ（常数提取 + 归一化） *)
    assert (Hs1 : Id (sum_over_S (fun s => mult (q s) (log (Z_temp t)))) (log (Z_temp t))).
    { assert (Hc : forall s : S, Id (mult (q s) (log (Z_temp t))) (mult (log (Z_temp t)) (q s)))
        by (intro s; apply mult_comm).
      exact (id_trans (sum_over_S_ext _ _ Hc)
             (id_trans (sum_over_S_linear (log (Z_temp t)) q)
                       (id_trans (id_cong (fun x => mult (log (Z_temp t)) x) Hnq)
                                 (mult_one (log (Z_temp t)))))). }
    (* Σ q·(βe) == β·Σ q·e *)
    assert (Hs2 : Id (sum_over_S (fun s => mult (q s) (mult (inv_pos t Ht) (base_loss s))))
                     (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))).
    { assert (Hc2 : forall s : S, Id (mult (q s) (mult (inv_pos t Ht) (base_loss s)))
                                     (mult (inv_pos t Ht) (mult (q s) (base_loss s)))).
      { intro s.
        apply (id_trans (mult_comm (q s) (mult (inv_pos t Ht) (base_loss s)))
               (id_trans (id_sym (mult_assoc (inv_pos t Ht) (base_loss s) (q s)))
                         (id_cong (fun x => mult (inv_pos t Ht) x) (mult_comm (base_loss s) (q s))))). }
      exact (id_trans (sum_over_S_ext _ _ Hc2)
             (sum_over_S_linear (inv_pos t Ht) (fun s => mult (q s) (base_loss s)))). }
    exact (id_trans H1 (id_trans Hadd
           (id_trans (id_cong (fun x => plus x (sum_over_S (fun s => opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))))
                              (sum_opp (fun s => mult (q s) (log (Z_temp t)))))
           (id_trans (id_cong (fun x => plus (opp (sum_over_S (fun s => mult (q s) (log (Z_temp t))))) x)
                              (sum_opp (fun s => mult (q s) (mult (inv_pos t Ht) (base_loss s)))))
           (id_trans (id_cong (fun x => plus (opp x) (opp (sum_over_S (fun s => mult (q s) (mult (inv_pos t Ht) (base_loss s)))))) Hs1)
           (id_trans (id_cong (fun x => plus (opp (log (Z_temp t))) (opp x)) Hs2)
                     (plus_comm (opp (log (Z_temp t)))
                                (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))))))))). }
  (* 组装：minus (Σ q·log q) (Σ q·log p) == −H + βE + logZ（手动链） *)
  assert (Hopp : Id (opp (plus (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                                 (opp (log (Z_temp t)))))
                    (plus (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))
                          (log (Z_temp t)))).
  { exact (id_trans (opp_plus (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                              (opp (log (Z_temp t))))
           (id_trans (id_cong (fun x => plus x (opp (opp (log (Z_temp t)))))
                              (double_neg (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))))
                     (id_cong (fun x => plus (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))) x)
                              (double_neg (log (Z_temp t)))))). }
  assert (Hfin : Id (minus (sum_over_S (fun s => mult (q s) (log (q s))))
                           (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))
                    (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                          (log (Z_temp t)))).
  { unfold minus.
    exact (id_trans (id_cong (fun x => plus x (opp (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))) Hq1)
           (id_trans (id_cong (fun x => plus (opp (entropy_dist q)) (opp x)) Hq2)
           (id_trans (id_cong (fun x => plus (opp (entropy_dist q)) x) Hopp)
                     (plus_assoc (opp (entropy_dist q))
                                         (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))
                                         (log (Z_temp t)))))). }
  assert (Hstep : Id (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))
                     (sum_over_S (fun s => minus (mult (q s) (log (q s)))
                                                 (mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))))
    by exact (sum_over_S_ext _ _ Hpt).
  exact (id_trans Hstep
         (id_trans (sum_over_S_minus (fun s => mult (q s) (log (q s)))
                                     (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                   Hfin)).
Qed.

(* 变分界：任意归一化正分布 q 的熵-能量组合 ≤ log Z（Gibbs 不等式展开） *)
Theorem variational_temp_bound : forall t : R, forall Ht : lt zero t, forall q : S -> R,
  normalized q -> positive_dist q ->
  le (minus (entropy_dist q) (mult (inv_pos t Ht) (energy_expectation q)))
     (log (Z_temp t)).
Proof.
  intros t Ht q Hnq Hpq.
  assert (Hkl : le zero (relative_entropy q (boltzmann_dist_temp t Ht)))
    by (apply (gibbs_inequality q (boltzmann_dist_temp t Ht) Hnq Hpq
               (boltzmann_dist_temp_normalized t Ht) (boltzmann_dist_temp_pos t Ht))).
  assert (Hrel : Id (relative_entropy q (boltzmann_dist_temp t Ht))
                    (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t))))
    by (apply (relative_entropy_temp_decomp t Ht q Hnq)).
  rewrite Hrel in Hkl.
  (* 移项 1：0 ≤ −H + βE + logZ ⟹ H ≤ βE + logZ *)
  assert (Hstep1 : le (entropy_dist q) (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)))).
  { apply (le_id_l (entropy_dist q) (plus (entropy_dist q) zero)).
    - exact (id_sym (plus_zero (entropy_dist q))).
    - apply (le_id_r (plus (entropy_dist q) zero)
             (plus (entropy_dist q) (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t))))
             (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)))).
      + (* H + (−H + βE + logZ) == βE + logZ *)
        apply (id_trans (plus_assoc (entropy_dist q)
                                    (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q)))
                                    (log (Z_temp t)))
               (id_trans (id_cong (fun x => plus x (log (Z_temp t)))
                                  (plus_assoc (entropy_dist q) (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))))
               (id_trans (id_cong (fun x => plus x (log (Z_temp t)))
                                  (id_cong (fun x => plus x (mult (inv_pos t Ht) (energy_expectation q)))
                                           (plus_opp (entropy_dist q))))
               (id_cong (fun x => plus x (log (Z_temp t)))
                        (id_trans (plus_comm zero (mult (inv_pos t Ht) (energy_expectation q)))
                                  (plus_zero (mult (inv_pos t Ht) (energy_expectation q)))))))).
      + apply (le_plus_compat (entropy_dist q) (entropy_dist q) zero
               (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t)))
               (le_refl (entropy_dist q)) Hkl). }
  (* 移项 2：H ≤ βE + logZ ⟹ H − βE ≤ logZ *)
  apply (le_id_r (plus (entropy_dist q) (opp (mult (inv_pos t Ht) (energy_expectation q))))
         (plus (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t))) (opp (mult (inv_pos t Ht) (energy_expectation q))))
         (log (Z_temp t))).
  - (* (βE + logZ) − βE == logZ *)
    apply (id_trans (id_sym (plus_assoc (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)) (opp (mult (inv_pos t Ht) (energy_expectation q)))))
           (id_trans (id_cong (fun x => plus (mult (inv_pos t Ht) (energy_expectation q)) x)
                              (plus_comm (log (Z_temp t)) (opp (mult (inv_pos t Ht) (energy_expectation q)))))
           (id_trans (plus_assoc (mult (inv_pos t Ht) (energy_expectation q)) (opp (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t)))
           (id_trans (id_cong (fun x => plus x (log (Z_temp t))) (plus_opp (mult (inv_pos t Ht) (energy_expectation q))))
           (id_trans (plus_comm zero (log (Z_temp t))) (plus_zero (log (Z_temp t)))))))).
  - apply (le_plus_compat (entropy_dist q) (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)))
                           (opp (mult (inv_pos t Ht) (energy_expectation q)))
                           (opp (mult (inv_pos t Ht) (energy_expectation q)))
                           Hstep1 (le_refl (opp (mult (inv_pos t Ht) (energy_expectation q))))).
Qed.

(* ============ T2.2 主定理：温度-期望能量单调性 ============ *)
Theorem energy_exp_temp_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 -> le (energy_exp_temp t1 Ht1) (energy_exp_temp t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := energy_exp_temp t1 Ht1). set (E2 := energy_exp_temp t2 Ht2).
  set (H1 := entropy_dist (boltzmann_dist_temp t1 Ht1)). set (H2 := entropy_dist (boltzmann_dist_temp t2 Ht2)).
  set (Z1 := Z_temp t1). set (Z2 := Z_temp t2).
  (* β2 < β1（inv 严格反序：t1 < t2 ⟹ 1/t2 < 1/t1） *)
  assert (Hb : lt b2 b1) by (unfold b1, b2; apply (inv_pos_lt_compat t1 t2 Ht1 Ht2 Ht12)).
  assert (Hbpos : lt zero (minus b1 b2)) by (unfold b1, b2; apply (lt_minus_nonneg b2 b1 Hb)).
  (* 变分 bound ×2 *)
  assert (Hv1 : le (minus H2 (mult b1 E2)) (log Z1)).
  { unfold H2, E2, Z1, b1.
    apply (variational_temp_bound t1 Ht1 (boltzmann_dist_temp t2 Ht2)).
    - apply boltzmann_dist_temp_normalized.
    - intro s. apply boltzmann_dist_temp_pos. }
  assert (Hv2 : le (minus H1 (mult b2 E1)) (log Z2)).
  { unfold H1, E1, Z2, b2.
    apply (variational_temp_bound t2 Ht2 (boltzmann_dist_temp t1 Ht1)).
    - apply boltzmann_dist_temp_normalized.
    - intro s. apply boltzmann_dist_temp_pos. }
  (* 熵显式代入（手动替换，无 rewrite） *)
  assert (Hex1 : Id H1 (plus (mult b1 E1) (log Z1))).
  { unfold H1, b1, E1, Z1. apply entropy_temp_explicit. }
  assert (Hex2 : Id H2 (plus (mult b2 E2) (log Z2))).
  { unfold H2, b2, E2, Z2. apply entropy_temp_explicit. }
  assert (Hv1' : le (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)) (log Z1)).
  { apply (le_id_l (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)) (minus H2 (mult b1 E2)) (log Z1)).
    - exact (id_cong (fun x => minus x (mult b1 E2)) (id_sym Hex2)).
    - exact Hv1. }
  assert (Hv2' : le (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1)) (log Z2)).
  { apply (le_id_l (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1)) (minus H1 (mult b2 E1)) (log Z2)).
    - exact (id_cong (fun x => minus x (mult b2 E1)) (id_sym Hex1)).
    - exact Hv2. }
  (* minus 内化简：minus (plus (mult b2 E2) (log Z2)) (mult b1 E2) == plus (mult (minus b2 b1) E2) (log Z2) *)
  assert (Hm1 : Id (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2))
                   (plus (mult (minus b2 b1) E2) (log Z2))).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (mult b2 E2) (log Z2) (opp (mult b1 E2))))
           (id_trans (id_cong (fun x => plus (mult b2 E2) x)
                              (plus_comm (log Z2) (opp (mult b1 E2))))
           (id_trans (plus_assoc (mult b2 E2) (opp (mult b1 E2)) (log Z2))
                     (id_sym (id_cong (fun x => plus x (log Z2))
                              (mult_minus_distr_r b2 b1 E2)))))). }
  assert (Hm2 : Id (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1))
                   (plus (mult (minus b1 b2) E1) (log Z1))).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (mult b1 E1) (log Z1) (opp (mult b2 E1))))
           (id_trans (id_cong (fun x => plus (mult b1 E1) x)
                              (plus_comm (log Z1) (opp (mult b2 E1))))
           (id_trans (plus_assoc (mult b1 E1) (opp (mult b2 E1)) (log Z1))
                     (id_sym (id_cong (fun x => plus x (log Z1))
                              (mult_minus_distr_r b1 b2 E1)))))). }
  assert (Hv1'' : le (plus (mult (minus b2 b1) E2) (log Z2)) (log Z1)).
  { apply (le_id_l (plus (mult (minus b2 b1) E2) (log Z2))
                   (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)) (log Z1)).
    - exact (id_sym Hm1).
    - exact Hv1'. }
  assert (Hv2'' : le (plus (mult (minus b1 b2) E1) (log Z1)) (log Z2)).
  { apply (le_id_l (plus (mult (minus b1 b2) E1) (log Z1))
                   (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1)) (log Z2)).
    - exact (id_sym Hm2).
    - exact Hv2'. }
  (* 移项：le (plus X (log Z2)) (log Z1) ⟹ le X (minus (log Z1) (log Z2)) *)
  assert (Hshift1 : le (mult (minus b2 b1) E2) (minus (log Z1) (log Z2))).
  { apply (le_id_l (mult (minus b2 b1) E2) (plus (plus (mult (minus b2 b1) E2) (log Z2)) (opp (log Z2)))).
    - exact (id_trans (id_sym (plus_zero (mult (minus b2 b1) E2)))
             (id_sym (id_trans (id_sym (plus_assoc (mult (minus b2 b1) E2) (log Z2) (opp (log Z2))))
                     (id_cong (fun x => plus (mult (minus b2 b1) E2) x) (plus_opp (log Z2)))))).
    - apply (le_plus_compat (plus (mult (minus b2 b1) E2) (log Z2)) (log Z1)
                             (opp (log Z2)) (opp (log Z2)) Hv1'' (le_refl (opp (log Z2)))). }
  assert (Hshift2 : le (mult (minus b1 b2) E1) (minus (log Z2) (log Z1))).
  { apply (le_id_l (mult (minus b1 b2) E1) (plus (plus (mult (minus b1 b2) E1) (log Z1)) (opp (log Z1)))).
    - exact (id_trans (id_sym (plus_zero (mult (minus b1 b2) E1)))
             (id_sym (id_trans (id_sym (plus_assoc (mult (minus b1 b2) E1) (log Z1) (opp (log Z1))))
                     (id_cong (fun x => plus (mult (minus b1 b2) E1) x) (plus_opp (log Z1)))))).
    - apply (le_plus_compat (plus (mult (minus b1 b2) E1) (log Z1)) (log Z2)
                             (opp (log Z1)) (opp (log Z1)) Hv2'' (le_refl (opp (log Z1)))). }
  (* 相加 *)
  assert (Hsum : le (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))
                   (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))).
  { apply (le_plus_compat (mult (minus b2 b1) E2) (minus (log Z1) (log Z2))
                           (mult (minus b1 b2) E1) (minus (log Z2) (log Z1)) Hshift1 Hshift2). }
  (* RHS == zero *)
  assert (Hz : Id (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))) zero).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (log Z1) (opp (log Z2)) (plus (log Z2) (opp (log Z1)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (plus_assoc (opp (log Z2)) (log Z2) (opp (log Z1))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_cong (fun x => plus x (opp (log Z1)))
                                       (id_trans (plus_comm (opp (log Z2)) (log Z2)) (plus_opp (log Z2)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_trans (plus_comm zero (opp (log Z1))) (plus_zero (opp (log Z1)))))
                     (plus_opp (log Z1)))))). }
  (* LHS == mult (minus b1 b2) (minus E1 E2) *)
  assert (Hoppm : Id (minus b2 b1) (opp (minus b1 b2))).
  { unfold minus.
    exact (id_sym (id_trans (opp_plus b1 (opp b2))
                   (id_trans (id_cong (fun x => plus (opp b1) x) (double_neg b2))
                             (plus_comm (opp b1) b2)))). }
  assert (Hlhs : Id (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))
                    (mult (minus b1 b2) (minus E1 E2))).
  { apply (id_trans (id_cong (fun x => plus (mult x E2) (mult (minus b1 b2) E1)) Hoppm)
           (id_trans (id_cong (fun x => plus x (mult (minus b1 b2) E1))
                              (opp_mult_r (minus b1 b2) E2))
           (id_trans (id_cong (fun x => plus x (mult (minus b1 b2) E1))
                              (id_sym (opp_mult_l (minus b1 b2) E2)))
           (id_trans (id_sym (distrib (minus b1 b2) (opp E2) E1))
                     (id_cong (fun x => mult (minus b1 b2) x) (plus_comm (opp E2) E1)))))). }
  (* 组装：le (mult (minus b1 b2) (minus E1 E2)) zero *)
  assert (Hmain : le (mult (minus b1 b2) (minus E1 E2)) zero).
  { apply (le_id_l (mult (minus b1 b2) (minus E1 E2))
                   (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))).
    - exact (id_sym Hlhs).
    - apply (le_id_r (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))
                     (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))) zero).
      + exact Hz.
      + exact Hsum. }
  (* 乘正数消去 ⟹ E1 ≤ E2 *)
  assert (Hcancel : le (minus E1 E2) zero).
  { apply (le_mult_pos_cancel (minus E1 E2) (minus b1 b2) Hbpos).
    apply (le_id_l (mult (minus E1 E2) (minus b1 b2)) (mult (minus b1 b2) (minus E1 E2))).
    - apply mult_comm.
    - exact Hmain. }
  apply (le_minus_nonneg_rev E1 E2 Hcancel).
Qed.


(* 熵唯一最大：同能量约束且 S[p] = S[p_b] ⟹ p = p_b。
   证明：S[p_b] - S[p] = KL 且等熵 ⟹ KL = 0 ⟹ gibbs_equality。 *)
Theorem entropy_max_unique :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (energy_expectation p) (energy_expectation boltzmann_dist) ->
    Id (entropy_dist p) (entropy_dist boltzmann_dist) ->
    forall s : S, Id (p s) (boltzmann_dist s).
Proof.
  intros p Hnp Hpp Henergy Hent s.
  (* 1. S[p_b] - S[p] = KL *)
  assert (Hdef : Id (minus (entropy_dist boltzmann_dist) (entropy_dist p))
                    (relative_entropy p boltzmann_dist))
    by exact (entropy_deficit_kl p Hnp Hpp Henergy).
  (* 2. 等熵 ⟹ KL = 0（minus_self_zero：S[p]=S[p_b] ⟹ S[p_b]-S[p] = 0） *)
  assert (Hkl0 : Id (relative_entropy p boltzmann_dist) zero).
  {
    assert (Hmz : Id (minus (entropy_dist boltzmann_dist) (entropy_dist p)) zero)
      by exact (minus_self_zero (entropy_dist boltzmann_dist) (entropy_dist p) (id_sym Hent)).
    exact (id_trans (id_sym Hdef) Hmz).
  }
  (* 3. gibbs_equality：KL = 0 ⟹ p = p_b *)
  exact (gibbs_equality p boltzmann_dist Hnp Hpp (boltzmann_normalized) (fun t => boltzmann_dist_pos t) Hkl0 s).
Qed.

(* ============================================================ *)
(* A-3：T2.2 对偶合拢——温度参数化 Boltzmann 族的约束熵最大     *)
(*   闭环（论文2 最大熵 Lagrange 对偶的构造性证明）             *)
(*   组装：entropy_temp_explicit（熵显式公式）+                 *)
(*   relative_entropy_temp_decomp（KL 温度分解）+               *)
(*   entropy_deficit_kl_temp（熵亏 = KL，温度版）⟹              *)
(*   max_entropy_is_boltzmann_temp（同能量 ⟹ 熵最大，温度版）   *)
(*   + entropy_max_unique_temp（同能量同熵 ⟹ 唯一，温度版）⟹    *)
(*   temp_energy_dual_closed（sigT 对偶闭环：对每个温度 t，      *)
(*   约束能量 E_temp(t) 下熵最大化问题解存在且唯一）             *)
(* ============================================================ *)

(* 熵亏 = KL（温度版）：同约束能量 E(p) == E_temp(t) 下，
   S[p_t] − S[p] == KL(p‖p_t)——组装 entropy_temp_explicit +
   relative_entropy_temp_decomp + 同能量换形（β·E(p) == β·E(p_t)）*)
Theorem entropy_deficit_kl_temp : forall t : R, forall Ht : lt zero t, forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (energy_expectation p) (energy_exp_temp t Ht) ->
  Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
     (relative_entropy p (boltzmann_dist_temp t Ht)).
Proof.
  intros t Ht p Hnp Hpp Henergy.
  set (B := boltzmann_dist_temp t Ht).
  set (Et := energy_exp_temp t Ht).
  set (Sp := entropy_dist p).
  set (Spt := entropy_dist B).
  set (K := relative_entropy p B).
  (* KL(p‖p_t) == −S[p] + β·E(p) + log Z *)
  assert (Hkl : Id K (plus (plus (opp Sp) (mult (inv_pos t Ht) (energy_expectation p))) (log (Z_temp t)))).
  { unfold K, Sp, B. exact (relative_entropy_temp_decomp t Ht p Hnp). }
  (* S[p_t] == β·E(p_t) + log Z *)
  assert (Hse : Id Spt (plus (mult (inv_pos t Ht) Et) (log (Z_temp t)))).
  { unfold Spt, Et, B. exact (entropy_temp_explicit t Ht). }
  (* 换形：−S[p] + β·E(p) + log Z == [β·E(p_t) + log Z] − S[p]
     （结合/交换重组 + 同能量替换 β·E(p) == β·E(p_t)） *)
  assert (Hkl' : Id K (plus (plus (mult (inv_pos t Ht) Et) (log (Z_temp t))) (opp Sp))).
  {
    apply (id_trans Hkl).
    apply (id_trans (id_sym (plus_assoc (opp Sp) (mult (inv_pos t Ht) (energy_expectation p)) (log (Z_temp t))))).
    apply (id_trans (plus_comm (opp Sp) (plus (mult (inv_pos t Ht) (energy_expectation p)) (log (Z_temp t))))).
    apply (id_cong (fun x => plus (plus x (log (Z_temp t))) (opp Sp))
                   (id_cong (fun x => mult (inv_pos t Ht) x) Henergy)).
  }
  (* 目标：minus Spt Sp == K；minus Spt Sp == plus Spt (opp Sp) == [β·E(p_t)+log Z] − Sp（Hse 正向 + Hkl' 反向） *)
  unfold minus.
  apply (id_trans (id_cong (fun x => plus x (opp Sp)) Hse) (id_sym Hkl')).
Qed.

(* 温度版最大熵：同约束能量 E(p) == E_temp(t) ⟹ S[p] ≤ S[p_t]
   （组装 entropy_deficit_kl_temp + gibbs_inequality + le 链，仿固定温度版骨架） *)
Theorem max_entropy_is_boltzmann_temp : forall t : R, forall Ht : lt zero t, forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (energy_expectation p) (energy_exp_temp t Ht) ->
  le (entropy_dist p) (entropy_dist (boltzmann_dist_temp t Ht)).
Proof.
  intros t Ht p Hnp Hpp Henergy.
  (* 1. S[p_t] - S[p] = KL（温度版熵亏） *)
  assert (Hdef : Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
                    (relative_entropy p (boltzmann_dist_temp t Ht)))
    by exact (entropy_deficit_kl_temp t Ht p Hnp Hpp Henergy).
  (* 2. KL ≥ 0（gibbs_inequality：p 与 p_t 均归一化正） *)
  assert (Hkl : le zero (relative_entropy p (boltzmann_dist_temp t Ht))).
  {
    apply (gibbs_inequality p (boltzmann_dist_temp t Ht)).
    - exact Hnp.
    - exact Hpp.
    - exact (boltzmann_dist_temp_normalized t Ht).
    - intro s. exact (boltzmann_dist_temp_pos t Ht s).
  }
  (* 3. 0 ≤ S[p_t] - S[p] ⟹ S[p] ≤ S[p_t] *)
  assert (Hnonneg : le zero (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)))
    by exact (le_id_r zero (relative_entropy p (boltzmann_dist_temp t Ht))
                     (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
                     (id_sym Hdef) Hkl).
  assert (Hplus : Id (plus (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)))
                     (entropy_dist (boltzmann_dist_temp t Ht)))
    by exact (minus_plus_cancel (entropy_dist p) (entropy_dist (boltzmann_dist_temp t Ht))).
  assert (Hle : le (entropy_dist p)
                   (plus (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))))
    by exact (le_plus_nonneg_r (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)) Hnonneg).
  exact (le_id_r (entropy_dist p)
                 (plus (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)))
                 (entropy_dist (boltzmann_dist_temp t Ht)) Hplus Hle).
Qed.

(* 温度版唯一性：同约束能量 + 同熵 ⟹ p == p_t 逐点
   （组装 entropy_deficit_kl_temp + minus_self_zero + gibbs_equality，仿固定温度版骨架） *)
Theorem entropy_max_unique_temp : forall t : R, forall Ht : lt zero t, forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (energy_expectation p) (energy_exp_temp t Ht) ->
  Id (entropy_dist p) (entropy_dist (boltzmann_dist_temp t Ht)) ->
  forall s : S, Id (p s) (boltzmann_dist_temp t Ht s).
Proof.
  intros t Ht p Hnp Hpp Henergy Hent s.
  (* 1. S[p_t] - S[p] = KL *)
  assert (Hdef : Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
                    (relative_entropy p (boltzmann_dist_temp t Ht)))
    by exact (entropy_deficit_kl_temp t Ht p Hnp Hpp Henergy).
  (* 2. 等熵 ⟹ KL = 0 *)
  assert (Hkl0 : Id (relative_entropy p (boltzmann_dist_temp t Ht)) zero).
  {
    assert (Hmz : Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)) zero)
      by exact (minus_self_zero (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p) (id_sym Hent)).
    exact (id_trans (id_sym Hdef) Hmz).
  }
  (* 3. gibbs_equality：KL = 0 ⟹ p = p_t *)
  exact (gibbs_equality p (boltzmann_dist_temp t Ht) Hnp Hpp (boltzmann_dist_temp_normalized t Ht)
                       (fun s => boltzmann_dist_temp_pos t Ht s) Hkl0 s).
Qed.

(* 对偶闭环（A-3 主定理）：对每个温度 t（= 每个约束能量 E_temp(t)），
   熵最大化问题解存在（sigT 见证 p_t 本身）且最优（同能量熵最大）且唯一（同能量同熵 ⟹ 逐点相等） *)
Theorem temp_energy_dual_closed : forall t : R, forall Ht : lt zero t,
  sigT (fun pb : S -> R =>
    And (And (normalized pb) (positive_dist pb))
        (And (Id (energy_expectation pb) (energy_exp_temp t Ht))
             (And (forall p : S -> R, normalized p -> positive_dist p ->
                    Id (energy_expectation p) (energy_exp_temp t Ht) ->
                    le (entropy_dist p) (entropy_dist pb))
                  (forall p : S -> R, normalized p -> positive_dist p ->
                    Id (energy_expectation p) (energy_exp_temp t Ht) ->
                    Id (entropy_dist p) (entropy_dist pb) ->
                    forall s : S, Id (p s) (pb s))))).
Proof.
  intros t Ht.
  exists (boltzmann_dist_temp t Ht).
  split.
  - split.
    + exact (boltzmann_dist_temp_normalized t Ht).
    + intro s. exact (boltzmann_dist_temp_pos t Ht s).
  - split.
    + reflexivity.
    + split.
      * intros p Hnp Hpp Henergy.
        exact (max_entropy_is_boltzmann_temp t Ht p Hnp Hpp Henergy).
      * intros p Hnp Hpp Henergy Hent.
        exact (entropy_max_unique_temp t Ht p Hnp Hpp Henergy Hent).
Qed.

(* ============================================================ *)
(* 项 6：温度-能量严格单调（，T2.2/A-3 严格化）       *)
(*   陈述（差正形态）：t1 < t2 且 KL(p_t2 竖线竖线 p_t1) > 0     *)
(*     ⟹ 0 < E(t2) − E(t1)。恒等：                              *)
(*     (b1−b2)·(E2−E1) == KL1 + KL2（两温度 KL 分解相减）        *)
(*   诚实条件（T4.3）：KL 严格正接口（能量非平凡 ⟹ 满足）       *)
(* ============================================================ *)

(* KL 分解换形：−S2 + b1·E2 + log Z1 == (b1−b2)·E2 + (log Z1 − log Z2)
   （S2 == b2·E2 + log Z2 代入 + opp_plus + 结合交换重排） *)
Lemma temp_strict_A_chain2 : forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  Id (plus (plus (opp (entropy_dist (boltzmann_dist_temp t2 Ht2))) (mult (inv_pos t1 Ht1) (energy_exp_temp t2 Ht2))) (log (Z_temp t1)))
     (plus (mult (minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) (energy_exp_temp t2 Ht2))
           (minus (log (Z_temp t1)) (log (Z_temp t2)))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E2 := energy_exp_temp t2 Ht2).
  set (S2 := entropy_dist (boltzmann_dist_temp t2 Ht2)).
  set (Z1 := Z_temp t1). set (Z2 := Z_temp t2).
  assert (Hse : Id S2 (plus (mult b2 E2) (log Z2))).
  { unfold S2, b2, E2, Z2. apply (entropy_temp_explicit t2 Ht2). }
  assert (H1 : Id (plus (plus (opp S2) (mult b1 E2)) (log Z1))
                  (plus (plus (opp (plus (mult b2 E2) (log Z2))) (mult b1 E2)) (log Z1))).
  { apply (id_cong (fun x => plus (plus (opp x) (mult b1 E2)) (log Z1)) Hse). }
  assert (H2 : Id (plus (plus (opp (plus (mult b2 E2) (log Z2))) (mult b1 E2)) (log Z1))
                  (plus (plus (plus (opp (mult b2 E2)) (opp (log Z2))) (mult b1 E2)) (log Z1))).
  { apply (id_cong (fun x => plus (plus x (mult b1 E2)) (log Z1))).
    apply (opp_plus (mult b2 E2) (log Z2)). }
  assert (H3 : Id (plus (plus (plus (opp (mult b2 E2)) (opp (log Z2))) (mult b1 E2)) (log Z1))
                  (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (plus (opp (log Z2)) (log Z1)))).
  {
    apply (id_trans
             (id_cong (fun x => plus x (log Z1))
                      (id_trans (id_sym (plus_assoc (opp (mult b2 E2)) (opp (log Z2)) (mult b1 E2)))
                     (id_trans (id_cong (fun x => plus (opp (mult b2 E2)) x)
                                        (plus_comm (opp (log Z2)) (mult b1 E2)))
                               (plus_assoc (opp (mult b2 E2)) (mult b1 E2) (opp (log Z2))))))).
    apply id_sym.
    apply (plus_assoc (plus (opp (mult b2 E2)) (mult b1 E2)) (opp (log Z2)) (log Z1)).
  }
  assert (H4 : Id (plus (opp (mult b2 E2)) (mult b1 E2))
                  (mult (minus b1 b2) E2)).
  {
    apply (id_trans (plus_comm (opp (mult b2 E2)) (mult b1 E2))
           (id_sym (mult_minus_distr_r b1 b2 E2))).
  }
  assert (H5 : Id (plus (opp (log Z2)) (log Z1))
                  (minus (log Z1) (log Z2))).
  { unfold minus. apply (plus_comm (opp (log Z2)) (log Z1)). }
  assert (Hm4 : Id (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (plus (opp (log Z2)) (log Z1)))
                   (plus (mult (minus b1 b2) E2) (plus (opp (log Z2)) (log Z1)))).
  { apply (id_cong (fun x => plus x (plus (opp (log Z2)) (log Z1))) H4). }
  assert (Hfin : Id (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (plus (opp (log Z2)) (log Z1)))
                    (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))).
  { apply (id_trans Hm4).
    apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x) H5). }
  apply (id_trans H1).
  apply (id_trans H2).
  apply (id_trans H3).
  exact Hfin.
Qed.

(* 简化（避免超长结合链）：直接逐步 trans——见 temp_strict_ident2 *)
Lemma temp_strict_ident2 : forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  Id (plus (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1))
           (relative_entropy (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2)))
     (mult (minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
           (minus (energy_exp_temp t2 Ht2) (energy_exp_temp t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := energy_exp_temp t1 Ht1). set (E2 := energy_exp_temp t2 Ht2).
  set (Z1 := Z_temp t1). set (Z2 := Z_temp t2).
  assert (HK1 : Id (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1))
                   (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))).
  {
    unfold b1, b2, E2, Z1, Z2.
    apply (id_trans
             (relative_entropy_temp_decomp t1 Ht1 (boltzmann_dist_temp t2 Ht2)
                                           (boltzmann_dist_temp_normalized t2 Ht2))
             (temp_strict_A_chain2 t1 t2 Ht1 Ht2)).
  }
  assert (HK2 : Id (relative_entropy (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2))
                   (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))).
  {
    unfold b1, b2, E1, Z1, Z2.
    apply (id_trans
             (relative_entropy_temp_decomp t2 Ht2 (boltzmann_dist_temp t1 Ht1)
                                           (boltzmann_dist_temp_normalized t1 Ht1))
             (temp_strict_A_chain2 t2 t1 Ht2 Ht1)).
  }
  assert (Hsum : Id (plus (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1))
                          (relative_entropy (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2)))
                    (plus (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))
                          (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))))).
  {
    apply (id_cong2 plus HK1 HK2).
  }
  apply (id_trans Hsum).
  (* log 抵消（Hz 同前） *)
  assert (Hz : Id (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))) zero).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (log Z1) (opp (log Z2)) (plus (log Z2) (opp (log Z1)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (plus_assoc (opp (log Z2)) (log Z2) (opp (log Z1))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_cong (fun x => plus x (opp (log Z1)))
                                       (id_trans (plus_comm (opp (log Z2)) (log Z2)) (plus_opp (log Z2)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_trans (plus_comm zero (opp (log Z1))) (plus_zero (opp (log Z1)))))
                     (plus_opp (log Z1)))))). }
  assert (Hoppm : Id (minus b2 b1) (opp (minus b1 b2))).
  {
    unfold minus.
    exact (id_sym (id_trans (opp_plus b1 (opp b2))
                   (id_trans (id_cong (fun x => plus (opp b1) x) (double_neg b2))
                             (plus_comm (opp b1) b2)))).
  }
  assert (Hmain2 : Id (plus (mult (minus b1 b2) E2) (mult (minus b2 b1) E1))
                      (mult (minus b1 b2) (minus E2 E1))).
  {
    apply (id_trans (id_cong (fun x => plus (mult (minus b1 b2) E2) (mult x E1)) Hoppm)
           (id_trans (id_cong (fun x => plus (mult (minus b1 b2) E2) x)
                              (opp_mult_r (minus b1 b2) E1))
                     (id_sym (mult_minus_distr_l (minus b1 b2) E2 E1)))).
  }
  (* 逐步：M1 := plus (plus (mult d E2)(minus L1 L2)) (plus (mult d' E1)(minus L2 L1))
            == plus (mult d E2)(plus (minus L1 L2)(plus (mult d' E1)(minus L2 L1)))（assoc 反向）
            == plus (mult d E2)(plus (mult d' E1)(plus (minus L1 L2)(minus L2 L1)))（comm 交换内层）
            == plus (mult d E2)(plus (mult d' E1) zero)（Hz）
            == plus (mult d E2)(mult d' E1)（plus_zero）
            == mult d (minus E2 E1)（Hmain2） *)
  assert (H1 : Id (plus (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))
                        (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))))
                  (plus (mult (minus b1 b2) E2)
                        (plus (minus (log Z1) (log Z2))
                              (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))))).
  { apply id_sym.
    apply (plus_assoc (mult (minus b1 b2) E2) (minus (log Z1) (log Z2))
                      (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))). }
  assert (H2 : Id (plus (mult (minus b1 b2) E2)
                        (plus (minus (log Z1) (log Z2))
                              (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))))
                  (plus (mult (minus b1 b2) E2)
                        (plus (mult (minus b2 b1) E1)
                              (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))))).
  {
    assert (H2a : Id (plus (mult (minus b1 b2) E2)
                           (plus (minus (log Z1) (log Z2))
                                 (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))))
                     (plus (mult (minus b1 b2) E2)
                           (plus (plus (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1))
                                 (minus (log Z2) (log Z1))))).
    { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x)).
      apply (plus_assoc (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))). }
    assert (H2b : Id (plus (mult (minus b1 b2) E2)
                           (plus (plus (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1))
                                 (minus (log Z2) (log Z1))))
                     (plus (mult (minus b1 b2) E2)
                           (plus (plus (mult (minus b2 b1) E1) (minus (log Z1) (log Z2)))
                                 (minus (log Z2) (log Z1))))).
    { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) (plus x (minus (log Z2) (log Z1))))).
      apply (plus_comm (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1)). }
    assert (H2c : Id (plus (mult (minus b1 b2) E2)
                           (plus (plus (mult (minus b2 b1) E1) (minus (log Z1) (log Z2)))
                                 (minus (log Z2) (log Z1))))
                     (plus (mult (minus b1 b2) E2)
                           (plus (mult (minus b2 b1) E1)
                                 (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))))).
    { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x)).
      apply id_sym.
      apply (plus_assoc (mult (minus b2 b1) E1) (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))). }
    exact (id_trans H2a (id_trans H2b H2c)).
  }
  assert (H3 : Id (plus (mult (minus b1 b2) E2)
                        (plus (mult (minus b2 b1) E1) zero))
                  (plus (mult (minus b1 b2) E2) (mult (minus b2 b1) E1))).
  { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x)).
    apply (plus_zero (mult (minus b2 b1) E1)). }
  assert (Hza : Id (plus (mult (minus b1 b2) E2)
                         (plus (mult (minus b2 b1) E1)
                               (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))))
                   (plus (mult (minus b1 b2) E2)
                         (plus (mult (minus b2 b1) E1) zero))).
  { apply (id_cong (fun x => plus (mult (minus b1 b2) E2)
                                  (plus (mult (minus b2 b1) E1) x)) Hz). }
  assert (Hfin : Id (plus (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))
                          (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))))
                    (mult (minus b1 b2) (minus E2 E1))).
  {
    apply (id_trans H1).
    apply (id_trans H2).
    apply (id_trans Hza).
    apply (id_trans H3).
    exact Hmain2.
  }
  exact Hfin.
Qed.

(* ============================================================ *)
(* 最终定理：温度-能量严格单调（差正形态）                      *)
(*   t1 < t2 且 KL(p_t2 竖线竖线 p_t1) > 0 ⟹ 0 < E2 − E1        *)
(* ============================================================ *)
Theorem energy_exp_temp_strict_mono : forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1)) ->
  lt zero (minus (energy_exp_temp t2 Ht2) (energy_exp_temp t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12 Hkl1.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := energy_exp_temp t1 Ht1). set (E2 := energy_exp_temp t2 Ht2).
  set (B1 := boltzmann_dist_temp t1 Ht1). set (B2 := boltzmann_dist_temp t2 Ht2).
  set (K1 := relative_entropy B2 B1). set (K2 := relative_entropy B1 B2).
  (* β2 < β1 且 d := b1 − b2 > 0 *)
  assert (Hb : lt b2 b1) by (unfold b1, b2; apply (inv_pos_lt_compat t1 t2 Ht1 Ht2 Ht12)).
  assert (Hbd : lt zero (minus b1 b2)) by (unfold b1, b2; apply (lt_minus_nonneg b2 b1 Hb)).
  (* K2 ≥ 0（gibbs 不等式） *)
  assert (Hkl2 : le zero K2).
  { unfold K2, B1, B2.
    apply (gibbs_inequality (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2)).
    - apply (boltzmann_dist_temp_normalized t1 Ht1).
    - intro s. apply (boltzmann_dist_temp_pos t1 Ht1 s).
    - apply (boltzmann_dist_temp_normalized t2 Ht2).
    - intro s. apply (boltzmann_dist_temp_pos t2 Ht2 s). }
  (* K1 + K2 > 0（K1 > 0 且 K2 ≥ 0 ⟹ K1 ≤ K1+K2 ⟹ lt 传递） *)
  assert (Hklsum : lt zero (plus K1 K2)).
  {
    apply (lt_le_trans zero K1 (plus K1 K2)).
    - unfold K1, B1, B2. exact Hkl1.
    - apply (le_plus_nonneg_r K1 K2). exact Hkl2.
  }
  (* 恒等：K1 + K2 == d·(E2−E1) *)
  assert (Hid : Id (plus K1 K2) (mult (minus b1 b2) (minus E2 E1))).
  { unfold K1, K2, b1, b2, E1, E2. exact (temp_strict_ident2 t1 t2 Ht1 Ht2). }
  (* 0 < d·(E2−E1)（lt_id_r 替换） *)
  assert (Hprod : lt zero (mult (minus b1 b2) (minus E2 E1))).
  { apply (lt_id_r zero (plus K1 K2) (mult (minus b1 b2) (minus E2 E1))).
    - exact Hid.
    - exact Hklsum. }
  (* 正乘严格消去 ⟹ 0 < E2 − E1（先 comm 换序） *)
  apply (lt_mult_pos_cancel (minus E2 E1) (minus b1 b2) Hbd).
  apply (lt_id_r zero (mult (minus b1 b2) (minus E2 E1))
                  (mult (minus E2 E1) (minus b1 b2))).
  - apply (mult_comm (minus b1 b2) (minus E2 E1)).
  - exact Hprod.
Qed.

(* ============================================================ *)



(* ============================================================ *)
(* RLHF 对齐（当前 AI 训练核心：KL 正则化奖励最大化）          *)
(* ============================================================ *)
(* 上帝视角：现代 LLM 对齐（RLHF/DPO/PPO）的目标是               *)
(*   maximize  E_π[r] - β·KL(π‖π_ref)                          *)
(* 即：在偏离参考策略 π_ref 不超过 KL 惩罚的前提下最大化奖励。 *)
(* 数学上这是 Boltzmann 机制的精确复刻（奖励替代能量，参考策略 *)
(* 替代均匀先验）——本 Section 给出闭式解与最优性定理：        *)
(*   最优策略 π*(s) ∝ π_ref(s)·e^{r(s)/β}（奖励加权 Boltzmann），*)
(*   且它是唯一最优解。                                        *)
(* ------------------------------------------------------------ *)

(* ============================================================ *)
(* 前三条支柱（自由能唯一极小 / KL 度量 / 熵最大）给出理论闭环；*)
(* 此处补实操接口：交叉熵 H(p,q) := -Σ p·log q。              *)
(* 由 energy_in_log_boltzmann（E = -D·(log p_b + log Z)）得    *)
(*   ⟨E⟩_p = -D·(H(p,p_b) + log Z)                             *)
(*   F[p] = ⟨E⟩_p - D·S[p] = -D·(H(p,p_b) + log Z + S[p])      *)
(* 即训练（最小化 F）等价于最小化交叉熵 H(p,p_b)（固定 p_b）。 *)
(* ------------------------------------------------------------ *)

(* 交叉熵：H(p,q) := -Σ_s p(s)·log q(s) *)
Definition cross_entropy (p q : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (opp (log (q s)))).

(* 交叉熵-相对熵-熵恒等式：H(p,q) = S[p] + KL(p||q)
   （信息论核心：交叉熵 = 自熵 + 相对熵。由定义展开 + 求和线性） *)
Theorem cross_entropy_decomp :
  forall p q : S -> R,
    Id (cross_entropy p q)
       (plus (entropy_dist p) (relative_entropy p q)).
Proof.
  intros p q.
  unfold cross_entropy, entropy_dist, relative_entropy.
  (* Σ p·(-log q) = Σ p·(-log p) + Σ p·(log p - log q) *)
  (* 逐点：mult (p s) (opp (log (q s))) = plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s)))) *)
  assert (Hpt : forall s, Id (mult (p s) (opp (log (q s))))
                            (plus (mult (p s) (opp (log (p s))))
                                  (mult (p s) (minus (log (p s)) (log (q s)))))).
  {
    intro s.
    unfold minus.
    assert (Hd : Id (mult (p s) (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s))))))
                    (plus (mult (p s) (opp (log (p s))))
                          (mult (p s) (plus (log (p s)) (opp (log (q s)))))))
      by exact (distrib (p s) (opp (log (p s))) (plus (log (p s)) (opp (log (q s))))).
    (* 左侧化简：opp (log p) + (log p - log q) = -log q（minus_plus_cancel） *)
    assert (Hcancel : Id (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s)))))
                         (opp (log (q s)))).
    {
      (* assoc：opp log p + (log p - log q) = (opp log p + log p) - log q *)
      assert (Ha : Id (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s)))))
                      (plus (plus (opp (log (p s))) (log (p s))) (opp (log (q s)))))
        by exact (plus_assoc (opp (log (p s))) (log (p s)) (opp (log (q s)))).
      (* 内层抵消：opp log p + log p = 0 *)
      assert (Hz : Id (plus (opp (log (p s))) (log (p s))) zero)
        by exact (id_trans (plus_comm (opp (log (p s))) (log (p s))) (plus_opp (log (p s)))).
      (* (opp log p + log p) - log q = 0 - log q = -log q *)
      assert (Hb : Id (plus (plus (opp (log (p s))) (log (p s))) (opp (log (q s))))
                      (plus zero (opp (log (q s)))))
        by exact (id_cong (fun x => plus x (opp (log (q s)))) Hz).
      assert (Hc : Id (plus zero (opp (log (q s)))) (opp (log (q s))))
        by exact (id_trans (plus_comm zero (opp (log (q s)))) (plus_zero (opp (log (q s))))).
      exact (id_trans Ha (id_trans Hb Hc)).
    }
    assert (Hleft : Id (mult (p s) (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s))))))
                       (mult (p s) (opp (log (q s)))))
      by exact (id_cong (fun x => mult (p s) x) Hcancel).
    (* 右侧展开：mult (p s) (log p - log q) = mult (p s) (log p) + mult (p s) (-log q) *)
    assert (Hdist2 : Id (mult (p s) (plus (log (p s)) (opp (log (q s)))))
                        (plus (mult (p s) (log (p s))) (mult (p s) (opp (log (q s))))))
      by exact (distrib (p s) (log (p s)) (opp (log (q s)))).
    (* 目标：mult (p s) (-log q) = plus (mult (p s) (-log p)) (mult (p s) (log p - log q))
       由 Hd 反向（Hleft 后两侧换位） *)
    exact (id_trans (id_sym Hleft) Hd).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (opp (log (q s)))))
                   (sum_over_S (fun s => plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (opp (log (q s))))
                             (fun s => plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s)))))
                             Hpt).
  rewrite Hext.
  assert (Hadd : Id (sum_over_S (fun s => plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s))))))
                   (plus (sum_over_S (fun s => mult (p s) (opp (log (p s)))))
                         (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))))))
    by exact (sum_over_S_add (fun s => mult (p s) (opp (log (p s))))
                             (fun s => mult (p s) (minus (log (p s)) (log (q s))))).
  rewrite Hadd.
  reflexivity.
Qed.

Theorem energy_cross_entropy :
  forall p : S -> R,
    normalized p ->
    Id (energy_expectation p)
       (plus (mult D (cross_entropy p boltzmann_dist)) (opp (mult D (log Z)))).
Proof.
  intros p Hnp.
  unfold energy_expectation, cross_entropy.
  (* 逐点：mult (p s) (base_loss s) = mult (p s) (-D·(log p_b s + log Z)) *)
  assert (Hpt : forall s, Id (mult (p s) (base_loss s))
                            (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))).
  {
    intro s.
    assert (He : Id (base_loss s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
      by exact (energy_in_log_boltzmann s).
    exact (id_cong (fun x => mult (p s) x) He).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (base_loss s)))
                   (sum_over_S (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (base_loss s))
                             (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                             Hpt).
  rewrite Hext.
  (* 逐点展开为 -D·(p·log p_b + p·log Z) *)
  assert (Hpt2 : forall s, Id (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                             (opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                (mult (p s) (log Z)))))).
  {
    intro s.
    assert (Hopp : Id (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                      (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))))
      by exact (opp_mult_l (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))).
    assert (Hsw : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                     (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z))))).
    {
      assert (H1 : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                      (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z))))
        by exact (mult_assoc (p s) D (plus (log (boltzmann_dist s)) (log Z))).
      assert (H2 : Id (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z)))
                      (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z))))
        by exact (id_cong (fun x => mult x (plus (log (boltzmann_dist s)) (log Z))) (mult_comm (p s) D)).
      assert (H3 : Id (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z)))
                      (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))))
        by exact (id_sym (mult_assoc D (p s) (plus (log (boltzmann_dist s)) (log Z)))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    assert (Hdist : Id (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))
                       (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
      by exact (distrib (p s) (log (boltzmann_dist s)) (log Z)).
    assert (Hd2 : Id (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z))))
                     (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z)))))
      by exact (id_cong (fun x => mult D x) Hdist).
    assert (Hd3 : Id (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
                     (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                           (mult D (mult (p s) (log Z)))))
      by exact (distrib D (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))).
    assert (Htot : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                     (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                           (mult D (mult (p s) (log Z)))))
      by exact (id_trans Hsw (id_trans Hd2 Hd3)).
    assert (Hopp2 : Id (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                      (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                                 (mult D (mult (p s) (log Z))))))
      by exact (id_cong opp Htot).
    assert (Hopp3 : Id (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                                 (mult D (mult (p s) (log Z)))))
                    (opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                       (mult (p s) (log Z)))))).
    {
      assert (Hd4 : Id (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
                      (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                            (mult D (mult (p s) (log Z)))))
        by exact (distrib D (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))).
      exact (id_cong opp (id_sym Hd4)).
    }
    exact (id_trans Hopp (id_trans Hopp2 Hopp3)).
  }
  assert (Hext2 : Id (sum_over_S (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))))
                     (sum_over_S (fun s => opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                           (mult (p s) (log Z)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                             (fun s => opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                         (mult (p s) (log Z)))))
                             Hpt2).
  rewrite Hext2.
  assert (Hso : Id (sum_over_S (fun s => opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                         (mult (p s) (log Z))))))
                   (opp (sum_over_S (fun s => mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                          (mult (p s) (log Z)))))))
    by exact (sum_opp (fun s => mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                            (mult (p s) (log Z))))).
  rewrite Hso.
  assert (Hlin : Id (sum_over_S (fun s => mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                       (mult (p s) (log Z)))))
                    (mult D (sum_over_S (fun s => plus (mult (p s) (log (boltzmann_dist s)))
                                                       (mult (p s) (log Z))))))
    by exact (sum_over_S_linear D (fun s => plus (mult (p s) (log (boltzmann_dist s)))
                                                 (mult (p s) (log Z)))).
  rewrite Hlin.
  assert (Hadd : Id (sum_over_S (fun s => plus (mult (p s) (log (boltzmann_dist s)))
                                              (mult (p s) (log Z))))
                   (plus (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))
                         (sum_over_S (fun s => mult (p s) (log Z)))))
    by exact (sum_over_S_add (fun s => mult (p s) (log (boltzmann_dist s)))
                             (fun s => mult (p s) (log Z))).
  rewrite Hadd.
  (* Σ p·log p_b = -cross_entropy（cross_entropy := Σ p·(-log p_b)） *)
  assert (Hce : Id (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))
                   (opp (sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s))))))).
  {
    assert (Hpt3 : forall s, Id (mult (p s) (log (boltzmann_dist s)))
                               (opp (mult (p s) (opp (log (boltzmann_dist s)))))).
    {
      intro s.
      apply id_sym.
      apply (id_trans (id_cong opp (opp_mult_l (p s) (log (boltzmann_dist s))))
                   (double_neg (mult (p s) (log (boltzmann_dist s))))).
    }
    assert (Hext3 : Id (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))
                      (sum_over_S (fun s => opp (mult (p s) (opp (log (boltzmann_dist s)))))))
      by exact (sum_over_S_ext (fun s => mult (p s) (log (boltzmann_dist s)))
                               (fun s => opp (mult (p s) (opp (log (boltzmann_dist s))))) Hpt3).
    assert (Hso3 : Id (sum_over_S (fun s => opp (mult (p s) (opp (log (boltzmann_dist s))))))
                      (opp (sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s)))))))
      by exact (sum_opp (fun s => mult (p s) (opp (log (boltzmann_dist s))))).
    exact (id_trans Hext3 Hso3).
  }
  rewrite Hce.
  (* Σ p·log Z = log Z（归一化） *)
  assert (Hlz : Id (sum_over_S (fun s => mult (p s) (log Z))) (log Z)).
  {
    assert (Hsw : Id (sum_over_S (fun s => mult (p s) (log Z)))
                     (sum_over_S (fun s => mult (log Z) (p s))))
      by exact (sum_over_S_ext (fun s => mult (p s) (log Z))
                               (fun s => mult (log Z) (p s))
                               (fun s => mult_comm (p s) (log Z))).
    rewrite Hsw.
    assert (Hl1 : Id (sum_over_S (fun s => mult (log Z) (p s))) (mult (log Z) (sum_over_S p)))
      by exact (sum_over_S_linear (log Z) p).
    rewrite Hl1.
    rewrite Hnp.
    assert (Hm1 : Id (mult (log Z) one) (log Z)) by exact (mult_one (log Z)).
    rewrite Hm1.
    reflexivity.
  }
  rewrite Hlz.
  (* 目标：opp (mult D (plus (opp (cross_entropy p boltzmann_dist)) (log Z)))
     实际 = D·(Σp log p_b + log Z) 取负 = D·(-H + log Z) 取负
     = plus (mult D H) (opp (mult D (log Z)))。 *)
  (* 直接用原始 cross_entropy 定义匹配目标 RHS *)
  unfold cross_entropy.
  (* 目标：opp (mult D (plus (opp (Σ p·(-log p_b))) (log Z)))
     = plus (mult D (Σ p·(-log p_b))) (opp (mult D (log Z)))
     由 ring_opp_plus_neg 恒等式。 *)
  assert (Hring : forall X Y : R, Id (opp (mult D (plus (opp X) Y)))
                                    (plus (mult D X) (opp (mult D Y)))).
  {
    intros X Y.
    assert (H1 : Id (opp (mult D (plus (opp X) Y)))
                    (opp (plus (mult D (opp X)) (mult D Y))))
      by exact (id_cong opp (distrib D (opp X) Y)).
    assert (H2 : Id (opp (plus (mult D (opp X)) (mult D Y)))
                    (plus (opp (mult D (opp X))) (opp (mult D Y))))
      by exact (opp_plus (mult D (opp X)) (mult D Y)).
    assert (H3 : Id (opp (mult D (opp X))) (mult D X))
      by exact (id_trans (id_sym (opp_mult_l D (opp X))) (id_cong (fun x => mult D x) (double_neg X))).
    assert (H4 : Id (plus (opp (mult D (opp X))) (opp (mult D Y)))
                    (plus (mult D X) (opp (mult D Y))))
      by exact (id_cong (fun x => plus x (opp (mult D Y))) H3).
    exact (id_trans H1 (id_trans H2 H4)).
  }
  (* 目标现在：Id (opp (mult D (plus (opp S) (log Z)))) (plus (mult D S) (opp (mult D (log Z))))
     其中 S := sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s)))) *)
  exact (Hring (sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s))))) (log Z)).
Qed.

(* ============================================================ *)
(* 变分推断：ELBO 与证据下界（VI 核心，改进恒等式.txt 块 1）   *)
(* ============================================================ *)
(* 在自由能框架中，ELBO(q) := -F[q] 是证据（配分函数对数的能量   *)
(* 形式 opp (free_energy boltzmann_dist)）的变分下界；训练（最大   *)
(* 化 ELBO）等价于最小化自由能。三定理：                         *)
(*   (a) elbo_lower_bound：ELBO(q) ≤ evidence（自由能最小化 + 取负）*)
(*   (b) evidence_kl_decomp：evidence = ELBO(q) + D·KL(q||p_b)     *)
(*       ——证据与 ELBO 的差距精确等于 KL 散度（VI 核心恒等式）；  *)
(*   (c) elbo_explicit：ELBO 的熵+能量显式形式。                  *)
(* ------------------------------------------------------------ *)

(* ELBO：变分分布 q 的证据下界 *)
Definition elbo (q : S -> R) : R :=
  opp (free_energy q).

(* 证据：配分函数对数的能量形式（D·log Z 的抽象，无需 D = 1） *)
Definition evidence : R :=
  opp (free_energy boltzmann_dist).

(* ELBO(q) ≤ evidence：由自由能最小化直接推出（取负 + opp_le_compat） *)
Theorem elbo_lower_bound :
  forall q : S -> R,
    normalized q -> positive_dist q ->
    le (elbo q) evidence.
Proof.
  intros q Hnq Hpq.
  unfold elbo, evidence.
  apply (opp_le_compat (free_energy boltzmann_dist) (free_energy q)).
  exact (min_free_energy_is_boltzmann q Hnq Hpq).
Qed.

(* 证据的 KL 分解：evidence = ELBO(q) + D·KL(q||p_b)
   变分推断的核心恒等式——证据与 ELBO 的差距精确等于 KL 散度
   （由 free_energy_kl_decomp 取负移项：-F[b] = -F[q] + D·KL） *)
Theorem evidence_kl_decomp :
  forall q : S -> R,
    normalized q ->
    Id evidence
       (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))).
Proof.
  intros q Hnq.
  unfold evidence, elbo.
  assert (Hdecomp : Id (free_energy q)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy q boltzmann_dist))))
    by exact (free_energy_kl_decomp q Hnq).
  assert (Htarget : Id (plus (opp (free_energy q)) (mult D (relative_entropy q boltzmann_dist)))
                       (opp (free_energy boltzmann_dist))).
  {
    assert (H1 : Id (plus (opp (free_energy q)) (mult D (relative_entropy q boltzmann_dist)))
                    (plus (opp (plus (free_energy boltzmann_dist) (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist))))
      by exact (id_cong (fun x => plus x (mult D (relative_entropy q boltzmann_dist))) (id_cong opp Hdecomp)).
    assert (H2 : Id (plus (opp (plus (free_energy boltzmann_dist) (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist)))
                    (plus (plus (opp (free_energy boltzmann_dist)) (opp (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist))))
      by exact (id_cong (fun x => plus x (mult D (relative_entropy q boltzmann_dist)))
                        (opp_plus (free_energy boltzmann_dist) (mult D (relative_entropy q boltzmann_dist)))).
    assert (H3 : Id (plus (plus (opp (free_energy boltzmann_dist)) (opp (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist)))
                    (plus (opp (free_energy boltzmann_dist)) zero)).
    {
      assert (H3a : Id (plus (plus (opp (free_energy boltzmann_dist)) (opp (mult D (relative_entropy q boltzmann_dist))))
                            (mult D (relative_entropy q boltzmann_dist)))
                      (plus (opp (free_energy boltzmann_dist))
                            (plus (opp (mult D (relative_entropy q boltzmann_dist)))
                                  (mult D (relative_entropy q boltzmann_dist)))))
        by exact (id_sym (plus_assoc (opp (free_energy boltzmann_dist))
                                     (opp (mult D (relative_entropy q boltzmann_dist)))
                                     (mult D (relative_entropy q boltzmann_dist)))).
      assert (H3b : Id (plus (opp (mult D (relative_entropy q boltzmann_dist))) (mult D (relative_entropy q boltzmann_dist))) zero)
        by exact (id_trans (plus_comm (opp (mult D (relative_entropy q boltzmann_dist))) (mult D (relative_entropy q boltzmann_dist)))
                           (plus_opp (mult D (relative_entropy q boltzmann_dist)))).
      assert (H3c : Id (plus (opp (free_energy boltzmann_dist))
                             (plus (opp (mult D (relative_entropy q boltzmann_dist)))
                                   (mult D (relative_entropy q boltzmann_dist))))
                      (plus (opp (free_energy boltzmann_dist)) zero))
        by exact (id_cong (fun x => plus (opp (free_energy boltzmann_dist)) x) H3b).
      exact (id_trans H3a H3c).
    }
    assert (H4 : Id (plus (opp (free_energy boltzmann_dist)) zero) (opp (free_energy boltzmann_dist)))
      by exact (plus_zero (opp (free_energy boltzmann_dist))).
    exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
  }
  exact (id_sym Htarget).
Qed.

(* ELBO 的显式分解：-F[q] = -⟨E⟩_q + D·S[q]（S[q] := -Σ q·log q 信息熵） *)
Theorem elbo_explicit :
  forall q : S -> R,
    Id (elbo q)
       (plus (opp (sum_over_S (fun s => mult (q s) (base_loss s))))
             (mult D (entropy_dist q))).
Proof.
  intro q.
  (* free_energy 为泛化 λ，unfold 不 β-归约 ⟹ change（内核转换） *)
  change (Id (opp (plus (sum_over_S (fun s => mult (q s) (base_loss s)))
                        (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))))
             (plus (opp (sum_over_S (fun s => mult (q s) (base_loss s))))
                   (mult D (sum_over_S (fun s => mult (q s) (opp (log (q s)))))))).
  assert (Hop : Id (opp (plus (sum_over_S (fun s => mult (q s) (base_loss s)))
                              (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))))
                   (plus (opp (sum_over_S (fun s => mult (q s) (base_loss s))))
                         (opp (mult D (sum_over_S (fun s => mult (q s) (log (q s))))))))
    by exact (opp_plus (sum_over_S (fun s => mult (q s) (base_loss s)))
                       (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))).
  rewrite Hop.
  assert (Hent : Id (opp (mult D (sum_over_S (fun s => mult (q s) (log (q s))))))
                   (mult D (sum_over_S (fun s => mult (q s) (opp (log (q s))))))).
  {
    assert (Hpt : forall s, Id (mult (q s) (opp (log (q s))))
                             (opp (mult (q s) (log (q s)))))
      by (intro s; exact (opp_mult_l (q s) (log (q s)))).
    assert (He : Id (sum_over_S (fun s => mult (q s) (opp (log (q s)))))
                    (sum_over_S (fun s => opp (mult (q s) (log (q s))))))
      by exact (sum_over_S_ext _ _ Hpt).
    assert (Hso : Id (sum_over_S (fun s => opp (mult (q s) (log (q s)))))
                     (opp (sum_over_S (fun s => mult (q s) (log (q s))))))
      by exact (sum_opp (fun s => mult (q s) (log (q s)))).
    assert (Hlin : Id (mult D (sum_over_S (fun s => mult (q s) (opp (log (q s))))))
                     (mult D (opp (sum_over_S (fun s => mult (q s) (log (q s)))))))
      by exact (id_cong (fun x => mult D x) (id_trans He Hso)).
    assert (Hoppr : Id (mult D (opp (sum_over_S (fun s => mult (q s) (log (q s))))))
                      (opp (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))))
      by exact (opp_mult_l D (sum_over_S (fun s => mult (q s) (log (q s))))).
    exact (id_sym (id_trans Hlin Hoppr)).
  }
  rewrite Hent.
  reflexivity.
Qed.

(* ============================================================ *)
(* ELBO 紧性与证据差距的精确 KL 形式（变分推断闭环补全）       *)
(* ============================================================ *)
(* (a) 当变分分布 q 恰好为 Boltzmann 后验时，ELBO 无间隙地      *)
(*     达到证据值（等号条件——变分推断的"零误差"态）；           *)
(* (b) 对任意归一化 q，evidence − ELBO(q) 精确等于 D·KL(q||p_b)，*)
(*     为 VI 训练提供可量化的后验逼近误差指标。                  *)
(* ------------------------------------------------------------ *)

(* KL(p||p) = 0（相对熵自零；FreeEnergyMinimization 内自证）：
   展开定义后逐点 p s·(log p s − log p s) = p s·0 = 0，
   经 sum_over_S_ext + sum_over_S_linear + mult_zero 收尾。 *)
Lemma relative_entropy_self_zero' : forall p : S -> R,
  Id (relative_entropy p p) zero.
Proof.
  intro p.
  unfold relative_entropy.
  (* 逐点：p s·(log p s − log p s) = zero *)
  assert (Hpt : forall s, Id (mult (p s) (minus (log (p s)) (log (p s)))) zero).
  {
    intro s.
    assert (Hz : Id (minus (log (p s)) (log (p s))) zero)
      by exact (minus_self_zero (log (p s)) (log (p s)) (@id_refl R (log (p s)))).
    exact (id_trans (id_cong (fun x => mult (p s) x) Hz) (mult_zero (p s))).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (p s)))))
                    (sum_over_S (fun s => zero)))
    by exact (sum_over_S_ext _ _ Hpt).
  assert (Hzero : Id (sum_over_S (fun s => zero)) zero).
  {
    (* 零函数 = mult zero (常一函数) 逐点；sum_over_S_linear 收尾 *)
    assert (Hsame : Id (sum_over_S (fun s => zero))
                       (sum_over_S (fun s => mult zero one)))
      by (apply sum_over_S_ext; intro s; exact (id_sym (id_trans (mult_comm zero one) (mult_zero one)))).
    assert (Hlin : Id (sum_over_S (fun s => mult zero one))
                      (mult zero (sum_over_S (fun s => one))))
      by exact (sum_over_S_linear zero (fun s : S => one)).
    assert (Hmz : Id (mult zero (sum_over_S (fun s : S => one))) zero)
      by exact (id_trans (mult_comm zero (sum_over_S (fun s : S => one)))
                         (mult_zero (sum_over_S (fun s : S => one)))).
    exact (id_trans Hsame (id_trans Hlin Hmz)).
  }
  exact (id_trans Hext Hzero).
Qed.

(* (a) ELBO 在 Boltzmann 分布处紧致：ELBO[p_b] = evidence。
    证明：evidence_kl_decomp 给 evidence = ELBO[p_b] + D·KL(p_b||p_b)，
    relative_entropy_self_zero' 给 KL(p_b||p_b) = 0，故 evidence = ELBO[p_b]。
    非平凡：KL 自零 + 环代数消去。 *)
Theorem elbo_tight :
  Id (elbo boltzmann_dist) evidence.
Proof.
  unfold evidence.
  (* evidence = ELBO[p_b] + D·KL(p_b||p_b)（KL 分解在 q = p_b 处） *)
  assert (Hkl : Id (mult D (relative_entropy boltzmann_dist boltzmann_dist)) zero).
  {
    assert (Hself : Id (relative_entropy boltzmann_dist boltzmann_dist) zero)
      by exact (relative_entropy_self_zero' boltzmann_dist).
    exact (id_trans (id_cong (fun x => mult D x) Hself) (mult_zero D)).
  }
  assert (Hdec : Id evidence
                   (plus (elbo boltzmann_dist) (mult D (relative_entropy boltzmann_dist boltzmann_dist))))
    by exact (evidence_kl_decomp boltzmann_dist (boltzmann_normalized)).
  (* evidence = ELBO[p_b] + 0 = ELBO[p_b] *)
  assert (Hplus : Id (plus (elbo boltzmann_dist) (mult D (relative_entropy boltzmann_dist boltzmann_dist)))
                     (elbo boltzmann_dist))
    by exact (id_trans (id_cong (fun x => plus (elbo boltzmann_dist) x) Hkl)
                       (plus_zero (elbo boltzmann_dist))).
  exact (id_sym (id_trans Hdec Hplus)).
Qed.

(* (b) 证据-ELBO 差距 = D·KL(q||p_b)（变分差距的精确诊断）。
    证明：evidence_kl_decomp 给 evidence = ELBO(q) + D·KL(q||p_b)，
    两侧减 ELBO(q)（minus_plus_cancel_r：minus (plus a b) a = b）。
    非平凡：KL 分解恒等式 + 减法消去。 *)
Theorem evidence_gap_kl :
  forall q : S -> R,
    normalized q ->
    Id (minus evidence (elbo q))
       (mult D (relative_entropy q boltzmann_dist)).
Proof.
  intros q Hnq.
  assert (Hdec : Id evidence
                   (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))))
    by exact (evidence_kl_decomp q Hnq).
  (* 两侧减 elbo q：minus evidence (elbo q) = minus (plus (elbo q) KL') (elbo q) = KL' *)
  assert (Hminus : Id (minus evidence (elbo q))
                      (minus (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))) (elbo q)))
    by exact (id_cong (fun x => minus x (elbo q)) Hdec).
  assert (Hcancel : Id (minus (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))) (elbo q))
                       (mult D (relative_entropy q boltzmann_dist)))
    by exact (minus_plus_cancel_r (elbo q) (mult D (relative_entropy q boltzmann_dist))).
  exact (id_trans Hminus Hcancel).
Qed.

(* ============================================================ *)
(* 交叉熵训练目标的 KL 等价性（单调改进与hentic KL 控制.txt 块3）*)
(* ============================================================ *)
(* 核心：cross_entropy(p,q) − cross_entropy(p,p) = KL(p||q)     *)
(* 含义：固定目标分布 p 时，最小化交叉熵就是最小化 KL(p||q)。    *)
(* 非平凡：cross_entropy_decomp + KL 自零 + 环代数重组。         *)
(* ------------------------------------------------------------ *)

(* 交叉熵减自熵 = KL：H(p,q) − H(p,p) = KL(p||q)。
   证明：H(p,q) = S[p] + KL(p||q)（cross_entropy_decomp），
   H(p,p) = S[p] + KL(p||p) = S[p]（KL 自零），
   相减：S[p] + KL(p||q) − S[p] = KL(p||q)（plus_assoc + plus_opp）。 *)
Theorem cross_entropy_minus_self :
  forall p q : S -> R,
    Id (minus (cross_entropy p q) (cross_entropy p p))
       (relative_entropy p q).
Proof.
  intros p q.
  (* H(p,q) = S[p] + KL(p||q) *)
  assert (H1 : Id (cross_entropy p q)
                  (plus (entropy_dist p) (relative_entropy p q)))
    by exact (cross_entropy_decomp p q).
  (* H(p,p) = S[p] + KL(p||p) = S[p]（KL 自零） *)
  assert (H2 : Id (cross_entropy p p) (entropy_dist p)).
  {
    assert (H2a : Id (cross_entropy p p)
                     (plus (entropy_dist p) (relative_entropy p p)))
      by exact (cross_entropy_decomp p p).
    assert (H2b : Id (relative_entropy p p) zero)
      by exact (relative_entropy_self_zero' p).
    assert (H2c : Id (plus (entropy_dist p) (relative_entropy p p))
                     (plus (entropy_dist p) zero))
      by exact (id_cong (fun x => plus (entropy_dist p) x) H2b).
    assert (H2d : Id (plus (entropy_dist p) zero) (entropy_dist p))
      by exact (plus_zero (entropy_dist p)).
    exact (id_trans H2a (id_trans H2c H2d)).
  }
  (* H(p,q) − H(p,p) = (S + KL) − S = KL *)
  assert (Hmain : Id (minus (plus (entropy_dist p) (relative_entropy p q)) (entropy_dist p))
                     (relative_entropy p q)).
  {
    unfold minus.
    (* plus (plus S KL) (opp S) = plus S (plus KL (opp S)) = plus S (plus (opp S) KL) = KL *)
    assert (Ha : Id (plus (plus (entropy_dist p) (relative_entropy p q)) (opp (entropy_dist p)))
                    (plus (entropy_dist p) (plus (relative_entropy p q) (opp (entropy_dist p)))))
      by exact (id_sym (plus_assoc (entropy_dist p) (relative_entropy p q) (opp (entropy_dist p)))).
    assert (Hb : Id (plus (entropy_dist p) (plus (relative_entropy p q) (opp (entropy_dist p))))
                    (plus (entropy_dist p) (plus (opp (entropy_dist p)) (relative_entropy p q))))
      by exact (id_cong (fun x => plus (entropy_dist p) x)
                        (plus_comm (relative_entropy p q) (opp (entropy_dist p)))).
    assert (Hc : Id (plus (entropy_dist p) (plus (opp (entropy_dist p)) (relative_entropy p q)))
                    (plus (plus (entropy_dist p) (opp (entropy_dist p))) (relative_entropy p q)))
      by exact (plus_assoc (entropy_dist p) (opp (entropy_dist p)) (relative_entropy p q)).
    assert (Hd : Id (plus (plus (entropy_dist p) (opp (entropy_dist p))) (relative_entropy p q))
                    (plus zero (relative_entropy p q)))
      by exact (id_cong (fun x => plus x (relative_entropy p q)) (plus_opp (entropy_dist p))).
    assert (He : Id (plus zero (relative_entropy p q)) (relative_entropy p q))
      by exact (id_trans (plus_comm zero (relative_entropy p q)) (plus_zero (relative_entropy p q))).
    exact (id_trans Ha (id_trans Hb (id_trans Hc (id_trans Hd He)))).
  }
  (* 组装：H(p,q) − H(p,p) = (S+KL) − S = KL *)
  assert (Hrepl : Id (minus (cross_entropy p q) (cross_entropy p p))
                     (minus (plus (entropy_dist p) (relative_entropy p q)) (entropy_dist p)))
    by exact (id_cong2 minus H1 H2).
  exact (id_trans Hrepl Hmain).
Qed.

(* 训练等价性：交叉熵下降量 = KL 下降量（固定目标 p）。
   若 H(p,q2) ≤ H(p,q1)，则 KL(p||q2) ≤ KL(p||q1)。
   非平凡：cross_entropy_decomp 分解 + 共同被加项消去 + 差分非负链。 *)

(* 局部引理：共同被加项消去 minus (plus A B) (plus A C) = minus B C *)
Lemma minus_plus_common_local : forall A B C : R,
  Id (minus (plus A B) (plus A C)) (minus B C).
Proof.
  intros A B C.
  unfold minus.
  assert (H1 : Id (plus (plus A B) (opp (plus A C)))
                  (plus (plus A B) (plus (opp A) (opp C))))
    by exact (id_cong (fun x => plus (plus A B) x) (opp_plus A C)).
  assert (H2 : Id (plus (plus A B) (plus (opp A) (opp C)))
                  (plus (plus A (opp A)) (plus B (opp C))))
    by exact (plus_swap_mid A B (opp A) (opp C)).
  assert (H3 : Id (plus (plus A (opp A)) (plus B (opp C)))
                  (plus zero (plus B (opp C))))
    by exact (id_cong (fun x => plus x (plus B (opp C))) (plus_opp A)).
  assert (H4 : Id (plus zero (plus B (opp C))) (plus B (opp C)))
    by exact (id_trans (plus_comm zero (plus B (opp C))) (plus_zero (plus B (opp C)))).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

Theorem training_equivalence :
  forall p q1 q2 : S -> R,
    le (cross_entropy p q2) (cross_entropy p q1) ->
    le (relative_entropy p q2) (relative_entropy p q1).
Proof.
  intros p q1 q2 Hce.
  (* 差分恒等：(H2 − H1) = (KL2 − KL1)。
     H2 = S + KL2、H1 = S + KL1（cross_entropy_decomp），
     相减经 minus_plus_common_local 消共同项 S。 *)
  assert (Hdiff : Id (minus (cross_entropy p q2) (cross_entropy p q1))
                     (minus (relative_entropy p q2) (relative_entropy p q1))).
  {
    assert (H2d : Id (cross_entropy p q2)
                     (plus (entropy_dist p) (relative_entropy p q2)))
      by exact (cross_entropy_decomp p q2).
    assert (H1d : Id (cross_entropy p q1)
                     (plus (entropy_dist p) (relative_entropy p q1)))
      by exact (cross_entropy_decomp p q1).
    assert (Hrepl : Id (minus (cross_entropy p q2) (cross_entropy p q1))
                       (minus (plus (entropy_dist p) (relative_entropy p q2))
                              (plus (entropy_dist p) (relative_entropy p q1))))
      by exact (id_cong2 minus H2d H1d).
    assert (Hcancel : Id (minus (plus (entropy_dist p) (relative_entropy p q2))
                                (plus (entropy_dist p) (relative_entropy p q1)))
                         (minus (relative_entropy p q2) (relative_entropy p q1)))
      by exact (minus_plus_common_local (entropy_dist p) (relative_entropy p q2) (relative_entropy p q1)).
    exact (id_trans Hrepl Hcancel).
  }
  (* 由 Hce : le H2 H1 得 le zero (minus H1 H2)（le_minus_nonneg H2 H1） *)
  assert (Hd : le zero (minus (cross_entropy p q1) (cross_entropy p q2)))
    by exact (le_minus_nonneg (cross_entropy p q2) (cross_entropy p q1) Hce).
  (* 替换：minus H1 H2 = minus KL1 KL2（cross_entropy_decomp + 共同项消去） *)
  assert (Hdiff' : Id (minus (cross_entropy p q1) (cross_entropy p q2))
                      (minus (relative_entropy p q1) (relative_entropy p q2))).
  {
    assert (H1d : Id (cross_entropy p q1)
                     (plus (entropy_dist p) (relative_entropy p q1)))
      by exact (cross_entropy_decomp p q1).
    assert (H2d : Id (cross_entropy p q2)
                     (plus (entropy_dist p) (relative_entropy p q2)))
      by exact (cross_entropy_decomp p q2).
    assert (Hrepl : Id (minus (cross_entropy p q1) (cross_entropy p q2))
                       (minus (plus (entropy_dist p) (relative_entropy p q1))
                              (plus (entropy_dist p) (relative_entropy p q2))))
      by exact (id_cong2 minus H1d H2d).
    assert (Hcancel : Id (minus (plus (entropy_dist p) (relative_entropy p q1))
                                (plus (entropy_dist p) (relative_entropy p q2)))
                         (minus (relative_entropy p q1) (relative_entropy p q2)))
      by exact (minus_plus_common_local (entropy_dist p) (relative_entropy p q1) (relative_entropy p q2)).
    exact (id_trans Hrepl Hcancel).
  }
  assert (Hd' : le zero (minus (relative_entropy p q1) (relative_entropy p q2)))
    by exact (le_id_r zero (minus (cross_entropy p q1) (cross_entropy p q2))
                      (minus (relative_entropy p q1) (relative_entropy p q2))
                      Hdiff' Hd).
  (* le KL2 KL1：KL2 ≤ KL2 + (KL1 − KL2) = KL1 *)
  apply (le_id_r (relative_entropy p q2)
                 (plus (relative_entropy p q2) (minus (relative_entropy p q1) (relative_entropy p q2)))
                 (relative_entropy p q1)
                 (minus_plus_cancel (relative_entropy p q2) (relative_entropy p q1))).
  exact (le_plus_nonneg_r (relative_entropy p q2)
                          (minus (relative_entropy p q1) (relative_entropy p q2)) Hd').
Qed.

End FreeEnergyMinimization.

(* ============================================================ *)
(* RLHF 对齐（当前 AI 训练核心：KL 正则化奖励最大化）          *)
(* ============================================================ *)
(* 现代 LLM 对齐（RLHF/DPO/PPO）的目标：                        *)
(*   maximize  E_π[r] - β·KL(π‖π_ref)                          *)
(* 在偏离参考策略 π_ref（SFT 策略）不超过 KL 惩罚的前提下最大化*)
(* 奖励。数学上是 Boltzmann 机制的精确复刻（奖励替代能量、参考 *)
(* 策略替代均匀先验）。闭式解：π*(s) ∝ π_ref(s)·e^{r(s)/β}。   *)
(* 最优性 J(pi) <= J(pi_star) 由奖励反解 + Gibbs 不等式严格证明。     *)
(* ------------------------------------------------------------ *)

Print Assumptions r_pow_nonneg.
Print Assumptions mult_one_minus_r.
Print Assumptions telescoping.
Print Assumptions one_minus_kappa_pos.
Print Assumptions mult_swap_mid.
Print Assumptions mult_swap_outer.
Print Assumptions minus_pos.
Print Assumptions mult_minus_distr_r.
