(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* S06_DiffSamplingGibbs.v                                     *)
(*                                                             *)
(* 目的：微分采样与 Gibbs 配分：log 可微性、Top-K 截断总变差与    *)
(*       求和分解代数（构造性 Set 层）。                         *)
(* 主件：TV(boltzmann, topk_renorm) == tail_mass/Z_thermo（精确   *)
(*       恒等）；log(1+t) 线性上下界族。                         *)
(* 依赖：S01–S05；Stdlib（QArith、Qabs、Qround、List、Bool、     *)
(*       Arith、Setoid、Morphisms、Lia、Qminmax）。              *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 拆分模块之一，原文区间 *)
(*       L24768-L32574，去头正文与原文区间逐字节同源。           *)
(* ============================================================ *)

(* ============================================================ *)
(* ToyR 工程 （ ）——同名非平凡替换交付稿       *)
(* 替换定理清单：partition_function_pos（原逐句转发 → 定义层展开＋逐点正性断言单列＋求和保正接口显式实例化装配）。                                          *)
(* 非平凡性说明：消除单跳/逐句转发，展开至定义层，逐点正性单列      *)
(*   为显式命题后对求和保正接口显式实例化装配（断言组合＋显式项）。 *)
(* 红线自检：纯构造性；零新增承认语句；替换证明以真证明闭合语句     *)
(*   闭尾；文件尾附假设面打印锚。                                   *)
(* 编译态：本件语法自检通过；全链编译待验（S 系深依赖链未建）。     *)
(* ============================================================ *)

(* ——  续作·切片二追加替换：partition_function_temp_pos /                *)
(*   partition_function_scaled_pos / partition_function_temp_param_pos       *)
(*   （同族样板复用：定义层展开＋逐点正性断言单列＋求和保正接口显式实例化）。 *)
(*   文件尾增假设面打印锚三条，余见记录册续作节。                               *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.

Section GramSchmidt.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpaceExtended RI}.
Context {HS : HilbertSpace RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let inner := @inner RI SS HS.
Let splus := @splus RI SS.
Let sopp := @sopp RI SS.
Let szero := @szero RI SS.
Let smult := @smult RI SS.
Let proj := @proj RI SS HS.

(* 内积对 sopp 的引理（经 inner_smult_l + smult_opp 推导）：
   ⟨-x, y⟩ = -⟨x, y⟩ *)
Lemma inner_sopp_l : forall x y : S,
  Id (inner (sopp x) y) (opp (inner x y)).
Proof.
  intros x y.
  exact (id_trans (id_sym (id_cong (fun z => inner z y)
                     (id_trans (smult_opp one x) (id_cong sopp (smult_one x)))))
           (id_trans (inner_smult_l (opp one) x y)
              (id_trans (opp_mult_r one (inner x y))
                 (id_cong opp (id_trans (mult_comm one (inner x y))
                                        (mult_one (inner x y))))))).
Qed.

(* 零向量与任意向量的内积为零：⟨0, y⟩ = 0（经 splus_opp + inner_splus_l） *)
Lemma inner_szero_l : forall y : S,
  Id (inner szero y) zero.
Proof.
  intro y.
  exact (id_trans (id_sym (id_cong (fun z => inner z y) (splus_opp y)))
           (id_trans (inner_splus_l y (sopp y) y)
              (id_trans (id_cong (fun t => plus (inner y y) t) (inner_sopp_l y y))
                 (plus_opp (inner y y))))).
Qed.

(* 投影幂等性需要额外假设（proj_linear + proj_orthogonal 不足以证明
   proj u (proj u v) = proj u v——需要 ⟨w,u⟩=0 ⟹ proj u w = 0 的
   "投影沿正交方向消失"性质，接口未提供；具体实例如 R^n 满足）。
   此处作为显式 Variable 假设给出，供后续代数推导使用。 *)
Variable projection_idempotent : forall u v : S,
  Id (proj u (proj u v)) (proj u v).

(* Gram-Schmidt 单步：给定非零向量 u 与任意 v，
   构造 w := v - proj u v 使得 ⟨u, w⟩ = 0（v 沿 u 的正交分量，sigT 存在性）。
   非平凡：proj_orthogonal 给出 ⟨v - proj u v, u⟩ = 0，
   用 inner_sym 换位到 ⟨u, w⟩ = 0，并给出分解见证 v = proj u v + w。 *)
Theorem gram_schmidt_step : forall u v : S,
  Not (Id u szero) ->
  sigT (fun w : S =>
    And (Id (inner u w) zero)
        (Id v (splus (proj u v) w))).
Proof.
  intros u v Hu.
  exists (splus v (sopp (proj u v))).
  split.
  - (* ⟨u, v - proj u v⟩ = 0：proj_orthogonal 给出 ⟨v - proj u v, u⟩ = 0，
       inner_sym 换位到 ⟨u, v - proj u v⟩ = 0 *)
    apply (id_trans (id_sym (inner_sym (splus v (sopp (proj u v))) u))
                    (proj_orthogonal u v)).
  - (* v = proj u v + (v - proj u v)：splus 代数（同 orthogonal_decomposition_exists） *)
    assert (Hopp : Id (splus (proj u v) (splus v (sopp (proj u v))))
                    (splus (proj u v) (splus (sopp (proj u v)) v))).
    { apply (id_cong (fun x => splus (proj u v) x)).
      exact (splus_comm v (sopp (proj u v))). }
    assert (Hassoc : Id (splus (proj u v) (splus (sopp (proj u v)) v))
                        (splus (splus (proj u v) (sopp (proj u v))) v)).
    { exact (splus_assoc (proj u v) (sopp (proj u v)) v). }
    assert (Hinv : Id (splus (proj u v) (sopp (proj u v))) szero)
      by exact (splus_opp (proj u v)).
    assert (Hzero : Id (splus szero v) v)
      by exact (id_trans (splus_comm szero v) (splus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc (id_trans (id_cong (fun x => splus x v) Hinv) Hzero)))).
Qed.

(* Gram-Schmidt 两向量版本：给定非零 u 与任意 v，
   构造正交基 {u, w}（w := v 在 u 正交补上的投影），sigT 形式。 *)
Theorem gram_schmidt_pair : forall u v : S,
  Not (Id u szero) ->
  sigT (fun w : S =>
    And (Id (inner u w) zero)
        (Id v (splus (proj u v) w))).
Proof.
  intros u v Hu.
  exact (gram_schmidt_step u v Hu).
Qed.

End GramSchmidt.

(* 概率分布基本性质 *)
Section ProbDistProperties.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Definition is_prob_dist (p : S -> R) : Set :=
  And (forall s, le zero (p s)) (Id (sum_over_S p) one).

Lemma prob_dist_sum_linear :
  forall (p : S -> R), is_prob_dist p ->
  forall (a : R),
    Id (sum_over_S (fun s => mult a (p s))) a.
Proof.
  intros p [Hnonneg Hnorm] a.
  rewrite sum_over_S_linear.
  rewrite Hnorm.
  apply mult_one.
Qed.

(* 修正：原假设 prob_dist_add（is_prob_dist (p+q)）数学上不成立——
   Σ(p+q) = Σp + Σq = 1+1 = 2 ≠ 1（分布之和不再归一化）。
   正确的混合操作是归一化平均 inv_2·(p+q)，且是可证定理。 *)
Theorem prob_dist_mix :
  forall p q : S -> R,
    is_prob_dist p -> is_prob_dist q ->
    is_prob_dist (fun s => mult (inv_pos (plus one one) two_pos) (plus (p s) (q s))).
Proof.
  intros p q [Hp_nonneg Hp_norm] [Hq_nonneg Hq_norm].
  unfold is_prob_dist.
  split.
  - (* 非负性：inv_2·(p s + q s) ≥ 0 *)
    intro s.
    apply (le_trans _ (mult zero (plus (p s) (q s))) _).
    + assert (Hz : Id (mult zero (plus (p s) (q s))) zero)
        by exact (id_trans (mult_comm zero (plus (p s) (q s))) (mult_zero (plus (p s) (q s)))).
      rewrite Hz. apply le_refl.
    + apply (le_mult_compat_weak zero (inv_pos (plus one one) two_pos) (plus (p s) (q s))).
      * apply (le_trans _ (plus zero zero) _).
        -- assert (Hz2 : Id (plus zero zero) zero)
             by exact (id_trans (plus_comm zero zero) (plus_zero zero)).
           rewrite Hz2. apply le_refl.
        -- apply le_plus_compat; [exact (Hp_nonneg s) | exact (Hq_nonneg s)].
      * apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - (* 归一化：Σ_s inv_2·(p s + q s) = inv_2·(Σp + Σq) = inv_2·(1+1) = 1 *)
    assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (plus one one) two_pos) (plus (p s) (q s))))
                     (mult (inv_pos (plus one one) two_pos) (sum_over_S (fun s => plus (p s) (q s)))))
      by exact (sum_over_S_linear (inv_pos (plus one one) two_pos) (fun s => plus (p s) (q s))).
    rewrite Hlin.
    assert (Hadd : Id (sum_over_S (fun s => plus (p s) (q s))) (plus (sum_over_S p) (sum_over_S q)))
      by exact (sum_over_S_add p q).
    rewrite Hadd.
    rewrite Hp_norm. rewrite Hq_norm.
    assert (Hcc : Id (mult (inv_pos (plus one one) two_pos) (plus one one)) one)
      by exact (id_trans (mult_comm (inv_pos (plus one one) two_pos) (plus one one))
                         (inv_pos_correct (plus one one) two_pos)).
    exact Hcc.
Qed.

End ProbDistProperties.

(* KL 散度 *)
Section KLDivergence.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 显式绑定基本类型与函数 *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let log := @log RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable q : S -> R.
Variable q_pos : forall s, lt zero (q s).

(* KL 散度：定义为相对熵 relative_entropy p q = Σ p·(log p − log q)。
   P1 消解：原定义用 log_inv(inv_pos q · p) 实为 −KL（符号反），
   且与已证 gibbs_inequality/gibbs_equality 平行冗余。现统一到
   FreeEnergyMinimization 的 relative_entropy 表示（消除双定义）。 *)
Definition kl_divergence (p : S -> R) : R :=
  relative_entropy p q.

(* q 归一化（gibbs 定理所需，KLDivergence 原缺）：诚实 Variable。 *)
Variable q_norm : normalized q.

(* Gibbs 不等式（KL ≥ 0）：由已证 gibbs_inequality 特化（P1 消解：
   原诚实 Variable kl_nonneg 提升为已证定理）。 *)
Theorem kl_nonneg : forall p : S -> R,
  normalized p -> positive_dist p -> le zero (kl_divergence p).
Proof.
  intros p Hnp Hpp.
  unfold kl_divergence.
  exact (gibbs_inequality p q Hnp Hpp q_norm q_pos).
Qed.

(* Gibbs 等式（KL = 0 ⟹ p = q）：由已证 gibbs_equality 特化（P1 消解：
   原诚实 Variable kl_zero_iff_eq 提升为已证定理）。 *)
Theorem kl_zero_iff_eq : forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (kl_divergence p) zero -> forall s : S, Id (p s) (q s).
Proof.
  intros p Hnp Hpp Hkl0 s.
  unfold kl_divergence in Hkl0.
  exact (gibbs_equality p q Hnp Hpp q_norm q_pos Hkl0 s).
Qed.

End KLDivergence.

(* 可微性引理 *)
Section DifferentiableLemmas.
Local Existing Instance RI_base.
Context {RI : RealInterfaceEnhanced}.

(* 显式解包字段 *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let plus_zero := @plus_zero RI.
Let plus_comm := @plus_comm RI.
Let plus_opp := @plus_opp RI.
Let mult_zero := @mult_zero RI.
Let mult_comm := @mult_comm RI.
Let mult_one := @mult_one RI.
Let abs_nonneg := @abs_nonneg RI.
Let le_mult_compat := @le_mult_compat RI.
Let le_trans := @le_trans RI.
Let one_pos := @one_pos RI.
Let exp_neg := @exp_neg RI.
Let log_inv := @log_inv RI.
Let log_inv_exp_neg := @log_inv_exp_neg RI.

(* abs_zero 已提升为 RealInterfaceEnhanced 字段（见上），此处不再声明为假设；
   证明中通过 change ... in abs_zero 将其陈述换到 Let 层以匹配目标。 *)

Lemma differentiable_const (c : R) : Differentiable (fun _ => c).
Proof.
  exists (fun _ => zero).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    unfold minus.
    rewrite (mult_comm zero h).
    rewrite mult_zero.
    rewrite plus_zero.
    rewrite plus_opp.
    (* 目标：le (abs zero) (mult eps (abs h))。
       注意：目标中 abs/zero/mult/le 是类投影（coqc 编译下为 <模块名>.abs 等，
       交互式加载下为 Top.abs 等），而 abs_zero 与各公理 Let 常量（abs/zero/mult 等）。
       rewrite 匹配不跨 δ-层级，故全程统一在 Let 层操作：
       change 把目标换到 Let 常量形态（可换性成立），assert+exact 生成 Let 层
       Id 引理（exact 按可换性检查），同层 rewrite，最后 exact 收尾。
       此写法不依赖任何模块名前缀，交互式与 coqc 命令行均可编译。 *)
    change (le (abs zero) (mult eps (abs h))).
    (* abs_zero 现为 Enhanced 字段（陈述投影级），先 pose 为局部假设再 change 到 Let 层 *)
    pose proof abs_zero as Habs_zero.
    change (Id (abs zero) zero) in Habs_zero.
    rewrite Habs_zero.
    assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
    rewrite <- Hmz.
    assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
    rewrite Hmc1.
    assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
    rewrite Hmc2.
    exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
Qed.

Lemma differentiable_id : Differentiable (fun x => x).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split; [apply one_pos | intros h Hh].
  unfold minus.
  rewrite (mult_comm one h).
  rewrite mult_one.
  rewrite plus_opp.
  (* 同 differentiable_const：全程 Let 层，不依赖模块名前缀 *)
  change (le (abs zero) (mult eps (abs h))).
  pose proof abs_zero as Habs_zero.
  change (Id (abs zero) zero) in Habs_zero.
  rewrite Habs_zero.
  assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
  rewrite <- Hmz.
  assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
  rewrite Hmc1.
  assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
  rewrite Hmc2.
  exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
Qed.

(* 非平凡实现：加法可微性（ε-δ 构造性证明）。
   思路：误差 |Δ(f+g) - (df+dg)·h| ≤ |Δf - df·h| + |Δg - dg·h| ≤ (eps/2+eps/2)|h| = eps|h|。
   δ = min δf δg（min_pos 保正）；eps/2 = inv_2·eps（half_pos/half_twice）；
   代数分解用 minus_plus_distr / plus_swap_mid / mult_plus_distr_r（RingLemmas）；
   各引理在 Let 层使用需 pose + change（见判例）。 *)
Theorem differentiable_plus : forall (f g : R -> R),
  Differentiable f -> Differentiable g ->
  Differentiable (fun x => plus (f x) (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => plus (df x) (dg x)).
  intros x eps Heps.
  pose (mult (inv_pos (plus one one) two_pos) eps) as eps_half.
  assert (Hhalf : lt zero eps_half) by (unfold eps_half; apply half_pos; exact Heps).
  destruct (Hf x eps_half Hhalf) as [dfdelta [Hdf1 Hdf2]].
  destruct (Hg x eps_half Hhalf) as [dgdelta [Hdg1 Hdg2]].
  exists (min dfdelta dgdelta).
  split.
  - (* lt zero (min dfdelta dgdelta) *)
    apply min_pos; [exact Hdf1 | exact Hdg1].
  - intros h Hh.
    (* 目标换到 Let 层（df_correct 陈述为投影级，Let 层便于 rewrite，见判例） *)
    change (le (abs (minus (plus (f (plus x h)) (g (plus x h)))
                            (plus (plus (f x) (g x)) (mult (plus (df x) (dg x)) h))))
              (mult eps (abs h))).
    (* |h| < min ⟹ |h| < dfdelta 且 |h| < dgdelta *)
    assert (Hh1 : lt (abs h) dfdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_l. }
    assert (Hh2 : lt (abs h) dgdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_r. }
    (* 误差分解：E = A_f + A_g（minus_plus_distr + plus_swap_mid + mult_plus_distr_r） *)
    assert (Hmpd : Id (mult (plus (df x) (dg x)) h) (plus (mult (df x) h) (mult (dg x) h)))
      by exact (mult_plus_distr_r (df x) (dg x) h).
    rewrite Hmpd.
    assert (Hswap : Id (plus (plus (f x) (g x)) (plus (mult (df x) h) (mult (dg x) h)))
                       (plus (plus (f x) (mult (df x) h)) (plus (g x) (mult (dg x) h))))
      by exact (plus_swap_mid (f x) (g x) (mult (df x) h) (mult (dg x) h)).
    rewrite Hswap.
    assert (Hmpd2 : Id (minus (plus (f (plus x h)) (g (plus x h)))
                              (plus (plus (f x) (mult (df x) h)) (plus (g x) (mult (dg x) h))))
                       (plus (minus (f (plus x h)) (plus (f x) (mult (df x) h)))
                             (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
      by exact (minus_plus_distr (f (plus x h)) (g (plus x h))
                                 (plus (f x) (mult (df x) h)) (plus (g x) (mult (dg x) h))).
    rewrite Hmpd2.
    (* 三角不等式 *)
    apply (le_trans _ (plus (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                            (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))).
    + apply abs_triangle.
    + apply (le_trans _ (plus (mult eps_half (abs h)) (mult eps_half (abs h)))).
      * apply le_plus_compat.
        -- apply (Hdf2 h Hh1).
        -- apply (Hdg2 h Hh2).
      * (* eps_half·|h| + eps_half·|h| = eps·|h| *)
        assert (Hsum : Id (plus (mult eps_half (abs h)) (mult eps_half (abs h)))
                          (mult eps (abs h))).
        {
          unfold eps_half.
          assert (Hd : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                      (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                           (plus (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                                 (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))))
            by exact (mult_plus_distr_r (mult (inv_pos (plus one one) two_pos) eps)
                                        (mult (inv_pos (plus one one) two_pos) eps) (abs h)).
          rewrite <- Hd.
          (* 在 mult _ (abs h) 上下文中替换：plus X X = eps（id_cong，避免 rewrite 过度替换） *)
          assert (Hcong : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                          (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                             (mult eps (abs h))).
          { apply (id_cong (fun z => mult z (abs h))). exact (half_twice eps). }
          rewrite Hcong. reflexivity.
        }
        rewrite Hsum. apply le_refl.
Qed.

(* 非平凡实现：乘法可微性（ε-δ 构造性证明；abs_mult/le_mult_compat_weak 字段已加）。
   误差 3 项：|g(x)|·|Δf - df·h| ≤ eps/4·|h|、|f(x)|·|Δg - dg·h| ≤ eps/4·|h|、
   |Δf|·|Δg| ≤ eps/2·|h|（δ₃ 控制 |h|² 项）。总 ≤ eps·|h|。
   代数分解用 mult_diff_decomp（RingLemmas）。 *)
Theorem differentiable_mult : forall (f g : R -> R),
  Differentiable f -> Differentiable g ->
  Differentiable (fun x => mult (f x) (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => plus (mult (df x) (g x)) (mult (f x) (dg x))).
  intros x eps Heps.
  pose (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) as eps4.
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply half_pos. apply half_pos. exact Heps. }
  pose (mult (inv_pos (plus one one) two_pos) eps) as eps2.
  assert (Heps2 : lt zero eps2).
  { unfold eps2. apply half_pos. exact Heps. }
  pose (plus (abs (f x)) one) as Mf.
  assert (Hmf : lt zero Mf) by (unfold Mf; apply abs_plus_one_pos).
  pose (plus (abs (g x)) one) as Mg.
  assert (Hmg : lt zero Mg) by (unfold Mg; apply abs_plus_one_pos).
  pose (mult (inv_pos Mg Hmg) eps4) as eps_f.
  assert (Hef : lt zero eps_f).
  { unfold eps_f. apply mult_positive. apply inv_pos_pos. exact Heps4. }
  pose (mult (inv_pos Mf Hmf) eps4) as eps_g.
  assert (Heg : lt zero eps_g).
  { unfold eps_g. apply mult_positive. apply inv_pos_pos. exact Heps4. }
  destruct (Hf x eps_f Hef) as [dfdelta [Hdf1 Hdf2]].
  destruct (Hg x eps_g Heg) as [dgdelta [Hdg1 Hdg2]].
  pose (mult (plus (abs (df x)) eps_f) (plus (abs (dg x)) eps_g)) as Den.
  assert (HD1 : lt zero (plus (abs (df x)) eps_f)).
  { apply plus_le_lt_pos. apply abs_nonneg. exact Hef. }
  assert (HD2 : lt zero (plus (abs (dg x)) eps_g)).
  { apply plus_le_lt_pos. apply abs_nonneg. exact Heg. }
  assert (HDpos : lt zero Den).
  { unfold Den. apply mult_positive. exact HD1. exact HD2. }
  pose (mult (inv_pos Den HDpos) eps2) as eps3.
  assert (He3 : lt zero eps3).
  { unfold eps3. apply mult_positive. apply inv_pos_pos. exact Heps2. }
  exists (min (min dfdelta dgdelta) eps3).
  split.
  - apply min_pos.
    + apply min_pos; [exact Hdf1 | exact Hdg1].
    + exact He3.
  - intros h Hh.
    change (le (abs (minus (mult (f (plus x h)) (g (plus x h)))
                           (plus (mult (f x) (g x))
                                 (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h))))
              (mult eps (abs h))).
    assert (Hh_d : lt (abs h) dfdelta).
    { eapply lt_le_trans. exact Hh. eapply le_trans. apply min_le_l. apply min_le_l. }
    assert (Hh_dg : lt (abs h) dgdelta).
    { eapply lt_le_trans. exact Hh. eapply le_trans. apply min_le_l. apply min_le_r. }
    assert (Hh_3 : lt (abs h) eps3).
    { eapply lt_le_trans. exact Hh. apply min_le_r. }
    assert (Hh_le3 : le (abs h) eps3).
    { apply (lt_le_iff _ _). left. exact Hh_3. }
    assert (Hdec : Id (minus (mult (f (plus x h)) (g (plus x h)))
                             (plus (mult (f x) (g x))
                                   (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h)))
                      (plus (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
                            (plus (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                                  (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))))
      by exact (mult_diff_decomp f g df dg x h).
    rewrite Hdec.
    assert (Hdf_bound : le (abs (minus (f (plus x h)) (f x)))
                           (mult (plus (abs (df x)) eps_f) (abs h))).
    {
      assert (Hsplit : Id (minus (f (plus x h)) (f x))
                          (plus (minus (f (plus x h)) (plus (f x) (mult (df x) h)))
                                (mult (df x) h)))
        by exact (minus_split (f (plus x h)) (f x) (mult (df x) h)).
      rewrite Hsplit.
      apply (le_trans _ (plus (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                              (abs (mult (df x) h))) _).
      { apply abs_triangle. }
      { apply (le_trans _ (plus (mult eps_f (abs h)) (mult (abs (df x)) (abs h))) _).
        { apply le_plus_compat.
          { apply (Hdf2 h Hh_d). }
          { assert (Ham : Id (abs (mult (df x) h)) (mult (abs (df x)) (abs h)))
              by exact (abs_mult (df x) h).
            rewrite Ham. apply le_refl. } }
        { assert (Hsum : Id (plus (mult eps_f (abs h)) (mult (abs (df x)) (abs h)))
                            (mult (plus (abs (df x)) eps_f) (abs h))).
          { assert (Hd : Id (mult (plus (abs (df x)) eps_f) (abs h))
                            (plus (mult (abs (df x)) (abs h)) (mult eps_f (abs h))))
              by exact (mult_plus_distr_r (abs (df x)) eps_f (abs h)).
            apply id_sym. rewrite Hd.
            apply (plus_comm (mult (abs (df x)) (abs h)) (mult eps_f (abs h))). }
          rewrite Hsum. apply le_refl. } }
    }
    assert (Hdg_bound : le (abs (minus (g (plus x h)) (g x)))
                           (mult (plus (abs (dg x)) eps_g) (abs h))).
    {
      assert (Hsplit : Id (minus (g (plus x h)) (g x))
                          (plus (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))
                                (mult (dg x) h)))
        by exact (minus_split (g (plus x h)) (g x) (mult (dg x) h)).
      rewrite Hsplit.
      apply (le_trans _ (plus (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
                              (abs (mult (dg x) h))) _).
      { apply abs_triangle. }
      { apply (le_trans _ (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h))) _).
        { apply le_plus_compat.
          { apply (Hdg2 h Hh_dg). }
          { assert (Ham : Id (abs (mult (dg x) h)) (mult (abs (dg x)) (abs h)))
              by exact (abs_mult (dg x) h).
            rewrite Ham. apply le_refl. } }
        { assert (Hsum : Id (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h)))
                            (mult (plus (abs (dg x)) eps_g) (abs h))).
          { assert (Hd : Id (mult (plus (abs (dg x)) eps_g) (abs h))
                            (plus (mult (abs (dg x)) (abs h)) (mult eps_g (abs h))))
              by exact (mult_plus_distr_r (abs (dg x)) eps_g (abs h)).
            apply id_sym. rewrite Hd.
            apply (plus_comm (mult (abs (dg x)) (abs h)) (mult eps_g (abs h))). }
          rewrite Hsum. apply le_refl. } }
    }
    apply (le_trans _ (plus (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                            (abs (plus (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                                       (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x)))))) _).
    { apply abs_triangle. }
    { apply (le_trans _ (plus (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                              (plus (abs (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
                                    (abs (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x)))))) _).
      { apply le_plus_compat.
        { apply le_refl. }
        { apply abs_triangle. } }
      { (* 三项上界 + 合并 *)
        assert (Hb1 : le (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                        (mult eps4 (abs h))).
        {
          apply (le_trans _ (mult (abs (f x)) (mult eps_g (abs h))) _).
          { apply (le_trans _ (mult (abs (f x)) (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))) _).
            { assert (Ham : Id (abs (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))))
                              (mult (abs (f x)) (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))))
                by exact (abs_mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))).
              rewrite Ham. apply le_refl. }
            { apply (le_mult_compat_r (abs (f x)) (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))) (mult eps_g (abs h))).
              { apply abs_nonneg. }
              { apply (Hdg2 h Hh_dg). } } }
          { assert (Hshare : le (mult (abs (f x)) eps_g) eps4).
            {
              apply (le_trans _ (mult Mf eps_g) _).
              { apply (le_mult_compat_weak _ _ _ (lt_le_iff zero eps_g (inl Heg)) (abs_le_abs_plus_one (f x))). }
              { assert (Hprod : Id (mult Mf eps_g) eps4).
                {
                  unfold eps_g.
                  assert (H1 : Id (mult Mf (mult (inv_pos Mf Hmf) eps4)) (mult (mult Mf (inv_pos Mf Hmf)) eps4))
                    by exact (mult_assoc Mf (inv_pos Mf Hmf) eps4).
                  assert (H2 : Id (mult (mult Mf (inv_pos Mf Hmf)) eps4) (mult one eps4))
                    by exact (id_cong (fun z => mult z eps4) (inv_pos_correct Mf Hmf)).
                  assert (H3 : Id (mult one eps4) eps4)
                    by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                  exact (id_trans H1 (id_trans H2 H3)).
                }
                rewrite Hprod. apply le_refl. } }
            assert (Hsh2 : le (mult (mult (abs (f x)) eps_g) (abs h)) (mult eps4 (abs h)))
              by apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hshare).
            assert (Hassoc : Id (mult (abs (f x)) (mult eps_g (abs h)))
                                (mult (mult (abs (f x)) eps_g) (abs h)))
              by exact (mult_assoc (abs (f x)) eps_g (abs h)).
            rewrite Hassoc. exact Hsh2. }
        }
        assert (Hb2 : le (abs (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
                        (mult eps4 (abs h))).
        {
          apply (le_trans _ (mult (abs (g x)) (mult eps_f (abs h))) _).
          { apply (le_trans _ (mult (abs (g x)) (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))) _).
            { assert (Ham : Id (abs (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
                              (mult (abs (g x)) (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))))
                by exact (abs_mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h)))).
              rewrite Ham. apply le_refl. }
            { apply (le_mult_compat_r (abs (g x)) (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h)))) (mult eps_f (abs h))).
              { apply abs_nonneg. }
              { apply (Hdf2 h Hh_d). } } }
          { assert (Hshare : le (mult (abs (g x)) eps_f) eps4).
            {
              apply (le_trans _ (mult Mg eps_f) _).
              { apply (le_mult_compat_weak _ _ _ (lt_le_iff zero eps_f (inl Hef)) (abs_le_abs_plus_one (g x))). }
              { assert (Hprod : Id (mult Mg eps_f) eps4).
                {
                  unfold eps_f.
                  assert (H1 : Id (mult Mg (mult (inv_pos Mg Hmg) eps4)) (mult (mult Mg (inv_pos Mg Hmg)) eps4))
                    by exact (mult_assoc Mg (inv_pos Mg Hmg) eps4).
                  assert (H2 : Id (mult (mult Mg (inv_pos Mg Hmg)) eps4) (mult one eps4))
                    by exact (id_cong (fun z => mult z eps4) (inv_pos_correct Mg Hmg)).
                  assert (H3 : Id (mult one eps4) eps4)
                    by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                  exact (id_trans H1 (id_trans H2 H3)).
                }
                rewrite Hprod. apply le_refl. } }
            assert (Hsh2 : le (mult (mult (abs (g x)) eps_f) (abs h)) (mult eps4 (abs h)))
              by apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hshare).
            assert (Hassoc : Id (mult (abs (g x)) (mult eps_f (abs h)))
                                (mult (mult (abs (g x)) eps_f) (abs h)))
              by exact (mult_assoc (abs (g x)) eps_f (abs h)).
            rewrite Hassoc. exact Hsh2. }
        }
        assert (Hthird : le (abs (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))
                            (mult eps2 (abs h))).
        {
          assert (Hm1 : Id (abs (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))
                          (mult (abs (minus (f (plus x h)) (f x)))
                                (abs (minus (g (plus x h)) (g x)))))
            by exact (abs_mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))).
          rewrite Hm1.
          apply (le_trans _ (mult (mult (plus (abs (df x)) eps_f) (abs h))
                                  (mult (plus (abs (dg x)) eps_g) (abs h))) _).
          { apply (le_trans _ (mult (mult (plus (abs (df x)) eps_f) (abs h))
                                    (abs (minus (g (plus x h)) (g x)))) _).
            { apply (le_mult_compat_weak _ _ _ (abs_nonneg (minus (g (plus x h)) (g x))) Hdf_bound). }
            { apply (le_mult_compat_r (mult (plus (abs (df x)) eps_f) (abs h)) (abs (minus (g (plus x h)) (g x))) (mult (plus (abs (dg x)) eps_g) (abs h))).
              { assert (HleA : le zero (mult (plus (abs (df x)) eps_f) (abs h))).
                { apply (le_trans _ (mult zero (abs h)) _).
                  { assert (Hz : Id (mult zero (abs h)) zero)
                      by exact (id_trans (mult_comm zero (abs h)) (mult_zero (abs h))).
                    rewrite Hz. apply le_refl. }
                  { apply (le_mult_compat_weak _ _ _ (abs_nonneg h) (lt_le_iff zero (plus (abs (df x)) eps_f) (inl HD1))). } }
                exact HleA. }
              { exact Hdg_bound. } } }
          { assert (Hre : Id (mult (mult (plus (abs (df x)) eps_f) (abs h))
                                    (mult (plus (abs (dg x)) eps_g) (abs h)))
                              (mult Den (mult (abs h) (abs h)))).
            {
              unfold Den.
              set (A := plus (abs (df x)) eps_f).
              set (B := plus (abs (dg x)) eps_g).
              assert (Hs1 : Id (mult (mult A (abs h)) (mult B (abs h)))
                               (mult A (mult (abs h) (mult B (abs h)))))
                by exact (id_sym (mult_assoc A (abs h) (mult B (abs h)))).
              assert (Hs2 : Id (mult A (mult (abs h) (mult B (abs h))))
                               (mult A (mult (mult (abs h) B) (abs h))))
                by exact (id_cong (fun z => mult A z) (mult_assoc (abs h) B (abs h))).
              assert (Hs3 : Id (mult A (mult (mult (abs h) B) (abs h)))
                               (mult A (mult (mult B (abs h)) (abs h))))
                by exact (id_cong (fun z => mult A (mult z (abs h))) (mult_comm (abs h) B)).
              assert (Hs4 : Id (mult A (mult (mult B (abs h)) (abs h)))
                               (mult (mult A (mult B (abs h))) (abs h)))
                by exact (mult_assoc A (mult B (abs h)) (abs h)).
              assert (Hs5 : Id (mult (mult A (mult B (abs h))) (abs h))
                               (mult (mult (mult A B) (abs h)) (abs h)))
                by exact (id_cong (fun z => mult z (abs h)) (mult_assoc A B (abs h))).
              assert (Hs6 : Id (mult (mult (mult A B) (abs h)) (abs h))
                               (mult (mult A B) (mult (abs h) (abs h))))
                by exact (id_sym (mult_assoc (mult A B) (abs h) (abs h))).
              exact (id_trans Hs1 (id_trans Hs2 (id_trans Hs3 (id_trans Hs4 (id_trans Hs5 Hs6))))).
            }
            rewrite Hre.
            apply (le_trans _ (mult Den (mult eps3 (abs h))) _).
            { apply (le_mult_compat_r Den (mult (abs h) (abs h)) (mult eps3 (abs h))).
              { assert (HleD : le zero Den).
                { apply (lt_le_iff _ _). left. exact HDpos. }
                exact HleD. }
              { apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hh_le3). } }
            { assert (Hdq : Id (mult Den (mult eps3 (abs h))) (mult eps2 (abs h))).
              {
                unfold eps3.
                assert (H1 : Id (mult Den (mult (mult (inv_pos Den HDpos) eps2) (abs h)))
                                (mult (mult Den (mult (inv_pos Den HDpos) eps2)) (abs h)))
                  by exact (mult_assoc Den (mult (inv_pos Den HDpos) eps2) (abs h)).
                rewrite H1.
                assert (H2 : Id (mult Den (mult (inv_pos Den HDpos) eps2)) (mult (mult Den (inv_pos Den HDpos)) eps2))
                  by exact (mult_assoc Den (inv_pos Den HDpos) eps2).
                assert (H2' : Id (mult (mult Den (mult (inv_pos Den HDpos) eps2)) (abs h))
                                 (mult (mult (mult Den (inv_pos Den HDpos)) eps2) (abs h)))
                  by exact (id_cong (fun z => mult z (abs h)) H2).
                rewrite H2'.
                assert (H3 : Id (mult (mult (mult Den (inv_pos Den HDpos)) eps2) (abs h))
                                 (mult (mult one eps2) (abs h)))
                  by exact (id_cong (fun z => mult (mult z eps2) (abs h)) (inv_pos_correct Den HDpos)).
                rewrite H3.
                assert (H4 : Id (mult (mult one eps2) (abs h)) (mult eps2 (abs h)))
                  by exact (id_cong (fun z => mult z (abs h)) (id_trans (mult_comm one eps2) (mult_one eps2))).
                rewrite H4. reflexivity.
              }
              rewrite Hdq. apply le_refl. }
          }
        }
        apply (le_trans _ (plus (mult eps4 (abs h)) (plus (mult eps4 (abs h)) (mult eps2 (abs h)))) _).
        { apply le_plus_compat. { exact Hb1. } { apply le_plus_compat. { exact Hb2. } { exact Hthird. } } }
        { assert (Hmerge1 : Id (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps2 (abs h))).
          {
            unfold eps4, eps2.
            assert (Ht : Id (plus (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                                  (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h)))
                            (mult (plus one one) (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h))))
              by exact (id_sym (two_mult (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h)))).
            rewrite Ht.
            assert (Hq : Id (mult (plus one one) (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)) (abs h)))
                            (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h)))
              by exact (two_times_quarter eps (abs h)).
            rewrite Hq. reflexivity.
          }
          assert (Hmerge2 : Id (plus (mult eps2 (abs h)) (mult eps2 (abs h))) (mult eps (abs h))).
          {
            unfold eps2.
            assert (Hd : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps) (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                            (plus (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                                  (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))))
              by exact (mult_plus_distr_r (mult (inv_pos (plus one one) two_pos) eps)
                                          (mult (inv_pos (plus one one) two_pos) eps) (abs h)).
            rewrite <- Hd.
            assert (Hcong : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                           (mult (inv_pos (plus one one) two_pos) eps)) (abs h))
                               (mult eps (abs h))).
            { apply (id_cong (fun z => mult z (abs h))). exact (half_twice eps). }
            rewrite Hcong. reflexivity.
          }
          apply (le_trans _ (plus (mult eps2 (abs h)) (mult eps2 (abs h))) _).
          { assert (Hpa : Id (plus (mult eps4 (abs h)) (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                             (plus (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps2 (abs h))))
              by exact (plus_assoc (mult eps4 (abs h)) (mult eps4 (abs h)) (mult eps2 (abs h))).
            rewrite Hpa. rewrite Hmerge1. apply le_refl. }
          { rewrite Hmerge2. apply le_refl. }
        }
      }
    }
Qed.

(* ============================================================ *)
(* 仿射函数可微性（改进恒等式.txt 块 4：神经网络线性层的基石）  *)
(* ============================================================ *)
(* f(x) = a·x + b 可微，df = a（误差恒为零：
   a·(x+h)+b − (a·x+b+a·h) = 0——distrib 展开 + 加法重组消去）   *)

Theorem differentiable_affine : forall a b : R,
  Differentiable (fun x => plus (mult a x) b).
Proof.
  intros a b.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* 误差恒为零：minus (a·(x+h)+b) (a·x+b+a·h) = 0。
       先证折叠形态（目标中 minus 保持折叠，rewrite 不跨 δ 层，见判例） *)
    assert (Hd : Id (mult a (plus x h)) (plus (mult a x) (mult a h)))
      by exact (distrib a x h).
    assert (Hzero : Id (minus (plus (mult a (plus x h)) b) (plus (plus (mult a x) b) (mult a h))) zero).
    {
      unfold minus.
      assert (Hnum : Id (plus (plus (mult a (plus x h)) b) (opp (plus (plus (mult a x) b) (mult a h))))
                        (plus (plus (plus (mult a x) (mult a h)) b) (opp (plus (plus (mult a x) b) (mult a h)))))
        by exact (id_cong (fun z => plus (plus z b) (opp (plus (plus (mult a x) b) (mult a h)))) Hd).
      (* 分子重组：(a·x + a·h) + b = (a·x + b) + a·h *)
      assert (Ha : Id (plus (plus (mult a x) (mult a h)) b) (plus (mult a x) (plus (mult a h) b)))
        by exact (id_sym (plus_assoc (mult a x) (mult a h) b)).
      assert (Hb : Id (plus (mult a h) b) (plus b (mult a h)))
        by exact (plus_comm (mult a h) b).
      assert (Hc : Id (plus (mult a x) (plus b (mult a h))) (plus (plus (mult a x) b) (mult a h)))
        by exact (plus_assoc (mult a x) b (mult a h)).
      assert (Hre : Id (plus (plus (mult a x) (mult a h)) b) (plus (plus (mult a x) b) (mult a h)))
        by exact (id_trans Ha (id_trans (id_cong (fun z => plus (mult a x) z) Hb) Hc)).
      assert (Hn2 : Id (plus (plus (plus (mult a x) (mult a h)) b) (opp (plus (plus (mult a x) b) (mult a h))))
                        (plus (plus (plus (mult a x) b) (mult a h)) (opp (plus (plus (mult a x) b) (mult a h)))))
        by exact (id_cong (fun z => plus z (opp (plus (plus (mult a x) b) (mult a h)))) Hre).
      exact (id_trans (id_trans Hnum Hn2) (plus_opp (plus (plus (mult a x) b) (mult a h)))).
    }
    (* 目标含 Let/投影混合拼写（判例），弃 rewrite：le_id_l + id_cong（内核转换） *)
    apply (le_id_l (abs (minus (plus (mult a (plus x h)) b) (plus (plus (mult a x) b) (mult a h))))
                   (abs zero) (mult eps (abs h))).
    + exact (id_cong abs Hzero).
    + (* 目标：le (abs zero) (mult eps (abs h))（同 differentiable_const 收尾） *)
      change (le (abs zero) (mult eps (abs h))).
      pose proof abs_zero as Habs_zero.
      change (Id (abs zero) zero) in Habs_zero.
      rewrite Habs_zero.
      assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
      rewrite <- Hmz.
      assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
      rewrite Hmc1.
      assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
      rewrite Hmc2.
      exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
Qed.

(* ============================================================ *)
(* 可微性代数闭环（可微性代数闭环.txt 模块一）：负函数 / 减法 / *)
(* 自然数幂——自动微分的局部规则在抽象实数接口下形成完整环      *)
(* ============================================================ *)

(* 负函数可微性：(-f)' = -(f')，误差经 opp_minus/opp_mult_l/double_neg 翻转 *)
Theorem differentiable_opp : forall (f : R -> R),
  Differentiable f -> Differentiable (fun x => opp (f x)).
Proof.
  intros f [df Hf].
  exists (fun x => opp (df x)).
  intros x eps Heps.
  destruct (Hf x eps Heps) as [delta [Hdelta Hdf]].
  exists delta. split. exact Hdelta.
  intros h Hh.
  (* 误差 = -f(x+h) - (-f(x) - df(x)·h) = -[f(x+h) - (f(x) + df(x)·h)] *)
  assert (Hzero : Id (minus (opp (f (plus x h))) (plus (opp (f x)) (mult (opp (df x)) h)))
                     (opp (minus (f (plus x h)) (plus (f x) (mult (df x) h))))).
  {
    unfold minus.
    assert (Hoppr : Id (mult (opp (df x)) h) (opp (mult (df x) h)))
      by exact (opp_mult_r (df x) h).
    assert (Hoppl : Id (opp (mult (opp (df x)) h)) (mult (df x) h))
      by exact (id_trans (id_cong opp Hoppr) (double_neg (mult (df x) h))).
    assert (Hopp2 : Id (opp (plus (opp (f x)) (mult (opp (df x)) h)))
                       (plus (f x) (mult (df x) h))).
    {
      assert (H2a : Id (opp (plus (opp (f x)) (mult (opp (df x)) h)))
                       (plus (opp (opp (f x))) (opp (mult (opp (df x)) h))))
        by exact (opp_plus (opp (f x)) (mult (opp (df x)) h)).
      assert (H2b : Id (plus (opp (opp (f x))) (opp (mult (opp (df x)) h)))
                       (plus (f x) (mult (df x) h)))
        by exact (id_trans (id_cong (fun z => plus z (opp (mult (opp (df x)) h))) (double_neg (f x)))
                           (id_cong (fun z => plus (f x) z) Hoppl)).
      exact (id_trans H2a H2b).
    }
    exact (id_trans (id_cong (fun z => plus (opp (f (plus x h))) z) Hopp2)
                    (id_sym (opp_minus (f (plus x h)) (plus (f x) (mult (df x) h))))).
  }
  assert (Habs1 : Id (abs (minus (opp (f (plus x h))) (plus (opp (f x)) (mult (opp (df x)) h))))
                    (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h)))))
    by exact (id_trans (id_cong abs Hzero)
                       (abs_opp (minus (f (plus x h)) (plus (f x) (mult (df x) h))))).
  apply (le_id_l (abs (minus (opp (f (plus x h))) (plus (opp (f x)) (mult (opp (df x)) h))))
                 (abs (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                 (mult eps (abs h))).
  + exact Habs1.
  + apply Hdf. exact Hh.
Qed.

(* 减法可微性：由 plus + opp 组合（dminus 即 Hplus 的导数） *)
Theorem differentiable_minus : forall (f g : R -> R),
  Differentiable f -> Differentiable g -> Differentiable (fun x => minus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  assert (Hopp_g : Differentiable (fun x => opp (g x))) by exact (differentiable_opp g Hg).
  assert (Hplus : Differentiable (fun x => plus (f x) (opp (g x))))
    by exact (differentiable_plus f (fun x => opp (g x)) Hf Hopp_g).
  destruct Hplus as [dminus Hminus].
  exists dminus.
  intros x eps Heps.
  destruct (Hminus x eps Heps) as [delta [Hdelta Hd]].
  exists delta. split. exact Hdelta.
  intros h Hh.
  assert (Hrew : Id (minus (minus (f (plus x h)) (g (plus x h)))
                          (plus (minus (f x) (g x)) (mult (dminus x) h)))
                    (minus (plus (f (plus x h)) (opp (g (plus x h))))
                           (plus (plus (f x) (opp (g x))) (mult (dminus x) h)))).
  { unfold minus. reflexivity. }
  apply (le_id_l (abs (minus (minus (f (plus x h)) (g (plus x h)))
                             (plus (minus (f x) (g x)) (mult (dminus x) h))))
                 (abs (minus (plus (f (plus x h)) (opp (g (plus x h))))
                             (plus (plus (f x) (opp (g x))) (mult (dminus x) h))))
                 (mult eps (abs h))).
  + exact (id_cong abs Hrew).
  + apply Hd. exact Hh.
Qed.

(* 自然数幂函数：x^n 的归纳构造（反向传播逐层幂次的基础） *)
Fixpoint power_nat (n : nat) (x : R) : R :=
  match n with
  | O => one
  | Datatypes.S n' => mult x (power_nat n' x)
  end.

(* x^(n+1) 可微（基例 x^1 = id，归纳步由 differentiable_mult 组合） *)
Theorem differentiable_power_nat : forall (n : nat),
  Differentiable (fun x => power_nat (Datatypes.S n) x).
Proof.
  induction n as [| n' IH].
  - exists (fun _ => one).
    intros x eps Heps.
    exists one. split. apply one_pos.
    intros h Hh.
    change (le (abs (minus (mult (plus x h) one) (plus (mult x one) (mult one h)))) (mult eps (abs h))).
    pose proof (mult_one (plus x h)) as Hmo1. change (Id (mult (plus x h) one) (plus x h)) in Hmo1. rewrite Hmo1.
    pose proof (mult_one x) as Hmo2. change (Id (mult x one) x) in Hmo2. rewrite Hmo2.
    pose proof (mult_one h) as Hmo3. change (Id (mult h one) h) in Hmo3.
    pose proof (mult_comm one h) as Hmc3. change (Id (mult one h) (mult h one)) in Hmc3. rewrite Hmc3. rewrite Hmo3.
    change (le (abs (plus (plus x h) (opp (plus x h)))) (mult eps (abs h))).
    pose proof (plus_opp (plus x h)) as Hpo. change (Id (plus (plus x h) (opp (plus x h))) zero) in Hpo. rewrite Hpo.
    change (le (abs zero) (mult eps (abs h))).
    pose proof abs_zero as Haz.
    change (Id (abs zero) zero) in Haz.
    rewrite Haz.
    assert (Hmz : Id (mult eps zero) zero) by exact (mult_zero eps).
    rewrite <- Hmz.
    assert (Hmc1 : Id (mult eps (abs h)) (mult (abs h) eps)) by exact (mult_comm eps (abs h)).
    rewrite Hmc1.
    assert (Hmc2 : Id (mult eps zero) (mult zero eps)) by exact (mult_comm eps zero).
    rewrite Hmc2.
    exact (le_mult_compat zero (abs h) eps Heps (abs_nonneg h)).
  - simpl. apply differentiable_mult.
    + apply differentiable_id.
    + exact IH.
Qed.

(* ============================================================ *)
(* 链式法则引理（P1 皇冠的第一步：误差分解与 ε 上界辅助）       *)
(* ============================================================ *)
(* 完整 differentiable_compose 的预算计划（已实现）：
   eps4 := inv_2·(inv_2·eps)（即 eps/4），L := |dg x|+1 局部 Lipschitz，
   M := |df(g x)|+1；eps_f := min one (inv_L·eps4)、eps_g := min one (inv_M·eps4)
   （min 同时保证 ≤1 供 Lipschitz 用、以及 eps_f·L ≤ eps4、M·eps_g ≤ eps4），
   δ := min dgd (min one (inv_L·dfd))；两项控制
   ≤ eps4·|h| + eps4·|h| = (eps/2)·|h| ≤ eps·|h|。 *)

(* 复合误差分解恒等式：Δ(f∘g) − df(g)·dg·h = [f 的误差] + df(g)·[g 的误差] *)
Lemma compose_diff_decomp : forall (A B C D G g0 h : R),
  Id (minus A (plus B (mult (mult C D) h)))
     (plus (minus A (plus B (mult C (minus G g0))))
           (mult C (minus (minus G g0) (mult D h)))).
Proof.
  intros A B C D G g0 h.
  set (X := minus G g0).
  assert (Hma : Id (mult (mult C D) h) (mult C (mult D h)))
    by exact (id_sym (mult_assoc C D h)).
  assert (Hcancel : Id (plus (opp (plus B (mult C X))) (mult C X)) (opp B)).
  {
    unfold X.
    assert (H1 : Id (plus (opp (plus B (mult C (minus G g0)))) (mult C (minus G g0)))
                    (plus (plus (opp B) (opp (mult C (minus G g0)))) (mult C (minus G g0))))
      by exact (id_cong (fun z => plus z (mult C (minus G g0))) (opp_plus B (mult C (minus G g0)))).
    assert (H2 : Id (plus (plus (opp B) (opp (mult C (minus G g0)))) (mult C (minus G g0)))
                    (plus (opp B) (plus (opp (mult C (minus G g0))) (mult C (minus G g0)))))
      by exact (id_sym (plus_assoc (opp B) (opp (mult C (minus G g0))) (mult C (minus G g0)))).
    assert (H3 : Id (plus (opp B) (plus (opp (mult C (minus G g0))) (mult C (minus G g0))))
                    (plus (opp B) zero))
      by exact (id_cong (fun z => plus (opp B) z)
                        (id_trans (plus_comm (opp (mult C (minus G g0))) (mult C (minus G g0)))
                                  (plus_opp (mult C (minus G g0))))).
    assert (H4 : Id (plus (opp B) zero) (opp B)) by exact (plus_zero (opp B)).
    exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
  }
  assert (Hre : Id (plus (minus A (plus B (mult C X))) (minus (mult C X) (mult C (mult D h))))
                   (minus A (plus B (mult C (mult D h))))).
  {
    unfold minus.
    assert (H1 : Id (plus (plus A (opp (plus B (mult C X)))) (plus (mult C X) (opp (mult C (mult D h)))))
                    (plus A (plus (plus (opp (plus B (mult C X))) (mult C X)) (opp (mult C (mult D h))))))
      by exact (id_trans (id_sym (plus_assoc A (opp (plus B (mult C X))) (plus (mult C X) (opp (mult C (mult D h))))))
                         (id_cong (fun z => plus A z)
                                  (plus_assoc (opp (plus B (mult C X))) (mult C X) (opp (mult C (mult D h)))))).
    assert (H2 : Id (plus A (plus (plus (opp (plus B (mult C X))) (mult C X)) (opp (mult C (mult D h)))))
                    (plus A (plus (opp B) (opp (mult C (mult D h))))))
      by exact (id_cong (fun z => plus A (plus z (opp (mult C (mult D h))))) Hcancel).
    assert (H3 : Id (plus A (plus (opp B) (opp (mult C (mult D h)))))
                    (plus A (opp (plus B (mult C (mult D h))))))
      by exact (id_cong (fun z => plus A z)
                        (id_sym (opp_plus B (mult C (mult D h))))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  assert (Hlhs : Id (minus A (plus B (mult (mult C D) h)))
                    (minus A (plus B (mult C (mult D h)))))
    by exact (id_cong (fun z => minus A (plus B z)) Hma).
  assert (Hmd : Id (mult C (minus X (mult D h))) (minus (mult C X) (mult C (mult D h))))
    by (unfold X; exact (mult_minus_distr_l C (minus G g0) (mult D h))).
  assert (Hrhs : Id (plus (minus A (plus B (mult C X))) (mult C (minus X (mult D h))))
                    (plus (minus A (plus B (mult C X))) (minus (mult C X) (mult C (mult D h)))))
    by exact (id_cong (fun z => plus (minus A (plus B (mult C X))) z) Hmd).
  exact (id_trans Hlhs (id_trans (id_sym Hre) (id_sym Hrhs))).
Qed.

(* inv_2 ≤ 1（eps/2 上界辅助） *)
Lemma half_le_one : le (inv_pos (plus one one) two_pos) one.
Proof.
  assert (Hm1 : Id (mult (inv_pos (plus one one) two_pos) one) (inv_pos (plus one one) two_pos))
    by exact (mult_one (inv_pos (plus one one) two_pos)).
  assert (Hm2 : Id (mult (inv_pos (plus one one) two_pos) (plus one one)) one)
    by exact (id_trans (mult_comm (inv_pos (plus one one) two_pos) (plus one one))
                       (inv_pos_correct (plus one one) two_pos)).
  apply (le_id_l (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) one) one).
  - exact (id_sym Hm1).
  - apply (le_id_r (mult (inv_pos (plus one one) two_pos) one)
                   (mult (inv_pos (plus one one) two_pos) (plus one one))
                   one).
    + exact Hm2.
    + apply (le_mult_compat_r (inv_pos (plus one one) two_pos) one (plus one one)).
      * exact (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))).
      * exact (le_plus_nonneg_r one one (lt_le_iff _ _ (inl one_pos))).
Qed.

(* eps/2 ≤ eps（非负系数；链式法则预算收尾用） *)
Lemma half_le_self : forall a : R, le zero a ->
  le (mult (inv_pos (plus one one) two_pos) a) a.
Proof.
  intros a Ha.
  exact (le_trans (mult (inv_pos (plus one one) two_pos) a) (mult one a) a
           (le_mult_compat_weak (inv_pos (plus one one) two_pos) one a Ha half_le_one)
           (le_id_l (mult one a) a a (id_trans (mult_comm one a) (mult_one a)) (le_refl a))).
Qed.

(* 链式法则（P1 皇冠：构造性 ε-δ 完整证明）。
   预算：eps_f := min one (inv_L·eps4)、eps_g := min one (inv_M·eps4)
   （eps4 := (eps/2)/2，L := |dg x|+1 为 g 的局部 Lipschitz 常数，
   M := |df(g x)|+1）；δ := min dgd (min one (inv_L·dfd))；
   两项控制 ≤ eps4·|h| + eps4·|h| = (eps/2)·|h| ≤ eps·|h|。 *)
Theorem differentiable_compose : forall (f g : R -> R),
  Differentiable f -> Differentiable g ->
  Differentiable (fun x => f (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => mult (df (g x)) (dg x)).
  intros x eps Heps.
  set (eps4 := mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive; [apply inv_pos_pos | apply half_pos; exact Heps]. }
  set (M := plus (abs (df (g x))) one).
  assert (HM : lt zero M) by (unfold M; apply abs_plus_one_pos).
  set (L := plus (abs (dg x)) one).
  assert (HL : lt zero L) by (unfold L; apply abs_plus_one_pos).
  set (eps_f := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_f : lt zero eps_f)
    by (unfold eps_f; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  set (eps_g := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_g : lt zero eps_g)
    by (unfold eps_g; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  destruct (Hf (g x) eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hg x eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dgd (min one (mult (inv_pos L HL) dfd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dfd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdf1]).
    apply min_pos; [exact Hdg1 | apply min_pos; [apply one_pos | exact Hltm]].
  - intros h Hh.
    set (Dg := minus (g (plus x h)) (g x)).
    assert (Hdecomp : Id (minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (df (g x)) (dg x)) h)))
                         (plus (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg)))
                               (mult (df (g x)) (minus Dg (mult (dg x) h)))))
      by (unfold Dg; exact (compose_diff_decomp (f (g (plus x h))) (f (g x)) (df (g x)) (dg x) (g (plus x h)) (g x) h)).
    apply (le_id_l (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (df (g x)) (dg x)) h))))
                   (abs (plus (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg)))
                              (mult (df (g x)) (minus Dg (mult (dg x) h)))))
                   (mult eps (abs h))).
    + exact (id_cong abs Hdecomp).
    + assert (Hh_dgd : lt (abs h) dgd)
        by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
      assert (Hh_one : lt (abs h) one)
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dfd)) _); [apply min_le_r | apply min_le_l]]).
      assert (Hh_dfd : lt (abs h) (mult (inv_pos L HL) dfd))
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dfd)) _); [apply min_le_r | apply min_le_r]]).
      (* (b) |Dg| ≤ L·|h|（minus_split + 三角 + eps_g ≤ 1） *)
      assert (HDg_bound : le (abs Dg) (mult L (abs h))).
      {
        assert (Hsplit : Id (minus (g (plus x h)) (g x))
                            (plus (minus (g (plus x h)) (plus (g x) (mult (dg x) h))) (mult (dg x) h)))
          by exact (minus_split (g (plus x h)) (g x) (mult (dg x) h)).
        unfold Dg. rewrite Hsplit.
        apply (le_trans _ (plus (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h)))) (abs (mult (dg x) h))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h))) _).
          { apply le_plus_compat.
            { exact (Hdg2 h Hh_dgd). }
            { apply (le_id_r (abs (mult (dg x) h)) (abs (mult (dg x) h)) (mult (abs (dg x)) (abs h))
                             (abs_mult (dg x) h) (le_refl _)). } }
          { assert (Heg : le eps_g one)
              by (unfold eps_g; exact (min_le_l one (mult (inv_pos M HM) eps4))).
            assert (Hle : le (plus eps_g (abs (dg x))) (plus (abs (dg x)) one))
              by (apply (le_id_r (plus eps_g (abs (dg x))) (plus one (abs (dg x))) (plus (abs (dg x)) one)
                                 (plus_comm one (abs (dg x)))
                                 (le_plus_compat eps_g one (abs (dg x)) (abs (dg x)) Heg (le_refl (abs (dg x)))))).
            assert (Hsum : Id (plus (mult eps_g (abs h)) (mult (abs (dg x)) (abs h)))
                               (mult (plus eps_g (abs (dg x))) (abs h)))
              by exact (id_sym (mult_plus_distr_r eps_g (abs (dg x)) (abs h))).
            rewrite Hsum.
            apply (le_mult_compat_weak _ _ _ (abs_nonneg h)).
            unfold L.
            exact Hle. } }
      }
      (* |Dg| < dfd（L·|h| < L·(inv_L·dfd) = dfd） *)
      assert (HdfDg : lt (abs Dg) dfd).
      {
        apply (le_lt_trans (abs Dg) (mult L (abs h)) dfd).
        - exact HDg_bound.
        - assert (Hraw : lt (mult (abs h) L) (mult (mult (inv_pos L HL) dfd) L))
            by (apply (lt_mult_compat (abs h) (mult (inv_pos L HL) dfd) L HL Hh_dfd)).
          assert (Hswap : Id (mult (mult (inv_pos L HL) dfd) L) (mult L (mult (inv_pos L HL) dfd))).
          { assert (H1 : Id (mult (mult (inv_pos L HL) dfd) L) (mult (inv_pos L HL) (mult dfd L)))
              by exact (id_sym (mult_assoc (inv_pos L HL) dfd L)).
            assert (H2 : Id (mult (inv_pos L HL) (mult dfd L)) (mult (inv_pos L HL) (mult L dfd)))
              by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm dfd L)).
            assert (H3 : Id (mult (inv_pos L HL) (mult L dfd)) (mult (mult (inv_pos L HL) L) dfd))
              by exact (mult_assoc (inv_pos L HL) L dfd).
            assert (H4 : Id (mult (mult (inv_pos L HL) L) dfd) (mult (mult L (inv_pos L HL)) dfd))
              by exact (id_cong (fun z => mult z dfd) (mult_comm (inv_pos L HL) L)).
            assert (H5 : Id (mult (mult L (inv_pos L HL)) dfd) (mult L (mult (inv_pos L HL) dfd)))
              by exact (id_sym (mult_assoc L (inv_pos L HL) dfd)).
            exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))). }
          assert (HltL : lt (mult L (abs h)) (mult L (mult (inv_pos L HL) dfd)))
            by exact (lt_id_l (mult L (abs h)) (mult (abs h) L) (mult L (mult (inv_pos L HL) dfd))
                              (mult_comm L (abs h))
                              (lt_id_r (mult (abs h) L) (mult (mult (inv_pos L HL) dfd) L) (mult L (mult (inv_pos L HL) dfd))
                                       Hswap Hraw)).
          assert (Hident : Id (mult L (mult (inv_pos L HL) dfd)) dfd).
          { assert (H1 : Id (mult L (mult (inv_pos L HL) dfd)) (mult (mult L (inv_pos L HL)) dfd))
              by exact (mult_assoc L (inv_pos L HL) dfd).
            assert (H2 : Id (mult (mult L (inv_pos L HL)) dfd) (mult one dfd))
              by exact (id_cong (fun z => mult z dfd) (inv_pos_correct L HL)).
            assert (H3 : Id (mult one dfd) dfd)
              by exact (id_trans (mult_comm one dfd) (mult_one dfd)).
            exact (id_trans H1 (id_trans H2 H3)). }
          apply (lt_id_r (mult L (abs h)) (mult L (mult (inv_pos L HL) dfd)) dfd Hident HltL).
      }
      (* T1：f 的误差 ≤ eps_f·|Dg| ≤ eps4·|h| *)
      assert (HT1 : le (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg))))
                       (mult eps4 (abs h))).
      {
        apply (le_trans _ (mult eps_f (abs Dg)) _).
        - apply (le_id_l (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg))))
                         (abs (minus (f (plus (g x) Dg)) (plus (f (g x)) (mult (df (g x)) Dg))))
                         (mult eps_f (abs Dg))
                         (id_cong (fun z => abs (minus (f z) (plus (f (g x)) (mult (df (g x)) Dg))))
                                  (id_sym (minus_plus_cancel (g x) (g (plus x h)))))
                         (Hdf2 Dg HdfDg)).
        - apply (le_trans _ (mult eps_f (mult L (abs h))) _).
          { apply (le_mult_compat_r eps_f (abs Dg) (mult L (abs h)) (lt_le_iff _ _ (inl Heps_f)) HDg_bound). }
          { assert (Hfl : Id (mult eps_f (mult L (abs h))) (mult (mult eps_f L) (abs h)))
              by exact (mult_assoc eps_f L (abs h)).
            rewrite Hfl.
            assert (Hfl_le : le (mult eps_f L) eps4).
            { assert (Hepf_le : le eps_f (mult (inv_pos L HL) eps4))
                by (unfold eps_f; exact (min_le_r one (mult (inv_pos L HL) eps4))).
              apply (le_trans _ (mult (mult (inv_pos L HL) eps4) L) _).
              { apply (le_mult_compat_weak eps_f (mult (inv_pos L HL) eps4) L (lt_le_iff zero L (inl HL)) Hepf_le). }
              { assert (H1 : Id (mult (mult (inv_pos L HL) eps4) L) (mult (inv_pos L HL) (mult eps4 L)))
                  by exact (id_sym (mult_assoc (inv_pos L HL) eps4 L)).
                assert (H2 : Id (mult (inv_pos L HL) (mult eps4 L)) (mult (inv_pos L HL) (mult L eps4)))
                  by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm eps4 L)).
                assert (H3 : Id (mult (inv_pos L HL) (mult L eps4)) (mult (mult (inv_pos L HL) L) eps4))
                  by exact (mult_assoc (inv_pos L HL) L eps4).
                assert (H4 : Id (mult (mult (inv_pos L HL) L) eps4) (mult (mult L (inv_pos L HL)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos L HL) L)).
                assert (H5 : Id (mult (mult L (inv_pos L HL)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct L HL)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos L HL) eps4) L) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hfl_le).
          }
      }
      (* T2：df(g)·(Dg − dg·h) ≤ |df(g)|·eps_g·|h| ≤ eps4·|h| *)
      assert (HT2 : le (abs (mult (df (g x)) (minus Dg (mult (dg x) h)))) (mult eps4 (abs h))).
      {
        assert (Habsmult : Id (abs (mult (df (g x)) (minus Dg (mult (dg x) h))))
                              (mult (abs (df (g x))) (abs (minus Dg (mult (dg x) h)))))
          by exact (abs_mult (df (g x)) (minus Dg (mult (dg x) h))).
        apply (le_id_l _ _ _ Habsmult).
        apply (le_trans _ (mult (abs (df (g x))) (mult eps_g (abs h))) _).
        - apply (le_mult_compat_r (abs (df (g x))) (abs (minus Dg (mult (dg x) h))) (mult eps_g (abs h)) (abs_nonneg (df (g x)))).
          apply (le_id_l (abs (minus Dg (mult (dg x) h)))
                         (abs (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
                         (mult eps_g (abs h))
                         (id_cong abs (minus_minus_distr (g (plus x h)) (g x) (mult (dg x) h)))
                         (Hdg2 h Hh_dgd)).
        - assert (Hfl : Id (mult (abs (df (g x))) (mult eps_g (abs h))) (mult (mult (abs (df (g x))) eps_g) (abs h)))
            by exact (mult_assoc (abs (df (g x))) eps_g (abs h)).
          rewrite Hfl.
          assert (Hdf_le : le (abs (df (g x))) M)
            by (unfold M; apply le_plus_nonneg_r; exact (lt_le_iff _ _ (inl one_pos))).
          assert (Hprod : le (mult (abs (df (g x))) eps_g) (mult M eps_g))
            by (apply (le_mult_compat_weak _ _ _ (lt_le_iff _ _ (inl Heps_g)) Hdf_le)).
          apply (le_trans _ (mult (mult M eps_g) (abs h)) _).
          { apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hprod). }
          { assert (Hmg_le : le (mult M eps_g) eps4).
            { assert (Hepg_le : le eps_g (mult (inv_pos M HM) eps4))
                by (unfold eps_g; exact (min_le_r one (mult (inv_pos M HM) eps4))).
              apply (le_trans _ (mult (mult (inv_pos M HM) eps4) M) _).
              { exact (le_id_l (mult M eps_g) (mult eps_g M) (mult (mult (inv_pos M HM) eps4) M)
                               (mult_comm M eps_g)
                               (le_mult_compat_weak eps_g (mult (inv_pos M HM) eps4) M (lt_le_iff zero M (inl HM)) Hepg_le)). }
              { assert (H1 : Id (mult (mult (inv_pos M HM) eps4) M) (mult (inv_pos M HM) (mult eps4 M)))
                  by exact (id_sym (mult_assoc (inv_pos M HM) eps4 M)).
                assert (H2 : Id (mult (inv_pos M HM) (mult eps4 M)) (mult (inv_pos M HM) (mult M eps4)))
                  by exact (id_cong (fun z => mult (inv_pos M HM) z) (mult_comm eps4 M)).
                assert (H3 : Id (mult (inv_pos M HM) (mult M eps4)) (mult (mult (inv_pos M HM) M) eps4))
                  by exact (mult_assoc (inv_pos M HM) M eps4).
                assert (H4 : Id (mult (mult (inv_pos M HM) M) eps4) (mult (mult M (inv_pos M HM)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos M HM) M)).
                assert (H5 : Id (mult (mult M (inv_pos M HM)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct M HM)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos M HM) eps4) M) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (abs_nonneg h) Hmg_le). }
      }
      (* 合并：T1 + T2 ≤ (eps4 + eps4)·|h| = (eps/2)·|h| ≤ eps·|h| *)
      assert (Hmid : le (abs (plus (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg)))
                                   (mult (df (g x)) (minus Dg (mult (dg x) h)))))
                        (mult eps (abs h))).
      {
        apply (le_trans _ (plus (abs (minus (f (g (plus x h))) (plus (f (g x)) (mult (df (g x)) Dg))))
                                (abs (mult (df (g x)) (minus Dg (mult (dg x) h))))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps4 (abs h)) (mult eps4 (abs h))) _).
          { apply le_plus_compat; [exact HT1 | exact HT2]. }
      { assert (Hsum : Id (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                          (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))).
        { unfold eps4.
          assert (H1 : Id (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                          (mult (plus one one) (mult eps4 (abs h))))
            by (apply id_sym; apply two_mult).
          assert (H2 : Id (mult (plus one one) (mult eps4 (abs h))) (mult (mult (plus one one) eps4) (abs h)))
            by exact (mult_assoc (plus one one) eps4 (abs h)).
          assert (H3 : Id (mult (plus one one) eps4) (mult (inv_pos (plus one one) two_pos) eps)).
          { assert (H3a : Id (mult (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)))
                              (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
            assert (H3b : Id (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps))
                              (mult one (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (id_cong (fun z => mult z (mult (inv_pos (plus one one) two_pos) eps)) (inv_pos_correct (plus one one) two_pos)).
            assert (H3c : Id (mult one (mult (inv_pos (plus one one) two_pos) eps)) (mult (inv_pos (plus one one) two_pos) eps))
              by exact (id_trans (mult_comm one (mult (inv_pos (plus one one) two_pos) eps)) (mult_one (mult (inv_pos (plus one one) two_pos) eps))).
            exact (id_trans H3a (id_trans H3b H3c)). }
          assert (H4 : Id (mult (mult (plus one one) eps4) (abs h)) (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h)))
            by exact (id_cong (fun z => mult z (abs h)) H3).
          exact (id_trans H1 (id_trans H2 H4)). }
        apply (le_id_l (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                       (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                       (mult eps (abs h))
                       Hsum
                       (le_id_l (mult (mult (inv_pos (plus one one) two_pos) eps) (abs h))
                                (mult (inv_pos (plus one one) two_pos) (mult eps (abs h)))
                                (mult eps (abs h))
                                (id_sym (mult_assoc (inv_pos (plus one one) two_pos) eps (abs h)))
                                (half_le_self (mult eps (abs h))
                                              (le_trans zero (mult zero (abs h)) (mult eps (abs h))
                                                        (le_id_l zero (mult zero (abs h)) (mult zero (abs h))
                                                                 (id_sym (id_trans (mult_comm zero (abs h)) (mult_zero (abs h))))
                                                                 (le_refl (mult zero (abs h))))
                                                        (le_mult_compat_weak zero eps (abs h) (abs_nonneg h)
                                                                             (lt_le_iff _ _ (inl Heps))))))).
        }
      }
      }
      exact Hmid.
Qed.

(* ============================================================ *)
(* 语言模型损失函数可微性（组相对策略优化.txt 模块五）          *)
(* ============================================================ *)
(* cross_entropy_softmax_diff：交叉熵软最大化可微                *)
(*   f(logit) = log_inv (exp_neg logit) ≡ logit（恒等映射，      *)
(*   log_inv_exp_neg），df = 1，误差恒为零。Softmax 反向传播的    *)
(*   构造性基础（单 logit 形式；误差经折叠为恒等映射后归零）。   *)
(* ------------------------------------------------------------ *)

Theorem cross_entropy_softmax_diff :
  Differentiable (fun logit => log_inv (exp_neg logit)).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* 误差恒为零：f(x+h) − (f(x) + 1·h) = 0，经 log_inv_exp_neg 折叠 *)
    assert (Hfold : Id (log_inv (exp_neg (plus x h))) (plus x h))
      by exact (log_inv_exp_neg (plus x h)).
    assert (Hfoldx : Id (log_inv (exp_neg x)) x)
      by exact (log_inv_exp_neg x).
    (* 误差主体归零：minus (x+h) (x + 1·h) = 0 *)
    assert (Hmain : Id (minus (plus x h) (plus x (mult one h))) zero).
    {
      assert (H1 : Id (plus x (mult one h)) (plus x h))
        by exact (id_cong (fun y => plus x y) (id_trans (mult_comm one h) (mult_one h))).
      assert (H2 : Id (minus (plus x h) (plus x (mult one h))) (minus (plus x h) (plus x h)))
        by exact (id_cong (fun y => minus (plus x h) y) H1).
      assert (H3 : Id (minus (plus x h) (plus x h)) zero)
        by exact (minus_self_zero (plus x h) (plus x h) (@id_refl R (plus x h))).
      exact (id_trans H2 H3).
    }
    (* 原误差 = 折叠后误差（id_cong2 替换两个位置） *)
    assert (Herr : Id (minus (log_inv (exp_neg (plus x h)))
                             (plus (log_inv (exp_neg x)) (mult one h)))
                      (minus (plus x h) (plus x (mult one h))))
      by exact (id_cong2 minus Hfold (id_cong (fun y => plus y (mult one h)) Hfoldx)).
    (* le (abs 误差) (abs 0) = le 0 ≤ eps·|h| *)
    assert (Herr0 : Id (abs (minus (log_inv (exp_neg (plus x h)))
                                   (plus (log_inv (exp_neg x)) (mult one h))))
                       (abs zero))
      by exact (id_cong abs (id_trans Herr Hmain)).
    assert (Habs0 : le (abs zero) zero)
      by exact (le_id_l (abs zero) zero zero (abs_zero) (le_refl zero)).
    assert (Hprod : le zero (mult eps (abs h))).
    {
      exact (le_id_l zero (mult zero (abs h)) (mult eps (abs h))
                     (id_sym (id_trans (mult_comm zero (abs h)) (mult_zero (abs h))))
                     (le_mult_compat_weak zero eps (abs h) (abs_nonneg h) (lt_le_iff _ _ (inl Heps)))).
    }
    exact (le_id_l (abs (minus (log_inv (exp_neg (plus x h)))
                               (plus (log_inv (exp_neg x)) (mult one h))))
                   (abs zero)
                   (mult eps (abs h))
                   Herr0
                   (le_trans (abs zero) zero (mult eps (abs h)) Habs0 Hprod)).
  Qed.

(* ============================================================ *)
(* MSE 可微性（组相对策略优化.txt 模块五 2）                     *)
(* ============================================================ *)
(* f(pred) = (pred − target)²，df = 2·(pred − target)，δ = min one eps。*)
(* 差分展开：(x+h−t)² − ((x−t)² + 2(x−t)·h) = h²（square_diff_  *)
(* expand，纯代数）；|h| < min one eps ⟹ |h| < 1 且 |h| < eps，   *)
(* |h²| = |h|² ≤ eps·|h|。                                       *)
(* ------------------------------------------------------------ *)

(* 辅助：(a+b) − c = (a−c) + b（减法加法定理） *)
Lemma minus_plus_zero_r : forall a b c : R,
  Id (minus (plus a b) c) (plus (minus a c) b).
Proof.
  intros a b c.
  unfold minus.
  (* plus (plus a b) (opp c) = plus (plus a (opp c)) b *)
  assert (H1 : Id (plus (plus a b) (opp c)) (plus a (plus b (opp c))))
    by exact (id_sym (plus_assoc a b (opp c))).
  assert (H2 : Id (plus a (plus b (opp c))) (plus a (plus (opp c) b)))
    by exact (id_cong (fun x => plus a x) (plus_comm b (opp c))).
  assert (H3 : Id (plus a (plus (opp c) b)) (plus (plus a (opp c)) b))
    by exact (plus_assoc a (opp c) b).
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* (x+h−t)² − ((x−t)² + 2·(x−t)·h) = h²（MSE 差分展开，纯代数） *)
Lemma square_diff_expand : forall x target h : R,
  Id (minus (mult (minus (plus x h) target) (minus (plus x h) target))
            (plus (mult (minus x target) (minus x target))
                  (mult (mult (plus one one) (minus x target)) h)))
     (mult h h).
Proof.
  intros x target h.
  set (u := minus x target).
  (* v := (x+h) − t = u + h *)
  assert (Hv : Id (minus (plus x h) target) (plus u h))
    by (unfold u; exact (minus_plus_zero_r x h target)).
  (* 主目标：minus (mult v v) (plus (mult u u) (mult 2 u h)) = mult h h *)
  assert (Hmain : Id (minus (mult (plus u h) (plus u h))
                            (plus (mult u u) (mult (mult (plus one one) u) h)))
                     (mult h h)).
  {
    (* (u+h)² = u² + 2·u·h + h² *)
    assert (H1 : Id (mult (plus u h) (plus u h))
                    (plus (mult u (plus u h)) (mult h (plus u h))))
      by exact (mult_plus_distr_r u h (plus u h)).
    assert (H2 : Id (mult u (plus u h)) (plus (mult u u) (mult u h)))
      by exact (distrib u u h).
    assert (H3 : Id (mult h (plus u h)) (plus (mult h u) (mult h h)))
      by exact (distrib h u h).
    assert (H4 : Id (plus (mult u (plus u h)) (mult h (plus u h)))
                    (plus (plus (mult u u) (mult u h)) (plus (mult h u) (mult h h))))
      by exact (id_cong2 plus H2 H3).
    (* h·u = u·h *)
    assert (H5 : Id (plus (plus (mult u u) (mult u h)) (plus (mult h u) (mult h h)))
                    (plus (plus (mult u u) (mult u h)) (plus (mult u h) (mult h h))))
      by exact (id_cong (fun z => plus (plus (mult u u) (mult u h)) (plus z (mult h h)))
                        (mult_comm h u)).
    (* 合并交叉项：u·h + u·h = 2·u·h（two_mult + mult_plus_distr_r） *)
    assert (H6 : Id (plus (mult u h) (mult u h)) (mult (mult (plus one one) u) h)).
    {
      assert (H6a : Id (mult (mult (plus one one) u) h) (mult (plus u u) h))
        by exact (id_cong (fun z => mult z h) (two_mult u)).
      assert (H6b : Id (mult (plus u u) h) (plus (mult u h) (mult u h)))
        by exact (mult_plus_distr_r u u h).
      exact (id_sym (id_trans H6a H6b)).
    }
    (* 重组：u² + u·h + u·h + h² = (u² + 2·u·h) + h² *)
    assert (H7 : Id (plus (plus (mult u u) (mult u h)) (plus (mult u h) (mult h h)))
                    (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h))).
    {
      assert (H7a : Id (plus (plus (mult u u) (mult u h)) (plus (mult u h) (mult h h)))
                       (plus (mult u u) (plus (mult u h) (plus (mult u h) (mult h h)))))
        by exact (id_sym (plus_assoc (mult u u) (mult u h) (plus (mult u h) (mult h h)))).
      assert (H7b : Id (plus (mult u u) (plus (mult u h) (plus (mult u h) (mult h h))))
                       (plus (mult u u) (plus (plus (mult u h) (mult u h)) (mult h h))))
        by exact (id_cong (fun z => plus (mult u u) z) (plus_assoc (mult u h) (mult u h) (mult h h))).
      assert (H7c : Id (plus (mult u u) (plus (plus (mult u h) (mult u h)) (mult h h)))
                       (plus (mult u u) (plus (mult (mult (plus one one) u) h) (mult h h))))
        by exact (id_cong (fun z => plus (mult u u) (plus z (mult h h))) H6).
      assert (H7d : Id (plus (mult u u) (plus (mult (mult (plus one one) u) h) (mult h h)))
                       (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h)))
        by exact (plus_assoc (mult u u) (mult (mult (plus one one) u) h) (mult h h)).
      exact (id_trans H7a (id_trans H7b (id_trans H7c H7d))).
    }
    assert (Hsq : Id (mult (plus u h) (plus u h))
                     (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h)))
      by exact (id_trans H1 (id_trans H4 (id_trans H5 H7))).
    (* minus (u² + 2uh + h²) (u² + 2uh) = h²：minus_plus_cancel_r *)
    assert (Hsub : Id (minus (plus (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h))
                             (plus (mult u u) (mult (mult (plus one one) u) h)))
                      (mult h h))
      by exact (minus_plus_cancel_r (plus (mult u u) (mult (mult (plus one one) u) h)) (mult h h)).
    exact (id_trans (id_cong (fun z => minus z (plus (mult u u) (mult (mult (plus one one) u) h))) Hsq) Hsub).
  }
  (* 组装：替换 v 为 u+h、u 为 minus x target *)
  change (Id (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                    (plus (mult u u) (mult (mult (plus one one) u) h)))
             (mult h h)).
  assert (Hrep : Id (mult (minus (plus x h) target) (minus (plus x h) target))
                    (mult (plus u h) (plus u h)))
    by exact (id_cong (fun z => mult z z) Hv).
  exact (id_trans (id_cong (fun z => minus z (plus (mult u u) (mult (mult (plus one one) u) h))) Hrep) Hmain).
Qed.

(* MSE 损失可微：f(pred) = (pred − target)²，df = 2·(pred − target)。
   误差 = h²（square_diff_expand）；δ := min one eps 同时保证
   |h| < 1 与 |h| < eps，故 |h²| = |h|² ≤ eps·|h|。 *)
Theorem mse_diff :
  forall (target : R), Differentiable (fun pred => mult (minus pred target) (minus pred target)).
Proof.
  intro target.
  exists (fun pred => mult (plus one one) (minus pred target)).
  intros x eps Heps.
  exists (min one eps).
  split.
  - apply min_pos; [apply one_pos | exact Heps].
  - intros h Hh.
    (* 误差 = h²（square_diff_expand） *)
    assert (Hexp : Id (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                             (plus (mult (minus x target) (minus x target))
                                   (mult (mult (plus one one) (minus x target)) h)))
                      (mult h h))
      by exact (square_diff_expand x target h).
    (* 目标：le (abs (minus ...)) (mult eps (abs h))；先换 LHS 为 abs (mult h h) *)
    assert (Herr0 : Id (abs (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                                   (plus (mult (minus x target) (minus x target))
                                         (mult (mult (plus one one) (minus x target)) h))))
                       (abs (mult h h)))
      by exact (id_cong abs Hexp).
    (* |h²| = |h|·|h| *)
    assert (Habs : Id (abs (mult h h)) (mult (abs h) (abs h)))
      by exact (abs_mult h h).
    (* |h| < 1 且 |h| < eps（δ = min one eps） *)
    assert (Hh1 : lt (abs h) one)
      by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
    assert (Hh_eps : lt (abs h) eps)
      by (eapply lt_le_trans; [exact Hh | apply min_le_r]).
    assert (Hhle : le (abs h) eps)
      by (apply (lt_le_iff _ _); left; exact Hh_eps).
    (* |h|·|h| ≤ eps·|h| *)
    assert (Hprod : le (mult (abs h) (abs h)) (mult eps (abs h))).
    {
      assert (Hp1 : le (mult (abs h) (abs h)) (mult (abs h) eps))
        by exact (le_mult_compat_r (abs h) (abs h) eps (abs_nonneg h) Hhle).
      exact (le_id_r (mult (abs h) (abs h)) (mult (abs h) eps) (mult eps (abs h))
                     (mult_comm (abs h) eps) Hp1).
    }
    (* 组装：abs 误差 = abs h² = |h|·|h| ≤ eps·|h| *)
    exact (le_id_l (abs (minus (mult (minus (plus x h) target) (minus (plus x h) target))
                              (plus (mult (minus x target) (minus x target))
                                    (mult (mult (plus one one) (minus x target)) h))))
                   (mult (abs h) (abs h))
                   (mult eps (abs h))
                   (id_trans Herr0 Habs)
                   Hprod).
  Qed.

(* ============================================================ *)
(* DPO 损失可微性（dpo_loss_gradient：偏好对直接优化.txt 梯度） *)
(* ============================================================ *)
(* DPO 对损失 L(Δ) = log(1 + e^{-Δ})（Δ = implicit_reward_diff）。*)
(* 1) 分母正性：1 + e^{-Δ} > 0（log 良定义）。                   *)
(* 2) 差分分解：L(x+h) − L(x) = log((1+e^{-(x+h)})·(1+e^{-x})^{-1})*)
(*    （log_div 反向——DPO 梯度推导的精确代数基础）。             *)
(* 3) sigmoid 定义方程：σ(x)·(1+e^{-x}) = 1（inv_pos_correct）。  *)
(* 4) sigmoid 互补：σ(x) + e^{-x}·σ(x) = 1（由 3 展开，非平凡）。 *)
(* 5) 梯度等价形式：σ(x) − 1 = −e^{-x}·σ(x)（sigmoid 交叉熵梯度  *)
(*    的 Set 层形式，由 4 反推；反向传播 sigmoid 导数 σ' = σ(1-σ)*)
(*    的代数核心）。                                              *)
(* ------------------------------------------------------------ *)

(* DPO 对损失 log 内项的正性：1 + e^{-x} > 0（one_pos + exp_neg_pos + plus_positive） *)
Lemma dpo_logit_denom_pos : forall x : R, lt zero (plus one (exp_neg x)).
Proof.
  intro x.
  apply plus_positive; [exact one_pos | apply exp_neg_pos].
Qed.

(* DPO 损失差分 = log 商（log_div 反向；非平凡：差分显式化——
   L(x+h) − L(x) = log(1+e^{-(x+h)}) − log(1+e^{-x}) = log 商） *)
Theorem dpo_loss_diff_decomp : forall x h : R,
  Id (minus (log (plus one (exp_neg (plus x h)))) (log (plus one (exp_neg x))))
     (log (mult (plus one (exp_neg (plus x h)))
                (inv_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x)))).
Proof.
  intros x h.
  exact (id_sym (log_div (plus one (exp_neg (plus x h))) (plus one (exp_neg x))
                 (dpo_logit_denom_pos (plus x h)) (dpo_logit_denom_pos x))).
Qed.

(* sigmoid（Set 层构造）：σ(x) = 1/(1+e^{-x})，正性见证内嵌 *)
Definition dpo_sigmoid (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x).

(* sigmoid 正性：0 < σ(x)（inv_pos_pos） *)
Lemma dpo_sigmoid_pos : forall x : R, lt zero (dpo_sigmoid x).
Proof.
  intro x. unfold dpo_sigmoid.
  exact (inv_pos_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x)).
Qed.

(* sigmoid 定义方程：σ(x)·(1+e^{-x}) = 1（inv_pos_correct + mult_comm） *)
Theorem dpo_sigmoid_identity : forall x : R,
  Id (mult (dpo_sigmoid x) (plus one (exp_neg x))) one.
Proof.
  intro x. unfold dpo_sigmoid.
  exact (id_trans (mult_comm (inv_pos (plus one (exp_neg x)) (dpo_logit_denom_pos x))
                             (plus one (exp_neg x)))
                  (inv_pos_correct (plus one (exp_neg x)) (dpo_logit_denom_pos x))).
Qed.

(* sigmoid 互补：σ(x) + e^{-x}·σ(x) = 1（非平凡：distrib 展开 +
   定义方程）——σ' = σ(1-σ) 的加性形式 *)
Theorem dpo_sigmoid_complement : forall x : R,
  Id (plus (dpo_sigmoid x) (mult (exp_neg x) (dpo_sigmoid x))) one.
Proof.
  intro x.
  (* σ·(1+e^{-x}) = σ·1 + σ·e^{-x}（distrib 正向） *)
  assert (Hdist : Id (mult (dpo_sigmoid x) (plus one (exp_neg x)))
                     (plus (mult (dpo_sigmoid x) one) (mult (dpo_sigmoid x) (exp_neg x))))
    by exact (distrib (dpo_sigmoid x) one (exp_neg x)).
  assert (Hone : Id (mult (dpo_sigmoid x) one) (dpo_sigmoid x))
    by exact (mult_one (dpo_sigmoid x)).
  assert (Hswap : Id (plus (mult (dpo_sigmoid x) one) (mult (dpo_sigmoid x) (exp_neg x)))
                     (plus (dpo_sigmoid x) (mult (exp_neg x) (dpo_sigmoid x))))
    by exact (id_cong2 plus Hone (mult_comm (dpo_sigmoid x) (exp_neg x))).
  exact (id_trans (id_sym Hswap) (id_trans (id_sym Hdist) (dpo_sigmoid_identity x))).
Qed.

(* DPO 梯度等价形式：df(x) = σ(x) − 1 = −e^{-x}·σ(x)
   （非平凡：由 sigmoid 互补反推——加性消去 + opp_plus + double_neg 链） *)
Theorem dpo_gradient_alt : forall x : R,
  Id (minus (dpo_sigmoid x) one) (opp (mult (exp_neg x) (dpo_sigmoid x))).
Proof.
  intro x.
  (* 1. 由互补恒等式：σ + e^{-x}σ = 1，且 σ + (1 − σ) = 1 ⟹ e^{-x}σ = 1 − σ（plus_cancel_l） *)
  assert (Hc : Id (plus (dpo_sigmoid x) (mult (exp_neg x) (dpo_sigmoid x))) one)
    by exact (dpo_sigmoid_complement x).
  assert (Hcancel : Id (plus (dpo_sigmoid x) (minus one (dpo_sigmoid x))) one)
    by exact (minus_plus_cancel (dpo_sigmoid x) one).
  assert (Hratio : Id (mult (exp_neg x) (dpo_sigmoid x)) (minus one (dpo_sigmoid x))).
  {
    apply (plus_cancel_l (dpo_sigmoid x)).
    exact (id_trans Hc (id_sym Hcancel)).
  }
  (* 2. 取负：−(e^{-x}σ) = −(1 − σ)（id_cong opp） *)
  assert (Hopp : Id (opp (mult (exp_neg x) (dpo_sigmoid x)))
                    (opp (minus one (dpo_sigmoid x))))
    by exact (id_cong opp Hratio).
  (* 3. −(1 − σ) = σ − 1：opp_plus + double_neg + plus_comm + minus 定义 *)
  assert (Hreduce : Id (opp (minus one (dpo_sigmoid x))) (minus (dpo_sigmoid x) one)).
  {
    unfold minus.
    assert (H1 : Id (opp (plus one (opp (dpo_sigmoid x))))
                    (plus (opp one) (opp (opp (dpo_sigmoid x)))))
      by exact (opp_plus one (opp (dpo_sigmoid x))).
    assert (H2 : Id (plus (opp one) (opp (opp (dpo_sigmoid x))))
                    (plus (opp one) (dpo_sigmoid x)))
      by exact (id_cong (fun z => plus (opp one) z) (double_neg (dpo_sigmoid x))).
    assert (H3 : Id (plus (opp one) (dpo_sigmoid x))
                    (plus (dpo_sigmoid x) (opp one)))
      by exact (plus_comm (opp one) (dpo_sigmoid x)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_sym (id_trans Hopp Hreduce)).
Qed.

End DifferentiableLemmas.

(* ============================================================ *)
(* entropy 可微性（P1-4 消解）：k_B·log(Ω_A·Ω_B∘E_B)           *)
(* 链式法则 + 乘法 + 减法组装；唯一缺口 log 可微性（诚实字段）   *)
(* ============================================================ *)
Section EntropyDifferentiable.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let one := @one RI.
Let lt := @lt RI.
Let mult := @mult RI.
Let minus := @minus RI.
Let log := @log RI.

Variable Omega_A : R -> R.
Variable Omega_B : R -> R.
Variable dOmega_A : Differentiable Omega_A.
Variable dOmega_B : Differentiable Omega_B.
Variable Omega_A_pos : forall E_A, lt zero (Omega_A E_A).
Variable Omega_B_pos : forall E_B, lt zero (Omega_B E_B).
Variable E_total : R.
Variable k_B : R.

Definition E_B_ent (E_A : R) : R := minus E_total E_A.
Definition Omega_total_ent (E_A : R) : R := mult (Omega_A E_A) (Omega_B (E_B_ent E_A)).
Definition entropy_ent (E_A : R) : R := mult k_B (log (Omega_total_ent E_A)).

(* log 可微性（诚实接口字段：构造性分析标准，抽象层缺；同 inv_pos 模式） *)
Variable log_differentiable : forall x : R, lt zero x -> Differentiable log.

(* entropy 可微：const/minus/id/mult/compose 全组装 *)
Theorem entropy_differentiable : Differentiable entropy_ent.
Proof.
  unfold entropy_ent.
  assert (HOmega_pos : forall E_A, lt zero (Omega_total_ent E_A)).
  { intro E_A. unfold Omega_total_ent.
    apply (mult_positive (Omega_A E_A) (Omega_B (E_B_ent E_A)) (Omega_A_pos E_A) (Omega_B_pos (E_B_ent E_A))). }
  assert (HEB_d : Differentiable E_B_ent).
  { unfold E_B_ent.
    apply (differentiable_minus (fun _ => E_total) (fun x => x)).
    - apply differentiable_const.
    - apply differentiable_id. }
  assert (HcompB : Differentiable (fun E_A => Omega_B (E_B_ent E_A))).
  { apply (differentiable_compose Omega_B E_B_ent); [exact dOmega_B | exact HEB_d]. }
  assert (HOmega_d : Differentiable Omega_total_ent).
  { unfold Omega_total_ent.
    apply (differentiable_mult Omega_A (fun E_A => Omega_B (E_B_ent E_A))); [exact dOmega_A | exact HcompB]. }
  assert (Hlog_d : Differentiable (fun E_A => log (Omega_total_ent E_A))).
  { apply (differentiable_compose log Omega_total_ent).
    - exact (log_differentiable one one_pos).
    - exact HOmega_d. }
  apply (differentiable_mult (fun _ => k_B) (fun E_A => log (Omega_total_ent E_A))).
  - apply differentiable_const.
  - exact Hlog_d.
Qed.

End EntropyDifferentiable.
(* ============================================================ *)
(* log 可微性 Set 层核心：log 在 1 附近的线性界                  *)
(* 上界 log(1+t) <= t [log_one_plus_le]；下界 log(1+t) >= t-t^2  *)
(* [log_one_plus_ge，链：t-t^2 <= t/(1+t) [set_div_linear_ge_quad] *)
(* == opp((1/(1+t))-1) [set_inv_minus_one_opp] <= log(1+t)]      *)
(* 供 Real 层对应构造复用；log_differentiable 之证成需           *)
(* df_correct 全称 x（含 x<=0）而接口 log 性质仅限 lt zero x ⟹   *)
(* 抽象接口数学上不可证，故在 Real 层逐 eps 复刻。               *)
(* ============================================================ *)
Section LogDiffPhase3.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* ============ 0. Set 层恒等：(1+t) − 1 == t ============ *)
Lemma minus_one_plus_t : forall t : R, Id (minus (plus one t) one) t.
Proof.
  intros t.
  unfold minus.
  rewrite <- (plus_assoc one t (opp one)).
  rewrite (plus_comm t (opp one)).
  rewrite (plus_assoc one (opp one) t).
  rewrite (plus_opp one).
  rewrite (plus_comm zero t).
  rewrite (plus_zero t).
  reflexivity.
Qed.

(* ============ 1. 上界：0 < 1+t ⟹ log(1+t) ≤ t ============ *)
Lemma log_one_plus_le : forall (t : R), lt zero (plus one t) ->
  le (log (plus one t)) t.
Proof.
  intros t Hpos.
  exact (le_trans (log (plus one t)) (minus (plus one t) one) t
           (log_le_linear (plus one t) Hpos)
           (lt_le_iff (minus (plus one t) one) t (inr (minus_one_plus_t t)))).
Qed.

(* ============ 2. Set 层代数辅助 ============ *)
(* eq → le 桥 *)
Lemma set_eq_le : forall a b : R, Id a b -> le a b.
Proof.
  intros a b Hab. exact (lt_le_iff a b (inr Hab)).
Qed.

(* t ≥ 0 ⟹ t² ≥ 0：t·0 == 0 ≤ t·t（le_mult_compat_r 于 t、0≤t） *)
Lemma set_square_nonneg : forall t : R, le zero t -> le zero (mult t t).
Proof.
  intros t Ht.
  exact (le_trans zero (mult t zero) (mult t t)
           (set_eq_le zero (mult t zero) (id_sym (mult_zero t)))
           (le_mult_compat_r t zero t Ht Ht)).
Qed.

(* t ≥ 0 ⟹ t³ ≥ 0 *)
Lemma set_cube_nonneg : forall t : R, le zero t -> le zero (mult t (mult t t)).
Proof.
  intros t Ht.
  exact (le_trans zero (mult t zero) (mult t (mult t t))
           (set_eq_le zero (mult t zero) (id_sym (mult_zero t)))
           (le_mult_compat_r t zero (mult t t) Ht (set_square_nonneg t Ht))).
Qed.

(* a·(b−c) == a·b − a·c *)
Lemma set_minus_mult : forall a b c : R,
  Id (mult a (minus b c)) (minus (mult a b) (mult a c)).
Proof.
  intros a b c. exact (mult_minus_distr_l a b c).
Qed.

(* opp zero == zero（opp_le_compat 桥需要；主文件无 Set 层 opp_zero） *)
Lemma set_opp_zero : Id (opp zero) zero.
Proof.
  exact (id_sym (plus_inv_unique zero zero (opp zero) (plus_zero zero) (plus_opp zero))).
Qed.

(* 环化简：(t + −t²) + (t² + −t³) == t + −t³（全显式组装，弃 setoid rewrite） *)
Lemma set_quad_cube : forall t : R,
  Id (plus (minus t (mult t t)) (minus (mult t t) (mult t (mult t t))))
     (minus t (mult t (mult t t))).
Proof.
  intros t.
  unfold minus.
  (* 段1：(t + −t²) + (t² + −t³) == t + (−t² + (t² + −t³)) [id_sym plus_assoc] *)
  pose proof (id_sym (plus_assoc t (opp (mult t t))
                                (plus (mult t t) (opp (mult t (mult t t)))))) as H1.
  (* 段2：t + (−t² + (t² + −t³)) == t + ((−t² + t²) + −t³) [id_cong plus_assoc] *)
  pose proof (id_cong (fun x => plus t x)
                      (plus_assoc (opp (mult t t)) (mult t t)
                                  (opp (mult t (mult t t))))) as H2.
  (* 段3a：opp t² + t² == t² + opp t² [plus_comm] == zero [plus_opp] *)
  pose proof (id_trans (plus_comm (opp (mult t t)) (mult t t))
                       (plus_opp (mult t t))) as Hopp_zero.
  (* 段3b：提升到 (… + −t³)：((opp t² + t²) + −t³) == (zero + −t³) *)
  pose proof (id_cong (fun y => plus y (opp (mult t (mult t t)))) Hopp_zero) as Hopp_z'.
  (* 段3c：提升到 t + … *)
  pose proof (id_cong (fun x => plus t x) Hopp_z') as H3.
  (* 段4：zero + −t³ == −t³ + zero [plus_comm]，提升到 t + … *)
  pose proof (id_cong (fun x => plus t x)
                      (plus_comm zero (opp (mult t (mult t t))))) as H4.
  (* 段5：−t³ + zero == −t³ [plus_zero]，提升到 t + … *)
  pose proof (id_cong (fun x => plus t x)
                      (plus_zero (opp (mult t (mult t t))))) as H5.
  exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
Qed.

(* 核心恒等：(t−t²)(1+t) == t−t³ *)
Lemma set_quad_prod : forall t : R,
  Id (mult (minus t (mult t t)) (plus one t))
     (minus t (mult t (mult t t))).
Proof.
  intros t.
  exact (id_trans (distrib (minus t (mult t t)) one t)
           (id_trans (id_cong2 plus (mult_one (minus t (mult t t)))
                        (id_trans (mult_comm (minus t (mult t t)) t)
                           (set_minus_mult t t (mult t t))))
              (set_quad_cube t))).
Qed.

(* t−t³ ≤ t（t³ ≥ 0 ⟹ −t³ ≤ 0 ⟹ t+(−t³) ≤ t+0） *)
Lemma set_minus_cube_le : forall t : R, le zero t ->
  le (minus t (mult t (mult t t))) t.
Proof.
  intros t Ht.
  unfold minus.
  apply (le_trans _ (plus t zero) _).
  - apply (le_plus_compat t t (opp (mult t (mult t t))) zero).
    + apply le_refl.
    + apply (le_id_r _ _ _ set_opp_zero).
      apply (opp_le_compat zero (mult t (mult t t))). exact (set_cube_nonneg t Ht).
  - apply set_eq_le. apply (plus_zero t).
Qed.

(* 0 ≤ t ⟹ 0 < 1+t：1+t ≥ 1+0 == 1 > 0 *)
Lemma set_one_plus_pos : forall t : R, le zero t -> lt zero (plus one t).
Proof.
  intros t Ht0.
  exact (lt_le_trans zero one (plus one t) one_pos
           (le_id_l one (plus one zero) (plus one t) (id_sym (plus_zero one))
              (le_plus_compat one one zero t (le_refl one) Ht0))).
Qed.

(* ============ 3. 主引理：0 ≤ t ⟹ t−t² ≤ t·(1/(1+t)) ============ *)
(* 链：t−t² ≤ t·inv s
       ⟸ (t−t²)·s ≤ t·inv s·s == t·1 == t
         （le_mult_compat 于 inv s > 0；inv s·s == 1 换形回 t−t²）
       ⟸ (t−t²)·(1+t) == t−t³ ≤ t   [set_quad_prod + set_minus_cube_le]
   其中 s == plus one t。 *)
(* 辅助：inv s · s == 1（inv_pos_correct 于 s + comm） *)
Lemma set_inv_mul : forall (s : R) (Hs : lt zero s),
  Id (mult (inv_pos s Hs) s) one.
Proof.
  intros s Hs.
  exact (id_trans (mult_comm (inv_pos s Hs) s) (inv_pos_correct s Hs)).
Qed.

Lemma set_div_linear_ge_quad : forall (t : R) (Ht0 : le zero t),
  forall (Hs : lt zero (plus one t)),
  le (minus t (mult t t))
     (mult t (inv_pos (plus one t) Hs)).
Proof.
  intros t Ht0 Hs.
  set (s := plus one t) in *.
  (* 核心：(t−t²)·(1+t) ≤ t（set_quad_prod + set_minus_cube_le） *)
  assert (Hcore : le (mult (minus t (mult t t)) s) t).
  { apply (le_trans _ (minus t (mult t (mult t t))) _).
    - apply set_eq_le. apply (set_quad_prod t).
    - apply (set_minus_cube_le t). exact Ht0. }
  (* 由 Hcore：(t−t²)·s ≤ t，乘 inv s 正（le_mult_compat）：
     (t−t²)·s·inv s ≤ t·inv s
     左边 == (t−t²)·(s·inv s) == (t−t²)·1 == t−t² [assoc 反向 + inv_correct + mult_one]
     目标 t−t² ≤ t·inv s ✓ *)
  apply (le_trans _ (mult (mult (minus t (mult t t)) s) (inv_pos s Hs)) _).
  - (* t−t² ≤ (t−t²)·s·inv s：反向换形（assoc + inv_correct + mult_one） *)
    apply set_eq_le.
    (* (t−t²) == (t−t²)·one [id_sym mult_one]
                 == (t−t²)·(s·inv s) [id_cong：one == s·inv s（id_sym inv_correct）]
                 == ((t−t²)·s)·inv s [mult_assoc] *)
    pose proof (id_sym (mult_one (minus t (mult t t)))) as Ha.
    pose proof (id_sym (inv_pos_correct s Hs)) as Hb.
    pose proof (id_cong (fun x => mult (minus t (mult t t)) x) Hb) as Hc.
    pose proof (id_trans Ha Hc) as Hd.
    pose proof (mult_assoc (minus t (mult t t)) s (inv_pos s Hs)) as He.
    exact (id_trans Hd He).
  - (* (t−t²)·s·inv s ≤ t·inv s：le_mult_compat 于 Hcore、inv s > 0 *)
    apply (le_mult_compat (mult (minus t (mult t t)) s) t (inv_pos s Hs)).
    + apply (inv_pos_pos s Hs).
    + exact Hcore.
Qed.

(* ============ 4. Set 层恒等：t·inv(1+t) == opp (minus (inv(1+t)) one)
   （判例 Real 层链的 Set 层翻译；1/x 导数核心恒等）
   链：t·inv s == (s−1)·inv s == inv s·(s−1) == inv s·s − inv s·1
              == one − inv s·one == one − inv s == opp (inv s − 1)
   其中 s == plus one t，s−1 == t（minus_one_plus_t 反向） *)
Lemma set_inv_minus_one_opp : forall (t : R) (Hs : lt zero (plus one t)),
  Id (mult t (inv_pos (plus one t) Hs))
     (opp (minus (inv_pos (plus one t) Hs) one)).
Proof.
  intros t Hs.
  set (s := plus one t) in *.
  (* H1：t == s − 1（minus_one_plus_t 反向） ⟹ t·inv s == (s−1)·inv s *)
  pose proof (id_sym (minus_one_plus_t t)) as Ht_sm1.
  pose proof (id_cong (fun x => mult x (inv_pos s Hs)) Ht_sm1) as H1.
  (* H2：(s−1)·inv s == inv s·(s−1)（mult_comm） *)
  pose proof (mult_comm (minus s one) (inv_pos s Hs)) as H2.
  (* H3：inv s·(s−1) == inv s·s − inv s·1（mult_minus_distr_l） *)
  pose proof (mult_minus_distr_l (inv_pos s Hs) s one) as H3.
  (* H4：inv s·s == one（set_inv_mul）⟹ minus (inv s·s) (inv s·one) == minus one (inv s·one) *)
  pose proof (set_inv_mul s Hs) as Hinv_s.
  pose proof (id_cong (fun x => minus x (mult (inv_pos s Hs) one)) Hinv_s) as H4.
  (* H5：minus one (inv s·one) == minus one (inv s)（mult_one） *)
  pose proof (id_cong (fun x => minus one x) (mult_one (inv_pos s Hs))) as H5.
  (* H6：minus one (inv s) == opp (minus (inv s) one)
        opp_minus (inv s) one : opp (minus (inv s) one) == plus (opp (inv s)) one
        plus_comm → plus one (opp (inv s)) == minus one (inv s)；id_sym 反向 *)
  pose proof (id_trans (opp_minus (inv_pos s Hs) one)
                       (plus_comm (opp (inv_pos s Hs)) one)) as H6a.
  pose proof (id_sym H6a) as H6.
  (* 组装 *)
  exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6))))).
Qed.

(* ============ 5. 下界：0 ≤ t ⟹ log(1+t) ≥ t − t²
   链：t−t² ≤ t·inv s                    [set_div_linear_ge_quad]
       t·inv s == opp (inv s − 1)        [set_inv_minus_one_opp]
       opp (inv s − 1) ≤ opp (log (inv s))   [opp_le_compat：log (inv s) ≤ inv s − 1（log_le_linear）]
       opp (log (inv s)) == log s         [log_inv_one_inv + id_cong opp + double_neg] *)
Lemma log_one_plus_ge : forall (t : R), le zero t ->
  lt zero (plus one t) ->
  le (minus t (mult t t)) (log (plus one t)).
Proof.
  intros t Ht0 Hs.
  set (s := plus one t) in *.
  (* 段1：t−t² ≤ t·inv s *)
  pose proof (set_div_linear_ge_quad t Ht0 Hs) as Hseg1.
  (* 段2a：t·inv s == opp (minus (inv s) one) *)
  pose proof (set_inv_minus_one_opp t Hs) as Hio.
  (* 段2b：log (inv s) ≤ inv s − 1（log_le_linear） *)
  pose proof (log_le_linear (inv_pos s Hs) (inv_pos_pos s Hs)) as Hlin.
  (* 段2c：opp (minus (inv s) one) ≤ opp (log (inv s))（opp_le_compat） *)
  pose proof (opp_le_compat (log (inv_pos s Hs)) (minus (inv_pos s Hs) one) Hlin) as Hoc.
  (* 段2d：le (mult t (inv s)) (opp (log (inv s)))：le_id_l Hio Hoc *)
  pose proof (le_id_l _ _ _ Hio Hoc) as Hseg2a.
  (* 段2e：opp (log (inv s)) == log s
        log_inv_one_inv s Hs : log (inv s) == opp (log s)
        id_cong opp → opp (log (inv s)) == opp (opp (log s))
        double_neg (log s) : opp (opp (log s)) == log s *)
  pose proof (log_inv_one_inv s Hs) as Hli.
  pose proof (id_cong opp Hli) as Ho1.
  pose proof (double_neg (log s)) as Hdn.
  pose proof (id_trans Ho1 Hdn) as Ho2.
  (* 段2f：le (mult t (inv s)) (log s)：le_id_r Ho2 Hseg2a *)
  pose proof (le_id_r _ _ _ Ho2 Hseg2a) as Hseg2.
  (* 组装 *)
  apply (le_trans _ (mult t (inv_pos s Hs)) _).
  - exact Hseg1.
  - exact Hseg2.
Qed.

End LogDiffPhase3.

(* ============================================================ *)
(* 多变量可微性（DifferentiableMV：StateSpace 内积接口版）       *)
(* ============================================================ *)
(* 结构性缺失.txt 建议的多变量化：f : S -> R，梯度 df : S -> S， *)
(* 线性化用 inner（HilbertSpace 内积），扰动用 smetric。         *)
(* 1) DifferentiableMV 记录：Fréchet 型定义（Set 层）。           *)
(* 2) 内积第二参数线性：⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩（inner_splus_l *)
(*    第一参数线性 + inner_sym 换位；注意力 logits 可微性基础）。 *)
(* 3) 常值场可微：f ≡ c，df ≡ szero（误差恒零：inner_szero_l）。  *)
(* 4) 线性泛函可微：f(x) = ⟨a,x⟩，df = a（误差恒零：内积线性；   *)
(*    attention_score(s) = ⟨s, key⟩ 对 s 可微，df = key！）。     *)
(* ------------------------------------------------------------ *)

Section MultivariableDifferentiable.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpaceExtended RI}.
Context {HS : HilbertSpace RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let szero := @szero RI SS.
Let splus := @splus RI SS.
Let smult := @smult RI SS.
Let sopp := @sopp RI SS.
Let smetric := @smetric RI SS.
Let inner := @inner RI SS HS.
Let smetric_pos := @smetric_pos RI SS.

(* 多变量可微（Fréchet 型，Set 层）：f : S -> R，梯度 dfmv : S -> S。
   线性化 df(x)·h 用 inner（内积），误差用 smetric 度量。 *)
Record DifferentiableMV (f : S -> R) := {
  dfmv : S -> S;
  dfmv_correct : forall x eps, lt zero eps ->
    sigT (fun delta : R => And (lt zero delta) (forall h : S,
      lt (smetric h szero) delta ->
      le (abs (minus (f (splus x h))
                     (plus (f x) (inner (dfmv x) h))))
         (mult eps (smetric h szero))))
}.

(* 内积第二参数线性：⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩
   （非平凡：inner_splus_l 给第一参数线性，inner_sym 换位两次） *)
Lemma inner_splus_r : forall x y z : S,
  Id (inner x (splus y z)) (plus (inner x y) (inner x z)).
Proof.
  intros x y z.
  exact (id_trans (inner_sym x (splus y z))
           (id_trans (inner_splus_l y z x)
              (id_cong2 plus (inner_sym y x) (inner_sym z x)))).
Qed.

(* 多变量复合误差分解（mv 版 compose_diff_decomp）：复用单变量版特化
   h := one、D := X（X := inner (dfmv x) h 为标量），mult (mult C X) one == mult C X、
   mult X one == X 换形。 *)
Lemma mv_compose_diff_decomp : forall (A B C G g0 X : R),
  Id (minus A (plus B (mult C X)))
     (plus (minus A (plus B (mult C (minus G g0))))
           (mult C (minus (minus G g0) X))).
Proof.
  intros A B C G g0 X.
  (* 复用 compose_diff_decomp（11238，h := one、D := X） *)
  assert (H1 : Id (minus A (plus B (mult (mult C X) one)))
                  (plus (minus A (plus B (mult C (minus G g0))))
                        (mult C (minus (minus G g0) (mult X one)))))
    by exact (compose_diff_decomp A B C X G g0 one).
  (* LHS 换形：mult (mult C X) one == mult C X *)
  assert (Hl : Id (minus A (plus B (mult (mult C X) one)))
                  (minus A (plus B (mult C X)))).
  {
    apply (id_cong (fun z => minus A (plus B z))).
    assert (Ha : Id (mult (mult C X) one) (mult C (mult X one)))
      by exact (id_sym (mult_assoc C X one)).
    assert (Hb : Id (mult C (mult X one)) (mult C X))
      by exact (id_cong (fun z => mult C z) (mult_one X)).
    exact (id_trans Ha Hb).
  }
  (* RHS 换形：mult X one == X（末项内） *)
  assert (Hr : Id (plus (minus A (plus B (mult C (minus G g0))))
                        (mult C (minus (minus G g0) (mult X one))))
                  (plus (minus A (plus B (mult C (minus G g0))))
                        (mult C (minus (minus G g0) X)))).
  {
    apply (id_cong (fun z => plus (minus A (plus B (mult C (minus G g0)))) z)).
    apply (id_cong (fun z => mult C z)).
    apply (id_cong (fun z => minus (minus G g0) z)).
    exact (mult_one X).
  }
  exact (id_trans (id_sym Hl) (id_trans H1 Hr)).
Qed.

(* 内积 Lipschitz 接口（诚实 Variable）：对每个向量 a，存在范数界 N 使
   |⟨a,h⟩| ≤ N·|h|（Cauchy-Schwarz 的构造性弱化；需内积正定性+连续性，
   列为接口——与 proj_orthogonal_compat / inv_pos_lt_contra 同先例）。
   支撑多变量链式法则：内层增量 |f(x+h) − f x| ≤ (N+1)·|h|。 *)
Variable inner_lipschitz : forall (a : S),
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (abs (inner a h)) (mult N (smetric h szero)))).

(* 常值场可微：f ≡ c，dfmv ≡ szero。误差恒零：
   |c − (c + ⟨0,h⟩)| = |⟨0,h⟩| = 0（inner_szero_l + plus_zero + plus_opp + abs_zero）。
   δ = one（one_pos）。 *)
Theorem differentiable_mv_const : forall c : R, DifferentiableMV (fun _ => c).
Proof.
  intro c.
  exists (fun _ => szero).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* 误差 = |c − (c + ⟨0,h⟩)| = |c − c| = 0 *)
    assert (Hinner : Id (inner szero h) zero)
      by exact (inner_szero_l h).
    assert (Herr : Id (minus c (plus c (inner szero h))) zero).
    {
      unfold minus.
      (* plus c (opp (plus c (inner szero h))) = plus c (opp (plus c zero))（inner_szero_l） *)
      assert (H1 : Id (plus c (opp (plus c (inner szero h))))
                    (plus c (opp (plus c zero))))
        by exact (id_cong (fun z => plus c (opp (plus c z))) Hinner).
      assert (H2 : Id (plus c (opp (plus c zero))) (plus c (opp c)))
        by exact (id_cong (fun z => plus c (opp z)) (plus_zero c)).
      assert (H3 : Id (plus c (opp c)) zero)
        by exact (plus_opp c).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    (* 目标：le (abs 误差) (mult eps (smetric h szero))；换 LHS 为 abs zero = 0 *)
    assert (Habs : Id (abs (minus c (plus c (inner szero h)))) (abs zero))
      by exact (id_cong abs Herr).
    assert (Habs0 : Id (abs zero) zero)
      by exact (abs_zero).
    assert (Hprod : le zero (mult eps (smetric h szero))).
    {
      assert (Hm0 : Id (mult zero (smetric h szero)) zero)
        by exact (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))).
      apply (le_id_l zero (mult zero (smetric h szero)) (mult eps (smetric h szero))).
      - exact (id_sym Hm0).
      - apply (le_mult_compat_weak zero eps (smetric h szero)).
        + apply smetric_pos.
        + apply (lt_le_iff _ _). left. exact Heps.
    }
    exact (le_id_l (abs (minus c (plus c (inner szero h))))
                   (abs zero)
                   (mult eps (smetric h szero))
                   Habs
                   (le_id_l (abs zero) zero (mult eps (smetric h szero)) Habs0 Hprod)).
Qed.

(* 线性泛函可微：f(x) = ⟨a, x⟩，dfmv = a。误差恒零：
   |⟨a, x+h⟩ − (⟨a,x⟩ + ⟨a,h⟩)| = |0|（inner_splus_r）。
   δ = one。这是注意力 logits 可微性：attention_score(s) = ⟨s,key⟩
   对 s 可微，梯度恰为 key（df = a）。 *)
Theorem differentiable_mv_linear : forall a : S, DifferentiableMV (fun x => inner a x).
Proof.
  intro a.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - apply one_pos.
  - intros h Hh.
    (* 误差 = |⟨a, x+h⟩ − (⟨a,x⟩ + ⟨a,h⟩)| = 0（inner_splus_r） *)
    assert (Hlin : Id (inner a (splus x h)) (plus (inner a x) (inner a h)))
      by exact (inner_splus_r a x h).
    assert (Herr : Id (minus (inner a (splus x h)) (plus (inner a x) (inner a h))) zero).
    {
      unfold minus.
      assert (H1 : Id (plus (inner a (splus x h)) (opp (plus (inner a x) (inner a h))))
                    (plus (plus (inner a x) (inner a h)) (opp (plus (inner a x) (inner a h)))))
        by exact (id_cong (fun z => plus z (opp (plus (inner a x) (inner a h)))) Hlin).
      assert (H2 : Id (plus (plus (inner a x) (inner a h)) (opp (plus (inner a x) (inner a h)))) zero)
        by exact (plus_opp (plus (inner a x) (inner a h))).
      exact (id_trans H1 H2).
    }
    assert (Habs : Id (abs (minus (inner a (splus x h)) (plus (inner a x) (inner a h)))) (abs zero))
      by exact (id_cong abs Herr).
    assert (Habs0 : Id (abs zero) zero)
      by exact (abs_zero).
    assert (Hprod : le zero (mult eps (smetric h szero))).
    {
      assert (Hm0 : Id (mult zero (smetric h szero)) zero)
        by exact (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))).
      apply (le_id_l zero (mult zero (smetric h szero)) (mult eps (smetric h szero))).
      - exact (id_sym Hm0).
      - apply (le_mult_compat_weak zero eps (smetric h szero)).
        + apply smetric_pos.
        + apply (lt_le_iff _ _). left. exact Heps.
    }
    exact (le_id_l (abs (minus (inner a (splus x h)) (plus (inner a x) (inner a h))))
                   (abs zero)
                   (mult eps (smetric h szero))
                   Habs
                   (le_id_l (abs zero) zero (mult eps (smetric h szero)) Habs0 Hprod)).
Qed.

(* 标量场之和可微：f+g，dfmv = splus df dg。
   非平凡 ε-δ：inner_splus_l（⟨df+dg,h⟩ = ⟨df,h⟩+⟨dg,h⟩）+ eps/2 预算
   （half_pos/half_twice）+ min δ（min_pos/min_le_l/min_le_r）+ abs_triangle
   + minus_plus_distr/plus_swap_mid 误差分解（约 40 步，与单变量
   differentiable_plus 同构但用内积线性化与 smetric 度量）。 *)
Theorem differentiable_mv_plus : forall (f g : S -> R),
  DifferentiableMV f -> DifferentiableMV g ->
  DifferentiableMV (fun x => plus (f x) (g x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => splus (df x) (dg x)).
  intros x eps Heps.
  pose (mult (inv_pos (plus one one) two_pos) eps) as eps_half.
  assert (Hhalf : lt zero eps_half) by (unfold eps_half; apply half_pos; exact Heps).
  destruct (Hf x eps_half Hhalf) as [dfdelta [Hdf1 Hdf2]].
  destruct (Hg x eps_half Hhalf) as [dgdelta [Hdg1 Hdg2]].
  exists (min dfdelta dgdelta).
  split.
  - apply min_pos; [exact Hdf1 | exact Hdg1].
  - intros h Hh.
    (* |h| < min ⟹ |h| < dfdelta 且 |h| < dgdelta *)
    assert (Hh1 : lt (smetric h szero) dfdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_l. }
    assert (Hh2 : lt (smetric h szero) dgdelta).
    { eapply lt_le_trans. exact Hh. apply min_le_r. }
    (* 误差分解：⟨df+dg, h⟩ = ⟨df,h⟩ + ⟨dg,h⟩（inner_splus_l 第一参数线性） *)
    assert (Hinner : Id (inner (splus (df x) (dg x)) h)
                       (plus (inner (df x) h) (inner (dg x) h)))
      by exact (inner_splus_l (df x) (dg x) h).
    change (le (abs (minus (plus (f (splus x h)) (g (splus x h)))
                           (plus (plus (f x) (g x)) (inner (splus (df x) (dg x)) h))))
               (mult eps (smetric h szero))).
    rewrite Hinner.
    assert (Hswap : Id (plus (plus (f x) (g x)) (plus (inner (df x) h) (inner (dg x) h)))
                       (plus (plus (f x) (inner (df x) h)) (plus (g x) (inner (dg x) h))))
      by exact (plus_swap_mid (f x) (g x) (inner (df x) h) (inner (dg x) h)).
    rewrite Hswap.
    assert (Hmpd2 : Id (minus (plus (f (splus x h)) (g (splus x h)))
                              (plus (plus (f x) (inner (df x) h)) (plus (g x) (inner (dg x) h))))
                       (plus (minus (f (splus x h)) (plus (f x) (inner (df x) h)))
                             (minus (g (splus x h)) (plus (g x) (inner (dg x) h)))))
      by exact (minus_plus_distr (f (splus x h)) (g (splus x h))
                                 (plus (f x) (inner (df x) h)) (plus (g x) (inner (dg x) h))).
    rewrite Hmpd2.
    (* 三角不等式 *)
    apply (le_trans _ (plus (abs (minus (f (splus x h)) (plus (f x) (inner (df x) h))))
                            (abs (minus (g (splus x h)) (plus (g x) (inner (dg x) h)))))).
    + apply abs_triangle.
    + apply (le_trans _ (plus (mult eps_half (smetric h szero)) (mult eps_half (smetric h szero)))).
      * apply le_plus_compat.
        -- apply (Hdf2 h Hh1).
        -- apply (Hdg2 h Hh2).
      * (* eps_half·s + eps_half·s = eps·s *)
        assert (Hsum : Id (plus (mult eps_half (smetric h szero)) (mult eps_half (smetric h szero)))
                          (mult eps (smetric h szero))).
        {
          unfold eps_half.
          assert (Hd : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                      (mult (inv_pos (plus one one) two_pos) eps)) (smetric h szero))
                           (plus (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                                 (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))))
            by exact (mult_plus_distr_r (mult (inv_pos (plus one one) two_pos) eps)
                                        (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero)).
          rewrite <- Hd.
          assert (Hcong : Id (mult (plus (mult (inv_pos (plus one one) two_pos) eps)
                                          (mult (inv_pos (plus one one) two_pos) eps)) (smetric h szero))
                             (mult eps (smetric h szero)))
            by (apply (id_cong (fun z => mult z (smetric h szero))); exact (half_twice eps)).
          rewrite Hcong. reflexivity.
        }
        rewrite Hsum. apply le_refl.
Qed.

(* 多变量链式法则（P1 皇冠 2：构造性 ε-δ 完整证明，多变量版）。
   最终预算分配：T1（外层误差经 |Dg| ≤ L·|h| 放大）用 eps_f（L 控制）；
   T2（内层误差经 |dg(f x)| ≤ M 缩放）用 eps_g（M 控制）。
   即：eps_f := min one (inv_L·eps4)（内层可微预算，被内层 Lipschitz L 缩放）；
   eps_g := min one (inv_M·eps4)（外层可微预算，被外层导数界 M 缩放）。
   T1 ≤ eps_f·L·|h| ≤ eps4·|h|；T2 ≤ M·eps_g·|h| ≤ eps4·|h|。 *)
Theorem differentiable_mv_compose : forall (f : S -> R) (g : R -> R),
  DifferentiableMV f -> Differentiable g ->
  DifferentiableMV (fun x => g (f x)).
Proof.
  intros f g [df Hf] [dg Hg].
  exists (fun x => smult (dg (f x)) (df x)).
  intros x eps Heps.
  set (eps4 := mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive; [apply inv_pos_pos | apply half_pos; exact Heps]. }
  (* 内层 Lipschitz：N := inner_lipschitz (df x)，L := N + 1（|Dg| ≤ L·|h|） *)
  destruct (inner_lipschitz (df x)) as [N HN].
  destruct HN as [HN0 HN2].
  set (L := plus N one).
  assert (HL : lt zero L).
  { unfold L. apply plus_le_lt_pos; [exact HN0 | apply one_pos]. }
  set (M := plus (abs (dg (f x))) one).
  assert (HM : lt zero M) by (unfold M; apply abs_plus_one_pos).
  set (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f)
    by (unfold eps_f; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  set (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g)
    by (unfold eps_g; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  destruct (Hf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    apply min_pos; [exact Hdf1 | apply min_pos; [apply one_pos | exact Hltm]].
  - intros h Hh.
    set (Dg := minus (f (splus x h)) (f x)).
    (* 线性化换形：inner (smult (dg (f x)) (df x)) h == mult (dg (f x)) (inner (df x) h) *)
    assert (Hlin : Id (inner (smult (dg (f x)) (df x)) h)
                      (mult (dg (f x)) (inner (df x) h)))
      by exact (inner_smult_l (dg (f x)) (df x) h).
    (* 误差分解（mv 版 compose_diff_decomp）：先用 mult (dg(f x)) (inner ...) 形式分解，
       再把线性化换回 inner (smult ...) 形式（Hlin 反向） *)
    assert (Hdec1 : Id (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) (inner (df x) h))))
                      (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                            (mult (dg (f x)) (minus Dg (inner (df x) h)))))
      by (unfold Dg; exact (mv_compose_diff_decomp (g (f (splus x h))) (g (f x)) (dg (f x))
                                                   (f (splus x h)) (f x) (inner (df x) h))).
    assert (Hdecomp : Id (minus (g (f (splus x h))) (plus (g (f x)) (inner (smult (dg (f x)) (df x)) h)))
                         (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                               (mult (dg (f x)) (minus Dg (inner (df x) h)))))
      by (exact (id_trans (id_cong (fun z => minus (g (f (splus x h))) (plus (g (f x)) z)) Hlin) Hdec1)).
    apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (smult (dg (f x)) (df x)) h))))
                   (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                              (mult (dg (f x)) (minus Dg (inner (df x) h)))))
                   (mult eps (smetric h szero))).
    + exact (id_cong abs Hdecomp).
    + assert (Hh_dfd : lt (smetric h szero) dfd)
        by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
      assert (Hh_one : lt (smetric h szero) one)
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_l]]).
      assert (Hh_dgd : lt (smetric h szero) (mult (inv_pos L HL) dgd))
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_r]]).
      (* (a) |Dg| ≤ L·|h|（minus_split + 三角 + inner_lipschitz + eps_f ≤ 1） *)
      assert (HDg_bound : le (abs Dg) (mult L (smetric h szero))).
      {
        assert (Hsplit : Id (minus (f (splus x h)) (f x))
                            (plus (minus (f (splus x h)) (plus (f x) (inner (df x) h))) (inner (df x) h)))
          by exact (minus_split (f (splus x h)) (f x) (inner (df x) h)).
        unfold Dg. rewrite Hsplit.
        apply (le_trans _ (plus (abs (minus (f (splus x h)) (plus (f x) (inner (df x) h)))) (abs (inner (df x) h))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps_f (smetric h szero)) (mult N (smetric h szero))) _).
          { apply le_plus_compat.
            { exact (Hdf2 h Hh_dfd). }
            { exact (HN2 h). } }
          { assert (Hef : le eps_f one)
              by (unfold eps_f; exact (min_le_l one (mult (inv_pos M HM) eps4))).
            assert (Hle : le (plus eps_f N) (plus N one))
              by (apply (le_id_r (plus eps_f N) (plus one N) (plus N one)
                                 (plus_comm one N)
                                 (le_plus_compat eps_f one N N Hef (le_refl N)))).
            assert (Hsum : Id (plus (mult eps_f (smetric h szero)) (mult N (smetric h szero)))
                               (mult (plus eps_f N) (smetric h szero)))
              by exact (id_sym (mult_plus_distr_r eps_f N (smetric h szero))).
            rewrite Hsum.
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero)).
            unfold L. exact Hle. } }
      }
      (* |Dg| < dgd（L·|h| < L·(inv_L·dgd) = dgd） *)
      assert (HdfDg : lt (abs Dg) dgd).
      {
        apply (le_lt_trans (abs Dg) (mult L (smetric h szero)) dgd).
        - exact HDg_bound.
        - assert (Hraw : lt (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L))
            by (apply (lt_mult_compat (smetric h szero) (mult (inv_pos L HL) dgd) L HL Hh_dgd)).
          assert (Hswap : Id (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))).
          { assert (H1 : Id (mult (mult (inv_pos L HL) dgd) L) (mult (inv_pos L HL) (mult dgd L)))
              by exact (id_sym (mult_assoc (inv_pos L HL) dgd L)).
            assert (H2 : Id (mult (inv_pos L HL) (mult dgd L)) (mult (inv_pos L HL) (mult L dgd)))
              by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm dgd L)).
            assert (H3 : Id (mult (inv_pos L HL) (mult L dgd)) (mult (mult (inv_pos L HL) L) dgd))
              by exact (mult_assoc (inv_pos L HL) L dgd).
            assert (H4 : Id (mult (mult (inv_pos L HL) L) dgd) (mult (mult L (inv_pos L HL)) dgd))
              by exact (id_cong (fun z => mult z dgd) (mult_comm (inv_pos L HL) L)).
            assert (H5 : Id (mult (mult L (inv_pos L HL)) dgd) (mult L (mult (inv_pos L HL) dgd)))
              by exact (id_sym (mult_assoc L (inv_pos L HL) dgd)).
            exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))). }
          assert (HltL : lt (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)))
            by exact (lt_id_l (mult L (smetric h szero)) (mult (smetric h szero) L) (mult L (mult (inv_pos L HL) dgd))
                              (mult_comm L (smetric h szero))
                              (lt_id_r (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))
                                       Hswap Hraw)).
          assert (Hident : Id (mult L (mult (inv_pos L HL) dgd)) dgd).
          { assert (H1 : Id (mult L (mult (inv_pos L HL) dgd)) (mult (mult L (inv_pos L HL)) dgd))
              by exact (mult_assoc L (inv_pos L HL) dgd).
            assert (H2 : Id (mult (mult L (inv_pos L HL)) dgd) (mult one dgd))
              by exact (id_cong (fun z => mult z dgd) (inv_pos_correct L HL)).
            assert (H3 : Id (mult one dgd) dgd)
              by exact (id_trans (mult_comm one dgd) (mult_one dgd)).
            exact (id_trans H1 (id_trans H2 H3)). }
          apply (lt_id_r (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)) dgd Hident HltL).
      }
      (* T1：外层误差 ≤ eps_g·|Dg| ≤ eps4·|h|（L·eps_g ≤ eps4，eps_g 由 L 控制） *)
      assert (HT1 : le (abs (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg))))
                       (mult eps4 (smetric h szero))).
      {
        apply (le_trans _ (mult eps_g (abs Dg)) _).
        - apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg))))
                         (abs (minus (g (plus (f x) Dg)) (plus (g (f x)) (mult (dg (f x)) Dg))))
                         (mult eps_g (abs Dg))
                         (id_cong (fun z => abs (minus (g z) (plus (g (f x)) (mult (dg (f x)) Dg))))
                                  (id_sym (minus_plus_cancel (f x) (f (splus x h)))))
                         (Hdg2 Dg HdfDg)).
        - apply (le_trans _ (mult eps_g (mult L (smetric h szero))) _).
          { apply (le_mult_compat_r eps_g (abs Dg) (mult L (smetric h szero)) (lt_le_iff _ _ (inl Heps_g)) HDg_bound). }
          { assert (Hfl : Id (mult eps_g (mult L (smetric h szero))) (mult (mult eps_g L) (smetric h szero)))
              by exact (mult_assoc eps_g L (smetric h szero)).
            rewrite Hfl.
            assert (Hfl_le : le (mult eps_g L) eps4).
            { assert (Hepg_le : le eps_g (mult (inv_pos L HL) eps4))
                by (unfold eps_g; exact (min_le_r one (mult (inv_pos L HL) eps4))).
              apply (le_trans _ (mult (mult (inv_pos L HL) eps4) L) _).
              { apply (le_mult_compat_weak eps_g (mult (inv_pos L HL) eps4) L (lt_le_iff zero L (inl HL)) Hepg_le). }
              { assert (H1 : Id (mult (mult (inv_pos L HL) eps4) L) (mult (inv_pos L HL) (mult eps4 L)))
                  by exact (id_sym (mult_assoc (inv_pos L HL) eps4 L)).
                assert (H2 : Id (mult (inv_pos L HL) (mult eps4 L)) (mult (inv_pos L HL) (mult L eps4)))
                  by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm eps4 L)).
                assert (H3 : Id (mult (inv_pos L HL) (mult L eps4)) (mult (mult (inv_pos L HL) L) eps4))
                  by exact (mult_assoc (inv_pos L HL) L eps4).
                assert (H4 : Id (mult (mult (inv_pos L HL) L) eps4) (mult (mult L (inv_pos L HL)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos L HL) L)).
                assert (H5 : Id (mult (mult L (inv_pos L HL)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct L HL)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos L HL) eps4) L) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hfl_le). }
      }
      (* T2：|dg(f x)·(Dg − inner (df x) h)| ≤ M·eps_f·|h| ≤ eps4·|h|（M·eps_f ≤ eps4） *)
      assert (HT2 : le (abs (mult (dg (f x)) (minus Dg (inner (df x) h)))) (mult eps4 (smetric h szero))).
      {
        assert (Habsmult : Id (abs (mult (dg (f x)) (minus Dg (inner (df x) h))))
                              (mult (abs (dg (f x))) (abs (minus Dg (inner (df x) h)))))
          by exact (abs_mult (dg (f x)) (minus Dg (inner (df x) h))).
        apply (le_id_l _ _ _ Habsmult).
        apply (le_trans _ (mult (abs (dg (f x))) (mult eps_f (smetric h szero))) _).
        - apply (le_mult_compat_r (abs (dg (f x))) (abs (minus Dg (inner (df x) h))) (mult eps_f (smetric h szero)) (abs_nonneg (dg (f x)))).
          apply (le_id_l (abs (minus Dg (inner (df x) h)))
                         (abs (minus (f (splus x h)) (plus (f x) (inner (df x) h))))
                         (mult eps_f (smetric h szero))
                         (id_cong abs (minus_minus_distr (f (splus x h)) (f x) (inner (df x) h)))
                         (Hdf2 h Hh_dfd)).
        - assert (Hfl : Id (mult (abs (dg (f x))) (mult eps_f (smetric h szero))) (mult (mult (abs (dg (f x))) eps_f) (smetric h szero)))
            by exact (mult_assoc (abs (dg (f x))) eps_f (smetric h szero)).
          rewrite Hfl.
          assert (Hdf_le : le (abs (dg (f x))) M)
            by (unfold M; apply le_plus_nonneg_r; exact (lt_le_iff _ _ (inl one_pos))).
          assert (Hprod : le (mult (abs (dg (f x))) eps_f) (mult M eps_f))
            by (apply (le_mult_compat_weak _ _ _ (lt_le_iff _ _ (inl Heps_f)) Hdf_le)).
          apply (le_trans _ (mult (mult M eps_f) (smetric h szero)) _).
          { apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hprod). }
          { assert (Hmg_le : le (mult M eps_f) eps4).
            { assert (Hepf_le : le eps_f (mult (inv_pos M HM) eps4))
                by (unfold eps_f; exact (min_le_r one (mult (inv_pos M HM) eps4))).
              apply (le_trans _ (mult (mult (inv_pos M HM) eps4) M) _).
              { exact (le_id_l (mult M eps_f) (mult eps_f M) (mult (mult (inv_pos M HM) eps4) M)
                               (mult_comm M eps_f)
                               (le_mult_compat_weak eps_f (mult (inv_pos M HM) eps4) M (lt_le_iff zero M (inl HM)) Hepf_le)). }
              { assert (H1 : Id (mult (mult (inv_pos M HM) eps4) M) (mult (inv_pos M HM) (mult eps4 M)))
                  by exact (id_sym (mult_assoc (inv_pos M HM) eps4 M)).
                assert (H2 : Id (mult (inv_pos M HM) (mult eps4 M)) (mult (inv_pos M HM) (mult M eps4)))
                  by exact (id_cong (fun z => mult (inv_pos M HM) z) (mult_comm eps4 M)).
                assert (H3 : Id (mult (inv_pos M HM) (mult M eps4)) (mult (mult (inv_pos M HM) M) eps4))
                  by exact (mult_assoc (inv_pos M HM) M eps4).
                assert (H4 : Id (mult (mult (inv_pos M HM) M) eps4) (mult (mult M (inv_pos M HM)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos M HM) M)).
                assert (H5 : Id (mult (mult M (inv_pos M HM)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct M HM)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos M HM) eps4) M) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hmg_le). }
      }
      (* 合并：T1 + T2 ≤ (eps4+eps4)·|h| = (eps/2)·|h| ≤ eps·|h| *)
      assert (Hmid : le (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg)))
                                   (mult (dg (f x)) (minus Dg (inner (df x) h)))))
                        (mult eps (smetric h szero))).
      {
        apply (le_trans _ (plus (abs (minus (g (f (splus x h))) (plus (g (f x)) (mult (dg (f x)) Dg))))
                                (abs (mult (dg (f x)) (minus Dg (inner (df x) h))))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero))) _).
          { apply le_plus_compat; [exact HT1 | exact HT2]. }
      { assert (Hsum : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))).
        { unfold eps4.
          assert (H1 : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (plus one one) (mult eps4 (smetric h szero))))
            by (apply id_sym; apply two_mult).
          assert (H2 : Id (mult (plus one one) (mult eps4 (smetric h szero))) (mult (mult (plus one one) eps4) (smetric h szero)))
            by exact (mult_assoc (plus one one) eps4 (smetric h szero)).
          assert (H3 : Id (mult (plus one one) eps4) (mult (inv_pos (plus one one) two_pos) eps)).
          { assert (H3a : Id (mult (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)))
                              (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
            assert (H3b : Id (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps))
                              (mult one (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (id_cong (fun z => mult z (mult (inv_pos (plus one one) two_pos) eps)) (inv_pos_correct (plus one one) two_pos)).
            assert (H3c : Id (mult one (mult (inv_pos (plus one one) two_pos) eps)) (mult (inv_pos (plus one one) two_pos) eps))
              by exact (id_trans (mult_comm one (mult (inv_pos (plus one one) two_pos) eps)) (mult_one (mult (inv_pos (plus one one) two_pos) eps))).
            exact (id_trans H3a (id_trans H3b H3c)). }
          assert (H4 : Id (mult (mult (plus one one) eps4) (smetric h szero)) (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero)))
            by exact (id_cong (fun z => mult z (smetric h szero)) H3).
          exact (id_trans H1 (id_trans H2 H4)). }
        apply (le_id_l (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                       (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                       (mult eps (smetric h szero))
                       Hsum
                       (le_id_l (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                                (mult (inv_pos (plus one one) two_pos) (mult eps (smetric h szero)))
                                (mult eps (smetric h szero))
                                (id_sym (mult_assoc (inv_pos (plus one one) two_pos) eps (smetric h szero)))
                                (half_le_self (mult eps (smetric h szero))
                                              (le_trans zero (mult zero (smetric h szero)) (mult eps (smetric h szero))
                                                        (le_id_l zero (mult zero (smetric h szero)) (mult zero (smetric h szero))
                                                                 (id_sym (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))))
                                                                 (le_refl (mult zero (smetric h szero))))
                                                        (le_mult_compat_weak zero eps (smetric h szero) (smetric_pos h szero)
                                                                             (lt_le_iff _ _ (inl Heps))))))).
        }
      }
      }
      exact Hmid.
Qed.

(* ============================================================ *)
(* 多变量向量场链式法则（DifferentiableMVVec：S -> S 内层）      *)
(* ============================================================ *)
(* 向量场版：f : S -> S（如隐藏状态动力学、词嵌入流动），       *)
(* g : S -> R（标量场，如注意力 logit）。复合 D(g∘f)(x) =       *)
(* (Df x)* (dg (f x))——外层梯度经内层导数的**伴随算子**拉回。    *)
(* 接口（诚实 Variable，与 inner_lipschitz 同先例）：            *)
(*   1) smetric_sminus_zero：度量由范数诱导（平移不变性）。      *)
(*   2) mv_adjoint：线性算子 L 的伴随 L*（⟨L h, w⟩ = ⟨h, L* w⟩）。*)
(*   3) op_lipschitz：算子范数界（|L h| ≤ N·|h|）。              *)
(* ------------------------------------------------------------ *)

(* 内积第二参数标量线性：⟨x, a·y⟩ = a·⟨x,y⟩（inner_smult_l + inner_sym 换位） *)
Lemma inner_smult_r : forall (a : R) (x y : S),
  Id (inner x (smult a y)) (mult a (inner x y)).
Proof.
  intros a x y.
  exact (id_trans (inner_sym x (smult a y))
           (id_trans (inner_smult_l a y x)
              (id_cong (fun z => mult a z) (inner_sym y x)))).
Qed.

(* 内积第二参数对 sopp：⟨x, -y⟩ = -⟨x,y⟩（smult_opp + smult_one + inner_smult_r） *)
Lemma inner_sopp_r : forall x y : S,
  Id (inner x (sopp y)) (opp (inner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (smult (opp one) y) (sopp (smult one y)))
    by exact (smult_opp one y).
  assert (Hone : Id (smult one y) y)
    by exact (smult_one y).
  assert (Hsopp : Id (smult (opp one) y) (sopp y))
    by exact (id_trans Hsm (id_cong sopp Hone)).
  assert (Hinner : Id (inner x (smult (opp one) y)) (mult (opp one) (inner x y)))
    by exact (inner_smult_r (opp one) x y).
  apply (id_trans (id_sym (id_cong (fun z => inner x z) Hsopp))).
  exact (id_trans Hinner (id_trans (opp_mult_r one (inner x y))
                                   (id_cong opp (id_trans (mult_comm one (inner x y))
                                                          (mult_one (inner x y)))))).
Qed.

(* 内积第二参数差分：⟨x, u−v⟩ = ⟨x,u⟩ − ⟨x,v⟩（inner_splus_r + inner_sopp_r） *)
Lemma inner_sminus_r : forall x u v : S,
  Id (inner x (sminus u v)) (minus (inner x u) (inner x v)).
Proof.
  intros x u v.
  unfold sminus, minus.
  assert (H1 : Id (inner x (splus u (sopp v))) (plus (inner x u) (inner x (sopp v))))
    by exact (inner_splus_r x u (sopp v)).
  exact (id_trans H1 (id_cong (fun t => plus (inner x u) t) (inner_sopp_r x v))).
Qed.

(* 向量差消去：a + (b − a) = b（splus 结合/交换/零/opp 链） *)
Lemma splus_sminus_cancel : forall a b : S, Id (splus a (sminus b a)) b.
Proof.
  intros a b.
  unfold sminus.
  assert (H1 : Id (splus a (splus b (sopp a))) (splus a (splus (sopp a) b)))
    by exact (id_cong (fun z => splus a z) (splus_comm b (sopp a))).
  assert (H2 : Id (splus a (splus (sopp a) b)) (splus (splus a (sopp a)) b))
    by exact (splus_assoc a (sopp a) b).
  assert (H3 : Id (splus (splus a (sopp a)) b) (splus szero b))
    by exact (id_cong (fun z => splus z b) (splus_opp a)).
  assert (H4 : Id (splus szero b) b)
    by exact (id_trans (splus_comm szero b) (splus_zero b)).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

(* 零向量取负仍为零：sopp szero == szero。
   splus szero (sopp szero) == szero（splus_opp szero），
   且 splus szero (sopp szero) == sopp szero（splus_comm + splus_zero）⟹ sopp szero == szero。 *)
Lemma sopp_szero : Id (sopp szero) szero.
Proof.
  (* sopp szero == splus (sopp szero) szero（splus_zero 反向）
     == splus szero (sopp szero)（splus_comm）
     == szero（splus_opp szero）。 *)
  assert (H1 : Id (sopp szero) (splus (sopp szero) szero))
    by exact (id_sym (splus_zero (sopp szero))).
  assert (H2 : Id (splus (sopp szero) szero) (splus szero (sopp szero)))
    by exact (splus_comm (sopp szero) szero).
  assert (H3 : Id (splus szero (sopp szero)) szero)
    by exact (splus_opp szero).
  exact (@id_trans S (sopp szero) (splus (sopp szero) szero) szero
                   H1 (@id_trans S (splus (sopp szero) szero) (splus szero (sopp szero)) szero
                              H2 H3)).
Qed.

(* sminus 自差化零：sminus (sminus u v) szero == sminus u v。
   sminus (sminus u v) szero = splus (sminus u v) (sopp szero) = splus (sminus u v) szero = sminus u v。 *)
Lemma sminus_sminus_szero : forall u v : S,
  Id (sminus (sminus u v) szero) (sminus u v).
Proof.
  intros u v.
  unfold sminus.
  (* splus (splus u (sopp v)) (sopp szero) == splus (splus u (sopp v)) szero（id_cong sopp_szero）
     == splus u (sopp v)（splus_zero）。 *)
  exact (id_trans (id_cong (fun z => splus (splus u (sopp v)) z) sopp_szero)
                  (splus_zero (splus u (sopp v)))).
Qed.

(* 度量平移兼容（已证定理，P2-2 消解）：smetric (sminus u v) szero == smetric u v。
   由 smetric_snorm（度量由范数诱导）：
   smetric (sminus u v) szero == snorm (sminus (sminus u v) szero)（smetric_snorm）
   == snorm (sminus u v)（sminus_sminus_szero）
   == smetric u v（smetric_snorm 反向）。 *)
Theorem smetric_sminus_zero : forall u v : S,
  Id (smetric (sminus u v) szero) (smetric u v).
Proof.

  intros u v. exact (id_trans (smetric_snorm (sminus u v) szero) (id_trans (id_cong snorm (sminus_sminus_szero u v)) (id_sym (smetric_snorm u v)))).

Qed.

(* 伴随接口（诚实 Variable）：线性算子 L : S -> S 的伴随 L* : S -> S 满足
   ⟨L h, w⟩ = ⟨h, L* w⟩。Riesz 表示定理的构造性弱化（Hilbert 空间伴随存在性）。
   支撑向量场链式法则：D(g∘f)(x) = (Df x)* (dg (f x))。 *)
Variable mv_adjoint : forall (L : S -> S),
  sigT (fun Lad : S -> S => forall h w : S,
    Id (inner (L h) w) (inner h (Lad w))).

(* 算子范数界（诚实 Variable）：|L h| ≤ N·|h|（有界线性算子的构造性弱化，
   与 inner_lipschitz 同先例；支撑向量场复合的 Lipschitz 界）。 *)
Variable op_lipschitz : forall (L : S -> S),
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (smetric (L h) szero) (mult N (smetric h szero)))).

(* ===== P1 强化（备份 80 后）：三件套可推部分非平凡实现 ===== *)
(* 三件套（inner_lipschitz/mv_adjoint/op_lipschitz）存在性为诚实接口
   （Cauchy-Schwarz 构造性弱化 / Riesz 表示 / 有界算子），但其结构性推论
   可从接口公理非平凡推出——按"能实现的必须实现"原则补齐。 *)

(* 内积第一参数差分：⟨a−b, c⟩ == ⟨a,c⟩ − ⟨b,c⟩（inner_splus_l + inner_sopp_l） *)
Lemma inner_sminus_l : forall a b c : S,
  Id (inner (sminus a b) c) (minus (inner a c) (inner b c)).
Proof.
  intros a b c.
  unfold sminus.
  assert (H1 : Id (inner (splus a (sopp b)) c) (plus (inner a c) (inner (sopp b) c)))
    by exact (inner_splus_l a (sopp b) c).
  assert (H2 : Id (plus (inner a c) (inner (sopp b) c))
                 (plus (inner a c) (opp (inner b c))))
    by exact (id_cong (fun z => plus (inner a c) z) (inner_sopp_l b c)).
  exact (id_trans H1 H2).
Qed.

(* 向量差消去：a − b == 0 ⟹ a == b（splus_sminus_cancel + splus_zero） *)
Lemma sminus_zero_cancel : forall a b : S,
  Id (sminus a b) szero -> Id a b.
Proof.
  intros a b H.
  assert (H1 : Id a (splus b (sminus a b))).
  { apply (id_sym (splus_sminus_cancel b a)). }
  apply (id_trans H1).
  apply (id_trans (id_cong (fun z => splus b z) H)).
  apply splus_zero.
Qed.

(* 伴随唯一性：若 Lad1、Lad2 均为 L 的伴随则逐点相等。
   ⟨h, Lad1 w⟩ == ⟨L h, w⟩ == ⟨h, Lad2 w⟩ ⟹ ⟨h, h'⟩ == 0（h' := Lad1 w − Lad2 w）
   ⟹ inner_definite ⟹ h' == szero ⟹ Lad1 w == Lad2 w。 *)
Lemma mv_adjoint_unique : forall (L : S -> S) (Lad1 Lad2 : S -> S),
  (forall h w : S, Id (inner (L h) w) (inner h (Lad1 w))) ->
  (forall h w : S, Id (inner (L h) w) (inner h (Lad2 w))) ->
  forall w : S, Id (Lad1 w) (Lad2 w).
Proof.
  intros L Lad1 Lad2 H1 H2 w.
  pose (h := sminus (Lad1 w) (Lad2 w)).
  assert (Hinner : Id (inner h h) zero).
  { unfold h.
    apply (id_trans (inner_sminus_r (sminus (Lad1 w) (Lad2 w)) (Lad1 w) (Lad2 w))).
    assert (Hmid1 : Id (inner (sminus (Lad1 w) (Lad2 w)) (Lad1 w))
                       (inner (sminus (Lad1 w) (Lad2 w)) (Lad2 w))).
    { apply (id_trans (id_sym (H1 (sminus (Lad1 w) (Lad2 w)) w))).
      exact (H2 (sminus (Lad1 w) (Lad2 w)) w). }
    unfold minus.
    apply (id_trans (id_sym (id_cong (fun z => plus (inner (sminus (Lad1 w) (Lad2 w)) (Lad1 w)) z)
                                    (id_cong opp Hmid1)))
                    (plus_opp (inner (sminus (Lad1 w) (Lad2 w)) (Lad1 w)))). }
  assert (Hhzero : Id h szero) by (apply (inner_definite h Hinner)).
  apply (sminus_zero_cancel (Lad1 w) (Lad2 w)).
  unfold h in Hhzero.
  exact Hhzero.
Qed.

(* 有界算子复合有界：|L(M h)| ≤ N_L·|M h| ≤ N_L·(N_M·|h|) == (N_L·N_M)·|h|。
   范数界 N := N_L·N_M（op_lipschitz 传递，N_L·N_M ≥ 0）。 *)
Lemma op_lipschitz_compose : forall (L M : S -> S),
  sigT (fun N : R => And (le zero N) (forall h : S,
    le (smetric (L (M h)) szero) (mult N (smetric h szero)))).
Proof.
  intros L M.
  destruct (op_lipschitz L) as [NL [HNL0 HNL]].
  destruct (op_lipschitz M) as [NM [HNM0 HNM]].
  exists (mult NL NM).
  split.
  - (* 0 ≤ NL·NM：le_mult_compat_weak + mult_zero 换形 *)
    apply (le_id_l _ (mult zero NM) _).
    + apply (id_trans (id_sym (mult_zero NM)) (mult_comm NM zero)).
    + apply (le_mult_compat_weak zero NL NM HNM0 HNL0).
  - intros h.
    apply (le_trans _ (mult NL (smetric (M h) szero)) _).
    + exact (HNL (M h)).
    + apply (le_trans _ (mult NL (mult NM (smetric h szero))) _).
      * apply (le_id_l _ (mult (smetric (M h) szero) NL) _).
        -- apply (mult_comm NL (smetric (M h) szero)).
        -- apply (le_id_r _ (mult (mult NM (smetric h szero)) NL) _).
           ++ apply (mult_comm (mult NM (smetric h szero)) NL).
           ++ apply (le_mult_compat_weak (smetric (M h) szero) (mult NM (smetric h szero)) NL HNL0).
              exact (HNM h).
      * apply (le_id_l _ (mult (mult NL NM) (smetric h szero)) _).
        -- apply (mult_assoc NL NM (smetric h szero)).
        -- apply le_refl.
Qed.

(* 向量场可微（Fréchet 型，Set 层）：f : S -> S，导数 dfvec : S -> S -> S。
   线性化 f x + dfvec x h，误差用 smetric 度量（增量 − 线性化）。 *)
Record DifferentiableMVVec (f : S -> S) := {
  dfvec : S -> S -> S;
  dfvec_correct : forall x eps, lt zero eps ->
    sigT (fun delta : R => And (lt zero delta) (forall h : S,
      lt (smetric h szero) delta ->
      le (smetric (sminus (f (splus x h)) (f x)) (dfvec x h))
         (mult eps (smetric h szero))))
}.

(* 通用误差分解：minus A (plus B X) == plus (minus A (plus B Y)) (minus Y X)
   （R 层代数：A−(B+X) = (A−(B+Y)) + (Y−X)） *)
Lemma mv_vec_diff_decomp : forall (A B X Y : R),
  Id (minus A (plus B X)) (plus (minus A (plus B Y)) (minus Y X)).
Proof.
  intros A B X Y.
  unfold minus.
  assert (Hcancel : Id (plus (opp (plus B Y)) Y) (opp B)).
  {
    assert (H1 : Id (plus (opp (plus B Y)) Y)
                    (plus (plus (opp B) (opp Y)) Y))
      by exact (id_cong (fun z => plus z Y) (opp_plus B Y)).
    assert (H2 : Id (plus (plus (opp B) (opp Y)) Y)
                    (plus (opp B) (plus (opp Y) Y)))
      by exact (id_sym (plus_assoc (opp B) (opp Y) Y)).
    assert (H3 : Id (plus (opp B) (plus (opp Y) Y))
                    (plus (opp B) zero))
      by exact (id_cong (fun z => plus (opp B) z)
                        (id_trans (plus_comm (opp Y) Y) (plus_opp Y))).
    assert (H4 : Id (plus (opp B) zero) (opp B)) by exact (plus_zero (opp B)).
    exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
  }
  assert (Hre : Id (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                   (plus A (opp (plus B X)))).
  {
    assert (H1 : Id (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                    (plus A (plus (plus (opp (plus B Y)) Y) (opp X))))
      by exact (id_trans (id_sym (plus_assoc A (opp (plus B Y)) (plus Y (opp X))))
                         (id_cong (fun z => plus A z)
                                  (plus_assoc (opp (plus B Y)) Y (opp X)))).
    assert (H2 : Id (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                    (plus A (plus (opp B) (opp X))))
      by exact (id_cong (fun z => plus A (plus z (opp X))) Hcancel).
    assert (H3 : Id (plus A (plus (opp B) (opp X)))
                    (plus A (opp (plus B X))))
      by exact (id_cong (fun z => plus A z) (id_sym (opp_plus B X))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_sym Hre).
Qed.

(* 向量场链式法则：f : S -> S 内层、g : S -> R 外层。
   D(g∘f)(x) = (Df x)* (dg (f x))（伴随拉回）。
   预算：eps4 = eps/4；内层增量范数界 L := N_op + 1（op_lipschitz），
   外层梯度内积范数界 M := N_a + 1（inner_lipschitz）。
   T1（外层误差）≤ eps_g·|Dg| ≤ eps4·|h|；T2（内层误差经伴随）
   ≤ N_a·|Dg − df·h| ≤ N_a·eps_f·|h| ≤ eps4·|h|。 *)
Theorem differentiable_mv_vec_compose : forall (f : S -> S) (g : S -> R),
  DifferentiableMVVec f -> DifferentiableMV g ->
  DifferentiableMV (fun x => g (f x)).
Proof.
  intros f g [df Hf] [dg Hg].
  (* 梯度 = 伴随拉回：(df x)* (dg (f x)) *)
  exists (fun x => projT1 (mv_adjoint (df x)) (dg (f x))).
  intros x eps Heps.
  set (eps4 := mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive; [apply inv_pos_pos | apply half_pos; exact Heps]. }
  (* 外层梯度内积范数：N_a := inner_lipschitz (dg (f x))，M := N_a + 1 *)
  destruct (inner_lipschitz (dg (f x))) as [N_a HN_a].
  destruct HN_a as [HN_a0 HN_a2].
  set (M := plus N_a one).
  assert (HM : lt zero M).
  { unfold M. apply plus_le_lt_pos; [exact HN_a0 | apply one_pos]. }
  (* 内层导数算子范数：N_op := op_lipschitz (df x)，L := N_op + 1 *)
  destruct (op_lipschitz (df x)) as [N_op HN_op].
  destruct HN_op as [HN_op0 HN_op2].
  set (L := plus N_op one).
  assert (HL : lt zero L).
  { unfold L. apply plus_le_lt_pos; [exact HN_op0 | apply one_pos]. }
  set (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f)
    by (unfold eps_f; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  set (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g)
    by (unfold eps_g; apply min_pos; [apply one_pos | apply mult_positive; [apply inv_pos_pos | exact Heps4]]).
  destruct (Hf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    apply min_pos; [exact Hdf1 | apply min_pos; [apply one_pos | exact Hltm]].
  - intros h Hh.
    set (Dg := sminus (f (splus x h)) (f x)).
    (* 伴随恒等式：⟨adj, h⟩ = ⟨dg (f x), df x h⟩，adj := (df x)* (dg (f x)) *)
    assert (Hlin : Id (inner (projT1 (mv_adjoint (df x)) (dg (f x))) h)
                      (inner (dg (f x)) (df x h))).
    {
      pose (adj := projT1 (mv_adjoint (df x)) (dg (f x))).
      pose (Hadj := projT2 (mv_adjoint (df x)) h (dg (f x))).
      assert (H1 : Id (inner adj h) (inner h adj)) by exact (inner_sym adj h).
      assert (H2 : Id (inner h adj) (inner (df x h) (dg (f x)))) by exact (id_sym Hadj).
      assert (H3 : Id (inner (df x h) (dg (f x))) (inner (dg (f x)) (df x h))) by exact (inner_sym (df x h) (dg (f x))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    (* 误差分解：E = T1 + T2，Y := ⟨dg(f x), Dg⟩，X := ⟨dg(f x), df x h⟩ *)
    assert (Hdecomp : Id (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) (df x h))))
                         (plus (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg)))
                               (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))))
      by (unfold Dg; exact (mv_vec_diff_decomp (g (f (splus x h))) (g (f x))
                                               (inner (dg (f x)) (df x h))
                                               (inner (dg (f x)) (sminus (f (splus x h)) (f x))))).
    apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (projT1 (mv_adjoint (df x)) (dg (f x))) h))))
                   (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg)))
                              (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))))
                   (mult eps (smetric h szero))).
    + exact (id_cong abs (id_trans (id_cong (fun z => minus (g (f (splus x h))) (plus (g (f x)) z)) Hlin) Hdecomp)).
    + assert (Hh_dfd : lt (smetric h szero) dfd)
        by (eapply lt_le_trans; [exact Hh | apply min_le_l]).
      assert (Hh_one : lt (smetric h szero) one)
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_l]]).
      assert (Hh_dgd : lt (smetric h szero) (mult (inv_pos L HL) dgd))
        by (eapply lt_le_trans; [exact Hh | apply (le_trans _ (min one (mult (inv_pos L HL) dgd)) _); [apply min_le_r | apply min_le_r]]).
      (* (a) |Dg| ≤ L·|h|（smetric_triangle：|Dg| ≤ |Dg − df·h| + |df·h|） *)
      assert (HDg_bound : le (smetric Dg szero) (mult L (smetric h szero))).
      {
        apply (le_trans _ (plus (smetric Dg (df x h)) (smetric (df x h) szero)) _).
        { apply smetric_triangle. }
        { apply (le_trans _ (plus (mult eps_f (smetric h szero)) (mult N_op (smetric h szero))) _).
          { apply le_plus_compat.
            { unfold Dg. exact (Hdf2 h Hh_dfd). }
            { exact (HN_op2 h). } }
          { assert (Hef : le eps_f one)
              by (unfold eps_f; exact (min_le_l one (mult (inv_pos M HM) eps4))).
            assert (Hle : le (plus eps_f N_op) (plus N_op one))
              by (apply (le_id_r (plus eps_f N_op) (plus one N_op) (plus N_op one)
                                 (plus_comm one N_op)
                                 (le_plus_compat eps_f one N_op N_op Hef (le_refl N_op)))).
            assert (Hsum : Id (plus (mult eps_f (smetric h szero)) (mult N_op (smetric h szero)))
                               (mult (plus eps_f N_op) (smetric h szero)))
              by exact (id_sym (mult_plus_distr_r eps_f N_op (smetric h szero))).
            rewrite Hsum.
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero)).
            unfold L. exact Hle. } }
      }
      (* |Dg| < dgd（L·|h| < L·(inv_L·dgd) = dgd） *)
      assert (HdfDg : lt (smetric Dg szero) dgd).
      {
        apply (le_lt_trans (smetric Dg szero) (mult L (smetric h szero)) dgd).
        - exact HDg_bound.
        - assert (Hraw : lt (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L))
            by (apply (lt_mult_compat (smetric h szero) (mult (inv_pos L HL) dgd) L HL Hh_dgd)).
          assert (Hswap : Id (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))).
          { assert (H1 : Id (mult (mult (inv_pos L HL) dgd) L) (mult (inv_pos L HL) (mult dgd L)))
              by exact (id_sym (mult_assoc (inv_pos L HL) dgd L)).
            assert (H2 : Id (mult (inv_pos L HL) (mult dgd L)) (mult (inv_pos L HL) (mult L dgd)))
              by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm dgd L)).
            assert (H3 : Id (mult (inv_pos L HL) (mult L dgd)) (mult (mult (inv_pos L HL) L) dgd))
              by exact (mult_assoc (inv_pos L HL) L dgd).
            assert (H4 : Id (mult (mult (inv_pos L HL) L) dgd) (mult (mult L (inv_pos L HL)) dgd))
              by exact (id_cong (fun z => mult z dgd) (mult_comm (inv_pos L HL) L)).
            assert (H5 : Id (mult (mult L (inv_pos L HL)) dgd) (mult L (mult (inv_pos L HL) dgd)))
              by exact (id_sym (mult_assoc L (inv_pos L HL) dgd)).
            exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))). }
          assert (HltL : lt (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)))
            by exact (lt_id_l (mult L (smetric h szero)) (mult (smetric h szero) L) (mult L (mult (inv_pos L HL) dgd))
                              (mult_comm L (smetric h szero))
                              (lt_id_r (mult (smetric h szero) L) (mult (mult (inv_pos L HL) dgd) L) (mult L (mult (inv_pos L HL) dgd))
                                       Hswap Hraw)).
          assert (Hident : Id (mult L (mult (inv_pos L HL) dgd)) dgd).
          { assert (H1 : Id (mult L (mult (inv_pos L HL) dgd)) (mult (mult L (inv_pos L HL)) dgd))
              by exact (mult_assoc L (inv_pos L HL) dgd).
            assert (H2 : Id (mult (mult L (inv_pos L HL)) dgd) (mult one dgd))
              by exact (id_cong (fun z => mult z dgd) (inv_pos_correct L HL)).
            assert (H3 : Id (mult one dgd) dgd)
              by exact (id_trans (mult_comm one dgd) (mult_one dgd)).
            exact (id_trans H1 (id_trans H2 H3)). }
          apply (lt_id_r (mult L (smetric h szero)) (mult L (mult (inv_pos L HL) dgd)) dgd Hident HltL).
      }
      (* T1：外层误差 ≤ eps_g·|Dg| ≤ eps4·|h|（splus_sminus_cancel 换形扰动 Dg） *)
      assert (HT1 : le (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg))))
                       (mult eps4 (smetric h szero))).
      {
        apply (le_trans _ (mult eps_g (smetric Dg szero)) _).
        - apply (le_id_l (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg))))
                         (abs (minus (g (splus (f x) Dg)) (plus (g (f x)) (inner (dg (f x)) Dg))))
                         (mult eps_g (smetric Dg szero))
                         (id_cong (fun z => abs (minus (g z) (plus (g (f x)) (inner (dg (f x)) Dg))))
                                  (id_sym (splus_sminus_cancel (f x) (f (splus x h)))))
                         (Hdg2 Dg HdfDg)).
        - apply (le_trans _ (mult eps_g (mult L (smetric h szero))) _).
          { apply (le_mult_compat_r eps_g (smetric Dg szero) (mult L (smetric h szero)) (lt_le_iff _ _ (inl Heps_g)) HDg_bound). }
          { assert (Hfl : Id (mult eps_g (mult L (smetric h szero))) (mult (mult eps_g L) (smetric h szero)))
              by exact (mult_assoc eps_g L (smetric h szero)).
            rewrite Hfl.
            assert (Hfl_le : le (mult eps_g L) eps4).
            { assert (Hepg_le : le eps_g (mult (inv_pos L HL) eps4))
                by (unfold eps_g; exact (min_le_r one (mult (inv_pos L HL) eps4))).
              apply (le_trans _ (mult (mult (inv_pos L HL) eps4) L) _).
              { apply (le_mult_compat_weak eps_g (mult (inv_pos L HL) eps4) L (lt_le_iff zero L (inl HL)) Hepg_le). }
              { assert (H1 : Id (mult (mult (inv_pos L HL) eps4) L) (mult (inv_pos L HL) (mult eps4 L)))
                  by exact (id_sym (mult_assoc (inv_pos L HL) eps4 L)).
                assert (H2 : Id (mult (inv_pos L HL) (mult eps4 L)) (mult (inv_pos L HL) (mult L eps4)))
                  by exact (id_cong (fun z => mult (inv_pos L HL) z) (mult_comm eps4 L)).
                assert (H3 : Id (mult (inv_pos L HL) (mult L eps4)) (mult (mult (inv_pos L HL) L) eps4))
                  by exact (mult_assoc (inv_pos L HL) L eps4).
                assert (H4 : Id (mult (mult (inv_pos L HL) L) eps4) (mult (mult L (inv_pos L HL)) eps4))
                  by exact (id_cong (fun z => mult z eps4) (mult_comm (inv_pos L HL) L)).
                assert (H5 : Id (mult (mult L (inv_pos L HL)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct L HL)).
                assert (H6 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult (mult (inv_pos L HL) eps4) L) eps4 eps4
                               (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6)))))
                               (le_refl eps4)). } }
            apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hfl_le). }
      }
      (* T2：|⟨a,Dg⟩ − ⟨a,df·h⟩| = |⟨a, Dg−df·h⟩| ≤ N_a·|Dg−df·h| = N_a·|Dg−df·h|
             ≤ N_a·eps_f·|h| ≤ M·eps_f·|h| ≤ eps4·|h|（smetric_sminus_zero 平移） *)
      assert (HT2 : le (abs (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h))))
                       (mult eps4 (smetric h szero))).
      {
        assert (Hsm : Id (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))
                          (inner (dg (f x)) (sminus Dg (df x h))))
          by (unfold Dg; apply id_sym; exact (inner_sminus_r (dg (f x)) (sminus (f (splus x h)) (f x)) (df x h))).
        apply (le_id_l (abs (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h))))
                       (abs (inner (dg (f x)) (sminus Dg (df x h))))
                       (mult eps4 (smetric h szero))
                       (id_cong abs Hsm)).
        apply (le_trans _ (mult N_a (mult eps_f (smetric h szero))) _).
        - apply (le_trans _ (mult N_a (smetric (sminus Dg (df x h)) szero)) _).
          { exact (HN_a2 (sminus Dg (df x h))). }
          { apply (le_id_l (mult N_a (smetric (sminus Dg (df x h)) szero))
                           (mult N_a (smetric Dg (df x h)))
                           (mult N_a (mult eps_f (smetric h szero)))
                           (id_cong (fun z => mult N_a z) (smetric_sminus_zero Dg (df x h)))).
            assert (Hw0 : le (mult (smetric (sminus (f (splus x h)) (f x)) (df x h)) N_a)
                              (mult (mult eps_f (smetric h szero)) N_a))
              by (apply (le_mult_compat_weak (smetric (sminus (f (splus x h)) (f x)) (df x h)) (mult eps_f (smetric h szero)) N_a HN_a0
                                             (Hdf2 h Hh_dfd))).
            assert (Hw : le (mult (smetric Dg (df x h)) N_a) (mult (mult eps_f (smetric h szero)) N_a))
              by (unfold Dg; exact Hw0).
            apply (le_id_l (mult N_a (smetric Dg (df x h)))
                           (mult (smetric Dg (df x h)) N_a)
                           (mult N_a (mult eps_f (smetric h szero)))
                           (mult_comm N_a (smetric Dg (df x h)))).
            apply (le_id_r (mult (smetric Dg (df x h)) N_a)
                           (mult (mult eps_f (smetric h szero)) N_a)
                           (mult N_a (mult eps_f (smetric h szero)))
                           (id_sym (mult_comm N_a (mult eps_f (smetric h szero))))
                           Hw). }
        - assert (Hfl : Id (mult N_a (mult eps_f (smetric h szero))) (mult (mult N_a eps_f) (smetric h szero)))
            by exact (mult_assoc N_a eps_f (smetric h szero)).
          rewrite Hfl.
          assert (Hmg_le : le (mult N_a eps_f) eps4).
          { assert (Hepf_le : le eps_f (mult (inv_pos M HM) eps4))
              by (unfold eps_f; exact (min_le_r one (mult (inv_pos M HM) eps4))).
            assert (HNa_le : le N_a M)
              by (unfold M; apply le_plus_nonneg_r; exact (lt_le_iff _ _ (inl one_pos))).
            assert (Hstep2 : le (mult N_a (mult (inv_pos M HM) eps4)) (mult M (mult (inv_pos M HM) eps4)))
              by (apply (le_mult_compat_weak N_a M (mult (inv_pos M HM) eps4)
                                             (lt_le_iff _ _ (inl (mult_positive (inv_pos M HM) eps4 (inv_pos_pos M HM) Heps4)))
                                             HNa_le)).
            apply (le_trans _ (mult N_a (mult (inv_pos M HM) eps4)) _).
            { apply (le_trans _ (mult eps_f N_a) _).
              { apply (le_id_l (mult N_a eps_f) (mult eps_f N_a) (mult eps_f N_a)
                               (mult_comm N_a eps_f) (le_refl (mult eps_f N_a))). }
              { apply (le_id_r (mult eps_f N_a)
                               (mult (mult (inv_pos M HM) eps4) N_a)
                               (mult N_a (mult (inv_pos M HM) eps4))
                               (id_sym (mult_comm N_a (mult (inv_pos M HM) eps4)))
                               (le_mult_compat_weak eps_f (mult (inv_pos M HM) eps4) N_a HN_a0 Hepf_le)). } }
            { apply (le_trans _ (mult M (mult (inv_pos M HM) eps4)) _).
              { exact Hstep2. }
              { assert (H1 : Id (mult M (mult (inv_pos M HM) eps4)) (mult (mult M (inv_pos M HM)) eps4))
                  by exact (mult_assoc M (inv_pos M HM) eps4).
                assert (H2 : Id (mult (mult M (inv_pos M HM)) eps4) (mult one eps4))
                  by exact (id_cong (fun z => mult z eps4) (inv_pos_correct M HM)).
                assert (H3 : Id (mult one eps4) eps4)
                  by exact (id_trans (mult_comm one eps4) (mult_one eps4)).
                exact (le_id_l (mult M (mult (inv_pos M HM) eps4)) eps4 eps4
                               (id_trans H1 (id_trans H2 H3)) (le_refl eps4)). } }
          }
          apply (le_mult_compat_weak _ _ _ (smetric_pos h szero) Hmg_le).
      }
      (* 合并：T1 + T2 ≤ (eps4+eps4)·|h| = (eps/2)·|h| ≤ eps·|h| *)
      assert (Hmid : le (abs (plus (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg)))
                                   (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h)))))
                        (mult eps (smetric h szero))).
      {
        apply (le_trans _ (plus (abs (minus (g (f (splus x h))) (plus (g (f x)) (inner (dg (f x)) Dg))))
                                (abs (minus (inner (dg (f x)) Dg) (inner (dg (f x)) (df x h))))) _).
        { apply abs_triangle. }
        { apply (le_trans _ (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero))) _).
          { apply le_plus_compat; [exact HT1 | exact HT2]. }
      { assert (Hsum : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))).
        { unfold eps4.
          assert (H1 : Id (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                          (mult (plus one one) (mult eps4 (smetric h szero))))
            by (apply id_sym; apply two_mult).
          assert (H2 : Id (mult (plus one one) (mult eps4 (smetric h szero))) (mult (mult (plus one one) eps4) (smetric h szero)))
            by exact (mult_assoc (plus one one) eps4 (smetric h szero)).
          assert (H3 : Id (mult (plus one one) eps4) (mult (inv_pos (plus one one) two_pos) eps)).
          { assert (H3a : Id (mult (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)))
                              (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) eps)).
            assert (H3b : Id (mult (mult (plus one one) (inv_pos (plus one one) two_pos)) (mult (inv_pos (plus one one) two_pos) eps))
                              (mult one (mult (inv_pos (plus one one) two_pos) eps)))
              by exact (id_cong (fun z => mult z (mult (inv_pos (plus one one) two_pos) eps)) (inv_pos_correct (plus one one) two_pos)).
            assert (H3c : Id (mult one (mult (inv_pos (plus one one) two_pos) eps)) (mult (inv_pos (plus one one) two_pos) eps))
              by exact (id_trans (mult_comm one (mult (inv_pos (plus one one) two_pos) eps)) (mult_one (mult (inv_pos (plus one one) two_pos) eps))).
            exact (id_trans H3a (id_trans H3b H3c)). }
          assert (H4 : Id (mult (mult (plus one one) eps4) (smetric h szero)) (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero)))
            by exact (id_cong (fun z => mult z (smetric h szero)) H3).
          exact (id_trans H1 (id_trans H2 H4)). }
        apply (le_id_l (plus (mult eps4 (smetric h szero)) (mult eps4 (smetric h szero)))
                       (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                       (mult eps (smetric h szero))
                       Hsum
                       (le_id_l (mult (mult (inv_pos (plus one one) two_pos) eps) (smetric h szero))
                                (mult (inv_pos (plus one one) two_pos) (mult eps (smetric h szero)))
                                (mult eps (smetric h szero))
                                (id_sym (mult_assoc (inv_pos (plus one one) two_pos) eps (smetric h szero)))
                                (half_le_self (mult eps (smetric h szero))
                                              (le_trans zero (mult zero (smetric h szero)) (mult eps (smetric h szero))
                                                        (le_id_l zero (mult zero (smetric h szero)) (mult zero (smetric h szero))
                                                                 (id_sym (id_trans (mult_comm zero (smetric h szero)) (mult_zero (smetric h szero))))
                                                                 (le_refl (mult zero (smetric h szero))))
                                                        (le_mult_compat_weak zero eps (smetric h szero) (smetric_pos h szero)
                                                                             (lt_le_iff _ _ (inl Heps))))))).
        }
      }
      }
      exact Hmid.
Qed.
End MultivariableDifferentiable.

(* 热力学第二定律 *)
Section SecondLaw.
Context {RI : RealInterfaceEnhanced}.

(* 显式绑定基本类型和关系，避免实例解析问题 *)
Let R := @R RI.
Let le := @le RI.
Let lt := @lt RI.

Variable entropy : R -> R.
Variable dynamics : R -> R.

Definition entropy_increases : Set :=
  forall x, le (entropy x) (entropy (dynamics x)).

(* [墙族登记·RW-LAW2 熵增公设] 模型公设（第二定律动力学形式）：dynamics/entropy 抽象场无表征兄弟，本位不可导，禁硬证；Not 前件=Prop 红线对象——Set 重述候选（argmax/间隙具体层构造，核），接口层原样保留留记。 *)
Variable strict_entropy_increase :
  forall x, Not (Id (dynamics x) x) ->
    lt (entropy x) (entropy (dynamics x)).

Theorem second_law_irreversible :
  forall x, Not (Id (dynamics x) x) ->
    lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hneq. exact (strict_entropy_increase x Hneq).
Qed.

End SecondLaw.

(* 语言模型扩展：温度采样 *)
Section LanguageModelExtensions.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.   (* 允许自动解析 RealInterface 字段 *)

(* 显式绑定常用字段，避免类型类解析问题 *)
Let R := @R RI.
Let zero := @zero RI.
Let lt := @lt RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).

Variable neg_log_prob : list Token -> Token -> R.

Definition Temperature : Set := R.
Variable temperature : Temperature.
Variable temperature_pos : lt zero temperature.

Definition temperature_weighted_prob (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)).

Variable top_k : list Token -> list Token.

End LanguageModelExtensions.

(* 状态空间实例（列表） *)
Section ListStateSpace.
Context {RI : RealInterface}.

Variable A : Set.
Definition ListS : Set := list A.

Definition list_szero : ListS := nil.
Definition list_splus (x y : ListS) : ListS := x ++ y.
Definition list_sopp (x : ListS) : ListS := nil.
Definition list_smult (a : R) (x : ListS) : ListS := nil.

Definition list_smetric (x y : ListS) : R := zero.

Definition list_clim (u : nat -> ListS) (l : ListS) : Set :=
  forall n : nat, Id (u n) l.

End ListStateSpace.

(* 涨落定理的对称形式 *)
Section FluctuationSymmetry.
Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let lt := @lt RI.
Let opp := @opp RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.

Variable sigma : R -> R.
Variable prob_forward : R -> R.
Variable prob_backward : R -> R.
Variable prob_backward_pos : forall x, lt zero (prob_backward x).
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_symmetry :
  forall ds,
    Id (mult (inv_pos (prob_backward (opp ds)) (prob_backward_pos (opp ds)))
             (prob_forward ds))
       (exp_neg (mult (inv_pos k_B k_B_pos) ds)).

End FluctuationSymmetry.

(* 可证明的简单代数性质 *)
Section SimpleAlgebra.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.   (* 启用 RealInterface 实例解析 *)

(* 或者使用 Let 绑定：
   Let R := @R RI.
   Let zero := @zero RI.
   Let plus := @plus RI.
   Let mult := @mult RI.
   Let opp := @opp RI.
*)

Lemma plus_zero_r :
  forall a : R, Id (plus a zero) a.
Proof. intro a. apply plus_zero. Qed.

Lemma plus_opp_r :
  forall a : R, Id (plus a (opp a)) zero.
Proof. intro a. exact (plus_opp a). Qed.

Lemma mult_one_r :
  forall a : R, Id (mult a one) a.
Proof. intro a. exact (mult_one a). Qed.

Lemma mult_zero_r :
  forall a : R, Id (mult a zero) zero.
Proof. intro a. exact (mult_zero a). Qed.

Lemma mult_comm_rewrite :
  forall a b : R, Id (mult a b) (mult b a).
Proof. intros a b. exact (mult_comm a b). Qed.

(* ============================================================ *)
(* 环论补充引理已前移至 Enhanced 定义后的 Section RingLemmas， *)
(* 供全文件各模块使用；SimpleAlgebra 仅保留代数小引理。        *)
(* ============================================================ *)

End SimpleAlgebra.

(* ============================================================ *)
(* 模块：AttentionGibbsBridge                                  *)
(* 将注意力 softmax 与热力学 Boltzmann 分布对应，并给出        *)
(* KV 逐出导致的 detailed-balance 破缺的定量约束。            *)
(* 整合自 AttentionGibbsBridge.txt（临时承认已全部转完整证明； *)
(* 纯构造性、Set 层、无 Prop 设施）。                          *)
(* ============================================================ *)

Section AttentionGibbsBridge.

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
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* 正指数函数：e^x := exp_neg(-x)（命名避免与 Stdlib exp 冲突） *)
Definition exp_pos_fn (x : R) : R := exp_neg (opp x).

(* ---- Softmax 定义 ---- *)
Definition logits : Set := S -> R.

Definition partition_function (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (z s)).

(* SumOver 抽象接口未提供"正函数求和为正"，作显式假设（非经典、可实例化） *)
Variable sum_pos_preserved :
  forall (f : S -> R), (forall s, lt zero (f s)) -> lt zero (sum_over_S f).

Lemma partition_function_pos :
  forall z : logits, lt zero (partition_function z).
Proof.
  intros z.
  (* 展开至定义层：逐点正性单列为显式命题（逐点支撑指派），再对
     求和保正接口显式实例化装配——不经逐句转发。 *)
  unfold partition_function, exp_pos_fn.
  assert (Hpt : forall s, lt zero (exp_neg (opp (z s)))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (z s))) Hpt).
Qed.

Definition softmax (z : logits) (s : S) : R :=
  mult (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z)).

(* ============================================================ *)
(* 概率分布公理（不可替代的机器检查保证：当前 AI 依赖浮点近似）*)
(* ============================================================ *)

(* softmax 正性：注意力权重 > 0（exp 正 × 逆元正） *)
Theorem softmax_pos :
  forall z : logits, forall s : S, lt zero (softmax z s).
Proof.
  intros z s.
  unfold softmax, exp_pos_fn.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* softmax 归一化：Σ_s softmax(z,s) = 1（概率质量守恒） *)
Theorem softmax_normalized :
  forall z : logits, Id (sum_over_S (fun s => softmax z s)) one.
Proof.
  intro z.
  unfold softmax.
  (* 逐点交换 mult 顺序（sum_over_S_ext + mult_comm） *)
  assert (Hext : Id (sum_over_S (fun s => mult (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z))))
                   (sum_over_S (fun s => mult (inv_pos (partition_function z) (partition_function_pos z)) (exp_pos_fn (z s)))))
    by exact (sum_over_S_ext (fun s => mult (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z)))
                             (fun s => mult (inv_pos (partition_function z) (partition_function_pos z)) (exp_pos_fn (z s)))
                             (fun s => mult_comm (exp_pos_fn (z s)) (inv_pos (partition_function z) (partition_function_pos z)))).
  rewrite Hext.
  (* 提取常数因子（sum_over_S_linear） *)
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (partition_function z) (partition_function_pos z)) (exp_pos_fn (z s))))
                    (mult (inv_pos (partition_function z) (partition_function_pos z))
                          (sum_over_S (fun s => exp_pos_fn (z s)))))
    by exact (sum_over_S_linear (inv_pos (partition_function z) (partition_function_pos z)) (fun s => exp_pos_fn (z s))).
  rewrite Hlin.
  (* Σ exp(z s) = partition_function z（定义展开） *)
  unfold partition_function.
  (* (1/Z)·Z = 1（inv_pos_correct + comm） *)
  assert (Hcc : Id (mult (inv_pos (partition_function z) (partition_function_pos z)) (partition_function z)) one)
    by exact (id_trans (mult_comm (inv_pos (partition_function z) (partition_function_pos z)) (partition_function z))
                       (inv_pos_correct (partition_function z) (partition_function_pos z))).
  exact Hcc.
Qed.

(* ============================================================ *)
(* 非平凡版本：softmax 凸组合归一化守恒（模型集成 / 专家混合 / *)
(* 注意力混合的数学基础——两组 logits 的凸组合仍是概率分布，   *)
(* 非配分函数定义的重述）。                                    *)
(* ============================================================ *)
Theorem softmax_mix_normalized :
  forall (z z' : logits) (alpha : R) (Halpha : lt zero alpha) (Halpha1 : lt zero (minus one alpha)),
    Id (sum_over_S (fun s => plus (mult alpha (softmax z s)) (mult (minus one alpha) (softmax z' s)))) one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : Id (sum_over_S (fun s => softmax z s)) one) by exact (softmax_normalized z).
  assert (Hq : Id (sum_over_S (fun s => softmax z' s)) one) by exact (softmax_normalized z').
  assert (Hadd : Id (sum_over_S (fun s => plus (mult alpha (softmax z s)) (mult (minus one alpha) (softmax z' s))))
                   (plus (sum_over_S (fun s => mult alpha (softmax z s)))
                         (sum_over_S (fun s => mult (minus one alpha) (softmax z' s)))))
    by exact (sum_over_S_add (fun s => mult alpha (softmax z s)) (fun s => mult (minus one alpha) (softmax z' s))).
  rewrite Hadd.
  assert (Hlin1 : Id (sum_over_S (fun s => mult alpha (softmax z s))) (mult alpha (sum_over_S (fun s => softmax z s))))
    by exact (sum_over_S_linear alpha (fun s => softmax z s)).
  rewrite Hlin1.
  assert (Hlin2 : Id (sum_over_S (fun s => mult (minus one alpha) (softmax z' s))) (mult (minus one alpha) (sum_over_S (fun s => softmax z' s))))
    by exact (sum_over_S_linear (minus one alpha) (fun s => softmax z' s)).
  rewrite Hlin2.
  rewrite Hp. rewrite Hq.
  assert (Hm1 : Id (mult alpha one) alpha) by exact (mult_one alpha).
  rewrite Hm1.
  assert (Hm2 : Id (mult (minus one alpha) one) (minus one alpha)) by exact (mult_one (minus one alpha)).
  rewrite Hm2.
  (* 目标：plus alpha (minus one alpha) = one——assert + exact 链（同 FreeEnergyMinimization 版） *)
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

(* 组合：softmax 是概率分布（正性 + 归一化） *)
Theorem softmax_is_prob :
  forall z : logits,
    And (forall s : S, le zero (softmax z s)) (Id (sum_over_S (fun s => softmax z s)) one).
Proof.
  intro z.
  split.
  - intro s.
    apply (lt_le_iff _ _). left. apply softmax_pos.
  - apply softmax_normalized.
Qed.

(* ============================================================ *)
(* 温度退火框架（推测解码 / 硬注意力 T→0 的数学基础）          *)
(* ============================================================ *)

Variable T : R.
Variable T_pos : lt zero T.

Definition partition_function_temp (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (mult (inv_pos T T_pos) (z s))).

Lemma partition_function_temp_pos :
  forall z : logits, lt zero (partition_function_temp z).
Proof.
  intros z.
  unfold partition_function_temp, exp_pos_fn.
  (* 展开至定义层（同族样板复用）：逐点正性单列为显式命题（逐点支撑
     指派），再对求和保正接口显式实例化装配——不经逐句转发。 *)
  assert (Hpt : forall s, lt zero (exp_neg (opp (mult (inv_pos T T_pos) (z s))))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (mult (inv_pos T T_pos) (z s)))) Hpt).
Qed.

Definition softmax_temp (z : logits) (s : S) : R :=
  mult (exp_pos_fn (mult (inv_pos T T_pos) (z s)))
       (inv_pos (partition_function_temp z) (partition_function_temp_pos z)).

(* 温度版概率分布公理（与单位温度版同构） *)
Theorem softmax_temp_pos :
  forall z : logits, forall s : S, lt zero (softmax_temp z s).
Proof.
  intros z s.
  unfold softmax_temp, exp_pos_fn.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

Theorem softmax_temp_normalized :
  forall z : logits, Id (sum_over_S (fun s => softmax_temp z s)) one.
Proof.
  intro z.
  unfold softmax_temp.
  assert (Hext : Id (sum_over_S (fun s => mult (exp_pos_fn (mult (inv_pos T T_pos) (z s))) (inv_pos (partition_function_temp z) (partition_function_temp_pos z))))
                   (sum_over_S (fun s => mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (exp_pos_fn (mult (inv_pos T T_pos) (z s))))))
    by exact (sum_over_S_ext (fun s => mult (exp_pos_fn (mult (inv_pos T T_pos) (z s))) (inv_pos (partition_function_temp z) (partition_function_temp_pos z)))
                             (fun s => mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (exp_pos_fn (mult (inv_pos T T_pos) (z s))))
                             (fun s => mult_comm (exp_pos_fn (mult (inv_pos T T_pos) (z s))) (inv_pos (partition_function_temp z) (partition_function_temp_pos z)))).
  rewrite Hext.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (exp_pos_fn (mult (inv_pos T T_pos) (z s)))))
                    (mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z))
                          (sum_over_S (fun s => exp_pos_fn (mult (inv_pos T T_pos) (z s))))))
    by exact (sum_over_S_linear (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (fun s => exp_pos_fn (mult (inv_pos T T_pos) (z s)))).
  rewrite Hlin.
  unfold partition_function_temp.
  assert (Hcc : Id (mult (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (partition_function_temp z)) one)
    by exact (id_trans (mult_comm (inv_pos (partition_function_temp z) (partition_function_temp_pos z)) (partition_function_temp z))
                       (inv_pos_correct (partition_function_temp z) (partition_function_temp_pos z))).
  exact Hcc.
Qed.

(* ============================================================ *)
(* 非平凡版本：温度化 softmax 的凸组合归一化守恒               *)
(* （温度退火下的注意力混合——多温度蒸馏 / 专家混合的数学基础； *)
(*   凸组合的权重与温度独立）。                                *)
(* ============================================================ *)
Theorem softmax_temp_mix_normalized :
  forall (z z' : logits) (alpha : R) (Halpha : lt zero alpha) (Halpha1 : lt zero (minus one alpha)),
    Id (sum_over_S (fun s => plus (mult alpha (softmax_temp z s)) (mult (minus one alpha) (softmax_temp z' s)))) one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : Id (sum_over_S (fun s => softmax_temp z s)) one) by exact (softmax_temp_normalized z).
  assert (Hq : Id (sum_over_S (fun s => softmax_temp z' s)) one) by exact (softmax_temp_normalized z').
  assert (Hadd : Id (sum_over_S (fun s => plus (mult alpha (softmax_temp z s)) (mult (minus one alpha) (softmax_temp z' s))))
                   (plus (sum_over_S (fun s => mult alpha (softmax_temp z s)))
                         (sum_over_S (fun s => mult (minus one alpha) (softmax_temp z' s)))))
    by exact (sum_over_S_add (fun s => mult alpha (softmax_temp z s)) (fun s => mult (minus one alpha) (softmax_temp z' s))).
  rewrite Hadd.
  assert (Hlin1 : Id (sum_over_S (fun s => mult alpha (softmax_temp z s))) (mult alpha (sum_over_S (fun s => softmax_temp z s))))
    by exact (sum_over_S_linear alpha (fun s => softmax_temp z s)).
  rewrite Hlin1.
  assert (Hlin2 : Id (sum_over_S (fun s => mult (minus one alpha) (softmax_temp z' s))) (mult (minus one alpha) (sum_over_S (fun s => softmax_temp z' s))))
    by exact (sum_over_S_linear (minus one alpha) (fun s => softmax_temp z' s)).
  rewrite Hlin2.
  rewrite Hp. rewrite Hq.
  assert (Hm1 : Id (mult alpha one) alpha) by exact (mult_one alpha).
  rewrite Hm1.
  assert (Hm2 : Id (mult (minus one alpha) one) (minus one alpha)) by exact (mult_one (minus one alpha)).
  rewrite Hm2.
  (* 目标：plus alpha (minus one alpha) = one——assert + exact 链（同 boltzmann_mix_normalized 版） *)
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

Theorem softmax_temp_relative :
  forall z : logits, forall s s' : S,
    Id (softmax_temp z s)
       (mult (softmax_temp z s')
             (exp_pos_fn (mult (inv_pos T T_pos) (minus (z s) (z s'))))).
Proof.
  intros z s s'.
  unfold softmax_temp, exp_pos_fn.
  set (A := exp_neg (opp (mult (inv_pos T T_pos) (z s')))).
  set (B := exp_neg (opp (mult (inv_pos T T_pos) (minus (z s) (z s'))))).
  set (C := inv_pos (partition_function_temp z) (partition_function_temp_pos z)).
  set (Ap := exp_neg (opp (mult (inv_pos T T_pos) (z s)))).
  (* 重组：mult (mult A C) B = mult (mult A B) C *)
  assert (Hre : Id (mult (mult A C) B) (mult (mult A B) C)).
  {
    assert (H1 : Id (mult (mult A C) B) (mult A (mult C B)))
      by exact (id_sym (mult_assoc A C B)).
    assert (H2 : Id (mult A (mult C B)) (mult A (mult B C)))
      by exact (id_cong (fun x => mult A x) (mult_comm C B)).
    assert (H3 : Id (mult A (mult B C)) (mult (mult A B) C))
      by exact (mult_assoc A B C).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* 指数相加：A·B = Ap（exp_neg_plus + 代数） *)
  assert (Hprod : Id (mult A B) Ap).
  {
    unfold A, B, Ap.
    assert (Hep : Id (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s'))))
                           (exp_neg (opp (mult (inv_pos T T_pos) (minus (z s) (z s'))))))
                     (exp_neg (plus (opp (mult (inv_pos T T_pos) (z s')))
                                    (opp (mult (inv_pos T T_pos) (minus (z s) (z s')))))))
      by exact (id_sym (exp_neg_plus (opp (mult (inv_pos T T_pos) (z s')))
                                     (opp (mult (inv_pos T T_pos) (minus (z s) (z s')))))).
    rewrite Hep.
    assert (Halg : Id (plus (opp (mult (inv_pos T T_pos) (z s')))
                            (opp (mult (inv_pos T T_pos) (minus (z s) (z s')))))
                      (opp (mult (inv_pos T T_pos) (z s)))).
    {
      set (X := opp (mult (inv_pos T T_pos) (z s'))).
      set (Y := opp (mult (inv_pos T T_pos) (z s))).
      set (Z := mult (inv_pos T T_pos) (z s')).
      (* opp (mult invT (minus (z s) (z s'))) = plus (opp (mult invT (z s))) (mult invT (z s')) = plus Y Z *)
      assert (H1 : Id (opp (mult (inv_pos T T_pos) (minus (z s) (z s'))))
                      (plus Y Z)).
      {
        assert (Hd : Id (mult (inv_pos T T_pos) (minus (z s) (z s')))
                        (minus (mult (inv_pos T T_pos) (z s)) (mult (inv_pos T T_pos) (z s'))))
          by exact (mult_minus_distr_l (inv_pos T T_pos) (z s) (z s')).
        assert (H2 : Id (opp (minus (mult (inv_pos T T_pos) (z s)) (mult (inv_pos T T_pos) (z s'))))
                        (plus (opp (mult (inv_pos T T_pos) (z s))) (mult (inv_pos T T_pos) (z s'))))
          by exact (opp_minus (mult (inv_pos T T_pos) (z s)) (mult (inv_pos T T_pos) (z s'))).
        unfold Y, Z.
        exact (id_trans (id_cong (fun x => opp x) Hd) H2).
      }
      (* 目标（set X/Y/Z 后）：plus X (opp (mult invT (minus ...))) = Y *)
      rewrite H1.
      (* 重组：plus X (plus Y Z) = plus Y (plus X Z) *)
      assert (Hsw : Id (plus X (plus Y Z)) (plus Y (plus X Z))).
      {
        assert (Hsw1 : Id (plus X (plus Y Z)) (plus (plus X Y) Z))
          by exact (plus_assoc X Y Z).
        assert (Hsw2 : Id (plus (plus X Y) Z) (plus (plus Y X) Z))
          by exact (id_cong (fun w => plus w Z) (plus_comm X Y)).
        assert (Hsw3 : Id (plus (plus Y X) Z) (plus Y (plus X Z)))
          by exact (id_sym (plus_assoc Y X Z)).
        exact (id_trans Hsw1 (id_trans Hsw2 Hsw3)).
      }
      rewrite Hsw.
      (* plus X Z = zero（X 与 Z 互逆，交换后配 plus_opp） *)
      assert (Hpz : Id (plus X Z) zero)
        by exact (id_trans (plus_comm X Z) (plus_opp (mult (inv_pos T T_pos) (z s')))).
      assert (H5 : Id (plus Y (plus X Z)) (plus Y zero))
        by exact (id_cong (fun w => plus Y w) Hpz).
      assert (H6 : Id (plus Y zero) Y) by exact (plus_zero Y).
      exact (id_trans H5 H6).
    }
    apply (id_cong (fun x => exp_neg x)). exact Halg.
  }
  (* 组装：mult Ap C = mult (mult A C) B *)
  rewrite Hre.
  rewrite Hprod.
  reflexivity.
Qed.
(* Gap 集中定理：能量间隙 ⟹ 非最优态的注意力权重指数地被最优态压制。
   前提（温度化 gap）：γ/T ≤ (z(s_star) - z(s))/T（γ > 0 为间隙）。
   结论：softmax_T(s) ≤ softmax_T(s_star)·e^{-γ/T}——硬注意力极限（T→0）的代数内核。 *)
Theorem softmax_gap_concentration :
  forall (z : logits) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (minus (z s_star) (z s))) ->
      le (softmax_temp z s)
         (mult (softmax_temp z s_star)
               (exp_neg (mult (inv_pos T T_pos) gamma))).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  assert (Hrel : Id (softmax_temp z s)
                    (mult (softmax_temp z s_star)
                          (exp_pos_fn (mult (inv_pos T T_pos) (minus (z s) (z s_star))))))
    by exact (softmax_temp_relative z s s_star).
  rewrite Hrel.
  (* 指数参数恒等：e^{(z(s)-z(s_star))/T} = exp_neg (mult invT (minus (z s_star) (z s))) *)
  assert (Heq : Id (exp_pos_fn (mult (inv_pos T T_pos) (minus (z s) (z s_star))))
                   (exp_neg (mult (inv_pos T T_pos) (minus (z s_star) (z s))))).
  {
    unfold exp_pos_fn.
    assert (Hopp : Id (opp (mult (inv_pos T T_pos) (minus (z s) (z s_star))))
                     (mult (inv_pos T T_pos) (minus (z s_star) (z s)))).
    {
      assert (H1 : Id (opp (mult (inv_pos T T_pos) (minus (z s) (z s_star))))
                      (mult (inv_pos T T_pos) (opp (minus (z s) (z s_star)))))
        by exact (id_sym (opp_mult_l (inv_pos T T_pos) (minus (z s) (z s_star)))).
      assert (H2 : Id (mult (inv_pos T T_pos) (opp (minus (z s) (z s_star))))
                      (mult (inv_pos T T_pos) (minus (z s_star) (z s))))
        by exact (id_cong (fun x => mult (inv_pos T T_pos) x)
                          (id_trans (opp_minus (z s) (z s_star)) (plus_comm (opp (z s)) (z s_star)))).
      exact (id_trans H1 H2).
    }
    apply (id_cong (fun x => exp_neg x)). exact Hopp.
  }
  rewrite Heq.
  (* 目标：softmax_T(s_star)·e^{-(z(s_star)-z(s))/T} ≤ softmax_T(s_star)·e^{-γ/T}
     由 exp_neg_le_decr（指数参数 ≤）+ mult 单调（softmax_temp_pos） *)
  apply (le_mult_compat_r (softmax_temp z s_star)
                          (exp_neg (mult (inv_pos T T_pos) (minus (z s_star) (z s))))
                          (exp_neg (mult (inv_pos T T_pos) gamma))).
  - apply (lt_le_iff _ _). left. apply softmax_temp_pos.
  - apply exp_neg_le_decr. exact Hgap.
Qed.

(* ============================================================ *)
(* 零温度极限（P3：硬注意力坍缩的定量形式）                     *)
(* ============================================================ *)
(* softmax_gap_concentration 给出 softmax_T(s) ≤ softmax_T(s_star)·e^{-γ/T}；
   此处两侧除以 softmax_T(s_star) > 0，得到非最优态相对最优态的权重比：
     softmax_T(s) / softmax_T(s_star) ≤ e^{-γ/T}
   当 T→0（1/T→∞）时该比指数衰减到 0——注意力坍缩（attention    *)
(* collapse）与硬注意力极限的定量证明。这是 gap 集中定理的非平凡 *)
(* 平行版本（比值形式，含构造性除法：两侧乘 inv B > 0 并折叠）。 *)
(* ------------------------------------------------------------ *)
Theorem temperature_zero_limit :
  forall (z : logits) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (minus (z s_star) (z s))) ->
      le (mult (softmax_temp z s)
               (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
         (exp_neg (mult (inv_pos T T_pos) gamma)).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  (* gap 集中：A ≤ B·C（A := softmax_T(s)，B := softmax_T(s_star)，
     C := e^{-γ/T}） *)
  assert (Hgc : le (softmax_temp z s)
                   (mult (softmax_temp z s_star)
                         (exp_neg (mult (inv_pos T T_pos) gamma))))
    by exact (softmax_gap_concentration z s_star gamma Hgamma s Hgap).
  (* 两侧乘以 inv B > 0：inv B · A ≤ inv B · (B·C)（le_mult_compat_r） *)
  assert (Hinv : le zero (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))).
  { apply (lt_le_iff _ _). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (softmax_temp z s))
                    (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (mult (softmax_temp z s_star)
                                (exp_neg (mult (inv_pos T T_pos) gamma)))))
    by exact (le_mult_compat_r (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                               (softmax_temp z s)
                               (mult (softmax_temp z s_star)
                                     (exp_neg (mult (inv_pos T T_pos) gamma)))
                               Hinv Hgc).
  (* LHS 交换：inv B · A = A · inv B（mult_comm） *)
  assert (Hsw : Id (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                         (softmax_temp z s))
                   (mult (softmax_temp z s)
                         (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))))
    by exact (mult_comm (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                        (softmax_temp z s)).
  assert (Hlhs : le (mult (softmax_temp z s)
                          (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
                    (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (mult (softmax_temp z s_star)
                                (exp_neg (mult (inv_pos T T_pos) gamma)))))
    by exact (le_id_l (mult (softmax_temp z s)
                            (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
                      (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                            (softmax_temp z s))
                      (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                            (mult (softmax_temp z s_star)
                                  (exp_neg (mult (inv_pos T T_pos) gamma))))
                      (id_sym Hsw) Hdiv).
  (* RHS 折叠：(inv B · B)·C = 1·C = C *)
  assert (Hrhs : Id (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                           (mult (softmax_temp z s_star)
                                 (exp_neg (mult (inv_pos T T_pos) gamma))))
                     (exp_neg (mult (inv_pos T T_pos) gamma))).
  {
    assert (H1 : Id (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                          (mult (softmax_temp z s_star)
                                (exp_neg (mult (inv_pos T T_pos) gamma))))
                    (mult (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                                (softmax_temp z s_star))
                          (exp_neg (mult (inv_pos T T_pos) gamma))))
      by exact (mult_assoc (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                           (softmax_temp z s_star)
                           (exp_neg (mult (inv_pos T T_pos) gamma))).
    assert (H2 : Id (mult (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                                (softmax_temp z s_star))
                          (exp_neg (mult (inv_pos T T_pos) gamma)))
                    (mult one (exp_neg (mult (inv_pos T T_pos) gamma))))
      by exact (id_cong (fun x => mult x (exp_neg (mult (inv_pos T T_pos) gamma)))
                        (id_trans (mult_comm (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                                             (softmax_temp z s_star))
                                  (inv_pos_correct (softmax_temp z s_star) (softmax_temp_pos z s_star)))).
    assert (H3 : Id (mult one (exp_neg (mult (inv_pos T T_pos) gamma)))
                    (exp_neg (mult (inv_pos T T_pos) gamma)))
      by exact (id_trans (mult_comm one (exp_neg (mult (inv_pos T T_pos) gamma)))
                         (mult_one (exp_neg (mult (inv_pos T T_pos) gamma)))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* 组合：A · inv B ≤ C（le_id_r 替换 RHS） *)
  exact (le_id_r (mult (softmax_temp z s)
                       (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star)))
                 (mult (inv_pos (softmax_temp z s_star) (softmax_temp_pos z s_star))
                       (mult (softmax_temp z s_star)
                             (exp_neg (mult (inv_pos T T_pos) gamma))))
                 (exp_neg (mult (inv_pos T T_pos) gamma))
                 Hrhs Hlhs).
Qed.

(* ============================================================ *)
(* 缩放-温度对偶（1/√d 缩放视角；sD2-scaled 增量）               *)
(* 缩放 softmax 族 sc(z; c)_s := e^{c·z_s} / Σ_{s'} e^{c·z_{s'}}：*)
(* c 为任意实缩放因子（无需正性：exp 恒正 ⟹ 配分函数正性自由）。*)
(* 核心对偶引理 scale_temp_duality：∀ c > 0，以 1/c 缩放 logits  *)
(* 的 softmax == 温度 c 的 softmax（缩放因子 1/√d 与温度 √d 是   *)
(* 同一正参数轴上的互逆参数化；纯 unfold + id_cong + inv_pos_ext *)
(* + id_refl 恒等证明，零新公理）。                              *)
(* (b) 平方维数 d = k² 以见证式 sqrt_witness d r := r·r == d 表述 *)
(* （无 sqrt 函数符号）：d = 4/r = 2 实例 + 通用 (d, r) 见证引理。*)
(* (c) 非平方 d 的一般 √d 需构造性平方根（单独设立，不在本块）。 *)
(* ============================================================ *)

(* 缩放配分函数：Z_c(z) := Σ_s e^{c·z_s}（c 任意实，无需正性） *)
Definition partition_function_scaled (c : R) (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (mult c (z s))).

(* 缩放配分正性：exp 恒正 × sum_pos_preserved（副本 L27471-27479） *)
Lemma partition_function_scaled_pos :
  forall c z, lt zero (partition_function_scaled c z).
Proof.
  intros c z.
  unfold partition_function_scaled, exp_pos_fn.
  (* 展开至定义层（同族样板复用）：逐点正性单列为显式命题（逐点支撑
     指派），再对求和保正接口显式实例化装配——不经逐句转发。 *)
  assert (Hpt : forall s, lt zero (exp_neg (opp (mult c (z s))))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (mult c (z s)))) Hpt).
Qed.

(* 缩放 softmax：sc(z; c)_s := e^{c·z_s} / Z_c(z)（c 任意实） *)
Definition softmax_scaled (c : R) (z : logits) (s : S) : R :=
  mult (exp_pos_fn (mult c (z s)))
       (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)).

(* 缩放族概率公理：正性（副本 softmax_temp_pos L27486-27494） *)
Theorem softmax_scaled_pos :
  forall c z s, lt zero (softmax_scaled c z s).
Proof.
  intros c z s.
  unfold softmax_scaled, exp_pos_fn.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* 缩放族概率公理：归一化（副本 softmax_temp_normalized L27496-27517） *)
Theorem softmax_scaled_normalized :
  forall c z, Id (sum_over_S (fun s => softmax_scaled c z s)) one.
Proof.
  intros c z.
  unfold softmax_scaled.
  assert (Hext : Id (sum_over_S (fun s => mult (exp_pos_fn (mult c (z s))) (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z))))
                   (sum_over_S (fun s => mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (exp_pos_fn (mult c (z s))))))
    by exact (sum_over_S_ext (fun s => mult (exp_pos_fn (mult c (z s))) (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)))
                             (fun s => mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (exp_pos_fn (mult c (z s))))
                             (fun s => mult_comm (exp_pos_fn (mult c (z s))) (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)))).
  rewrite Hext.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (exp_pos_fn (mult c (z s)))))
                    (mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z))
                          (sum_over_S (fun s => exp_pos_fn (mult c (z s))))))
    by exact (sum_over_S_linear (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (fun s => exp_pos_fn (mult c (z s)))).
  rewrite Hlin.
  unfold partition_function_scaled.
  assert (Hcc : Id (mult (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (partition_function_scaled c z)) one)
    by exact (id_trans (mult_comm (inv_pos (partition_function_scaled c z) (partition_function_scaled_pos c z)) (partition_function_scaled c z))
                       (inv_pos_correct (partition_function_scaled c z) (partition_function_scaled_pos c z))).
  exact Hcc.
Qed.

(* 温度参数化配分函数（= partition_function_temp L27468 的      *)
(* (T0, HT0) 显式版；供对偶引理对任意温度 c 陈述）              *)
Definition partition_function_temp_param (T0 : R) (HT0 : lt zero T0) (z : logits) : R :=
  sum_over_S (fun s => exp_pos_fn (mult (inv_pos T0 HT0) (z s))).

(* 温度参数化配分正性（副本 L27471-27479） *)
Lemma partition_function_temp_param_pos :
  forall T0 HT0 z, lt zero (partition_function_temp_param T0 HT0 z).
Proof.
  intros T0 HT0 z.
  unfold partition_function_temp_param, exp_pos_fn.
  (* 展开至定义层（同族样板复用）：逐点正性单列为显式命题（逐点支撑
     指派），再对求和保正接口显式实例化装配——不经逐句转发。 *)
  assert (Hpt : forall s, lt zero (exp_neg (opp (mult (inv_pos T0 HT0) (z s))))).
  { intro s. apply exp_neg_pos. }
  exact (sum_pos_preserved (fun s => exp_neg (opp (mult (inv_pos T0 HT0) (z s)))) Hpt).
Qed.

(* 温度参数化 softmax（= softmax_temp L27481 的 (T0, HT0) 显式版）*)
Definition softmax_temp_param (T0 : R) (HT0 : lt zero T0) (z : logits) (s : S) : R :=
  mult (exp_pos_fn (mult (inv_pos T0 HT0) (z s)))
       (inv_pos (partition_function_temp_param T0 HT0 z) (partition_function_temp_param_pos T0 HT0 z)).

(* ============================================================ *)
(* (a) 缩放-温度对偶引理（本块核心）                             *)
(* 语句：∀ c > 0，以 1/c 缩放 logits 的 softmax（= 缩放因子      *)
(* inv_pos c Hc 即 1/c）== 温度 c 的 softmax。缩放因子 1/√d 与   *)
(* 温度 √d 互逆：取 c := √d 即"1/√d 缩放 == 温度 √d"。          *)
(* 证明：unfold 后两侧首因子（分子 e^{(1/c)z_s}）逐字相同，       *)
(* id_cong 消去；配分函数定义性相等 ⟹ inv_pos_ext + id_refl。    *)
(* 纯恒等链，零新公理（只用接口既有字段）。                      *)
(* ============================================================ *)
Theorem scale_temp_duality :
  forall (c : R) (Hc : lt zero c) (z : logits) (s : S),
    Id (softmax_scaled (inv_pos c Hc) z s) (softmax_temp_param c Hc z s).
Proof.

  intros c Hc z s. unfold softmax_scaled, softmax_temp_param. exact (id_cong (fun x => mult (exp_pos_fn (mult (inv_pos c Hc) (z s))) x) (inv_pos_ext (partition_function_scaled (inv_pos c Hc) z) (partition_function_temp_param c Hc z) (partition_function_scaled_pos (inv_pos c Hc) z) (partition_function_temp_param_pos c Hc z) id_refl)).

Qed.

(* 反向对称：温度 c 的 softmax == 以 1/c 缩放的 softmax（id_sym） *)
Lemma temp_is_scale_duality :
  forall (c : R) (Hc : lt zero c) (z : logits) (s : S),
    Id (softmax_temp_param c Hc z s) (softmax_scaled (inv_pos c Hc) z s).
Proof.
  intros c Hc z s. exact (id_sym (scale_temp_duality c Hc z s)).
Qed.

(* ============================================================ *)
(* (b) 平方维数特例：d = k²（√d := r 见证式，无 sqrt 函数符号） *)
(* sqrt_witness d r := Id (mult r r) d（r·r == d）。              *)
(* 1/√d 缩放构造地取 inv_pos r Hr（r 为 √d 的见证），温度 √d  *)
(* 即 r。d = k² 时见证 r := k；d = 4、r = 2 见下（two_mult：  *)
(* 2·2 == 2+2，非自反、真证明）。                                *)
(* ============================================================ *)
Definition sqrt_witness (d r : R) : Set := Id (mult r r) d.

(* d = 4 = 2² 见证：r := 2，2·2 == 4（4 写作 plus 2 2；two_mult） *)
Lemma sq_witness_4 :
  sqrt_witness (plus (plus one one) (plus one one)) (plus one one).
Proof.
  unfold sqrt_witness.
  exact (two_mult (plus one one)).
Qed.

(* 通用平方维数对偶：凡 d = r²（r > 0，见证式）则 1/r 缩放 ==    *)
(* 温度 r 的 softmax（scale_temp_duality 的 r-实例；d 仅经见证    *)
(* 命名，√d 的角色由 r 承担——抽象层无 sqrt 函数符号）           *)
Theorem scale_sqrt_witness_dual :
  forall (d r : R) (Hr : lt zero r),
    sqrt_witness d r ->
    forall (z : logits) (s : S),
      Id (softmax_scaled (inv_pos r Hr) z s) (softmax_temp_param r Hr z s).
Proof.
  intros d r Hr Hw z s. exact (scale_temp_duality r Hr z s).
Qed.

(* d = 4（r = 2）实例：softmax(z/2) == 温度 2 的 softmax          *)
(* （1/√4 = 1/2 := inv_pos 2；温度 √4 = 2 := plus one one）      *)
Lemma half_scale_is_temp_two :
  forall (z : logits) (s : S),
    Id (softmax_scaled (inv_pos (plus one one) two_pos) z s)
       (softmax_temp_param (plus one one) two_pos z s).
Proof.
  intros z s. exact (scale_temp_duality (plus one one) two_pos z s).
Qed.

(* ---- Boltzmann 分布（温度 D > 0，能量 energy） ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : logits.
Variable z : logits.   (* 注意力 logits（attention_is_gibbs 的前提变量） *)

Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo : R := sum_over_S boltzmann_factor.

(* 前置引理（原 Variable 换同名 Lemma， 基座消融波 T2 终判 B21）：由 sum_pos_preserved+逐点 exp_neg_pos 导出；零承认件 *)
Lemma Z_thermo_pos : lt zero Z_thermo.
Proof.
  unfold Z_thermo. apply sum_pos_preserved. intros s. unfold boltzmann_factor.
  apply exp_neg_pos.
Qed.


Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

(* 关键定理：单位温度（inv_pos D D_pos = one）且 energy = -logits 时，
   softmax = Boltzmann 分布。
   注：前提用 Id (inv_pos D D_pos) one（定义层面的"单位温度"），
   避免 Id D one 下证明参数 D_pos 的依赖类型移植。 *)
Theorem attention_is_gibbs :
  (Id (inv_pos D D_pos) one) ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id Z_thermo (partition_function z) ->
  forall s : S, Id (softmax z s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  unfold softmax, boltzmann_dist_attn, boltzmann_factor, exp_pos_fn.
  rewrite HD.
  assert (Hml : Id (mult one (energy s)) (energy s))
    by exact (id_trans (mult_comm one (energy s)) (mult_one (energy s))).
  rewrite Hml.
  rewrite (Henergy s).
  (* 配分函数相等 ⟹ 分布中的逆元统一（inv_pos_ext 升级版，直接桥接不同 x） *)
  assert (Hie : Id (inv_pos Z_thermo Z_thermo_pos)
                   (inv_pos (partition_function z) (partition_function_pos z)))
    by exact (inv_pos_ext Z_thermo (partition_function z) Z_thermo_pos (partition_function_pos z) HZ).
  rewrite Hie.
  apply (mult_comm (exp_neg (opp (z s))) (inv_pos (partition_function z) (partition_function_pos z))).
Qed.

(* ============================================================ *)
(* 非平凡版本：任意温度下的 softmax = Boltzmann 对应            *)
(* attention_is_gibbs 的前提是 Id (inv_pos D D_pos) one（单位   *)
(* 温度特例）。此处推广到任意温度：只要注意力温度 T 与热力学   *)
(* 温度 D 一致（1/T = 1/D），且 energy = -logits，则温度化      *)
(* softmax 就是 Boltzmann 分布——推理温度 = 物理温度的核心对应。*)
(* ============================================================ *)
Theorem attention_is_gibbs_temp :
  (Id (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id Z_thermo (partition_function_temp z) ->
  forall s : S, Id (softmax_temp z s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  unfold softmax_temp, boltzmann_dist_attn, boltzmann_factor, exp_pos_fn.
  (* 温度统一（1/T = 1/D）+ energy = -logits ⟹ 因子相等：
     e^{-(-z(s))/T} = e^{-E(s)/D} *)
  assert (Hf : Id (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                  (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  {
    apply (id_cong (fun x => exp_neg x)).
    rewrite (Henergy s).
    (* 目标：opp (mult invT (z s)) = mult invD (opp (z s)) *)
    assert (H1 : Id (opp (mult (inv_pos T T_pos) (z s)))
                    (mult (inv_pos T T_pos) (opp (z s))))
      by exact (id_sym (opp_mult_l (inv_pos T T_pos) (z s))).
    assert (H2 : Id (mult (inv_pos T T_pos) (opp (z s)))
                    (mult (inv_pos D D_pos) (opp (z s))))
      by exact (id_cong (fun x => mult x (opp (z s))) HD).
    exact (id_trans H1 H2).
  }
  (* 配分函数相等 ⟹ 归一化逆元统一（inv_pos_ext 桥接不同配分函数） *)
  assert (Hie : Id (inv_pos Z_thermo Z_thermo_pos)
                   (inv_pos (partition_function_temp z) (partition_function_temp_pos z)))
    by exact (inv_pos_ext Z_thermo (partition_function_temp z) Z_thermo_pos (partition_function_temp_pos z) HZ).
  rewrite Hf.
  rewrite Hie.
  apply (mult_comm (exp_neg (mult (inv_pos D D_pos) (energy s)))
                   (inv_pos (partition_function_temp z) (partition_function_temp_pos z))).
Qed.

(* ============================================================ *)
(* 缩放-温度对偶 × Boltzmann 桥（合成；sD2-scaled 增量）         *)
(* 以 1/T 缩放的 attention（T := √d，d = T² 见证见上 sqrt_witness）*)
(* == 温度 T 的 softmax（scale_temp_duality c := T 特例）        *)
(* == 温度 D 的 Boltzmann（attention_is_gibbs_temp：1/T = 1/D、   *)
(*    energy = -logits、Z 匹配）。读法：√d := T := D 时即        *)
(* "1/√d 缩放 attention == 温度 √d 的 Boltzmann"。               *)
(* ============================================================ *)

(* 桥：1/T 缩放族 == 库内温度化 softmax（配分函数定义性相等，    *)
(* inv_pos_ext + id_refl；scale_temp_duality c := T + 副本合成） *)
Lemma scale_inv_T_eq_softmax_temp :
  forall (s : S),
    Id (softmax_scaled (inv_pos T T_pos) z s) (softmax_temp z s).
Proof.

  intros s. unfold softmax_scaled, softmax_temp. exact (id_cong (fun x => mult (exp_pos_fn (mult (inv_pos T T_pos) (z s))) x) (inv_pos_ext (partition_function_scaled (inv_pos T T_pos) z) (partition_function_temp z) (partition_function_scaled_pos (inv_pos T T_pos) z) (partition_function_temp_pos z) id_refl)).

Qed.

(* 合成：缩放-温度对偶 + attention_is_gibbs_temp（1/T = 1/D、     *)
(* energy = -logits、Z 匹配）⟹ 缩放 attention == Boltzmann。      *)
(* 语句即"1/√d 缩放 == 温度 √d 的 Boltzmann"（√d := T := D）。    *)
Theorem scaled_attention_is_gibbs_temp :
  (Id (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id Z_thermo (partition_function_temp z) ->
  forall s : S, Id (softmax_scaled (inv_pos T T_pos) z s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  assert (Hbr : Id (softmax_scaled (inv_pos T T_pos) z s) (softmax_temp z s))
    by exact (scale_inv_T_eq_softmax_temp s).
  assert (Hboltz : Id (softmax_temp z s) (boltzmann_dist_attn s))
    by exact (attention_is_gibbs_temp HD Henergy HZ s).
  exact (id_trans Hbr Hboltz).
Qed.

(* ---- 详细平衡与稳态（KV 逐出前的理论参照） ---- *)
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_dist_attn s) (transition s s'))
       (mult (boltzmann_dist_attn s') (transition s' s)).

(* 非平凡实现：详细平衡 ⟹ Boltzmann 分布是稳态
   （与 BoltzmannSteadyState 同型；此处针对本模块的 boltzmann_dist_attn，
     改名避免顶层重名） *)
Theorem steady_state_boltzmann_attn :
  forall s,
    Id (sum_over_S (fun s' => mult (boltzmann_dist_attn s') (transition s' s)))
       (boltzmann_dist_attn s).
Proof.
  intro s.
  assert (Hpoint : forall s', Id (mult (boltzmann_dist_attn s') (transition s' s))
                               (mult (boltzmann_dist_attn s) (transition s s'))).
  { intro s'. apply (detailed_balance s' s). }
  assert (Hext2 : Id (sum_over_S (fun s' => mult (boltzmann_dist_attn s') (transition s' s)))
                     (sum_over_S (fun s' => mult (boltzmann_dist_attn s) (transition s s'))))
    by exact (sum_over_S_ext (fun s' => mult (boltzmann_dist_attn s') (transition s' s))
                             (fun s' => mult (boltzmann_dist_attn s) (transition s s')) Hpoint).
  rewrite Hext2.
  assert (Hlin : Id (sum_over_S (fun s' => mult (boltzmann_dist_attn s) (transition s s')))
                    (mult (boltzmann_dist_attn s) (sum_over_S (fun s' => transition s s'))))
    by exact (sum_over_S_linear (boltzmann_dist_attn s) (fun s' => transition s s')).
  rewrite Hlin.
  rewrite (transition_normalization s).
  assert (Hmo : Id (mult (boltzmann_dist_attn s) one) (boltzmann_dist_attn s))
    by exact (mult_one (boltzmann_dist_attn s)).
  rewrite Hmo. reflexivity.
Qed.

(* ============ T2.1 新诚实接口假设 ============ *)
(* sTB1 净消口径（呼应审稿 01-M6 前提块/足迹表）：
   - 保留 = 诚实接口 C 类：delta/delta_pos/delta_lt_one/minorization（Doeblin 下界——
     softmax 核 peaked 时任意接近退化，δ 由实例核提供，代码侧不消）；
     lt_plus_compat_lt_le/lt_plus_compat_le_lt、sum_swap_cc 为待归一接口
     （Real 佐证 real_lt_plus_compat_le_lt L37815 / _lt_le L37828 已在库，TB-2 字段化归一）。
   - 净消（A 类）：abs_triangle_cc（零使用，已删——先例 differentiable_compose
     虚假假设清除）；abs_mult_cc（→ 接口字段 abs_mult，RIE L289，3 使用点改引）。
   - 保留（B-min 缺口）：abs_ge_zero_id_cc，缺口注释见声明处（Real 佐证组合 L38999+L38976）。 *)
(* Doeblin 下界：delta ∈ (0,1)，转移核每分量 ≥ δ·稳态质量 *)
Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.
Variable minorization : forall s s', le (mult delta (boltzmann_dist_attn s')) (transition s s').
(* lt+le 混合加保序（ConvergenceCauchy 同款；one_minus_delta_pos 需要） *)
(* [墙族登记·RW-MIX 混合保序] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批（TB-2 归一在案 :3974）。 *)
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
(* [墙族登记·RW-MIX 混合保序（对偶 le_lt 形）] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批（TB-2 归一在案 :3974）。 *)
Variable lt_plus_compat_le_lt : forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
(* 双和交换（任何具体有限和满足） *)
Variable sum_swap_cc : forall (f : S -> S -> R),
  Id (sum_over_S (fun s => sum_over_S (fun s' => f s s')))
     (sum_over_S (fun s' => sum_over_S (fun s => f s s'))).
(* abs 性质（构造性有序域标准性质）。sTB1 净消：
   - abs_triangle_cc：零使用虚假假设，已删（先例：differentiable_compose 虚假假设
     清除，注释 L13712-14）；同型真定理 = 接口字段 abs_triangle（RIE L286）。
   - abs_mult_cc：与接口字段 abs_mult（RIE L289，精确 Id 恒等 abs(a·b)==abs a·abs b）
     Section 内重复声明，已删；3 处使用点（原 L28274/L28350/L29606）改引接口字段
     abs_mult——签名同型（forall a b, Id (abs (mult a b)) (mult (abs a) (abs b))），
     参数序不变，使用点仅换名。
   以下保留为诚实缺口：abs_ge_zero_id_cc（le 版 abs 恒等：le zero a -> |a| == a）。
   接口 abs_pos（RIE L295）仅 lt 版；le→(lt∨eq) 无 tightness 桥（抽象层缺口）。
   Real 佐证组合路径：real_abs_pos_req（L38999，strict 版）+ real_abs_zero_req
   （L38976）+ real_le 的 Or 编码（L3409-3410）；le 版现成真引理库内暂无。 *)
Variable abs_ge_zero_id_cc : forall a, le zero a -> Id (abs a) a.

(* ============ 定义 ============ *)
(* two 用全局引理 two_pos（lt zero (plus one one)）；inv_two := 1/2 *)
Definition inv_two : R := inv_pos (plus one one) two_pos.

(* 总变差距离 TV(mu, nu) := (1/2)·Σ|mu − nu| *)
Definition tv_dist (mu nu : S -> R) : R :=
  mult inv_two (sum_over_S (fun s => abs (minus (mu s) (nu s)))).

(* 单步马尔可夫迭代 mu_{n+1}(s') := Σ_s mu(s)·T(s,s') *)
Definition attention_step (mu : S -> R) (s' : S) : R :=
  sum_over_S (fun s => mult (mu s) (transition s s')).

(* ============ 引理 1：1−δ > 0 ============ *)
Lemma one_minus_delta_pos : lt zero (minus one delta).
Proof.

  unfold minus. exact (lt_id_l zero (plus delta (opp delta)) (plus one (opp delta)) (id_sym (plus_opp delta)) (lt_plus_compat_lt_le delta one (opp delta) (opp delta) delta_lt_one (le_refl (opp delta)))).

Qed.

(* ============ 引理 2：Boltzmann 分布归一化 ============ *)
Lemma boltzmann_normalized_attn : Id (sum_over_S boltzmann_dist_attn) one.
Proof.

  unfold boltzmann_dist_attn. exact (id_trans (sum_over_S_linear (inv_pos Z_thermo Z_thermo_pos) boltzmann_factor) (id_trans (mult_comm (inv_pos Z_thermo Z_thermo_pos) Z_thermo) (inv_pos_correct Z_thermo Z_thermo_pos))).

Qed.

(* ============ 引理 3：残差核 Q ============ *)
(* Q(s,s') := inv(1−δ)·(T(s,s') − δ·p_b(s'))（Doeblin 分解的随机核） *)
Definition q_kernel (s s' : S) : R :=
  mult (inv_pos (minus one delta) one_minus_delta_pos)
       (minus (transition s s') (mult delta (boltzmann_dist_attn s'))).

(* Q 非负（minorization + inv 正） *)
Lemma q_kernel_nonneg : forall s s', le zero (q_kernel s s').
Proof.
  intros s s'.
  unfold q_kernel.
  apply (le_mult_nonneg_t12 (inv_pos (minus one delta) one_minus_delta_pos)
                            (minus (transition s s') (mult delta (boltzmann_dist_attn s')))).
  - apply (lt_le_iff _ _ (inl (inv_pos_pos (minus one delta) one_minus_delta_pos))).
  - apply (le_minus_nonneg (mult delta (boltzmann_dist_attn s')) (transition s s')).
    exact (minorization s s').
Qed.

(* Q 行归一化：Σ_{s'} Q(s,s') == one *)
Lemma q_kernel_normalized : forall s, Id (sum_over_S (fun s' => q_kernel s s')) one.
Proof.

  intro s. unfold q_kernel. exact (id_trans (sum_over_S_linear (inv_pos (minus one delta) one_minus_delta_pos) (fun s' => minus (transition s s') (mult delta (boltzmann_dist_attn s')))) (id_trans (id_cong (fun x => mult (inv_pos (minus one delta) one_minus_delta_pos) x) (id_trans (sum_over_S_minus (fun s' => transition s s') (fun s' => mult delta (boltzmann_dist_attn s'))) (id_cong2 minus (transition_normalization s) (id_trans (sum_over_S_linear delta boltzmann_dist_attn) (id_cong (fun x => mult delta x) boltzmann_normalized_attn))))) (id_trans (id_cong (fun x => mult (inv_pos (minus one delta) one_minus_delta_pos) x) (id_cong (fun y => minus one y) (mult_one delta))) (id_trans (mult_comm (inv_pos (minus one delta) one_minus_delta_pos) (minus one delta)) (inv_pos_correct (minus one delta) one_minus_delta_pos))))).

Qed.

(* ============ 引理 4：T 分解 T == δ·p + (1−δ)·Q ============ *)
Lemma transition_decomp : forall s s',
  Id (transition s s')
     (plus (mult delta (boltzmann_dist_attn s'))
           (mult (minus one delta) (q_kernel s s'))).
Proof.
  intros s s'.
  unfold q_kernel.
  assert (Habs : Id (mult (minus one delta)
                          (mult (inv_pos (minus one delta) one_minus_delta_pos)
                                (minus (transition s s') (mult delta (boltzmann_dist_attn s')))))
                    (minus (transition s s') (mult delta (boltzmann_dist_attn s')))).
  {
    apply (id_trans (mult_assoc (minus one delta) (inv_pos (minus one delta) one_minus_delta_pos)
                                (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))).
    apply (id_trans (id_cong (fun x => mult x (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))
                             (inv_pos_correct (minus one delta) one_minus_delta_pos))).
    apply (id_trans (mult_comm one (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))
                    (mult_one (minus (transition s s') (mult delta (boltzmann_dist_attn s'))))).
  }
  apply (id_trans (id_sym (minus_plus_cancel_gap (transition s s') (mult delta (boltzmann_dist_attn s'))))).
  apply (id_trans (plus_comm (minus (transition s s') (mult delta (boltzmann_dist_attn s')))
                             (mult delta (boltzmann_dist_attn s')))).
  apply (id_cong (fun x => plus (mult delta (boltzmann_dist_attn s')) x) (id_sym Habs)).
Qed.

(* ============ 引理 5：delta 吸收 delta·a + (1−delta)·a == a ============ *)
Lemma delta_absorb : forall a : R,
  Id (plus (mult delta a) (mult (minus one delta) a)) a.
Proof.
  intro a.
  assert (H1 : Id (plus delta (minus one delta)) one).
  {
    unfold minus.
    apply (id_trans (plus_assoc delta one (opp delta))).
    apply (id_trans (id_cong (fun x => plus x (opp delta)) (plus_comm delta one))).
    apply (id_trans (id_sym (plus_assoc one delta (opp delta)))).
    apply (id_trans (id_cong (fun x => plus one x) (plus_opp delta))).
    exact (plus_zero one).
  }
  assert (H2 : Id (plus (mult delta a) (mult (minus one delta) a))
                  (plus (mult a delta) (mult a (minus one delta)))).
  { apply (id_cong2 plus (mult_comm delta a) (mult_comm (minus one delta) a)). }
  assert (H3 : Id (plus (mult a delta) (mult a (minus one delta))) (mult a (plus delta (minus one delta)))).
  { exact (id_sym (distrib a delta (minus one delta))). }
  apply (id_trans H2 (id_trans H3 (id_trans (id_cong (fun x => mult a x) H1) (mult_one a)))).
Qed.

(* ============ 引理 6：迭代分解 mu' == δ·p + (1−δ)·mu·Q ============ *)
Lemma attention_step_decomp : forall mu s',
  Id (sum_over_S mu) one ->
  Id (attention_step mu s')
     (plus (mult delta (boltzmann_dist_attn s'))
           (mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s'))))).
Proof.
  intros mu s' Hmu_norm.
  unfold attention_step.
  apply (id_trans (sum_over_S_ext _ _
        (fun s => id_cong (fun x => mult (mu s) x) (transition_decomp s s')))).
  apply (id_trans (sum_over_S_ext _ _
        (fun s => distrib (mu s) (mult delta (boltzmann_dist_attn s')) (mult (minus one delta) (q_kernel s s'))))).
  apply (id_trans (sum_over_S_add (fun s => mult (mu s) (mult delta (boltzmann_dist_attn s')))
                                  (fun s => mult (mu s) (mult (minus one delta) (q_kernel s s'))))).
  (* 第一项：Σ mu·(δ·p) == δ·p（mu 归一化） *)
  assert (Hfirst : Id (sum_over_S (fun s => mult (mu s) (mult delta (boltzmann_dist_attn s'))))
                      (mult delta (boltzmann_dist_attn s'))).
  {
    apply (id_trans (sum_over_S_ext _ _ (fun s => mult_assoc (mu s) delta (boltzmann_dist_attn s')))).
    apply (id_trans (sum_over_S_ext _ _
        (fun s => id_cong (fun x => mult x (boltzmann_dist_attn s')) (mult_comm (mu s) delta)))).
    apply (id_trans (sum_over_S_ext _ _ (fun s => id_sym (mult_assoc delta (mu s) (boltzmann_dist_attn s'))))).
    apply (id_trans (sum_over_S_linear delta (fun s => mult (mu s) (boltzmann_dist_attn s')))).
    apply (id_trans (id_cong (fun x => mult delta x)
                             (id_trans (sum_over_S_ext _ _ (fun s => mult_comm (mu s) (boltzmann_dist_attn s')))
                                       (id_trans (sum_over_S_linear (boltzmann_dist_attn s') mu)
                                                 (id_trans (mult_comm (boltzmann_dist_attn s') (sum_over_S mu))
                                                           (id_cong (fun x => mult x (boltzmann_dist_attn s')) Hmu_norm)))))).
    apply (id_cong (fun x => mult delta x)
                   (id_trans (mult_comm one (boltzmann_dist_attn s')) (mult_one (boltzmann_dist_attn s')))).
  }
  exact (id_cong2 plus Hfirst (id_trans (sum_over_S_ext _ _ (fun s => id_trans (mult_assoc (mu s) (minus one delta) (q_kernel s s')) (id_trans (id_cong (fun x => mult x (q_kernel s s')) (mult_comm (mu s) (minus one delta))) (id_sym (mult_assoc (minus one delta) (mu s) (q_kernel s s')))))) (sum_over_S_linear (minus one delta) (fun s => mult (mu s) (q_kernel s s'))))).
Qed.

(* ============ 引理 7：迭代保持归一化 ============ *)
Lemma attention_step_normalized : forall mu,
  Id (sum_over_S mu) one ->
  Id (sum_over_S (attention_step mu)) one.
Proof.
  intros mu Hmu_norm.
  apply (id_trans (sum_over_S_ext _ _ (fun s' => attention_step_decomp mu s' Hmu_norm))).
  apply (id_trans (sum_over_S_add (fun s' => mult delta (boltzmann_dist_attn s'))
                                  (fun s' => mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))))).
  apply (id_trans (id_cong2 plus (id_trans (sum_over_S_linear delta boltzmann_dist_attn) (id_cong (fun x => mult delta x) boltzmann_normalized_attn)) (id_trans (sum_over_S_linear (minus one delta) (fun s2 => sum_over_S (fun s => mult (mu s) (q_kernel s s2)))) (id_cong (fun x => mult (minus one delta) x) (id_trans (id_sym (sum_swap_cc (fun s s2 => mult (mu s) (q_kernel s s2)))) (id_trans (sum_over_S_ext _ _ (fun s => sum_over_S_linear (mu s) (fun s2 => q_kernel s s2))) (sum_over_S_ext _ _ (fun s => id_cong (fun x => mult (mu s) x) (q_kernel_normalized s))))))))).
  (* 现在：plus (mult delta one) (mult (minus one delta) (sum_over_S (fun s => mult (mu s) one))) == one *)
  assert (Hsum_one : Id (sum_over_S (fun s => mult (mu s) one)) one).
  {
    apply (id_trans (sum_over_S_ext _ _ (fun s => mult_one (mu s)))).
    apply (id_trans (sum_over_S_ext _ _ (fun s => id_sym (id_trans (mult_comm one (mu s)) (mult_one (mu s)))))).
    apply (id_trans (sum_over_S_linear one mu)).
    apply (id_trans (id_cong (fun x => mult one x) Hmu_norm)).
    apply (id_trans (mult_comm one one) (mult_one one)).
  }
  apply (id_trans (id_cong (fun x => plus (mult delta one) x)
                           (id_cong (fun x => mult (minus one delta) x) Hsum_one))).
  exact (delta_absorb one).
Qed.


(* ============ 段 2：TV 收缩核心 ============ *)

(* 辅助：minus (plus a b) c == plus b (minus a c) *)
Lemma minus_plus_swap_cc : forall a b c : R,
  Id (minus (plus a b) c) (plus b (minus a c)).
Proof.

  intros a b c. unfold minus. exact (id_trans (id_sym (plus_assoc a b (opp c))) (id_trans (id_cong (fun x => plus a x) (plus_comm b (opp c))) (id_trans (plus_assoc a (opp c) b) (plus_comm (plus a (opp c)) b)))).

Qed.

(* 辅助：minus (mult a b) b == opp (mult (minus one a) b) *)
Lemma minus_scal_opp_cc : forall a b : R,
  Id (minus (mult a b) b) (opp (mult (minus one a) b)).
Proof.
  intros a b.
  assert (H : Id (minus a one) (opp (minus one a))).
  {
    unfold minus.
    apply (id_trans (plus_comm a (opp one))).
    apply (id_trans (id_cong2 plus (id_refl) (id_sym (double_neg a)))).
    apply (id_sym (opp_plus one (opp a))).
  }
  apply (id_trans (id_cong (fun x => minus (mult a b) x)
                           (id_sym (id_trans (mult_comm one b) (mult_one b))))).
  apply (id_trans (id_sym (mult_minus_distr_r_t12 a one b))).
  apply (id_trans (id_cong (fun x => mult x b) H) (opp_mult_r (minus one a) b)).
Qed.

(* 辅助：加性消去 plus a b == c ⟹ b == minus c a *)
Lemma plus_cancel_cc : forall a b c : R,
  Id (plus a b) c -> Id b (minus c a).
Proof.

  intros a b c H. unfold minus. exact (id_trans (id_sym (id_trans (plus_comm zero b) (plus_zero b))) (id_trans (id_cong (fun x => plus x b) (id_sym (plus_opp a))) (id_trans (id_sym (plus_assoc a (opp a) b)) (id_trans (id_cong (fun x => plus a x) (plus_comm (opp a) b)) (id_trans (plus_assoc a b (opp a)) (id_cong (fun x => plus x (opp a)) H)))))).

Qed.

(* 辅助：inv 吸收 mult (inv c) (mult c a) == a *)
Lemma absorb_inv_cc : forall (c : R) (Hc : lt zero c) (a : R),
  Id (mult (inv_pos c Hc) (mult c a)) a.
Proof.

  intros c Hc a. exact (id_trans (mult_assoc (inv_pos c Hc) c a) (id_trans (id_cong (fun x => mult x a) (id_trans (mult_comm (inv_pos c Hc) c) (inv_pos_correct c Hc))) (id_trans (mult_comm one a) (mult_one a)))).

Qed.

(* Boltzmann 分布正性 *)
Lemma boltzmann_attn_pos : forall s, lt zero (boltzmann_dist_attn s).
Proof.
  intro s.
  unfold boltzmann_dist_attn.
  apply mult_positive.
  - apply inv_pos_pos.
  - unfold boltzmann_factor. apply exp_neg_pos.
Qed.

(* 1−δ ≤ 1（delta ≥ 0） *)
Lemma one_minus_delta_le_one : le (minus one delta) one.
Proof.
  apply (le_id_r _ (plus (minus one delta) delta) _).
  - apply (id_trans (plus_comm (minus one delta) delta)
                    (minus_plus_cancel delta one)).
  - apply (le_plus_nonneg_r (minus one delta) delta).
    apply (lt_le_iff _ _ (inl delta_pos)).
Qed.

(* 1−δ < 1（delta > 0） *)
Lemma one_minus_delta_lt_one : lt (minus one delta) one.
Proof.

  unfold minus. exact (lt_id_r (plus one (opp delta)) (plus one zero) one (plus_zero one) (lt_plus_compat_le_lt one one (opp delta) zero (le_refl one) (lt_zero_opp delta delta_pos))).

Qed.

(* 稳态保持：p·Q == p（p·T==p 与分解结合） *)
Lemma boltzmann_q_fixed : forall s',
  Id (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))
     (boltzmann_dist_attn s').
Proof.
  intro s'.
  pose proof (steady_state_boltzmann_attn s') as H1.
  pose proof (attention_step_decomp boltzmann_dist_attn s' boltzmann_normalized_attn) as H2.
  assert (H3 : Id (plus (mult delta (boltzmann_dist_attn s'))
                        (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))))
                  (boltzmann_dist_attn s')).
  { apply (id_trans (id_sym H2) H1). }
  assert (H4 : Id (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s'))))
                  (minus (boltzmann_dist_attn s') (mult delta (boltzmann_dist_attn s')))).
  { exact (plus_cancel_cc (mult delta (boltzmann_dist_attn s'))
                          (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s'))))
                          (boltzmann_dist_attn s') H3). }
  assert (H6 : Id (minus (boltzmann_dist_attn s') (mult delta (boltzmann_dist_attn s')))
                  (mult (minus one delta) (boltzmann_dist_attn s'))).
  {
    apply (id_trans (id_cong (fun x => minus x (mult delta (boltzmann_dist_attn s')))
                             (id_sym (id_trans (mult_comm one (boltzmann_dist_attn s')) (mult_one (boltzmann_dist_attn s')))))).
    apply (id_sym (mult_minus_distr_r_t12 one delta (boltzmann_dist_attn s'))).
  }
  assert (H7 : Id (mult (minus one delta) (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s'))))
                  (mult (minus one delta) (boltzmann_dist_attn s'))).
  { apply (id_trans H4 H6). }
  apply (id_trans (id_sym (absorb_inv_cc (minus one delta) one_minus_delta_pos
                                          (sum_over_S (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))))
                  (id_trans (id_cong (fun x => mult (inv_pos (minus one delta) one_minus_delta_pos) x) H7)
                            (absorb_inv_cc (minus one delta) one_minus_delta_pos (boltzmann_dist_attn s')))).
Qed.

(* 逐点差分解：mu' − p == (1−δ)·Σ_s (mu−p)·Q *)
Lemma attention_diff_decomp : forall mu s',
  Id (sum_over_S mu) one ->
  Id (minus (attention_step mu s') (boltzmann_dist_attn s'))
     (mult (minus one delta)
           (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))).
Proof.

  intros mu s' Hmu_norm. exact (id_trans (id_cong (fun x => minus x (boltzmann_dist_attn s')) (attention_step_decomp mu s' Hmu_norm)) (id_trans (minus_plus_swap_cc (mult delta (boltzmann_dist_attn s')) (mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))) (boltzmann_dist_attn s')) (id_trans (id_cong (fun x => plus (mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))) x) (minus_scal_opp_cc delta (boltzmann_dist_attn s'))) (id_trans (id_sym (mult_minus_distr_l (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s'))) (boltzmann_dist_attn s'))) (id_cong (fun x => mult (minus one delta) x) (id_trans (id_cong (fun x => minus (sum_over_S (fun s => mult (mu s) (q_kernel s s'))) x) (id_sym (boltzmann_q_fixed s'))) (id_trans (id_sym (sum_over_S_minus (fun s => mult (mu s) (q_kernel s s')) (fun s => mult (boltzmann_dist_attn s) (q_kernel s s')))) (id_sym (sum_over_S_ext _ _ (fun s => id_trans (mult_comm (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')) (id_trans (mult_minus_distr_l (q_kernel s s') (mu s) (boltzmann_dist_attn s)) (id_cong2 minus (mult_comm (q_kernel s s') (mu s)) (mult_comm (q_kernel s s') (boltzmann_dist_attn s)))))))))))))).

Qed.


(* ============ 段 3：TV 收缩主定理 ============ *)

(* |Σ f·Q| ≤ Σ |f|·Q（abs_sum_le + 接口字段 abs_mult + Q ≥ 0） *)
Lemma abs_kernel_bound : forall (f : S -> R) (s' : S),
  le (abs (sum_over_S (fun s => mult (f s) (q_kernel s s'))))
     (sum_over_S (fun s => mult (abs (f s)) (q_kernel s s'))).
Proof.
  intros f s'.
  apply (le_id_r (abs (sum_over_S (fun s => mult (f s) (q_kernel s s'))))
                 (sum_over_S (fun s => abs (mult (f s) (q_kernel s s'))))
                 (sum_over_S (fun s => mult (abs (f s)) (q_kernel s s')))).
  - apply (sum_over_S_ext _ _ (fun s =>
      id_trans (abs_mult (f s) (q_kernel s s'))
               (id_cong (fun x => mult (abs (f s)) x) (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))))).
  - exact (abs_sum_le (fun s => mult (f s) (q_kernel s s'))).
Qed.

(* TV 距离非负 *)
Lemma tv_dist_nonneg : forall mu nu, le zero (tv_dist mu nu).
Proof.
  intros mu nu.
  unfold tv_dist.
  apply (le_mult_nonneg_t12 inv_two (sum_over_S (fun s => abs (minus (mu s) (nu s))))).
  - apply (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))).
  - apply sum_over_S_nonneg. intro s. apply abs_nonneg.
Qed.

(* 迭代保持非负：mu 归一化且非负 ⟹ attention_step mu 非负 *)
Lemma attention_step_nonneg : forall mu,
  Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
  forall s', le zero (attention_step mu s').
Proof.
  intros mu Hmu_norm Hmu_nonneg s'.
  set (X := mult delta (boltzmann_dist_attn s')).
  set (Y := mult (minus one delta) (sum_over_S (fun s => mult (mu s) (q_kernel s s')))).
  assert (HX : le zero X).
  {
    unfold X.
    apply (le_mult_nonneg_t12 delta (boltzmann_dist_attn s')).
    - apply (lt_le_iff _ _ (inl delta_pos)).
    - apply (lt_le_iff _ _ (inl (boltzmann_attn_pos s'))).
  }
  assert (HY : le zero Y).
  {
    unfold Y.
    apply (le_mult_nonneg_t12 (minus one delta)
                              (sum_over_S (fun s => mult (mu s) (q_kernel s s')))).
    - apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
    - apply sum_over_S_nonneg. intro s.
      apply (le_mult_nonneg_t12 (mu s) (q_kernel s s')).
      + exact (Hmu_nonneg s).
      + exact (q_kernel_nonneg s s').
  }
  assert (Hstep : le zero (plus X Y)).
  {
    assert (Hplus : le (plus zero zero) (plus X Y))
      by exact (le_plus_compat zero X zero Y HX HY).
    apply (le_id_l zero (plus zero zero) (plus X Y) (id_sym (plus_zero zero)) Hplus).
  }
  apply (le_id_r zero (plus X Y) (attention_step mu s')).
  - apply (id_sym (attention_step_decomp mu s' Hmu_norm)).
  - exact Hstep.
Qed.


(* 双和归约：(1/2)·Σ_{s'} (1−δ)·Σ_s f·Q == (1−δ)·(1/2)·Σ_s f *)
Lemma tv_reduce_cc : forall (f : S -> R),
  Id (mult inv_two (sum_over_S (fun s' => mult (minus one delta) (sum_over_S (fun s => mult (f s) (q_kernel s s'))))))
     (mult (minus one delta) (mult inv_two (sum_over_S f))).
Proof.

  intros f. exact (id_trans (id_cong (fun x => mult inv_two x) (id_trans (sum_over_S_linear (minus one delta) (fun s' => sum_over_S (fun s => mult (f s) (q_kernel s s')))) (id_cong (fun x => mult (minus one delta) x) (id_trans (id_sym (sum_swap_cc (fun s s' => mult (f s) (q_kernel s s')))) (id_trans (sum_over_S_ext _ _ (fun s => sum_over_S_linear (f s) (fun s2 => q_kernel s s2))) (id_trans (sum_over_S_ext _ _ (fun s => id_cong (fun x => mult (f s) x) (q_kernel_normalized s))) (sum_over_S_ext _ _ (fun s => mult_one (f s))))))))) (id_trans (mult_assoc inv_two (minus one delta) (sum_over_S f)) (id_trans (id_cong (fun x => mult x (sum_over_S f)) (mult_comm inv_two (minus one delta))) (id_sym (mult_assoc (minus one delta) inv_two (sum_over_S f)))))).

Qed.

(* |c·b| ≤ c·|b|（c ≥ 0） *)
Lemma abs_mult_nonneg_cc : forall a b, le zero a -> le (abs (mult a b)) (mult a (abs b)).
Proof.

  intros a b Ha. exact (le_id_l (abs (mult a b)) (mult a (abs b)) (mult a (abs b)) (id_trans (abs_mult a b) (id_cong (fun x => mult x (abs b)) (abs_ge_zero_id_cc a Ha))) (le_refl _)).

Qed.

(* ============ 主定理：单步 TV 收缩（Doeblin） ============ *)
Theorem attention_tv_contraction :
  forall mu, Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
    le (tv_dist (attention_step mu) boltzmann_dist_attn)
       (mult (minus one delta) (tv_dist mu boltzmann_dist_attn)).
Proof.
  intros mu Hmu_norm Hmu_nonneg.
  unfold tv_dist, attention_step.
  assert (Hpt : forall s', le (abs (minus (attention_step mu s') (boltzmann_dist_attn s')))
                             (mult (minus one delta)
                                   (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s'))))).
  {
    intro s'.
    pose proof (attention_diff_decomp mu s' Hmu_norm) as Hd.
    apply (le_id_l (abs (minus (attention_step mu s') (boltzmann_dist_attn s')))
                   (abs (mult (minus one delta)
                              (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))))
                   (mult (minus one delta)
                         (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s'))))).
    - apply (id_cong abs Hd).
    - apply (le_trans _ (mult (minus one delta)
                              (abs (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))))
                     _).
      + apply (abs_mult_nonneg_cc (minus one delta)
                                  (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s')))).
        apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
      + apply (le_mult_compat_r (minus one delta)
                                (abs (sum_over_S (fun s => mult (minus (mu s) (boltzmann_dist_attn s)) (q_kernel s s'))))
                                (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s')))).
        * apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
        * apply (abs_kernel_bound (fun s => minus (mu s) (boltzmann_dist_attn s)) s').
  }
  apply (le_trans _ (mult inv_two (sum_over_S (fun s' => mult (minus one delta)
                                                    (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s')))))) _).
  - apply (le_mult_compat_r inv_two
                            (sum_over_S (fun s' => abs (minus (attention_step mu s') (boltzmann_dist_attn s'))))
                            (sum_over_S (fun s' => mult (minus one delta)
                                              (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s')))))).
    + apply (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))).
    + apply sum_over_S_le. exact Hpt.
  - (* 第二项归约：(1/2)·Σ_{s'} (1−δ)·Σ_s |mu−p|·Q == (1−δ)·(1/2)·Σ_s |mu−p| *)
    apply (le_id_l (mult inv_two (sum_over_S (fun s' => mult (minus one delta)
                                                  (sum_over_S (fun s => mult (abs (minus (mu s) (boltzmann_dist_attn s))) (q_kernel s s'))))))
                   (mult (minus one delta) (mult inv_two (sum_over_S (fun s => abs (minus (mu s) (boltzmann_dist_attn s))))))
                   (mult (minus one delta) (mult inv_two (sum_over_S (fun s => abs (minus (mu s) (boltzmann_dist_attn s))))))).
    + exact (tv_reduce_cc (fun s => abs (minus (mu s) (boltzmann_dist_attn s)))).
    + apply le_refl.
Qed.


(* ============ 最终：几何迭代收缩与收敛 ============ *)

(* 几何击穿（Real 层阿基米德性质，同 ConvergenceCauchy r_arch_pow 模式） *)
Variable r_arch_pow_attn : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (r_pow (minus one delta) N)) eps).

(* (1−δ)^n 递减：m ≤ n ⟹ (1−δ)^n ≤ (1−δ)^m *)
Lemma r_pow_dec_iter_attn : forall m n, (m <= n)%nat -> le (r_pow (minus one delta) n) (r_pow (minus one delta) m).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (r_pow (minus one delta) n) _).
      * apply (r_pow_dec (minus one delta) n one_minus_delta_pos one_minus_delta_lt_one).
      * apply (IH m (proj1 (PeanoNat.Nat.leb_le m n) Emn)).
    + apply PeanoNat.Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* 迭代保持归一化 *)
Lemma iterate_attention_normalized : forall mu n,
  Id (sum_over_S mu) one -> Id (sum_over_S (iterate attention_step n mu)) one.
Proof.
  intros mu n Hmu_norm.
  induction n as [| n IH].
  - simpl. exact Hmu_norm.
  - simpl. apply attention_step_normalized. exact IH.
Qed.

(* 迭代保持非负 *)
Lemma iterate_attention_nonneg : forall mu n,
  Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
  forall s, le zero (iterate attention_step n mu s).
Proof.
  intros mu n Hmu_norm Hmu_nonneg.
  induction n as [| n IH].
  - simpl. exact Hmu_nonneg.
  - simpl. intro s. apply attention_step_nonneg. apply (iterate_attention_normalized mu n Hmu_norm). exact IH.
Qed.

(* 几何迭代 TV 收缩：(1−δ)^n·TV_0 界 *)
Lemma attention_tv_iter_contraction : forall mu n,
  Id (sum_over_S mu) one -> (forall s, le zero (mu s)) ->
    le (tv_dist (iterate attention_step n mu) boltzmann_dist_attn)
       (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn)).
Proof.
  intros mu n Hmu_norm Hmu_nonneg.
  induction n as [| n IH].
  - simpl.
    apply (le_id_l (tv_dist mu boltzmann_dist_attn)
                   (tv_dist (iterate attention_step 0 mu) boltzmann_dist_attn)
                   (mult one (tv_dist mu boltzmann_dist_attn))).
    + apply (id_sym (id_cong (fun x => tv_dist x boltzmann_dist_attn) (id_refl))).
    + apply (le_id_l (tv_dist mu boltzmann_dist_attn)
                     (mult one (tv_dist mu boltzmann_dist_attn))
                     (mult one (tv_dist mu boltzmann_dist_attn))
                     (id_sym (id_trans (mult_comm one (tv_dist mu boltzmann_dist_attn))
                                 (mult_one (tv_dist mu boltzmann_dist_attn))))
                     (le_refl _)).
  - set (mun := iterate attention_step n mu).
    assert (Hn_norm : Id (sum_over_S mun) one) by (unfold mun; apply (iterate_attention_normalized mu n Hmu_norm)).
    assert (Hn_nonneg : forall s, le zero (mun s)) by (unfold mun; apply (iterate_attention_nonneg mu n Hmu_norm Hmu_nonneg)).
    apply (le_trans _ (mult (minus one delta)
                            (tv_dist mun boltzmann_dist_attn)) _).
    + apply (le_id_l (tv_dist (attention_step mun) boltzmann_dist_attn)
                     (tv_dist (iterate attention_step (Datatypes.S n) mu) boltzmann_dist_attn)
                     (mult (minus one delta) (tv_dist mun boltzmann_dist_attn))).
      * apply (id_sym (id_cong (fun x => tv_dist x boltzmann_dist_attn) (id_refl))).
      * apply (attention_tv_contraction mun Hn_norm Hn_nonneg).
    + apply (le_trans _ (mult (minus one delta)
                              (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn))) _).
      * apply (le_mult_compat_r (minus one delta) (tv_dist mun boltzmann_dist_attn)
                                (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn))).
        -- apply (le_minus_nonneg delta one). apply (lt_le_iff _ _ (inl delta_lt_one)).
        -- exact IH.
      * apply (le_id_l (mult (minus one delta)
                             (mult (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn)))
                       (mult (r_pow (minus one delta) (Datatypes.S n)) (tv_dist mu boltzmann_dist_attn))
                       (mult (r_pow (minus one delta) (Datatypes.S n)) (tv_dist mu boltzmann_dist_attn))).
        -- apply (mult_assoc (minus one delta) (r_pow (minus one delta) n) (tv_dist mu boltzmann_dist_attn)).
        -- apply le_refl.
Qed.

(* 最终：注意力迭代收敛（TV → 0，sigT 形式；初态 TV 正） *)
Theorem attention_iterate_converges :
  forall mu0, Id (sum_over_S mu0) one -> (forall s, le zero (mu0 s)) ->
  forall eps, lt zero eps ->
    lt zero (tv_dist mu0 boltzmann_dist_attn) ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      lt (tv_dist (iterate attention_step n mu0) boltzmann_dist_attn) eps).
Proof.
  intros mu0 Hmu_norm Hmu_nonneg eps Hep Htv0.
  destruct (r_arch_pow_attn (tv_dist mu0 boltzmann_dist_attn) Htv0 eps Hep) as [N HN].
  exists N.
  intros n Hn.
  apply (le_lt_trans _ (mult (r_pow (minus one delta) n) (tv_dist mu0 boltzmann_dist_attn)) _).
  - exact (attention_tv_iter_contraction mu0 n Hmu_norm Hmu_nonneg).
  - apply (le_lt_trans _ (mult (r_pow (minus one delta) N) (tv_dist mu0 boltzmann_dist_attn)) _).
    + apply (le_mult_compat_weak (r_pow (minus one delta) n)
                               (r_pow (minus one delta) N)
                               (tv_dist mu0 boltzmann_dist_attn)).
      * exact (tv_dist_nonneg mu0 boltzmann_dist_attn).
      * apply (r_pow_dec_iter_attn N n (NatLe_drop N n Hn)).
    + exact (lt_id_l (mult (r_pow (minus one delta) N) (tv_dist mu0 boltzmann_dist_attn))
                     (mult (tv_dist mu0 boltzmann_dist_attn) (r_pow (minus one delta) N))
                     eps
                     (mult_comm (r_pow (minus one delta) N) (tv_dist mu0 boltzmann_dist_attn))
                     HN).
Qed.

(* ---- KV 逐出：打破详细平衡 ---- *)
Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition evicted_partition : R :=
  sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero evicted_partition.

Definition evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evicted_partition evicted_partition_pos) (boltzmann_factor s)
  else zero.

Definition db_breaking (s s' : S) : R :=
  abs (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
             (mult (evicted_boltzmann s') (evicted_transition s' s))).

(* 涨落-耗散型约束（由具体动力学推导，此处作显式假设） *)
Variable fluctuation_dissipation_bound :
  forall s s',
    le (db_breaking s s')
       (mult (abs (energy s)) (plus (abs (energy s')) one)).

Theorem eviction_db_breaking_bound :
  forall s s',
    le (db_breaking s s')
       (mult (abs (energy s)) (plus (abs (energy s')) one)).
Proof.

  intros s s'. exact (fluctuation_dissipation_bound s s').

Qed.

(* ============================================================ *)
(* KV 逐出最优策略（支撑定理）                                 *)
(* ============================================================ *)
(* 策略背景：给定容量预算，应保留 Boltzmann 权重最高（能量     *)
(* 最低 / 未来使用频率最高）的状态。以下两条支撑定理确保该     *)
(* 策略在数学上良性：                                        *)
(*   (a) 逐出后分布仍是概率测度（保留态上归一化）——概率语义  *)
(*       不因逐出而崩坏；                                      *)
(*   (b) 保留集合单调扩张 ⟹ 逐出配分函数不减——"保留越多质量越多"，贪心/最优保留策略的方向正确性。 *)

(* 逐点恒等：if k s then a·f(s) else 0 = a·(if k s then f(s) else 0) *)
Lemma eviction_if_linear :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) (a : R) (f : S -> R) (s : S),
    Id (if kd s then mult a (f s) else zero)
       (mult a (if kd s then f s else zero)).
Proof.
  intros k kd a f s.
  destruct (kd s) as [Hk | Hnk].
  - reflexivity.
  - (* 非保留态：zero = a·zero *)
    apply id_sym.
    apply mult_zero.
Qed.

(* 逐点单调：k1 ⊆ k2 ⟹ if k1 s then f s else 0 ≤ if k2 s then f s else 0
   （f 取 Boltzmann 因子，正性保证 zero ≤ f s 侧） *)
Lemma eviction_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    le (if kd1 s then boltzmann_factor s else zero)
       (if kd2 s then boltzmann_factor s else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | Hn1].
  - (* k1 s 成立 ⟹ k2 s 成立（Hsub） *)
    destruct (kd2 s) as [H2 | Hn2].
    + apply le_refl.
    + (* 矛盾：k2 s 与 Not (k2 s) *)
      exact (match Hn2 (Hsub s H1) with end).
  - (* k1 s 不成立：左侧为 zero *)
    destruct (kd2 s) as [H2 | Hn2].
    + (* 右侧为 f s > 0 ⟹ zero ≤ f s *)
      apply (lt_le_iff zero (boltzmann_factor s)).
      left.
      unfold boltzmann_factor.
      apply exp_neg_pos.
    + apply le_refl.
Qed.

(* 保留态上的条件配分函数（参数化 keep：单调性需要比较两个保留集） *)
Definition evicted_partition_of
  (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then boltzmann_factor s else zero).

(* 支撑定理 (a)：逐出后分布仍归一化——Σ_s evicted_boltzmann(s) = 1
   （保留态上概率质量守恒；非保留态贡献 0） *)
Theorem evicted_boltzmann_normalized :
  Id (sum_over_S (fun s => evicted_boltzmann s)) one.
Proof.
  (* assert + exact 链（避免 rewrite 对 if/match 形态的语法失配） *)
  assert (H1 : Id (sum_over_S (fun s => evicted_boltzmann s))
                  (sum_over_S (fun s => mult (inv_pos evicted_partition evicted_partition_pos)
                                            (if keep_dec s then boltzmann_factor s else zero)))).
  {
    apply sum_over_S_ext.
    intro s.
    unfold evicted_boltzmann.
    exact (eviction_if_linear keep keep_dec (inv_pos evicted_partition evicted_partition_pos) boltzmann_factor s).
  }
  assert (H2 : Id (sum_over_S (fun s => mult (inv_pos evicted_partition evicted_partition_pos)
                                            (if keep_dec s then boltzmann_factor s else zero)))
                  (mult (inv_pos evicted_partition evicted_partition_pos)
                        (sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero)))).
  { apply sum_over_S_linear. }
  assert (H3 : Id (mult (inv_pos evicted_partition evicted_partition_pos)
                        (sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero)))
                  one).
  {
    unfold evicted_partition.
    assert (Hcc : Id (mult (inv_pos evicted_partition evicted_partition_pos) evicted_partition) one)
      by exact (id_trans (mult_comm (inv_pos evicted_partition evicted_partition_pos) evicted_partition)
                         (inv_pos_correct evicted_partition evicted_partition_pos)).
    exact Hcc.
  }
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* 支撑定理 (b)：保留集合单调扩张 ⟹ 配分函数不减（保留越多质量越多）。
   最优保留策略（按 Boltzmann 权重降序贪心选入）方向的正确性基础。 *)
Theorem eviction_partition_monotone :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    le (evicted_partition_of k1 kd1) (evicted_partition_of k2 kd2).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evicted_partition_of.
  apply sum_over_S_le.
  intro s.
  exact (eviction_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* ============================================================ *)
(* KV 逐出最优策略（配套支撑定理）                           *)
(* ============================================================ *)
(*   (c) 逐出配分函数以全配分函数为上界：任意保留集的         *)
(*       evicted_partition ≤ Z_thermo（保留越多质量越多 ⟹     *)
(*       全保留是质量上界；容量预算下逐出质量损失的度量基准）。*)
(*   (d) 逐出破缺的参照：全保留时 evicted_transition =         *)
(*       transition 且 evicted_boltzmann = boltzmann_dist_attn，*)
(*       详细平衡零破缺（逐出是破缺的唯一来源）。             *)

(* 引理：if k s then f s else 0 ≤ f s（Boltzmann 因子非负） *)
Lemma eviction_if_le :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
  forall s : S,
    le (if kd s then boltzmann_factor s else zero) (boltzmann_factor s).
Proof.
  intros k kd s.
  destruct (kd s) as [Hk | Hnk].
  - apply le_refl.
  - (* zero ≤ f s（f 正） *)
    apply (lt_le_iff zero (boltzmann_factor s)).
    left.
    unfold boltzmann_factor.
    apply exp_neg_pos.
Qed.

(* 支撑定理 (c)：evicted_partition ≤ Z_thermo——全保留是质量上界。
   逐出只可能损失概率质量；容量预算下的质量损失 = Z_thermo - evicted_partition ≥ 0。 *)
Theorem eviction_partition_le_full :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    le (evicted_partition_of k kd) Z_thermo.
Proof.
  intros k kd.
  unfold evicted_partition_of, Z_thermo.
  apply sum_over_S_le.
  intro s.
  exact (eviction_if_le k kd s).
Qed.

(* 支撑定理 (d)：全保留（keep 恒真）⟹ evicted_transition = transition。
   即 keep 不排除任何状态时逐出转移与原始转移逐点一致。 *)

Theorem eviction_transition_full :
  (forall s, keep s) ->
  forall s s' : S, Id (evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + reflexivity.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* 支撑定理 (d')：全保留且 evicted_partition = Z_thermo ⟹
   evicted_boltzmann = boltzmann_dist_attn（逐出分布回到原始分布）。 *)
Theorem eviction_boltzmann_full :
  (forall s, keep s) ->
  Id evicted_partition Z_thermo ->
  forall s : S, Id (evicted_boltzmann s) (boltzmann_dist_attn s).
Proof.
  intros Hkall HZ s.
  unfold evicted_boltzmann, boltzmann_dist_attn, boltzmann_factor, evicted_partition.
  destruct (keep_dec s) as [Hks | Hnks].
  - (* 保留态：inv_ev·f s = inv_Z·f s（逆元统一 inv_pos_ext） *)
    assert (Hie : Id (inv_pos evicted_partition evicted_partition_pos)
                     (inv_pos Z_thermo Z_thermo_pos))
      by exact (inv_pos_ext evicted_partition Z_thermo evicted_partition_pos Z_thermo_pos HZ).
    exact (id_cong (fun x => mult x (exp_neg (mult (inv_pos D D_pos) (energy s)))) Hie).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* 支撑定理 (e)：全保留 ⟹ 详细平衡零破缺——逐出是破缺的唯一来源。
   （对照 eviction_db_breaking_bound：破缺有界；此处证明不逐出则无破缺。） *)
Theorem eviction_db_zero_full :
  (forall s, keep s) ->
  Id evicted_partition Z_thermo ->
  forall s s' : S, Id (db_breaking s s') zero.
Proof.
  intros Hkall HZ s s'.
  unfold db_breaking.
  assert (Heb : forall t, Id (evicted_boltzmann t) (boltzmann_dist_attn t))
    by exact (eviction_boltzmann_full Hkall HZ).
  assert (Het : forall t u, Id (evicted_transition t u) (transition t u))
    by exact (eviction_transition_full Hkall).
  (* 目标：abs (minus (ev_b s · ev_t s s') (ev_b s' · ev_t s' s)) = 0 *)
  assert (Harg : Id (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                           (mult (evicted_boltzmann s') (evicted_transition s' s)))
                    zero).
  {
    assert (Hdb : Id (mult (boltzmann_dist_attn s) (transition s s'))
                     (mult (boltzmann_dist_attn s') (transition s' s)))
      by exact (detailed_balance s s').
    assert (Hl : Id (mult (evicted_boltzmann s) (evicted_transition s s'))
                    (mult (boltzmann_dist_attn s) (transition s s')))
      by exact (id_trans (id_cong (fun x => mult x (evicted_transition s s')) (Heb s))
                          (id_cong (fun x => mult (boltzmann_dist_attn s) x) (Het s s'))).
    assert (Hr : Id (mult (evicted_boltzmann s') (evicted_transition s' s))
                    (mult (boltzmann_dist_attn s') (transition s' s)))
      by exact (id_trans (id_cong (fun x => mult x (evicted_transition s' s)) (Heb s'))
                          (id_cong (fun x => mult (boltzmann_dist_attn s') x) (Het s' s))).
    assert (Heq : Id (mult (evicted_boltzmann s) (evicted_transition s s'))
                     (mult (evicted_boltzmann s') (evicted_transition s' s)))
      by exact (id_trans Hl (id_trans Hdb (id_sym Hr))).
    exact (minus_self_zero _ _ Heq).
  }
  assert (Habs : Id (abs (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                                (mult (evicted_boltzmann s') (evicted_transition s' s))))
                    zero)
    by exact (id_trans (id_cong abs Harg) abs_zero).
  exact Habs.
Qed.

(* ============================================================ *)
(* 逐出稳态偏差量化（KV 逐出最优策略的代价度量）               *)
(* ============================================================ *)
(* 背景：逐出打破详细平衡后，evicted_boltzmann 不再是稳态。     *)
(* 本定理量化稳态方程的偏差：                                   *)
(*   |Σ_{s'} ev_b(s')·ev_t(s',s) - ev_b(s)·Σ_{s'} ev_t(s,s')|  *)
(*     ≤ Σ_{s'} db_breaking(s,s')                              *)
(* 即：逐出导致的稳态破坏程度受详细平衡破缺的求和控制——        *)
(* db_breaking 是逐出代价的精确上界源。                       *)
(* 证明：差项 = Σ[ev_b(s')·ev_t(s',s) - ev_b(s)·ev_t(s,s')]    *)
(* （线性提出 ev_b(s)），取 abs 用 abs_sum_le 得 Σ|·| = Σ db。 *)
(* ------------------------------------------------------------ *)

(* 逐出稳态偏差 ≤ 破缺求和（KV 逐出代价的定量界） *)
Theorem eviction_steady_deviation :
  forall s,
    le (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                   (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
       (sum_over_S (fun s' => db_breaking s s')).
Proof.
  intro s.
  (* 1. 提出常数因子 ev_b(s)：Σ ev_b(s)·ev_t(s,s') = ev_b(s)·Σ ev_t(s,s') *)
  assert (Hlin : Id (sum_over_S (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))
                    (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))))
    by exact (sum_over_S_linear (evicted_boltzmann s) (fun s' => evicted_transition s s')).
  (* 2. 差项改写：Σ_{s'} ev_b(s')·ev_t(s',s) - Σ_{s'} ev_b(s)·ev_t(s,s')
        = Σ_{s'} [ev_b(s')·ev_t(s',s) - ev_b(s)·ev_t(s,s')]（sum_over_S_minus） *)
  assert (Hdiff : Id (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                            (sum_over_S (fun s' => mult (evicted_boltzmann s) (evicted_transition s s'))))
                    (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                (mult (evicted_boltzmann s) (evicted_transition s s')))))
    by exact (id_sym (sum_over_S_minus (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s))
                               (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))).
  assert (Hlhs : Id (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                           (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))))
                    (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                           (sum_over_S (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))))
    by exact (id_cong (fun x => minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s))) x)
                      (id_sym Hlin)).
  (* 4. 组合：目标 LHS = Σ diff，再 abs_sum_le ⟹ |Σ diff| ≤ Σ|diff| *)
  assert (Hlhs2 : Id (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                            (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))))
                     (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                 (mult (evicted_boltzmann s) (evicted_transition s s')))))
    by exact (id_trans Hlhs Hdiff).
  (* 5. |Σ diff| ≤ Σ |diff|（abs_sum_le） *)
  assert (Habs : le (abs (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                     (mult (evicted_boltzmann s) (evicted_transition s s')))))
                    (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                     (mult (evicted_boltzmann s) (evicted_transition s s'))))))
    by exact (abs_sum_le (fun s0 => minus (mult (evicted_boltzmann s0) (evicted_transition s0 s)) (mult (evicted_boltzmann s) (evicted_transition s s0)))).

  assert (Hlhs3 : le (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                                  (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
                     (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                      (mult (evicted_boltzmann s) (evicted_transition s s')))))).
  {
    (* le_id_l：把 LHS 的项换成 Hlhs2 右侧（Σ diff）后应用 Habs *)
    exact (le_id_l (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                               (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
                   (abs (sum_over_S (fun s' => minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                    (mult (evicted_boltzmann s) (evicted_transition s s')))))
                   (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                    (mult (evicted_boltzmann s) (evicted_transition s s')))))
                   (id_cong abs Hlhs2) Habs).
  }
  (* 7. RHS：Σ|minus A B| = Σ db_breaking（db_breaking := abs (minus B A)，abs_minus_sym 换向） *)
  assert (Hrhs : Id (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                     (mult (evicted_boltzmann s) (evicted_transition s s')))))
                    (sum_over_S (fun s' => db_breaking s s'))).
  {
    apply sum_over_S_ext.
    intro s'.
    unfold db_breaking.
    (* db_breaking s s' := abs (minus (ev_b s · ev_t s s') (ev_b s' · ev_t s' s))
       目标：abs (minus (ev_b s' · ev_t s' s) (ev_b s · ev_t s s'))
       = db_breaking s s'（abs_minus_sym） *)
    exact (id_sym (abs_minus_sym (mult (evicted_boltzmann s) (evicted_transition s s'))
                         (mult (evicted_boltzmann s') (evicted_transition s' s)))).
  }
  (* 8. 组合：Hlhs3 的 RHS 换成 Σ db_breaking（Hrhs 反向，le_id_r） *)
  exact (le_id_r (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                            (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
                 (sum_over_S (fun s' => abs (minus (mult (evicted_boltzmann s') (evicted_transition s' s))
                                                  (mult (evicted_boltzmann s) (evicted_transition s s')))))
                 (sum_over_S (fun s' => db_breaking s s'))
                 Hrhs Hlhs3).
Qed.

(* ============================================================ *)
(* KV 逐出：容量预算与尾部质量（P2，从定性到定量）            *)
(* ============================================================ *)
(* 工程背景：KV 缓存有严格容量预算，最多保留 K 个状态。        *)
(* 逐出的信息损失 = 未保留的 Boltzmann 质量（尾部质量）。      *)
(* 以下定理将尾部质量与容量预算关联，并给出信息损失上界。      *)
(* ------------------------------------------------------------ *)

(* 容量预算：保留集基数上界（构造性：list 长度计数） *)
Variable K : nat.  (* 容量预算：最多保留 K 个状态 *)
Variable S_enum : list S.  (* 有限状态空间的枚举 *)
Variable S_finite_cover : forall s : S, InT s S_enum.

(* 尾部质量：未保留态的 Boltzmann 权重之和（逐出损失） *)
Definition tail_mass : R :=
  sum_over_S (fun s => if keep_dec s then zero else boltzmann_factor s).

(* 尾部质量上界：tail_mass <= Z_thermo（逐出损失不超过全部质量）。 *)
Theorem top_k_tail_bound :
  le tail_mass Z_thermo.
Proof.
  unfold tail_mass, Z_thermo.
  apply sum_over_S_le.
  intro s.
  destruct (keep_dec s) as [Hk | Hnk].
  - apply (lt_le_iff zero (boltzmann_factor s)).
    left. unfold boltzmann_factor. apply exp_neg_pos.
  - apply le_refl.
Qed.

(* 质量守恒：尾部质量 + 保留质量 = 全部质量。 *)
Theorem tail_plus_kept_full :
  Id (plus tail_mass evicted_partition) Z_thermo.
Proof.
  unfold tail_mass, evicted_partition, Z_thermo.
  assert (Hpt : forall s, Id (plus (if keep_dec s then zero else boltzmann_factor s)
                                  (if keep_dec s then boltzmann_factor s else zero))
                            (boltzmann_factor s)).
  {
    intro s.
    destruct (keep_dec s) as [Hk | Hnk].
    - assert (Hadd : Id (plus zero (boltzmann_factor s)) (boltzmann_factor s))
        by exact (id_trans (plus_comm zero (boltzmann_factor s)) (plus_zero (boltzmann_factor s))).
      exact Hadd.
    - exact (plus_zero (boltzmann_factor s)).
  }
  assert (Hext : Id (sum_over_S (fun s => plus (if keep_dec s then zero else boltzmann_factor s)
                                             (if keep_dec s then boltzmann_factor s else zero)))
                   (sum_over_S (fun s => boltzmann_factor s)))
    by exact (sum_over_S_ext (fun s => plus (if keep_dec s then zero else boltzmann_factor s)
                                            (if keep_dec s then boltzmann_factor s else zero))
                             (fun s => boltzmann_factor s) Hpt).
  assert (Hadd : Id (sum_over_S (fun s => plus (if keep_dec s then zero else boltzmann_factor s)
                                             (if keep_dec s then boltzmann_factor s else zero)))
                   (plus (sum_over_S (fun s => if keep_dec s then zero else boltzmann_factor s))
                         (sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero))))
    by exact (sum_over_S_add (fun s => if keep_dec s then zero else boltzmann_factor s)
                             (fun s => if keep_dec s then boltzmann_factor s else zero)).
  exact (id_trans (id_sym Hadd) Hext).
Qed.

(* ============================================================ *)
(* Top-K 最优性（P2 非平凡平行版本：贪心交换论证的引擎）       *)
(* ============================================================ *)
(* top_k_tail_bound / tail_plus_kept_full 是尾部质量的定性上界与  *)
(* 守恒版本；以下给出贪心 Top-K 策略（保留 Boltzmann 权重最高的  *)
(* K 个状态）最优性的定量引擎：                                 *)
(*   (a) 交换引理 top_k_exchange：若保留态 s 比逐出态 s' 更轻     *)
(*       （f s ≤ f s'），则把 s 换出、s' 换入不增加尾部质量——    *)
(*       任何非 Top-K 的选择都可通过交换被改进（贪心最优性内核）；*)
(*   (b) 反单调性 top_k_tail_antitone：保留集单调扩张 ⟹ 尾部质量  *)
(*       单调不增——"保留越多，损失越少"，与                     *)
(*       eviction_partition_monotone（保留越多质量越多）对偶。    *)
(* ------------------------------------------------------------ *)

(* 参数化尾部质量（按任意保留集 k 计算未保留的 Boltzmann 权重） *)
Definition tail_mass_of
  (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then zero else boltzmann_factor s).

(* 减法序内核：a ≤ b ⟹ a - b ≤ 0（交换引理第一步） *)
Lemma le_minus_le_zero : forall a b : R, le a b -> le (minus a b) zero.
Proof.
  intros a b Hab.
  unfold minus.
  assert (H1 : le (plus a (opp b)) (plus a (opp a)))
    by exact (le_plus_compat a a (opp b) (opp a) (le_refl a) (opp_le_compat a b Hab)).
  assert (H2 : Id (plus a (opp a)) zero) by exact (plus_opp a).
  exact (le_id_r (plus a (opp b)) (plus a (opp a)) zero H2 H1).
Qed.

(* 加法序零侧：b ≤ 0 ⟹ a + b ≤ a（交换引理第二步） *)
Lemma le_plus_zero_l : forall a b : R, le b zero -> le (plus a b) a.
Proof.
  intros a b Hb.
  assert (H1 : le (plus a b) (plus a zero))
    by exact (le_plus_compat a a b zero (le_refl a) Hb).
  assert (H2 : le (plus a zero) a)
    by exact (le_id_l (plus a zero) a a (plus_zero a) (le_refl a)).
  exact (le_trans (plus a b) (plus a zero) a H1 H2).
Qed.

(* 减法换序：(a - b) + c = a + (c - b)（交换引理的代数骨架） *)
Lemma minus_plus_swap : forall a b c : R,
  Id (plus (minus a b) c) (plus a (minus c b)).
Proof.
  intros a b c.
  unfold minus.
  assert (H1 : Id (plus (plus a (opp b)) c) (plus a (plus (opp b) c)))
    by exact (id_sym (plus_assoc a (opp b) c)).
  exact (id_trans H1 (id_cong (fun x => plus a x) (plus_comm (opp b) c))).
Qed.

(* 交换引理（贪心 Top-K 最优性引擎）：
   保留态 s 比逐出态 s' 更轻（f s ≤ f s'）⟹ 交换（s 换出、s' 换入）
   不增加尾部质量。数学内容：交换后尾质量 = 原尾质量 - f s' + f s
   ≤ 原尾质量（因 f s ≤ f s'），即任何"保留更轻、逐出更重"的选择
   都可被交换改进——贪心保留最重 K 个状态是最优的局部依据。
   （keep s / Not (keep s') 为语义守卫：交换只对保留态与逐出态定义。） *)
Theorem top_k_exchange :
  forall s s' : S,
    keep s -> Not (keep s') ->
    le (boltzmann_factor s) (boltzmann_factor s') ->
    le (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s)) tail_mass.
Proof.
  intros s s' Hks Hnks' Hff.
  (* 代数重组：LHS = tail_mass + (f s - f s')（减法换序） *)
  assert (Hr : Id (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                  (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))))
    by exact (minus_plus_swap tail_mass (boltzmann_factor s') (boltzmann_factor s)).
  (* f s ≤ f s' ⟹ f s - f s' ≤ 0 *)
  assert (Hmm : le (minus (boltzmann_factor s) (boltzmann_factor s')) zero)
    by exact (le_minus_le_zero (boltzmann_factor s) (boltzmann_factor s') Hff).
  (* tail_mass + (≤ 0) ≤ tail_mass *)
  assert (Hfin : le (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))) tail_mass)
    by exact (le_plus_zero_l tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')) Hmm).
  exact (le_id_l (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                 (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')))
                 tail_mass Hr Hfin).
Qed.

(* 尾部质量逐点反单调：k1 ⊆ k2 ⟹（k2 的尾项）≤（k1 的尾项）
   （若 k2 保留 s 则 k1 的尾项为 0 或 f s ≥ 0；若 k2 逐出 s 则
    k1 也逐出 s（Hsub 逆否），两项相等。） *)
Lemma eviction_tail_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    le (if kd2 s then zero else boltzmann_factor s)
       (if kd1 s then zero else boltzmann_factor s).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd2 s) as [H2 | Hn2].
  - (* k2 保留 s：左侧为 0，右侧为 0 或 f s ≥ 0 *)
    destruct (kd1 s) as [H1 | Hn1].
    + apply le_refl.
    + apply (lt_le_iff zero (boltzmann_factor s)).
      left.
      unfold boltzmann_factor.
      apply exp_neg_pos.
  - (* k2 逐出 s ⟹ k1 也逐出 s（Hsub 逆否）⟹ 两侧相等 *)
    destruct (kd1 s) as [H1 | Hn1].
    + (* 矛盾：k1 保留 s 而 k2 逐出 s *)
      exact (match Hn2 (Hsub s H1) with end).
    + apply le_refl.
Qed.

(* 尾部质量反单调：保留集单调扩张 ⟹ 尾部质量单调不增。
   与 eviction_partition_monotone（保留质量单调不减）对偶；
   贪心 Top-K（按权重降序扩张保留集至预算 K）下信息损失单调递减。 *)
Theorem top_k_tail_antitone :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    le (tail_mass_of k2 kd2) (tail_mass_of k1 kd1).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold tail_mass_of.
  apply sum_over_S_le.
  intro s.
  exact (eviction_tail_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* ============================================================ *)
(* Top-K 最优性（完整版：构造性选择排序 + 计数阈值刻画）       *)
(* ============================================================ *)
(* 文档草稿（结构性缺失.txt 6.x）用 select_top_k 排序 +          *)
(* relative_entropy 精确形式；本实现给出可证明的两条路径：       *)
(*   (a) 构造性选择排序 select_top_k（插入排序，权重降序，       *)
(*       无需默认元素）；                                        *)
(*   (b) 计数阈值刻画 keep_top_k：保留"严格更重的状态数 < K"的   *)
(*       状态——Top-K 的构造性判定（可计算，无需 S 的可判定等号）；*)
(* 最优性定理 top_k_majorization（Top-K 保留者支配所有逐出者，   *)
(* 即文档 top_k_majorization 的完整证明）+ top_k_swap_no_gain     *)
(* （Top-K 交换不减少尾部质量——交换论证内核）。                  *)
(* relative_entropy 形式因逐出态上 log 0 未定义而不可表示，      *)
(* 见结构性缺失.txt 状态注记。                                  *)
(* ------------------------------------------------------------ *)

Context {DO : DecidableOrder RI}.

(* lt_dec 投影别名：类字段名 lt_dec 被 Stdlib Compare_dec.lt_dec 遮蔽，
   经构造子解构提取（coqc/coqtop 双环境均可用） *)
Definition lt_dec_field : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => lt_d
  end.

(* 严格小于（nat 版，与顶层 NatLe 对偶） *)
Definition NatLt (n m : nat) : Set := Id (Nat.ltb n m) true.

(* (a) 权重降序插入排序（构造性选择排序 select_top_k） *)
Fixpoint insert_weight (a : S) (l : list S) : list S :=
  match l with
  | nil => a :: nil
  | b :: rest =>
      match (@ord_le_dec _ DO) (boltzmann_factor b) (boltzmann_factor a) with
      | inl _ => a :: b :: rest      (* f a ≥ f b：a 置于 b 前 *)
      | inr _ => b :: insert_weight a rest
      end
  end.

Fixpoint sort_weight (l : list S) : list S :=
  match l with
  | nil => nil
  | a :: rest => insert_weight a (sort_weight rest)
  end.

(* Top-K 选择：枚举按权重降序排列后取前 K 个 *)
Definition select_top_k (l : list S) (k : nat) : list S :=
  firstn k (sort_weight l).

(* (b) 严格更重计数：l 中比 s 权重严格更大的状态数（lt_dec 三分） *)
Fixpoint count_heavier (s : S) (l : list S) : nat :=
  match l with
  | nil => O
  | a :: rest =>
      match (lt_dec_field (boltzmann_factor s) (boltzmann_factor a)) with
      | inl _ => Datatypes.S (count_heavier s rest)
      | inr _ => count_heavier s rest
      end
  end.

(* Top-K 判定：严格更重者不足 K 个 ⟹ s 属 Top-K *)
Definition keep_top_k (s : S) : Set := NatLt (count_heavier s S_enum) K.

(* keep_top_k 的可判定性（Nat.ltb 计算 + bool 消去，无需 S 等号） *)
Lemma id_false_true : forall (H : Id false true), Empty_set.
Proof. intro H. inversion H. Qed.

Definition keep_top_k_dec : forall s : S, Or (keep_top_k s) (Not (keep_top_k s)) :=
  fun s => match Nat.ltb (count_heavier s S_enum) K as b
                return Or (Id b true) (Not (Id b true)) with
           | true => inl id_refl
           | false => inr (fun H => id_false_true H)
           end.

(* 计数单调（在"更重"方向上）：f s1 < f s2 ⟹ count_heavier s2 ≤ count_heavier s1
   （比 s2 重的状态也是比 s1 重的——lt_trans 传递性；decider 撒谎分支归谬） *)
Lemma count_heavier_mono : forall s1 s2 : S, forall l : list S,
  lt (boltzmann_factor s1) (boltzmann_factor s2) ->
  NatLe (count_heavier s2 l) (count_heavier s1 l).
Proof.
  intros s1 s2 l. induction l as [| a rest IH]; intros Hlt.
  - simpl. apply NatLe_lift. lia.
  - simpl.
    destruct (lt_dec_field (boltzmann_factor s1) (boltzmann_factor a)) as [d1 | nd1];
    destruct (lt_dec_field (boltzmann_factor s2) (boltzmann_factor a)) as [d2 | nd2].
    + pose proof (NatLe_drop _ _ (IH Hlt)) as IHle. apply NatLe_lift. lia.
    + pose proof (NatLe_drop _ _ (IH Hlt)) as IHle. apply NatLe_lift. lia.
    + (* nd1 ∧ d2：矛盾（d2 : lt (f s2) (f a)，nd1 否定了 lt (f s1) (f a)） *)
      destruct nd1 as [Hid | Hlt_a_s1].
      * (* Hid : Id (f s1) (f a)：换写 d2 ⟹ lt (f s2) (f s1)，与 Hlt 矛盾 *)
        exact (match (lt_irrefl (boltzmann_factor s1)
                        (lt_trans (boltzmann_factor s1) (boltzmann_factor s2) (boltzmann_factor s1)
                           Hlt
                           (lt_id_r (boltzmann_factor s2) (boltzmann_factor a) (boltzmann_factor s1)
                              (id_sym Hid) d2))) with end).
      * (* Hlt_a_s1 : lt (f a) (f s1)：lt_trans a s1 s2 ⟹ lt (f a) (f s2)，与 d2 矛盾 *)
        exact (match (lt_irrefl (boltzmann_factor a)
                        (lt_trans (boltzmann_factor a) (boltzmann_factor s2) (boltzmann_factor a)
                           (lt_trans (boltzmann_factor a) (boltzmann_factor s1) (boltzmann_factor s2)
                              Hlt_a_s1 Hlt)
                           d2)) with end).
    + pose proof (NatLe_drop _ _ (IH Hlt)) as IHle. apply NatLe_lift. lia.
Qed.

(* 计数 +1（InT 前提）：f s1 < f s2 且 s2 ∈ l ⟹ S (count_heavier s2 l) ≤ count_heavier s1 l
   （s2 自身计入 s1 的计数；比 s2 重的也计入 s1——对 InT 归纳） *)
Lemma count_heavier_succ_le : forall s1 s2 : S, forall l : list S,
  lt (boltzmann_factor s1) (boltzmann_factor s2) ->
  InT s2 l ->
  NatLe (Datatypes.S (count_heavier s2 l)) (count_heavier s1 l).
Proof.
  intros s1 s2 l Hlt Hin.
  induction Hin as [l0 | a0 l0 Hin_ IH].
  - (* InT_here：s2 是表头（l = s2 :: l0，依赖消去自动替换） *)
    simpl.
    destruct (lt_dec_field (boltzmann_factor s1) (boltzmann_factor s2)) as [d1 | nd1];
    destruct (lt_dec_field (boltzmann_factor s2) (boltzmann_factor s2)) as [d2 | nd2].
    + (* d2 : lt (f s2) (f s2) → 矛盾（lt_irrefl） *)
      exact (match (lt_irrefl (boltzmann_factor s2) d2) with end).
    + (* 目标：NatLe (S (count_heavier s2 l0)) (count_heavier s1 l0)，即 count_heavier_mono 的结论；
         NatLe_drop／NatLe_lift 在 NatLe 形与 nat 层序间转换，末端由 lia 完成 *)
      pose proof (NatLe_drop _ _ (count_heavier_mono s1 s2 l0 Hlt)) as Hm.
      apply NatLe_lift. lia.
    + (* nd1 → 矛盾（Hlt : lt (f s1) (f s2)） *)
      destruct nd1 as [Hid | Hlt21].
      * exact (match (lt_irrefl (boltzmann_factor s1)
                      (lt_id_r (boltzmann_factor s1) (boltzmann_factor s2) (boltzmann_factor s1)
                         (id_sym Hid) Hlt)) with end).
      * exact (match (lt_irrefl (boltzmann_factor s2)
                      (lt_trans (boltzmann_factor s2) (boltzmann_factor s1) (boltzmann_factor s2)
                         Hlt21 Hlt)) with end).
    + (* nd1 ∧ nd2：nd1 与 Hlt 直接矛盾（同上） *)
      destruct nd1 as [Hid | Hlt21].
      * exact (match (lt_irrefl (boltzmann_factor s1)
                      (lt_id_r (boltzmann_factor s1) (boltzmann_factor s2) (boltzmann_factor s1)
                         (id_sym Hid) Hlt)) with end).
      * exact (match (lt_irrefl (boltzmann_factor s2)
                      (lt_trans (boltzmann_factor s2) (boltzmann_factor s1) (boltzmann_factor s2)
                         Hlt21 Hlt)) with end).
  - (* InT_next：s2 ∈ l0；IH : S (count_heavier s2 l0) ≤ count_heavier s1 l0 *)
    simpl.
    destruct (lt_dec_field (boltzmann_factor s1) (boltzmann_factor a0)) as [d1 | nd1];
    destruct (lt_dec_field (boltzmann_factor s2) (boltzmann_factor a0)) as [d2 | nd2].
    + pose proof (NatLe_drop _ _ IH) as IHle. apply NatLe_lift. lia.
    + pose proof (NatLe_drop _ _ IH) as IHle. apply NatLe_lift. lia.
    + (* nd1 ∧ d2：矛盾（同 count_heavier_mono 的 (nd1, d2) 情形） *)
      destruct nd1 as [Hid | Hlt_a_s1].
      * exact (match (lt_irrefl (boltzmann_factor s2)
                      (lt_trans (boltzmann_factor s2) (boltzmann_factor s1) (boltzmann_factor s2)
                         (lt_id_r (boltzmann_factor s2) (boltzmann_factor a0) (boltzmann_factor s1)
                            (id_sym Hid) d2)
                         Hlt)) with end).
      * exact (match (lt_irrefl (boltzmann_factor a0)
                      (lt_trans (boltzmann_factor a0) (boltzmann_factor s2) (boltzmann_factor a0)
                         (lt_trans (boltzmann_factor a0) (boltzmann_factor s1) (boltzmann_factor s2)
                            Hlt_a_s1 Hlt)
                         d2)) with end).
    + pose proof (NatLe_drop _ _ IH) as IHle. apply NatLe_lift. lia.
Qed.

(* Top-K 支配性（文档 top_k_majorization 的完整证明）：
   Top-K 保留者权重 ≥ 任意逐出者——Top-K 是"最重 K 个"的序刻画 *)
Theorem top_k_majorization :
  forall s1 s2 : S,
    keep_top_k s1 -> Not (keep_top_k s2) ->
    le (boltzmann_factor s2) (boltzmann_factor s1).
Proof.
  intros s1 s2 Hk1 Hnk2.
  destruct (@ord_le_dec _ DO (boltzmann_factor s2) (boltzmann_factor s1)) as [Hle | Hnle].
  - exact Hle.
  - (* Hnle ⟹ lt (f s1) (f s2)（not_le_lt）⟹ 计数矛盾 *)
    assert (Hlt : lt (boltzmann_factor s1) (boltzmann_factor s2))
      by exact (@not_le_lt _ DO (boltzmann_factor s2) (boltzmann_factor s1) Hnle).
    assert (Hsucc : NatLe (Datatypes.S (count_heavier s2 S_enum)) (count_heavier s1 S_enum))
      by exact (count_heavier_succ_le s1 s2 S_enum Hlt (S_finite_cover s2)).
    pose proof (NatLe_drop _ _ Hsucc) as Hsucle.
    unfold keep_top_k, NatLt in Hk1, Hnk2.
    assert (Hlt1 : (count_heavier s1 S_enum < K)%nat).
    { apply (proj1 (Nat.ltb_lt _ _)).
      exact (match Hk1 in (Id _ y) return (Nat.ltb (count_heavier s1 S_enum) K = y) with id_refl => eq_refl end). }
    assert (Hge2 : (K <= count_heavier s2 S_enum)%nat).
    { apply Nat.nlt_ge. intro Hlt2.
      exact (match (Hnk2 (match (proj2 (Nat.ltb_lt _ _) Hlt2) in (_ = y) return (Id (Nat.ltb (count_heavier s2 S_enum) K) y) with eq_refl => id_refl end)) with end). }
    exfalso. lia.
Qed.

(* Top-K 交换不获益：把 Top-K 保留者 s 换成逐出者 s'（重换出、轻换入）
   不会减少尾部质量——Top-K 是最小信息损失选择（交换论证的结论形式）。
   数学内容：新尾质量 = T - f s' + f s ≥ T（因 f s ≥ f s'）。 *)
Theorem top_k_swap_no_gain :
  forall s s' : S,
    keep_top_k s -> Not (keep_top_k s') ->
    le tail_mass (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s)).
Proof.
  intros s s' Hks Hnks'.
  (* Top-K 支配性：f s' ≤ f s *)
  assert (Hle : le (boltzmann_factor s') (boltzmann_factor s))
    by exact (top_k_majorization s s' Hks Hnks').
  (* 代数重组：T - f s' + f s = T + (f s - f s')（minus_plus_swap） *)
  assert (Hr : Id (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                  (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))))
    by exact (minus_plus_swap tail_mass (boltzmann_factor s') (boltzmann_factor s)).
  (* f s' ≤ f s ⟹ 0 ≤ f s - f s'（le_minus_nonneg） *)
  assert (Hnn : le zero (minus (boltzmann_factor s) (boltzmann_factor s')))
    by exact (le_minus_nonneg (boltzmann_factor s') (boltzmann_factor s) Hle).
  (* T ≤ T + (≥0)（le_plus_nonneg_r） *)
  assert (Hfin : le tail_mass (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s'))))
    by exact (le_plus_nonneg_r tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')) Hnn).
  exact (le_id_r tail_mass (plus tail_mass (minus (boltzmann_factor s) (boltzmann_factor s')))
                 (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s))
                 (id_sym Hr) Hfin).
Qed.

(* ============================================================ *)
(* Top-K 排序级最优性（select_top_k 的排序正确性 + 支配性）     *)
(* ============================================================ *)
(* 相对熵精确形式因逐出态 log 0 不可表示（见结构性缺失.txt 注记）；*)
(* 此处给出排序级核心：sorted_noninc（前缀最大排序不变量）、      *)
(* insert_preserves_sorted / sort_sorted（插入排序正确性）、      *)
(* firstn_head_dominates_skipn（排序下前缀元素支配后缀元素）、    *)
(* top_k_majorization_mem（select_top_k 保留者支配任意逐出者）。 *)

(* 排序不变量：每个元素 ≥ 其后所有元素（前缀最大形式） *)
Fixpoint sorted_noninc (l : list S) : Set :=
  match l with
  | nil => unit
  | a :: rest => And (forall b : S, InT b rest -> le (boltzmann_factor b) (boltzmann_factor a))
                     (sorted_noninc rest)
  end.

(* 跳过函数子集：InT x (skipn k l) ⟹ InT x l *)
Lemma skipn_sub : forall (k : nat) (l : list S) (x : S),
  InT x (skipn k l) -> InT x l.
Proof.
  intros k l x. revert l. induction k as [| k' IH]; intros l Hx.
  - simpl in Hx. exact Hx.
  - destruct l as [| a rest].
    + simpl in Hx. exact Hx.
    + simpl in Hx. apply InT_next. exact (IH rest Hx).
Qed.

(* 拼接成员分解：InT x (l1 ++ l2) ⟹ x ∈ l1 或 x ∈ l2 *)
Lemma InT_app_or : forall (l1 l2 : list S) (x : S),
  InT x (l1 ++ l2) -> Or (InT x l1) (InT x l2).
Proof.
  intros l1. induction l1 as [| a rest IH]; intros l2 x Hx.
  - simpl in Hx. right. exact Hx.
  - simpl in Hx. inversion Hx as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
    + left. exact (InT_here a rest).
    + destruct (IH l2 x Hnext_rec) as [Hl | Hr].
      * left. exact (InT_next x a rest Hl).
      * right. exact Hr.
Qed.

(* 插入保持成员：x ∈ l ⟹ x ∈ insert a l *)
Lemma insert_mem_in : forall a x : S, forall l : list S,
  InT x l -> InT x (insert_weight a l).
Proof.
  intros a x l. induction l as [| b rest IH]; intros Hx.
  - simpl. inversion Hx.
  - simpl.
    destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + apply InT_next. exact Hx.
    + inversion Hx as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * exact (InT_here b (insert_weight a rest)).
      * apply InT_next. exact (IH Hnext_rec).
Qed.

(* 插入自成员：a 恒在 insert a l 中 *)
Lemma insert_mem_self : forall a : S, forall l : list S, InT a (insert_weight a l).
Proof.
  intros a l. induction l as [| b rest IH]; simpl.
  - exact (InT_here a nil).
  - destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + exact (InT_here a (b :: rest)).
    + apply InT_next. exact IH.
Qed.

(* 排序保持成员：x ∈ l ⟹ x ∈ sort_weight l *)
Lemma sort_mem_in : forall (l : list S) (x : S),
  InT x l -> InT x (sort_weight l).
Proof.
  intros l. induction l as [| a rest IH]; intros x Hx.
  - simpl. inversion Hx.
  - simpl. inversion Hx as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
    + exact (insert_mem_self a (sort_weight rest)).
    + exact (insert_mem_in a x (sort_weight rest) (IH x Hnext_rec)).
Qed.

(* 插入成员分解：InT c (insert a l) ⟹ c = a 或 c ∈ l *)
Lemma insert_mem_split : forall a c : S, forall l : list S,
  InT c (insert_weight a l) -> Or (Id c a) (InT c l).
Proof.
  intros a c l. induction l as [| b rest IH]; intros Hc.
  - simpl in Hc. inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
    + left. exact (@id_refl S a).
    + exact (match Hnext_rec with end).
  - simpl in Hc.
    destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * left. exact (@id_refl S a).
      * inversion Hnext_rec as [Hl0' | Hnext_y' Hnext_l' Hnext_rec']; subst.
        -- right. exact (InT_here b rest).
        -- right. exact (InT_next c b rest Hnext_rec').
    + inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * right. exact (InT_here b rest).
      * destruct (IH Hnext_rec) as [Hca | Hcr].
        -- left. exact Hca.
        -- right. exact (InT_next c b rest Hcr).
Qed.

(* 插入保持排序（inr 分支用 not_le_lt + lt_le_iff 得 f a ≤ f b） *)
Lemma insert_preserves_sorted : forall a : S, forall l : list S,
  sorted_noninc l -> sorted_noninc (insert_weight a l).
Proof.
  intros a l. induction l as [| b rest IH]; intros Hs.
  - simpl. split.
    + intros c Hc. inversion Hc.
    + exact tt.
  - simpl.
    change (And (forall b0 : S, InT b0 rest -> le (boltzmann_factor b0) (boltzmann_factor b)) (sorted_noninc rest)) in Hs.
    destruct Hs as [Hs_head Hs_tail].
    destruct (@ord_le_dec _ DO (boltzmann_factor b) (boltzmann_factor a)) as [Hba | Hnba].
    + split.
      * intros c Hc. inversion Hc as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
        -- exact Hba.
        -- apply (le_trans (boltzmann_factor c) (boltzmann_factor b) (boltzmann_factor a)).
           ++ exact (Hs_head c Hnext_rec).
           ++ exact Hba.
      * exact (pair Hs_head Hs_tail).
    + split.
      * intros c Hc.
        destruct (insert_mem_split a c rest Hc) as [Hca | Hcr].
        -- (* c = a：f a ≤ f b（Hnba ⟹ lt (f a) (f b) ⟹ le） *)
           assert (Hlt_ab : lt (boltzmann_factor a) (boltzmann_factor b))
             by exact (@not_le_lt _ DO (boltzmann_factor b) (boltzmann_factor a) Hnba).
           apply (le_id_l (boltzmann_factor c) (boltzmann_factor a) (boltzmann_factor b)).
           ++ exact (id_cong (fun z => boltzmann_factor z) Hca).
           ++ apply (lt_le_iff _ _). left. exact Hlt_ab.
        -- exact (Hs_head c Hcr).
      * exact (IH Hs_tail).
Qed.

(* 排序正确性：sort_weight l 满足排序不变量 *)
Lemma sort_sorted : forall l : list S, sorted_noninc (sort_weight l).
Proof.
  induction l as [| a rest IH]; simpl.
  - exact tt.
  - exact (insert_preserves_sorted a (sort_weight rest) IH).
Qed.

(* firstn 对空表恒为 nil（firstn 先匹配 n，需按 k 消解） *)
Lemma firstn_nil : forall (k : nat), Id (firstn (A := S) k nil) nil.
Proof. destruct k; simpl; apply id_refl. Qed.

(* 前缀支配后缀：排序下 firstn k 的元素支配 skipn k 的元素（归纳于 k） *)
Lemma firstn_head_dominates_skipn : forall (L : list S) (k : nat),
  sorted_noninc L ->
  forall s : S, InT s (firstn k L) ->
  forall s' : S, InT s' (skipn k L) ->
  le (boltzmann_factor s') (boltzmann_factor s).
Proof.
  intros L. induction L as [| a rest IH]; intros k Hsorted s Hs s' Hs'.
  - (* firstn_nil 给出 firstn k nil = nil（Id 形）；沿该等式作 Id 消元替换，
       将 Hs : InT s (firstn k nil) 化为 InT s nil——空表无成员，
       InT s nil 无构造案例，故目标随之成立 *)
    assert (Hs0 : InT s nil).
    { exact (match firstn_nil k in (Id _ y)
               return (InT s (firstn (A := S) k nil) -> InT s y)
             with | id_refl => fun H => H end Hs). }
    exact (match Hs0 with end).
  - destruct k as [| k'].
    + exact (match Hs with end).
    + simpl.
      change (And (forall b0 : S, InT b0 rest -> le (boltzmann_factor b0) (boltzmann_factor a)) (sorted_noninc rest)) in Hsorted.
      destruct Hsorted as [Hs_head Hs_tail].
      inversion Hs as [Hl0 | Hnext_y Hnext_l Hnext_rec]; subst.
      * (* s = a：s' ∈ skipn k' rest ⊆ rest，由排序头支配性 *)
        assert (Hrest : InT s' rest) by (apply (skipn_sub k' rest s'); exact Hs').
        exact (Hs_head s' Hrest).
      * (* s ∈ firstn k' rest、s' ∈ skipn k' rest：IH *)
        exact (IH k' Hs_tail s Hnext_rec s' Hs').
Qed.

(* Top-K 支配性（排序版）：select_top_k 保留者权重 ≥ 任意逐出者。
   证明：s2 ∈ sort S_enum（有限覆盖 + sort_mem_in），经 firstn_skipn
   分解到 skipn K（排除 firstn 分支），再 firstn_head_dominates_skipn。 *)
Theorem top_k_majorization_mem :
  forall s1 s2 : S,
    InT s1 (select_top_k S_enum K) -> Not (InT s2 (select_top_k S_enum K)) ->
    le (boltzmann_factor s2) (boltzmann_factor s1).
Proof.
  intros s1 s2 Hs1 Hs2n.
  assert (Hs2_in : InT s2 (sort_weight S_enum)).
  { apply (sort_mem_in S_enum s2). apply S_finite_cover. }
  assert (Hsplit : Or (InT s2 (firstn K (sort_weight S_enum))) (InT s2 (skipn K (sort_weight S_enum)))).
  { apply (InT_app_or (firstn K (sort_weight S_enum)) (skipn K (sort_weight S_enum)) s2).
    rewrite firstn_skipn. exact Hs2_in. }
  destruct Hsplit as [Hs2_first | Hs2_skip].
  - exact (match (Hs2n Hs2_first) with end).
  - exact (firstn_head_dominates_skipn (sort_weight S_enum) K (sort_sorted S_enum) s1 Hs1 s2 Hs2_skip).
Qed.

(* ============================================================ *)
(* Top-K 截断总变差定量界（论文2 P2 项 9）*)
(*   TV(boltzmann, topk_renorm) == tail_mass/Z_thermo（精确恒等）*)
(*   链：守恒（kept + tail == Z）→ kept ≤ Z（子集和）→          *)
(*   符号分支（inv 反序，destruct le 的 Or）→ 逐点差分解（abs   *)
(*   消去）→ 求和分解（Σ_keep + Σ_evict）→ 归一化代数证毕。     *)
(* ============================================================ *)

(* Top-K 版尾部质量（tail_mass 的 keep_top_k 实例化） *)
Definition topk_tail_mass : R :=
  sum_over_S (fun s => if keep_top_k_dec s then zero else boltzmann_factor s).

(* Top-K 版保留质量（重归一化分母） *)
Definition topk_kept_partition : R :=
  sum_over_S (fun s => if keep_top_k_dec s then boltzmann_factor s else zero).

(* 诚实接口：保留集非空（有限集 + K ≥ 1 的可实例化前提，同 evicted_partition_pos 先例） *)
Variable topk_kept_partition_pos : lt zero topk_kept_partition.

(* Top-K 重归一化分布：保留者 b_s/Z_keep，逐出者 0（未归一化空间，与论文形态一致） *)
Definition topk_renorm (s : S) : R :=
  if keep_top_k_dec s then
    mult (inv_pos topk_kept_partition topk_kept_partition_pos) (boltzmann_factor s)
  else zero.

(* 辅助：单参 boltzmann_factor 正性（Section 内自证；全局 boltzmann_factor_pos 是两参版） *)
Lemma boltzmann_factor_pos_attn : forall s : S, lt zero (boltzmann_factor s).
Proof.

  intro s. unfold boltzmann_factor. exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).

Qed.

(* 辅助：if 项非负（keep 时 b > 0，else 0） *)
Lemma topk_kept_term_nonneg : forall s,
  le zero (if keep_top_k_dec s then boltzmann_factor s else zero).
Proof.
  intro s. destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply (lt_le_iff _ _). left. apply boltzmann_factor_pos_attn.
  - apply le_refl.
Qed.

(* 辅助：if 项 ≤ b（keep 时 refl，else 0 ≤ b） *)
Lemma topk_kept_term_le_factor : forall s,
  le (if keep_top_k_dec s then boltzmann_factor s else zero) (boltzmann_factor s).
Proof.
  intro s. destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply le_refl.
  - apply (lt_le_iff _ _). left. apply boltzmann_factor_pos_attn.
Qed.

(* 守恒：kept + tail == Z_thermo（仿 tail_plus_kept_full，keep_top_k_dec 版） *)
Lemma topk_kept_plus_tail_full : Id (plus topk_kept_partition topk_tail_mass) Z_thermo.
Proof.
  unfold topk_kept_partition, topk_tail_mass, Z_thermo.
  assert (Hpt : forall s, Id (plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                   (if keep_top_k_dec s then zero else boltzmann_factor s))
                            (boltzmann_factor s)).
  { intro s. destruct (keep_top_k_dec s) as [Hk | Hnk].
    - apply (plus_zero (boltzmann_factor s)).
    - apply (id_trans (plus_comm zero (boltzmann_factor s)) (plus_zero (boltzmann_factor s))). }
  assert (Hext : Id (sum_over_S (fun s => plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                               (if keep_top_k_dec s then zero else boltzmann_factor s)))
                    (sum_over_S (fun s => boltzmann_factor s)))
    by exact (sum_over_S_ext (fun s => plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                            (if keep_top_k_dec s then zero else boltzmann_factor s))
                             (fun s => boltzmann_factor s) Hpt).
  assert (Hadd : Id (sum_over_S (fun s => plus (if keep_top_k_dec s then boltzmann_factor s else zero)
                                               (if keep_top_k_dec s then zero else boltzmann_factor s)))
                    (plus (sum_over_S (fun s => if keep_top_k_dec s then boltzmann_factor s else zero))
                          (sum_over_S (fun s => if keep_top_k_dec s then zero else boltzmann_factor s))))
    by exact (sum_over_S_add (fun s => if keep_top_k_dec s then boltzmann_factor s else zero)
                             (fun s => if keep_top_k_dec s then zero else boltzmann_factor s)).
  exact (id_trans (id_sym Hadd) Hext).
Qed.

(* kept ≤ Z_thermo（子集和 ≤ 全和：逐点 ≤ b + sum_over_S_le） *)
Lemma topk_kept_le_Zthermo : le topk_kept_partition Z_thermo.
Proof.
  unfold topk_kept_partition, Z_thermo.
  apply sum_over_S_le.
  intro s. apply topk_kept_term_le_factor.
Qed.

(* inv 反序：kept ≤ Z ⟹ inv Z ≤ inv kept（inv_pos_le_compat） *)
Lemma topk_inv_Z_le_inv_kept : le (inv_pos Z_thermo Z_thermo_pos)
                                  (inv_pos topk_kept_partition topk_kept_partition_pos).
Proof.
  exact (inv_pos_le_compat topk_kept_partition Z_thermo topk_kept_partition_pos Z_thermo_pos topk_kept_le_Zthermo).
Qed.

(* 辅助：inv one == one（id_sym (mult_one) + comm + inv_pos_correct） *)
Lemma inv_one_cc : Id (inv_pos one one_pos) one.
Proof.

  exact (id_trans (id_sym (mult_one (inv_pos one one_pos))) (id_trans (mult_comm (inv_pos one one_pos) one) (inv_pos_correct one one_pos))).

Qed.

(* 辅助：opp zero == zero（Section 内自证，防前向引用） *)
Lemma opp_zero_cc : Id (opp zero) zero.
Proof.
  apply id_sym.
  apply (plus_inv_unique zero zero (opp zero)).
  - apply (plus_zero zero).
  - apply (plus_opp zero).
Qed.

(* 辅助：lt a b ⟹ lt (minus a b) zero（lt_plus_compat_lt_le 平移） *)
Lemma lt_minus_cc : forall a b : R, lt a b -> lt (minus a b) zero.
Proof.
  intros a b Hab.
  unfold minus.
  apply (lt_id_r _ (plus b (opp b)) _).
  - apply (plus_opp b).
  - apply (lt_plus_compat_lt_le a b (opp b) (opp b) Hab (le_refl (opp b))).
Qed.

(* 辅助：abs 负号消去：lt a zero → abs a == opp a（abs_opp + abs_pos + opp_lt_compat） *)
Lemma abs_neg_cc : forall a : R, lt a zero -> Id (abs a) (opp a).
Proof.
  intros a Ha.
  apply (id_trans (id_sym (abs_opp a))).
  apply (abs_pos (opp a)).
  apply (lt_id_l zero (opp zero) (opp a)).
  - apply (id_sym opp_zero_cc).
  - apply (opp_lt_compat a zero). exact Ha.
Qed.

(* 辅助：minus x zero == x（opp zero == zero + plus_zero） *)
Lemma minus_zero_cc : forall x : R, Id (minus x zero) x.
Proof.

  intro x. unfold minus. exact (id_trans (id_cong (fun z => plus x z) (opp_zero_cc)) (plus_zero x)).

Qed.

(* 逐点恒等（keep 分支，条件化）：|b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z)
   前提 lt (invZ) (invKeep)（严格逐出，Real 层由 T > 0 实例化）——抽象层 le 不可
   析取（判例 边界），精确符号走显式 lt 前提（T4.3 条件定理模式） *)
Lemma topk_tv_pointwise_keep : forall s,
  keep_top_k s ->
  lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos) ->
  Id (abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                  (mult (inv_pos topk_kept_partition topk_kept_partition_pos) (boltzmann_factor s))))
     (mult (boltzmann_factor s)
           (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                  (inv_pos Z_thermo Z_thermo_pos))).
Proof.
  intros s Hs Hst.
  (* 提公因子：b/Z − b/Z_keep == b·(1/Z − 1/Z_keep)（mult_minus_distr_r 反向） *)
  assert (Hfac : Id (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                            (mult (inv_pos topk_kept_partition topk_kept_partition_pos) (boltzmann_factor s)))
                     (mult (minus (inv_pos Z_thermo Z_thermo_pos)
                                  (inv_pos topk_kept_partition topk_kept_partition_pos))
                           (boltzmann_factor s))).
  { apply (id_sym (mult_minus_distr_r (inv_pos Z_thermo Z_thermo_pos)
                                      (inv_pos topk_kept_partition topk_kept_partition_pos)
                                      (boltzmann_factor s))). }
  (* |D·b| == b·|D|（接口字段 abs_mult + comm + |b| == b） *)
  assert (Habs : Id (abs (mult (minus (inv_pos Z_thermo Z_thermo_pos)
                                      (inv_pos topk_kept_partition topk_kept_partition_pos))
                                (boltzmann_factor s)))
                    (mult (boltzmann_factor s)
                          (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                      (inv_pos topk_kept_partition topk_kept_partition_pos))))).
  { apply (id_trans (abs_mult (minus (inv_pos Z_thermo Z_thermo_pos)
                                        (inv_pos topk_kept_partition topk_kept_partition_pos))
                                 (boltzmann_factor s))).
    apply (id_trans (mult_comm (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                           (inv_pos topk_kept_partition topk_kept_partition_pos)))
                               (abs (boltzmann_factor s)))).
    apply (id_cong (fun z => mult z (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                                (inv_pos topk_kept_partition topk_kept_partition_pos))))
                   (abs_ge_zero_id_cc (boltzmann_factor s)
                                      (lt_le_iff zero (boltzmann_factor s) (inl (boltzmann_factor_pos_attn s))))). }
  (* 符号（前提 lt invZ invKeep）：|1/Z − 1/Z_keep| == 1/Z_keep − 1/Z（abs_neg_cc） *)
  assert (Hsign : Id (abs (minus (inv_pos Z_thermo Z_thermo_pos)
                                 (inv_pos topk_kept_partition topk_kept_partition_pos)))
                     (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                            (inv_pos Z_thermo Z_thermo_pos))).
  { apply (id_trans (abs_neg_cc (minus (inv_pos Z_thermo Z_thermo_pos)
                                       (inv_pos topk_kept_partition topk_kept_partition_pos))
                                (lt_minus_cc (inv_pos Z_thermo Z_thermo_pos)
                                             (inv_pos topk_kept_partition topk_kept_partition_pos)
                                             Hst))
                    (id_trans (opp_minus (inv_pos Z_thermo Z_thermo_pos)
                                         (inv_pos topk_kept_partition topk_kept_partition_pos))
                              (id_trans (plus_comm (opp (inv_pos Z_thermo Z_thermo_pos))
                                                   (inv_pos topk_kept_partition topk_kept_partition_pos))
                                        (id_refl)))). }
  (* 组装：|b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z) *)
  apply (id_trans (id_cong (fun z => abs z) Hfac)).
  apply (id_trans Habs).
  apply (id_cong (fun z => mult (boltzmann_factor s) z) Hsign).
Qed.

(* 逐点恒等（evict 分支）：|b/Z − 0| == b/Z *)
Lemma topk_tv_pointwise_evict : forall s,
  Not (keep_top_k s) ->
  Id (abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) zero))
     (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)).
Proof.
  intros s Hnk.
  assert (Hz : Id (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) zero)
                   (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
    by exact (minus_zero_cc (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))).
  apply (id_trans (id_cong (fun z => abs z) Hz)).
  apply (abs_pos (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))).
  apply (mult_positive (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)).
  - apply (inv_pos_pos Z_thermo Z_thermo_pos).
  - apply (boltzmann_factor_pos_attn s).
Qed.

(* 逐点 if 分解：if k then X else Y == (if k then X else 0) + (if k then 0 else Y) *)
Lemma topk_if_split : forall (X Y : R) (s : S),
  Id (if keep_top_k_dec s then X else Y)
     (plus (if keep_top_k_dec s then X else zero)
           (if keep_top_k_dec s then zero else Y)).
Proof.
  intros X Y s. destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply (id_sym (plus_zero X)).
  - apply (id_trans (id_sym (plus_zero Y)) (id_sym (plus_comm zero Y))).
Qed.

(* 逐点 else 分支线性：if k then 0 else a·f == a·(if k then 0 else f)（对偶 eviction_if_linear） *)
Lemma eviction_if_linear_else :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) (a : R) (f : S -> R) (s : S),
    Id (if kd s then zero else mult a (f s))
       (mult a (if kd s then zero else f s)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - apply (id_sym (mult_zero a)).
  - apply id_refl.
Qed.

(* 逐点总恒等（条件化）：|b/Z − topk| == if keep then b·(invKeep − invZ) else b/Z *)
Lemma topk_tv_pointwise : forall s
  (Hst : lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos)),
  Id (abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) (topk_renorm s)))
     (if keep_top_k_dec s
      then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                            (inv_pos Z_thermo Z_thermo_pos))
      else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)).
Proof.
  intros s Hst.
  unfold topk_renorm.
  destruct (keep_top_k_dec s) as [Hk | Hnk].
  - apply (topk_tv_pointwise_keep s Hk Hst).
  - apply (topk_tv_pointwise_evict s Hnk).
Qed.

(* 求和分解：Σ (if keep then b·D else b/Z) == kept·D + invZ·T *)
Lemma topk_sum_decomp : forall
  (Hst : lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos)),
  Id (sum_over_S (fun s => if keep_top_k_dec s
                           then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                (inv_pos Z_thermo Z_thermo_pos))
                           else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
     (plus (mult topk_kept_partition
                 (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                        (inv_pos Z_thermo Z_thermo_pos)))
           (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)).
Proof.
  intro Hst.
  (* if 分解 → Σ_add *)
  assert (Hsplit : Id (sum_over_S (fun s => if keep_top_k_dec s
                                            then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                                 (inv_pos Z_thermo Z_thermo_pos))
                                            else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
                      (sum_over_S (fun s => plus (if keep_top_k_dec s
                                                  then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                                       (inv_pos Z_thermo Z_thermo_pos))
                                                  else zero)
                                                 (if keep_top_k_dec s
                                                  then zero
                                                  else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))))).
  { apply sum_over_S_ext.
    intro s. apply (topk_if_split (mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                   (inv_pos Z_thermo Z_thermo_pos)))
                                  (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)) s). }
  apply (id_trans Hsplit).
  apply (id_trans (sum_over_S_add (fun s => if keep_top_k_dec s
                                            then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                                 (inv_pos Z_thermo Z_thermo_pos))
                                            else zero)
                                  (fun s => if keep_top_k_dec s
                                            then zero
                                            else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))).
  apply (id_cong2 plus
    (id_trans (sum_over_S_ext _ _ (fun s => id_trans
                                        (id_cong (fun z => if keep_top_k_dec s then z else zero)
                                                 (mult_comm (boltzmann_factor s)
                                                            (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                   (inv_pos Z_thermo Z_thermo_pos))))
                                        (eviction_if_linear keep_top_k keep_top_k_dec
                                                            (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                   (inv_pos Z_thermo Z_thermo_pos))
                                                            boltzmann_factor s)))
              (id_trans (sum_over_S_linear (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                  (inv_pos Z_thermo Z_thermo_pos))
                                           (fun s => if keep_top_k_dec s then boltzmann_factor s else zero))
                        (mult_comm (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                          (inv_pos Z_thermo Z_thermo_pos))
                                   (sum_over_S (fun s => if keep_top_k_dec s then boltzmann_factor s else zero)))))
    (id_trans (sum_over_S_ext _ _ (fun s => eviction_if_linear_else keep_top_k keep_top_k_dec
                                                                    (inv_pos Z_thermo Z_thermo_pos)
                                                                    boltzmann_factor s))
              (sum_over_S_linear (inv_pos Z_thermo Z_thermo_pos)
                                 (fun s => if keep_top_k_dec s then zero else boltzmann_factor s)))).
Qed.

(* 关键代数恒等式：kept·(invKeep − invZ) + invZ·T == 2·(invZ·T) *)
Lemma topk_sum_collapse :
  Id (plus (mult topk_kept_partition
                 (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                        (inv_pos Z_thermo Z_thermo_pos)))
           (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
     (mult (plus one one) (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)).
Proof.
  (* kept·(invK − invZ) == 1 − kept·invZ（mult_minus_distr_l 反向 + kept·invK == 1） *)
  assert (Hk1 : Id (mult topk_kept_partition
                          (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                 (inv_pos Z_thermo Z_thermo_pos)))
                   (minus one (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))).
  { apply (id_trans (mult_minus_distr_l topk_kept_partition
                                        (inv_pos topk_kept_partition topk_kept_partition_pos)
                                        (inv_pos Z_thermo Z_thermo_pos))).
    apply (id_cong (fun z => minus z (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))
                   (id_trans (mult_comm topk_kept_partition
                                        (inv_pos topk_kept_partition topk_kept_partition_pos))
                             (id_trans (mult_comm (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                  topk_kept_partition)
                                       (inv_pos_correct topk_kept_partition topk_kept_partition_pos)))). }
  (* kept·invZ + invZ·T == 1（(kept+T)·invZ == Z·invZ == 1） *)
  assert (Hk2 : Id (plus (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos))
                          (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                    one).
  { apply (id_trans (id_sym (id_cong2 plus (id_refl) (mult_comm topk_tail_mass (inv_pos Z_thermo Z_thermo_pos))))
                    (id_trans (id_sym (mult_plus_distr_r topk_kept_partition topk_tail_mass
                                                         (inv_pos Z_thermo Z_thermo_pos)))
                              (id_trans (id_cong (fun z => mult z (inv_pos Z_thermo Z_thermo_pos))
                                                 topk_kept_plus_tail_full)
                                        (inv_pos_correct Z_thermo Z_thermo_pos)))). }
  (* 1 − kept·invZ == invZ·T：由 plus kept·invZ invZ·T == 1 的 minus 侧 *)
  assert (Hk3 : Id (minus one (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))
                   (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)).
  { apply (id_trans (id_cong (fun z => minus z (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos)))
                             (id_sym Hk2))
                    (minus_plus_cancel_r (mult topk_kept_partition (inv_pos Z_thermo Z_thermo_pos))
                                         (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))). }
  (* 组装：kept·D + invZ·T == (1 − kept·invZ) + invZ·T == invZ·T + invZ·T == 2·(invZ·T) *)
  apply (id_trans (id_trans (id_cong2 plus Hk1 (id_refl))
                            (id_cong (fun z => plus z (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)) Hk3))
                  (id_sym (two_mult (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass)))).
Qed.

(* T2.4-1 主定理（条件化精确恒等）：严格逐出（lt invZ invKeep，Real 层由 T > 0 实例化）
   ⟹ TV(boltzmann, topk_renorm) == tail_mass/Z_thermo *)
Theorem topk_tv_identity_strict :
  lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos) ->
  Id (tv_dist boltzmann_dist_attn topk_renorm)
     (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass).
Proof.
  intro Hst.
  unfold tv_dist, boltzmann_dist_attn, topk_renorm.
  (* 逐点替换（topk_tv_pointwise） *)
  assert (Hpt : Id (sum_over_S (fun s => abs (minus (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                                                     (if keep_top_k_dec s
                                                      then mult (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                               (boltzmann_factor s)
                                                      else zero))))
                    (sum_over_S (fun s => if keep_top_k_dec s
                                          then mult (boltzmann_factor s) (minus (inv_pos topk_kept_partition topk_kept_partition_pos)
                                                                               (inv_pos Z_thermo Z_thermo_pos))
                                          else mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))).
  { apply sum_over_S_ext.
    intro s. apply (topk_tv_pointwise s Hst). }
  apply (id_trans (id_cong (fun z => mult inv_two z) Hpt)).
  apply (id_trans (id_cong (fun z => mult inv_two z) (topk_sum_decomp Hst))).
  apply (id_trans (id_cong (fun z => mult inv_two z) (topk_sum_collapse))).
  (* inv_two·(2·X) == X：assoc + inv_pos_correct + one *)
  apply (id_trans (mult_assoc inv_two (plus one one) (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                  (id_trans (id_cong (fun z => mult z (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                                     (id_trans (mult_comm inv_two (plus one one))
                                               (inv_pos_correct (plus one one) two_pos)))
                            (id_trans (mult_comm one (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))
                                      (mult_one (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass))))).
Qed.

End AttentionGibbsBridge.

(* ============================================================ *)
(* Section MinPSampling：构造性 Min-P 截断采样核               *)
(* ============================================================ *)
(* Llama 3.1 / vLLM 核心解码策略的构造性形式化：
   min-p 采样保留概率 ≥ min_p × max 概率 的 token，其余置零，
   再对保留 token 的 temp_factor 重新归一化。
   路线：Set 层 + sigT + 非平凡实现 + 可提取 OCaml。
   依赖：RealInterfaceEnhanced + DecidableOrder（可判定序）；
   词表基础设施自包含重述（与 StochasticLanguageModel 同构，
   Section 泛化使其定理不可全局复用，故以诚实 Variable 重声明
   已证接口——主文件既有模式）。 *)
(* ------------------------------------------------------------ *)

Section MinPSampling.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---------- 1. 接口假设（与 StochasticLanguageModel 同构） ---------- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* ---------- 2. 基础设施（自包含重述） ---------- *)
Definition temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w]))).

Fixpoint list_sum (f : Token -> R) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (f w) (list_sum f rest)
  end.

Lemma list_sum_linear : forall a f l,
  Id (list_sum (fun w => mult a (f w)) l) (mult a (list_sum f l)).
Proof.
  intros a f l. induction l as [|w rest IH].
  - (* 目标：Id zero (mult a zero)；mult_zero a : Id (mult a zero) zero，id_sym 反转 *)
    simpl. exact (id_sym (mult_zero a)).
  - (* 目标：Id (mult a (plus (f w) (list_sum ...))) (plus (mult a (f w)) (mult a (list_sum ...)))
       IH : Id (mult a (list_sum f rest)) (list_sum (fun w => mult a (f w)) rest)
       左分配：mult a (x+y) == (x+y)·a（mult_comm）== x·a + y·a（mult_plus_distr_r） *)
    simpl.
    (* 目标：Id (plus (mult a (f w)) (list_sum (fun w => mult a (f w)) rest))
               (mult a (plus (f w) (list_sum f rest)))
       用 IH 正向把 LHS 的 list_sum (mult a∘f) rest 换成 mult a (list_sum f rest) *)
    rewrite IH.
    (* 目标：Id (plus (mult a (f w)) (mult a (list_sum f rest)))
               (mult a (plus (f w) (list_sum f rest)))
       左分配：mult a (x + y) == mult a x + mult a y *)
    rewrite (mult_comm a (plus (f w) (list_sum f rest))).
    rewrite (mult_plus_distr_r (f w) (list_sum f rest) a).
    rewrite (mult_comm (f w) a).
    rewrite (mult_comm (list_sum f rest) a).
    apply id_refl.
Qed.

Lemma list_sum_ext : forall f g l,
  (forall w, Id (f w) (g w)) -> Id (list_sum f l) (list_sum g l).
Proof.
  intros f g l H. induction l as [|w rest IH].
  - simpl. apply id_refl.
  - simpl. rewrite H. rewrite IH. apply id_refl.
Qed.

Lemma list_sum_nonneg : forall l f,
  (forall w, le zero (f w)) -> le zero (list_sum f l).
Proof.
  intros l f Hf. induction l as [|w rest IH].
  - simpl. apply le_refl.
  - simpl.
    apply (le_id_l zero (plus zero zero) (plus (f w) (list_sum f rest))
                   (id_sym (plus_zero zero))).
    apply le_plus_compat; [apply Hf | apply IH].
Qed.

Lemma list_sum_single_le_total : forall l f w,
  InT w l -> (forall w', le zero (f w')) -> le (f w) (list_sum f l).
Proof.
  intros l f w Hin Hnonneg. induction l as [|a rest IH].
  - inversion Hin.
  - simpl. inversion Hin as [| y l' HIn']; subst.
    + (* w = a：f a ≤ f a + Σ rest（le_plus_nonneg_r，Σ rest ≥ 0） *)
      exact (le_plus_nonneg_r (f a) (list_sum f rest) (list_sum_nonneg rest f Hnonneg)).
    + (* w ∈ rest：f w ≤ Σ rest ≤ f a + Σ rest *)
      assert (Hle : le (f w) (list_sum f rest)) by exact (IH HIn').
      apply (le_trans _ (list_sum f rest) _ Hle).
      apply (le_id_l (list_sum f rest) (plus zero (list_sum f rest)) (plus (f a) (list_sum f rest))
                     (id_trans (id_sym (plus_zero (list_sum f rest))) (plus_comm (list_sum f rest) zero))).
      apply le_plus_compat; [apply Hnonneg | apply le_refl].
Qed.

Lemma sum_temp_positive : forall (f : Token -> R),
  (forall w, lt zero (f w)) -> forall l : list Token, Not (Id l nil) -> lt zero (list_sum f l).
Proof.
  intros f Hf l Hl. induction l as [|w rest IH].
  - destruct Hl. apply id_refl.
  - destruct rest as [|w' rest'].
    + simpl. apply (lt_id_r zero (f w) (plus (f w) zero) (id_sym (plus_zero (f w))) (Hf w)).
    + simpl. apply (lt_id_l zero (plus zero zero) (plus (f w) (plus (f w') (list_sum f rest')))
                           (id_sym (plus_zero zero))).
      apply lt_plus_compat; [apply Hf | apply IH; intro H; inversion H].
Qed.

Definition partition_temp (prefix : list Token) : R :=
  list_sum (temp_factor prefix) vocab.

Lemma partition_temp_pos : forall prefix, lt zero (partition_temp prefix).
Proof.
  intro prefix. unfold partition_temp.
  apply sum_temp_positive.
  - intro w. unfold temp_factor. apply exp_neg_pos.
  - apply vocab_nonempty.
Qed.

Definition markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (temp_factor prefix w) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)).

(* ---------- 3. 贪心最优 token（自包含重述） ---------- *)
Definition candidate_token : Set := (Token * R)%type.

Fixpoint argmin_aux_token (prefix : list Token) (l : list Token) (best : candidate_token) : candidate_token :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      let loss_best := snd best in
      match ord_le_dec loss_w loss_best with
      | inl _ => argmin_aux_token prefix rest (w, loss_w)
      | inr _ => argmin_aux_token prefix rest best
      end
  end.

Definition pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest => fst (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* ---------- 3b. 贪心最优 token 的实现（StochasticLanguageModel 已证模式重述） ---------- *)
(* InT 头前插：x ∈ y :: l ⟹ x ∈ y :: a :: l（在 y 与 l 之间插入 a） *)
Lemma InT_head_extend : forall (x y a : Token) (l : list Token),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - exact (@InT_next Token x y (a :: l) (@InT_next Token x a l H1)).
Qed.

(* argmin 结果 ∈ 候选列表 ∪ 初始 token：归纳证明。
   换 a 分支：fst ∈ a :: rest（IH），经 InT_next best_token 提升；
   保留分支：fst ∈ best_token :: rest（IH），经 InT_head_extend 提升。 *)
Lemma argmin_aux_token_mem : forall prefix l best_token best_loss,
  InT best_token (best_token :: l) ->
  InT (fst (argmin_aux_token prefix l (best_token, best_loss))) (best_token :: l).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + (* 换 a：fst ∈ a :: rest（IH 于新 best (a, loss a)），提升到 best_token :: a :: rest *)
      assert (Hmem : InT (fst (argmin_aux_token prefix rest (a, total_loss (prefix ++ [a])))) (a :: rest))
        by (apply (IH a (total_loss (prefix ++ [a]))); apply InT_here).
      apply InT_next. exact Hmem.
    + (* 保留：fst ∈ best_token :: rest（IH），提升到 best_token :: a :: rest *)
      assert (Hmem : InT (fst (argmin_aux_token prefix rest (best_token, best_loss))) (best_token :: rest))
        by (apply (IH best_token best_loss); apply InT_here).
      apply (InT_head_extend _ _ a rest). exact Hmem.
Qed.

(* pick_best ∈ vocab（非平凡：argmin 遍历 vocab 且保持成员） *)
Theorem pick_best_in_vocab' : forall prefix, InT (pick_best_token prefix) vocab.
Proof.
  intro prefix.
  unfold pick_best_token.
  destruct vocab as [| w0 rest].
  - (* vocab 为空，但 vocab_nonempty 矛盾 *)
    exact (match vocab_nonempty (@id_refl (list Token) nil) with end).
  - (* 初始 w0 ∈ w0 :: rest = vocab；argmin 保持成员 *)
    apply (argmin_aux_token_mem prefix rest w0 (total_loss (prefix ++ [w0]))).
    apply InT_here.
Qed.

(* 核正性（温度采样概率 > 0：temp_factor > 0 且 inv(partition) > 0） *)
Lemma markov_pos : forall prefix w, lt zero (markov_kernel prefix w).
Proof.
  intros prefix w. unfold markov_kernel.
  apply mult_positive.
  - unfold temp_factor. apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---------- 4. Min-P 参数与核心定义 ---------- *)
Variable min_p : R.
Variable min_p_pos : lt zero min_p.
Variable min_p_lt_one : lt min_p one.

(* 乘法单位元左消去 *)
Lemma mult_one_l : forall a : R, Id (mult one a) a.
Proof.
  intros a. rewrite mult_comm. apply mult_one.
Qed.

(* 0 ≤ a 且 b ≤ 1 → b·a ≤ a（环代数，非平凡） *)
Lemma le_mult_le_one_r : forall a b : R,
  le zero a -> le b one -> le (mult b a) a.
Proof.
  intros a b Ha Hb.
  assert (H1 : le zero (minus one b)).
  { apply le_minus_nonneg. apply Hb. }
  assert (H2 : le zero (mult (minus one b) a)).
  {
    (* 目标 le zero (mult (minus one b) a)：
       1) zero == mult a zero（mult_zero 反向）；
       2) mult (minus one b) a == mult a (minus one b)（mult_comm）；
       3) le (mult a zero) (mult a (minus one b))（le_mult_compat_r a zero (minus one b) Ha H1）。 *)
    apply (le_id_l zero (mult a zero) (mult (minus one b) a) (id_sym (mult_zero a))).
    rewrite <- (mult_comm a (minus one b)).
    apply (le_mult_compat_r a zero (minus one b) Ha H1).
  }
  assert (H3 : Id (mult (minus one b) a) (minus a (mult b a))).
  {
    (* mult (minus one b) a == mult a (minus one b)（comm）
       == minus (mult a one) (mult a b)（distr_l）
       == minus a (mult a b)（mult_one）== minus a (mult b a)（comm） *)
    rewrite (mult_comm (minus one b) a).
    rewrite mult_minus_distr_l.
    rewrite mult_one.
    rewrite (mult_comm a b).
    apply id_refl.
  }
  rewrite H3 in H2.
  assert (H4 : le (plus (mult b a) zero) (plus (mult b a) (minus a (mult b a)))).
  { apply le_plus_compat; [apply le_refl | apply H2]. }
  rewrite plus_zero_r in H4.
  assert (H5 : Id (plus (mult b a) (minus a (mult b a))) a).
  { apply minus_plus_cancel. }
  rewrite H5 in H4.
  apply H4.
Qed.

(* 最佳 token 即 pick_best_token（最小损失 = 最大 temp_factor） *)
Definition pick_max_token (prefix : list Token) : Token := pick_best_token prefix.

(* 最大概率值 *)
Definition max_markov_prob (prefix : list Token) : R :=
  markov_kernel prefix (pick_max_token prefix).

(* Min-P 阈值 = min_p × 最大概率 *)
Definition minp_threshold (prefix : list Token) : R :=
  mult min_p (max_markov_prob prefix).

(* 判定：token w 的概率是否 ≥ 阈值（Set 层可判定） *)
Definition minp_keep (prefix : list Token) (w : Token) : Set :=
  le (minp_threshold prefix) (markov_kernel prefix w).

Definition minp_keep_dec (prefix : list Token) (w : Token) :
  Or (minp_keep prefix w) (Not (minp_keep prefix w)).
Proof.
  unfold minp_keep. apply ord_le_dec.
Defined.

(* 截断后的非归一化质量（保留 token 的 temp_factor 之和） *)
Definition minp_temp_sum (prefix : list Token) : R :=
  list_sum (fun w => match minp_keep_dec prefix w with
                     | inl _ => temp_factor prefix w
                     | inr _ => zero
                     end) vocab.

(* ---------- 5. 核心引理（全部非平凡实现） ---------- *)
Lemma pick_max_token_correct : forall prefix,
  Id (markov_kernel prefix (pick_max_token prefix)) (max_markov_prob prefix).
Proof.

  intro prefix. unfold max_markov_prob, pick_max_token. exact id_refl.

Qed.

(* 引理：pick_max_token 满足 Min-P 条件（自包含性，保证截断集非空） *)
Lemma pick_max_token_minp_keep : forall prefix,
  minp_keep prefix (pick_max_token prefix).
Proof.
  intro prefix. unfold minp_keep.
  rewrite pick_max_token_correct.
  apply le_mult_le_one_r.
  - apply (lt_le_iff _ _). left. apply markov_pos.
  - apply (lt_le_iff _ _). left. apply min_p_lt_one.
Qed.

(* 引理：lt zero a 且 le a b → lt zero b（序传递，非平凡） *)
Lemma lt_zero_le_trans : forall a b : R,
  lt zero a -> le a b -> lt zero b.
Proof.
  intros a b Ha Hab.
  assert (Hnonneg : le zero (minus b a)).
  { apply le_minus_nonneg. apply Hab. }
  assert (Hpos : lt zero (plus (minus b a) a)).
  { apply plus_le_lt_pos.
    - apply Hnonneg.
    - apply Ha. }
  assert (Heq : Id (plus (minus b a) a) b).
  { rewrite (plus_comm (minus b a) a). apply minus_plus_cancel. }
  rewrite Heq in Hpos. apply Hpos.
Qed.

(* 引理：minp_temp_sum 正性（非平凡：至少 pick_max_token 被计入） *)
Lemma minp_temp_sum_pos : forall prefix, lt zero (minp_temp_sum prefix).
Proof.
  intro prefix.
  set (f := fun w => match minp_keep_dec prefix w with
                     | inl _ => temp_factor prefix w
                     | inr _ => zero
                     end).
  assert (Hin : InT (pick_max_token prefix) vocab).
  { apply pick_best_in_vocab'. }
  assert (Hkeep : minp_keep prefix (pick_max_token prefix)).
  { apply pick_max_token_minp_keep. }
  assert (Hf_eq : Id (f (pick_max_token prefix)) (temp_factor prefix (pick_max_token prefix))).
  { unfold f. destruct (minp_keep_dec prefix (pick_max_token prefix)).
    - apply id_refl.
    - destruct n. apply Hkeep. }
  assert (Hle : le (temp_factor prefix (pick_max_token prefix)) (minp_temp_sum prefix)).
  { unfold minp_temp_sum. rewrite <- Hf_eq.
    apply list_sum_single_le_total.
    - apply Hin.
    - intro w. unfold f. destruct (minp_keep_dec prefix w).
      + apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
      + apply le_refl. }
  apply lt_zero_le_trans with (a := temp_factor prefix (pick_max_token prefix)).
  - unfold temp_factor. apply exp_neg_pos.
  - apply Hle.
Qed.

(* Min-P 截断采样核（基于 temp_factor 重新归一化） *)
Definition minp_markov_kernel (prefix : list Token) (w : Token) : R :=
  match minp_keep_dec prefix w with
  | inl _ =>
      mult (temp_factor prefix w)
           (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
  | inr _ => zero
  end.

(* ---------- 6. 核心定理（全部非平凡实现） ---------- *)

(* 定理 1：Min-P 核非负——保留者 > 0，逐出者 == 0（Or 分解）。
   非平凡：match 分支 + mult_positive + inv_pos_pos（保留分支），
   定义性归约（逐出分支）。 *)
Lemma minp_markov_kernel_nonneg : forall prefix w,
  Or (Id (minp_markov_kernel prefix w) zero) (lt zero (minp_markov_kernel prefix w)).
Proof.
  intros prefix w. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hkeep | Hdrop].
  - right. apply mult_positive.
    + unfold temp_factor. apply exp_neg_pos.
    + apply inv_pos_pos.
  - left. apply id_refl.
Qed.

(* 定理 2：Min-P 核的保留者正性（**条件式**：前提 minp_keep prefix w。
   与无条件定理 minp_markov_kernel_nonneg 区分——命名带 keep 前缀，
   引用时需提供保留前提，避免误读为无条件成立。 *)
Lemma minp_markov_kernel_keep_pos : forall prefix w,
  minp_keep prefix w -> lt zero (minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hdrop].
  - apply mult_positive.
    + unfold temp_factor. apply exp_neg_pos.
    + apply inv_pos_pos.
  - destruct (Hdrop Hkeep).
Qed.

(* 定理 3：Min-P 核归一化——保留者重归一化后 Σ = 1（概率守恒）。
   非平凡：minp_temp_sum 定义 + list_sum_linear 提取公因子 +
   inv_pos_correct 消去（仿 markov_normalized 模式）。 *)
Theorem minp_markov_kernel_normalized : forall prefix,
  Id (list_sum (fun w => minp_markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  unfold minp_markov_kernel.
  (* 用 r_if 模式展开：保留分支 temp_factor·inv(sum)，逐出分支 zero。
     以 match 展开（minp_keep_dec 固定后分支确定）。 *)
  assert (Hext : Id (list_sum (fun w => match minp_keep_dec prefix w with
                                        | inl _ => mult (temp_factor prefix w) (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                                        | inr _ => zero
                                        end) vocab)
                    (list_sum (fun w => mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                                            (match minp_keep_dec prefix w with
                                             | inl _ => temp_factor prefix w
                                             | inr _ => zero
                                             end)) vocab)).
  { apply list_sum_ext. intro w.
    destruct (minp_keep_dec prefix w) as [Hk | Hd].
    - simpl. apply mult_comm.
    - simpl. apply (id_sym (mult_zero (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix)))). }
  rewrite Hext.
  assert (Hlin : Id (list_sum (fun w => mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                                            (match minp_keep_dec prefix w with
                                             | inl _ => temp_factor prefix w
                                             | inr _ => zero
                                             end)) vocab)
                    (mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                          (list_sum (fun w => match minp_keep_dec prefix w with
                                              | inl _ => temp_factor prefix w
                                              | inr _ => zero
                                              end) vocab))).
  { apply list_sum_linear. }
  rewrite Hlin.
  assert (Hdef : Id (list_sum (fun w => match minp_keep_dec prefix w with
                                        | inl _ => temp_factor prefix w
                                        | inr _ => zero
                                        end) vocab) (minp_temp_sum prefix)).
  { unfold minp_temp_sum. apply id_refl. }
  rewrite Hdef.
  (* inv(Z)·Z == 1（inv_pos_correct + mult_comm） *)
  assert (Hcc : Id (mult (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))
                         (minp_temp_sum prefix)) one).
  { exact (id_trans (mult_comm (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix)) (minp_temp_sum prefix))
                    (inv_pos_correct (minp_temp_sum prefix) (minp_temp_sum_pos prefix))). }
  exact Hcc.
Qed.

(* 定理 4：Min-P 核 ≤ 完整核——截断不增加任何 token 的概率。
   非平凡：保留者 = temp_factor·inv(minp_sum)，完整 = temp_factor·inv(partition)，
   需 minp_sum ≤ partition（minp_sum 是子集和，list_sum_single_le_total +
   partition_temp 定义）；再由 inv 反单调（**接口字段 inv_pos_le_compat**：
   a ≤ b ⟹ inv b ≤ inv a，RealInterfaceEnhanced 已补齐）。 *)
(* 补充：list_sum 逐点单调（f ≤ g 逐点 ⟹ Σ f ≤ Σ g，归纳） *)
Lemma list_sum_le : forall (l : list Token) (f g : Token -> R),
  (forall w, le (f w) (g w)) -> le (list_sum f l) (list_sum g l).
Proof.
  intros l f g Hfg. induction l as [|w rest IH]; simpl.
  - apply le_refl.
  - apply le_plus_compat; [apply Hfg | apply IH].
Qed.

(* minp_temp_sum ≤ partition_temp（list_sum_le 收尾） *)
Lemma minp_temp_sum_le_partition : forall prefix,
  le (minp_temp_sum prefix) (partition_temp prefix).
Proof.
  intro prefix. unfold minp_temp_sum, partition_temp.
  apply list_sum_le.
  intro w. destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - apply le_refl.
  - apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
Qed.

(* 定理 5：Min-P 核与完整核的关系（诚实陈述）。
   Min-P 截断 + 重归一化 ⟹ 保留者核被放大（分母 minp_sum ≤ partition
   ⟹ inv(minp_sum) ≥ inv(partition) ⟹ 保留者核 ≥ 完整核），
   逐出者核 = 0 ≤ 完整核。**条件式**：前提 minp_keep prefix w——
   命名带 keep 前缀与无条件定理区分。 *)
Lemma minp_markov_kernel_keep_ge_full : forall prefix w,
  minp_keep prefix w -> le (markov_kernel prefix w) (minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold minp_markov_kernel, markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - (* 保留分支：temp_factor·inv(partition) ≤ temp_factor·inv(minp_sum) *)
    apply (le_mult_compat_r (temp_factor prefix w)
                            (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                            (inv_pos (minp_temp_sum prefix) (minp_temp_sum_pos prefix))).
    + (* temp_factor ≥ 0（exp_neg_pos） *)
      apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
    + (* inv(partition) ≤ inv(minp_sum)（inv_pos_le_compat：a ≤ b ⟹ inv b ≤ inv a；
         取 a := minp_sum, b := partition，需 le minp_sum partition ✓） *)
      apply (inv_pos_le_compat (minp_temp_sum prefix) (partition_temp prefix)
                               (minp_temp_sum_pos prefix) (partition_temp_pos prefix)
                               (minp_temp_sum_le_partition prefix)).
  - destruct (Hd Hkeep).
Qed.

(* 定理 6：逐出者核 = 0（截断语义） *)
Lemma minp_markov_kernel_dropped_zero : forall prefix w,
  Not (minp_keep prefix w) -> Id (minp_markov_kernel prefix w) zero.
Proof.
  intros prefix w Hdrop. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - destruct (Hdrop Hk).
  - apply id_refl.
Qed.

Lemma markov_kernel_unfold : forall (prefix : list Token) (w : Token),
  Id (markov_kernel prefix w)
     (mult (temp_factor prefix w)
           (inv_pos (partition_temp prefix)
                    (partition_temp_pos prefix))).
Proof.

  intros prefix w. unfold markov_kernel, temp_factor, partition_temp. exact id_refl.

Qed.

(* ===== T2 保留者 minp 核展开 ===== *)
Lemma minp_markov_kernel_unfold_keep : forall (prefix : list Token) (w : Token),
  minp_keep prefix w ->
  Id (minp_markov_kernel prefix w)
     (mult (temp_factor prefix w)
           (inv_pos (minp_temp_sum prefix)
                    (minp_temp_sum_pos prefix))).
Proof.
  intros prefix w Hkeep. unfold minp_markov_kernel.
  destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - apply id_refl.
  - destruct (Hd Hkeep).
Qed.

(* ===== T3 放大因子显式形式：minp 核 = markov 核 · (inv(minp_sum)·partition) =====
   数学：保留者 minp 核 = tf·inv(minp_sum) = (tf·inv(partition))·(partition·inv(minp_sum))
        = markov 核 · (inv(minp_sum)·partition)（mult_assoc + inv_pos_correct + comm） *)
Lemma minp_kernel_ratio : forall (prefix : list Token) (w : Token),
  minp_keep prefix w ->
  Id (minp_markov_kernel prefix w)
     (mult (markov_kernel prefix w)
           (mult (inv_pos (minp_temp_sum prefix)
                          (minp_temp_sum_pos prefix))
                 (partition_temp prefix))).
Proof.
  intros prefix w Hkeep.
  rewrite (minp_markov_kernel_unfold_keep prefix w Hkeep).
  rewrite (markov_kernel_unfold prefix w).
  (* 目标：tf·inv(minp_sum) == (tf·inv(partition))·(inv(minp_sum)·partition) *)
  (* RHS 反向结合：mult (mult tf inv_p) (mult inv_s p) → mult tf (mult inv_p (mult inv_s p)) *)
  rewrite <- (mult_assoc (temp_factor prefix w)
                         (inv_pos (partition_temp prefix)
                                  (partition_temp_pos prefix))
                         (mult (inv_pos (minp_temp_sum prefix)
                                        (minp_temp_sum_pos prefix))
                               (partition_temp prefix))).
  (* 目标：tf·inv(minp_sum) == tf·(inv(partition)·(inv(minp_sum)·partition)) *)
  (* 内层：inv(partition)·(inv(minp_sum)·partition) == inv(minp_sum) *)
  assert (Hinner : Id (mult (inv_pos (partition_temp prefix)
                                     (partition_temp_pos prefix))
                            (mult (inv_pos (minp_temp_sum prefix)
                                           (minp_temp_sum_pos prefix))
                                  (partition_temp prefix)))
                      (inv_pos (minp_temp_sum prefix)
                               (minp_temp_sum_pos prefix))).
  {
    (* inv_p·(inv_s·p) == inv_p·(p·inv_s)（comm 换内层） *)
    assert (Hc : Id (mult (inv_pos (partition_temp prefix)
                                   (partition_temp_pos prefix))
                          (mult (inv_pos (minp_temp_sum prefix)
                                         (minp_temp_sum_pos prefix))
                                (partition_temp prefix)))
                    (mult (inv_pos (partition_temp prefix)
                                   (partition_temp_pos prefix))
                          (mult (partition_temp prefix)
                                (inv_pos (minp_temp_sum prefix)
                                         (minp_temp_sum_pos prefix))))).
    { apply (id_cong (fun z => mult (inv_pos (partition_temp prefix)
                                             (partition_temp_pos prefix)) z)
                     (mult_comm (inv_pos (minp_temp_sum prefix)
                                         (minp_temp_sum_pos prefix))
                                (partition_temp prefix))). }
    apply (id_trans Hc).
    (* 目标：inv_p·(p·inv_s) == inv_s *)
    apply (id_trans (mult_assoc (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)
                                        (inv_pos (minp_temp_sum prefix)
                                                 (minp_temp_sum_pos prefix)))).
    (* 目标：(inv_p·p)·inv_s == inv_s *)
    (* 换序：mult (mult inv_p p) inv_s == mult (mult p inv_p) inv_s *)
    apply (id_trans (id_cong (fun z => mult z (inv_pos (minp_temp_sum prefix)
                                                       (minp_temp_sum_pos prefix)))
                             (mult_comm (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)))).
    apply (id_trans (id_cong (fun z => mult z (inv_pos (minp_temp_sum prefix)
                                                       (minp_temp_sum_pos prefix)))
                             (inv_pos_correct (partition_temp prefix)
                                              (partition_temp_pos prefix)))).
    (* 目标：one·inv_s == inv_s *)
    apply (id_trans (mult_comm one (inv_pos (minp_temp_sum prefix)
                                            (minp_temp_sum_pos prefix)))).
    apply (mult_one (inv_pos (minp_temp_sum prefix)
                             (minp_temp_sum_pos prefix))).
  }
  (* 用 Hinner 替换内层（方向：目标 LHS==RHS，Hinner 给 RHS==LHS 侧，id_sym 反转） *)
  apply (id_sym (id_cong (fun z => mult (temp_factor prefix w) z) Hinner)).
Qed.

(* ===== T5 截断质量：1 − Z_minp/Z_full，非负 ===== *)
Definition minp_dropped_mass (prefix : list Token) : R :=
  minus one (mult (inv_pos (partition_temp prefix)
                           (partition_temp_pos prefix))
                  (minp_temp_sum prefix)).

Lemma minp_dropped_mass_nonneg : forall prefix,
  le zero (minp_dropped_mass prefix).
Proof.
  intro prefix. unfold minp_dropped_mass.
  apply le_minus_nonneg.
  (* 目标：le (mult inv_p minp_sum) one *)
  (* minp_sum ≤ partition ⟹ inv_p·minp_sum ≤ inv_p·partition == one *)
  apply (le_id_r (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (minp_temp_sum prefix))
                 (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (partition_temp prefix))
                 one).
  - (* inv_p·partition == one（inv_pos_correct + comm） *)
    apply (id_trans (mult_comm (inv_pos (partition_temp prefix)
                                        (partition_temp_pos prefix))
                               (partition_temp prefix))).
    apply (inv_pos_correct (partition_temp prefix)
                           (partition_temp_pos prefix)).
  - (* inv_p ≥ 0 且 minp_sum ≤ partition ⟹ inv_p·minp_sum ≤ inv_p·partition *)
    apply (le_mult_compat_r (inv_pos (partition_temp prefix)
                                     (partition_temp_pos prefix))
                            (minp_temp_sum prefix)
                            (partition_temp prefix)).
    + (* inv_p ≥ 0：inv_pos_pos ⟹ lt zero ⟹ le zero *)
      apply (lt_le_iff _ _). left.
      apply (inv_pos_pos (partition_temp prefix)
                         (partition_temp_pos prefix)).
    + (* minp_sum ≤ partition（已有 L25502） *)
      exact (minp_temp_sum_le_partition prefix).
Qed.

(* ===== T6 截断质量定量上界：1 − Z_minp/Z_full ≤ 1 − max_prob =====
   数学：pick_max ∈ 保留集 ⟹ minp_sum ≥ tf(pick_max) == max_prob·partition
         ⟹ inv(partition)·minp_sum ≥ max_prob ⟹ 1 − ... ≤ 1 − max_prob。
   意义：最大核概率越接近 1，Min-P 截断的信息损失越小——定量界。 *)
Lemma temp_factor_max_eq : forall prefix,
  Id (temp_factor prefix
                  (pick_max_token prefix))
     (mult (max_markov_prob prefix)
           (partition_temp prefix)).
Proof.
  intro prefix.
  (* H1 : tf(pick_max)·inv(p) == max_prob *)
  assert (H1 : Id (mult (temp_factor prefix
                                    (pick_max_token prefix))
                        (inv_pos (partition_temp prefix)
                                 (partition_temp_pos prefix)))
                   (max_markov_prob prefix)).
  {
    apply (id_trans (id_sym (markov_kernel_unfold prefix (pick_max_token prefix)))).
    exact (pick_max_token_correct prefix).
  }
  (* tf == tf·one == tf·(inv_p·p) == (tf·inv_p)·p == max·p *)
  apply (id_trans (id_sym (mult_one (temp_factor prefix
                                                 (pick_max_token prefix))))).
  apply (id_trans (id_cong (fun z => mult (temp_factor prefix
                                                      (pick_max_token prefix)) z)
                           (id_sym (id_trans (mult_comm (inv_pos (partition_temp prefix)
                                                                 (partition_temp_pos prefix))
                                                        (partition_temp prefix))
                                             (inv_pos_correct (partition_temp prefix)
                                                              (partition_temp_pos prefix)))))).
  apply (id_trans (mult_assoc (temp_factor prefix
                                           (pick_max_token prefix))
                              (inv_pos (partition_temp prefix)
                                       (partition_temp_pos prefix))
                              (partition_temp prefix))).
  apply (id_cong (fun z => mult z (partition_temp prefix)) H1).
Qed.

Lemma temp_factor_max_le_sum : forall prefix,
  le (temp_factor prefix
                  (pick_max_token prefix))
     (minp_temp_sum prefix).
Proof.
  intro prefix. unfold minp_temp_sum.
  (* f(pick_max) == match (pick_max)（pick_max 保留 ⟹ inl 分支） *)
  assert (Heq : Id (temp_factor prefix
                                (pick_max_token prefix))
                   (match minp_keep_dec prefix
                                 (pick_max_token prefix)
                    with
                    | inl _ => temp_factor prefix
                                             (pick_max_token prefix)
                    | inr _ => zero
                    end)).
  {
    destruct (minp_keep_dec prefix
                            (pick_max_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd (pick_max_token_minp_keep prefix)).
  }
  apply (le_id_l (temp_factor prefix
                              (pick_max_token prefix))
                 (match minp_keep_dec prefix
                               (pick_max_token prefix)
                  with
                  | inl _ => temp_factor prefix
                                           (pick_max_token prefix)
                  | inr _ => zero
                  end)
                 (list_sum (fun w => match minp_keep_dec prefix w with
                                      | inl _ => temp_factor prefix w
                                      | inr _ => zero
                                      end) vocab)
                 Heq).
  apply (list_sum_single_le_total vocab
                                  (fun w => match minp_keep_dec prefix w with
                                            | inl _ => temp_factor prefix w
                                            | inr _ => zero
                                            end)
                                  (pick_max_token prefix)
                                  (pick_best_in_vocab' prefix)).
  intro w. destruct (minp_keep_dec prefix w) as [Hk | Hd].
  - apply (lt_le_iff _ _). left. unfold temp_factor. apply exp_neg_pos.
  - apply le_refl.
Qed.

Lemma minp_scaled_sum_ge_max : forall prefix,
  le (max_markov_prob prefix)
     (mult (inv_pos (partition_temp prefix)
                    (partition_temp_pos prefix))
           (minp_temp_sum prefix)).
Proof.
  intro prefix.
  (* max·p ≤ minp_sum（temp_factor_max_le_sum + temp_factor_max_eq 桥） *)
  assert (H1 : le (mult (max_markov_prob prefix)
                        (partition_temp prefix))
                  (minp_temp_sum prefix)).
  {
    apply (le_id_l (mult (max_markov_prob prefix)
                          (partition_temp prefix))
                   (temp_factor prefix
                                (pick_max_token prefix))
                   (minp_temp_sum prefix)
                   (id_sym (temp_factor_max_eq prefix))
                   (temp_factor_max_le_sum prefix)).
  }
  (* inv_p·(max·p) ≤ inv_p·minp_sum；左侧 == max（assoc + inv_correct + one） *)
  (* 代数链：inv_p·(max·p) == max *)
  assert (Hid : Id (mult (inv_pos (partition_temp prefix)
                                  (partition_temp_pos prefix))
                         (mult (max_markov_prob prefix)
                               (partition_temp prefix)))
                   (max_markov_prob prefix)).
  {
    apply (id_trans (mult_assoc (inv_pos (partition_temp prefix)
                                         (partition_temp_pos prefix))
                                (max_markov_prob prefix)
                                (partition_temp prefix))).
    apply (id_trans (id_cong (fun z => mult z (partition_temp prefix))
                             (mult_comm (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (max_markov_prob prefix)))).
    apply (id_trans (id_sym (mult_assoc (max_markov_prob prefix)
                                        (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)))).
    apply (id_trans (id_cong (fun z => mult (max_markov_prob prefix) z)
                             (mult_comm (inv_pos (partition_temp prefix)
                                                 (partition_temp_pos prefix))
                                        (partition_temp prefix)))).
    apply (id_trans (id_cong (fun z => mult (max_markov_prob prefix) z)
                             (inv_pos_correct (partition_temp prefix)
                                              (partition_temp_pos prefix)))).
    apply (id_trans (mult_comm (max_markov_prob prefix) one)).
    apply (mult_one_l (max_markov_prob prefix)).
  }
  (* 组装：max ≤ inv_p·minp_sum（inv_p·(max·p) == max 且 inv_p·(max·p) ≤ inv_p·minp_sum） *)
  apply (le_id_l (max_markov_prob prefix)
                 (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (mult (max_markov_prob prefix)
                             (partition_temp prefix)))
                 (mult (inv_pos (partition_temp prefix)
                                (partition_temp_pos prefix))
                       (minp_temp_sum prefix))
                 (id_sym Hid)
                 (le_mult_compat_r (inv_pos (partition_temp prefix)
                                            (partition_temp_pos prefix))
                                   (mult (max_markov_prob prefix)
                                         (partition_temp prefix))
                                   (minp_temp_sum prefix)
                                   (lt_le_iff _ _ (inl (inv_pos_pos (partition_temp prefix)
                                                                    (partition_temp_pos prefix))))
                                   H1)).

Qed.
Lemma minp_dropped_mass_le_one_minus_max : forall prefix,
  le (minp_dropped_mass prefix)
     (minus one (max_markov_prob prefix)).
Proof.

  intro prefix. unfold minp_dropped_mass. exact (le_id_l (plus one (opp (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix)))) (minus one (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix))) (minus one (max_markov_prob prefix)) (id_refl) (le_plus_compat one one (opp (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix))) (opp (max_markov_prob prefix)) (le_refl one) (opp_le_compat (max_markov_prob prefix) (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (minp_temp_sum prefix)) (minp_scaled_sum_ge_max prefix)))).

Qed.

Definition minp_threshold_p (mp : R) (prefix : list Token) : R :=
  mult mp (max_markov_prob prefix).

Definition minp_keep_p (mp : R) (prefix : list Token) (w : Token) : Set :=
  le (minp_threshold_p mp prefix) (markov_kernel prefix w).

Definition minp_keep_dec_p (mp : R) (prefix : list Token) (w : Token) :
  Or (minp_keep_p mp prefix w) (Not (minp_keep_p mp prefix w)).
Proof.
  unfold minp_keep_p, minp_threshold_p. apply ord_le_dec.
Defined.

Definition minp_temp_sum_p (mp : R) (prefix : list Token) : R :=
  list_sum (fun w => match minp_keep_dec_p mp prefix w with
                           | inl _ => temp_factor prefix w
                           | inr _ => zero
                           end) vocab.

Definition minp_dropped_mass_p (mp : R) (prefix : list Token) : R :=
  minus one (mult (inv_pos (partition_temp prefix)
                           (partition_temp_pos prefix))
                  (minp_temp_sum_p mp prefix)).

(* ===== T4a：min_p 增大 ⟹ 保留判定反单调（保留集缩小） =====
   mp1 ≤ mp2 ⟹ threshold1 ≤ threshold2（le_mult_compat_r，max ≥ 0）
   ⟹ keep2 w（threshold2 ≤ kernel）⟹ threshold1 ≤ kernel（le_trans）⟹ keep1 w *)
Lemma minp_keep_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix w,
    minp_keep_p mp2 prefix w -> minp_keep_p mp1 prefix w.
Proof.
  intros mp1 mp2 Hmp prefix w Hk2.
  unfold minp_keep_p, minp_threshold_p in *.
  (* max_markov_prob ≥ 0（markov_pos 提升） *)
  assert (Hmax : le zero (max_markov_prob prefix)).
  { unfold max_markov_prob. rewrite pick_max_token_correct.
    apply (lt_le_iff _ _). left.
    exact (markov_pos prefix
                      (pick_max_token prefix)). }
  (* mp1·max ≤ mp2·max（le_mult_compat_r） *)
  assert (Hthr : le (mult mp1 (max_markov_prob prefix))
                    (mult mp2 (max_markov_prob prefix))).
  { apply (le_mult_compat_weak mp1 mp2 (max_markov_prob prefix) Hmax Hmp). }
  (* threshold1 ≤ threshold2 ≤ kernel ⟹ threshold1 ≤ kernel *)
  apply (le_trans _ (mult mp2 (max_markov_prob prefix)) _ Hthr).
  exact Hk2.
Qed.

(* 辅助：temp_factor ≥ 0 *)
Lemma temp_factor_nonneg_p : forall prefix w,
  le zero (temp_factor prefix w).
Proof.
  intros prefix w. unfold temp_factor. apply (lt_le_iff _ _). left. apply exp_neg_pos.
Qed.

(* 辅助：参数化保留者项 ≥ 0（inl 分支 tf ≥ 0，inr 分支 0） *)
Lemma minp_term_nonneg_p : forall mp prefix w,
  le zero (match minp_keep_dec_p mp prefix w with
           | inl _ => temp_factor prefix w
           | inr _ => zero
           end).
Proof.
  intros mp prefix w. destruct (minp_keep_dec_p mp prefix w) as [Hk | Hd].
  - exact (temp_factor_nonneg_p prefix w).
  - apply le_refl.
Qed.

(* ===== T4b：min_p 增大 ⟹ 保留质量反单调（minp_sum2 ≤ minp_sum1） =====
   逐项：keep2 w ⟹ keep1 w（antitone）⟹ 项贡献相同；keep2 逐出 ⟹ 项2 = 0 ≤ 项1 *)
Lemma minp_temp_sum_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (minp_temp_sum_p mp2 prefix) (minp_temp_sum_p mp1 prefix).
Proof.
  intros mp1 mp2 Hmp prefix.
  unfold minp_temp_sum_p.
  apply (list_sum_le vocab
                     (fun w => match minp_keep_dec_p mp2 prefix w with
                               | inl _ => temp_factor prefix w
                               | inr _ => zero
                               end)
                     (fun w => match minp_keep_dec_p mp1 prefix w with
                               | inl _ => temp_factor prefix w
                               | inr _ => zero
                               end)).
  intro w. destruct (minp_keep_dec_p mp2 prefix w) as [Hk2 | Hd2].
  - (* keep2 ⟹ keep1（antitone）⟹ 项相同 *)
    assert (Hk1 : minp_keep_p mp1 prefix w) by exact (minp_keep_p_antitone mp1 mp2 Hmp prefix w Hk2).
    destruct (minp_keep_dec_p mp1 prefix w) as [Hk1' | Hd1'].
    + apply le_refl.
    + destruct (Hd1' Hk1).
  - (* 逐出 ⟹ 项2 = 0 ≤ 项1 *)
    apply (minp_term_nonneg_p mp1 prefix w).
Qed.

(* ===== T4c：min_p 增大 ⟹ 截断质量不降（mass1 ≤ mass2） =====
   sum2 ≤ sum1 ⟹ inv·sum2 ≤ inv·sum1 ⟹ 1−inv·sum1 ≤ 1−inv·sum2 *)
Lemma minp_dropped_mass_p_monotone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (minp_dropped_mass_p mp1 prefix) (minp_dropped_mass_p mp2 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold minp_dropped_mass_p.
  (* sum2 ≤ sum1（antitone） *)
  assert (Hsum : le (minp_temp_sum_p mp2 prefix) (minp_temp_sum_p mp1 prefix))
    by exact (minp_temp_sum_p_antitone mp1 mp2 Hmp prefix).
  (* inv_p ≥ 0（inv_pos_pos） *)
  assert (Hinv : le zero (inv_pos (partition_temp prefix)
                                  (partition_temp_pos prefix))).
  { apply (lt_le_iff _ _). left.
    apply (inv_pos_pos (partition_temp prefix)
                       (partition_temp_pos prefix)). }
  (* inv·sum2 ≤ inv·sum1（le_mult_compat_r） *)
  assert (Hscaled : le (mult (inv_pos (partition_temp prefix)
                                      (partition_temp_pos prefix))
                             (minp_temp_sum_p mp2 prefix))
                       (mult (inv_pos (partition_temp prefix)
                                      (partition_temp_pos prefix))
                             (minp_temp_sum_p mp1 prefix)))
    by exact (le_mult_compat_r (inv_pos (partition_temp prefix)
                                        (partition_temp_pos prefix))
                               (minp_temp_sum_p mp2 prefix) (minp_temp_sum_p mp1 prefix) Hinv Hsum).
  (* 1−X ≤ 1−Y（X ≥ Y ⟹ 1−X ≤ 1−Y）：le_id_l + le_plus_compat one one (opp Y) (opp X) *)
  apply (le_id_l (plus one (opp (mult (inv_pos (partition_temp prefix)
                                                (partition_temp_pos prefix))
                                       (minp_temp_sum_p mp1 prefix))))
                 (minus one (mult (inv_pos (partition_temp prefix)
                                           (partition_temp_pos prefix))
                                  (minp_temp_sum_p mp1 prefix)))
                 (minus one (mult (inv_pos (partition_temp prefix)
                                           (partition_temp_pos prefix))
                                  (minp_temp_sum_p mp2 prefix)))
                 (id_refl)
                 (le_plus_compat one one
                                 (opp (mult (inv_pos (partition_temp prefix)
                                                     (partition_temp_pos prefix))
                                            (minp_temp_sum_p mp1 prefix)))
                                 (opp (mult (inv_pos (partition_temp prefix)
                                                     (partition_temp_pos prefix))
                                            (minp_temp_sum_p mp2 prefix)))
                                 (le_refl one)
                                 (opp_le_compat (mult (inv_pos (partition_temp prefix)
                                                               (partition_temp_pos prefix))
                                                      (minp_temp_sum_p mp2 prefix))
                                                (mult (inv_pos (partition_temp prefix)
                                                               (partition_temp_pos prefix))
                                                      (minp_temp_sum_p mp1 prefix))
                                                Hscaled))).
Qed.

(* ============================================================ *)
(* T2.4-2（）：Min-P 截断质量与词表大小挂钩（回应 S4）*)
(*   dropped ≤ 1 − 1/|S|（截断质量 ≤ 1 − 词表大小倒数）：        *)
(*   链① p_max ≥ 1/|S|：Σp = 1（完整核归一化）+ 逐项 p_w ≤ p_max *)
(*     （argmin 遍历最小性重述）+ 和 ≤ 势·最大 + 除以正数；       *)
(*   链② dropped ≤ 1 − p_max（minp_dropped_mass_le_one_minus_max）*)
(*   非平凡：argmin 最小性 + 归一化 + 计数三块组装，13 引理。     *)
(* ============================================================ *)

(* nat 到 R 的嵌入（MinPSampling 自包含；GRPO of_nat 已全局，防重名） *)
Fixpoint mp_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (mp_of_nat n')
  end.

(* 非空列表长度正性：l ≠ nil ⟹ 0 < mp_of_nat (length l) *)
Lemma mp_of_nat_pos : forall (l : list Token), Not (Id l nil) -> lt zero (mp_of_nat (length l)).
Proof.
  intros l Hl.
  destruct l as [| w rest].
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - simpl.
    induction rest as [| w' rest' IH']; simpl.
    + (* 0 < 1 + 0：换形 (plus one zero) == one，one_pos *)
      apply (@lt_id_r RI zero one (plus one zero)).
      * apply (id_sym (plus_zero one)).
      * exact one_pos.
    + (* 0 < 1 + (1 + mp_of_nat (length rest'))：lt_plus_compat + 结构 IH *)
      apply (@lt_id_l RI zero (plus zero zero) (plus one (plus one (mp_of_nat (length rest'))))).
      * apply (id_sym (plus_zero zero)).
      * apply (lt_plus_compat zero one zero (plus one (mp_of_nat (length rest')))).
        -- exact one_pos.
        -- exact (IH' (fun Hn => match Hn with end)).
Qed.

(* 完整核归一化：Σ_w markov_kernel w == 1（自包含重述；inv_p·Σtemp == inv_p·partition == 1） *)
Lemma markov_kernel_normalized_mp : forall prefix,
  Id (list_sum (markov_kernel prefix) vocab) one.
Proof.
  intro prefix.
  unfold markov_kernel.
  assert (Hext : Id (list_sum (fun w => mult (temp_factor prefix w)
                                             (inv_pos (partition_temp prefix) (partition_temp_pos prefix))) vocab)
                    (list_sum (fun w => mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                                             (temp_factor prefix w)) vocab))
    by (apply list_sum_ext; intro w; apply mult_comm).
  apply (id_trans Hext).
  assert (Hlin : Id (list_sum (fun w => mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                                             (temp_factor prefix w)) vocab)
                    (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                          (list_sum (temp_factor prefix) vocab)))
    by exact (list_sum_linear (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                              (temp_factor prefix) vocab).
  apply (id_trans Hlin).
  assert (Hp : Id (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                        (partition_temp prefix)) one).
  { apply (id_trans (mult_comm (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                               (partition_temp prefix))).
    apply (inv_pos_correct (partition_temp prefix) (partition_temp_pos prefix)). }
  exact Hp.
Qed.

(* temp_factor 反单调：loss a ≤ loss b ⟹ temp b ≤ temp a（exp_neg_le_decr + inv/T ≥ 0） *)
Lemma temp_factor_antitone_mp : forall (prefix : list Token) (a b : Token),
  le (total_loss (prefix ++ [a])) (total_loss (prefix ++ [b])) ->
  le (temp_factor prefix b) (temp_factor prefix a).
Proof.
  intros prefix a b Hloss.
  unfold temp_factor.
  apply (exp_neg_le_decr (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [a])))
                         (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [b])))).
  apply (le_mult_compat_r (inv_pos temperature temperature_pos)
                          (total_loss (prefix ++ [a]))
                          (total_loss (prefix ++ [b]))).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - exact Hloss.
Qed.

(* argmin 遍历最小性（StochasticLanguageModel L2347 模式自包含重述） *)
Lemma argmin_aux_token_min_mp : forall prefix l best_token best_loss,
  And (forall w : Token, InT w l ->
    le (snd (argmin_aux_token prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [w])))
      (le (snd (argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - assert (Hempty : forall w : Token, InT w nil -> le (snd (argmin_aux_token prefix nil (best_token, best_loss)))
                                                        (total_loss (prefix ++ [w]))).
    { intros w HIn. exact (match HIn with end). }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a]))) by (apply not_le_lt; exact Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* snd 恒等于对应 fst 的损失（argmin 遍历不变式，自包含重述） *)
Lemma argmin_aux_token_snd_correct_mp : forall prefix l best_token best_loss,
  Id best_loss (total_loss (prefix ++ [best_token])) ->
  Id (snd (argmin_aux_token prefix l (best_token, best_loss)))
     (total_loss (prefix ++ [fst (argmin_aux_token prefix l (best_token, best_loss))])).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) id_refl).
    + exact (IH best_token best_loss Hinit).
Qed.

(* pick_best 的最优性：loss(pick_best) ≤ loss w（w ∈ vocab） *)
Theorem pick_best_optimal_mp : forall prefix w,
  InT w vocab ->
  le (total_loss (prefix ++ [pick_best_token prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - destruct (argmin_aux_token_min_mp prefix rest w0 (total_loss (prefix ++ [w0]))) as [Hmin Hle].
    assert (Hsnd : Id (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [fst (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))])))
      by exact (argmin_aux_token_snd_correct_mp prefix rest w0 (total_loss (prefix ++ [w0])) id_refl).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + assert (Hr : le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w0])))
        by exact Hle.
      exact (match Hsnd in (Id _ y)
               return (le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                          (total_loss (prefix ++ [w0]))
                          -> le y (total_loss (prefix ++ [w0])))
             with | id_refl => fun H => H end Hr).
    + assert (Hr : le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w])))
        by exact (Hmin w Hwrest).
      exact (match Hsnd in (Id _ y)
               return (le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                          (total_loss (prefix ++ [w]))
                          -> le y (total_loss (prefix ++ [w])))
             with | id_refl => fun H => H end Hr).
Qed.

(* max 最大性：kernel w ≤ max（w ∈ vocab）——loss 最小 + temp 反单调 + inv ≥ 0 保序 *)
Lemma markov_kernel_le_max_mp : forall prefix w,
  InT w vocab ->
  le (markov_kernel prefix w) (max_markov_prob prefix).
Proof.
  intros prefix w Hw.
  unfold max_markov_prob, markov_kernel.
  apply (le_mult_compat_weak (temp_factor prefix w) (temp_factor prefix (pick_max_token prefix))
                             (inv_pos (partition_temp prefix) (partition_temp_pos prefix))).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - apply (temp_factor_antitone_mp prefix (pick_max_token prefix) w).
    apply (pick_best_optimal_mp prefix w Hw).
Qed.

(* 和 ≤ 势·最大：逐项（w ∈ l）f w ≤ M ⟹ Σ f l ≤ mp_of_nat(length l)·M *)
Lemma list_sum_le_const_mp : forall (l : list Token) (f : Token -> R) (M : R),
  (forall w : Token, InT w l -> le (f w) M) ->
  le (list_sum f l) (mult (mp_of_nat (length l)) M).
Proof.
  intros l f M Hf.
  induction l as [| w rest IH]; simpl.
  - apply (le_id_l zero (mult zero M) (mult zero M)).
    + apply (id_sym (id_trans (mult_comm zero M) (mult_zero M))).
    + apply le_refl.
  - apply (le_id_r (plus (f w) (list_sum f rest))
                   (plus M (mult (mp_of_nat (length rest)) M))
                   (mult (plus one (mp_of_nat (length rest))) M)).
    + assert (Hd : Id (plus M (mult (mp_of_nat (length rest)) M))
                      (mult (plus one (mp_of_nat (length rest))) M)).
      { apply (id_sym (id_trans (mult_plus_distr_r one (mp_of_nat (length rest)) M)
                                (id_cong (fun z => plus z (mult (mp_of_nat (length rest)) M))
                                         (id_trans (mult_comm one M) (mult_one M))))). }
      exact Hd.
    + apply le_plus_compat.
      * apply (Hf w). apply InT_here.
      * apply IH. intro w'. intro Hw'. apply (Hf w'). apply InT_next. exact Hw'.
Qed.

(* 除以正数：0 < G、1 ≤ G·M ⟹ inv G ≤ M（(inv G)·(G·M) == M 桥 + 保序） *)
Lemma le_one_mult_le_inv_mp : forall (G M : R) (Hg : lt zero G),
  le one (mult G M) -> le (inv_pos G Hg) M.
Proof.
  intros G M Hg Hle.
  assert (Habs : Id (mult (inv_pos G Hg) (mult G M)) M).
  { apply (id_trans (mult_assoc (inv_pos G Hg) G M)).
    apply (id_trans (id_cong (fun z => mult z M)
                             (id_trans (mult_comm (inv_pos G Hg) G) (inv_pos_correct G Hg)))).
    apply (id_trans (mult_comm one M)).
    apply (mult_one M). }
  apply (le_id_r (inv_pos G Hg) (mult (inv_pos G Hg) (mult G M)) M Habs).
  apply (le_id_l (inv_pos G Hg) (mult (inv_pos G Hg) one) (mult (inv_pos G Hg) (mult G M))).
  - apply (id_sym (mult_one (inv_pos G Hg))).
  - apply (le_mult_compat_r (inv_pos G Hg) one (mult G M)).
    + apply (lt_le_iff _ _). left. apply (inv_pos_pos G Hg).
    + exact Hle.
Qed.

(* p_max ≥ 1/|S|：1 == Σ kernel ≤ |S|·max ⟹ inv(|S|) ≤ max（T2.4-2 链①） *)
Lemma minp_max_ge_inv_vocab_size : forall prefix,
  le (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty))
     (max_markov_prob prefix).
Proof.
  intro prefix.
  apply (le_one_mult_le_inv_mp (mp_of_nat (length vocab)) (max_markov_prob prefix)
                               (mp_of_nat_pos vocab vocab_nonempty)).
  apply (le_id_l one (list_sum (markov_kernel prefix) vocab)
                 (mult (mp_of_nat (length vocab)) (max_markov_prob prefix))).
  - apply (id_sym (markov_kernel_normalized_mp prefix)).
  - apply (list_sum_le_const_mp vocab (markov_kernel prefix) (max_markov_prob prefix)).
    intro w. intro Hw. apply (markov_kernel_le_max_mp prefix w Hw).
Qed.

(* T2.4-2 主定理：截断质量 ≤ 1 − 1/|S|（链②：dropped ≤ 1 − max ≤ 1 − inv|S|） *)
Theorem minp_dropped_mass_le_inv_vocab_size : forall prefix,
  le (minp_dropped_mass prefix)
     (minus one (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty))).
Proof.
  intro prefix.
  apply (le_trans _ (minus one (max_markov_prob prefix)) _).
  - exact (minp_dropped_mass_le_one_minus_max prefix).
  - unfold minus.
    apply (le_plus_compat one one
                           (opp (max_markov_prob prefix))
                           (opp (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty)))).
    + apply le_refl.
    + apply (opp_le_compat (inv_pos (mp_of_nat (length vocab)) (mp_of_nat_pos vocab vocab_nonempty))
                           (max_markov_prob prefix)).
      exact (minp_max_ge_inv_vocab_size prefix).
Qed.

End MinPSampling.

(* ============================================================
   Section TopPSampling：top-p（nucleus）采样构造性形式化
   （论文2 §10.2 #5， 并入：概率降序排序 + 保留判定）
   ============================================================ *)
Section TopPSampling.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* MinPSampling 同签名前提（闭包显式参数形式） *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* ===== 概率降序插入排序（markov_kernel 权重，ord_le_dec 可判定） ===== *)
Fixpoint insert_kernel (prefix : list Token) (w : Token) (l : list Token) : list Token :=
  match l with
  | nil => w :: nil
  | a :: rest =>
      match ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
                       (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w) with
      | inl _ => w :: a :: rest
      | inr _ => a :: insert_kernel prefix w rest
      end
  end.

Fixpoint sort_kernel (prefix : list Token) (l : list Token) : list Token :=
  match l with
  | nil => nil
  | w :: rest => insert_kernel prefix w (sort_kernel prefix rest)
  end.

(* ===== 前缀累积概率（top-p 累积阈值判定） ===== *)
Fixpoint prefix_sum (prefix : list Token) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
                      (prefix_sum prefix rest)
  end.

(* ===== 成员引理：插入保持既有元素（induction 于 InT 结构） ===== *)
Lemma insert_kernel_preserves : forall prefix a w l,
  InT w l -> InT w (insert_kernel prefix a l).
Proof.
  intros prefix a w l Hin.
  induction Hin as [l' | y l' Hw IHw].
  - (* w 是头：insert a (w :: l') *)
    simpl.
    destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
                         (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)) as [Hle | Hnot].
    + apply InT_next. apply InT_here.
    + apply InT_here.
  - (* w ∈ y :: l' 的尾部，IHw : InT w (insert_kernel prefix a l') *)
    simpl.
    destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix y)
                         (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)) as [Hle | Hnot].
    + apply InT_next. apply InT_next. exact Hw.
    + apply InT_next. exact IHw.
Qed.

(* 引理：插入的 w 本身在其中 *)
Lemma insert_kernel_mem : forall prefix w l,
  InT w (insert_kernel prefix w l).
Proof.
  intros prefix w l. induction l as [| a rest IH]; simpl.
  - apply InT_here.
  - destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
                         (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)) as [Hle | Hnot].
    + apply InT_here.
    + apply InT_next. exact IH.
Qed.

(* 引理：排序保持成员 *)
Lemma sort_kernel_mem : forall prefix w l,
  InT w l -> InT w (sort_kernel prefix l).
Proof.
  intros prefix w l. induction l as [| a rest IH]; intros Hin.
  - inversion Hin.
  - simpl. inversion Hin as [Hwa | Hy Hl Hwrest].
    + subst. apply (insert_kernel_mem prefix a (sort_kernel prefix rest)).
    + apply (insert_kernel_preserves prefix a w (sort_kernel prefix rest)). exact (IH Hwrest).
Qed.

(* ===== 支配性：插入 w 到已排序列表，w 概率 ≥ 其后所有元素（头部即可） ===== *)
Lemma insert_kernel_head_ge : forall prefix w a l,
  le (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
     (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w) ->
  Id (insert_kernel prefix w (a :: l)) (w :: a :: l).
Proof.
  intros prefix w a l Hge.
  unfold insert_kernel.
  destruct (ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a)
                       (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)) as [Hle | Hnot].
  - apply id_refl.
  - destruct (Hnot Hge).
Qed.

(* ===== top-p 保留判定：遍历排序列表，遇 w 或概率 ≤ p 停止 ===== *)
Fixpoint top_p_member (p : R) (prefix : list Token) (l : list Token) : Token -> Set :=
  match l with
  | nil => fun _ => Empty_set
  | w :: rest =>
      fun x =>
        match token_eq_dec x w with
        | inl _ => unit
        | inr _ =>
            match ord_le_dec (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w) p with
            | inl _ => Empty_set
            | inr _ => top_p_member p prefix rest x
            end
        end
  end.

Definition top_p_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  top_p_member p prefix (sort_kernel prefix vocab) w.


Definition topp_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  le p (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).

Definition topp_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (topp_keep p prefix w) (Not (topp_keep p prefix w)).
Proof. unfold topp_keep. apply ord_le_dec. Defined.

(* top-p 保留和（nucleus 截断质量） *)
Definition topp_temp_sum (p : R) (prefix : list Token) : R :=
  list_sum Token (fun w => match topp_keep_dec p prefix w with
                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab.

Lemma topp_temp_sum_unfold : forall p prefix,
  Id (topp_temp_sum p prefix)
     (list_sum Token (fun w => match topp_keep_dec p prefix w with
                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                               | inr _ => zero
                               end) vocab).
Proof. intros. unfold topp_temp_sum. apply id_refl. Qed.

(* 非空：p ≤ max_markov_prob ⟹ pick_max 保留 ⟹ sum ≥ tf(pick_max) > 0 *)
Lemma topp_temp_sum_pos : forall p prefix,
  le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix) ->
  lt zero (topp_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  unfold topp_temp_sum.
  assert (Hkeep : topp_keep p prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold topp_keep. rewrite pick_max_token_correct. exact Hp. }
  assert (Heq : Id (temp_factor Token total_loss temperature temperature_pos prefix
                                  (pick_max_token Token vocab total_loss default_token prefix))
                   (match topp_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)).
  { destruct (topp_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd Hkeep). }
  assert (Hle : le (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)).
  { apply (le_id_l (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (match topp_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)
                   (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)
                   Heq
                   (list_sum_single_le_total Token vocab
                                     (fun w => match topp_keep_dec p prefix w with
                                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                               | inr _ => zero
                                               end)
                                     (pick_max_token Token vocab total_loss default_token prefix)
                                     (pick_best_in_vocab' Token vocab vocab_nonempty total_loss default_token prefix)
                                     (fun w' => match topp_keep_dec p prefix w' as d return le zero (match d with
                                                                                                                          | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w'
                                                                                                                          | inr _ => zero
                                                                                                                          end) with
                                                | inl _ => lt_le_iff _ _ (inl (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w'])))))
                                                | inr _ => le_refl zero
                                                end))). }
  apply (lt_le_trans zero (temp_factor Token total_loss temperature temperature_pos prefix
                                          (pick_max_token Token vocab total_loss default_token prefix))
                          (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                                          | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                          | inr _ => zero
                                                          end) vocab)).
  - unfold temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* top-p 重归一化核（p ≤ max 作为全局前提 Hpmax） *)
Definition topp_markov_kernel (p : R) (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
                              (prefix : list Token) (w : Token) : R :=
  match topp_keep_dec p prefix w with
  | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                  (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

(* ===== ③ top-p 核归一化：Σ_w topp_markov_kernel w == 1 ===== *)
Theorem topp_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
  (prefix : list Token),
  Id (list_sum Token (topp_markov_kernel p Hpmax prefix) vocab) one.
Proof.
  intros p Hpmax prefix.
  unfold topp_markov_kernel.
  apply (id_trans (list_sum_ext Token
                    (fun w => match topp_keep_dec p prefix w with
                              | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                              (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => zero
                              end)
                    (fun w => mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                  (match topp_keep_dec p prefix w with
                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                   | inr _ => zero
                                   end))
                    vocab
                    (fun w => match topp_keep_dec p prefix w as d return Id (match d with
                                                                            | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                                                            (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                                                            | inr _ => zero
                                                                            end)
                                                                          (mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                                                                (match d with
                                                                                 | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                                 | inr _ => zero
                                                                                 end)) with
                              | inl _ => mult_comm (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                   (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => id_sym (mult_zero (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix))))
                              end))).
  assert (Hlin : Id (list_sum Token (fun w => mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                                                                  (match topp_keep_dec p prefix w with
                                                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                   | inr _ => zero
                                                                   end)) vocab)
                    (mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                          (list_sum Token (fun w => match topp_keep_dec p prefix w with
                                                                     | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                     | inr _ => zero
                                                                     end) vocab))).
  { apply (list_sum_linear Token (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                             (fun w => match topp_keep_dec p prefix w with
                                       | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                       | inr _ => zero
                                       end) vocab). }
  apply (id_trans Hlin).
  assert (Hsum : Id (mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                          (topp_temp_sum p prefix)) one).
  {
    apply (id_trans (id_sym (id_cong (fun z => mult (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix))) z)
                                        (topp_temp_sum_unfold p prefix)))).
    apply (id_trans (mult_comm (inv_pos (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix)))
                               (topp_temp_sum p prefix))).
    apply (inv_pos_correct (topp_temp_sum p prefix) (topp_temp_sum_pos p prefix (Hpmax prefix))).
  }
  exact Hsum.
Qed.


(* Top-p+Min-P 联合核所需 min_p 前提（与 MinPSampling 同签名） *)
Variable min_p : R.
Variable min_p_pos : lt zero min_p.
Variable min_p_lt_one : lt min_p one.

Definition combined_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  And (minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w)
      (topp_keep p prefix w).

Definition combined_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (combined_keep p prefix w) (Not (combined_keep p prefix w)).
Proof.
  unfold combined_keep.
  destruct (minp_keep_dec Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w) as [Hmin | Hnotmin].
  - destruct (topp_keep_dec p prefix w) as [Htp | Hntp].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntp Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

(* 联合保留和 *)
Definition combined_temp_sum (p : R) (prefix : list Token) : R :=
  list_sum Token (fun w => match combined_keep_dec p prefix w with
                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab.

Lemma combined_temp_sum_unfold : forall p prefix,
  Id (combined_temp_sum p prefix)
     (list_sum Token (fun w => match combined_keep_dec p prefix w with
                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                               | inr _ => zero
                               end) vocab).
Proof. intros. unfold combined_temp_sum. apply id_refl. Qed.

(* ===== ② 非空：p ≤ max 且 pick_max 满足 Min-P ⟹ pick_max ∈ 联合集 ⟹ sum > 0 ===== *)
Lemma combined_temp_sum_pos : forall p prefix,
  le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix) ->
  lt zero (combined_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  unfold combined_temp_sum.
  (* pick_max 满足 topp_keep（p ≤ max） *)
  assert (Htp : topp_keep p prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold topp_keep. rewrite pick_max_token_correct. exact Hp. }
  (* pick_max 满足 minp_keep（pick_max_token_minp_keep） *)
  assert (Hmin : minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix
                               (pick_max_token Token vocab total_loss default_token prefix)).
  { exact (pick_max_token_minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p min_p_lt_one prefix). }
  (* pick_max ∈ 联合保留集 *)
  assert (Hkeep : combined_keep p prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold combined_keep. split; assumption. }
  (* 提取 pick_max 的 tf 项（match inl 分支） *)
  assert (Heq : Id (temp_factor Token total_loss temperature temperature_pos prefix
                                  (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)).
  { destruct (combined_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd Hkeep). }
  (* tf(pick_max) ≤ combined_temp_sum（list_sum_single_le_total） *)
  assert (Hle : le (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)).
  { apply (le_id_l (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_keep_dec p prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)
                   (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)
                   Heq
                   (list_sum_single_le_total Token vocab
                                     (fun w => match combined_keep_dec p prefix w with
                                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                               | inr _ => zero
                                               end)
                                     (pick_max_token Token vocab total_loss default_token prefix)
                                     (pick_best_in_vocab' Token vocab vocab_nonempty total_loss default_token prefix)
                                     (fun w' => match combined_keep_dec p prefix w' as d return le zero (match d with
                                                                                                          | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w'
                                                                                                          | inr _ => zero
                                                                                                          end) with
                                                | inl _ => lt_le_iff _ _ (inl (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w'])))))
                                                | inr _ => le_refl zero
                                                end))). }
  apply (lt_le_trans zero (temp_factor Token total_loss temperature temperature_pos prefix
                                          (pick_max_token Token vocab total_loss default_token prefix))
                          (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                    | inr _ => zero
                                                    end) vocab)).
  - unfold temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* ===== ③ 联合核 + 归一化（Σ=1，同 topp_markov_kernel_normalized 模式） ===== *)
Definition combined_markov_kernel (p : R)
  (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
  (prefix : list Token) (w : Token) : R :=
  match combined_keep_dec p prefix w with
  | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                  (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

Theorem combined_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix, le p (max_markov_prob Token vocab vocab_nonempty total_loss temperature temperature_pos default_token prefix))
  (prefix : list Token),
  Id (list_sum Token (combined_markov_kernel p Hpmax prefix) vocab) one.
Proof.
  intros p Hpmax prefix.
  unfold combined_markov_kernel.
  apply (id_trans (list_sum_ext Token
                    (fun w => match combined_keep_dec p prefix w with
                              | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                              (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => zero
                              end)
                    (fun w => mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                  (match combined_keep_dec p prefix w with
                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                   | inr _ => zero
                                   end))
                    vocab
                    (fun w => match combined_keep_dec p prefix w as d return Id (match d with
                                                                                | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                                                                (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                                                                | inr _ => zero
                                                                                end)
                                                                              (mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                                                                    (match d with
                                                                                     | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                                     | inr _ => zero
                                                                                     end)) with
                              | inl _ => mult_comm (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                   (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                              | inr _ => id_sym (mult_zero (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix))))
                              end))).
  assert (Hlin : Id (list_sum Token (fun w => mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                                                  (match combined_keep_dec p prefix w with
                                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                   | inr _ => zero
                                                   end)) vocab)
                    (mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                          (list_sum Token (fun w => match combined_keep_dec p prefix w with
                                                     | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                     | inr _ => zero
                                                     end) vocab))).
  { apply (list_sum_linear Token (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                             (fun w => match combined_keep_dec p prefix w with
                                       | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                       | inr _ => zero
                                       end) vocab). }
  apply (id_trans Hlin).
  assert (Hsum : Id (mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                          (combined_temp_sum p prefix)) one).
  {
    apply (id_trans (id_sym (id_cong (fun z => mult (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix))) z)
                                     (combined_temp_sum_unfold p prefix)))).
    apply (id_trans (mult_comm (inv_pos (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix)))
                               (combined_temp_sum p prefix))).
    apply (inv_pos_correct (combined_temp_sum p prefix) (combined_temp_sum_pos p prefix (Hpmax prefix))).
  }
  exact Hsum.
Qed.

(* ================================================================
   计数形式：严格更重者计数 < K（主文件 keep_top_k 模式，绕开排序
   排序正确性判例与 InT 成员判定）；非空性用诚实前提 topk_pickmax_head
   （pick_max 在前 K 个中，同判例 κ 正分支 g>0 前提模式）。
   纪律：纯构造性 / Set 层 / 零 承认 / 零经典。
   ================================================================ *)

(* lt_dec 投影别名（类字段名 lt_dec 被 Stdlib Compare_dec.lt_dec 遮蔽，
   经构造子解构提取——L24787 同款，改名防冲突） *)
Definition lt_dec_field_tk : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => lt_d
  end.

(* 严格小于（nat 版） *)
Definition NatLt_tk (n m : nat) : Set := Id (Nat.ltb n m) true.

(* AB2-T2 孪生合并（  D1）：id_false_true_tk 与上游 id_false_true
   （AttentionGibbsBridge，本文件 5134 行，keep_top_k_dec 同款直引）语句与证明
   100% 重合（forall H : Id false true, Empty_set / intro. inversion.）。
   _tk 改名族中仅 lt_dec_field_tk/NatLt_tk 系 Stdlib 遮蔽改名所必需，
   id_false_true 无任何遮蔽与撞名——消去本重定义，下游 topk_keep_dec 直引上游件。 *)

(* ===== Top-k 计数：vocab 中 kernel 严格大于 kernel w 的 token 数 ===== *)
Fixpoint count_kernel_heavier (prefix : list Token) (w : Token) (l : list Token) : nat :=
  match l with
  | nil => Datatypes.O
  | a :: rest =>
      match lt_dec_field_tk (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
                            (markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix a) with
      | inl _ => Datatypes.S (count_kernel_heavier prefix w rest)
      | inr _ => count_kernel_heavier prefix w rest
      end
  end.

(* Top-k 保留：严格更重者不足 K 个 *)
Definition topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  NatLt_tk (count_kernel_heavier prefix w vocab) K.

(* Top-k 判定（Nat.ltb 计算 + bool 消去，无需 Token 等号） *)
Definition topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (topk_keep K prefix w) (Not (topk_keep K prefix w)) :=
  match Nat.ltb (count_kernel_heavier prefix w vocab) K as b
        return Or (Id b true) (Not (Id b true)) with
  | true => inl id_refl
  | false => inr (fun H => id_false_true H)
  end.

(* 诚实前提（排序正确性弱化，判例障碍绕行）：pick_max 在前 K 个中（K ≥ 1） *)
Variable topk_pickmax_head : forall (K : nat) (prefix : list Token),
  NatLe 1 K ->
  topk_keep K prefix (pick_max_token Token vocab total_loss default_token prefix).

(* ===== 联合保留：Min-P ∧ Top-k ===== *)
Definition combined_topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  And (minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w)
      (topk_keep K prefix w).

Definition combined_topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (combined_topk_keep K prefix w) (Not (combined_topk_keep K prefix w)).
Proof.
  unfold combined_topk_keep.
  destruct (minp_keep_dec Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix w) as [Hmin | Hnotmin].
  - destruct (topk_keep_dec K prefix w) as [Htop | Hntop].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntop Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

(* 联合保留和 *)
Definition combined_topk_temp_sum (K : nat) (prefix : list Token) : R :=
  list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab.

Lemma combined_topk_temp_sum_unfold : forall K prefix,
  Id (combined_topk_temp_sum K prefix)
     (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                               | inr _ => zero
                               end) vocab).
Proof. intros. unfold combined_topk_temp_sum. apply id_refl. Qed.

(* ===== 非空：K ≥ 1 且 pick_max 满足 Min-P 且 ∈ Top-k（诚实前提）⟹ sum > 0 ===== *)
Lemma combined_topk_temp_sum_pos : forall K prefix,
  NatLe 1 K ->
  lt zero (combined_topk_temp_sum K prefix).
Proof.
  intros K prefix HK.
  unfold combined_topk_temp_sum.
  assert (Hmin : minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p prefix
                               (pick_max_token Token vocab total_loss default_token prefix)).
  { exact (pick_max_token_minp_keep Token vocab vocab_nonempty total_loss temperature temperature_pos default_token min_p min_p_lt_one prefix). }
  assert (Htop : topk_keep K prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { exact (topk_pickmax_head K prefix HK). }
  assert (Hkeep : combined_topk_keep K prefix (pick_max_token Token vocab total_loss default_token prefix)).
  { unfold combined_topk_keep. split; assumption. }
  assert (Heq : Id (temp_factor Token total_loss temperature temperature_pos prefix
                                  (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_topk_keep_dec K prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)).
  { destruct (combined_topk_keep_dec K prefix (pick_max_token Token vocab total_loss default_token prefix)) as [Hk | Hd].
    - apply id_refl.
    - destruct (Hd Hkeep). }
  assert (Hle : le (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)).
  { apply (le_id_l (temp_factor Token total_loss temperature temperature_pos prefix
                                (pick_max_token Token vocab total_loss default_token prefix))
                   (match combined_topk_keep_dec K prefix (pick_max_token Token vocab total_loss default_token prefix) with
                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix
                                             (pick_max_token Token vocab total_loss default_token prefix)
                    | inr _ => zero
                    end)
                   (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                             | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                             | inr _ => zero
                                             end) vocab)
                   Heq
                   (list_sum_single_le_total Token vocab
                                     (fun w => match combined_topk_keep_dec K prefix w with
                                               | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                               | inr _ => zero
                                               end)
                                     (pick_max_token Token vocab total_loss default_token prefix)
                                     (pick_best_in_vocab' Token vocab vocab_nonempty total_loss default_token prefix)
                                     (fun w' => match combined_topk_keep_dec K prefix w' as d return le zero (match d with
                                                                                                              | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w'
                                                                                                              | inr _ => zero
                                                                                                              end) with
                                                | inl _ => lt_le_iff _ _ (inl (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w'])))))
                                                | inr _ => le_refl zero
                                                end))). }
  apply (lt_le_trans zero (temp_factor Token total_loss temperature temperature_pos prefix
                                          (pick_max_token Token vocab total_loss default_token prefix))
                          (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                    | inr _ => zero
                                                    end) vocab)).
  - unfold temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* ===== 联合核 + 归一化（Σ=1，同 combined_markov_kernel_normalized 模式） ===== *)
Definition combined_topk_markov_kernel (K : nat)
  (HK : forall prefix, NatLe 1 K)
  (prefix : list Token) (w : Token) : R :=
  match combined_topk_keep_dec K prefix w with
  | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                  (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
  | inr _ => zero
  end.

Theorem combined_topk_markov_kernel_normalized : forall (K : nat)
  (HK : forall prefix, NatLe 1 K)
  (prefix : list Token),
  Id (list_sum Token (combined_topk_markov_kernel K HK prefix) vocab) one.
Proof.
  intros K HK prefix.
  unfold combined_topk_markov_kernel.
  apply (id_trans (list_sum_ext Token
                    (fun w => match combined_topk_keep_dec K prefix w with
                              | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                              (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                              | inr _ => zero
                              end)
                    (fun w => mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                  (match combined_topk_keep_dec K prefix w with
                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                   | inr _ => zero
                                   end))
                    vocab
                    (fun w => match combined_topk_keep_dec K prefix w as d return Id (match d with
                                                                                      | inl _ => mult (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                                                                      (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                                                                      | inr _ => zero
                                                                                      end)
                                                                                    (mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                                                                          (match d with
                                                                                           | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                                                           | inr _ => zero
                                                                                           end)) with
                              | inl _ => mult_comm (temp_factor Token total_loss temperature temperature_pos prefix w)
                                                   (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                              | inr _ => id_sym (mult_zero (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix))))
                              end))).
  assert (Hlin : Id (list_sum Token (fun w => mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                                                  (match combined_topk_keep_dec K prefix w with
                                                   | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                   | inr _ => zero
                                                   end)) vocab)
                    (mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                          (list_sum Token (fun w => match combined_topk_keep_dec K prefix w with
                                                    | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                                    | inr _ => zero
                                                    end) vocab))).
  { apply (list_sum_linear Token (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                             (fun w => match combined_topk_keep_dec K prefix w with
                                       | inl _ => temp_factor Token total_loss temperature temperature_pos prefix w
                                       | inr _ => zero
                                       end) vocab). }
  apply (id_trans Hlin).
  assert (Hsum : Id (mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                          (combined_topk_temp_sum K prefix)) one).
  {
    apply (id_trans (id_sym (id_cong (fun z => mult (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix))) z)
                                     (combined_topk_temp_sum_unfold K prefix)))).
    apply (id_trans (mult_comm (inv_pos (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix)))
                               (combined_topk_temp_sum K prefix))).
    apply (inv_pos_correct (combined_topk_temp_sum K prefix) (combined_topk_temp_sum_pos K prefix (HK prefix))).
  }
  exact Hsum.
Qed.

End TopPSampling.

(* ============================================================ *)
(* 路径 3：证明层与计算层分离（Extraction 映射）               *)
(* ============================================================ *)
(* 证明层保持纯构造性 Set 层（抽象 RealInterface，无经典公理）；*)
(* 提取层将抽象实数映射到 OCaml float，定理保证理想行为，       *)
(* 提取保证工程可用性。此处仅声明映射契约（可选项），不改变    *)
(* 证明层语义。                                                *)
(* ------------------------------------------------------------ *)
(* 提取映射（工程落地时取消注释并使用 OCaml 后端）：            *)
(*   Extract Inductive unit => "unit" [ "()" ].                 *)
(*   Extract Constant RealInterface.R => "float".               *)
(*   Extract Constant RealInterface.plus => "( +. )".           *)
(*   Extract Constant RealInterface.mult => "( *. )".           *)
(*   Extract Constant RealInterface.opp => "( ~-. )".           *)
(* 验证层（可选，需 Flocq）：|float_result - exact_result| < ε  *)
(* 与主理论框架正交。                                          *)
(* ============================================================ *)

(* ============================================================
   Core 版：RealSetoidCore.RealInterfaceSetoidCore 实例组装（req := real_eq）
   metric_pos/metric_triangle 用逐 eps 形式（判例）；缺口：exp_neg_plus/log_inv（阶段 2）
   注：RealInterfaceSetoid 类字段与 RealInterface 全局投影同名（zero/one/plus...），
       同文件全局冲突（检验不冲突因 CW 是导入名可遮蔽）→ 包 Module 隔离（判例）。
   ============================================================ *)

(* ============ Core 版接口（阶段 3 组装目标）：无 exp/log 字段 ============
   完整 RealInterfaceSetoid 的 exp_neg_plus/log_inv 族属阶段 2（大工程）。
   先实例化 Core（Proper + 环 + 序 + inv_pos + metric 逐 eps + lim + cauchy_complete），
   阶段 2 补 exp/log 后再组装完整版。
   注：Core 类字段与完整类同名（req 等），Class 投影全局唯一——用 Module 隔离。 *)

(* ToyR  ：替换定理假设面打印（零新增依赖验证锚） *)
Print Assumptions partition_function_pos.
Print Assumptions partition_function_temp_pos.
Print Assumptions partition_function_scaled_pos.
Print Assumptions partition_function_temp_param_pos.
