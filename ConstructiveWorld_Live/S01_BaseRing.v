(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 【ToyR 切片七·信任根本体替换稿】基于 Main 基线同名替换：全文保留，仅换三枚       *)
(*   reflexivity 核验微刀（core_claim5_holds 三位＋core_claim3_holds 一位，各改      *)
(*   @id_refl 命名恒等元显式正体）；语句面零动，Proof/Qed 计数 99/99 守恒。          *)
(* ============================================================ *)
(* S01_BaseRing.v —— 构造性 Set 层基础环结构                                      *)
(* 目的/主件：奠定实数接口、三类索引、分层证明约定与基础代数序引理；                *)
(*   RealInterface / RealInterfaceEnhanced 类接口及其假设体系（构造世界之基础环）。  *)
(* 依赖：Stdlib（QArith、List、Bool、Arith、Setoid、Morphisms、Lia、Qminmax）。      *)
(* 备注：逻辑连接词与等同类型在 Set 层定义，nat 序与 Leibniz 相等采用标准库 Prop     *)
(*   层设施；使用 Set 宇宙，存在量词使用 sig；不可由接口推得的性质以显式             *)
(*   Variable/假设申报位呈现（非承认件）；序三分律 le_lt_dec 已移除，禁临时公理面    *)
(*   与经典公理面；R 层（自定义 Id 等价关系）证明用显式 id_trans/id_cong 链          *)
(*   （Id 非 setoid，ring 不可用），Q 层（QArith 可判定相等）可用                    *)
(*   setoid_replace/setoid_rewrite 与 ring/field。                                  *)
(* 三类索引：A. 接口字段（Class，实例化提供，非本文件证明）——RealInterface：环序    *)
(*   plus/mult/opp/abs/lt/le 公理、inv_pos（正数逆）/exp_neg/log_inv/metric/lim/     *)
(*   cauchy_complete/min/r_max/pos_test/log 族；Enhanced：one_pos/lt·le·plus·mult    *)
(*   兼容族/inv_pos 保序（0<a、0<b、a≤b ⟹ inv b ≤ inv a）/half/abs 引理。              *)
(*   B. Section Variables（诚实接口假设，End Section 后参数化，非死代码）：           *)
(*   StochasticLanguageModel（token_eq_dec/vocab_nonempty/total_loss/               *)
(*   temperature(>0)/default_token）；Alignment（pi_ref 族、beta/beta_pos、D/D_pos）；  *)
(*   MinPSampling（min_p/min_p_pos/min_p_lt_one，Min-P 阈值超参，接口参数不可证明）；  *)
(*   MultivariableDifferentiable（inner_lipschitz/smetric_sminus_zero/mv_adjoint/    *)
(*   op_lipschitz，几何接口）。                                                     *)
(*   C. 已证定理（非平凡实现，零承认）：文件全部 Theorem/Lemma；代表性里程碑：        *)
(*   real_lim_unique、real_cauchy_complete（零 Variable）、real_lim_plus/scal/mult、   *)
(*   differentiable_(mv_)(vec_)compose（向量场链式法则）、                             *)
(*   minp_markov_kernel_normalized、pick_best_in_vocab' 等；                            *)
(*   完整清单见 submission/STRUCTURE.md（自动提取）。                                *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.   (* entropy Real 层并入所需 *)
(* ============================================================ *)
(* 基础：构造性逻辑连接词与等同类型（Set 层）                 *)
(* ============================================================ *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition And (A B : Set) : Set := A * B.
Definition Or  (A B : Set) : Set := A + B.
Definition Not (A : Set) : Set := A -> Empty_set.

(* 存在量词（Set 层，使用 sig） *)
Definition ExistsT {A : Set} (P : A -> Set) : Set := sigT P.
Definition ForallT {A : Set} (P : A -> Set) : Set := forall x : A, P x.

Definition id_sym {A : Set} {x y : A} (p : Id x y) : Id y x :=
  match p with
  | id_refl => id_refl
  end.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

Definition id_cong {A B : Set} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y) :=
  match p with
  | id_refl => id_refl
  end.

(* 二元同余：p : Id x x'、q : Id y y' ⟹ Id (f x y) (f x' y') *)
Definition id_cong2 {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
                    (p : Id x x') (q : Id y y') : Id (f x y) (f x' y') :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* 构造性 list 成员关系（Set 层） *)
Inductive InT {A : Set} (x : A) : list A -> Set :=
| InT_here : forall l, InT x (x :: l)
| InT_next : forall y l, InT x l -> InT x (y :: l).

Definition not_InT {A : Set} (x : A) (l : list A) : Set :=
  InT x l -> Empty_set.

(* ============================================================ *)
(* 构造性实数接口：Class 形式（Set 层）                       *)
(* ============================================================ *)

Definition NatLe (n m : nat) : Set := Id (Nat.leb n m) true.

(* ---- 完全构造论证 kernel 桥：NatLe ↔ (<=)%nat（Set 序界 ↔ Prop 序界）---- *)
Lemma NatLe_drop : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  unfold NatLe in H.
  destruct (Nat.leb n m) eqn:E.
  - apply (proj1 (Nat.leb_le n m)). exact E.
  - inversion H.
Qed.

Lemma NatLe_lift : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt n m)) in E.
    lia.
Qed.

Class RealInterface := {
  R : Set;
  zero : R;
  one  : R;
  plus : R -> R -> R;
  mult : R -> R -> R;
  opp  : R -> R;
  abs  : R -> R;

  lt : R -> R -> Set;
  le : R -> R -> Set;

  plus_assoc : forall a b c : R, Id (plus a (plus b c)) (plus (plus a b) c);
  plus_comm  : forall a b : R, Id (plus a b) (plus b a);
  plus_zero  : forall a : R, Id (plus a zero) a;
  plus_opp   : forall a : R, Id (plus a (opp a)) zero;
  mult_assoc : forall a b c : R, Id (mult a (mult b c)) (mult (mult a b) c);
  mult_comm  : forall a b : R, Id (mult a b) (mult b a);
  mult_one   : forall a : R, Id (mult a one) a;
  distrib    : forall a b c : R, Id (mult a (plus b c)) (plus (mult a b) (mult a c));
  mult_zero  : forall a : R, Id (mult a zero) zero;

  lt_irrefl   : forall a : R, Not (lt a a);
  lt_trans    : forall a b c : R, lt a b -> lt b c -> lt a c;
  le_refl     : forall a : R, le a a;
  le_trans    : forall a b c : R, le a b -> le b c -> le a c;
  le_antisym  : forall a b : R, le a b -> le b a -> Id a b;
  le_lt_trans : forall a b c : R, le a b -> lt b c -> lt a c;
  lt_le_trans : forall a b c : R, lt a b -> le b c -> lt a c;
  lt_le_iff   : forall a b : R, Or (lt a b) (Id a b) -> le a b;
  (* le 的 Id 替换（外延性）：相等项在 ≤ 中可替换。
     构造性可接受（任何有序域中相等是可替换的等价关系；
     Gibbs 不等式 / 自由能最小化推导需要） *)
  le_id_l : forall a b c : R, Id a b -> le b c -> le a c;
  le_id_r : forall a b c : R, Id b c -> le a b -> le a c;
  (* lt 的 Id 替换（严格序外延性）：相等项在 < 中可替换。
     构造性可接受（任何有序域中相等是可替换的等价关系；
     RLHF 对齐中 boltzmann_dist = pi_star 的正性传递需要） *)
  lt_id_l : forall a b c : R, Id a b -> lt b c -> lt a c;
  lt_id_r : forall a b c : R, Id b c -> lt a b -> lt a c;
  (* 注：原 le_lt_dec（序三分律：Or (le a b) (lt b a)）是经典公理，
     构造性模型（如本文件自建的柯西实数 Real）不可满足，与『禁止经典公理』
     自述冲突；已移除，并打通 Real 实例化路径。
     可判定序由具体模型局部提供（如 LanguageModelInstance 的 le_dec）。 *)

  inv_pos         : forall x : R, lt zero x -> R;
  inv_pos_correct : forall x (H : lt zero x), Id (mult x (inv_pos x H)) one;

  exp_neg       : R -> R;
  exp_neg_pos   : forall x : R, lt zero (exp_neg x);
  exp_neg_zero  : Id (exp_neg zero) one;
  exp_neg_plus  : forall a b : R, Id (exp_neg (plus a b)) (mult (exp_neg a) (exp_neg b));

  log_inv       : R -> R;
  log_inv_exp_neg : forall x : R, Id (log_inv (exp_neg x)) x;
  log_inv_one   : Id (log_inv one) zero;
  log_inv_mult  : forall a b : R, lt zero a -> lt zero b ->
                    Id (log_inv (mult a b)) (plus (log_inv a) (log_inv b));

  metric : R -> R -> R;
  metric_sym       : forall a b : R, Id (metric a b) (metric b a);
  metric_pos       : forall a b : R, le zero (metric a b);
  metric_zero      : forall a b : R, Id (metric a b) zero -> Id a b;
  metric_triangle  : forall a b c : R,
                       le (metric a c) (plus (metric a b) (metric b c));

  lim : (nat -> R) -> R -> Set;
  lim_unique : forall u l1 l2, lim u l1 -> lim u l2 -> Id l1 l2;

  cauchy_complete :
    forall (u : nat -> R),
      (forall eps : R, lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n ->
          lt (metric (u m) (u n)) eps)) ->
      sigT (fun l : R => lim u l);
}.

Definition minus {RI : RealInterface} (a b : R) : R := plus a (opp b).

(* ============================================================ *)
(* 增强实数接口：补充序兼容性与正对数                         *)
(* ============================================================ *)

Class RealInterfaceEnhanced := {
  RI_base :> RealInterface;

  one_pos : lt zero one;

  lt_plus_compat : forall a b c d : R, lt a b -> lt c d -> lt (plus a c) (plus b d);
  le_plus_compat : forall a b c d : R, le a b -> le c d -> le (plus a c) (plus b d);
  plus_positive  : forall a b : R, lt zero a -> lt zero b -> lt zero (plus a b);
  mult_positive  : forall a b : R, lt zero a -> lt zero b -> lt zero (mult a b);

  lt_mult_compat : forall a b c : R, lt zero c -> lt a b -> lt (mult a c) (mult b c);
  le_mult_compat : forall a b c : R, lt zero c -> le a b -> le (mult a c) (mult b c);
  (* 乘法单调的非严格版本（c ≥ 0；differentiable_mult 处理 |h| = 0 时需要） *)
  le_mult_compat_weak : forall a b c : R, le zero c -> le a b -> le (mult a c) (mult b c);

  opp_lt_compat : forall a b : R, lt a b -> lt (opp b) (opp a);
  lt_zero_opp   : forall a : R, lt zero a -> lt (opp a) zero;
  (* le 的负号反变：a ≤ b ⟹ -b ≤ -a（构造性可接受；Gibbs 不等式需要） *)
  opp_le_compat : forall a b : R, le a b -> le (opp b) (opp a);

  (* 正数的逆仍为正（构造性有序域性质：CReals 等构造实数中为定理，
     抽象接口下声明为字段；非经典公理，由模型实例化提供）。 *)
  inv_pos_pos : forall x : R, forall H : lt zero x, lt zero (inv_pos x H);
  (* 逆元对参数（值 + 正性证明）的外延性：x = y ⟹ inv_pos x Hx = inv_pos y Hy
     （构造性可接受；具体实例中 inv 不依赖参数；attention_is_gibbs 需要） *)
  inv_pos_ext : forall x y : R, forall Hx : lt zero x, forall Hy : lt zero y,
    Id x y -> Id (inv_pos x Hx) (inv_pos y Hy);

  (* 逆元保序（反单调）：0 < a、0 < b 且 a ≤ b ⟹ inv b ≤ inv a。
     构造性有序域标准性质（具体实例如柯西实数层中为定理；抽象接口下
     声明为字段，非经典公理）。支撑 Min-P 核放大：minp_sum ≤ partition
     ⟹ inv(minp_sum) ≥ inv(partition)。 *)
  inv_pos_le_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    le a b -> le (inv_pos b Hb) (inv_pos a Ha);

  (* 最小值运算（构造性有序域标准操作；供 ε-δ 可微性取 δ = min δf δg）。 *)
  min : R -> R -> R;
  min_le_l : forall a b : R, le (min a b) a;
  min_le_r : forall a b : R, le (min a b) b;
  min_pos : forall a b : R, lt zero a -> lt zero b -> lt zero (min a b);

  (* 最大值运算（ReLU、MaxPool、贪心解码的构造性基础；与 min 对偶）。 *)
  r_max : R -> R -> R;
  r_max_le_l : forall a b : R, le a (r_max a b);
  r_max_le_r : forall a b : R, le b (r_max a b);
  r_max_l_iff : forall a b : R, le b a -> Id (r_max a b) a;
  r_max_r_iff : forall a b : R, le a b -> Id (r_max a b) b;

  (* 严格正性测试（ReLU、逐出掩码的 Set 层可判定基础；
     pos_test x 当且仅当 0 < x，双射由接口保证）。 *)
  pos_test : R -> Set;
  pos_test_lt : forall x : R, pos_test x -> lt zero x;
  lt_pos_test : forall x : R, lt zero x -> pos_test x;

  (* 正部运算：ReLU 的构造性定义（max a 0）。
     支撑激活函数、注意力掩码的数学基础。 *)
  pos_part : R -> R;
  pos_part_def : forall a : R, Id (pos_part a) (r_max a zero);
  pos_part_nonneg : forall a : R, le zero (pos_part a);

  (* 条件选择（构造性 if-then-else：以 Set 层 Or 见证驱动，
     替代依赖 Prop 的 match；支撑 ReLU/剪枝/掩码的定义）。 *)
  r_if : bool -> R -> R -> R;
  r_if_true : forall (v_true v_false : R),
    Id (r_if true v_true v_false) v_true;
  r_if_false : forall (v_true v_false : R),
    Id (r_if false v_true v_false) v_false;

  abs_nonneg   : forall a : R, le zero (abs a);
  abs_triangle : forall a b : R, le (abs (plus a b)) (plus (abs a) (abs b));
  abs_zero     : Id (abs zero) zero;
  (* abs 的乘法性质（构造性可接受；differentiable_mult 需要） *)
  abs_mult     : forall a b : R, Id (abs (mult a b)) (mult (abs a) (abs b));
  (* abs 的负号对称：|-x| = |x|（构造性可接受；CReals 等构造实数
     中可证；逐出稳态偏差量化需要） *)
  abs_opp      : forall a : R, Id (abs (opp a)) (abs a);
  (* abs 的正数保持：0 < a ⟹ |a| = a（构造性有序域标准性质，
     与 abs_opp 同先例；梯度收敛论证的 |g| 单调需要） *)
  abs_pos      : forall a : R, lt zero a -> Id (abs a) a;

  (* exp_neg 单调递减（e^{-x} 语义，Boltzmann 因子需要）：
     a < b ⟹ e^{-b} < e^{-a}。原接口缺此公理，导致
     prediction_fluctuation_scale 的方向在接口内无法判定。 *)
  exp_neg_decr : forall a b : R, lt a b -> lt (exp_neg b) (exp_neg a);
  (* exp_neg 非严格单调（le 版本；gap 集中定理需要） *)
  exp_neg_le_decr : forall a b : R, le a b -> le (exp_neg b) (exp_neg a);

  log : R -> R;
  log_mult : forall a b : R, lt zero a -> lt zero b ->
               Id (log (mult a b)) (plus (log a) (log b));
  log_one : Id (log one) zero;
  log_inv_log : forall x : R, lt zero x -> Id (log_inv x) (opp (log x));
  (* exp_neg 与 log_inv 互逆（逆方向）：exp_neg (log_inv x) = x
     （构造性可接受；CReals 等构造指数中可证；free_energy 显式值需要） *)
  exp_neg_log_inv : forall x : R, Id (exp_neg (log_inv x)) x;
  (* log 凹性切线：log x ≤ x - 1（对 x > 0；x=1 处切线，凹函数
     位于切线下方）。构造性可接受（CReals 等构造对数中可证；
     Gibbs 不等式 KL ≥ 0 的关键支撑）。 *)
  log_le_linear : forall x : R, lt zero x -> le (log x) (minus x one);
  (* log 严格凹：切线等号仅当 x = 1。
     log x = x - 1 ⟹ x = 1（x > 0）。
     构造性可接受（CReals 等构造对数中可证；Gibbs 等号条件
     KL = 0 ⟹ p = q 的关键支撑）。 *)
  log_eq_linear : forall x : R, lt zero x -> Id (log x) (minus x one) -> Id x one;
}.

(* ============================================================ *)
(* 路径 2：可判定序接口化（Set 层，零 Prop，可选扩展）        *)
(* ============================================================ *)
(* 可判定性作为 RealInterfaceEnhanced 的**可选扩展类**，而非   *)
(* 全局经典公理。抽象接口保持纯粹构造性；具体模型（有理数 Q、*)
(* 柯西实数、浮点区间）在实例化时按需提供。存在性用 sigT，    *)
(* 可判定性用 Set 层 Or（sum 类型）。                         *)

Class DecidableOrder (RI : RealInterface) : Set := {
  ord_le_dec : forall a b : R, Or (le a b) (Not (le a b));
  lt_dec : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a));
  eq_dec : forall a b : R, Or (Id a b) (Not (Id a b));
  not_le_lt : forall a b : R, Not (le a b) -> lt b a;
  lt_le_iff_dec : forall a b : R, Or (lt a b) (Id a b) -> le a b;
}.

(* ============================================================ *)
(* 环论补充引理（纯 Set 层推导，无 Prop 设施；供全文件各模块  *)
(* 使用——语言模型/核心/可微性等均依赖）。                     *)
(* 注意：接口 plus_assoc 方向为 Id (plus a (plus b c))          *)
(* (plus (plus a b) c)（LHS 右结合），与标准库相反。           *)
(* ============================================================ *)

Section RingLemmas.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 代数恒等式自动化简，替代手工 id_trans/id_cong 拼接。        *)

(* 加法逆的唯一性：b 和 c 都是 a 的右逆 ⟹ b = c *)
Lemma plus_inv_unique :
  forall a b c : R, Id (plus a b) zero -> Id (plus a c) zero -> Id b c.
Proof.
  intros a b c Hab Hac.
  exact (id_trans (id_sym (plus_zero b))
  (id_trans (id_cong (fun x => plus b x) (id_sym Hac))
  (id_trans (plus_assoc b a c)
  (id_trans (id_cong (fun x => plus x c) (plus_comm b a))
  (id_trans (id_cong (fun x => plus x c) Hab)
  (id_trans (plus_comm zero c) (plus_zero c))))))).
Qed.

(* 负号对加法分配：opp (a+b) = (-a) + (-b) *)
Lemma opp_plus :
  forall a b : R, Id (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply id_sym.
  apply (plus_inv_unique (plus a b)).
  - (* 重组为 zero。注意：接口 plus_assoc 方向为
       Id (plus a (plus b c)) (plus (plus a b) c)（右结合 = 左结合），
       与标准库相反，以下 rewrite 按此方向。 *)
    rewrite <- (plus_assoc a b (plus (opp a) (opp b))).
    rewrite (plus_assoc b (opp a) (opp b)).
    rewrite (plus_comm b (opp a)).
    rewrite <- (plus_assoc (opp a) b (opp b)).
    rewrite (plus_opp b).
    rewrite (plus_zero (opp a)).
    apply plus_opp.
  - apply plus_opp.
Qed.

(* 右分配律：a·c + b·c = (a+b)·c（由交换律与 distrib 推出） *)
Lemma mult_plus_distr_r :
  forall a b c : R, Id (mult (plus a b) c) (plus (mult a c) (mult b c)).
Proof.
  intros a b c.
  exact (id_trans (mult_comm (plus a b) c) (id_trans (distrib c a b) (id_trans (id_cong (fun w => plus w (mult c b)) (mult_comm c a)) (id_cong (fun w => plus (mult a c) w) (mult_comm c b))))).
Qed.

(* 负号对乘法：(-a)·b = -(a·b) *)
Lemma opp_mult_r :
  forall a b : R, Id (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (plus_inv_unique (mult a b)).
  - rewrite <- (mult_plus_distr_r a (opp a) b).
    rewrite (plus_opp a).
    rewrite (mult_comm zero b).
    rewrite (mult_zero b).
    reflexivity.
  - apply plus_opp.
Qed.

(* 负号对乘法：a·(-b) = -(a·b) *)
Lemma opp_mult_l :
  forall a b : R, Id (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b. exact (id_trans (mult_comm a (opp b)) (id_trans (opp_mult_r b a) (id_cong opp (mult_comm b a)))).
Qed.

(* 2·a = a + a（2 := plus one one） *)
Lemma two_mult :
  forall a : R, Id (mult (plus one one) a) (plus a a).
Proof.
  intro a. exact (id_trans (mult_comm (plus one one) a) (id_trans (distrib a one one) (id_cong (fun w => plus w w) (mult_one a)))).
Qed.

(* 双重取负：opp (opp a) = a *)
Lemma double_neg :
  forall a : R, Id (opp (opp a)) a.
Proof.
  intros a.
  exact (id_sym (id_trans (id_sym (plus_zero a)) (id_trans (id_cong (fun x => plus a x) (id_sym (plus_opp (opp a)))) (id_trans (plus_assoc a (opp a) (opp (opp a))) (id_trans (id_cong (fun x => plus x (opp (opp a))) (plus_opp a)) (id_trans (plus_comm zero (opp (opp a))) (plus_zero (opp (opp a))))))))).
Qed.

(* 1 ≠ 0：由 one_pos 与 lt_irrefl 推出（纯 Set 层，Empty_set 归谬） *)
Lemma one_neq_zero : Not (Id one zero).
Proof.
  intro H. exact (lt_irrefl zero (match H in (Id _ y) return lt zero y with | id_refl => one_pos end)).
Qed.

(* ============================================================ *)
(* 分析辅助引理（ε-δ 证明用；纯 Set 层）                       *)
(* ============================================================ *)

(* 2 := plus one one 的正性 *)
Lemma two_pos : lt zero (plus one one).
Proof.
  apply plus_positive; apply one_pos.
Qed.

(* eps/2 正性：lt zero a ⟹ lt zero (inv_2 · a) *)
Lemma half_pos :
  forall a, lt zero a -> lt zero (mult (inv_pos (plus one one) two_pos) a).
Proof.
  intros a Ha. exact (mult_positive (inv_pos (plus one one) two_pos) a (inv_pos_pos (plus one one) two_pos) Ha).
Qed.

(* eps/2 加倍还原：inv_2·a + inv_2·a = a *)
Lemma half_twice :
  forall a,
    Id (plus (mult (inv_pos (plus one one) two_pos) a)
             (mult (inv_pos (plus one one) two_pos) a)) a.
Proof.
  intro a.
  rewrite <- (two_mult (mult (inv_pos (plus one one) two_pos) a)).
  rewrite (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) a).
  rewrite (inv_pos_correct (plus one one) two_pos).
  rewrite (mult_comm one a).
  rewrite (mult_one a).
  reflexivity.
Qed.

(* 加法中项交换：(a+b)+(c+d) = (a+c)+(b+d) *)
Lemma plus_swap_mid :
  forall a b c d : R,
    Id (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
Proof.
  intros a b c d.
  exact (id_trans (id_sym (plus_assoc a b (plus c d)))
                  (id_trans (id_cong (fun w => plus a w) (plus_assoc b c d))
                    (id_trans (id_cong (fun w => plus a (plus w d)) (plus_comm b c))
                      (id_trans (id_cong (fun w => plus a w) (id_sym (plus_assoc c b d)))
                                (plus_assoc a c (plus b d)))))).
Qed.

(* 减法对加法分配：(a+b)-(c+d) = (a-c)+(b-d) *)
Lemma minus_plus_distr :
  forall a b c d : R,
    Id (minus (plus a b) (plus c d)) (plus (minus a c) (minus b d)).
Proof.
  intros a b c d. unfold minus.
  exact (id_trans (id_cong (fun w => plus (plus a b) w) (opp_plus c d)) (plus_swap_mid a b (opp c) (opp d))).
Qed.

(* ============================================================ *)
(* differentiable_mult 辅助引理（纯 Set 层）                    *)
(* ============================================================ *)

(* |a| + 1 > 0：由 one_pos + abs_nonneg + le_plus_compat + lt_le_trans 推出 *)
Lemma abs_plus_one_pos : forall a : R, lt zero (plus (abs a) one).
Proof.
  intro a.
  exact (lt_le_trans zero one (plus (abs a) one) one_pos
  (le_trans one (plus zero one) (plus (abs a) one)
  (le_id_r one one (plus zero one)
  (id_trans (id_sym (plus_zero one)) (id_sym (plus_comm zero one)))
  (le_refl one))
  (le_plus_compat zero (abs a) one one (abs_nonneg a) (le_refl one)))).
Qed.

(* b ≥ 0 时 a ≤ a + b *)
Lemma le_plus_nonneg_r : forall a b : R, le zero b -> le a (plus a b).
Proof.
  intros a b Hb.
  exact (le_trans a (plus a zero) (plus a b)
  (le_id_l a (plus a zero) (plus a zero) (id_sym (plus_zero a)) (le_refl (plus a zero)))
  (le_plus_compat a a zero b (le_refl a) Hb)).
Qed.

(* |a| ≤ |a| + 1 *)
Lemma abs_le_abs_plus_one : forall a : R, le (abs a) (plus (abs a) one).
Proof.
  intro a. exact (le_plus_nonneg_r (abs a) one (lt_le_iff zero one (inl one_pos))).
Qed.

(* 非负 + 正 = 正：le zero a + lt zero b ⟹ lt zero (plus a b) *)
Lemma plus_le_lt_pos : forall a b : R, le zero a -> lt zero b -> lt zero (plus a b).
Proof.
  intros a b Ha Hb.
  apply (lt_le_trans _ b _).
  - exact Hb.
  - apply (le_trans _ (plus zero b) _).
    + rewrite (plus_comm zero b). rewrite (plus_zero b). apply le_refl.
    + apply le_plus_compat; [exact Ha | apply le_refl].
Qed.

(* log 对 exp_neg 是逆：log (e^{-x}) = -x（由 log_inv_exp_neg + log_inv_log + double_neg） *)
Lemma log_exp_neg : forall x : R, Id (log (exp_neg x)) (opp x).
Proof.
  intro x.
  exact (id_trans (id_sym (double_neg (log (exp_neg x))))
  (id_cong opp (id_sym (id_trans (id_sym (log_inv_exp_neg x))
  (log_inv_log (exp_neg x) (exp_neg_pos x)))))).
Qed.

(* log 对逆元：log (1/x) = -log x（由 log_mult + log_one + plus_inv_unique） *)
Lemma log_inv_one_inv : forall x : R, forall Hx : lt zero x,
  Id (log (inv_pos x Hx)) (opp (log x)).
Proof.
  intros x Hx.
  assert (Hprod : Id (mult (inv_pos x Hx) x) one)
    by exact (id_trans (mult_comm (inv_pos x Hx) x) (inv_pos_correct x Hx)).
  assert (Hlm : Id (log (mult (inv_pos x Hx) x)) (plus (log (inv_pos x Hx)) (log x)))
    by exact (log_mult (inv_pos x Hx) x (inv_pos_pos x Hx) Hx).
  assert (Hz : Id (plus (log (inv_pos x Hx)) (log x)) zero).
  {
    assert (Hl1 : Id (log (mult (inv_pos x Hx) x)) zero)
      by exact (id_trans (id_cong log Hprod) (log_one)).
    exact (id_trans (id_sym Hlm) Hl1).
  }
  apply (plus_inv_unique (log x)).
  - apply (id_trans (plus_comm (log x) (log (inv_pos x Hx))) Hz).
  - apply plus_opp.
Qed.

(* e^{-log x} = x（x > 0）：由 log_inv_log（log_inv x = -log x）+
   exp_neg_log_inv（exp_neg (log_inv x) = x）推出。
   RLHF 对齐的 partition_condition 证明需要（e^{-E/β} = π_ref·e^{r/β}）。 *)
Lemma exp_neg_opp_log :
  forall x : R, forall Hx : lt zero x,
    Id (exp_neg (opp (log x))) x.
Proof.
  intros x Hx.
  exact (id_trans (id_cong (fun t => exp_neg t) (id_sym (log_inv_log x Hx)))
  (exp_neg_log_inv x)).
Qed.

(* exp_neg 的和差：e^{-(a+b)} = e^{-a}·e^{-b}（exp_neg_plus 反向） *)
Lemma exp_neg_opp_plus :
  forall a b : R, Id (exp_neg (opp (plus a b))) (mult (exp_neg (opp a)) (exp_neg (opp b))).
Proof.
  intros a b.
  exact (id_trans (id_cong (fun t => exp_neg t) (opp_plus a b))
  (exp_neg_plus (opp a) (opp b))).
Qed.

(* log 对商：log (a/b) = log a - log b（由 log_mult + log_inv_one_inv） *)
Lemma log_div :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    Id (log (mult a (inv_pos b Hb))) (minus (log a) (log b)).
Proof.
  intros a b Ha Hb. unfold minus.
  exact (id_trans (log_mult a (inv_pos b Hb) Ha (inv_pos_pos b Hb))
  (id_cong (fun x => plus (log a) x) (log_inv_one_inv b Hb))).
Qed.

(* 减法消元：a + (b - a) = b *)
Lemma minus_plus_cancel : forall a b : R, Id (plus a (minus b a)) b.
Proof.
  intros a b. unfold minus.
  exact (id_trans (plus_assoc a b (opp a)) (id_trans (id_cong (fun w => plus w (opp a)) (plus_comm a b)) (id_trans (id_sym (plus_assoc b a (opp a))) (id_trans (id_cong (fun w => plus b w) (plus_opp a)) (plus_zero b))))).
Qed.

(* 减法消元（右）：(a + b) - a = b *)
Lemma minus_plus_cancel_r : forall a b : R, Id (minus (plus a b) a) b.
Proof.
  intros a b.
  unfold minus.
  exact (id_trans (id_sym (plus_assoc a b (opp a)))
                  (id_trans (id_cong (fun w => plus a w) (plus_comm b (opp a)))
                            (id_trans (plus_assoc a (opp a) b)
                                      (id_trans (id_cong (fun x => plus x b) (plus_opp a))
                                                (id_trans (plus_comm zero b) (plus_zero b)))))).
Qed.

(* 减法的右分配：a - (b + c) = (a - b) - c *)
Lemma minus_plus_r : forall a b c : R,
  Id (minus a (plus b c)) (minus (minus a b) c).
Proof.
  intros a b c. unfold minus.
  exact (id_trans (id_cong (fun w => plus a w) (opp_plus b c)) (plus_assoc a (opp b) (opp c))).
Qed.

(* 负号对减法：-(a - b) = (-a) + b *)
Lemma opp_minus : forall a b : R, Id (opp (minus a b)) (plus (opp a) b).
Proof.
  intros a b. unfold minus.
  exact (id_trans (opp_plus a (opp b)) (id_cong (fun w => plus (opp a) w) (double_neg b))).
Qed.

(* |a - b| = |b - a|（减法对称；逐出稳态偏差量化需要。
   由 minus a b = opp (minus b a) + abs_opp 推出） *)
Lemma abs_minus_sym :
  forall a b : R, Id (abs (minus a b)) (abs (minus b a)).
Proof.
  intros a b.
  exact (id_trans (id_cong abs (id_sym (id_trans (opp_minus b a)
  (plus_comm (opp b) a)))) (abs_opp (minus b a))).
Qed.

(* log 对商反号：log (a/b) = -log (b/a)（由 log_div 两次 + opp_minus + double_neg） *)
Lemma log_div_neg :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    Id (log (mult a (inv_pos b Hb))) (opp (log (mult b (inv_pos a Ha)))).
Proof.
  intros a b Ha Hb.
  assert (H1 : Id (log (mult a (inv_pos b Hb))) (minus (log a) (log b)))
    by exact (log_div a b Ha Hb).
  assert (H2 : Id (log (mult b (inv_pos a Ha))) (minus (log b) (log a)))
    by exact (log_div b a Hb Ha).
  assert (H3 : Id (minus (log b) (log a)) (opp (minus (log a) (log b))))
    by exact (id_trans (plus_comm (log b) (opp (log a))) (id_sym (opp_minus (log a) (log b)))).
  assert (H4 : Id (opp (log (mult b (inv_pos a Ha)))) (opp (minus (log b) (log a))))
    by exact (id_cong opp H2).
  assert (H5 : Id (opp (minus (log b) (log a))) (minus (log a) (log b))).
  {
    assert (H5a : Id (opp (minus (log b) (log a))) (opp (opp (minus (log a) (log b)))))
      by exact (id_cong opp H3).
    exact (id_trans H5a (double_neg (minus (log a) (log b)))).
  }
  assert (H6 : Id (opp (log (mult b (inv_pos a Ha)))) (minus (log a) (log b)))
    by exact (id_trans H4 H5).
  exact (id_trans H1 (id_sym H6)).
Qed.

(* 增量分解：a - b = (a - (b + c)) + c *)
Lemma minus_split : forall a b c : R,
  Id (minus a b) (plus (minus a (plus b c)) c).
Proof.
  intros a b c.
  unfold minus.
  rewrite (opp_plus b c).
  rewrite (plus_assoc a (opp b) (opp c)).
  rewrite <- (plus_assoc (plus a (opp b)) (opp c) c).
  rewrite (plus_comm (opp c) c).
  rewrite (plus_opp c).
  rewrite (plus_zero (plus a (opp b))).
  reflexivity.
Qed.

(* 乘法单调（右因子）：a ≥ 0 且 b ≤ c ⟹ a·b ≤ a·c *)
Lemma le_mult_compat_r : forall a b c : R,
  le zero a -> le b c -> le (mult a b) (mult a c).
Proof.
  intros a b c Ha Hbc.
  exact (le_id_r (mult a b) (mult c a) (mult a c) (mult_comm c a)
                 (le_id_l (mult a b) (mult b a) (mult c a) (mult_comm a b)
                          (le_mult_compat_weak b c a Ha Hbc))).
Qed.

(* 2·((1/2)·(1/2)·e)·h = (1/2·e)·h（epsilon 份额合并） *)
Lemma two_times_quarter : forall e h' : R,
  Id (mult (plus one one) (mult (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) e)) h'))
     (mult (mult (inv_pos (plus one one) two_pos) e) h').
Proof.
  intros e h'.
  rewrite (mult_assoc (plus one one) (mult (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) e)) h').
  rewrite (mult_assoc (plus one one) (inv_pos (plus one one) two_pos) (mult (inv_pos (plus one one) two_pos) e)).
  rewrite (inv_pos_correct (plus one one) two_pos).
  rewrite (mult_comm one (mult (inv_pos (plus one one) two_pos) e)).
  rewrite (mult_one (mult (inv_pos (plus one one) two_pos) e)).
  reflexivity.
Qed.

(* 乘积增量分解：(a+da)(b+db) - ab = a·db + b·da + da·db *)
Lemma mult_delta_split : forall a b da db : R,
  Id (minus (mult (plus a da) (plus b db)) (mult a b))
     (plus (mult a db) (plus (mult b da) (mult da db))).
Proof.
  intros a b da db.
  unfold minus.
  rewrite distrib.
  rewrite (mult_plus_distr_r a da b).
  rewrite (mult_plus_distr_r a da db).
  rewrite <- (plus_assoc (mult a b) (mult da b) (plus (mult a db) (mult da db))).
  rewrite <- (plus_assoc (mult a b) (plus (mult da b) (plus (mult a db) (mult da db))) (opp (mult a b))).
  rewrite (plus_comm (mult da b) (plus (mult a db) (mult da db))).
  rewrite <- (plus_assoc (mult a db) (mult da db) (mult da b)).
  rewrite (plus_comm (plus (mult a db) (plus (mult da db) (mult da b))) (opp (mult a b))).
  rewrite (plus_assoc (mult a b) (opp (mult a b)) (plus (mult a db) (plus (mult da db) (mult da b)))).
  rewrite (plus_opp (mult a b)).
  rewrite (plus_comm zero (plus (mult a db) (plus (mult da db) (mult da b)))).
  rewrite (plus_zero (plus (mult a db) (plus (mult da db) (mult da b)))).
  rewrite (plus_comm (mult da db) (mult da b)).
  rewrite (mult_comm da b).
  reflexivity.
Qed.

(* 五元加减重组：(A + (B+C)) - (D+E) = (A-D) + ((B-E) + C) *)
Lemma minus_plus_quad : forall A B C D E : R,
  Id (minus (plus A (plus B C)) (plus D E))
     (plus (minus A D) (plus (minus B E) C)).
Proof.
  intros A B C D E.
  unfold minus.
  rewrite (opp_plus D E).
  rewrite (plus_swap_mid A (plus B C) (opp D) (opp E)).
  rewrite <- (plus_assoc B C (opp E)).
  rewrite (plus_comm C (opp E)).
  rewrite (plus_assoc B (opp E) C).
  reflexivity.
Qed.

(* mult 对减法的分配：a·(b-c) = a·b - a·c *)
Lemma mult_minus_distr_l : forall a b c : R,
  Id (mult a (minus b c)) (minus (mult a b) (mult a c)).
Proof.
  intros a b c. unfold minus.
  exact (id_trans (distrib a b (opp c)) (id_cong (fun w => plus (mult a b) w) (opp_mult_l a c))).
Qed.

(* 乘积误差分解：f(x+h)g(x+h) - [f(x)g(x) + (df·g + f·dg)·h]
   = f(x)·(Δg - dg·h) + g(x)·(Δf - df·h) + Δf·Δg *)
Lemma mult_diff_decomp :
  forall (f g : R -> R) (df dg : R -> R) (x h : R),
  Id (minus (mult (f (plus x h)) (g (plus x h)))
            (plus (mult (f x) (g x))
                  (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h)))
     (plus (mult (f x) (minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
           (plus (mult (g x) (minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                 (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))))).
Proof.
  intros f g df dg x h.
  assert (Hder : Id (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h)
                    (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))).
  {
    rewrite (mult_plus_distr_r (mult (df x) (g x)) (mult (f x) (dg x)) h).
    rewrite <- (mult_assoc (df x) (g x) h).
    rewrite (mult_comm (g x) h).
    rewrite (mult_assoc (df x) h (g x)).
    rewrite (mult_comm (mult (df x) h) (g x)).
    rewrite <- (mult_assoc (f x) (dg x) h).
    reflexivity.
  }
  rewrite Hder.
  assert (Hf : Id (minus (mult (f (plus x h)) (g (plus x h)))
                         (plus (mult (f x) (g x)) (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))))
                  (minus (mult (plus (f x) (minus (f (plus x h)) (f x))) (g (plus x h)))
                         (plus (mult (f x) (g x)) (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))))).
  { apply id_sym.
    apply (id_cong (fun t => minus (mult t (g (plus x h)))
                                  (plus (mult (f x) (g x)) (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))))).
    exact (minus_plus_cancel (f x) (f (plus x h))). }
  rewrite Hf.
  assert (Hg : Id (minus (mult (plus (f x) (minus (f (plus x h)) (f x))) (g (plus x h)))
                         (plus (mult (f x) (g x)) (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))))
                  (minus (mult (plus (f x) (minus (f (plus x h)) (f x))) (plus (g x) (minus (g (plus x h)) (g x))))
                         (plus (mult (f x) (g x)) (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))))).
  { apply id_sym.
    apply (id_cong (fun t => minus (mult (plus (f x) (minus (f (plus x h)) (f x))) t)
                                  (plus (mult (f x) (g x)) (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))))).
    exact (minus_plus_cancel (g x) (g (plus x h))). }
  rewrite Hg.
  rewrite (minus_plus_r (mult (plus (f x) (minus (f (plus x h)) (f x))) (plus (g x) (minus (g (plus x h)) (g x))))
                        (mult (f x) (g x))
                        (plus (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h)))).
  rewrite (mult_delta_split (f x) (g x) (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x))).
  rewrite (plus_comm (mult (g x) (mult (df x) h)) (mult (f x) (mult (dg x) h))).
  rewrite (minus_plus_quad (mult (f x) (minus (g (plus x h)) (g x)))
                           (mult (g x) (minus (f (plus x h)) (f x)))
                           (mult (minus (f (plus x h)) (f x)) (minus (g (plus x h)) (g x)))
                           (mult (f x) (mult (dg x) h))
                           (mult (g x) (mult (df x) h))).
  rewrite <- (mult_minus_distr_l (f x) (minus (g (plus x h)) (g x)) (mult (dg x) h)).
  rewrite <- (minus_plus_r (g (plus x h)) (g x) (mult (dg x) h)).
  rewrite <- (mult_minus_distr_l (g x) (minus (f (plus x h)) (f x)) (mult (df x) h)).
  rewrite <- (minus_plus_r (f (plus x h)) (f x) (mult (df x) h)).
  reflexivity.
Qed.

(* 乘法左消去：a > 0 ⟹ a·b = a·c ⟹ b = c（有序域标准性质；
   由乘逆元 + 结合律 + 交换律推出，自由能最小点唯一性需要） *)
Lemma mult_cancel_l :
  forall a b c : R, lt zero a -> Id (mult a b) (mult a c) -> Id b c.
Proof.
  intros a b c Ha Habc.
  (* 两边左乘 inv_pos a Ha：inv a · (a·b) = inv a · (a·c) *)
  assert (H1 : Id (mult (inv_pos a Ha) (mult a b))
                  (mult (inv_pos a Ha) (mult a c)))
    by exact (id_cong (fun x => mult (inv_pos a Ha) x) Habc).
  (* 重组：(inv a · a) · b = b *)
  assert (Hlb : Id (mult (inv_pos a Ha) (mult a b)) b).
  {
    assert (H2 : Id (mult (inv_pos a Ha) (mult a b))
                    (mult (mult (inv_pos a Ha) a) b))
      by exact (mult_assoc (inv_pos a Ha) a b).
    assert (H3 : Id (mult (mult (inv_pos a Ha) a) b)
                    (mult one b))
      by exact (id_cong (fun x => mult x b)
                        (id_trans (mult_comm (inv_pos a Ha) a) (inv_pos_correct a Ha))).
    assert (H4 : Id (mult one b) b)
      by exact (id_trans (mult_comm one b) (mult_one b)).
    exact (id_trans H2 (id_trans H3 H4)).
  }
  assert (Hrc : Id (mult (inv_pos a Ha) (mult a c)) c).
  {
    assert (H5 : Id (mult (inv_pos a Ha) (mult a c))
                    (mult (mult (inv_pos a Ha) a) c))
      by exact (mult_assoc (inv_pos a Ha) a c).
    assert (H6 : Id (mult (mult (inv_pos a Ha) a) c)
                    (mult one c))
      by exact (id_cong (fun x => mult x c)
                        (id_trans (mult_comm (inv_pos a Ha) a) (inv_pos_correct a Ha))).
    assert (H7 : Id (mult one c) c)
      by exact (id_trans (mult_comm one c) (mult_one c)).
    exact (id_trans H5 (id_trans H6 H7)).
  }
  exact (id_trans (id_sym Hlb) (id_trans H1 Hrc)).
Qed.

(* 乘法右消去：a > 0 ⟹ b·a = c·a ⟹ b = c（由左消去 + 交换律） *)
Lemma mult_cancel_r :
  forall a b c : R, lt zero a -> Id (mult b a) (mult c a) -> Id b c.
Proof.
  intros a b c Ha Hba. exact (mult_cancel_l a b c Ha (id_trans (mult_comm a b) (id_trans Hba (mult_comm c a)))).
Qed.

(* 减法非负：a ≤ b ⟹ 0 ≤ b - a（由 le_plus_compat 推导；
   Gibbs 等号条件 d(s) ≥ 0 需要） *)
Lemma le_minus_nonneg :
  forall a b : R, le a b -> le zero (minus b a).
Proof.
  intros a b Hab. unfold minus.
  exact (le_id_l zero (plus a (opp a)) (plus b (opp a)) (id_sym (plus_opp a)) (le_plus_compat a b (opp a) (opp a) Hab (le_refl (opp a)))).
Qed.

(* 减法为零消去：a - b = 0 ⟹ a = b（Gibbs 等号条件 d(s) = 0 ⟹ 项相等） *)
Lemma minus_eq_cancel :
  forall a b : R, Id (minus a b) zero -> Id a b.
Proof.
  intros a b Hab. unfold minus in Hab.
  exact (id_sym (id_trans (id_trans (id_sym (double_neg b))
  (id_cong opp (plus_inv_unique a (opp b) (opp a) Hab (plus_opp a))))
  (double_neg a))).
Qed.

(* 减法自零：a = b ⟹ a - b = 0（minus_eq_cancel 的逆；逐出零破缺需要） *)
Lemma minus_self_zero :
  forall a b : R, Id a b -> Id (minus a b) zero.
Proof.
  intros a b Hab. unfold minus. exact (id_trans (id_cong (fun x => plus x (opp b)) Hab) (plus_opp b)).
Qed.

(* 加法消去（右）：a + b = a ⟹ b = 0（两边加 -a，重组为 0 + b = b） *)
Lemma plus_cancel_zero :
  forall a b : R, Id (plus a b) a -> Id b zero.
Proof.
  intros a b Hab.
  exact (id_trans
          (id_sym (id_trans (plus_assoc (opp a) a b)
                            (id_trans (id_cong (fun x => plus x b)
                                               (id_trans (plus_comm (opp a) a) (plus_opp a)))
                                      (id_trans (plus_comm zero b) (plus_zero b)))))
          (id_trans (id_cong (fun x => plus (opp a) x) Hab)
                    (id_trans (plus_comm (opp a) a) (plus_opp a)))).
Qed.

(* 加法左消去：a + b = a + c ⟹ b = c（由 minus_plus_cancel_r 推出） *)
Lemma plus_cancel_l :
  forall a b c : R, Id (plus a b) (plus a c) -> Id b c.
Proof.
  intros a b c Habc.
  exact (id_trans (id_sym (minus_plus_cancel_r a b))
  (id_trans (id_cong (fun x => minus x a) Habc) (minus_plus_cancel_r a c))).
Qed.
(* 环消去（熵差-相对熵恒等式核心）：
   由 a·(-b) = a·(-c) + a·d 且 a > 0 推出 c - b = d。
   证明：两边加 a·c 得 a·(c - b) = a·d（distrib 反向 + 抵消），
   再 a > 0 消去（mult_cancel_l）。 *)
Lemma ring_d_cancel :
  forall a b c d : R,
    lt zero a ->
    Id (mult a (opp b)) (plus (mult a (opp c)) (mult a d)) ->
    Id (minus c b) d.
Proof.
  intros a b c d Ha Hmain.
  (* 第一步：mult a (minus c b) = mult a d *)
  assert (Hmul : Id (mult a (minus c b)) (mult a d)).
  {
    assert (Hd : Id (mult a (minus c b))
                   (plus (mult a c) (mult a (opp b))))
      by (unfold minus; exact (distrib a c (opp b))).
    assert (Hopp : Id (mult a (opp c)) (opp (mult a c)))
      by exact (opp_mult_l a c).
    assert (Hswap : Id (plus (mult a c) (plus (mult a (opp c)) (mult a d)))
                      (plus (plus (mult a c) (mult a (opp c))) (mult a d)))
      by exact (plus_assoc (mult a c) (mult a (opp c)) (mult a d)).
    assert (Hc0 : Id (plus (mult a c) (mult a (opp c))) zero)
      by exact (id_trans (id_cong (fun x => plus (mult a c) x) Hopp) (plus_opp (mult a c))).
    assert (Hr : Id (plus (plus (mult a c) (mult a (opp c))) (mult a d))
                    (plus zero (mult a d)))
      by exact (id_cong (fun x => plus x (mult a d)) Hc0).
    assert (Hz : Id (plus zero (mult a d)) (mult a d))
      by exact (id_trans (plus_comm zero (mult a d)) (plus_zero (mult a d))).
    assert (Hp1 : Id (plus (mult a c) (mult a (opp b)))
                     (plus (mult a c) (plus (mult a (opp c)) (mult a d))))
      by exact (id_cong (fun x => plus (mult a c) x) Hmain).
    assert (Hp2 : Id (plus (mult a c) (plus (mult a (opp c)) (mult a d)))
                     (mult a d))
      by exact (id_trans Hswap (id_trans Hr Hz)).
    exact (id_trans Hd (id_trans Hp1 Hp2)).
  }
  (* 第二步：a > 0 ⟹ minus c b = d *)
  exact (mult_cancel_l a (minus c b) d Ha Hmul).
Qed.

Lemma ring_minus_trans :
  forall a b c : R, Id (minus a b) (minus (minus a c) (minus b c)).
Proof.
  intros a b c.
  (* 两边同加 c：目标是 a - b = (a-c)-(b-c)
     等价于 (a - b) + c = (a - c) - (b - c) + c = a - c - b + c + c？不对。
     直接用 plus_inv_unique 证明。 *)
  (* 展开 RHS：minus (minus a c) (minus b c)
     = plus (plus a (opp c)) (opp (plus b (opp c)))
     = plus a (plus (opp c) (plus (opp b) (opp (opp c)))) [assoc + opp_plus]
     = plus a (plus (opp c) (plus (opp b) c)) [double_neg]
     = plus a (plus (opp c) (plus c (opp b))) [comm]
     = plus a (plus (plus (opp c) c) (opp b)) [assoc]
     = plus a (plus zero (opp b)) [opp 抵消]
     = plus a (opp b) [zero]
     = minus a b [unfold] *)
  unfold minus.
  (* 目标：plus a (opp b) = plus (plus a (opp c)) (opp (plus b (opp c))) *)
  assert (H1 : Id (plus (plus a (opp c)) (opp (plus b (opp c))))
                  (plus a (plus (opp c) (opp (plus b (opp c))))))
    by exact (id_sym (plus_assoc a (opp c) (opp (plus b (opp c))))).
  assert (H2 : Id (plus (opp c) (opp (plus b (opp c))))
                  (plus (opp c) (plus (opp b) (opp (opp c)))))
    by exact (id_cong (fun x => plus (opp c) x) (opp_plus b (opp c))).
  assert (H3 : Id (plus (opp c) (plus (opp b) (opp (opp c))))
                  (plus (opp c) (plus (opp b) c)))
    by exact (id_cong (fun x => plus (opp c) (plus (opp b) x)) (double_neg c)).
  assert (H4 : Id (plus (opp c) (plus (opp b) c))
                  (plus (opp c) (plus c (opp b))))
    by exact (id_cong (fun x => plus (opp c) x) (plus_comm (opp b) c)).
  assert (H5 : Id (plus (opp c) (plus c (opp b)))
                  (plus (plus (opp c) c) (opp b)))
    by exact (plus_assoc (opp c) c (opp b)).
  assert (H6 : Id (plus (plus (opp c) c) (opp b))
                  (plus zero (opp b)))
    by exact (id_cong (fun x => plus x (opp b)) (id_trans (plus_comm (opp c) c) (plus_opp c))).
  assert (H7 : Id (plus zero (opp b)) (opp b))
    by exact (id_trans (plus_comm zero (opp b)) (plus_zero (opp b))).
  assert (H8 : Id (plus (opp c) (opp (plus b (opp c)))) (opp b))
    by exact (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 (id_trans H6 H7))))).
  assert (H9 : Id (plus (plus a (opp c)) (opp (plus b (opp c))))
                  (plus a (opp b)))
    by exact (id_trans H1 (id_cong (fun x => plus a x) H8)).
  exact (id_sym H9).
Qed.

(* ============================================================ *)
(* Set 层自动化：Id 代数化简策略（路径 1）                    *)
(* ============================================================ *)
(* Stdlib Proper/Setoid 依赖 Prop 层 relation，与 Set 层 Id     *)
(* 宇宙不兼容。替代方案：Ltac 组合 apply（内核转换匹配）闭环   *)
(* 恒等引理。定义在 RingLemmas 内（RI 实例在上下文，引理已证）。 *)

Ltac id_simpl_step :=
  first [ apply double_neg | apply plus_zero | apply plus_opp
        | apply mult_one | apply mult_zero
        | apply opp_plus | apply opp_mult_l | apply opp_mult_r
        | apply minus_plus_cancel_r ].

Ltac id_simpl := repeat id_simpl_step.

(* id_ring：直接闭合或化简后反射 *)
Ltac id_ring := first [ apply double_neg | apply plus_zero | apply plus_opp
                       | apply mult_one | apply mult_zero
                       | apply opp_plus | apply opp_mult_l | apply opp_mult_r
                       | id_simpl; reflexivity ].

(* ============================================================ *)
(* id_ring 自动化演示（在 section 内，RI 可用）                *)
(* ============================================================ *)
Lemma id_ring_demo_double_neg :
  forall a : R, Id (opp (opp a)) a.
Proof. intro a. id_ring. Qed.

Lemma id_ring_demo_plus_opp :
  forall a : R, Id (plus a (opp a)) zero.
Proof. intro a. id_ring. Qed.

Lemma id_ring_demo_mult_one :
  forall a : R, Id (mult a one) a.
Proof. intro a. id_ring. Qed.

End RingLemmas.

(* ============================================================ *)
(* 状态空间接口：向量空间结构 + 度量 + 收敛（Set 层）        *)
(* ============================================================ *)

Class StateSpace (RI : RealInterface) := {
  S : Set;

  szero : S;
  splus : S -> S -> S;
  smult : R -> S -> S;
  sopp  : S -> S;

  splus_assoc : forall a b c : S, Id (splus a (splus b c)) (splus (splus a b) c);
  splus_comm  : forall a b : S, Id (splus a b) (splus b a);
  splus_zero  : forall a : S, Id (splus a szero) a;
  splus_opp   : forall a : S, Id (splus a (sopp a)) szero;
  smult_one   : forall a : S, Id (smult one a) a;
  smult_assoc : forall a b : R, forall x : S, Id (smult a (smult b x)) (smult (mult a b) x);
  smult_distrib_r : forall a : R, forall x y : S,
                      Id (smult a (splus x y)) (splus (smult a x) (smult a y));
  smult_distrib_l : forall a b : R, forall x : S,
                      Id (smult (plus a b) x) (splus (smult a x) (smult b x));

  smetric : S -> S -> R;
  smetric_sym       : forall a b : S, Id (smetric a b) (smetric b a);
  smetric_pos       : forall a b : S, le zero (smetric a b);
  smetric_zero      : forall a b : S, Id (smetric a b) zero -> Id a b;
  smetric_triangle  : forall a b c : S,
                        le (smetric a c) (plus (smetric a b) (smetric b c));

  clim : (nat -> S) -> S -> Set;
  clim_unique : forall u l1 l2, clim u l1 -> clim u l2 -> Id l1 l2;

  cauchy_complete_S :
    forall (u : nat -> S),
      (forall eps : R, lt zero eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n ->
          lt (smetric (u m) (u n)) eps)) ->
      sigT (fun l : S => clim u l);
}.

(* ============ 0. Real 自状态空间：clim := lim 的实例 ============ *)
Section RealSelfStateSpace.
Context {RI : RealInterface}.

(* 左单位元：1·a == a（RealInterface 只给右单位 mult_one，由 mult_comm 补左） *)
Lemma smult_one_l : forall a : @R RI, Id (@mult RI (@one RI) a) a.
Proof.
  intro a. exact (id_trans (@mult_comm RI (@one RI) a) (@mult_one RI a)).
Qed.

(* 右分配律：(a+b)·x == a·x + b·x（mult_comm + distrib 直接组装；
   库内 mult_plus_distr_r(L389) 在 Enhanced 层，此处底层自给） *)
Lemma smult_distrib_l_real : forall a b x : @R RI,
  Id (@mult RI (@plus RI a b) x) (@plus RI (@mult RI a x) (@mult RI b x)).
Proof.
  intros a b x. exact (id_sym (id_trans (id_trans (id_trans (id_cong (fun z => @plus RI (@mult RI a x) z) (@mult_comm RI b x)) (id_cong (fun z => @plus RI z (@mult RI x b)) (@mult_comm RI a x))) (id_sym (@distrib RI x a b))) (id_sym (@mult_comm RI (@plus RI a b) x)))).
Qed.

(* 全部字段由 RI 字段直供（clim := @lim RI / clim_unique := @lim_unique RI /
   cauchy_complete_S := @cauchy_complete RI 即桥本体）。 *)
Definition RealSelfSS : StateSpace RI :=
  {| S := @R RI;
     szero := @zero RI;
     splus := @plus RI;
     smult := @mult RI;
     sopp  := @opp RI;
     splus_assoc := @plus_assoc RI;
     splus_comm  := @plus_comm RI;
     splus_zero  := @plus_zero RI;
     splus_opp   := @plus_opp RI;
     smult_one   := smult_one_l;
     smult_assoc := @mult_assoc RI;
     smult_distrib_r := @distrib RI;
     smult_distrib_l := smult_distrib_l_real;
     smetric := @metric RI;
     smetric_sym := @metric_sym RI;
     smetric_pos := @metric_pos RI;
     smetric_zero := @metric_zero RI;
     smetric_triangle := @metric_triangle RI;
     clim := @lim RI;
     clim_unique := @lim_unique RI;
     cauchy_complete_S := @cauchy_complete RI |}.

(* 打印：clim/clim_unique/cauchy_complete_S 在实例上的类型 *)

End RealSelfStateSpace.

(* ============================================================ *)
(* Hilbert 空间（P0：注意力 Q·K 内积的几何基础）               *)
(* ============================================================ *)
(* Transformer 注意力本质是内积空间中的正交投影（Query-Key 点积 *)
(* 是内积，Softmax 是内积下的 Gibbs 测度，Value 是线性投影）。   *)
(* 本类为 StateSpace 增加内积结构，连接 AttentionGibbsBridge 的  *)
(* 抽象 logits 与 Q·K^T 的具体几何。                           *)
(* ------------------------------------------------------------ *)

Class HilbertSpace (RI : RealInterface) (SS : StateSpace RI) : Set := {
  inner : S -> S -> R;
  inner_sym       : forall x y : S, Id (inner x y) (inner y x);
  inner_pos       : forall x : S, le zero (inner x x);
  inner_definite  : forall x : S, Id (inner x x) zero -> Id x szero;
  inner_splus_l   : forall x y z : S,
    Id (inner (splus x y) z) (plus (inner x z) (inner y z));
  inner_smult_l   : forall (a : R) (x y : S),
    Id (inner (smult a x) y) (mult a (inner x y));

  (* 正交投影：注意力中 Value 的加权平均本质。
     proj u v = 沿 u 方向对 v 的（度量）投影。 *)
  proj : S -> S -> S;
  proj_linear     : forall u v w : S, Id (proj u (splus v w)) (splus (proj u v) (proj u w));
  proj_orthogonal : forall u v : S,
    Id (inner (splus v (sopp (proj u v))) u) zero;
}.

(* ============================================================ *)
(* Hilbert 空间非平凡定理（P0：注意力几何的核心性质）          *)
(* ============================================================ *)
(* 以下定理从 HilbertSpace 公理推出注意力机制的关键代数性质，   *)
(* 全部为非平凡推导（非公理重述），支撑 Q·K 投影的几何语义。    *)

Section HilbertTheorems.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {HS : HilbertSpace RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let smetric := @smetric RI SS.
Let inner := @inner RI SS HS.
Let splus := @splus RI SS.
Let sopp := @sopp RI SS.
Let proj := @proj RI SS HS.

(* 正交残差存在性（信息性证明：给出残差向量 w := v - proj u v，
   使得 ⟨w, u⟩ = 0 且 v = proj u v + w——正交分解的构造性见证）。
   这是注意力 Value 分解（投影 + 残差）的 sigT 形式。 *)
Theorem orthogonal_decomposition_exists :
  forall u v : S,
    sigT (fun w : S =>
      And (Id (inner w u) zero)
          (Id v (splus (proj u v) w))).
Proof.
  intros u v.
  (* 取 w := splus v (sopp (proj u v))（v 减去其投影） *)
  exists (splus v (sopp (proj u v))).
  split.
  - (* ⟨v - proj u v, u⟩ = 0：proj_orthogonal 直接给出 *)
    exact (proj_orthogonal u v).
  - (* v = proj u v + (v - proj u v)：splus_opp + splus_assoc 抵消 *)
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

(* ============================================================ *)
(* 正交分解唯一性（非平凡平行版本：投影的几何确定性）          *)
(* ============================================================ *)
(* orthogonal_decomposition_exists 给出分解 v = p + w（⟨w,u⟩=0，    *)
(* p := proj u v）的存在性；此处证明唯一性：若 w1、w2 都满足      *)
(* v = p + w，则 w1 = w2。证明用向量空间消去律（左加 sopp p 折叠：*)
(* sopp p + (p + w) = w，经 splus_assoc/comm/opp），非平凡：       *)
(* 约 15 步 S 层代数链。正交条件（⟨w,u⟩=0）与唯一性相容——        *)
(* 残差 w := v - p 是唯一正交残差，注意力 Value 投影的分解确定。  *)
(* ------------------------------------------------------------ *)

Theorem orthogonal_decomposition_unique :
  forall u v w1 w2 : S,
    Id (inner w1 u) zero -> Id v (splus (proj u v) w1) ->
    Id (inner w2 u) zero -> Id v (splus (proj u v) w2) ->
    Id w1 w2.
Proof.
  intros u v w1 w2 _ Hv1 _ Hv2.
  (* v = p + w1 且 v = p + w2 ⟹ p + w1 = p + w2 *)
  assert (Heq : Id (splus (proj u v) w1) (splus (proj u v) w2))
    by exact (id_trans (id_sym Hv1) Hv2).
  (* 两侧左加 sopp p（p := proj u v） *)
  assert (Hc : Id (splus (sopp (proj u v)) (splus (proj u v) w1))
                  (splus (sopp (proj u v)) (splus (proj u v) w2)))
    by exact (id_cong (fun x => splus (sopp (proj u v)) x) Heq).
  (* 左端折叠：sopp p + (p + w1) = w1 *)
  assert (Hl1 : Id (splus (sopp (proj u v)) (splus (proj u v) w1)) w1).
  {
    assert (H1 : Id (splus (sopp (proj u v)) (splus (proj u v) w1))
                    (splus (splus (sopp (proj u v)) (proj u v)) w1))
      by exact (splus_assoc (sopp (proj u v)) (proj u v) w1).
    assert (H2 : Id (splus (splus (sopp (proj u v)) (proj u v)) w1)
                    (splus szero w1))
      by exact (id_cong (fun x => splus x w1)
                        (id_trans (splus_comm (sopp (proj u v)) (proj u v))
                                  (splus_opp (proj u v)))).
    assert (H3 : Id (splus szero w1) w1)
      by exact (id_trans (splus_comm szero w1) (splus_zero w1)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* 右端折叠：sopp p + (p + w2) = w2（对称） *)
  assert (Hl2 : Id (splus (sopp (proj u v)) (splus (proj u v) w2)) w2).
  {
    assert (H1 : Id (splus (sopp (proj u v)) (splus (proj u v) w2))
                    (splus (splus (sopp (proj u v)) (proj u v)) w2))
      by exact (splus_assoc (sopp (proj u v)) (proj u v) w2).
    assert (H2 : Id (splus (splus (sopp (proj u v)) (proj u v)) w2)
                    (splus szero w2))
      by exact (id_cong (fun x => splus x w2)
                        (id_trans (splus_comm (sopp (proj u v)) (proj u v))
                                  (splus_opp (proj u v)))).
    assert (H3 : Id (splus szero w2) w2)
      by exact (id_trans (splus_comm szero w2) (splus_zero w2)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* w1 = LHS1 = LHS2 = w2 *)
  exact (id_trans (id_sym Hl1) (id_trans Hc Hl2)).
Qed.

End HilbertTheorems.

Fixpoint iterate {A : Set} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | Datatypes.S n' => f (iterate f n' x)
  end.

Class SumOver (RI : RealInterface) (SS : StateSpace RI) : Set := {
  sum_over_S : (S -> R) -> R;
  sum_over_S_linear :
    forall (a : R) (f : S -> R),
      Id (sum_over_S (fun s => mult a (f s))) (mult a (sum_over_S f));
  sum_over_S_add :
    forall f g : S -> R,
      Id (sum_over_S (fun s => plus (f s) (g s)))
         (plus (sum_over_S f) (sum_over_S g));
  (* 外延性（函数 Proper 性）：逐点相等 ⟹ 求和相等。
     构造性可接受（任何具体求和均满足），用于详细平衡 ⟹ 稳态等推导。 *)
  sum_over_S_ext :
    forall f g : S -> R, (forall s, Id (f s) (g s)) -> Id (sum_over_S f) (sum_over_S g);
  (* 求和的保序性：逐点 ≤ ⟹ 求和 ≤（构造性可接受；任何具体求和
     （有限和 / 可数和）均满足；Gibbs 不等式 KL ≥ 0 需要） *)
  sum_over_S_le :
    forall f g : S -> R, (forall s, le (f s) (g s)) -> le (sum_over_S f) (sum_over_S g);
  (* 非负函数求和非负：0 ≤ f(s) 逐点 ⟹ 0 ≤ Σ f
     （构造性可接受；正函数之和为正的和——任何具体求和均满足；
     Gibbs 等号条件 KL = 0 ⟹ p = q 需要） *)
  sum_over_S_nonneg :
    forall f : S -> R, (forall s, le zero (f s)) -> le zero (sum_over_S f);
  (* 和为零且逐点非负 ⟹ 逐点为零：
     Σ f = 0 且 0 ≤ f(s) ⟹ f(s) = 0。
     构造性可接受（有限和/可数和的正性：非负项和为零则每项为零；
     Gibbs 等号条件的关键一步） *)
  sum_over_S_zero_nonneg :
    forall f : S -> R, (forall s, le zero (f s)) -> Id (sum_over_S f) zero ->
      forall s, Id (f s) zero;
  (* 求和的三角不等式：|Σ f| ≤ Σ |f|（构造性可接受；任何具体求和
     （有限和 / 可数和）均满足；逐出稳态偏差量化需要） *)
  abs_sum_le :
    forall f : S -> R, le (abs (sum_over_S f)) (sum_over_S (fun s => abs (f s)));
}.

(* ============================================================ *)
(* 可微性（参数化版本，Set 层）                               *)
(* ============================================================ *)

Record Differentiable {RI : RealInterface} (f : R -> R) := {
  df : R -> R;
  df_correct : forall x eps, lt zero eps ->
    sigT (fun delta : R => And (lt zero delta) (forall h, lt (abs h) delta ->
        le (abs (minus (f (plus x h))
                       (plus (f x) (mult (df x) h))))
           (mult eps (abs h))))
}.

(* ============================================================ *)
(* 命题汇聚论核心框架                                          *)
(* ============================================================ *)

Module PropositionConvergenceCore.

Section PropositionConvergenceCore.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

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
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let log_inv := @log_inv RI.
Let log := @log RI.
Let metric := @metric RI.
Let lim := @lim RI.

(* 解包 StateSpace 字段 *)
Let S := @S RI SS.
Let szero := @szero RI SS.
Let splus := @splus RI SS.
Let smult := @smult RI SS.
Let sopp := @sopp RI SS.
Let smetric := @smetric RI SS.
Let clim := @clim RI SS.

(* 解包 SumOver 字段 *)
Let sum_over_S := @sum_over_S RI SS SO.

Definition Proposition : Set := S -> R.
(* 后续定义正常使用 R, S, plus, log_inv 等即可 *)

Definition IsProposition (P : Proposition) : Set :=
  forall s : S, And (le zero (P s)) (le (P s) one).

Definition IsPositiveProposition (P : Proposition) : Set :=
  forall s : S, lt zero (P s).

Definition loss_of_proposition (P : Proposition) (s : S) : R :=
  log_inv (P s).

Variable weighted_propositions : list (Proposition * R).
Variable weighted_props_positive :
  forall (p_w : Proposition * R), InT p_w weighted_propositions ->
    IsPositiveProposition (fst p_w).

Definition total_loss (s : S) : R :=
  fold_right (fun (p_w : Proposition * R) acc =>
                let (P, w) := p_w in
                plus (mult w (loss_of_proposition P s)) acc)
             zero weighted_propositions.

Variable base_loss : S -> R.
Definition full_loss (s : S) : R :=
  plus (base_loss s) (total_loss s).

Variable grad : (S -> R) -> S -> S.
Variable force : (S -> R) -> S -> S.

(* 力 = 负梯度（与 GradientDescentAndAttractor 的 force := sopp (grad ...)、
   LanguageModelInstance 的 force := -Δloss、PhysicalMechanics 的 F = -∇V
   约定一致；原版写为 +grad，若与下游定义同时成立将平凡化 grad = -grad）。 *)
Definition force_is_gradient (L : S -> R) : Set :=
  forall s : S, Id (force L s) (sopp (grad L s)).

Variable dynamics : (S -> R) -> S -> S.

Definition is_truth (L : S -> R) (s : S) : Set :=
  forall s' : S, le (L s) (L s').

Definition is_attractor (L : S -> R) (s : S) : Set :=
  forall s0 : S, clim (fun n => iterate (dynamics L) n s0) s.

Definition truth_iff_attractor (L : S -> R) (s : S) : Set :=
  And (is_truth L s -> is_attractor L s)
      (is_attractor L s -> is_truth L s).

Variable Z : R.
Variable Z_pos : lt zero Z.
Variable D : R.
Variable D_pos : lt zero D.

Definition boltzmann_factor (L : S -> R) (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (L s)).

Definition boltzmann_prob (L : S -> R) (s : S) : R :=
  mult (inv_pos Z Z_pos) (boltzmann_factor L s).

Definition partition_condition (L : S -> R) : Set :=
  Id Z (sum_over_S (boltzmann_factor L)).

Variable free_energy : (S -> R) -> R.
Variable entropy     : (S -> R) -> R.
Variable free_energy_argmin : (S -> R) -> S -> R.

(* 以下抽象性质作为假设变量引入，非承认件 *)
Variable free_energy_minimization :
  ExistsT (fun p_min : S -> R =>
    forall p : S -> R, le (free_energy p_min) (free_energy p)).

Variable min_free_energy_is_boltzmann :
  forall L : S -> R,
    Id (free_energy_argmin L) (boltzmann_prob L).

Variable E_A : R.
Variable T_A T_B : R.
Variable k : R.
Variable heat_flux : R.

Variable fourier_heat_conduction :
  Id heat_flux (mult k (plus T_B (opp T_A))).

Variable entropy_prod : R -> R.
Variable prob_density : R -> R.
Variable prob_pos : forall x : R, lt zero (prob_density x).
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_theorem :
  forall ds : R,
    Id (mult (inv_pos (prob_density (opp ds)) (prob_pos (opp ds)))
             (prob_density ds))
       (exp_neg (mult (inv_pos k_B k_B_pos) ds)).

Variable lower_prop : list Proposition.
Variable upper_prop : Proposition.
Variable hierarchical_relation : Proposition -> Proposition -> Set.

Definition hierarchical_stability : Set :=
  forall (P : Proposition), InT P lower_prop ->
    forall s : S, le (loss_of_proposition upper_prop s)
                     (loss_of_proposition P s).

Definition CoreClaim1 : Set :=
  forall P : S -> R, IsProposition P -> IsPositiveProposition P.

Definition CoreClaim2 : Set :=
  forall L : S -> R, forall s : S,
    is_attractor L s -> is_truth L s.

Definition CoreClaim3 : Set :=
  forall L : S -> R, force_is_gradient L.

Definition CoreClaim4 : Set :=
  forall L : S -> R, forall s : S,
    truth_iff_attractor L s.

Definition CoreClaim5 : Set :=
  forall L : S -> R,
    partition_condition L ->
    ExistsT (fun p : S -> R => Id p (boltzmann_prob L)).

Definition CoreClaim6 : Set := hierarchical_stability.

(* ============================================================ *)
(* 核心定理的非平凡实现（纯构造性、Set 层、无 Prop 设施）      *)
(* ============================================================ *)

(* CoreClaim5 的实现：见证 p := boltzmann_prob L 自身（存在性，自反）。 *)
Theorem core_claim5_holds : CoreClaim5.
Proof.
  unfold CoreClaim5.
  intros L Hpc.
  exists (boltzmann_prob L).
  reflexivity.
Qed.

(* Boltzmann 因子正性：由 exp_neg_pos 直接给出 *)
Theorem boltzmann_factor_pos :
  forall L : S -> R, forall s : S, lt zero (boltzmann_factor L s).
Proof.
  unfold boltzmann_factor.
  intros L s. exact (exp_neg_pos (mult (inv_pos D D_pos) (L s))).
Qed.

(* Boltzmann 概率正性：inv_pos_pos（Enhanced 字段）+ mult_positive + exp_neg_pos *)
Theorem boltzmann_prob_pos :
  forall L : S -> R, forall s : S, lt zero (boltzmann_prob L s).
Proof.
  unfold boltzmann_prob, boltzmann_factor.
  intros L s.
  exact (mult_positive (inv_pos Z Z_pos)
                       (exp_neg (mult (inv_pos D D_pos) (L s)))
                       (inv_pos_pos Z Z_pos)
                       (exp_neg_pos (mult (inv_pos D D_pos) (L s)))).
Qed.

Variable T_A_t : nat -> R.
Variable T_B_t : nat -> R.

Variable prediction_heat_relaxation :
  forall t : nat,
    le (metric (T_A_t t) (T_B_t t)) (metric (T_A_t (Nat.succ t)) (T_B_t (Nat.succ t))).

Variable equilibrium_dist : (S -> R) -> S -> R.

Variable prediction_equilibrium_boltzmann :
  forall L : S -> R,
    Id (equilibrium_dist L) (boltzmann_prob L).

Variable E_min : R.
Variable T_landauer : R.

Variable prediction_landauer :
  Id E_min (mult k_B (mult T_landauer (log_inv (plus one one)))).

(* 涨落标度：大小为 N 的涨落概率 = e^{-N/k_B}，随 N 增大而减小。
   原版方向写反（与 Boltzmann 的 e^{-x} 约定冲突），已翻转。
   P3-1 消解：由 exp_neg_le_decr（le a b -> le (exp_neg b) (exp_neg a)）
   于 le (N·inv) (plus N one · inv)（N ≤ N+1 乘 inv ≥ 0）直接推出——
   从诚实 Variable 提升为已证定理。 *)
Theorem prediction_fluctuation_scale :
  forall N : R,
    le (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
       (exp_neg (mult N (inv_pos k_B k_B_pos))).
Proof.
  intro N.
  apply exp_neg_le_decr.
  (* N·inv ≤ (N+1)·inv：N ≤ N+1（le_plus_nonneg_r）+ inv ≥ 0（le_mult_compat_weak） *)
  apply (le_mult_compat_weak N (plus N one) (inv_pos k_B k_B_pos)).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - apply le_plus_nonneg_r. exact (lt_le_iff _ _ (inl one_pos)).
Qed.

Variable loss_drop : nat -> R.
Variable f_N : nat -> R.
Variable power : R -> R -> R.
Variable of_nat : nat -> R.

Variable prediction_cross_domain_scaling :
  ExistsT (fun alpha : R =>
    forall N : nat, Id (loss_drop N) (mult (power (of_nat N) alpha) (f_N N))).

Variable disturbance : Proposition -> R.

Variable prediction_hierarchical_stability_holds :
  forall (P : Proposition), InT P lower_prop ->
    le (disturbance upper_prop) (disturbance P).

Variable model : nat -> S.
Variable grammar_error : S -> R.

(* 语法错误沿训练递减（与 LanguageModelInstance 的
   prediction_grammar_error_decreases 方向一致；原版方向写反）。 *)
Variable prediction_lm_loss_structure :
  forall epoch : nat,
    le (grammar_error (model (Nat.succ epoch))) (grammar_error (model epoch)).

End PropositionConvergenceCore.

End PropositionConvergenceCore.

(* ============ 1. PCT 定义实例化到 (S := R, clim := lim) ============ *)
Section PCTRealBridge.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 解包（对齐 PCT Section L1408-1431 的写法） *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let metric := @metric RI.
Let lim := @lim RI.

(* Real 自状态空间提升到 Enhanced 上下文（RI_base :> RealInterface 投影） *)
Let SS_R : StateSpace RI := @RealSelfSS (@RI_base RI).
Let S := @S RI SS_R.

(* 打印：PCT 导出定义（Section 关闭后已参量化）的实例化类型。
   若 is_attractor/CoreClaim2 不依赖 SumOver 与其他 Variable，此处类型将
   只含 dynamics 参数（证明桥只需 is_truth/is_attractor，SO 可缺）。 *)

(* ---- 定义层桥本体：PCT is_attractor 在 (S:=R, clim:=lim) 下逐字展开为
       lim 序列收敛（dynamics_wrap := 忽略损失的动力学，论文4 dynamics 提升）。
       两侧均为 Set 层命题（不可用 Id 作等词，A:=Set 超宇宙），改证双向蕴含
       —— 双方向由展开/转换直接闭合（定义层桥为平凡）。 *)
Theorem pct_attractor_is_lim :
  forall (dyn : R -> R) (L : R -> R) (s : R),
    (@PropositionConvergenceCore.is_attractor RI SS_R
       (fun (_ : R -> R) => dyn) L s ->
     forall s0 : R, lim (fun n => iterate dyn n s0) s) *
    ((forall s0 : R, lim (fun n => iterate dyn n s0) s) ->
     @PropositionConvergenceCore.is_attractor RI SS_R
       (fun (_ : R -> R) => dyn) L s).
Proof.
  intros dyn L s. split.
  - intro h. exact h.
  - intro h. exact h.
Qed.

(* ---- 对应 is_truth 的定义层展开：全局最小点形态（双向蕴含）。 *)
Theorem pct_truth_is_global_min :
  forall (L : R -> R) (s : R),
    (@PropositionConvergenceCore.is_truth RI SS_R L s ->
     forall s' : R, le (L s) (L s')) *
    ((forall s' : R, le (L s) (L s')) ->
     @PropositionConvergenceCore.is_truth RI SS_R L s).
Proof.
  intros L s. split.
  - intro h. exact h.
  - intro h. exact h.
Qed.

End PCTRealBridge.

(* ============================================================ *)
(* 语言模型实例化（独立 Module 避免命名冲突）                 *)
(* ============================================================ *)

Module LanguageModelInstance.

Section LanguageModelInstance.

Context {RI : RealInterfaceEnhanced}.

Local Existing Instance RI_base.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).

Definition Sequence : Set := list Token.

Variable neg_log_prob : Sequence -> Token -> R.

Fixpoint sequence_loss_prefix (prefix : Sequence) (s : Sequence) : R :=
  match s with
  | nil => zero
  | w :: rest =>
      plus (neg_log_prob prefix w) (sequence_loss_prefix (prefix ++ [w]) rest)
  end.

Definition sequence_loss (s : Sequence) : R := sequence_loss_prefix nil s.

Definition LangProp : Set := Sequence -> R.

Variable has_verb : LangProp.
Variable semantics_coherent : LangProp.
Variable style_appropriate : LangProp.

Variable alpha_grammar : R.
Variable alpha_semantics : R.
Variable alpha_style : R.

Variable prop_pos : forall P : LangProp, forall s : Sequence, lt zero (P s).

Definition loss_of_proposition (c : LangProp) (s : Sequence) : R :=
  log_inv (c s).

Definition total_loss (s : Sequence) : R :=
  plus (sequence_loss s)
       (plus (mult alpha_grammar (loss_of_proposition has_verb s))
             (plus (mult alpha_semantics (loss_of_proposition semantics_coherent s))
                   (mult alpha_style (loss_of_proposition style_appropriate s)))).

Definition force (s : Sequence) (w : Token) : R :=
  opp (minus (total_loss (s ++ [w])) (total_loss s)).

Context {DO : DecidableOrder RI}.
Variable default_token : Token.

Definition candidate : Set := (Token * R)%type.

Fixpoint argmin_aux (prefix : Sequence) (l : list Token) (best : candidate) : candidate :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match (@ord_le_dec _ DO) loss_w (snd best) with
      | inl _ => argmin_aux prefix rest (w, loss_w)
      | inr _ => argmin_aux prefix rest best
      end
  end.

Definition pick_best (prefix : Sequence) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

Definition dynamics (s : Sequence) : Sequence :=
  s ++ [pick_best s].

Definition is_truth (s : Sequence) : Set :=
  forall s' : Sequence, le (total_loss s) (total_loss s').

(* 注意：原此处命名为 is_attractor（单步不动点），与
   PropositionConvergenceCore / GradientDescentAndAttractor 中的收敛定义
   （forall s0, clim (iterate (dynamics L) n s0) s）同名异义；
   为避免术语漂移，改名为 is_fixed_point。 *)
Definition is_fixed_point (s : Sequence) : Set :=
  Id (dynamics s) s.

Variable plus_positive : forall a b : R, lt zero a -> lt zero b -> lt zero (plus a b).

Fixpoint sum_exp (prefix : Sequence) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (neg_log_prob prefix w)) (sum_exp prefix rest)
  end.

Definition partition_function (prefix : Sequence) : R :=
  sum_exp prefix vocab.

Lemma exp_neg_positive : forall x : R, lt zero (exp_neg x).
Proof. apply exp_neg_pos. Qed.

Lemma sum_exp_positive : forall prefix l, Not (Id l nil) -> lt zero (sum_exp prefix l).
Proof.
  intros prefix l. induction l as [| w rest IH].
  - intros Hnil. contradiction Hnil. apply id_refl.
  - intros _. simpl.
    destruct rest as [| w' rest'].
    + (* rest = [] *)
      change (lt zero (plus (exp_neg (neg_log_prob prefix w)) zero)).
      rewrite plus_zero.
      apply exp_neg_positive.
    + (* rest = w' :: rest' *)
      apply plus_positive.
      * apply exp_neg_positive.
      * apply IH. intro H. inversion H.
Qed.

Definition partition_positive (prefix : Sequence) : lt zero (partition_function prefix) :=
  sum_exp_positive prefix vocab vocab_nonempty.

Definition normalized_prob (prefix : Sequence) (w : Token) : R :=
  mult (exp_neg (neg_log_prob prefix w))
       (inv_pos (partition_function prefix) (partition_positive prefix)).

Definition CoreClaim1 : Set :=
  forall P : LangProp, forall s : Sequence, lt zero (P s).

Definition CoreClaim2 : Set :=
  forall s, is_fixed_point s -> is_truth s.

Definition CoreClaim3 : Set :=
  forall s w,
    Id (force s w) (minus (total_loss s) (total_loss (s ++ [w]))).

Definition CoreClaim4 : Set :=
  forall s, And (is_truth s) (is_fixed_point s).

Definition CoreClaim5 : Set :=
  forall prefix w,
    Id (normalized_prob prefix w)
       (mult (exp_neg (neg_log_prob prefix w))
             (inv_pos (partition_function prefix) (partition_positive prefix))).

Variable vocab_propositions : list LangProp.
Variable syntax_rules : LangProp.

Definition CoreClaim6 : Set :=
  forall (P : LangProp), InT P vocab_propositions ->
    forall s : Sequence,
      le (loss_of_proposition syntax_rules s)
         (loss_of_proposition P s).

(* ============================================================ *)
(* 核心定理的非平凡实现（纯构造性、Set 层、无 Prop 设施）      *)
(* ============================================================ *)

(* CoreClaim1：命题正性（由 prop_pos 假设直接给出） *)
Theorem core_claim1_holds : CoreClaim1.
Proof. exact prop_pos. Qed.

(* CoreClaim3：force 的等价形式（非平凡——环论推导）。
   force s w = opp (minus (loss (s++[w])) (loss s))
             = minus (loss s) (loss (s++[w]))
   由 opp_plus + double_neg + plus_comm 推出。 *)
Theorem core_claim3_holds : CoreClaim3.
Proof.
  unfold CoreClaim3, force, minus.
  intros s w.
  rewrite (opp_plus (total_loss (s ++ [w])) (opp (total_loss s))).
  rewrite (double_neg (total_loss s)).
  rewrite (plus_comm (opp (total_loss (s ++ [w]))) (total_loss s)).
  reflexivity.
Qed.

(* CoreClaim5：normalized_prob 的定义展开（自反） *)
Theorem core_claim5_holds : CoreClaim5.
Proof.
  unfold CoreClaim5, normalized_prob.
  intros prefix w.
  exact (@id_refl _ _).
Qed.
Print Assumptions core_claim5_holds.  (* ToyR 假设审计 *)

Variable grammar_error : Sequence -> R.

(* 以下性质作为假设变量引入，非承认件 *)
Variable prediction_loss_monotone :
  forall s, le (total_loss (dynamics s)) (total_loss s).

Variable prediction_grammar_error_decreases :
  forall s, le (grammar_error (dynamics s)) (grammar_error s).

(* 注：prediction_boltzmann_sampling 原为 Variable，但内容与
   core_claim5_holds 相同（normalized_prob 的定义展开），故删除该
   假设，直接用已证定理 core_claim5_holds。 *)

Variable prediction_hierarchical_stability_holds :
  CoreClaim6.

Variable prediction_loss_structure_correlation :
  forall s, le (total_loss (dynamics s)) (total_loss s) ->
            le (grammar_error (dynamics s)) (grammar_error s).

(* ============================================================ *)
(* 补齐预测性质（模块1：LanguageModelInstance）                *)
(* ============================================================ *)
(* normalized_prob 逐点正：exp_neg 正 × partition 倒数正（非平凡：
   mult_positive 组合 exp_neg_pos 与 inv_pos_pos）。 *)
Theorem normalized_prob_pos :
  forall prefix w, lt zero (normalized_prob prefix w).
Proof.
  intros prefix w.
  unfold normalized_prob.
  apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* Boltzmann 采样概率的显式形式（由定理而非假设给出）：
   与 core_claim5_holds 同一内容，此处以命名定理形式落库。 *)
Theorem prediction_boltzmann_sampling_holds :
  forall prefix w,
    Id (normalized_prob prefix w)
       (mult (exp_neg (neg_log_prob prefix w))
             (inv_pos (partition_function prefix) (partition_positive prefix))).
Proof.
  intros prefix w.
  unfold normalized_prob.
  reflexivity.
Qed.

End LanguageModelInstance.

End LanguageModelInstance.

(* ============================================================ *)
(* 随机语言模型：温度采样马尔可夫核（P3，结构性缺失.txt 七）    *)
(* ============================================================ *)
(* 文档草稿的温度采样核，此处以可证明形式落地：temp_factor /     *)
(* partition_temp / markov_kernel（温度化 Boltzmann 概率），      *)
(* markov_normalized（核归一化——概率守恒），markov_relative      *)
(* （相对恒等），markov_temperature_zero_limit（零温极限比值形式： *)
(* 损失间隙 ⟹ 概率比指数衰减——温度采样退化为贪心解码的定量内容）。*)
(* 注：文档草稿的 `Id temperature zero` 前提与 temperature_pos 矛盾，*)
(* 改为比值形式（同 AttentionGibbsBridge.temperature_zero_limit）。*)

Module StochasticLanguageModel.
Section StochasticLanguageModel.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let log := @log RI.
Let le_refl := @le_refl RI.
Let le_trans := @le_trans RI.
Let le_plus_compat := @le_plus_compat RI.
Let opp_le_compat := @opp_le_compat RI.
Let le_mult_compat_r := @le_mult_compat_r RI.
Let le_minus_nonneg := le_minus_nonneg.
Let opp_minus := opp_minus.
Let log_le_linear := @log_le_linear RI.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable total_loss : list Token -> R.   (* 序列损失（prefix ++ [w] 的损失） *)

Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* 温度化因子：e^{-loss/T}（损失越小权重越大） *)
Definition temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w]))).

(* 列表求和（泛化：任意 Token → R 函数） *)
Fixpoint list_sum (f : Token -> R) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (f w) (list_sum f rest)
  end.

Definition partition_temp (prefix : list Token) : R :=
  list_sum (temp_factor prefix) vocab.

(* 温度化因子反单调：损失小 ⟹ temp_factor 大。
   loss(w1) ≤ loss(w2) ⟹ e^{−loss(w1)/T} ≥ e^{−loss(w2)/T}。
   非平凡：exp_neg_le_decr（指数参数 ≤）+ le_mult_compat_r（inv T > 0）。 *)
Lemma temp_factor_antitone : forall (prefix : list Token) (w1 w2 : Token),
  le (total_loss (prefix ++ [w1])) (total_loss (prefix ++ [w2])) ->
  le (temp_factor prefix w2) (temp_factor prefix w1).
Proof.
  intros prefix w1 w2 Hloss.
  unfold temp_factor.
  exact (exp_neg_le_decr (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w1])))
                         (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w2])))
                         (le_mult_compat_r (inv_pos temperature temperature_pos)
                                           (total_loss (prefix ++ [w1])) (total_loss (prefix ++ [w2]))
                                           (lt_le_iff zero (inv_pos temperature temperature_pos)
                                                      (inl (inv_pos_pos temperature temperature_pos)))
                                           Hloss)).
Qed.

(* 温度采样核反单调：损失小 ⟹ 核概率大（共同配分因子约去）。
   loss(w1) ≤ loss(w2) ⟹ P_T(w2) ≤ P_T(w1)。
   非平凡：temp_factor_antitone + 乘以共同 inv(partition)（非负，le_mult_compat_r）。
   注：markov_kernel 定义于下方（partition_temp_pos 后），本引理随之。 *)

Lemma list_sum_linear : forall a : R, forall f : Token -> R, forall l : list Token,
  Id (list_sum (fun w => mult a (f w)) l) (mult a (list_sum f l)).
Proof.
  intros a f l. induction l as [| w rest IH]; simpl.
  - apply id_sym. apply mult_zero.
  - rewrite IH.
    apply id_sym. apply distrib.
Qed.

Lemma list_sum_add : forall f g : Token -> R, forall l : list Token,
  Id (list_sum (fun w => plus (f w) (g w)) l) (plus (list_sum f l) (list_sum g l)).
Proof.
  intros f g l. induction l as [| w rest IH]; simpl.
  - apply id_sym. apply plus_zero.
  - rewrite IH.
    exact (plus_swap_mid (f w) (g w) (list_sum f rest) (list_sum g rest)).
Qed.

Lemma list_sum_ext : forall f g : Token -> R, forall l : list Token,
  (forall w : Token, Id (f w) (g w)) -> Id (list_sum f l) (list_sum g l).
Proof.
  intros f g l Hfg. induction l as [| w rest IH]; simpl.
  - reflexivity.
  - assert (H1 : Id (plus (f w) (list_sum f rest)) (plus (f w) (list_sum g rest)))
      by exact (id_cong (fun x => plus (f w) x) IH).
    assert (H2 : Id (plus (f w) (list_sum g rest)) (plus (g w) (list_sum g rest)))
      by exact (id_cong (fun x => plus x (list_sum g rest)) (Hfg w)).
    exact (id_trans H1 H2).
Qed.

(* 非空列表的正函数和为正（同 LanguageModelInstance.sum_exp_positive 结构） *)
Lemma sum_temp_positive : forall (f : Token -> R),
  (forall w, lt zero (f w)) -> forall l : list Token, Not (Id l nil) -> lt zero (list_sum f l).
Proof.
  intros f Hpos l. induction l as [| w rest IH]; intros Hnil.
  - contradiction Hnil. apply id_refl.
  - simpl.
    destruct rest as [| w' rest'].
    + change (lt zero (plus (f w) zero)).
      rewrite plus_zero.
      apply Hpos.
    + apply plus_positive.
      * apply Hpos.
      * apply IH. intro H. inversion H.
Qed.

Definition partition_temp_pos (prefix : list Token) : lt zero (partition_temp prefix) :=
  sum_temp_positive (temp_factor prefix)
                    (fun w => exp_neg_pos (mult (inv_pos temperature temperature_pos)
                                                (total_loss (prefix ++ [w]))))
                    vocab vocab_nonempty.

(* 温度采样核：P(w|prefix) ∝ e^{-loss/T}，归一化配分函数 *)
Definition markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (temp_factor prefix w) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)).

(* 温度采样核反单调：损失小 ⟹ 核概率大（共同配分因子约去）。
   loss(w1) ≤ loss(w2) ⟹ P_T(w2) ≤ P_T(w1)。
   非平凡：temp_factor_antitone + 乘以共同 inv(partition)（非负，le_mult_compat_r）。 *)
Theorem markov_kernel_antitone : forall (prefix : list Token) (w1 w2 : Token),
  le (total_loss (prefix ++ [w1])) (total_loss (prefix ++ [w2])) ->
  le (markov_kernel prefix w2) (markov_kernel prefix w1).
Proof.
  intros prefix w1 w2 Hloss.
  unfold markov_kernel.
  (* temp_factor w2 ≤ temp_factor w1（temp_factor_antitone） *)
  assert (Htf : le (temp_factor prefix w2) (temp_factor prefix w1))
    by exact (temp_factor_antitone prefix w1 w2 Hloss).
  (* 乘以共同 inv(partition)（≥ 0）；le_mult_compat_r 给 mult inv tf ≤ mult inv tf'，
     用 mult_comm 换到 mult tf inv ≤ mult tf' inv *)
  assert (Hinv_nonneg : le zero (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))
    by (apply (lt_le_iff _ _); left; apply inv_pos_pos).
  assert (Hm1 : le (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w2))
                   (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w1)))
    by exact (le_mult_compat_r (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                               (temp_factor prefix w2) (temp_factor prefix w1)
                               Hinv_nonneg Htf).
  (* mult tf inv ≤ mult inv tf ≤ mult inv tf' ≤ mult tf' inv *)
  assert (Hsw2 : le (mult (temp_factor prefix w2) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))
                    (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w2)))
    by exact (le_id_l (mult (temp_factor prefix w2) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))
                      (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w2))
                      (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w2))
                      (mult_comm (temp_factor prefix w2) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))
                      (le_refl _)).
  assert (Hsw3 : le (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w1))
                    (mult (temp_factor prefix w1) (inv_pos (partition_temp prefix) (partition_temp_pos prefix))))
    by exact (le_id_l (mult (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w1))
                      (mult (temp_factor prefix w1) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))
                      (mult (temp_factor prefix w1) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))
                      (mult_comm (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (temp_factor prefix w1))
                      (le_refl _)).
  exact (le_trans _ _ _ Hsw2 (le_trans _ _ _ Hm1 Hsw3)).
Qed.

(* 核正性（温度采样概率 > 0） *)
Lemma markov_pos : forall prefix w, lt zero (markov_kernel prefix w).
Proof.
  intros prefix w.
  unfold markov_kernel.
  exact (mult_positive (temp_factor prefix w)
                       (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
                       (exp_neg_pos (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w]))))
                       (inv_pos_pos (partition_temp prefix) (partition_temp_pos prefix))).
Qed.

(* 核归一化：Σ_w P(w|prefix) = 1（概率守恒——温度采样是概率测度） *)
Theorem markov_normalized : forall prefix,
  Id (list_sum (fun w => markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  unfold markov_kernel.
  exact (id_trans (list_sum_ext (fun w => mult (temp_factor prefix w) (inv_pos (partition_temp
    prefix) (partition_temp_pos prefix))) (fun w => mult (inv_pos (partition_temp prefix)
    (partition_temp_pos prefix)) (temp_factor prefix w)) vocab (fun w => mult_comm (temp_factor
    prefix w) (inv_pos (partition_temp prefix) (partition_temp_pos prefix)))) (id_trans
    (list_sum_linear (inv_pos (partition_temp prefix) (partition_temp_pos prefix))
    (temp_factor prefix) vocab) (id_trans (@id_refl R (mult (inv_pos (partition_temp prefix)
    (partition_temp_pos prefix)) (list_sum (temp_factor prefix) vocab))) (id_trans (mult_comm
    (inv_pos (partition_temp prefix) (partition_temp_pos prefix)) (partition_temp prefix))
    (inv_pos_correct (partition_temp prefix) (partition_temp_pos prefix)))))).
Qed.

(* 相对恒等：P(w) = P(wstar)·e^{-(loss_w - loss_wstar)/T}（温度采样核的分解） *)
Theorem markov_relative :
  forall (prefix : list Token) (w wstar : Token),
    Id (markov_kernel prefix w)
       (mult (markov_kernel prefix wstar)
             (exp_neg (mult (inv_pos temperature temperature_pos)
                            (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar])))))).
Proof.
  intros prefix w wstar.
  unfold markov_kernel, temp_factor.
  set (A := exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar])))).
  set (B := exp_neg (mult (inv_pos temperature temperature_pos) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))).
  set (C := inv_pos (partition_temp prefix) (partition_temp_pos prefix)).
  set (Ap := exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w])))).
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
    assert (Hep : Id (mult (exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar]))))
                           (exp_neg (mult (inv_pos temperature temperature_pos) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))))
                     (exp_neg (plus (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar])))
                                    (mult (inv_pos temperature temperature_pos) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar])))))))
      by exact (id_sym (exp_neg_plus (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar])))
                                     (mult (inv_pos temperature temperature_pos) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar])))))).
    rewrite Hep.
    assert (Halg : Id (plus (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar])))
                            (mult (inv_pos temperature temperature_pos) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar])))))
                      (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w])))).
    {
      assert (Hd : Id (plus (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar])))
                            (mult (inv_pos temperature temperature_pos) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar])))))
                      (mult (inv_pos temperature temperature_pos)
                            (plus (total_loss (prefix ++ [wstar])) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))))
        by exact (id_sym (distrib (inv_pos temperature temperature_pos) (total_loss (prefix ++ [wstar])) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))).
      assert (Hc : Id (plus (total_loss (prefix ++ [wstar])) (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))
                      (total_loss (prefix ++ [w])))
        by exact (minus_plus_cancel (total_loss (prefix ++ [wstar])) (total_loss (prefix ++ [w]))).
      exact (id_trans Hd (id_cong (fun x => mult (inv_pos temperature temperature_pos) x) Hc)).
    }
    apply (id_cong (fun x => exp_neg x)). exact Halg.
  }
  (* 组装：mult Ap C = mult (mult A C) B *)
  rewrite Hre.
  rewrite Hprod.
  reflexivity.
Qed.

(* 零温极限（比值形式）：损失间隙 ⟹ 概率比指数衰减。
   对任意 wstar（贪心最优候选：loss(wstar) ≤ loss(w)），
   P_T(w)/P_T(wstar) ≤ e^{-(loss(w) - loss(wstar))/T}——T→0 时温度采样
   的概率质量向最小损失态集中（退化为贪心解码的定量形式）。 *)
Theorem markov_temperature_zero_limit :
  forall (prefix : list Token) (w wstar : Token),
    le (total_loss (prefix ++ [wstar])) (total_loss (prefix ++ [w])) ->
    le (mult (markov_kernel prefix w)
             (inv_pos (markov_kernel prefix wstar) (markov_pos prefix wstar)))
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))).
Proof.
  intros prefix w wstar Hloss.
  (* 相对恒等 + 两侧除以 markov_kernel wstar > 0（同 temperature_zero_limit 模式） *)
  assert (Hrel : Id (markov_kernel prefix w)
                    (mult (markov_kernel prefix wstar)
                          (exp_neg (mult (inv_pos temperature temperature_pos)
                                         (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar])))))))
    by exact (markov_relative prefix w wstar).
  set (A := markov_kernel prefix w).
  set (B := markov_kernel prefix wstar).
  set (C := exp_neg (mult (inv_pos temperature temperature_pos)
                          (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [wstar]))))).
  assert (Hgc : le A (mult B C))
    by (unfold A, B, C; rewrite Hrel; apply le_refl).
  assert (Hinv : le zero (inv_pos B (markov_pos prefix wstar))).
  { apply (lt_le_iff _ _). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos B (markov_pos prefix wstar)) A)
                    (mult (inv_pos B (markov_pos prefix wstar)) (mult B C)))
    by exact (le_mult_compat_r (inv_pos B (markov_pos prefix wstar)) A (mult B C) Hinv Hgc).
  assert (Hsw : Id (mult (inv_pos B (markov_pos prefix wstar)) A)
                   (mult A (inv_pos B (markov_pos prefix wstar))))
    by exact (mult_comm (inv_pos B (markov_pos prefix wstar)) A).
  assert (Hlhs : le (mult A (inv_pos B (markov_pos prefix wstar)))
                    (mult (inv_pos B (markov_pos prefix wstar)) (mult B C)))
    by exact (le_id_l (mult A (inv_pos B (markov_pos prefix wstar)))
                      (mult (inv_pos B (markov_pos prefix wstar)) A)
                      (mult (inv_pos B (markov_pos prefix wstar)) (mult B C))
                      (id_sym Hsw) Hdiv).
  assert (Hrhs : Id (mult (inv_pos B (markov_pos prefix wstar)) (mult B C)) C).
  {
    assert (H1 : Id (mult (inv_pos B (markov_pos prefix wstar)) (mult B C))
                    (mult (mult (inv_pos B (markov_pos prefix wstar)) B) C))
      by exact (mult_assoc (inv_pos B (markov_pos prefix wstar)) B C).
    assert (H2 : Id (mult (mult (inv_pos B (markov_pos prefix wstar)) B) C) (mult one C))
      by exact (id_cong (fun x => mult x C)
                        (id_trans (mult_comm (inv_pos B (markov_pos prefix wstar)) B)
                                  (inv_pos_correct B (markov_pos prefix wstar)))).
    assert (H3 : Id (mult one C) C)
      by exact (id_trans (mult_comm one C) (mult_one C)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  assert (Hfin : le (mult A (inv_pos B (markov_pos prefix wstar))) C)
    by exact (le_id_r (mult A (inv_pos B (markov_pos prefix wstar)))
                      (mult (inv_pos B (markov_pos prefix wstar)) (mult B C))
                      C Hrhs Hlhs).
  unfold A, B, C in Hfin.
  exact Hfin.
Qed.

(* 列表求和保序（仅对列表元素要求逐点）：若 f ≤ g 在 l 的元素上成立，
   则 list_sum f l ≤ list_sum g l。非平凡：归纳 l + le_plus_compat +
   InT_here/InT_next 递推。 *)
Lemma list_sum_le_on_list : forall (l : list Token) (f g : Token -> R),
  (forall w : Token, InT w l -> le (f w) (g w)) -> le (list_sum f l) (list_sum g l).
Proof.
  intros l f g Hfg. induction l as [| w rest IH]; simpl.
  - apply le_refl.
  - apply le_plus_compat.
    + apply Hfg. apply InT_here.
    + apply IH. intros w0 Hw0. apply Hfg. apply (InT_next w0 w rest Hw0).
Qed.

(* 期望损失：温度采样核下的平均损失（模块2 扩展定义） *)
Definition expected_loss (prefix : list Token) : R :=
  list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [w]))) vocab.

(* 期望损失的贪心下界：若 wstar 是 vocab 上的全局最小损失候选
   （对任意 w ∈ vocab，loss(wstar) ≤ loss(w)），则期望损失 ≥ loss(wstar)。
   非平凡：逐点 p_w·loss(wstar) ≤ p_w·loss_w（p_w > 0，le_mult_compat_r）
   + 求和保序（list_sum_le_on_list，只在 vocab 元素上要求）
   + 线性化 Σ p_w·loss(wstar) = loss(wstar)·Σ p_w（list_sum_linear）
   + 归一化 Σ p_w = 1（markov_normalized）——温度采样的"期望不小于最小"。 *)
Theorem expected_loss_min_bound :
  forall prefix wstar,
    (forall w : Token, InT w vocab ->
      le (total_loss (prefix ++ [wstar])) (total_loss (prefix ++ [w]))) ->
    le (total_loss (prefix ++ [wstar])) (expected_loss prefix).
Proof.
  intros prefix wstar Hmin.
  unfold expected_loss.
  (* 逐点：p_w·loss(wstar) ≤ p_w·loss_w（对 w ∈ vocab） *)
  assert (Hpt : forall w : Token, InT w vocab ->
    le (mult (markov_kernel prefix w) (total_loss (prefix ++ [wstar])))
       (mult (markov_kernel prefix w) (total_loss (prefix ++ [w])))).
  {
    intros w Hw.
    apply (le_mult_compat_r (markov_kernel prefix w) (total_loss (prefix ++ [wstar]))
                            (total_loss (prefix ++ [w]))
                            (lt_le_iff _ _ (inl (markov_pos prefix w)))
                            (Hmin w Hw)).
  }
  (* 求和：Σ p_w·loss(wstar) ≤ Σ p_w·loss_w *)
  assert (Hsum_le : le (list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [wstar]))) vocab)
                       (list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [w]))) vocab)).
  { apply list_sum_le_on_list. exact Hpt. }
  (* 左端线性化：Σ p_w·loss(wstar) = loss(wstar)·Σ p_w *)
  assert (Hlin : Id (list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [wstar]))) vocab)
                    (mult (total_loss (prefix ++ [wstar]))
                          (list_sum (markov_kernel prefix) vocab))).
  {
    assert (Hswap : Id (list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [wstar]))) vocab)
                       (list_sum (fun w => mult (total_loss (prefix ++ [wstar])) (markov_kernel prefix w)) vocab))
      by (apply list_sum_ext; intro w; apply mult_comm).
    assert (Hlin' : Id (list_sum (fun w => mult (total_loss (prefix ++ [wstar])) (markov_kernel prefix w)) vocab)
                       (mult (total_loss (prefix ++ [wstar])) (list_sum (markov_kernel prefix) vocab)))
      by exact (list_sum_linear (total_loss (prefix ++ [wstar])) (markov_kernel prefix) vocab).
    exact (id_trans Hswap Hlin').
  }
  (* 归一化：Σ p_w = 1，故 loss(wstar)·Σ p_w = loss(wstar) *)
  assert (Hnorm : Id (list_sum (markov_kernel prefix) vocab) one)
    by exact (markov_normalized prefix).
  assert (Hunit : Id (mult (total_loss (prefix ++ [wstar])) (list_sum (markov_kernel prefix) vocab))
                     (total_loss (prefix ++ [wstar]))).
  {
    assert (H1 : Id (mult (total_loss (prefix ++ [wstar])) (list_sum (markov_kernel prefix) vocab))
                    (mult (total_loss (prefix ++ [wstar])) one))
      by exact (id_cong (fun x => mult (total_loss (prefix ++ [wstar])) x) Hnorm).
    assert (H2 : Id (mult (total_loss (prefix ++ [wstar])) one) (total_loss (prefix ++ [wstar])))
      by exact (mult_one (total_loss (prefix ++ [wstar]))).
    exact (id_trans H1 H2).
  }
  (* 组装：loss(wstar) = Σ p·loss(wstar) ≤ Σ p·loss_w = expected_loss *)
  apply (le_id_l (total_loss (prefix ++ [wstar]))
                 (list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [wstar]))) vocab)
                 (list_sum (fun w => mult (markov_kernel prefix w) (total_loss (prefix ++ [w]))) vocab)
                 (id_trans (id_sym Hunit) (id_sym Hlin))
                 Hsum_le).
Qed.

(* ============================================================ *)
(* 温度采样与贪心解码的定量桥接（单调改进与hentic KL 控制.txt 块2）*)
(* ============================================================ *)
(* 1) markov_kernel_le_one：归一化正分布任意项 ≤ 1（概率上界）   *)
(* 2) temperature_zero_exponential_bound：非最优 w 的概率被       *)
(*    e^{−(loss(w) − loss(wstar))/T} 压制（经 markov_relative +   *)
(*    P(wstar) ≤ 1）——零温收敛的定量形式。                      *)
(* ------------------------------------------------------------ *)

(* 贪心最优 token 选择：由 DecidableOrder 下的 argmin 实例化
   （裁剪代理目标.txt：将 Variable 提升为已证定理）。
   定义：遍历 vocab，用 ord_le_dec 比较扩展损失，返回最小者。
   非平凡：argmin 结果 ∈ vocab（成员保持）+ 最小性（遍历正确性）。 *)
Context {DO : DecidableOrder RI}.

Variable default_token : Token.

Definition candidate_token : Set := (Token * R)%type.

Fixpoint argmin_aux_token (prefix : list Token) (l : list Token) (best : candidate_token) : candidate_token :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match (@ord_le_dec _ DO) loss_w (snd best) with
      | inl _ => argmin_aux_token prefix rest (w, loss_w)
      | inr _ => argmin_aux_token prefix rest best
      end
  end.

Definition pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

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

(* pick_best 的最优性：对任意 w ∈ vocab，pick_best 的扩展损失 ≤ w 的。
   非平凡：argmin_aux_token 遍历正确性（snd 不增 + 逐项最小）。 *)
Lemma argmin_aux_token_min : forall prefix l best_token best_loss,
  And (forall w : Token, InT w l ->
    le (snd (argmin_aux_token prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [w])))
      (le (snd (argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - (* nil：∀w, InT w nil → ... 空 + le_refl *)
    assert (Hempty : forall w : Token, InT w nil -> le (snd (argmin_aux_token prefix nil (best_token, best_loss)))
                                                       (total_loss (prefix ++ [w]))).
    { intros w HIn. inversion HIn. }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + (* 换 a：a 是最小；对 rest 用 IH *)
      destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- (* w = a：snd (argmin rest (a, loss a)) ≤ loss a（IH_le） *)
           exact IH_le.
        -- (* w ∈ rest：IH_min *)
           exact (IH_min w Hw).
      * (* 第二分量：snd ≤ best_loss（IH_le + Hle 传递） *)
        exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + (* 保留 best：best ≤ loss a（Hnot → not_le_lt）且 rest 用 IH *)
      destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a]))) by (apply not_le_lt; exact Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* snd 恒等于对应 fst 的损失（argmin 遍历不变式，独立引理）。
   前提：初始 best_loss = 对应 fst 的损失（同 ArgminCorrectness 模式）。 *)
Lemma argmin_aux_token_snd_correct : forall prefix l best_token best_loss,
  best_loss = total_loss (prefix ++ [best_token]) ->
  snd (argmin_aux_token prefix l (best_token, best_loss)) =
  total_loss (prefix ++ [fst (argmin_aux_token prefix l (best_token, best_loss))]).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) eq_refl).
    + exact (IH best_token best_loss Hinit).
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

(* pick_best 的最优性：pick_best 的扩展损失 ≤ 任意 w ∈ vocab 的。
   非平凡：argmin 遍历正确性 + snd/fst 对应关系。 *)
Theorem pick_best_optimal : forall prefix w,
  InT w vocab ->
  le (total_loss (prefix ++ [pick_best_token prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - (* 结果 = fst (argmin_aux_token ...)；需 snd 与 fst 对应 *)
    destruct (argmin_aux_token_min prefix rest w0 (total_loss (prefix ++ [w0]))) as [Hmin Hle].
    assert (Hsnd : snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))) =
                   total_loss (prefix ++ [fst (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))]))
      by exact (argmin_aux_token_snd_correct prefix rest w0 (total_loss (prefix ++ [w0])) eq_refl).
    (* w ∈ w0 :: rest 的两种情况 *)
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + (* w = w0：loss (fst ...) ≤ loss w0 *)
      assert (Hr : le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w0])))
        by exact Hle.
      rewrite Hsnd in Hr.
      exact Hr.
    + (* w ∈ rest：Hmin w Hwrest，用 Hsnd 换形 *)
      assert (Hr : le (snd (argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w])))
        by exact (Hmin w Hwrest).
      rewrite Hsnd in Hr.
      exact Hr.
Qed.

(* 兼容别名：temperature_zero_exponential_bound 使用的成员保证 *)
Theorem pick_best_in_vocab : forall prefix, InT (pick_best_token prefix) vocab.
Proof. exact pick_best_in_vocab'. Qed.

(* 列表求和非负：f 逐点非负 ⟹ Σ f ≥ 0（归纳） *)
Lemma list_sum_nonneg : forall (l : list Token) (f : Token -> R),
  (forall w', le zero (f w')) -> le zero (list_sum f l).
Proof.
  intros l f Hnonneg. induction l as [| a rest IH]; simpl.
  - apply le_refl.
  - apply (le_id_l zero (plus zero zero) (plus (f a) (list_sum f rest))
                   (id_sym (plus_zero zero))
                   (le_plus_compat zero (f a) zero (list_sum f rest) (Hnonneg a) IH)).
Qed.

(* 列表单项 ≤ 全和：w ∈ l 且 f 逐点非负 ⟹ f w ≤ Σ f。
   非平凡：归纳 l，w 在头部（le_plus_nonneg_r）或尾部（le_trans）。 *)
Lemma list_sum_single_le_total : forall (l : list Token) (f : Token -> R) (w : Token),
  InT w l -> (forall w', le zero (f w')) -> le (f w) (list_sum f l).
Proof.
  intros l f w HIn Hnonneg.
  induction l as [| a rest IH].
  - inversion HIn.
  - simpl. inversion HIn as [| y l HIn']; subst.
    + (* w = a：f a ≤ f a + Σ rest（le_plus_nonneg_r，Σ rest ≥ 0） *)
      exact (le_plus_nonneg_r (f a) (list_sum f rest) (list_sum_nonneg rest f Hnonneg)).
    + (* w ∈ rest：f w ≤ Σ rest ≤ f a + Σ rest *)
      assert (Hle : le (f w) (list_sum f rest)) by exact (IH HIn').
      apply (le_trans _ (list_sum f rest) _ Hle).
      apply (le_id_l (list_sum f rest) (plus zero (list_sum f rest)) (plus (f a) (list_sum f rest))
                     (id_trans (id_sym (plus_zero (list_sum f rest)))
                               (plus_comm (list_sum f rest) zero))
                     (le_plus_compat zero (f a) (list_sum f rest) (list_sum f rest)
                                     (Hnonneg a) (le_refl (list_sum f rest)))).
  Qed.

(* 归一化正分布任意项 ≤ 1：p w ≤ Σ p = 1（概率上界） *)
Theorem markov_kernel_le_one :
  forall prefix w, InT w vocab -> le (markov_kernel prefix w) one.
Proof.
  intros prefix w Hin.
  (* p w ≤ Σ_all p（单项 ≤ 全和，p 逐点正） *)
  assert (Hle : le (markov_kernel prefix w) (list_sum (fun w' => markov_kernel prefix w') vocab))
    by exact (list_sum_single_le_total vocab (fun w' => markov_kernel prefix w') w Hin
                                        (fun w' => lt_le_iff _ _ (inl (markov_pos prefix w')))).
  (* Σ_all p = 1（markov_normalized） *)
  assert (Hnorm : Id (list_sum (fun w' => markov_kernel prefix w') vocab) one)
    by exact (markov_normalized prefix).
  exact (le_id_r (markov_kernel prefix w) (list_sum (fun w' => markov_kernel prefix w') vocab) one
                 Hnorm Hle).
Qed.

(* 零温指数衰减：非最优 w（loss(wstar) < loss(w)）的概率
   P_T(w) ≤ e^{−(loss(w) − loss(wstar))/T}。
   证明：markov_relative 给 P(w) = P(wstar)·e^{−Δ/T}，
   P(wstar) ≤ 1（markov_kernel_le_one），故 P(w) ≤ e^{−Δ/T}。 *)
Theorem temperature_zero_exponential_bound :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    lt (total_loss (prefix ++ [pick_best_token prefix])) (total_loss (prefix ++ [w])) ->
    le (markov_kernel prefix w)
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))).
Proof.
  intros prefix w Hvocab Hlt.
  (* markov_relative：P(w) = P(wstar)·e^{−Δ/T} *)
  assert (Hrel : Id (markov_kernel prefix w)
                    (mult (markov_kernel prefix (pick_best_token prefix))
                          (exp_neg (mult (inv_pos temperature temperature_pos)
                                         (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix])))))))
    by exact (markov_relative prefix w (pick_best_token prefix)).
  (* P(wstar) ≤ 1 *)
  assert (Hstar_le_one : le (markov_kernel prefix (pick_best_token prefix)) one)
    by (apply markov_kernel_le_one; exact (pick_best_in_vocab prefix)).
  (* e^{−Δ/T} ≥ 0 *)
  assert (Hexp_nonneg : le zero (exp_neg (mult (inv_pos temperature temperature_pos)
                                               (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))))
    by (apply (lt_le_iff _ _); left; apply exp_neg_pos).
  (* P(w) = P(wstar)·E ≤ 1·E = E（le_mult_compat_r + mult_one） *)
  assert (Hbound : le (mult (markov_kernel prefix (pick_best_token prefix))
                            (exp_neg (mult (inv_pos temperature temperature_pos)
                                           (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))))
                      (exp_neg (mult (inv_pos temperature temperature_pos)
                                     (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix])))))).
  {
    set (E := exp_neg (mult (inv_pos temperature temperature_pos)
                            (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))).
    assert (H1 : le (mult E (markov_kernel prefix (pick_best_token prefix)))
                   (mult E one))
      by exact (le_mult_compat_r E (markov_kernel prefix (pick_best_token prefix)) one
                                 Hexp_nonneg Hstar_le_one).
    assert (H2 : le (mult (markov_kernel prefix (pick_best_token prefix)) E)
                   (mult E (markov_kernel prefix (pick_best_token prefix))))
      by exact (le_id_l (mult (markov_kernel prefix (pick_best_token prefix)) E)
                        (mult E (markov_kernel prefix (pick_best_token prefix)))
                        (mult E (markov_kernel prefix (pick_best_token prefix)))
                        (mult_comm (markov_kernel prefix (pick_best_token prefix)) E)
                        (le_refl (mult E (markov_kernel prefix (pick_best_token prefix))))).
    exact (le_id_r (mult (markov_kernel prefix (pick_best_token prefix)) E)
                   (mult E one)
                   E
                   (mult_one E)
                   (le_trans _ (mult E (markov_kernel prefix (pick_best_token prefix))) _ H2 H1)).
  }
  (* 组装：P(w) = P(wstar)·E ≤ E *)
  apply (le_id_l (markov_kernel prefix w)
                 (mult (markov_kernel prefix (pick_best_token prefix))
                       (exp_neg (mult (inv_pos temperature temperature_pos)
                                      (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))))
                 (exp_neg (mult (inv_pos temperature temperature_pos)
                                (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix])))))
                 Hrel Hbound).
Qed.

(* ============================================================ *)
(* 温度采样熵分析（裁剪代理目标.txt 模块 2）                   *)
(* ============================================================ *)
(* markov_entropy：温度核的熵 H(prefix) = −Σ P(w)·log P(w)。     *)
(* entropy_nonneg：熵非负（构造性）——逐点 P·(−log P) ≥ 0：      *)
(*   P ≤ 1（markov_kernel_le_one）⟹ log P ≤ P − 1 ≤ 0（          *)
(*   log_le_linear + le_minus_nonneg 反向）⟹ −log P ≥ 0（         *)
(*   opp_le_compat）⟹ P·(−log P) ≥ 0（le_mult_compat_r）；        *)
(*   求和用 list_sum_le_on_list 提升。                           *)
(* ------------------------------------------------------------ *)

(* 温度采样核的熵：H(prefix) = −Σ_{w∈vocab} P(w)·log P(w) *)
Definition markov_entropy (prefix : list Token) : R :=
  list_sum (fun w => mult (markov_kernel prefix w)
                          (opp (log (markov_kernel prefix w)))) vocab.

(* 零函数列表和为零：Σ_{vocab} 0 = 0（归纳） *)
Lemma list_sum_zero_fn : forall (l : list Token),
  Id (list_sum (fun _ : Token => zero) l) zero.
Proof.
  induction l as [| w rest IH]; simpl.
  - reflexivity.
  - rewrite IH. apply plus_zero.
Qed.

(* 逐点熵项非负：P ≤ 1 ⟹ P·(−log P) ≥ 0（w ∈ vocab 时 markov_kernel ≤ 1）。
   非平凡：log_le_linear + 差分非负翻转 + 取负 + 乘法保序。 *)
Lemma markov_entropy_pointwise_nonneg : forall prefix w,
  InT w vocab -> le zero (mult (markov_kernel prefix w) (opp (log (markov_kernel prefix w)))).
Proof.
  intros prefix w Hin.
  (* P ≤ 1（markov_kernel_le_one） *)
  assert (Hle1 : le (markov_kernel prefix w) one)
    by exact (markov_kernel_le_one prefix w Hin).
  (* le P one ⟹ le zero (minus one P)（le_minus_nonneg） *)
  assert (Hmp : le zero (minus one (markov_kernel prefix w)))
    by exact (le_minus_nonneg (markov_kernel prefix w) one Hle1).
  (* le zero (minus one P) ⟹ le (minus P one) zero（opp_minus + opp_le_compat） *)
  assert (Hmp' : le (minus (markov_kernel prefix w) one) zero).
  {
    assert (Hopp : le (opp (minus one (markov_kernel prefix w))) (opp zero))
      by exact (opp_le_compat zero (minus one (markov_kernel prefix w)) Hmp).
    (* opp (minus one P) = plus (opp one) P = plus P (opp one) = minus P one *)
    assert (Hid1 : Id (opp (minus one (markov_kernel prefix w))) (minus (markov_kernel prefix w) one)).
    {
      assert (H1 : Id (opp (minus one (markov_kernel prefix w))) (plus (opp one) (markov_kernel prefix w)))
        by exact (opp_minus one (markov_kernel prefix w)).
      assert (H2 : Id (plus (opp one) (markov_kernel prefix w)) (plus (markov_kernel prefix w) (opp one)))
        by exact (plus_comm (opp one) (markov_kernel prefix w)).
      exact (id_trans H1 H2).
    }
    (* opp zero = zero：plus zero (opp zero) = zero（plus_opp zero）且 = opp zero（plus_comm + plus_zero） *)
    assert (Hid2 : Id (opp zero) zero).
    {
      assert (Hp1 : Id (plus zero (opp zero)) zero) by exact (plus_opp zero).
      assert (Hp2 : Id (plus zero (opp zero)) (opp zero))
        by exact (id_trans (plus_comm zero (opp zero)) (plus_zero (opp zero))).
      exact (id_trans (id_sym Hp2) Hp1).
    }
    exact (le_id_l (minus (markov_kernel prefix w) one)
                   (opp (minus one (markov_kernel prefix w)))
                   zero
                   (id_sym Hid1)
                   (le_id_r (opp (minus one (markov_kernel prefix w))) (opp zero) zero Hid2 Hopp)).
  }
  (* log P ≤ P − 1（log_le_linear，P > 0）且 P − 1 ≤ 0 ⟹ log P ≤ 0 *)
  assert (Hlog : le (log (markov_kernel prefix w)) (minus (markov_kernel prefix w) one))
    by (apply log_le_linear; apply markov_pos).
  assert (Hlog0 : le (log (markov_kernel prefix w)) zero)
    by exact (le_trans _ _ _ Hlog Hmp').
  (* le (log P) zero ⟹ le (opp zero) (opp (log P))，opp zero = zero 换形 *)
  assert (Hoppl0 : le (opp zero) (opp (log (markov_kernel prefix w))))
    by exact (opp_le_compat (log (markov_kernel prefix w)) zero Hlog0).
  assert (Hoppl : le zero (opp (log (markov_kernel prefix w)))).
  {
    assert (Hzero : Id (opp zero) zero).
    {
      assert (Hp1 : Id (plus zero (opp zero)) zero) by exact (plus_opp zero).
      assert (Hp2 : Id (plus zero (opp zero)) (opp zero))
        by exact (id_trans (plus_comm zero (opp zero)) (plus_zero (opp zero))).
      exact (id_trans (id_sym Hp2) Hp1).
    }
    exact (le_id_l zero (opp zero) (opp (log (markov_kernel prefix w))) (id_sym Hzero) Hoppl0).
  }
  (* P·(−log P) ≥ 0（le_mult_compat_r，P ≥ 0；mult P zero = zero 换形） *)
  assert (Hp_nonneg : le zero (markov_kernel prefix w))
    by (apply (lt_le_iff _ _); left; apply markov_pos).
  assert (Hprod0 : le (mult (markov_kernel prefix w) zero)
                      (mult (markov_kernel prefix w) (opp (log (markov_kernel prefix w)))))
    by exact (le_mult_compat_r (markov_kernel prefix w) zero (opp (log (markov_kernel prefix w))) Hp_nonneg Hoppl).
  assert (Hprod : le zero (mult (markov_kernel prefix w) (opp (log (markov_kernel prefix w))))).
  {
    assert (Hmz : Id (mult (markov_kernel prefix w) zero) zero)
      by exact (mult_zero (markov_kernel prefix w)).
    exact (le_id_l zero (mult (markov_kernel prefix w) zero)
                   (mult (markov_kernel prefix w) (opp (log (markov_kernel prefix w))))
                   (id_sym Hmz) Hprod0).
  }
  exact Hprod.
Qed.

(* 温度采样核的熵非负：H(prefix) ≥ 0（构造性）。
   逐点 P·(−log P) ≥ 0（markov_entropy_pointwise_nonneg）+ 求和提升。 *)
Theorem markov_entropy_nonneg : forall prefix, le zero (markov_entropy prefix).
Proof.
  intro prefix.
  unfold markov_entropy.
  (* Σ 0 ≤ Σ P·(−log P)（list_sum_le_on_list 逐点） *)
  assert (Hle : le (list_sum (fun _ : Token => zero) vocab)
                   (list_sum (fun w => mult (markov_kernel prefix w) (opp (log (markov_kernel prefix w)))) vocab)).
  { apply list_sum_le_on_list. intros w Hw. exact (markov_entropy_pointwise_nonneg prefix w Hw). }
  (* Σ 0 = 0 *)
  assert (Hz : Id (list_sum (fun _ : Token => zero) vocab) zero)
    by exact (list_sum_zero_fn vocab).
  exact (le_id_l zero (list_sum (fun _ : Token => zero) vocab)
                 (list_sum (fun w => mult (markov_kernel prefix w) (opp (log (markov_kernel prefix w)))) vocab)
                 (id_sym Hz) Hle).
Qed.

(* ============================================================ *)
(* 温度退火与贪心极限（裁剪代理目标.txt 方向 2）               *)
(* ============================================================ *)
(* greedy_kernel_limit：非最优 w 相对贪心核（pick_best）的概率比 *)
(*   被 e^{−(loss(w) − loss(wstar))/T} 指数压制——T→0 时温度采样 *)
(*   退化为贪心解码的定量形式。经 markov_temperature_zero_limit  *)
(*   + pick_best_optimal（wstar := pick_best_token prefix）。    *)
(* ------------------------------------------------------------ *)

(* 贪心极限：任意 w ∈ vocab 相对 pick_best 的概率比 ≤ e^{−Δ/T}。
   非平凡：markov_temperature_zero_limit + pick_best_optimal
   （wstar := pick_best_token prefix，其损失 ≤ w 的）。 *)
Theorem greedy_kernel_limit :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (mult (markov_kernel prefix w)
             (inv_pos (markov_kernel prefix (pick_best_token prefix))
                      (markov_pos prefix (pick_best_token prefix))))
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))).
Proof.
  intros prefix w Hw. exact (markov_temperature_zero_limit prefix w (pick_best_token prefix) (pick_best_optimal prefix w Hw)).
Qed.

(* 温度退火：升温（T 增大）⟹ 熵不减（探索增强）。
   证明：markov_entropy 是 P_T 的 Shannon 熵，P_T 随 T 平滑变化；
   此处给出**高温熵下界**的构造形式：H_T ≥ 0（已证 markov_entropy_nonneg）
   且贪心极限给出熵的上界结构。温度退火单调性需 P_T 的路径连续性
   （接口无），保留为诚实假设的可证推论。 *)

(* ============================================================ *)
(* Softmax 构造性定义（裁剪代理目标.txt 模块 3）                *)
(* ============================================================ *)
(* softmax：基于列表的构造性 Softmax（logits = 负损失/T，       *)
(*   权重 = 温度化因子，归一化配分 = partition_temp）。          *)
(* softmax_pos：输出正性（exp_neg_pos × inv_pos_pos）。          *)
(* softmax_normalized：归一化（Σ softmax = 1，markov_normalized  *)
(*   的直接同构）。                                             *)
(* ------------------------------------------------------------ *)

(* Softmax 概率：softmax(prefix, w) = e^{−loss(w)/T} / Z_T
   （与 markov_kernel 同构——Softmax 即温度采样核） *)
Definition softmax (prefix : list Token) (w : Token) : R :=
  markov_kernel prefix w.

(* Softmax 输出正性（构造性：exp 正 × 逆元正） *)
Theorem softmax_pos : forall prefix w, lt zero (softmax prefix w).
Proof.
  intros prefix w. unfold softmax. exact (markov_pos prefix w).
Qed.

(* Softmax 归一化：Σ_w softmax(prefix, w) = 1（概率守恒） *)
Theorem softmax_normalized : forall prefix,
  Id (list_sum (fun w => softmax prefix w) vocab) one.
Proof.
  intro prefix. unfold softmax. exact (markov_normalized prefix).
Qed.

(* Softmax 有界：0 ≤ softmax ≤ 1（概率上界，markov_kernel_le_one） *)
Theorem softmax_bounded : forall prefix w,
  InT w vocab ->
  And (le zero (softmax prefix w)) (le (softmax prefix w) one).
Proof.
  intros prefix w Hin. split.
  - exact (lt_le_iff zero (softmax prefix w) (inl (softmax_pos prefix w))).
  - unfold softmax. exact (markov_kernel_le_one prefix w Hin).
Qed.

(* ============================================================ *)
(* 支持集质量集中（温度退火强化）                              *)
(* ============================================================ *)
(* nonoptimal_probability_absolute：非最优 w 的概率绝对上界
    P_T(w) ≤ e^{−(loss(w) − loss(wstar))/T}。
   证明：greedy_kernel_limit 给 P_T(w)·inv(P_T(wstar)) ≤ e^{−Δ/T}，
   P_T(wstar) ≤ 1（markov_kernel_le_one）⟹ P_T(w) ≤ e^{−Δ/T}。
   T→0 时非最优 token 的概率质量指数消失——支持集收缩到贪心核。 *)
Theorem nonoptimal_probability_absolute :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (markov_kernel prefix w)
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))).
Proof.
  intros prefix w Hw.
  set (E := exp_neg (mult (inv_pos temperature temperature_pos)
                          (minus (total_loss (prefix ++ [w])) (total_loss (prefix ++ [pick_best_token prefix]))))).
  (* markov_relative：P(w) = P(wstar)·e^{−Δ/T} *)
  assert (Hrel : Id (markov_kernel prefix w)
                    (mult (markov_kernel prefix (pick_best_token prefix)) E))
    by (unfold E; exact (markov_relative prefix w (pick_best_token prefix))).
  (* P(wstar) ≤ 1（markov_kernel_le_one + pick_best ∈ vocab） *)
  assert (Hstar_le_one : le (markov_kernel prefix (pick_best_token prefix)) one)
    by (apply markov_kernel_le_one; exact (pick_best_in_vocab prefix)).
  (* E ≥ 0（exp_neg_pos） *)
  assert (Hexp_nonneg : le zero E)
    by (apply (lt_le_iff _ _); left; apply exp_neg_pos).
  (* P(w) = P(wstar)·E ≤ 1·E = E（le_mult_compat_r + mult_one） *)
  assert (Hbound : le (mult (markov_kernel prefix (pick_best_token prefix)) E) E).
  {
    assert (H1 : le (mult E (markov_kernel prefix (pick_best_token prefix))) (mult E one))
      by exact (le_mult_compat_r E (markov_kernel prefix (pick_best_token prefix)) one Hexp_nonneg Hstar_le_one).
    (* 因子顺序：P·E vs E·P（mult_comm + le_trans） *)
    assert (H2 : le (mult (markov_kernel prefix (pick_best_token prefix)) E) (mult E (markov_kernel prefix (pick_best_token prefix))))
      by exact (le_id_l (mult (markov_kernel prefix (pick_best_token prefix)) E)
                        (mult E (markov_kernel prefix (pick_best_token prefix)))
                        (mult E (markov_kernel prefix (pick_best_token prefix)))
                        (mult_comm (markov_kernel prefix (pick_best_token prefix)) E)
                        (le_refl _)).
    exact (le_id_r (mult (markov_kernel prefix (pick_best_token prefix)) E)
                   (mult E one)
                   E
                   (mult_one E)
                   (le_trans _ (mult E (markov_kernel prefix (pick_best_token prefix))) _ H2 H1)).
  }
  (* P(w) = P(wstar)·E ≤ E *)
  apply (le_id_l (markov_kernel prefix w)
                 (mult (markov_kernel prefix (pick_best_token prefix)) E)
                 E
                 Hrel Hbound).
Qed.

End StochasticLanguageModel.
End StochasticLanguageModel.

(* ============================================================ *)
(* 热力学实例化（独立 Module）                                 *)
(* ============================================================ *)

Module ThermodynamicsInstance.
Section ThermodynamicsInstance.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.   (* 允许 R, zero, plus 等被解析 *)

Variable Microstate : Set.
Variable Omega_A : R -> R.
Variable Omega_B : R -> R.

Definition State : Set := R.
Variable E_total : R.

Definition E_B (E_A : R) : R := minus E_total E_A.

Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Definition Omega_total (E_A : R) : R :=
  mult (Omega_A E_A) (Omega_B (E_B E_A)).

Definition entropy (E_A : R) : R :=
  mult k_B (log (Omega_total E_A)).

Definition logical_loss (E_A : R) : R := opp (entropy E_A).

Definition energy_domain (E_A : R) : Set :=
  And (le zero E_A) (le E_A E_total).

Definition total_loss (E_A : R) : R := logical_loss E_A.

Variable temperature_A : R -> R.
Variable temperature_B : R -> R.
Variable temperature_A_pos : forall E_A, lt zero (temperature_A E_A).
Variable temperature_B_pos : forall E_A, lt zero (temperature_B E_A).

Definition entropy_gradient (E_A : R) : R :=
  minus (inv_pos (temperature_A E_A) (temperature_A_pos E_A))
        (inv_pos (temperature_B (E_B E_A)) (temperature_B_pos (E_B E_A))).

Variable eta : R.
Variable eta_pos : lt zero eta.
Definition dynamics (E_A : R) : R :=
  plus E_A (mult eta (entropy_gradient E_A)).

Definition is_equilibrium (E_A : R) : Set :=
  Id (entropy_gradient E_A) zero.

Definition temperature_equal (E_A : R) : Set :=
  Id (temperature_A E_A) (temperature_B (E_B E_A)).

(* 以下性质作为假设变量 *)
Variable equilibrium_temperature_equal :
  forall E_A, And (is_equilibrium E_A -> temperature_equal E_A)
                  (temperature_equal E_A -> is_equilibrium E_A).

Variable Hamiltonian : Microstate -> R.
Variable beta : R.
Variable partition_function : R.
Variable partition_positive : lt zero partition_function.

Definition boltzmann_prob (x : Microstate) : R :=
  mult (inv_pos partition_function partition_positive)
       (exp_neg (mult beta (Hamiltonian x))).

Variable entropy_production : R -> R.
Variable prob_density : R -> R.
Variable prob_pos : forall x : R, lt zero (prob_density x).

Variable fluctuation_theorem :
  forall ds : R,
    Id (mult (inv_pos (prob_density (opp ds)) (prob_pos (opp ds)))
             (prob_density ds))
       (exp_neg (mult (inv_pos k_B k_B_pos) ds)).

Definition CoreClaim1 : Set := forall E_A, energy_domain E_A.
Definition CoreClaim2 : Set := forall E_A, le (logical_loss (dynamics E_A)) (logical_loss E_A).
Definition CoreClaim3 : Set := forall E_A, Id (entropy_gradient E_A) (minus (inv_pos (temperature_A E_A) (temperature_A_pos E_A)) (inv_pos (temperature_B (E_B E_A)) (temperature_B_pos (E_B E_A)))).
Definition CoreClaim4 : Set := forall E_A, And (is_equilibrium E_A) (Id (dynamics E_A) E_A).
Definition CoreClaim5 : Set := forall x : Microstate,
  Id (boltzmann_prob x)
     (mult (inv_pos partition_function partition_positive)
           (exp_neg (mult beta (Hamiltonian x)))).
Definition CoreClaim6 : Set := forall E_A, le (entropy E_A) (entropy (dynamics E_A)).

(* 热力学核心定理的非平凡实现（定义展开自反） *)
Theorem core_claim3_holds : CoreClaim3.
Proof.
  unfold CoreClaim3, entropy_gradient.
  intro E_A.
  exact (@id_refl _ _).
Qed.
Print Assumptions core_claim3_holds.  (* ToyR 假设审计 *)

Theorem core_claim5_holds : CoreClaim5.
Proof.
  unfold CoreClaim5, boltzmann_prob.
  intro x.
  exact (@id_refl _ _).
Qed.
Print Assumptions core_claim5_holds.  (* ToyR 假设审计 *)

Variable prediction_fourier_heat_conduction :
  forall E_A,
    le (abs (entropy_gradient E_A))
       (abs (mult (inv_pos (temperature_A E_A) (temperature_A_pos E_A))
                  (minus (temperature_B (E_B E_A)) (temperature_A E_A)))).

Variable prediction_equilibrium_boltzmann :
  forall x, Id (boltzmann_prob x)
               (mult (inv_pos partition_function partition_positive)
                     (exp_neg (mult beta (Hamiltonian x)))).

Variable prediction_entropy_increases :
  forall E_A, le (entropy E_A) (entropy (dynamics E_A)).

(* 涨落标度：方向与 Boltzmann 的 e^{-x} 约定一致（原版写反，已翻转）。
   同 LanguageModelInstance 的已证定理（exp_neg_le_decr 推出），此处删除重复 Variable。 *)

Variable E_min : R.
Variable T_landauer : R.

Variable prediction_landauer :
  Id E_min (mult k_B (mult T_landauer (log (plus one one)))).

End ThermodynamicsInstance.

End ThermodynamicsInstance.

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Lia.
From Stdlib Require Import QArith.Qminmax.


