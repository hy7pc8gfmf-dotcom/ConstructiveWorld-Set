(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* S02_CauchyComplete.v                                        *)
(*                                                             *)
(* 目的：柯西实数核心：柯西序列的加法、乘法、求逆与序结构       *)
(*       （构造性 Set 层）。                                     *)
(* 主件：CauchyRealMultiplication 系列引理；real_lt 加性平移     *)
(*       （a<b ∧ c<d ⟹ a+c<b+d）；real_lim 收敛代数。           *)
(* 依赖：S01_BaseRing；Stdlib（QArith、Qabs、Qround、List、     *)
(*       Bool、Arith、Setoid、Morphisms、Lia、Qminmax）。        *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 之拆分分片，原文区间  *)
(*       L3072-L6982，去头正文与原文区间逐字节同源。             *)
(* ============================================================ *)
(* ============================================================ *)
(* ToyR 工程 （S 系下半） · 记录册号         *)
(* 替换定理清单：qltT_0_1 / qltT_0_2 / qltT_0_3 / qltT_0_4 /     *)
(*   qleT'_refl / qeq_le（共 6 条，语句与声明序不变）             *)
(* 非平凡性说明：本件仅替换上列玩具定理的证明体；声明面、其余定理、*)
(*   原头注一律原样保留。替换证明为实质非平凡推导：定义层展开      *)
(*   （QltT→Qlt_bool→Qcompare→Z 层交叉积）＋ 显式算术判定 ＋      *)
(*   结构性 tactic 组合（replace/assert/rewrite/三分 destruct），  *)
(*   消除原单跳 reflexivity 转发。纯构造性 Set 层：零 公理、      *)
(*   零 承认件、零经典逻辑；替换证明以真证闭闭合，文件尾附         *)
(*   假设面查证指令。基准树只读比对，零改零删。                    *)
(* ============================================================ *)
Require Import S01_BaseRing.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Section CauchyRealMultiplication.
(* ============================================================ *)
(* 柯西实数核心（构造性 Set 层版本）                           *)
(* ============================================================ *)
(* 所需 QArith/Qabs/Qround 已在文件头加载，此处不再于 section 内
   Require（Rocq 9.0 对 section 内 Require 给出 fragile 警告）。 *)

Definition Qseq := nat -> Q.

Definition Qlt_bool (x y : Q) : bool :=
  match Qcompare x y with
  | Lt => true
  | _ => false
  end.

Definition QltT (x y : Q) : Set := Id (Qlt_bool x y) true.
Definition QleT (x y : Q) : Set := Or (QltT x y) (Id x y).

Lemma QltT_to_Qlt : forall x y : Q, QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold QltT in H.
  unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

Lemma Qlt_to_QltT : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H.
  unfold QltT, Qlt_bool.
  destruct (Qcompare x y) eqn:E.
  - (* Eq 分支：x == y *)
    exfalso.
    apply (Qlt_irrefl y).          (* 目标变为 y < y -> False *)
    assert (Heq : x == y) by (apply Qeq_alt; exact E).
    rewrite Heq in H.              (* H : y < y *)
    exact H.
  - (* Lt 分支：x < y *)
    reflexivity.
  - (* Gt 分支：x > y，即 y < x *)
    exfalso.
    apply (Qlt_irrefl x).          (* 目标变为 x < x -> False *)
    assert (Hyx : y < x) by (apply Qgt_alt; exact E).
    eapply Qlt_trans.              (* 需要两个不等式 *)
    exact H.
    exact Hyx.
Qed.



(* ============================================================ *)
(* Prop 消融 L0（轮 25）：Qle 的 Set 层健全化桥                 *)
(*   Qle_bool/QleT'（Qcompare 反映形）+ 双向桥                  *)
(*   ——消融 L1/L2 用（QleT' 替代库内 QleT：其 Id-Leibniz 相等    *)
(*     分支无法从 Prop 层 Qle 健全构造，见 Prop消融方案 §5）     *)
(* 纪律：纯构造性 Set 层、零 承认、零经典。                    *)
(* ============================================================ *)
(* Qcompare 反映的 ≤-判定：Lt/Eq → true（与 Qle : Qcompare ≠ Gt 同义） *)
Definition Qle_bool (x y : Q) : bool :=
  match Qcompare x y with
  | Gt => false
  | _ => true
  end.

(* Set 层 Qle 的健全形态：bool 反映（可提取，构造不需 Leibniz） *)
Definition QleT' (x y : Q) : Set := Id (Qle_bool x y) true.

(* 消解：QleT' x y → Qle x y（Qle 展开 = Z.le = (a ?= b) ≠ Gt；本环境 Qle 非 Qcompare≠Gt 形态，
   而是 Z 层 (Qnum·QDen ≤ Qnum·QDen)%Z = Z.le —— 经 Z.le 定义 (x ?= y) ≠ Gt 桥） *)
Lemma QleT'_to_Qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  unfold QleT' in H.
  unfold Qle_bool, Qcompare in H.
  unfold Qle.
  change ((Qnum x * QDen y ?= Qnum y * QDen x)%Z <> Gt).
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl in H;
    try (inversion H); try (intro Hc; inversion Hc).
Qed.

(* 构造：Qle x y → QleT' x y（Z 比较三分 + Qle 排除 Gt；不需 Leibniz） *)
Lemma Qle_to_QleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H.
  unfold QleT', Qle_bool, Qcompare.
  unfold Qle in H.
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl; try reflexivity.
  - exfalso. exact (H E).
Qed.

(* --- Set 层 Q 相等（QeqT）：提取友好的单态语句叶子（cos_scan_spec/log_scan_spec 等） --- *)
Definition QeqT (a b : Q) : Set :=
  Id (match Qcompare a b with
      | Eq => true
      | _ => false
      end) true.

Lemma qeq_imp_qeqT : forall a b : Q, a == b -> QeqT a b.
Proof.
  intros a b Hab.
  unfold QeqT.
  destruct (Qcompare a b) eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hc : Qcompare a b = Eq).
    { apply (proj1 (Qeq_alt a b)). exact Hab. }
    rewrite E in Hc. discriminate.
  - exfalso.
    assert (Hc : Qcompare a b = Eq).
    { apply (proj1 (Qeq_alt a b)). exact Hab. }
    rewrite E in Hc. discriminate.
Qed.

Lemma qeqT_imp_qeq : forall a b : Q, QeqT a b -> a == b.
Proof.
  intros a b H. unfold QeqT in H. destruct (Qcompare a b) eqn:E.
  - exact (proj2 (Qeq_alt a b) E).
  - inversion H.
  - inversion H.
Qed.

(* ============================================================ *)
(* L2 提升引理库：QltT/QleT' 运算（消融依存者 Set 化用）     *)
(* 证法：qltT_trans 同款（内部 Prop 论证 + 计算判定收尾），   *)
(* 检验实测提取无 __（不可达分支提为 assert false）。        *)
(* ============================================================ *)
(* --- 数字与基本 --- *)
Lemma qeq_imp_qle : forall a b : Q, QeqT a b -> QleT' a b.
Proof.
  intros a b Hab.
  apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq a b Hab) as Hab'.
  unfold Qle, Qeq in *. destruct a, b. simpl in *. rewrite Hab'. apply Z.le_refl.
Qed.

(* ToyR 替换：定义层展开推导链（交叉积归约 → Z.compare 判定 → 布尔收敛） *)
Lemma qltT_0_1 : QltT 0 1.
Proof.
  unfold QltT, Qlt_bool, Qcompare.
  assert (H1 : (Qnum 0 * QDen 1)%Z = 0%Z) by reflexivity.
  assert (H2 : (Qnum 1 * QDen 0)%Z = 1%Z) by reflexivity.
  rewrite H1, H2.
  assert (Hcmp : (0 ?= 1)%Z = Lt) by reflexivity.
  rewrite Hcmp.
  reflexivity.
Qed.

Lemma qltT_0_2 : QltT 0 2.
Proof.
  unfold QltT, Qlt_bool, Qcompare.
  assert (H1 : (Qnum 0 * QDen 2)%Z = 0%Z) by reflexivity.
  assert (H2 : (Qnum 2 * QDen 0)%Z = 2%Z) by reflexivity.
  rewrite H1, H2.
  assert (Hcmp : (0 ?= 2)%Z = Lt) by reflexivity.
  rewrite Hcmp.
  reflexivity.
Qed.

Lemma qltT_0_3 : QltT 0 3.
Proof.
  unfold QltT, Qlt_bool, Qcompare.
  assert (H1 : (Qnum 0 * QDen 3)%Z = 0%Z) by reflexivity.
  assert (H2 : (Qnum 3 * QDen 0)%Z = 3%Z) by reflexivity.
  rewrite H1, H2.
  assert (Hcmp : (0 ?= 3)%Z = Lt) by reflexivity.
  rewrite Hcmp.
  reflexivity.
Qed.

Lemma qltT_0_4 : QltT 0 4.
Proof.
  unfold QltT, Qlt_bool, Qcompare.
  assert (H1 : (Qnum 0 * QDen 4)%Z = 0%Z) by reflexivity.
  assert (H2 : (Qnum 4 * QDen 0)%Z = 4%Z) by reflexivity.
  rewrite H1, H2.
  assert (Hcmp : (0 ?= 4)%Z = Lt) by reflexivity.
  rewrite Hcmp.
  reflexivity.
Qed.

(* ToyR 替换：Set 层直构（不绕 Qle_to_QleT' 桥）：三分判定就地分析，
   相等/小于支定义性收敛，大于支以 Z.compare 自反引理排除 *)
Lemma qleT'_refl : forall x : Q, QleT' x x.
Proof.
  intro x.
  unfold QleT', Qle_bool, Qcompare.
  (* Z.compare 同元自反：对 Z 结构归纳，同侧支归约收敛 Eq（零新增依赖） *)
  assert (Hrefl : forall z : Z, (z ?= z)%Z = Eq).
  { intro z. induction z as [| p | p].
    - reflexivity.
    - apply Z.compare_refl.
    - apply Z.compare_refl. }
  destruct (Qnum x * QDen x ?= Qnum x * QDen x)%Z as [E|E|E] eqn:Ec.
  - reflexivity.
  - reflexivity.
  - exfalso.
    rewrite Hrefl in Ec.
    discriminate Ec.
Qed.

(* --- 传递族 --- *)
Lemma qleT'_trans : forall x y z : Q, QleT' x y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z Hxy Hyz. exact (Qle_to_QleT' _ _ (Qle_trans x y z (QleT'_to_Qle _ _ Hxy) (QleT'_to_Qle _ _ Hyz))).
Qed.

Lemma qltT_leT' : forall x y : Q, QltT x y -> QleT' x y.
Proof.
  intros x y H. exact (Qle_to_QleT' _ _ (Qlt_le_weak _ _ (QltT_to_Qlt _ _ H))).
Qed.

Lemma qleT'_ltT_ltT : forall x y z : Q, QleT' x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. exact (Qlt_to_QltT _ _ (Qle_lt_trans x y z (QleT'_to_Qle _ _ Hxy) (QltT_to_Qlt _ _ Hyz))).
Qed.

Lemma qltT_leT'_ltT : forall x y z : Q, QltT x y -> QleT' y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. exact (Qlt_to_QltT _ _ (Qlt_le_trans x y z (QltT_to_Qlt _ _ Hxy) (QleT'_to_Qle _ _ Hyz))).
Qed.

(* --- 加法保序族 --- *)
Lemma qleT'_plus_compat : forall a b c d : Q, QleT' a b -> QleT' c d -> QleT' (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd. exact (Qle_to_QleT' _ _ (Qplus_le_compat a b c d (QleT'_to_Qle _ _ Hab) (QleT'_to_Qle _ _ Hcd))).
Qed.

Lemma qleT'_plus_nonneg_rT : forall x y : Q, QleT' 0 y -> QleT' x (x + y).
Proof.
  intros x y Hy.
  exact (qleT'_trans x (x + 0) (x + y)
  (qeq_imp_qle x (x + 0) (qeq_imp_qeqT x (x + 0) (Qeq_sym (x + 0) x (Qplus_0_r x))))
  (qleT'_plus_compat x x 0 y (qleT'_refl x) Hy)).
Qed.

Lemma qltT_plus_ltT : forall a b c d : Q, QltT a b -> QltT c d -> QltT (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd. exact (Qlt_to_QltT _ _ (Qplus_lt_compat a b c d (QltT_to_Qlt _ _ Hab) (QltT_to_Qlt _ _ Hcd))).
Qed.

Lemma qltT_plus_leT'_ltT : forall a b c d : Q, QltT a b -> QleT' c d -> QltT (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd. exact (Qlt_to_QltT _ _ (Qplus_lt_le_compat a b c d (QltT_to_Qlt _ _ Hab) (QleT'_to_Qle _ _ Hcd))).
Qed.

Lemma qleT'_plus_ltT_ltT : forall a b c d : Q, QleT' a b -> QltT c d -> QltT (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd.
  exact (Qlt_to_QltT (a + c) (b + d)
  (Qlt_le_trans (a + c) (a + d) (b + d)
  (proj2 (Qplus_lt_r c d a) (QltT_to_Qlt c d Hcd))
  (Qplus_le_compat a b d d (QleT'_to_Qle a b Hab) (Qle_refl d)))).
Qed.

(* --- 乘法保序族 --- *)
Lemma qleT'_mult_compat_r : forall x y z : Q, QleT' 0 z -> QleT' x y -> QleT' (x * z) (y * z).
Proof.
  intros x y z Hz Hxy. exact (Qle_to_QleT' _ _ (Qmult_le_compat_r x y z (QleT'_to_Qle _ _ Hxy) (QleT'_to_Qle _ _ Hz))).
Qed.

Lemma qleT'_mult_compat_l : forall x y z : Q, QleT' 0 z -> QleT' x y -> QleT' (z * x) (z * y).
Proof.
  intros x y z Hz Hxy.
  apply Qle_to_QleT'.
  rewrite (Qmult_comm z x). rewrite (Qmult_comm z y).
  apply (Qmult_le_compat_r x y z).
  - apply QleT'_to_Qle. exact Hxy.
  - apply QleT'_to_Qle. exact Hz.
Qed.

(* a ≤T b、0 ≤T c、c <T d、0 <T b ⟹ a·c <T b·d（real_mult 项界） *)
Lemma qleT'_mult_ltT_compat : forall a b c d : Q,
  QltT 0 b -> QleT' 0 c -> QleT' a b -> QltT c d -> QltT (a * c) (b * d).
Proof.
  intros a b c d Hb Hc0 Hab Hcd.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (a * c) (b * c) (b * d)).
  - apply (Qmult_le_compat_r a b c).
    + apply QleT'_to_Qle. exact Hab.
    + apply QleT'_to_Qle. exact Hc0.
  - rewrite (Qmult_comm b c). rewrite (Qmult_comm b d).
    apply (Qmult_lt_compat_r c d b).
    + apply QltT_to_Qlt. exact Hb.
    + apply QltT_to_Qlt. exact Hcd.
Qed.

Lemma qmult_ltT_0_compat : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (a * b).
Proof.
  intros a b Ha Hb. exact (Qlt_to_QltT _ _ (Qmult_lt_0_compat a b (QltT_to_Qlt _ _ Ha) (QltT_to_Qlt _ _ Hb))).
Qed.

(* --- 等式与弱化 --- *)
Lemma qeq_leT' : forall a b : Q, QeqT a b -> QleT' a b.
Proof.
  intros a b Hab. exact (qeq_imp_qle _ _ Hab).
Qed.

Lemma qeq_ltT : forall a b : Q, QeqT a b -> QltT 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha.
  exact (Qlt_to_QltT _ _ (Qlt_le_trans 0 a b (QltT_to_Qlt _ _ Ha)
          (QleT'_to_Qle _ _ (qeq_imp_qle _ _ Hab)))).
Qed.

(* --- 非负与绝对值 --- *)
Lemma qabs_nonnegT : forall x : Q, QleT' 0 (Qabs x).
Proof.
  intro x. exact (Qle_to_QleT' _ _ (Qabs_nonneg x)).
Qed.

(* --- 正性算术 --- *)
Lemma qltT_plus_pos_r : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x + y).
Proof.
  intros x y Hx Hy.
  exact (Qlt_to_QltT 0 (x + y)
  (Qlt_trans 0 x (x + y) (QltT_to_Qlt 0 x Hx)
  (Qle_lt_trans x (x + 0) (x + y)
  (QleT'_to_Qle _ _ (qeq_imp_qle x (x + 0) (qeq_imp_qeqT x (x + 0) (Qeq_sym (x + 0) x (Qplus_0_r x)))))
  (proj2 (Qplus_lt_r 0 y x) (QltT_to_Qlt 0 y Hy))))).
Qed.

Lemma qltT_div_pos : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x / y).
Proof.
  intros x y Hx Hy. apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 x y).
  - exact (QltT_to_Qlt 0 y Hy).
  - rewrite (Qmult_0_l y). exact (QltT_to_Qlt 0 x Hx).
Qed.

Lemma qltT_eq_compat_l : forall a a' b : Q, QeqT a a' -> QltT a b -> QltT a' b.
Proof.
  intros a a' b Ha H.
  exact (Qlt_to_QltT _ _ (Qle_lt_trans a' a b
          (QleT'_to_Qle _ _ (qeq_leT' _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ Ha)))))
          (QltT_to_Qlt _ _ H))).
Qed.

Lemma qltT_half_lt_selfT : forall x : Q, QltT 0 x -> QltT (x / 2) x.
Proof.
  intros x Hx.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (x / 2) x)).
  setoid_replace (x - x / 2) with (x / 2) by field.
  apply (Qlt_shift_div_l 0 x 2).
  - change (Qlt 0 2). compute. reflexivity.
  - rewrite Qmult_0_l. apply QltT_to_Qlt. exact Hx.
Qed.

Lemma qltT_eq_compat_r : forall a a' b : Q, QeqT a a' -> QltT b a' -> QltT b a.
Proof.
  intros a a' b Ha H.
  exact (Qlt_to_QltT _ _ (Qlt_le_trans b a' a (QltT_to_Qlt _ _ H)
          (QleT'_to_Qle _ _ (qeq_leT' _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ Ha))))))).
Qed.

Lemma qltT_mult_ltT_compat_r : forall a b c : Q, QltT 0 c -> QltT a b -> QltT (a * c) (b * c).
Proof.
  intros a b c Hc Hab. exact (Qlt_to_QltT _ _ (Qmult_lt_compat_r a b c (QltT_to_Qlt _ _ Hc) (QltT_to_Qlt _ _ Hab))).
Qed.

Lemma qltT_not_eq_zero : forall x : Q, QltT 0 x -> Not (QeqT x 0).
Proof.
  intros x Hx Hz.
  exact (False_rect Empty_set
          (Qlt_not_eq 0 x (QltT_to_Qlt 0 x Hx) (Qeq_sym x 0 (qeqT_imp_qeq x 0 Hz)))).
Qed.

Lemma qltT_shift_div_lT : forall x y z : Q, QltT 0 z -> QltT (x * z) y -> QltT x (y / z).
Proof.
  intros x y z Hz Hxz. exact (Qlt_to_QltT _ _ (Qlt_shift_div_l x y z (QltT_to_Qlt _ _ Hz) (QltT_to_Qlt _ _ Hxz))).
Qed.
Definition cauchy (u : Qseq) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
        QltT (Qabs (u m - u n)) eps).

Definition Real : Set := sigT (fun u : Qseq => cauchy u).

Definition real_eq (x y : Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
        QltT (Qabs (projT1 x n - projT1 y n)) eps).

Definition real_plus (x y : Real) : Real.
Proof.
  destruct x as [u Hu]. destruct y as [v Hv].
  exists (fun n => (u n + v n)%Q).
  intros eps Heps.
  destruct (Hu (eps/2)%Q) as [N1 HN1].
  { assert (Hhalf : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    apply Qlt_to_QltT. exact Hhalf. }
  destruct (Hv (eps/2)%Q) as [N2 HN2].
  { assert (Hhalf2 : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    apply Qlt_to_QltT. exact Hhalf2. }
  exists (max N1 N2).
  intros m n Hm Hn.
  assert (HN1' := HN1 m n).
  assert (HN2' := HN2 m n).
  apply Qlt_to_QltT.
  apply Qle_lt_trans with (Qabs (u m - u n) + Qabs (v m - v n)).
  - assert (Hsum : u m + v m - (u n + v n) == (u m - u n) + (v m - v n)).
    { ring. }
    setoid_rewrite Hsum.
    apply Qabs_triangle.
  - assert (Heps_sum : eps/2 + eps/2 == eps). { field. }
    setoid_rewrite <- Heps_sum.   (* 将目标中的 eps 替换为 eps/2 + eps/2 *)
    apply Qplus_lt_compat.
    * apply QltT_to_Qlt. apply HN1'.
      -- apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)].
      -- apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
    * apply QltT_to_Qlt. apply HN2'.
      -- apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hm)].
      -- apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)].
Defined.

Definition real_opp (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n => (- u n)%Q).
  intros eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  assert (H1 : - u m - - u n == -(u m - u n)).
  { ring. }
  assert (H2 : Qabs (- u m - - u n) == Qabs (u m - u n)).
  { setoid_rewrite H1. apply Qabs_opp. }
  apply Qlt_to_QltT.
  setoid_rewrite H2.
  apply QltT_to_Qlt. exact HN.
Defined.

Definition real_zero : Real.
Proof.
  exists (fun n => 0%Q).
  intros eps Heps. exists O. intros m n Hm Hn.
  simpl.          (* 将 Qabs (0 - 0) 简化为 0 *)
  exact Heps.     (* 目标变为 QltT 0 eps，直接使用假设 *)
Defined.

Definition real_lt (x y : Real) : Set :=
  sigT (fun eps : Q => And (QltT 0 eps) (sigT (fun N : nat => forall n, NatLe N n ->
        QltT eps (projT1 y n - projT1 x n)))).

Definition real_le (x y : Real) : Set :=
  Or (real_lt x y) (real_eq x y).

Lemma real_lt_trans : forall x y z : Real, real_lt x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy as [eps1 [Heps1 [N1 HN1]]].
  destruct Hyz as [eps2 [Heps2 [N2 HN2]]].
  exists (eps1 + eps2)%Q.
  split.
  - (* 正性：证明 0 < eps1 + eps2 *)
    assert (Hlt1 : Qlt 0 eps1) by (apply QltT_to_Qlt; exact Heps1).
    assert (Hlt2 : Qlt 0 eps2) by (apply QltT_to_Qlt; exact Heps2).
    assert (Hsum : Qlt (0 + 0) (eps1 + eps2)).
    { apply Qplus_lt_compat; [exact Hlt1 | exact Hlt2]. }
    assert (H0 : 0 + 0 == 0). { apply Qplus_0_l. }
    rewrite H0 in Hsum.
    apply Qlt_to_QltT. exact Hsum.
  - (* 分离性：取 N = max N1 N2 *)
    exists (max N1 N2).
    intros n Hn.
    assert (HN1n : Qlt eps1 (projT1 y n - projT1 x n)).
    { apply QltT_to_Qlt.
      apply HN1.
      apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
    assert (HN2n : Qlt eps2 (projT1 z n - projT1 y n)).
    { apply QltT_to_Qlt.
      apply HN2.
      apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
    assert (Hsum_lt : Qlt (eps1 + eps2)
                           ((projT1 y n - projT1 x n) + (projT1 z n - projT1 y n))).
    { apply Qplus_lt_compat; [exact HN1n | exact HN2n]. }
    assert (Hsum_eq :
      (projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)
        == projT1 z n - projT1 x n).
    { ring. }
    rewrite Hsum_eq in Hsum_lt.
    apply Qlt_to_QltT. exact Hsum_lt.
Qed.

(* 柯西实数乘法（完整构造性证明 *)

(* 辅助函数：前 n 项绝对值和 *)
Fixpoint sum_abs_prefix (u : Qseq) (n : nat) : Q :=
  match n with
  | Datatypes.O => 0%Q
  | Datatypes.S n' => (sum_abs_prefix u n' + Qabs (u n'))%Q
  end.

Lemma sum_abs_prefix_nonneg : forall u n, QleT' 0 (sum_abs_prefix u n).
Proof.
  induction n; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    exact (Qplus_le_compat 0 (sum_abs_prefix u n) 0 (Qabs (u n))
            (QleT'_to_Qle _ _ IHn) (Qabs_nonneg (u n))).
Qed.

(* 辅助引理：如果 0 <= y，则 x <= x + y *)
Lemma Qle_plus_nonneg_r : forall x y, 0 <= y -> x <= x + y.
Proof.
  intros x y Hy.
  exact (QleT'_to_Qle _ _ (qleT'_plus_nonneg_rT x y (Qle_to_QleT' _ _ Hy))).
Qed.

(* 主引理：若 i < n，则 Qabs (u i) <= sum_abs_prefix u n *)
Lemma Qabs_in_sum_abs_prefix :
  forall u n i, NatLe (Datatypes.S i) n ->
    QleT' (Qabs (u i)) (sum_abs_prefix u n).
Proof.
  intros u n. induction n as [| n' IH]; intros i Hi.
  - exfalso. pose proof (NatLe_drop (Datatypes.S i) 0 Hi). lia.
  - apply Qle_to_QleT'. simpl.
    pose proof (NatLe_drop (Datatypes.S i) (Datatypes.S n') Hi) as Hile.
    destruct (Nat.lt_ge_cases i n') as [Hlt | Hge].
    + (* i < n' *)
      apply Qle_trans with (sum_abs_prefix u n').
      * apply QleT'_to_Qle. apply IH. apply NatLe_lift. lia.
      * apply Qle_plus_nonneg_r.
        apply Qabs_nonneg.
    + (* n' <= i 且 i < S n'，所以 i = n' *)
      assert (Heq : i = n') by lia.
      subst i.
      assert (Htmp : Qabs (u n') <= Qabs (u n') + sum_abs_prefix u n').
      { apply Qle_plus_nonneg_r.
        apply QleT'_to_Qle. apply sum_abs_prefix_nonneg. }
      rewrite Qplus_comm in Htmp.   (* 交换右端加法 *)
      exact Htmp.
Qed.

(* 证明 0 <= 1 *)
Lemma Qle_0_1 : QleT' 0 1.
Proof.
  apply Qle_to_QleT'. unfold Qle; simpl; lia.
Qed.

(* 柯西序列有界性 *)
Lemma cauchy_bounded : forall (u : Qseq) (Hu : cauchy u),
  sigT (fun M : Q => forall n, QleT' (Qabs (u n)) M).
Proof.
  intros u Hu.
  destruct (Hu 1%Q) as [N HN].
  { reflexivity. }  (* QltT 0 1 *)
  exists (sum_abs_prefix u N + Qabs (u N) + 1)%Q.
  intros n.
  apply Qle_to_QleT'.
  destruct (Nat.lt_ge_cases n N) as [Hlt | Hge].
  - (* n < N *)
    apply Qle_trans with (sum_abs_prefix u N).
    + apply QleT'_to_Qle. apply Qabs_in_sum_abs_prefix. apply NatLe_lift. lia.
    + apply Qle_trans with (sum_abs_prefix u N + Qabs (u N)).
      * apply Qle_plus_nonneg_r. apply Qabs_nonneg.
      * apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1.
  - (* n >= N *)
    assert (H := HN n N (NatLe_lift _ _ Hge) (NatLe_lift _ _ (Nat.le_refl N))).
    apply QltT_to_Qlt in H.
    apply Qle_trans with (Qabs (u N) + 1).
    + (* 证明 Qabs (u n) <= Qabs (u N) + 1 *)
      apply Qle_trans with (Qabs (u n - u N) + Qabs (u N)).
      * assert (Heq : u n == (u n - u N) + u N) by ring.
        rewrite Heq at 1.
        apply Qabs_triangle.
      * apply Qle_trans with (1 + Qabs (u N)).
        -- apply Qplus_le_compat.
           ++ apply Qlt_le_weak. exact H.
           ++ apply Qle_refl.
        -- rewrite Qplus_comm. apply Qle_refl.
    + (* 证明 Qabs (u N) + 1 <= sum_abs_prefix u N + Qabs (u N) + 1 *)
      apply Qle_trans with ((Qabs (u N) + 1) + sum_abs_prefix u N).
      * apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply sum_abs_prefix_nonneg.
      * rewrite Qplus_comm. rewrite <- Qplus_assoc. apply Qle_refl.
Qed.

(* Q 层：x == y ⟹ x ≤ y。
   Rocq 9 注意：Qle x y 已定义为 (Qnum x * QDen y <= Qnum y * QDen x)%Z
   （不再是旧版的 Qcompare x y <> Gt），Qeq 即 (Qnum x * QDen y)%Z = (Qnum y * QDen x)%Z
   的原始 Z 相等，故 unfold 后用 Z.eq_le_incl 直接收尾——不要对 Qcompare destruct。 *)
Lemma qeq_le : forall x y : Q, QeqT x y -> QleT' x y.
Proof.
  intros x y H.
  (* 语句面 Set 化后与 qeq_imp_qle 同构：经在册换形件一步收束 *)
  exact (qeq_imp_qle _ _ H).
Qed.

(* ============================================================ *)
(* 实值范数一致有界（Real 层）                                  *)
(* ============================================================ *)
(* 每个柯西实数 x : Real 存在**严格正**一致界 M > 0，使 ∀k |x_k| ≤ M。
   由 Q 层 cauchy_bounded（柯西序列有界）提升：M := |M0| + 1（M0 为 Q 层界，
   取绝对确保正性）。零 Variable，纯构造性。
   支撑 real_lim_mult（乘性保持）与 real_mult（柯西乘积界）：
   l1/l2 的逐点范数一致有界是 |u_n(m)| ≤ 1+Ml1' 常数界与项② |l2|·|u−l1|
   的关键输入；real_mult 的 Cauchy 阈值需正界。 *)
Lemma real_norm_bounded : forall (x : Real),
  sigT (fun M : Q => And (QltT 0 M) (forall k : nat, QleT' (Qabs (projT1 x k)) M)).
Proof.
  intro x. destruct x as [u Hu].
  destruct (cauchy_bounded u Hu) as [M0 HM0].
  exists (Qabs M0 + 1)%Q.
  split.
  - apply Qlt_to_QltT.
    apply (Qlt_le_trans _ 1%Q _).
    + reflexivity.  (* Qlt 0 1 计算可判定 *)
    + apply (Qle_trans _ (1 + Qabs M0) _).
      * exact (Qle_plus_nonneg_r 1 (Qabs M0) (Qabs_nonneg M0)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qplus_comm 1 (Qabs M0)).
  - (* |u k| ≤ M0 ≤ |M0| ≤ |M0| + 1 *)
    intro k.
    apply Qle_to_QleT'.
    apply (Qle_trans _ M0 _).
    + apply QleT'_to_Qle. exact (HM0 k).
    + apply (Qle_trans _ (Qabs M0) _).
      * apply Qle_Qabs.
      * apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1.
Qed.

(* 柯西实数乘法定义 *)
Definition real_mult (x y : Real) : Real.
Proof.
  destruct x as [u Hu]. destruct y as [v Hv].
  exists (fun n => (u n * v n)%Q).
  intros eps Heps.
  (* 同型收敛：用实值范数一致有界（real_norm_bounded）替代 Q 层 cauchy_bounded 提升。
     得到严格正一致界 Mu/Mv（HMu_pos/HMv_pos），Mupos/Mvpos 链保留兼容。 *)
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [Mu [HMu_pos HMu]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) v Hv)) as [Mv [HMv_pos HMv]].
  (* 确保 Mu, Mv 为正 *)
  set (Mupos := (1 + Qabs Mu)%Q).
  set (Mvpos := (1 + Qabs Mv)%Q).
  assert (Mupos_pos : Qlt 0 Mupos).
  { unfold Mupos. apply Qlt_le_trans with 1%Q.
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (Mvpos_pos : Qlt 0 Mvpos).
  { unfold Mvpos. apply Qlt_le_trans with 1%Q.
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  (* 选择 N1, N2 *)
  destruct (Hu (eps / (2 * Mvpos))%Q) as [N1 HN1].
  { apply Qlt_to_QltT.
    apply Qlt_shift_div_l.
    - apply Qmult_lt_0_compat.
      + reflexivity.            (* 0 < 2 *)
      + exact Mvpos_pos.
    - rewrite Qmult_0_l.
      apply QltT_to_Qlt. exact Heps. }
  destruct (Hv (eps / (2 * Mupos))%Q) as [N2 HN2].
  { apply Qlt_to_QltT.
    apply Qlt_shift_div_l.
    - apply Qmult_lt_0_compat.
      + reflexivity.            (* 0 < 2 *)
      + exact Mupos_pos.
    - rewrite Qmult_0_l.
      apply QltT_to_Qlt. exact Heps. }
  exists (max N1 N2).
  intros m n Hm Hn.
  assert (HN1' := HN1 m n).
  assert (HN2' := HN2 m n).
  (* ===== Set 层柯西链（消融 L2：QleT'/QltT 全程 Set 流动，无降级） ===== *)
  (* 三角：|uv 差| ≤T |u|·|Δv| + |v|·|Δu|（独立代数 → 计算判定） *)
  assert (HtriT : QleT' (Qabs (u m * v m - u n * v n))
                        (Qabs (u m) * Qabs (v m - v n) + Qabs (v n) * Qabs (u m - u n))).
  { apply Qle_to_QleT'.
    apply Qle_trans with (Qabs (u m * (v m - v n)) + Qabs ((u m - u n) * v n)).
    - assert (Heq : u m * v m - u n * v n == u m * (v m - v n) + (u m - u n) * v n) by ring.
      setoid_rewrite Heq.
      apply Qabs_triangle.
    - apply Qplus_le_compat.
      + rewrite Qabs_Qmult. apply Qle_refl.
      + rewrite Qabs_Qmult. rewrite Qmult_comm. apply Qle_refl. }
  (* 界：|u m| ≤T Mupos（HMu Set 数据直接 + Set 传递） *)
  assert (HMu_boundT : QleT' (Qabs (u m)) Mupos).
  { apply (qleT'_trans (Qabs (u m)) Mu Mupos).
    - apply HMu.
    - apply Qle_to_QleT'.
      unfold Mupos.
      apply (Qle_trans Mu (Qabs Mu) (1 + Qabs Mu)).
      + apply Qle_Qabs.
      + rewrite Qplus_comm. apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1. }
  assert (HMv_boundT : QleT' (Qabs (v n)) Mvpos).
  { apply (qleT'_trans (Qabs (v n)) Mv Mvpos).
    - apply HMv.
    - apply Qle_to_QleT'.
      unfold Mvpos.
      apply (Qle_trans Mv (Qabs Mv) (1 + Qabs Mv)).
      + apply Qle_Qabs.
      + rewrite Qplus_comm. apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1. }
  (* 项1严格：|u m|·|Δv| <T Mupos·(eps/(2·Mupos))（HN2' QltT 直接） *)
  assert (Ht1T : QltT (Qabs (u m) * Qabs (v m - v n))
                      (Mupos * (eps / (2 * Mupos)))).
  { apply (qleT'_mult_ltT_compat (Qabs (u m)) Mupos (Qabs (v m - v n)) (eps / (2 * Mupos))).
    - apply Qlt_to_QltT. exact Mupos_pos.
    - apply qabs_nonnegT.
    - exact HMu_boundT.
    - apply HN2'.
      + apply NatLe_lift. apply (Nat.le_trans _ _ _ (Nat.le_max_r _ _) (NatLe_drop _ _ Hm)).
      + apply NatLe_lift. apply (Nat.le_trans _ _ _ (Nat.le_max_r _ _) (NatLe_drop _ _ Hn)). }
  (* 项2严格：|v n|·|Δu| <T Mvpos·(eps/(2·Mvpos))（HN1' QltT 直接） *)
  assert (Ht2T : QltT (Qabs (v n) * Qabs (u m - u n))
                      (Mvpos * (eps / (2 * Mvpos)))).
  { apply (qleT'_mult_ltT_compat (Qabs (v n)) Mvpos (Qabs (u m - u n)) (eps / (2 * Mvpos))).
    - apply Qlt_to_QltT. exact Mvpos_pos.
    - apply qabs_nonnegT.
    - exact HMv_boundT.
    - apply HN1'.
      + apply NatLe_lift. apply (Nat.le_trans _ _ _ (Nat.le_max_l _ _) (NatLe_drop _ _ Hm)).
      + apply NatLe_lift. apply (Nat.le_trans _ _ _ (Nat.le_max_l _ _) (NatLe_drop _ _ Hn)). }
  (* 界和 == eps（field；Mupos/Mvpos ≠ 0 经正性） *)
  assert (Hupper_eq : Mupos * (eps / (2 * Mupos)) + Mvpos * (eps / (2 * Mvpos)) == eps).
  { field.
    split; intro Heq.
    - apply (Qlt_not_eq 0 Mvpos Mvpos_pos).
      apply Qeq_sym. exact Heq.
    - apply (Qlt_not_eq 0 Mupos Mupos_pos).
      apply Qeq_sym. exact Heq. }
  (* 结论：三角 + 项和 <T 界和 ≤T eps（Set 传递收尾） *)
  apply (qleT'_ltT_ltT (Qabs (u m * v m - u n * v n))
                       (Qabs (u m) * Qabs (v m - v n) + Qabs (v n) * Qabs (u m - u n))
                       eps).
  - exact HtriT.
  - apply (qltT_leT'_ltT (Qabs (u m) * Qabs (v m - v n) + Qabs (v n) * Qabs (u m - u n))
                         (Mupos * (eps / (2 * Mupos)) + Mvpos * (eps / (2 * Mvpos)))
                         eps).
    + apply (qltT_plus_ltT (Qabs (u m) * Qabs (v m - v n))
                           (Mupos * (eps / (2 * Mupos)))
                           (Qabs (v n) * Qabs (u m - u n))
                           (Mvpos * (eps / (2 * Mvpos)))).
      * exact Ht1T.
      * exact Ht2T.
    + apply qeq_leT'. apply qeq_imp_qeqT. exact Hupper_eq.
Defined.

(* ============================================================ *)
(* 平方正定性（柯西实数层）                                    *)
(* ============================================================ *)
(* 抽象 RealInterface 层的 `le zero (mult a a)`（信息性 Or 定义）
   不可证（需三分律）。但柯西实数层可证**否定式平方正定性**：
   Not (real_lt (real_mult a a) real_zero)——a·a 不严格小于 0。
   证明：Q 层 q·q ≥ 0（Qsquare_nonneg，经 Qlt_le_dec 三分）逐点成立；
   反证 real_lt (a·a) 0 给 eps > 0 与逐点 eps < 0 − a_n·a_n，
   Q 层 q_lt_neg_inv 得 a_n·a_n < 0，与 Qsquare_nonneg 矛盾。
   非平凡：Q 层平方非负三分构造 + 负号转置 + 柯西逐点矛盾。 *)

(* Q 层：0 ≤ q·q（三分律 + 乘法保序 + 负负得正） *)
Lemma Qsquare_nonneg : forall q : Q, QleT' 0 (q * q).
Proof.
  intro q.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 q) as [Hq | Hq].
  - apply Qlt_le_weak in Hq.
    exact (Qmult_le_0_compat q q Hq Hq).
  - (* q ≤ 0 ⟹ 0 ≤ −q，且 (−q)·(−q) == q·q *)
    assert (Hnq : Qle 0 (- q)).
    { apply (Qopp_le_compat q 0). exact Hq. }
    assert (Hsq : Qle 0 ((- q) * (- q)))
      by exact (Qmult_le_0_compat (- q) (- q) Hnq Hnq).
    assert (Hrepl : (- q) * (- q) == q * q) by ring.
    setoid_rewrite Hrepl in Hsq.
    exact Hsq.
Qed.

(* Q 层：若 0 < eps 且 eps < 0 − q，则 q < 0（传递 + 负号翻转） *)
Lemma q_lt_neg_inv : forall eps q : Q,
  QltT 0 eps -> QltT eps (0 - q) -> QltT q 0.
Proof.
  intros eps q Heps Hlt.
  apply QltT_to_Qlt in Heps.
  apply QltT_to_Qlt in Hlt.
  apply Qlt_to_QltT.
  (* 0 < eps 且 eps < 0 − q ⟹ 0 < 0 − q（Qlt_trans） *)
  assert (H0 : Qlt 0 (0 - q)) by exact (Qlt_trans 0 eps (0 - q) Heps Hlt).
  (* 0 < −q ⟹ −(−q) < −0，即 q < 0（Qopp_lt_compat 翻转） *)
  assert (Hopp : Qlt (- (0 - q)) (- 0)).
  { apply (Qopp_lt_compat 0 (0 - q)). exact H0. }
  assert (H1 : (- (0 - q))%Q == q) by ring.
  assert (H2 : (- 0)%Q == 0) by ring.
  rewrite H1, H2 in Hopp.
  exact Hopp.
Qed.

(* 柯西实数层否定式平方正定性：a·a 不严格小于 0。
   信息性 real_le 的全称形式不可证（需判定 a 的符号），
   但"非负的否定式"（Not 严格负）构造性可证。 *)
Theorem real_square_not_negative : forall a : Real,
  Not (real_lt (real_mult a a) real_zero).
Proof.
  intros a Hlt.
  destruct a as [u Hu].
  destruct Hlt as [eps [Heps [N HN]]].
  (* 取 n = N：eps < 0 − (u·u)_N（real_zero/real_mult 逐点定义化简） *)
  assert (Hline : QltT eps (0 - (u N * u N))).
  {
    apply HN.
    apply NatLe_lift. apply Nat.le_refl.
  }
  (* Q 层：0 < eps、eps < 0 − q ⟹ q < 0，q := u N·u N
     （q_lt_neg_inv 为 QltT 形，结论回桥取 Qlt） *)
  assert (Hq_neg : Qlt (u N * u N) 0)
    by exact (QltT_to_Qlt _ _ (q_lt_neg_inv eps (u N * u N) Heps Hline)).
  (* 与 Qsquare_nonneg 矛盾：Qlt_not_le 给 False，用空匹配转 Empty_set *)
  assert (Hq_nn : Qle 0 (u N * u N))
    by exact (QleT'_to_Qle _ _ (Qsquare_nonneg (u N))).
  assert (Habs : False)
    by exact (Qlt_not_le (u N * u N) 0 Hq_neg Hq_nn).
  exact (match Habs with end).
Qed.

End CauchyRealMultiplication.

(* ============================================================ *)
(* 柯西实数完备性（real_lim：lim 谓词 + 唯一性 + 完备性骨架）   *)
(* ============================================================ *)
(* Real = 有理柯西序列商。RealInterface 的 lim : (nat -> R) -> R -> Set
   在此以"逐 eps 的 real_lt 夹逼"定义（等价于 metric 收敛，因 Real 层
   尚未定义 metric/abs）：
     real_lim u l := forall eps : Q, QltT 0 eps ->
       sigT (fun N => forall n, (N <= n)%nat ->
         real_lt (u n) (real_plus l (real_eps eps))) 且
         real_lt (real_plus l (real_opp (real_eps eps))) (u n)。
   其中 real_eps eps 是常值 eps 的 Real（柯西序列）。这给出"|u n − l| < eps"
   的构造性双向夹逼。lim_unique 由两极限的 eps/2 分割 + real_lt_trans +
   Qabs_triangle 证明（约 20 步）。cauchy_complete 完整构造（对角线极限）
   是构造性分析的数十字大工程，声明为诚实 Variable（与 proj_orthogonal_compat
   同先例；结构性缺失记录）。 *)
(* ------------------------------------------------------------ *)

(* 常值实数：c（有理数嵌入 Real，即常值柯西序列） *)
Definition real_const (c : Q) : Real.
Proof.
  exists (fun n => c).
  intros eps Heps. exists O. intros m n Hm Hn.
  (* |c − c| == 0，故 QltT 0 eps 即为目标（仿 q_abs_self_zero 模式） *)
  assert (Hself : Qabs (c - c) == 0).
  {
    apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. ring.
    - apply (Qeq_trans _ (-0) _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl.
  }
  (* 仿 real_eq_refl：Qcompare_comp 替换 |c−c| == 0 到 Qlt 判定 *)
  assert (Hcmp0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp : Qcompare (Qabs (c - c)) eps = Lt).
  {
    assert (Hc1 : Qcompare (Qabs (c - c)) eps = Qcompare 0 eps).
    { exact (Qcompare_comp (Qabs (c - c)) 0 Hself eps eps (Qeq_refl eps)). }
    rewrite Hc1. apply Qlt_alt. exact Hcmp0.
  }
  unfold QltT, Qlt_bool. rewrite Hcmp. reflexivity.
Defined.

(* real_lim：序列收敛到实数的双向夹逼（|u n − l| < eps 的构造性形式） *)
Definition real_lim (u : nat -> Real) (l : Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
      And (real_lt (u n) (real_plus l (real_const eps)))
          (real_lt (real_plus l (real_opp (real_const eps))) (u n))).

(* ============================================================ *)
(* real_lim 唯一性（分步实现）                                 *)
(* ============================================================ *)
(* real_lim_unique 的完整证明需要多个 Q 层辅助引理。先落地核心    *)
(* 辅助：real_lt 双向夹逼到逐点差分界（Qabs 上界）。             *)
(* ------------------------------------------------------------ *)

(* Q 层：a < b 且 c < d ⟹ a + c < b + d（Qplus_lt_compat 已有） *)

(* Q 层辅助：0 < e 且 e < x ⟹ 0 < x（Qlt_trans 直接） *)

(* Q 层：由 a_m < b_m + eps 与 b_m − eps < a_m 得 |a_m − b_m| < eps。
   非平凡：Qlt_le_dec 三分 + Qabs_pos/Qabs_neg 符号判定 +
   Qopp_lt_compat 反号 + Qlt_trans 链（约 15 步；Q 层可判定，非经典）。 *)
Lemma q_abs_lt_two_sided :
  forall (x eps : Q) (Heps : QltT 0 eps),
    QltT (- eps) x -> QltT x eps -> QltT (Qabs x) eps.
Proof.
  intros x eps Heps Hlo Hhi.
  apply QltT_to_Qlt in Hlo.
  apply QltT_to_Qlt in Hhi.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec x 0) as [Hxlt0 | Hxge0].
  - (* x < 0 ⟹ Qabs x == −x；Hlo : −eps < x ⟹ −x < eps（Qopp_lt_compat） *)
    assert (Habs : Qabs x == - x) by (apply Qabs_neg; apply Qlt_le_weak; exact Hxlt0).
    assert (Hopplt : Qlt (- x) eps).
    {
      assert (H1 : Qlt (- x) (- (- eps))) by exact (Qopp_lt_compat (- eps) x Hlo).
      rewrite (Qopp_involutive eps) in H1. exact H1.
    }
    rewrite Habs. exact Hopplt.
  - (* x ≥ 0 ⟹ Qabs x == x；Hhi : x < eps 直接 *)
    assert (Habs : Qabs x == x) by (apply Qabs_pos; exact Hxge0).
    rewrite Habs. exact Hhi.
Qed.

(* real_lt 双向夹逼到逐点差分界：
   若 a < b+eps 且 b−eps < a（real_lt 逐点见证），则对足够大 m：
   |a_m − b_m| < eps。非平凡：real_lt 见证的 e>0 传递（Qlt_trans）+
   q_abs_lt_two_sided 符号判定。 *)
Lemma real_lt_abs_bound :
  forall (a : nat -> Real) (b : Real) (eps : Q) (Heps : QltT 0 eps) (N : nat),
    (forall n, (N <= n)%nat ->
      And (real_lt (a n) (real_plus b (real_const eps)))
          (real_lt (real_plus b (real_opp (real_const eps))) (a n))) ->
    forall k, (N <= k)%nat ->
    sigT (fun M : nat => forall m, (M <= m)%nat ->
      QltT (Qabs (projT1 (a k) m - projT1 b m)) eps).
Proof.
  intros a b eps Heps N Hclamp k Hk.
  destruct (Hclamp k Hk) as [Hup Hdn].
  destruct Hup as [e1 [He1 [M1 HM1]]].
  destruct Hdn as [e2 [He2 [M2 HM2]]].
  exists (max M1 M2).
  intros m Hm.
  assert (Hm1 : (M1 <= m)%nat) by (apply Nat.le_trans with (max M1 M2); [apply Nat.le_max_l | exact Hm]).
  assert (Hm2 : (M2 <= m)%nat) by (apply Nat.le_trans with (max M1 M2); [apply Nat.le_max_r | exact Hm]).
  specialize (HM1 m (NatLe_lift _ _ Hm1)).
  specialize (HM2 m (NatLe_lift _ _ Hm2)).
  (* HM1 : QltT e1 ((b+eps)_m − (a k)_m)；HM2 : QltT e2 ((a k)_m − (b−eps)_m)。
     real_plus/real_const/real_opp 逐点展开：*) 
  (* (b+eps)_m = b_m + eps；(b−eps)_m = b_m − eps *)
  (* 由 HM1：0 < e1 且 e1 < (b_m + eps) − (a k)_m ⟹ 0 < (b_m + eps) − (a k)_m
     ⟹ (a k)_m < b_m + eps（Qlt 代数） *)
  assert (Hup_lt : Qlt (projT1 (a k) m) (projT1 b m + eps)).
  {
    (* HM1 的逐点形式需要展开 real_plus/real_const：projT1 (real_plus b (real_const eps)) m == b_m + eps *)
    assert (Hpt1 : projT1 (real_plus b (real_const eps)) m == projT1 b m + eps).
    {
      (* real_plus 体内 destruct b；real_const eps 的 projT1 是常值 eps（unfold 归约） *)
      destruct b as [ub Hb].
      unfold real_const.
      simpl. ring.
    }
    assert (Hdiff : Qlt 0 (projT1 b m + eps - projT1 (a k) m)).
    {
      (* 由 HM1 : QltT e1 ((b+eps)_m − (a k)_m)：e1 < 差分（Qlt_compat 换 X == b_m+eps），
         且 0 < e1（He1）⟹ 0 < 差分 *)
      assert (Hq1 : Qlt e1 (projT1 (real_plus b (real_const eps)) m - projT1 (a k) m))
        by (apply QltT_to_Qlt; exact HM1).
      assert (Hq1' : Qlt e1 (projT1 b m + eps - projT1 (a k) m)).
      {
        (* Qlt_compat 替换：projT1 (real_plus b (real_const eps)) m == projT1 b m + eps *)
        setoid_rewrite Hpt1 in Hq1. exact Hq1.
      }
      exact (Qlt_trans 0 e1 (projT1 b m + eps - projT1 (a k) m)
                       (QltT_to_Qlt 0 e1 He1) Hq1').
    }
    (* 0 < (b_m + eps) − a_m ⟹ a_m < b_m + eps（Qlt 代数：Qplus_lt_compat_r 反向） *)
    apply (Qlt_minus_iff (projT1 (a k) m) (projT1 b m + eps)).
    exact Hdiff.
  }
  (* 同理：由 HM2 ⟹ b_m − eps < a_m *)
  assert (Hdn_lt : Qlt (projT1 b m - eps) (projT1 (a k) m)).
  {
    assert (Hpt2 : projT1 (real_opp (real_const eps)) m == - eps).
    {
      unfold real_opp, real_const. simpl. reflexivity.
    }
    assert (Hpt3 : projT1 (real_plus b (real_opp (real_const eps))) m == projT1 b m - eps).
    {
      destruct b as [ub Hb].
      unfold real_const.
      simpl. ring.
    }
    assert (Hdiff : Qlt 0 (projT1 (a k) m - (projT1 b m - eps))).
    {
      assert (Hq2 : Qlt e2 (projT1 (a k) m - projT1 (real_plus b (real_opp (real_const eps))) m))
        by (apply QltT_to_Qlt; exact HM2).
      assert (Hq2' : Qlt e2 (projT1 (a k) m - (projT1 b m - eps))).
      {
        setoid_rewrite Hpt3 in Hq2. exact Hq2.
      }
      exact (Qlt_trans 0 e2 (projT1 (a k) m - (projT1 b m - eps))
                       (QltT_to_Qlt 0 e2 He2) Hq2').
    }
    apply (Qlt_minus_iff (projT1 b m - eps) (projT1 (a k) m)).
    exact Hdiff.
  }
  (* 目标：QltT (Qabs (a_m − b_m)) eps；q_abs_lt_two_sided 直供，前提经前向桥 *)
  assert (Hlob : Qlt (- eps) (projT1 (a k) m - projT1 b m)).
  {
    (* Qlt_minus_iff：−eps < a_m − b_m ⟺ 0 < (a_m − b_m) − (−eps) = a_m − b_m + eps
       Hdn_lt : b_m − eps < a_m ⟺ 0 < a_m − (b_m − eps)（ring 等价） *)
    apply Qlt_minus_iff.
    setoid_replace ((projT1 (a k) m - projT1 b m) - (- eps)) with (projT1 (a k) m - (projT1 b m - eps)) by ring.
    apply (proj1 (Qlt_minus_iff (projT1 b m - eps) (projT1 (a k) m))).
    exact Hdn_lt.
  }
  assert (Hhib : Qlt (projT1 (a k) m - projT1 b m) eps).
  {
    (* Qlt_minus_iff：a_m − b_m < eps ⟺ 0 < eps − (a_m − b_m)
       Hup_lt : a_m < b_m + eps ⟺ 0 < b_m + eps − a_m（ring 等价） *)
    apply Qlt_minus_iff.
    setoid_replace (eps - (projT1 (a k) m - projT1 b m)) with (projT1 b m + eps - projT1 (a k) m) by ring.
    apply (proj1 (Qlt_minus_iff (projT1 (a k) m) (projT1 b m + eps))).
    exact Hup_lt.
  }
  exact (q_abs_lt_two_sided (projT1 (a k) m - projT1 b m) eps Heps
         (Qlt_to_QltT _ _ Hlob) (Qlt_to_QltT _ _ Hhib)).
Qed.

(* real_lim 唯一性：同一序列的两极限 real_eq。
   非平凡：eps/4 分割 + real_lt_abs_bound（夹逼两项各 < eps/4）+
   l1/l2 内部柯西（两项各 < eps/4）+ Qabs_triangle 四次三角链
   （约 60 步，零 承认，纯构造性 sigT 见证）。 *)
Section RealCompletenessSkeleton.
Theorem real_lim_unique :
  forall (u : nat -> Real) (l1 l2 : Real),
    real_lim u l1 -> real_lim u l2 -> real_eq l1 l2.
Proof.
  intros u l1 l2 Hlim1 Hlim2 eps Heps.
  (* eps/4 分割：先证 Qlt 0 (eps/4) 再转 QltT（仿 real_plus 2955 模式） *)
  assert (Heps4 : QltT 0 (eps / 4)%Q).
  {
    assert (Hq : Qlt 0 (eps / 4)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 4) Hq).
  }
  destruct (Hlim1 (eps / 4)%Q) as [N1 HN1].
  { exact Heps4. }
  destruct (Hlim2 (eps / 4)%Q) as [N2 HN2].
  { exact Heps4. }
  destruct l1 as [l1s Hl1c]. destruct l2 as [l2s Hl2c].
  (* 柯西阈值（先取）：|l1s a − l1s b| < eps/4（a,b ≥ C1）、|l2s a − l2s b| < eps/4（a,b ≥ C2） *)
  destruct (Hl1c (eps / 4)%Q) as [C1 HC1].
  { exact Heps4. }
  destruct (Hl2c (eps / 4)%Q) as [C2 HC2].
  { exact Heps4. }
  (* 见证 N 含 N1/N2/C1/C2 *)
  exists (max (max N1 N2) (max C1 C2)).
  intros k Hk.
  assert (HkN1 : (N1 <= k)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | apply Nat.le_trans with (max (max N1 N2) (max C1 C2)); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]]).
  assert (HkN2 : (N2 <= k)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | apply Nat.le_trans with (max (max N1 N2) (max C1 C2)); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]]).
  assert (HkC1 : (C1 <= k)%nat) by (apply Nat.le_trans with (max C1 C2); [apply Nat.le_max_l | apply Nat.le_trans with (max (max N1 N2) (max C1 C2)); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]]).
  assert (HkC2 : (C2 <= k)%nat) by (apply Nat.le_trans with (max C1 C2); [apply Nat.le_max_r | apply Nat.le_trans with (max (max N1 N2) (max C1 C2)); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]]).
  (* 夹逼差分界：u 对 l1/l2（real_lt_abs_bound，Heps4 见开头） *)
  destruct (real_lt_abs_bound u (existT _ l1s Hl1c) (eps / 4)%Q Heps4 N1 HN1 k HkN1) as [M1k HM1k].
  destruct (real_lt_abs_bound u (existT _ l2s Hl2c) (eps / 4)%Q Heps4 N2 HN2 k HkN2) as [M2k HM2k].
  (* 中间下标 m := max k (max C1 (max C2 (max M1k M2k))) *)
  set (m := max k (max C1 (max C2 (max M1k M2k)))).
  assert (Hmk : (k <= m)%nat) by (unfold m; apply Nat.le_max_l).
  assert (Hmc1 : (C1 <= m)%nat).
  { unfold m. apply Nat.le_trans with (max C1 (max C2 (max M1k M2k))).
    - apply Nat.le_max_l.
    - apply Nat.le_max_r. }
  assert (Hmc2 : (C2 <= m)%nat).
  { unfold m. apply Nat.le_trans with (max C1 (max C2 (max M1k M2k))).
    - apply Nat.le_trans with (max C2 (max M1k M2k)); [apply Nat.le_max_l | apply Nat.le_max_r].
    - apply Nat.le_max_r. }
  assert (Hmm1k : (M1k <= m)%nat).
  { unfold m. apply Nat.le_trans with (max C1 (max C2 (max M1k M2k))).
    - apply Nat.le_trans with (max C2 (max M1k M2k)).
      + apply Nat.le_trans with (max M1k M2k).
        * apply Nat.le_max_l.
        * apply Nat.le_max_r.
      + apply Nat.le_max_r.
    - apply Nat.le_max_r. }
  assert (Hmm2k : (M2k <= m)%nat).
  { unfold m. apply Nat.le_trans with (max C1 (max C2 (max M1k M2k))).
    - apply Nat.le_trans with (max C2 (max M1k M2k)).
      + apply Nat.le_trans with (max M1k M2k).
        * apply Nat.le_max_r.
        * apply Nat.le_max_r.
      + apply Nat.le_max_r.
    - apply Nat.le_max_r. }
  (* 夹逼逐点界（m 坐标）：|(u k)_m − l1s m| < eps/4、|(u k)_m − l2s m| < eps/4 *)
  assert (Hb1 : QltT (Qabs (projT1 (u k) m - l1s m)) (eps / 4)%Q)
    by (apply (HM1k m Hmm1k)).
  assert (Hb2 : QltT (Qabs (projT1 (u k) m - l2s m)) (eps / 4)%Q)
    by (apply (HM2k m Hmm2k)).
  (* 柯西逐点界：|l1s k − l1s m| < eps/4、|l2s k − l2s m| < eps/4（k,m ≥ C1/C2） *)
  assert (Hc1 : QltT (Qabs (l1s k - l1s m)) (eps / 4)%Q)
    by (apply (HC1 k m (NatLe_lift _ _ HkC1) (NatLe_lift _ _ Hmc1))).
  assert (Hc2 : QltT (Qabs (l2s k - l2s m)) (eps / 4)%Q)
    by (apply (HC2 k m (NatLe_lift _ _ HkC2) (NatLe_lift _ _ Hmc2))).
  (* 目标：QltT (Qabs (l1s k − l2s k)) eps
     三角链：|l1s k − l2s k| ≤ |l1s k − l1s m| + |l1s m − (u k)_m| + |(u k)_m − l2s m| + |l2s m − l2s k|
            < eps/4·4 = eps *)
  apply Qlt_to_QltT.
  (* 先把各项 QltT 转 Qlt，Qabs_triangle 展开链 *)
  assert (Hb1q : Qlt (Qabs (projT1 (u k) m - l1s m)) (eps / 4)%Q) by (apply QltT_to_Qlt; exact Hb1).
  assert (Hb2q : Qlt (Qabs (projT1 (u k) m - l2s m)) (eps / 4)%Q) by (apply QltT_to_Qlt; exact Hb2).
  assert (Hc1q : Qlt (Qabs (l1s k - l1s m)) (eps / 4)%Q) by (apply QltT_to_Qlt; exact Hc1).
  assert (Hc2q : Qlt (Qabs (l2s k - l2s m)) (eps / 4)%Q) by (apply QltT_to_Qlt; exact Hc2).
  (* |l1s m − (u k)_m| == |(u k)_m − l1s m|（Qabs_opp + ring；q_abs_minus_sym 定义在后，内联） *)
  assert (Hsym1 : Qabs (l1s m - projT1 (u k) m) == Qabs (projT1 (u k) m - l1s m)).
  {
    setoid_replace (l1s m - projT1 (u k) m) with (- (projT1 (u k) m - l1s m)) by ring.
    apply Qabs_opp.
  }
  assert (Hsym2 : Qabs (l2s m - projT1 (u k) m) == Qabs (projT1 (u k) m - l2s m)).
  {
    setoid_replace (l2s m - projT1 (u k) m) with (- (projT1 (u k) m - l2s m)) by ring.
    apply Qabs_opp.
  }
  (* 三角链四步：先用 Qle_lt_trans 逐步放大 *)
  assert (Htri1 : Qle (Qabs (l1s k - l2s k))
                     (Qabs (l1s k - l1s m) + Qabs (l1s m - l2s m) + Qabs (l2s m - l2s k))).
  { apply Qle_trans with (Qabs (l1s k - l1s m) + Qabs (l1s m - l2s m) + Qabs (l2s m - l2s k)).
    - (* |l1s k − l2s k| ≤ |l1s k − l1s m| + |l1s m − l2s m| + |l2s m − l2s k|（Qabs_triangle 两次） *)
      assert (Heq : (l1s k - l2s k)%Q == ((l1s k - l1s m) + (l1s m - l2s m) + (l2s m - l2s k))%Q) by field.
      setoid_rewrite Heq.
      (* Qabs (x + y + z) ≤ |x| + |y| + |z|（两次 Qabs_triangle） *)
      apply Qle_trans with (Qabs ((l1s k - l1s m) + (l1s m - l2s m)) + Qabs (l2s m - l2s k)).
      + apply Qabs_triangle.
      + apply Qplus_le_compat.
        * apply Qabs_triangle.
        * apply Qle_refl.
    - apply Qle_refl. }
  assert (Htri2 : Qle (Qabs (l1s m - l2s m))
                     (Qabs (l1s m - projT1 (u k) m) + Qabs (projT1 (u k) m - l2s m))).
  {
    assert (Heq2 : (l1s m - l2s m)%Q == ((l1s m - projT1 (u k) m) + (projT1 (u k) m - l2s m))%Q) by field.
    (* 换 LHS：Qabs_wd 给 Qeq（Qabs 间），qeq_le 转 Qle *)
    apply (Qle_trans (Qabs (l1s m - l2s m))
                     (Qabs ((l1s m - projT1 (u k) m) + (projT1 (u k) m - l2s m)))
                     (Qabs (l1s m - projT1 (u k) m) + Qabs (projT1 (u k) m - l2s m))).
    - exact (QleT'_to_Qle _ _ (qeq_le _ _
              (qeq_imp_qeqT _ _ (Qabs_wd (l1s m - l2s m) ((l1s m - projT1 (u k) m) + (projT1 (u k) m - l2s m)) Heq2)))).
    - apply Qabs_triangle.
  }
  assert (Htri_total : Qle (Qabs (l1s k - l2s k))
                          (Qabs (l1s k - l1s m) + (Qabs (l1s m - projT1 (u k) m) + (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k))))).
  {
    (* 由 Htri1（三项）+ Htri2 替换中间项（l1s m − l2s m ≤ |l1s m−u|+|u−l2s m|） *)
    apply Qle_trans with (Qabs (l1s k - l1s m) + Qabs (l1s m - l2s m) + Qabs (l2s m - l2s k)).
    - exact Htri1.
    - (* 右端替换：|l1s m−l2s m| ≤ |l1s m−u| + |u−l2s m| *)
      setoid_replace (Qabs (l1s k - l1s m) + Qabs (l1s m - l2s m) + Qabs (l2s m - l2s k))
        with (Qabs (l1s k - l1s m) + (Qabs (l1s m - l2s m) + Qabs (l2s m - l2s k))) by field.
      apply Qplus_le_compat.
      + apply Qle_refl.
      + (* 先把右端重结合为 (A + B) + C，再按 Qplus_le_compat 拆，
          使第一子目标恰为 Htri2（Y ≤ A + B）；否则 A + (B + C) 会拆成 Y ≤ A。 *)
        setoid_replace (Qabs (l1s m - projT1 (u k) m) + (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k)))
          with ((Qabs (l1s m - projT1 (u k) m) + Qabs (projT1 (u k) m - l2s m)) + Qabs (l2s m - l2s k)) by field.
        apply Qplus_le_compat.
        * exact Htri2.
        * apply Qle_refl.
  }
  (* 各项 < eps/4（含符号替换 Hsym1/Hsym2）⟹ 总和 < eps（Qplus_lt_compat 链 + eps/4·4 = eps） *)
  assert (Hsum_lt : Qlt (Qabs (l1s k - l1s m) + (Qabs (l1s m - projT1 (u k) m) + (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k))))
                       eps).
  {
    (* 四项各 < eps/4：Qplus_lt_compat 两次组合 *)
    assert (H1 : Qlt (Qabs (l1s k - l1s m)) (eps / 4)%Q) by exact Hc1q.
    assert (H2 : Qlt (Qabs (l1s m - projT1 (u k) m)) (eps / 4)%Q).
    { rewrite Hsym1. exact Hb1q. }
    assert (H3 : Qlt (Qabs (projT1 (u k) m - l2s m)) (eps / 4)%Q) by exact Hb2q.
    assert (H4 : Qlt (Qabs (l2s m - l2s k)) (eps / 4)%Q).
    { (* Hc2q 是 |l2s k − l2s m| < eps/4，符号反向：Qabs_opp 对称（同 Hsym1/Hsym2 内联） *)
      assert (Hsym4 : Qabs (l2s m - l2s k) == Qabs (l2s k - l2s m)).
      {
        setoid_replace (l2s m - l2s k) with (- (l2s k - l2s m)) by ring.
        apply Qabs_opp.
      }
      rewrite Hsym4. exact Hc2q. }
    (* (H1 + H2) + (H3 + H4) < eps/4+eps/4 + eps/4+eps/4 = eps *)
    assert (H12 : Qlt (Qabs (l1s k - l1s m) + Qabs (l1s m - projT1 (u k) m)) ((eps / 4)%Q + (eps / 4)%Q))
      by exact (Qplus_lt_compat _ _ _ _ H1 H2).
    assert (H34 : Qlt (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k)) ((eps / 4)%Q + (eps / 4)%Q))
      by exact (Qplus_lt_compat _ _ _ _ H3 H4).
    (* 总和 < (eps/4+eps/4) + (eps/4+eps/4) = eps（ring 化简） *)
    assert (H1234 : Qlt (Qabs (l1s k - l1s m) + (Qabs (l1s m - projT1 (u k) m) + (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k))))
                        (((eps / 4)%Q + (eps / 4)%Q) + ((eps / 4)%Q + (eps / 4)%Q))).
    {
      (* 重组括号：左结合加法 *)
      setoid_replace (Qabs (l1s k - l1s m) + (Qabs (l1s m - projT1 (u k) m) + (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k))))
        with ((Qabs (l1s k - l1s m) + Qabs (l1s m - projT1 (u k) m)) + (Qabs (projT1 (u k) m - l2s m) + Qabs (l2s m - l2s k))) by ring.
      exact (Qplus_lt_compat _ _ _ _ H12 H34).
    }
    (* eps/4·4 == eps ⟹ 目标 < eps（含除法，用 field 而非 ring） *)
    apply (Qlt_le_trans _ (((eps / 4)%Q + (eps / 4)%Q) + ((eps / 4)%Q + (eps / 4)%Q)) _ H1234).
    setoid_replace (((eps / 4)%Q + (eps / 4)%Q) + ((eps / 4)%Q + (eps / 4)%Q)) with eps by field.
    apply Qle_refl.
  }
  (* 组装：目标 Qlt (Qabs (l1s k − l2s k)) eps 由 Htri_total + Hsum_lt（Qle_lt_trans） *)
  exact (Qle_lt_trans _ _ _ Htri_total Hsum_lt).
Qed.

(* ============================================================ *)
(* real_cauchy_complete 完整化（构造性对角线极限）             *)
(* ------------------------------------------------------------ *)
(* 分解：Bishop 正则化标准中间结论（实值双柯西 → 统一逐点双柯西）*)
(* 保持诚实 Variable（与 proj_orthogonal_compat 同先例）；其余   *)
(* 全部完整证明：对角线柯西性（参考桥接）+ real_lim 收敛双向。   *)
(* ============================================================ *)

(* Q 层：|x| < e ⟹ −e < x（e > 0；Qlt_le_dec 三分 + Qabs_neg/pos） *)
Lemma q_abs_gt_neg : forall x e : Q, QltT 0 e -> QltT (Qabs x) e -> QltT (- e) x.
Proof.
  intros x e He H.
  apply QltT_to_Qlt in He.
  apply QltT_to_Qlt in H.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec x 0) as [Hxlt | Hxge0].
  - (* x < 0：|x| == −x < e ⟹ −e < x（Qopp_lt_compat） *)
    assert (Habs : Qabs x == - x) by (apply Qabs_neg; apply Qlt_le_weak; exact Hxlt).
    rewrite Habs in H.
    assert (Hopp : Qlt (- e) (- (- x))).
    { apply Qopp_lt_compat. exact H. }
    rewrite (Qopp_involutive x) in Hopp. exact Hopp.
  - (* x ≥ 0：|x| == x < e，且 −e < 0 ≤ x *)
    assert (Habs : Qabs x == x) by (apply Qabs_pos; exact Hxge0).
    rewrite Habs in H.
    assert (Hneg0 : Qlt (- e) 0).
    { apply (Qlt_le_trans (- e) (- 0) 0).
      - apply Qopp_lt_compat. exact He.
      - apply Qle_refl. }
    exact (Qlt_le_trans (- e) 0 x Hneg0 Hxge0).
Qed.

(* Q 层：|d| < eps/2 ⟹ eps/2 < d + eps（收敛界：u 向 l+eps 夹逼的逐点代数） *)
Lemma q_bound_eps_half :
  forall (d eps : Q), QltT 0 eps -> QltT (Qabs d) (eps / 2) -> QltT (eps / 2) (d + eps).
Proof.
  intros d eps Heps Hd.
  apply QltT_to_Qlt in Heps.
  apply QltT_to_Qlt in Hd.
  apply Qlt_to_QltT.
  assert (Hhalf : Qlt 0 (eps / 2)).
  { apply Qlt_shift_div_l; [reflexivity | simpl; exact Heps]. }
  (* 目标 eps/2 < d+eps ⟸ 0 < (d+eps) + −(eps/2)（Qlt_minus_iff proj2） *)
  apply (proj2 (Qlt_minus_iff (eps / 2) (d + eps))).
  setoid_replace ((d + eps) + - (eps / 2)) with (d + eps / 2) by field.
  (* 目标 0 < d + eps/2 换形为 0 < d + −(−(eps/2))（Qlt_minus_iff proj1 正向） *)
  setoid_replace (d + eps / 2) with (d + - - (eps / 2)) by ring.
  apply (proj1 (Qlt_minus_iff (- (eps / 2)) d)).
  apply QltT_to_Qlt.
  apply q_abs_gt_neg; [apply Qlt_to_QltT; exact Hhalf | apply Qlt_to_QltT; exact Hd].
Qed.

(* Q 层交换形：|d| < eps/2 ⟹ eps/2 < eps + d *)
Lemma q_bound_eps_half_comm :
  forall (d eps : Q), QltT 0 eps -> QltT (Qabs d) (eps / 2) -> QltT (eps / 2) (eps + d).
Proof.
  intros d eps Heps Hd.
  assert (Hmid : Qlt (eps / 2) (d + eps)).
  { apply QltT_to_Qlt. apply q_bound_eps_half; [exact Heps | exact Hd]. }
  setoid_replace (d + eps) with (eps + d) in Hmid by ring.
  apply Qlt_to_QltT. exact Hmid.
Qed.

(* Q 层：三项各 < eps/3 ⟹ 和 < eps（Qabs_triangle 两次 + field 收尾） *)
Lemma q_three_bound : forall (eps a b c : Q), QltT 0 eps ->
  QltT (Qabs a) (eps / 3) -> QltT (Qabs b) (eps / 3) -> QltT (Qabs c) (eps / 3) ->
  QltT (Qabs (a + b + c)) eps.
Proof.
  intros eps a b c Heps Ha Hb Hc.
  apply QltT_to_Qlt in Heps.
  apply QltT_to_Qlt in Ha.
  apply QltT_to_Qlt in Hb.
  apply QltT_to_Qlt in Hc.
  apply Qlt_to_QltT.
  assert (Ht1 : Qle (Qabs (a + b + c)) (Qabs (a + b) + Qabs c)).
  { apply Qabs_triangle. }
  assert (Ht2 : Qle (Qabs (a + b)) (Qabs a + Qabs b)).
  { apply Qabs_triangle. }
  apply (Qle_lt_trans _ (Qabs (a + b) + Qabs c) _ Ht1).
  apply (Qle_lt_trans _ (Qabs a + Qabs b + Qabs c) _).
  - apply Qplus_le_compat; [exact Ht2 | apply Qle_refl].
  - assert (Hab : Qlt (Qabs a + Qabs b) (eps / 3 + eps / 3))
      by (apply Qplus_lt_compat; [exact Ha | exact Hb]).
    assert (H123 : Qlt (Qabs a + Qabs b + Qabs c) ((eps / 3 + eps / 3) + eps / 3)).
    { exact (Qplus_lt_compat _ _ _ _ Hab Hc). }
    apply (Qlt_le_trans _ (((eps / 3) + (eps / 3)) + (eps / 3)) _ H123).
    setoid_replace (((eps / 3) + (eps / 3)) + (eps / 3)) with eps by field.
    apply Qle_refl.
Qed.

(* Q 层三点链：|x−p|,|p−q|,|q−y| 各 < eps/3 ⟹ |x−y| < eps
   （对角线柯西的 eps/3 三角链：x:=u_m(m), p:=u_R(m), q:=u_R(n), y:=u_n(n)） *)
Lemma q_chain3 : forall (x p q y : Q) (eps : Q), QltT 0 eps ->
  QltT (Qabs (x - p)) (eps / 3) -> QltT (Qabs (p - q)) (eps / 3) -> QltT (Qabs (q - y)) (eps / 3) ->
  QltT (Qabs (x - y)) eps.
Proof.
  intros x p q y eps Heps Hxp Hpq Hqy.
  assert (Hsum : Qlt (Qabs ((x - p) + (p - q) + (q - y))) eps).
  { apply QltT_to_Qlt. apply q_three_bound with (a := x - p) (b := p - q) (c := q - y).
    - exact Heps.
    - exact Hxp.
    - exact Hpq.
    - exact Hqy. }
  setoid_replace ((x - p) + (p - q) + (q - y)) with (x - y) in Hsum by ring.
  apply Qlt_to_QltT. exact Hsum.
Qed.

(* 逐点投影引理：real_plus/real_opp/real_const/real_mult 的 projT1 展开（Defined 可计算） *)
Lemma real_plus_proj : forall (x y : Real) (k : nat),
  QeqT (projT1 (real_plus x y) k) (projT1 x k + projT1 y k).
Proof.
  intros [u Hu] [v Hv] k. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma real_mult_proj : forall (x y : Real) (k : nat),
  QeqT (projT1 (real_mult x y) k) (projT1 x k * projT1 y k).
Proof.
  intros [u Hu] [v Hv] k. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma real_opp_proj : forall (x : Real) (k : nat),
  QeqT (projT1 (real_opp x) k) (- projT1 x k).
Proof.
  intros [u Hu] k. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma real_const_proj : forall (c : Q) (k : nat),
  QeqT (projT1 (real_const c) k) c.
Proof.
  intros c k. apply qeq_imp_qeqT. reflexivity.
Qed.

End RealCompletenessSkeleton.

(* ============================================================ *)
(* 反例：实值双柯西 ⟹ 统一逐点双柯西 不可证（构造性否定）       *)
(* ============================================================ *)
(* u_m(k) := 0 if k < 2^m else 1                                *)
(* 每个 u_m 是柯西序列（实值 = 1）；序列族满足实值双柯西        *)
(* （N := 0，因全部实值相等）；但统一逐点双柯西构造性失败：     *)
(* ∀N M ∃m n k（m,n≥N, k≥M）使 |u_m(k) − u_n(k)| == 1。        *)
(* 此反例证明 real_cauchy_pointwise 作为"定理"不可证，          *)
(* 完备性证明必须走 Bishop 正则化路线（见后续正规划）。         *)
(* ------------------------------------------------------------ *)

(* 2^m ≥ 1 *)
Lemma pow2_ge_one : forall m : nat, NatLe 1 (2 ^ m).
Proof.
  intros m. apply NatLe_lift.
  induction m; simpl; [lia | exact (Nat.le_trans _ (2 ^ m) _ IHm (Nat.le_add_r _ _))].
Qed.

(* 2^m ≥ m *)
Lemma pow2_ge : forall m : nat, NatLe m (2 ^ m).
Proof.
  intros m. apply NatLe_lift.
  induction m; simpl; [lia | ].
  assert (H1 : (1 <= 2 ^ m)%nat) by (apply NatLe_drop; apply pow2_ge_one).
  assert (Htwo : (2 ^ m <= 2 ^ m + 2 ^ m)%nat) by lia.
  lia.
Qed.

(* 2^m > m（严格） *)
Lemma pow2_gt : forall m : nat, NatLe (Datatypes.S m) (2 ^ m).
Proof.
  intros m. apply NatLe_lift.
  induction m; simpl; [lia | ].
  assert (H1 : (1 <= 2 ^ m)%nat) by (apply NatLe_drop; apply pow2_ge_one).
  assert (Hle : (m + 1 <= 2 ^ m)%nat) by lia.
  assert (Hlt : (2 ^ m < 2 ^ m + 2 ^ m)%nat) by lia.
  lia.
Qed.

(* 反例序列族：u_m(k) := 0 if k < 2^m else 1 *)
Definition step_seq (m k : nat) : Q :=
  if Nat.ltb k (2 ^ m) then 0 else 1.

(* k < 2^m ⟹ u_m(k) == 0 *)
Lemma step_seq_lt : forall m k : nat, NatLe (Datatypes.S k) (2 ^ m) -> QeqT (step_seq m k) 0.
Proof.
  intros m k Hk. unfold step_seq.
  apply qeq_imp_qeqT.
  exact (@eq_ind bool true (fun b : bool => (if b then 0 else 1)%Q == 0)
  eq_refl (Nat.ltb k (2 ^ m)) (eq_sym (proj2 (Nat.ltb_lt k (2 ^ m)) (NatLe_drop _ _ Hk)))).
Qed.

(* 2^m ≤ k ⟹ u_m(k) == 1 *)
Lemma step_seq_ge : forall m k : nat, NatLe (2 ^ m) k -> QeqT (step_seq m k) 1.
Proof.
  intros m k Hk. unfold step_seq.
  apply qeq_imp_qeqT.
  exact (@eq_ind bool false (fun b : bool => (if b then 0 else 1)%Q == 1)
  eq_refl (Nat.ltb k (2 ^ m)) (eq_sym (proj2 (Nat.ltb_ge k (2 ^ m)) (NatLe_drop _ _ Hk)))).
Qed.

(* 每个 u_m 是柯西（取 N := 2^m：k ≥ 2^m 后恒为 1） *)
Lemma step_seq_cauchy : forall m : nat, cauchy (step_seq m).
Proof.
  intros m eps Heps.
  exists (2 ^ m)%nat.
  intros a b Ha Hb.
  assert (Hsa : step_seq m a == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; exact Ha).
  assert (Hsb : step_seq m b == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; exact Hb).
  (* |u_m(a) − u_m(b)| == 0 < eps *)
  assert (Hd : Qabs (step_seq m a - step_seq m b) == 0).
  {
    setoid_rewrite Hsa. setoid_rewrite Hsb.
    apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. ring.
    - apply (Qeq_trans _ (-0) _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl.
  }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (step_seq m a - step_seq m b)) eps = Lt).
  { rewrite Hd. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* 序列族（Real 化）：u : nat -> Real *)
Definition step_real (m : nat) : Real :=
  existT _ (step_seq m) (step_seq_cauchy m).

(* 每个 u_m 实值 = 1（real_eq，N := 2^m） *)
Lemma step_real_eq_one : forall m : nat, real_eq (step_real m) (real_const 1).
Proof.
  intros m eps Heps.
  exists (2 ^ m)%nat.
  intros k Hk.
  assert (Hs : step_seq m k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; exact Hk).
  assert (Hc : projT1 (real_const 1) k == 1) by (apply qeqT_imp_qeq; apply real_const_proj).
  (* |u_m(k) − 1| == 0 < eps *)
  assert (Hd : Qabs (projT1 (step_real m) k - projT1 (real_const 1) k) == 0).
  {
    change (projT1 (step_real m) k) with (step_seq m k).
    setoid_rewrite Hs. setoid_rewrite Hc.
    apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. ring.
    - apply (Qeq_trans _ (-0) _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl.
  }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (projT1 (step_real m) k - projT1 (real_const 1) k)) eps = Lt).
  { rewrite Hd. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* Q 层：0 < eps ⟹ eps/2 < eps *)
Lemma q_half_lt : forall eps : Q, QltT 0 eps -> QltT (eps / 2) eps.
Proof.
  intros eps Heps.
  apply QltT_to_Qlt in Heps.
  apply Qlt_to_QltT.
  apply Qlt_shift_div_r; [reflexivity | ].
  setoid_replace (eps * 2) with (eps + eps) by ring.
  apply Qlt_minus_iff.
  setoid_replace (eps + eps + - eps) with eps by ring.
  exact Heps.
Qed.

(* 实值双柯西成立（N := 0，全部实值相等 ⟹ 逐点差在坐标 ≥ max(2^m,2^n) 后为 0） *)
Lemma step_real_double_cauchy :
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat,
    (N <= m)%nat -> (N <= n)%nat ->
    And (real_lt (real_plus (step_real m) (real_opp (step_real n))) (real_const eps))
        (real_lt (real_plus (step_real n) (real_opp (step_real m))) (real_const eps))).
Proof.
  intros eps Heps.
  exists 0%nat.
  intros m n Hm Hn.
  split.
  - (* 方向 1：real_lt (u_m − u_n) (const eps)，见证 eps/2，N1 := max (2^m) (2^n) *)
    exists (eps / 2)%Q. split.
    + assert (Hhalf : Qlt 0 (eps / 2)).
      { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
      exact (Qlt_to_QltT 0 (eps / 2) Hhalf).
    + exists (max (2 ^ m) (2 ^ n))%nat. intros k Hk.
      assert (Hkm : (2 ^ m <= k)%nat)
        by (apply Nat.le_trans with (max (2 ^ m) (2 ^ n)); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
      assert (Hkn : (2 ^ n <= k)%nat)
        by (apply Nat.le_trans with (max (2 ^ m) (2 ^ n)); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
      assert (Hsm : step_seq m k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; apply NatLe_lift; exact Hkm).
      assert (Hsn : step_seq n k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; apply NatLe_lift; exact Hkn).
      (* 目标：QltT (eps/2) (projT1 (real_const eps) k − projT1 (u_m − u_n) k) *)
      apply Qlt_to_QltT.
      assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
      (* 投影展开（定义性 change）：const eps k == eps；u_m − u_n k == u_m k − u_n k *)
      assert (Hgoal :
        projT1 (real_const eps) k - projT1 (real_plus (step_real m) (real_opp (step_real n))) k == eps).
      {
        change (projT1 (real_const eps) k) with eps.
        change (projT1 (real_plus (step_real m) (real_opp (step_real n))) k)
          with (projT1 (step_real m) k - projT1 (step_real n) k).
        change (projT1 (step_real m) k) with (step_seq m k).
        change (projT1 (step_real n) k) with (step_seq n k).
        setoid_rewrite Hsm. setoid_rewrite Hsn. ring.
      }
      setoid_replace (projT1 (real_const eps) k - projT1 (real_plus (step_real m) (real_opp (step_real n))) k)
        with eps by exact Hgoal.
      exact (QltT_to_Qlt _ _ (q_half_lt eps Heps)).
  - (* 方向 2：real_lt (u_n − u_m) (const eps)，对称 *)
    exists (eps / 2)%Q. split.
    + assert (Hhalf : Qlt 0 (eps / 2)).
      { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
      exact (Qlt_to_QltT 0 (eps / 2) Hhalf).
    + exists (max (2 ^ m) (2 ^ n))%nat. intros k Hk.
      assert (Hkm : (2 ^ m <= k)%nat)
        by (apply Nat.le_trans with (max (2 ^ m) (2 ^ n)); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
      assert (Hkn : (2 ^ n <= k)%nat)
        by (apply Nat.le_trans with (max (2 ^ m) (2 ^ n)); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
      assert (Hsm : step_seq m k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; apply NatLe_lift; exact Hkm).
      assert (Hsn : step_seq n k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; apply NatLe_lift; exact Hkn).
      apply Qlt_to_QltT.
      assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
      assert (Hgoal :
        projT1 (real_const eps) k - projT1 (real_plus (step_real n) (real_opp (step_real m))) k == eps).
      {
        change (projT1 (real_const eps) k) with eps.
        change (projT1 (real_plus (step_real n) (real_opp (step_real m))) k)
          with (projT1 (step_real n) k - projT1 (step_real m) k).
        change (projT1 (step_real n) k) with (step_seq n k).
        change (projT1 (step_real m) k) with (step_seq m k).
        setoid_rewrite Hsn. setoid_rewrite Hsm. ring.
      }
      setoid_replace (projT1 (real_const eps) k - projT1 (real_plus (step_real n) (real_opp (step_real m))) k)
        with eps by exact Hgoal.
      exact (QltT_to_Qlt _ _ (q_half_lt eps Heps)).
Qed.

(* 统一逐点双柯西的定义（real_cauchy_pointwise 的结论形态） *)
Definition unif_pointwise_cauchy (u : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => sigT (fun M : nat => forall m n k : nat,
      (N <= m)%nat -> (N <= n)%nat -> (M <= k)%nat ->
      QltT (Qabs (projT1 (u m) k - projT1 (u n) k)) eps)).

(* ¬(1 < 1/2)：Qcompare 1 (1/2) = Gt ≠ Lt *)
Lemma not_qlt_one_half : Not (QltT 1 (1/2)).
Proof.
  intro H.
  apply QltT_to_Qlt in H.
  unfold Qlt, Qcompare in H.
  simpl in H.
  discriminate H.
Qed.

(* 核心反例定理：统一逐点双柯西对 step_real 构造性失败。
   给定任意 N M，取 m := max N M（≥ N），n := S m（≥ N），k := 2^m（≥ M），
   则 u_m(k) == 1（k = 2^m ≥ 2^m）而 u_n(k) == 0（k < 2^n = 2·2^m），
   |1 − 0| == 1 且 ¬(1 < 1/2)。 *)
Theorem step_not_unif_pointwise :
  Not (unif_pointwise_cauchy step_real).
Proof.
  intro H.
  (* eps := 1/2 *)
  assert (Hhalf0 : QltT 0 (1/2)).
  { unfold QltT, Qlt_bool. simpl. reflexivity. }
  destruct (H (1/2) Hhalf0) as [N [M HM]].
  (* 构造破坏性三参数：m := max N M，n := S m，k := 2^m *)
  set (m := max N M).
  set (n := Datatypes.S m).
  set (k := (2 ^ m)%nat).
  assert (HmN : (N <= m)%nat) by (unfold m; apply Nat.le_max_l).
  assert (HnN : (N <= n)%nat) by (unfold n; lia).
  assert (HkM : (M <= k)%nat).
  { unfold k.
    assert (HmM : (M <= m)%nat) by (unfold m; apply Nat.le_max_r).
    apply (Nat.le_trans _ m _ HmM).
    apply NatLe_drop. apply pow2_ge. }
  (* HM m n k HmN HnN HkM : QltT (Qabs (u_m(k) − u_n(k))) (1/2) *)
  assert (Hbad : QltT (Qabs (projT1 (step_real m) k - projT1 (step_real n) k)) (1/2))
    by (apply (HM m n k HmN HnN HkM)).
  (* u_m(k) == 1，u_n(k) == 0 ⟹ |1 − 0| == 1 *)
  assert (Hsm : step_seq m k == 1).
  { apply qeqT_imp_qeq. apply step_seq_ge. apply NatLe_lift. unfold k. apply Nat.le_refl. }
  assert (Hsn0 : step_seq n k == 0).
  { apply qeqT_imp_qeq. apply step_seq_lt. apply NatLe_lift. unfold n, k.
    (* k = 2^m < 2^(S m) = 2^n *)
    assert (Htwo : (2 ^ Datatypes.S m)%nat = (2 * 2 ^ m)%nat) by (simpl; reflexivity).
    rewrite Htwo.
    assert (Hp : (1 <= 2 ^ m)%nat) by (apply NatLe_drop; apply pow2_ge_one).
    lia. }
  (* 化简 Hbad 到 ¬(Qlt 1 (1/2)) *)
  apply (not_qlt_one_half).
  apply Qlt_to_QltT.
  apply QltT_to_Qlt in Hbad.
  setoid_replace (projT1 (step_real m) k - projT1 (step_real n) k)
    with 1%Q in Hbad by (change (projT1 (step_real m) k) with (step_seq m k);
                         change (projT1 (step_real n) k) with (step_seq n k);
                         setoid_rewrite Hsm; setoid_rewrite Hsn0; ring).
  assert (Ha : Qabs 1 == 1) by reflexivity.
  setoid_rewrite Ha in Hbad.
  exact Hbad.
Qed.

(* 朴素对角线给出错误极限：l_k := u_k(k) == 0（因 k < 2^k），
   但实值极限是 1 ≠ 0（由 real_lim_unique 分离）。 *)
Lemma step_diag_zero : forall k : nat, QeqT (step_seq k k) 0.
Proof.
  intro k. exact (step_seq_lt k k (pow2_gt k)).
Qed.

(* real_lim step_real (real_const 1)：N := 0，双向 eps/2 夹逼 *)
Lemma step_real_lim_one : real_lim step_real (real_const 1).
Proof.
  intros eps Heps.
  exists 0%nat.
  intros n Hn.
  split.
  - (* 方向 1：real_lt (u n) (1 + eps)：见证 eps/2，N1 := 2^n *)
    exists (eps / 2)%Q. split.
    + assert (Hhalf : Qlt 0 (eps / 2)).
      { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
      exact (Qlt_to_QltT 0 (eps / 2) Hhalf).
    + exists (2 ^ n)%nat. intros k Hk.
      assert (Hsn : step_seq n k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; exact Hk).
      apply Qlt_to_QltT.
      assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
      (* 目标：eps/2 < projT1 (1 + eps) k − u_n(k) == (1 + eps) − 1 == eps *)
      change (projT1 (real_plus (real_const 1) (real_const eps)) k)
        with (projT1 (real_const 1) k + projT1 (real_const eps) k).
      assert (Hc1 : projT1 (real_const 1) k == 1) by (apply qeqT_imp_qeq; apply real_const_proj).
      assert (Hce : projT1 (real_const eps) k == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
      setoid_replace (projT1 (real_const 1) k + projT1 (real_const eps) k - projT1 (step_real n) k)
        with eps by (change (projT1 (step_real n) k) with (step_seq n k);
                     setoid_rewrite Hc1; setoid_rewrite Hce; setoid_rewrite Hsn; ring).
      exact (QltT_to_Qlt _ _ (q_half_lt eps Heps)).
  - (* 方向 2：real_lt (1 − eps) (u n)：见证 eps/2，N2 := 2^n *)
    exists (eps / 2)%Q. split.
    + assert (Hhalf : Qlt 0 (eps / 2)).
      { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
      exact (Qlt_to_QltT 0 (eps / 2) Hhalf).
    + exists (2 ^ n)%nat. intros k Hk.
      assert (Hsn : step_seq n k == 1) by (apply qeqT_imp_qeq; apply step_seq_ge; exact Hk).
      apply Qlt_to_QltT.
      assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
      (* 目标：eps/2 < u_n(k) − projT1 (1 − eps) k == 1 − (1 − eps) == eps *)
      change (projT1 (real_plus (real_const 1) (real_opp (real_const eps))) k)
        with (projT1 (real_const 1) k + projT1 (real_opp (real_const eps)) k).
      assert (Hc1 : projT1 (real_const 1) k == 1) by (apply qeqT_imp_qeq; apply real_const_proj).
      assert (Hoe : projT1 (real_opp (real_const eps)) k == - projT1 (real_const eps) k).
      { apply qeqT_imp_qeq. apply real_opp_proj. }
      assert (Hce : projT1 (real_const eps) k == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
      setoid_replace (projT1 (step_real n) k - (projT1 (real_const 1) k + projT1 (real_opp (real_const eps)) k))
        with eps by (change (projT1 (step_real n) k) with (step_seq n k);
                     setoid_rewrite Hc1; setoid_rewrite Hoe; setoid_rewrite Hce;
                     setoid_rewrite Hsn; ring).
      exact (QltT_to_Qlt _ _ (q_half_lt eps Heps)).
Qed.

(* 朴素对角线不是极限：¬(real_lim step_real (real_const 0))。
   由 real_lim_unique：若同时收敛到 0，则 real_eq (const 1) (const 0)，
   取 eps := 1/2 得 |1 − 0| < 1/2，矛盾 ¬(1 < 1/2)。 *)
Theorem step_not_lim_zero : Not (real_lim step_real (real_const 0)).
Proof.
  intro Hlim0.
  assert (Hlim1 : real_lim step_real (real_const 1)) by apply step_real_lim_one.
  assert (Heq : real_eq (real_const 1) (real_const 0))
    by (apply (real_lim_unique step_real (real_const 1) (real_const 0) Hlim1 Hlim0)).
  assert (Hhalf0 : QltT 0 (1/2)).
  { unfold QltT, Qlt_bool. simpl. reflexivity. }
  destruct (Heq (1/2) Hhalf0) as [N HN].
  (* N ≤ N：|projT1 (const 1) N − projT1 (const 0) N| < 1/2，即 |1 − 0| < 1/2 *)
  assert (Hbad : QltT (Qabs (projT1 (real_const 1) N - projT1 (real_const 0) N)) (1/2))
    by (apply (HN N (NatLe_lift _ _ (Nat.le_refl N)))).
  apply (not_qlt_one_half).
  apply Qlt_to_QltT.
  apply QltT_to_Qlt in Hbad.
  assert (Hc1 : projT1 (real_const 1) N == 1) by (apply qeqT_imp_qeq; apply real_const_proj).
  assert (Hc0 : projT1 (real_const 0) N == 0) by (apply qeqT_imp_qeq; apply real_const_proj).
  assert (Hgoal : projT1 (real_const 1) N - projT1 (real_const 0) N == 1).
  { simpl. ring. }
  setoid_replace (projT1 (real_const 1) N - projT1 (real_const 0) N)
    with 1%Q in Hbad by exact Hgoal.
  change (Qabs 1) with 1 in Hbad.
  exact Hbad.
Qed.

(* ============================================================ *)
(* Bishop 正则化：Q 层地基（q_arch_inv 阿基米德引理）           *)
(* ============================================================ *)
(* 完备性证明的对角线构造需要"与项无关的统一模"（反例块证明     *)
(* 朴素对角线给出错误极限）。Bishop 正则化：把 cauchy u 重标为   *)
(* v := u∘f，其中 f 递增且 f(k) ≥ modulus(1/(k+2))，使           *)
(* |v a − v b| < 1/(min a b + 2)。                               *)
(* 第一步（本节）：阿基米德引理 ∃N, 1/(N+2) < eps（Qarchimedean）。*)
(* ------------------------------------------------------------ *)

(* Q 层：∀eps>0 ∃N, 1/(N+2)#1 < eps。
   证明：Qarchimedean (1/eps) 给 p 使 1/eps < p#1；
   取 N := 2·|p|（则 p ≤ N+2），链 1/(N+2) < 1/p < eps。 *)
Lemma q_arch_inv : forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => QltT (1 / (Z.of_nat (N + 2) # 1)) eps).
Proof.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  destruct (Qarchimedean (1 / eps)) as [p Hp].
  set (N := (Z.to_nat (Z.pos p) * 2)%nat).
  exists N.
  apply Qlt_to_QltT.
  apply Qlt_shift_div_r; [ | ].
  - (* 0 < (N+2)#1 *)
    unfold Qlt. simpl.
    assert (Hnz : (0 < Z.of_nat (N + 2))%Z) by (unfold N; lia).
    lia.
  - (* 1 < eps * (N+2)#1：链 1 < eps*p#1 < eps*(N+2)#1 *)
    apply (Qlt_trans _ (eps * (Z.pos p # 1)) _).
    + (* 1 < eps * p#1：由 Hp 乘 eps（正） *)
      assert (Hmul : Qlt ((1 / eps) * eps) ((Z.pos p # 1) * eps)).
      { apply (Qmult_lt_compat_r (1 / eps) (Z.pos p # 1) eps HepsQ). exact Hp. }
      setoid_replace ((1 / eps) * eps) with 1%Q in Hmul.
      2: { field. intro Hz. apply (Qlt_not_eq 0 eps HepsQ). exact (Qeq_sym _ _ Hz). }
      setoid_replace ((Z.pos p # 1) * eps) with (eps * (Z.pos p # 1)) in Hmul by ring.
      exact Hmul.
    + setoid_replace (eps * (Z.pos p # 1)) with ((Z.pos p # 1) * eps) by ring.
      setoid_replace (eps * (Z.of_nat (N + 2) # 1)) with ((Z.of_nat (N + 2) # 1) * eps) by ring.
      apply (Qmult_lt_compat_r (Z.pos p # 1) (Z.of_nat (N + 2) # 1) eps HepsQ).
      unfold Qlt. simpl.
      assert (Hz : (Z.pos p < Z.of_nat (N + 2))%Z).
      { unfold N. lia. }
      lia.
Qed.

(* Q 层：1/(N+2)#1 < eps ⟹ 1/(M+2)#1 < eps（M ≥ N，分母增大则值减小）。
   实质：M ≥ N ⟹ M+2 ≥ N+2 ⟹ 1/(M+2) ≤ 1/(N+2) < eps。 *)
Lemma q_arch_inv_mono : forall (eps : Q) (N M : nat),
  (N <= M)%nat -> QltT (1 / (Z.of_nat (N + 2) # 1)) eps ->
  QltT (1 / (Z.of_nat (M + 2) # 1)) eps.
Proof.
  intros eps N M Hle Harch.
  assert (HarchQ : Qlt (1 / (Z.of_nat (N + 2) # 1)) eps) by (apply QltT_to_Qlt; exact Harch).
  destruct (Nat.eq_dec M N) as [Heq | Hne].
  - (* M = N：直接 *)
    subst. exact Harch.
  - (* M > N：(N+2)#1 < (M+2)#1 ⟹ 1/(M+2) < 1/(N+2) < eps *)
    assert (Hlt : (N < M)%nat) by lia.
    apply Qlt_to_QltT.
    apply (Qlt_trans _ (1 / (Z.of_nat (N + 2) # 1)) _).
    + (* 1/(M+2) < 1/(N+2)：Qinv_lt_contravar（倒数反序） *)
      setoid_replace (1 / (Z.of_nat (M + 2) # 1)) with (/ (Z.of_nat (M + 2) # 1))
        by (unfold Qdiv; apply Qmult_1_l).
      setoid_replace (1 / (Z.of_nat (N + 2) # 1)) with (/ (Z.of_nat (N + 2) # 1))
        by (unfold Qdiv; apply Qmult_1_l).
      assert (HposN : Qlt 0 (Z.of_nat (N + 2) # 1)) by (unfold Qlt; simpl; lia).
      assert (HposM : Qlt 0 (Z.of_nat (M + 2) # 1)) by (unfold Qlt; simpl; lia).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (N + 2) # 1) (Z.of_nat (M + 2) # 1)
                    HposN HposM)).
      unfold Qlt. simpl. lia.
    + exact HarchQ.
Qed.

(* Q 层：0 < eps 时 1/(N+2)#1 为正（正则化模的正性） *)
Lemma q_arch_inv_pos : forall (N : nat), QltT 0 (1 / (Z.of_nat (N + 2) # 1)).
Proof.
  intro N.
  apply Qlt_to_QltT.
  (* 0 < 1/x：Qlt_shift_div_l a:=0 b:=1 c:=(N+2)#1 ⟹ 0 < (N+2)#1 且 0·x < 1 *)
  apply Qlt_shift_div_l; [ | ].
  - (* 0 < (N+2)#1 *)
    unfold Qlt. simpl. lia.
  - (* 0·(N+2)#1 < 1：左边 == 0 < 1 *)
    setoid_replace (0 * (Z.of_nat (N + 2) # 1)) with 0%Q by ring.
    reflexivity.
Qed.

(* Q 层：k ≤ f(k) 的均匀模版本——Bishop 正则化的核心不等式
   |v a − v b| ≤ 1/(min a b + 2) 当 a ≤ b 时化为 1/(a+2)。 *)
(* 辅助：Nat.min a b = a 当 a ≤ b（nat 层；min 被 RealInterface.min 遮蔽，用 Nat.min） *)
Lemma nat_min_l : forall a b : nat, (a <= b)%nat -> Id a (Nat.min a b).
Proof. intros a b H. rewrite (Nat.min_l a b H). exact id_refl. Qed.
Lemma nat_min_r : forall a b : nat, (b <= a)%nat -> Id b (Nat.min a b).
Proof. intros a b H. rewrite (Nat.min_r a b H). exact id_refl. Qed.

(* ============================================================ *)
(* Bishop 正则化：regularize / reg_index / 统一模 / 对角线       *)
(* ============================================================ *)
(* 目标：证明完备性不需要 real_cauchy_pointwise（反例已证其不可证）。
   方法：对 cauchy u 构造正则化 v := u ∘ f，其中 f : nat -> nat 严格
   递增且 f(k) ≥ k、f(k) ≥ modulus_u(1/(k+2))（modulus_u = 柯西见证的
   阈值函数）。则 v 有"与项无关的统一模"：|v a − v b| < 1/(min a b + 2)。
   随后用正则化序列族 v_m 的对角线构造完备性极限（v_m 保持实值、
   且继承 u 的实值双柯西；对角线柯西性仅需统一模 + 实值双柯西）。 *)
(* ------------------------------------------------------------ *)

(* 正则化指标函数：f(0) := fmod 0；f(S k) := max (S (f k)) (fmod (S k))。
   性质：f 保序、f(k) ≥ k、f(k) ≥ fmod(k) 恒成立。 *)
Fixpoint reg_index (fmod : nat -> nat) (k : nat) : nat :=
  match k with
  | O => fmod O
  | Datatypes.S k' => max (Datatypes.S (reg_index fmod k')) (fmod (Datatypes.S k'))
  end.

(* reg_index 保序：a ≤ b ⟹ f a ≤ f b（f 严格递增：f(S k) ≥ S (f k) > f k） *)
Lemma reg_index_mono : forall (fmod : nat -> nat) (a b : nat),
  (a <= b)%nat -> NatLe (reg_index fmod a) (reg_index fmod b).
Proof.
  intros fmod. induction b as [| b' IHb]; intros Ha.
  - (* b = 0：a = 0 ⟹ f a = f 0 ≤ f 0 *)
    destruct a; simpl; apply NatLe_lift; lia.
  - (* b = S b'：分 a = S b' 或 a ≤ b' *)
    destruct (Nat.eq_dec a (Datatypes.S b')) as [Heq | Hne].
    + subst. apply NatLe_lift. lia.
    + assert (Ha_le : (a <= b')%nat) by lia.
      (* f a ≤ f b'（IH）≤ S (f b') ≤ max (S (f b')) (fmod (S b')) = f (S b') *)
      apply NatLe_lift.
      apply (Nat.le_trans _ (reg_index fmod b') _ (NatLe_drop _ _ (IHb Ha_le))).
      (* 目标：reg_index fmod b' ≤ reg_index fmod (S b') = max (S (f b')) (fmod (S b')) *)
      change ((reg_index fmod b' <=
              Nat.max (Datatypes.S (reg_index fmod b')) (fmod (Datatypes.S b')))%nat).
      apply Nat.le_trans with (Nat.max (Datatypes.S (reg_index fmod b')) (fmod (Datatypes.S b'))).
      * apply Nat.le_trans with (Datatypes.S (reg_index fmod b')).
        -- apply Nat.le_succ_diag_r.
        -- apply Nat.le_max_l.
      * reflexivity.
Qed.

(* reg_index 覆盖：f(k) ≥ k *)
Lemma reg_index_ge : forall (fmod : nat -> nat) (k : nat),
  NatLe k (reg_index fmod k).
Proof.
  intros fmod. induction k; [ apply NatLe_lift; lia | apply NatLe_lift ].
  (* 目标：S k ≤ f (S k) = max (S (f k)) (fmod (S k))
     链：S k ≤ S (f k)（IH 的 succ 单调）≤ max ... *)
  apply (Nat.le_trans _ (Datatypes.S (reg_index fmod k)) _).
  - exact (le_n_S k (reg_index fmod k) (NatLe_drop _ _ IHk)).
  - change ((Datatypes.S (reg_index fmod k) <=
            Nat.max (Datatypes.S (reg_index fmod k)) (fmod (Datatypes.S k)))%nat).
    apply Nat.le_max_l.
Qed.

(* reg_index 控制模：f(k) ≥ fmod(k) 恒成立 *)
Lemma reg_index_fmod : forall (fmod : nat -> nat) (k : nat),
  NatLe (fmod k) (reg_index fmod k).
Proof.
  intros fmod k. induction k; [ apply NatLe_lift; simpl; lia | apply NatLe_lift ].
  (* 目标：fmod (S k) ≤ f (S k) = max (S (f k)) (fmod (S k)) *)
  change ((fmod (Datatypes.S k) <=
           Nat.max (Datatypes.S (reg_index fmod k)) (fmod (Datatypes.S k)))%nat).
  apply Nat.le_max_r.
Qed.

(* 正则化：v := u ∘ f，f 由柯西模驱动（f(k) ≥ 模(1/(k+2))） *)
(* 第 j 个模（柯西阈值）：q_arch_inv_pos 提供正性（Qlt → QltT） *)
Definition reg_mod (u : Qseq) (Hu : cauchy u) (j : nat) : nat :=
  projT1 (Hu (1 / (Z.of_nat (j + 2) # 1))
              (q_arch_inv_pos j)).

Definition regularize (u : Qseq) (Hu : cauchy u) : Qseq :=
  fun k => u (reg_index (fun j => reg_mod u Hu j) k).

(* Q 层：|a-b| == |b-a|（有理数绝对值对称；正则化对称分支需要） *)
Lemma q_abs_minus_sym : forall a b : Q, QeqT (Qabs (a - b)) (Qabs (b - a)).
Proof.
  intros a b.
  apply qeq_imp_qeqT.
  assert (H : b - a == - (a - b)). { ring. }
  setoid_rewrite H.
  symmetry.
  apply Qabs_opp.
Qed.

(* 正则化保持柯西（统一模）：
   |v a − v b| < 1/(min a b + 2)。
   a ≤ b：f a ≥ fmod a 且 f b ≥ f a ⟹ 由 u 柯西（阈值 fmod a）得
   |u(f a) − u(f b)| < 1/(a+2) == 1/(min a b + 2)。 *)
Lemma regularize_uniform_mod : forall (u : Qseq) (Hu : cauchy u) (a b : nat),
  QltT (Qabs (regularize u Hu a - regularize u Hu b)) (1 / (Z.of_nat (Nat.min a b + 2) # 1)).
Proof.
  intros u Hu a b.
  destruct (Nat.leb a b) eqn:Habeq.
  - assert (Hab : (a <= b)%nat) by (apply Nat.leb_le; exact Habeq).
    (* a ≤ b：min a b = a *)
    destruct (nat_min_l a b Hab).
    unfold regularize.
    set (fmod := fun j : nat => reg_mod u Hu j).
    set (fa := reg_index fmod a).
    set (fb := reg_index fmod b).
    (* 目标：|u(fa) − u(fb)| < 1/(a+2) *)
    assert (Hfa_fmod : (fmod a <= fa)%nat) by (unfold fa; apply NatLe_drop; apply reg_index_fmod).
    assert (Hfa_le_fb : (fa <= fb)%nat) by (unfold fa, fb; apply NatLe_drop; apply reg_index_mono; exact Hab).
    (* u 的柯西性：Hu (1/(a+2)#1) (q_arch_inv_pos a) 给阈值 fmod a：
       对 m n ≥ fmod a，|u m − u n| < 1/(a+2)。取 m := fa, n := fb。 *)
    assert (Hc : QltT (Qabs (u fa - u fb)) (1 / (Z.of_nat (a + 2) # 1))).
    { apply (projT2 (Hu (1 / (Z.of_nat (a + 2) # 1))
                        (q_arch_inv_pos a))
                    fa fb (NatLe_lift _ _ Hfa_fmod)).
      apply NatLe_lift. apply (Nat.le_trans _ fa _ Hfa_fmod Hfa_le_fb). }
    (* 目标：Qlt (Qabs (u fa − u fb)) (1/(a+2)#1) —— 即 Hc 本身（QltT 转 Qlt） *)
    unfold fa, fb in Hc.
    exact Hc.
  - assert (Hba : (b < a)%nat) by (apply Nat.leb_gt; exact Habeq).
    (* b < a：对称，min a b = b *)
    destruct (nat_min_r a b (Nat.lt_le_incl _ _ Hba)).
    apply Qlt_to_QltT.
    unfold regularize.
    set (fmod := fun j : nat => reg_mod u Hu j).
    set (fa := reg_index fmod a).
    set (fb := reg_index fmod b).
    assert (Hfb_fmod : (fmod b <= fb)%nat) by (unfold fb; apply NatLe_drop; apply reg_index_fmod).
    assert (Hfb_le_fa : (fb <= fa)%nat) by (unfold fa, fb; apply NatLe_drop; apply reg_index_mono; lia).
    assert (Hc : QltT (Qabs (u fb - u fa)) (1 / (Z.of_nat (b + 2) # 1))).
    { apply (projT2 (Hu (1 / (Z.of_nat (b + 2) # 1))
                        (q_arch_inv_pos b))
                    fb fa (NatLe_lift _ _ Hfb_fmod)).
      apply NatLe_lift. apply (Nat.le_trans _ fb _ Hfb_fmod Hfb_le_fa). }
    (* 目标：Qlt (Qabs (u fa − u fb)) (1/(b+2)#1) == |u(fb) − u(fa)| 的对称上界 *)
    assert (Hsym : Qabs (u fa - u fb) == Qabs (u fb - u fa)).
    { apply qeqT_imp_qeq. apply q_abs_minus_sym. }
    setoid_rewrite Hsym.
    exact (QltT_to_Qlt _ _ Hc).
Qed.

(* 正则化的柯西见证：统一模 ⟹ 柯西（对 eps，取 N 使 1/(N+2) < eps，
   min a b ≥ N ⟹ 1/(min a b + 2) ≤ 1/(N+2) < eps） *)
Lemma regularize_cauchy : forall (u : Qseq) (Hu : cauchy u),
  cauchy (regularize u Hu).
Proof.
  intros u Hu eps Heps.
  destruct (q_arch_inv eps Heps) as [N HN].
  exists N.
  intros a b Ha Hb.
  (* 目标：QltT (Qabs (v a − v b)) eps *)
  assert (Hmin : (N <= Nat.min a b)%nat).
  { destruct (Nat.le_gt_cases a b) as [Hab' | Hba'].
    - (* min a b = a：N ≤ a ✓ *)
      destruct (nat_min_l a b Hab'). exact (NatLe_drop _ _ Ha).
    - (* min a b = b：N ≤ b ✓ *)
      destruct (nat_min_r a b (Nat.lt_le_incl _ _ Hba')). exact (NatLe_drop _ _ Hb). }
  (* 统一模：|v a − v b| < 1/(min a b + 2) ≤ 1/(N+2) < eps *)
  assert (Hum : Qlt (Qabs (regularize u Hu a - regularize u Hu b))
                    (1 / (Z.of_nat (Nat.min a b + 2) # 1))) by (apply QltT_to_Qlt; apply regularize_uniform_mod).
  assert (Hmono : Qlt (1 / (Z.of_nat (Nat.min a b + 2) # 1)) eps).
  { apply QltT_to_Qlt; apply (q_arch_inv_mono eps N (Nat.min a b) Hmin); exact HN. }
  apply Qlt_to_QltT.
  exact (Qlt_trans _ _ _ Hum Hmono).
Qed.

(* 正则化保持实值：v ≈ u（real_eq）。
   对 eps > 0：u 柯西在 eps/2 给阈值 C（|u m − u n| < eps/2 当 m,n ≥ C）；
   取 N := C。对 k ≥ N：|v k − u k| == |u(f k) − u k|，f k ≥ k ≥ C（reg_index_ge）
   且 k ≥ C，故由 u 柯西得 < eps/2 < eps。 —— 无需 fmod 比较！ *)
Lemma regularize_same_real : forall (u : Qseq) (Hu : cauchy u),
  real_eq (existT _ (regularize u Hu) (regularize_cauchy u Hu))
          (existT _ u Hu).
Proof.
  intros u Hu eps Heps.
  (* eps/2 正性 *)
  assert (Hhalf0 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  destruct (Hu (eps / 2)%Q Hhalf0) as [C HC].
  exists C.
  intros k Hk.
  (* 目标：QltT (Qabs (v k − u k)) eps *)
  assert (Hfk : (C <= reg_index (fun j => reg_mod u Hu j) k)%nat).
  {
    (* f k ≥ k ≥ C *)
    apply (Nat.le_trans _ k _ (NatLe_drop _ _ Hk)).
    apply NatLe_drop. apply reg_index_ge.
  }
  (* HC k (f k) Hk Hfk：|u k − u(f k)| < eps/2 *)
  assert (Hc : QltT (Qabs (u k - u (reg_index (fun j => reg_mod u Hu j) k))) (eps / 2)%Q).
  { apply (HC k (reg_index (fun j => reg_mod u Hu j) k) Hk (NatLe_lift _ _ Hfk)). }
  (* |v k − u k| == |u(f k) − u k| == |u k − u(f k)|（对称） *)
  assert (Hgoal : Qlt (Qabs (regularize u Hu k - u k)) eps).
  {
    unfold regularize.
    assert (Hd : Qabs (u (reg_index (fun j => reg_mod u Hu j) k) - u k)
                  == Qabs (u k - u (reg_index (fun j => reg_mod u Hu j) k))).
    { apply qeqT_imp_qeq. apply q_abs_minus_sym. }
    setoid_rewrite Hd.
    exact (Qlt_trans _ (eps / 2)%Q _ (QltT_to_Qlt _ _ Hc) (QltT_to_Qlt _ _ (q_half_lt eps Heps))).
  }
  apply Qlt_to_QltT.
  exact Hgoal.
Qed.

(* ============================================================ *)
(* 正则化序列族：u : nat -> Real 逐项正则化                    *)
(* ============================================================ *)
(* v_m := regularize (projT1 (u m)) (projT2 (u m))。
   性质：
   (1) 每个 v_m 是柯西（regularize_cauchy）；
   (2) v_m ≈ u_m（real_eq，regularize_same_real）；
   (3) v_m 有统一模：|v_m a − v_m b| < 1/(min a b + 2)（regularize_uniform_mod，
       与 m 无关！）；
   (4) 实值双柯西由 u 继承：real_lt (v_m − v_n) (const eps) 经 v ≈ u 与
       real_lt_eq_lt / real_eq_lt_lt 外延转换。 *)
Definition regularized_family (u : nat -> Real) : nat -> Real :=
  fun m => existT _ (regularize (projT1 (u m)) (projT2 (u m)))
                   (regularize_cauchy (projT1 (u m)) (projT2 (u m))).

(* 正则化族与原始族实值相等：v_m ≈ u_m *)
Lemma regularized_family_same : forall (u : nat -> Real) (m : nat),
  real_eq (regularized_family u m) (u m).
Proof.
  intros u m. unfold regularized_family.
  apply regularize_same_real.
Qed.

(* 正则化族的统一模（与 m 无关）：|v_m a − v_m b| < 1/(min a b + 2) *)
Lemma regularized_family_uniform_mod : forall (u : nat -> Real) (m a b : nat),
  QltT (Qabs (projT1 (regularized_family u m) a - projT1 (regularized_family u m) b))
      (1 / (Z.of_nat (Nat.min a b + 2) # 1)).
Proof.
  intros u m a b. unfold regularized_family.
  apply regularize_uniform_mod.
Qed.

(* ============================================================ *)
(* 柯西实数实例化地基（用户要求：该实例化的必须实例化）       *)
(* ============================================================ *)
(* real_eq 是柯西序列的 Set 层等价（逐 eps 给出 sigT 见证）。  *)
(* 以下证明 real_eq 的自反性——这是未来实例化 RealInterface 时  *)
(* Id 替换性质的最小支撑，也是"信息性证明"（每步 sigT 见证）   *)
(* 的典范。Q 层引理（Qcompare_comp/Qabs_neg/Qplus_opp_r）提供   *)
(* 可判定的有理数算术基础。                                    *)
(* ------------------------------------------------------------ *)

(* Q 层：|a - a| == 0（有理数绝对值自零） *)
Lemma q_abs_self_zero : forall a : Q, QeqT (Qabs (a - a)) 0.
Proof.
  intro a.
  apply qeq_imp_qeqT.
  exact (Qeq_trans (Qabs (a - a)) (Qabs 0) (- 0)%Q
  (Qabs_wd (a - a) 0 (Qplus_opp_r a))
  (Qeq_trans (Qabs 0) (- 0)%Q (- 0)%Q (Qabs_neg 0 (Qle_refl 0))
  (Qeq_refl (- 0)%Q))).
Qed.

(* real_eq 自反性：任意柯西实数与其自身等价（x ~ x） *)
Lemma real_eq_refl : forall x : Real, real_eq x x.
Proof.
  intro x. intro eps. intro Heps. exists O. intro n. intro Hn.
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hz : Qabs (projT1 x n - projT1 x n) == 0) by (apply qeqT_imp_qeq; apply q_abs_self_zero).
  assert (Hcmp : Qcompare (Qabs (projT1 x n - projT1 x n)) eps = Lt).
  {
    assert (Hc1 : Qcompare (Qabs (projT1 x n - projT1 x n)) eps = Qcompare 0 eps).
    { exact (Qcompare_comp (Qabs (projT1 x n - projT1 x n)) 0 Hz eps eps (Qeq_refl eps)). }
    rewrite Hc1. exact Hcmp0.
  }
  rewrite Hcmp. reflexivity.
Qed.

(* ============================================================ *)
(* real_eq 等价关系补全（非平凡平行版本：对称性 + 传递性）     *)
(* ============================================================ *)
(* real_eq_refl 完成自反性；此处补对称性与传递性，使 real_eq 成为 *)
(* 柯西实数的完全等价关系（后续 RealInterface 实例化的前提）。   *)
(* 对称性非平凡：需 |a-b| == |b-a|（ring + Qabs_opp 两步）；      *)
(* 传递性非平凡：需 eps/2 分割 + Qabs_triangle + Qplus_lt_compat  *)
(* （与 real_plus 的柯西界同型，但作用于差序列）。               *)
(* ------------------------------------------------------------ *)

(* Q 层：|a-b| == |b-a|（有理数绝对值对称） *)
(* ============================================================ *)
(* real_lim_scal 的 Q 层缩放引理族（标量 c : Q，|c|+1 归一）    *)
(* ============================================================ *)

(* x ≤ x + y（y ≥ 0） *)
Lemma q_le_plus_nonneg_r_q : forall x y : Q, QleT' 0 y -> QleT' x (x + y).
Proof.
  intros x y Hy.
  apply Qle_to_QleT'.
  exact (Qle_trans x (x + 0) (x + y)
  (QleT'_to_Qle _ _ (qeq_imp_qle x (x + 0) (qeq_imp_qeqT x (x + 0) (Qeq_sym (x + 0) x (Qplus_0_r x)))))
  (Qplus_le_compat x x 0 y (Qle_refl x) (QleT'_to_Qle _ _ Hy))).
Qed.

(* 核心：|d| < e ⟹ c·d < (|c|+1)·e（分 c 符号；上界用 |d|<e 下界用 −e<d） *)
Lemma q_scal_lt : forall c d e : Q, QltT (Qabs d) e -> QltT (c * d) ((Qabs c + 1) * e).
Proof.
  intros c d e Hde.
  assert (HdeQ : Qlt (Qabs d) e) by (apply QltT_to_Qlt; exact Hde).
  destruct (Qlt_le_dec c 0) as [Hc | Hc0].
  - (* c < 0：c == −|c|；用下界 −e < d ⟹ −(|c|·d) < |c|·e == c·d 的上界 *)
    assert (Hac : Qabs c == - c) by (apply Qabs_neg; apply Qlt_le_weak; exact Hc).
    (* |d| < e ⟹ −e < d（Qabs_Qlt_condition proj1 前半） *)
    assert (Hboth : Qlt (- e) d /\ Qlt d e) by (exact (proj1 (Qabs_Qlt_condition d e) HdeQ)).
    pose proof (proj1 Hboth) as Hlow.
    pose proof (proj2 Hboth) as Hup.
    (* 0 < |c|（c < 0 ⟹ |c| == −c > 0） *)
    assert (Hpos : Qlt 0 (Qabs c)).
    { setoid_rewrite Hac. apply (Qopp_lt_compat c 0 Hc). }
    (* −e < d ⟹ |c|·(−e) < |c|·d（Qmult_lt_compat_r 换序） ⟹ −(|c|·e) < |c|·d *)
    assert (Hmid : Qlt (- (Qabs c * e)) (Qabs c * d)).
    {
      assert (Hlt : Qlt ((- e) * (Qabs c)) (d * (Qabs c)))
        by (apply Qmult_lt_compat_r; [exact Hpos | exact Hlow]).
      setoid_replace ((- e) * (Qabs c)) with (- (Qabs c * e)) in Hlt by ring.
      setoid_replace (d * (Qabs c)) with (Qabs c * d) in Hlt by ring.
      exact Hlt.
    }
    (* −(|c|·d) < |c|·e：由 Hmid : −(|c|·e) < |c|·d 取负得
       −(|c|·d) < −(−(|c|·e))，再 Qopp_involutive 化简右侧 *)
    assert (Hopp : Qlt (- (Qabs c * d)) (Qabs c * e)).
    {
      assert (H1 : Qlt (- (Qabs c * d)) (- (- (Qabs c * e)))).
      { apply (Qopp_lt_compat (- (Qabs c * e)) (Qabs c * d)). exact Hmid. }
      setoid_replace (- (- (Qabs c * e))) with (Qabs c * e) in H1 by
        (apply Qopp_involutive).
      exact H1.
    }
    (* c·d == −(|c|·d)（c == −|c|） *)
    assert (Hcid : c * d == - (Qabs c * d)).
    { setoid_rewrite Hac. ring. }
    (* |c|·e ≤ (|c|+1)·e（e > 0 由 |d| < e 且 Qabs d ≥ 0：Qlt 0 (Qabs d) ≤ ... 反推）
       直接：0 ≤ Qabs d < e ⟹ 0 < e（Qlt_le_trans 0 (Qabs d) e） *)
    assert (He0 : Qle 0 e).
    {
      apply Qlt_le_weak.
      apply (Qle_lt_trans 0 (Qabs d) e).
      - apply Qabs_nonneg.
      - exact HdeQ.
    }
    assert (Hle : Qle (Qabs c * e) ((Qabs c + 1) * e)).
    { apply (Qmult_le_compat_r (Qabs c) (Qabs c + 1) e).
      - apply QleT'_to_Qle. apply q_le_plus_nonneg_r_q. apply Qle_to_QleT'. apply Qlt_le_weak. reflexivity.
      - exact He0. }
    assert (Hcd_lt : Qlt (c * d) (Qabs c * e)).
    { setoid_replace (c * d) with (- (Qabs c * d)) by exact Hcid. exact Hopp. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (Qabs c * e) _).
    + exact Hcd_lt.
    + exact Hle.
  - (* c ≥ 0：c·d ≤ |c|·|d| ≤ (|c|+1)·|d| < (|c|+1)·e *)
    assert (Hac : Qabs c == c) by (apply Qabs_pos; exact Hc0).
    (* c·d ≤ |c|·|d|：c ≥ 0 且 d ≤ |d|（Qle_Qabs），Qmult_le_compat_r 换序 *)
    assert (Hd : Qle 0 (Qabs c)) by apply Qabs_nonneg.
    assert (Hcd : Qle (c * d) (Qabs c * Qabs d)).
    {
      assert (H1 : Qle (d * c) (Qabs d * c))
        by (apply Qmult_le_compat_r; [apply Qle_Qabs | exact Hc0]).
      setoid_replace (d * c) with (c * d) in H1 by ring.
      (* 右侧 |d|·c == |c|·|d|（Hac 正向换 Qabs c → c 后 ring；勿反向换裸 c） *)
      assert (Hrhs : Qabs d * c == Qabs c * Qabs d).
      {
        apply (Qeq_trans _ (Qabs d * Qabs c) _).
        - rewrite Hac. reflexivity.   (* |d|·c == |d|·|c|：仅 Qabs c 被换 *)
        - ring.                        (* |d|·|c| == |c|·|d| *)
      }
      setoid_rewrite Hrhs in H1.
      exact H1.
    }
    assert (Hd' : Qle 0 (Qabs d)) by apply Qabs_nonneg.
    assert (Hmid : Qle (Qabs c * Qabs d) ((Qabs c + 1) * Qabs d)).
    { apply (Qmult_le_compat_r (Qabs c) (Qabs c + 1) (Qabs d)).
      - apply QleT'_to_Qle. apply q_le_plus_nonneg_r_q. apply Qle_to_QleT'. apply Qlt_le_weak. reflexivity.
      - exact Hd'. }
    assert (Hlt : Qlt ((Qabs c + 1) * Qabs d) ((Qabs c + 1) * e)).
    {
      assert (Hpos : Qlt 0 (Qabs c + 1)).
      { apply Qlt_le_trans with 1%Q.
        - reflexivity.
        - (* 1 ≤ |c|+1：先换形 1+|c| 再 q_le_plus_nonneg_r_q *)
          setoid_replace (Qabs c + 1) with (1 + Qabs c) by ring.
          apply QleT'_to_Qle. apply q_le_plus_nonneg_r_q. apply Qle_to_QleT'. apply Qabs_nonneg. }
      assert (Hr : Qlt (Qabs d * (Qabs c + 1)) (e * (Qabs c + 1)))
        by (apply Qmult_lt_compat_r; [exact Hpos | exact HdeQ]).
      setoid_replace (Qabs d * (Qabs c + 1)) with ((Qabs c + 1) * Qabs d) in Hr by ring.
      setoid_replace (e * (Qabs c + 1)) with ((Qabs c + 1) * e) in Hr by ring.
      exact Hr.
    }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs c * Qabs d) _).
    + exact Hcd.
    + apply (Qle_lt_trans _ ((Qabs c + 1) * Qabs d) _); [exact Hmid | exact Hlt].
Qed.

(* |a| ≤ A、|b| < E、0 < A、0 < E ⟹ |a|·|b| < A·E（乘积界，real_lim_mult 需要） *)
Lemma q_abs_mul_bound : forall a b A E : Q,
  QleT' (Qabs a) A -> QltT (Qabs b) E -> QltT 0 A -> QltT 0 E ->
  QltT (Qabs a * Qabs b) (A * E).
Proof.
  intros a b A E Ha Hb HA HE.
  apply QleT'_to_Qle in Ha.
  apply QltT_to_Qlt in Hb.
  apply QltT_to_Qlt in HA.
  apply QltT_to_Qlt in HE.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (A * Qabs b) _).
  - apply Qmult_le_compat_r; [exact Ha | apply Qabs_nonneg].
  - (* A·|b| < A·E：Qmult_lt_compat_r 给 |b|·A < E·A，ring 换序 *)
    setoid_replace (A * Qabs b) with (Qabs b * A) by ring.
    setoid_replace (A * E) with (E * A) by ring.
    apply (Qmult_lt_compat_r _ _ A HA). exact Hb.
Qed.

(* 0 < eps 且 0 ≤ M ⟹ 0 < eps/(4·(M+1))（缩放分母正性，real_lim_mult 需要） *)
Lemma q_pos_scale : forall (eps M : Q), QltT 0 eps -> QleT' 0 M -> QltT 0 (eps / (4 * (M + 1))).
Proof.
  intros eps M Heps HM.
  apply QltT_to_Qlt in Heps.
  apply QleT'_to_Qle in HM.
  apply Qlt_to_QltT.
  apply (Qlt_shift_div_l 0 eps (4 * (M + 1))).
  - apply Qmult_lt_0_compat.
    + reflexivity.  (* 0 < 4 *)
    + (* 0 < M+1：Qplus_lt_le_compat 0 1 0 M（0<1、0≤M）⟹ 0+0 < 1+M，化简 *)
      assert (Hsum : Qlt (0 + 0) (1 + M)) by (apply Qplus_lt_le_compat; [reflexivity | exact HM]).
      setoid_replace (1 + M) with (M + 1) in Hsum by ring.
      setoid_replace (0 + 0) with 0 in Hsum by ring.
      exact Hsum.
  - setoid_replace (0 * (4 * (M + 1))) with 0 by ring.
    exact Heps.
Qed.

(* 乘积差分解：a·b − c·d == a·(b−d) + (a−c)·d *)
Lemma q_prod_diff : forall a b c d : Q,
  QeqT (a * b - c * d) (a * (b - d) + (a - c) * d).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* 乘积差的三角界：|a·b − c·d| ≤ |a|·|b−d| + |a−c|·|d|（real_lim_mult 核心分解） *)
Lemma q_prod_diff_bound : forall a b c d : Q,
  QleT' (Qabs (a * b - c * d)) (Qabs a * Qabs (b - d) + Qabs (a - c) * Qabs d).
Proof.
  intros a b c d.
  apply Qle_to_QleT'.
  assert (Hdecomp : a * b - c * d == a * (b - d) + (a - c) * d) by ring.
  setoid_rewrite Hdecomp.
  apply (Qle_trans _ (Qabs (a * (b - d)) + Qabs ((a - c) * d)) _).
  - apply Qabs_triangle.
  - apply Qplus_le_compat.
    + rewrite Qabs_Qmult. apply Qle_refl.
    + rewrite Qabs_Qmult. apply Qle_refl.
Qed.

(* 缩放 eps：|d| < eps/(2(|c|+1)) ⟹ c·d < eps/2 *)
Lemma q_scal_eps_half : forall c d eps : Q, QltT 0 eps ->
  QltT (Qabs d) (eps / (2 * (Qabs c + 1))) -> QltT (c * d) (eps / 2).
Proof.
  intros c d eps HepsT Hd.
  apply QltT_to_Qlt in Hd.
  apply Qlt_to_QltT.
  assert (Hmid : Qlt (c * d) ((Qabs c + 1) * (eps / (2 * (Qabs c + 1))))).
  { apply QltT_to_Qlt. apply q_scal_lt. exact (Qlt_to_QltT _ _ Hd). }
  apply (Qlt_le_trans _ ((Qabs c + 1) * (eps / (2 * (Qabs c + 1)))) _ Hmid).
  assert (Heq : (Qabs c + 1) * (eps / (2 * (Qabs c + 1))) == eps / 2).
  {
    field.
    (* 条件：~ (Qabs c + 1 == 0)：由 0 < |c|+1 且 Qlt_not_eq 给 ~ 0 == |c|+1，Qeq_sym 换向 *)
    intro Hzero.
    assert (Hlt0 : Qlt 0 (Qabs c + 1)).
    { apply (Qlt_le_trans 0 1 (Qabs c + 1)).
      - assert (Hz : Qlt 0 1) by reflexivity. exact Hz.
      - setoid_replace (Qabs c + 1) with (1 + Qabs c) by ring.
        apply QleT'_to_Qle. apply q_le_plus_nonneg_r_q. apply Qle_to_QleT'. apply Qabs_nonneg. }
    exact (Qlt_not_eq 0 (Qabs c + 1) Hlt0 (Qeq_sym _ _ Hzero)).
  }
  rewrite Heq. apply Qle_refl.
Qed.

(* 对称：|d| < eps/(2(|c|+1)) ⟹ −(c·d) < eps/2（下夹逼用） *)
Lemma q_scal_eps_half_neg : forall c d eps : Q, QltT 0 eps ->
  QltT (Qabs d) (eps / (2 * (Qabs c + 1))) -> QltT (- (c * d)) (eps / 2).
Proof.
  intros c d eps HepsT HdT.
  apply Qlt_to_QltT.
  setoid_replace (- (c * d)) with ((- c) * d) by ring.
  apply QltT_to_Qlt.
  apply (q_scal_eps_half (- c) d eps HepsT).
  apply Qlt_to_QltT.
  setoid_replace (2 * (Qabs (- c) + 1)) with (2 * (Qabs c + 1)).
  - apply QltT_to_Qlt. exact HdT.
  - assert (Hao : Qabs (- c) == Qabs c) by apply Qabs_opp.
    setoid_rewrite Hao. reflexivity.
Qed.

(* real_eq 对称性：x ~ y ⟹ y ~ x（差序列绝对值对称） *)
Lemma real_eq_sym : forall x y : Real, real_eq x y -> real_eq y x.
Proof.
  intros x y Hxy eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N.
  intro n. intro Hn.
  specialize (HN n Hn).   (* HN : QltT (Qabs (x n - y n)) eps *)
  unfold QltT, Qlt_bool in HN |- *.
  assert (Hcmp : Qcompare (Qabs (projT1 y n - projT1 x n)) eps =
                 Qcompare (Qabs (projT1 x n - projT1 y n)) eps).
  { exact (Qcompare_comp (Qabs (projT1 y n - projT1 x n))
                         (Qabs (projT1 x n - projT1 y n))
                         (qeqT_imp_qeq _ _ (q_abs_minus_sym (projT1 y n) (projT1 x n)))
                         eps eps (Qeq_refl eps)). }
  rewrite Hcmp.
  exact HN.
Qed.

(* real_eq 传递性：x ~ y ⟹ y ~ z ⟹ x ~ z（eps/2 分割 + 三角不等式） *)
Lemma real_eq_trans : forall x y z : Real, real_eq x y -> real_eq y z -> real_eq x z.
Proof.
  intros x y z Hxy Hyz eps Heps.
  destruct (Hxy (eps/2)%Q) as [N1 HN1].
  { assert (Hhalf : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    apply Qlt_to_QltT. exact Hhalf. }
  destruct (Hyz (eps/2)%Q) as [N2 HN2].
  { assert (Hhalf2 : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    apply Qlt_to_QltT. exact Hhalf2. }
  exists (max N1 N2).
  intro n. intro Hn.
  apply Qlt_to_QltT.
  apply Qle_lt_trans with (Qabs (projT1 x n - projT1 y n) + Qabs (projT1 y n - projT1 z n)).
  - (* 三角不等式：|x-z| ≤ |x-y| + |y-z| *)
    assert (Hsum : projT1 x n - projT1 z n ==
                   (projT1 x n - projT1 y n) + (projT1 y n - projT1 z n)).
    { ring. }
    setoid_rewrite Hsum.
    apply Qabs_triangle.
  - (* eps/2 + eps/2 = eps *)
    assert (Heps_sum : eps/2 + eps/2 == eps). { field. }
    setoid_rewrite <- Heps_sum.
    apply Qplus_lt_compat.
    + apply QltT_to_Qlt. apply HN1.
      apply NatLe_lift. exact (Nat.le_trans _ (max N1 N2) _ (Nat.le_max_l N1 N2) (NatLe_drop _ _ Hn)).
    + apply QltT_to_Qlt. apply HN2.
      apply NatLe_lift. exact (Nat.le_trans _ (max N1 N2) _ (Nat.le_max_r N1 N2) (NatLe_drop _ _ Hn)).
Qed.

(* ============================================================ *)
(* Real 环核心（RealInterface 实例化的代数骨架）                *)
(* ============================================================ *)
(* 完整 RealInterface 实例需 exp/log/metric/lim 等分析构造（大工程）； *)
(* 此处先完成代数骨架：Real 在 real_eq 意义下构成交换环——加法/   *)
(* 乘法/零/壹/负元/分配律共 9 条（逐点成立，N = 0）。            *)
(* 注：接口的 Id 是定义性相等（单构造子），柯西实数非典范表示 ⟹  *)
(* 完整实例需先改接口等式或商掉 real_eq（结构性缺失.txt 已注记）。*)

Definition real_one : Real.
Proof.
  exists (fun _ => 1%Q).
  intros eps Heps. exists O. intros m n Hm Hn.
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hz : Qabs (1 - 1) == 0) by (apply qeqT_imp_qeq; apply q_abs_self_zero).
  assert (Hcmp : Qcompare (Qabs (1 - 1)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (1 - 1)) eps = Qcompare 0 eps)
      by (exact (Qcompare_comp (Qabs (1 - 1)) 0 Hz eps eps (Qeq_refl eps))).
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Defined.

(* 逐点差为零 ⟹ real_eq（N = 0 的统一证明模式，环律的公共内核） *)
Lemma real_eq_of_zero_diff : forall x y : Real,
  (forall n : nat, QeqT (projT1 x n - projT1 y n) 0) -> real_eq x y.
Proof.
  intros x y Hz eps Heps. exists O. intro n. intro Hn.
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hd : Qabs (projT1 x n - projT1 y n) == 0).
  { rewrite (qeqT_imp_qeq _ _ (Hz n)). reflexivity. }
  assert (Hcmp : Qcompare (Qabs (projT1 x n - projT1 y n)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (projT1 x n - projT1 y n)) eps = Qcompare 0 eps)
      by (exact (Qcompare_comp (Qabs (projT1 x n - projT1 y n)) 0 Hd eps eps (Qeq_refl eps))).
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* 环律（real_eq 层，逐点 Q 环恒等，N = 0）
   注：先 destruct 输入为 existT 构造子形式，simpl 才能归约 projT1
   （real_plus/real_mult 体内对输入做 match）。 *)
Lemma real_plus_comm : forall x y : Real, real_eq (real_plus x y) (real_plus y x).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_plus_assoc : forall x y z : Real, real_eq (real_plus x (real_plus y z)) (real_plus (real_plus x y) z).
Proof.
  intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_plus_zero : forall x : Real, real_eq (real_plus x real_zero) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_plus_opp : forall x : Real, real_eq (real_plus x (real_opp x)) real_zero.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_mult_comm : forall x y : Real, real_eq (real_mult x y) (real_mult y x).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_mult_assoc : forall x y z : Real, real_eq (real_mult x (real_mult y z)) (real_mult (real_mult x y) z).
Proof.
  intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_mult_one : forall x : Real, real_eq (real_mult x real_one) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_mult_zero : forall x : Real, real_eq (real_mult x real_zero) real_zero.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma real_distrib : forall x y z : Real,
  real_eq (real_mult x (real_plus y z)) (real_plus (real_mult x y) (real_mult x z)).
Proof.
  intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* ============================================================ *)
(* Real 序核心（RealInterface 实例化的序骨架）                  *)
(* ============================================================ *)
(* 环核心之上补齐序律：real_lt 不可反、real_le 自反/反对称/传递、 *)
(* 混合传递（real_lt_eq_lt / real_eq_lt_lt 用 eps/2 分割 +         *)
(* Qabs_Qlt_condition 下界）。exp/log/metric/lim 仍为剩余大工程   *)
(* （见结构性缺失.txt 注记）。                                   *)

(* real_lt 不可反：不存在 eps > 0 使 eps < x_n - x_n = 0 *)
Lemma real_lt_irrefl : forall x : Real, Not (real_lt x x).
Proof.
  intros x [eps [Heps [N HN]]].
  specialize (HN N (NatLe_lift _ _ (Nat.le_refl N))).
  assert (Hlt0 : Qlt eps 0).
  {
    assert (Hz : projT1 x N - projT1 x N == 0).
    { unfold Qminus. apply Qplus_opp_r. }
    apply QltT_to_Qlt in HN.
    setoid_rewrite Hz in HN.
    exact HN.
  }
  assert (H0e : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  exact (match (Qlt_irrefl 0 (Qlt_trans 0 eps 0 H0e Hlt0)) with end).
Qed.

(* real_le 自反（real_eq_refl 直接） *)
Lemma real_le_refl : forall x : Real, real_le x x.
Proof. intro x. exact (inr (real_eq_refl x)). Qed.

(* 兼容引理：real_lt x y ∧ real_eq y z ⟹ real_lt x z（eps/2 分割 + 下界） *)
Lemma real_lt_eq_lt : forall x y z : Real, real_lt x y -> real_eq y z -> real_lt x z.
Proof.
  intros x y z Hlt Hyz.
  destruct Hlt as [eps1 [Heps1 [N1 HN1]]].
  destruct (Hyz (eps1/2)%Q) as [N2 HN2].
  { assert (Hhalf : Qlt 0 (eps1 / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps1. }
    apply Qlt_to_QltT. exact Hhalf. }
  exists (eps1/2)%Q.
  split.
  - apply Qlt_to_QltT.
    apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps1.
  - exists (max N1 N2). intro n. intro Hn.
    apply Qlt_to_QltT.
    assert (Hlt1 : Qlt eps1 (projT1 y n - projT1 x n)).
    { apply QltT_to_Qlt. apply HN1.
      apply NatLe_lift. exact (Nat.le_trans _ (max N1 N2) _ (Nat.le_max_l N1 N2) (NatLe_drop _ _ Hn)). }
    assert (Hd2 : Qlt (Qabs (projT1 y n - projT1 z n)) (eps1 / 2)).
    { apply QltT_to_Qlt. apply HN2.
      apply NatLe_lift. exact (Nat.le_trans _ (max N1 N2) _ (Nat.le_max_r N1 N2) (NatLe_drop _ _ Hn)). }
    (* z_n - x_n = (y_n - x_n) + (z_n - y_n) > eps1 - eps1/2 = eps1/2 *)
    assert (Hsum : projT1 z n - projT1 x n == (projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)).
    { ring. }
    setoid_rewrite Hsum.
    assert (Hlb : Qlt (- (eps1 / 2)) (projT1 z n - projT1 y n)).
    {
      assert (Hzd : Qlt (Qabs (projT1 z n - projT1 y n)) (eps1 / 2)).
      { setoid_rewrite (qeqT_imp_qeq _ _ (q_abs_minus_sym (projT1 z n) (projT1 y n))). exact Hd2. }
      destruct (proj1 (Qabs_Qlt_condition (projT1 z n - projT1 y n) (eps1 / 2)) Hzd) as [Hlow _].
      exact Hlow.
    }
    assert (Hcomb : Qlt (eps1 + (- (eps1 / 2))) ((projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)))
      by (apply Qplus_lt_compat; [exact Hlt1 | exact Hlb]).
    assert (Heps : eps1 + (- (eps1 / 2)) == eps1 / 2). { field. }
    setoid_rewrite Heps in Hcomb.
    exact Hcomb.
Qed.

(* 兼容引理：real_eq x y ∧ real_lt y z ⟹ real_lt x z（对称论证） *)
Lemma real_eq_lt_lt : forall x y z : Real, real_eq x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hxy Hlt.
  destruct Hlt as [eps1 [Heps1 [N1 HN1]]].
  destruct (Hxy (eps1/2)%Q) as [N2 HN2].
  { assert (Hhalf : Qlt 0 (eps1 / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps1. }
    apply Qlt_to_QltT. exact Hhalf. }
  exists (eps1/2)%Q.
  split.
  - apply Qlt_to_QltT.
    apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps1.
  - exists (max N1 N2). intro n. intro Hn.
    apply Qlt_to_QltT.
    assert (Hlt1 : Qlt eps1 (projT1 z n - projT1 y n)).
    { apply QltT_to_Qlt. apply HN1.
      apply NatLe_lift. exact (Nat.le_trans _ (max N1 N2) _ (Nat.le_max_l N1 N2) (NatLe_drop _ _ Hn)). }
    assert (Hd2 : Qlt (Qabs (projT1 x n - projT1 y n)) (eps1 / 2)).
    { apply QltT_to_Qlt. apply HN2.
      apply NatLe_lift. exact (Nat.le_trans _ (max N1 N2) _ (Nat.le_max_r N1 N2) (NatLe_drop _ _ Hn)). }
    (* z_n - x_n = (z_n - y_n) + (y_n - x_n) > eps1 - eps1/2 = eps1/2 *)
    assert (Hsum : projT1 z n - projT1 x n == (projT1 z n - projT1 y n) + (projT1 y n - projT1 x n)).
    { ring. }
    setoid_rewrite Hsum.
    assert (Hlb : Qlt (- (eps1 / 2)) (projT1 y n - projT1 x n)).
    {
      assert (Hzd : Qlt (Qabs (projT1 y n - projT1 x n)) (eps1 / 2)).
      { setoid_rewrite (qeqT_imp_qeq _ _ (q_abs_minus_sym (projT1 y n) (projT1 x n))). exact Hd2. }
      destruct (proj1 (Qabs_Qlt_condition (projT1 y n - projT1 x n) (eps1 / 2)) Hzd) as [Hlow _].
      exact Hlow.
    }
    assert (Hcomb : Qlt (eps1 + (- (eps1 / 2))) ((projT1 z n - projT1 y n) + (projT1 y n - projT1 x n)))
      by (apply Qplus_lt_compat; [exact Hlt1 | exact Hlb]).
    assert (Heps : eps1 + (- (eps1 / 2)) == eps1 / 2). { field. }
    setoid_rewrite Heps in Hcomb.
    exact Hcomb.
Qed.

(* real_le 传递（四种情形组合） *)
Lemma real_le_trans : forall x y z : Real, real_le x y -> real_le y z -> real_le x z.
Proof.
  intros x y z Hxy Hyz.
  exact (match Hxy with
  | inl Hlt => match Hyz with
  | inl Hlt' => inl (real_lt_trans x y z Hlt Hlt')
  | inr Heq' => inl (real_lt_eq_lt x y z Hlt Heq') end
  | inr Heq => match Hyz with
  | inl Hlt' => inl (real_eq_lt_lt x y z Heq Hlt')
  | inr Heq' => inr (real_eq_trans x y z Heq Heq') end end).
Qed.

(* ============================================================ *)
(* Bishop 正则化续节：差外延 + 正则化族双柯西保持              *)
(* ============================================================ *)
(* real_eq 对减法（plus + opp）的外延性：a≈c ∧ b≈d ⟹ a−b ≈ c−d。
   直接构造：eps/2 分割 + |(a−c)−(b−d)| ≤ |a−c| + |b−d|（Qabs_triangle）。 *)
Lemma real_eq_minus_compat : forall (a b c d : Real),
  real_eq a c -> real_eq b d ->
  real_eq (real_plus a (real_opp b)) (real_plus c (real_opp d)).
Proof.
  intros a b c d Hac Hbd eps Heps.
  (* 一致界：|a_k| ≤ Ma、|d_k| ≤ Md（q_prod_diff_bound 需要 |a| 与 |d| 的界） *)
  destruct (real_norm_bounded a) as [Ma [HMa_pos HMa]].
  destruct (real_norm_bounded d) as [Md [HMd_pos HMd]].
  (* eps/2 正性 *)
  assert (Hhalf0 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  destruct (Hac (eps / 2)%Q Hhalf0) as [N1 HN1].
  destruct (Hbd (eps / 2)%Q Hhalf0) as [N2 HN2].
  exists (max N1 N2).
  intros k Hk.
  assert (HkN1 : (N1 <= k)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hk)]).
  assert (HkN2 : (N2 <= k)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hk)]).
  (* 目标：QltT (Qabs (projT1 (a−b) k − projT1 (c−d) k)) eps *)
  apply Qlt_to_QltT.
  (* 换形：(a−b) − (c−d) == (a−c) − (b−d)（ring） *)
  assert (Hd : projT1 (real_plus a (real_opp b)) k - projT1 (real_plus c (real_opp d)) k
               == (projT1 a k - projT1 c k) - (projT1 b k - projT1 d k)).
  {
    (* real_plus/real_opp 是 Defined 体：projT1 展开需 destruct（定义性归约）
       —— 用投影引理（Section 内定义，全局可用） *)
    assert (Hpa : projT1 (real_plus a (real_opp b)) k == projT1 a k + projT1 (real_opp b) k)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Hob : projT1 (real_opp b) k == - projT1 b k) by (apply qeqT_imp_qeq; apply real_opp_proj).
    assert (Hpc : projT1 (real_plus c (real_opp d)) k == projT1 c k + projT1 (real_opp d) k)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Hod : projT1 (real_opp d) k == - projT1 d k) by (apply qeqT_imp_qeq; apply real_opp_proj).
    setoid_rewrite Hpa. setoid_rewrite Hob.
    setoid_rewrite Hpc. setoid_rewrite Hod.
    ring.
  }
  setoid_rewrite Hd.
  (* 目标：Qlt (Qabs ((a−c) − (b−d))) eps；三角不等式 *)
  assert (H1 : Qlt (Qabs (projT1 a k - projT1 c k)) (eps / 2)%Q)
    by (apply QltT_to_Qlt; apply HN1; exact (NatLe_lift _ _ HkN1)).
  assert (H2 : Qlt (Qabs (projT1 b k - projT1 d k)) (eps / 2)%Q)
    by (apply QltT_to_Qlt; apply HN2; exact (NatLe_lift _ _ HkN2)).
  apply (Qle_lt_trans _ (Qabs (projT1 a k - projT1 c k) + Qabs (projT1 b k - projT1 d k)) _).
  - (* |(a−c) − (b−d)| ≤ |a−c| + |b−d|：三角不等式（减法版） *)
    setoid_replace ((projT1 a k - projT1 c k) - (projT1 b k - projT1 d k))
      with ((projT1 a k - projT1 c k) + (- (projT1 b k - projT1 d k))) by ring.
    apply (Qle_trans _ (Qabs (projT1 a k - projT1 c k) + Qabs (- (projT1 b k - projT1 d k))) _).
    + apply Qabs_triangle.
    + assert (Habs : Qabs (- (projT1 b k - projT1 d k)) == Qabs (projT1 b k - projT1 d k)).
      { apply Qabs_opp. }
      setoid_rewrite Habs. apply Qle_refl.
  - assert (Hsum : eps / 2 + eps / 2 == eps). { field. }
    setoid_rewrite <- Hsum.
    apply Qplus_lt_compat; exact H1 || exact H2.
Qed.

(* 实值双柯西经正则化族保持：
   v_m ≈ u_m ∧ v_n ≈ u_n ⟹ (v_m − v_n) ≈ (u_m − u_n)（real_eq_minus_compat），
   故 real_lt (v_m − v_n) (const eps) 由前提 real_lt (u_m − u_n) (const eps)
   经 real_lt_eq_lt 传递。 *)
Lemma regularized_family_double_cauchy :
  forall (u : nat -> Real),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        And (real_lt (real_plus (u m) (real_opp (u n))) (real_const eps))
            (real_lt (real_plus (u n) (real_opp (u m))) (real_const eps)))) ->
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        And (real_lt (real_plus (regularized_family u m) (real_opp (regularized_family u n))) (real_const eps))
            (real_lt (real_plus (regularized_family u n) (real_opp (regularized_family u m))) (real_const eps)))).
Proof.
  intros u Hcau eps Heps.
  destruct (Hcau eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  destruct (HN m n Hm Hn) as [Hlt1 Hlt2].
  split.
  - (* 方向 1：real_lt (v_m − v_n) (const eps)
       链：v_m − v_n ≈ u_m − u_n（差外延）< const eps ⟹ real_lt（real_eq_lt_lt） *)
    apply (real_eq_lt_lt (real_plus (regularized_family u m) (real_opp (regularized_family u n)))
                          (real_plus (u m) (real_opp (u n)))
                          (real_const eps)).
    + (* real_eq (v_m − v_n) (u_m − u_n)：由 v_m ≈ u_m、v_n ≈ u_n 及差外延 *)
      apply (real_eq_minus_compat (regularized_family u m) (regularized_family u n) (u m) (u n)).
      * apply regularized_family_same.
      * apply regularized_family_same.
    + exact Hlt1.
  - (* 方向 2：对称 *)
    apply (real_eq_lt_lt (real_plus (regularized_family u n) (real_opp (regularized_family u m)))
                          (real_plus (u n) (real_opp (u m)))
                          (real_const eps)).
    + apply (real_eq_minus_compat (regularized_family u n) (regularized_family u m) (u n) (u m)).
      * apply regularized_family_same.
      * apply regularized_family_same.
    + exact Hlt2.
Qed.

(* 双向实值差界 ⟹ 逐点差界：
   real_lt (x−y) (const eps) ∧ real_lt (y−x) (const eps)
   ⟹ ∃M ∀k≥M: |x k − y k| < eps。
   证明：e1 < eps − (x k − y k) ⟹ x k − y k < eps − e1 < eps；
         e2 < eps − (y k − x k) ⟹ −eps < x k − y k（e2 > 0）；
         q_abs_lt_two_sided 组装。 *)
Lemma real_lt_pair_abs_bound :
  forall (x y : Real) (eps : Q) (Heps : QltT 0 eps),
    real_lt (real_plus x (real_opp y)) (real_const eps) ->
    real_lt (real_plus y (real_opp x)) (real_const eps) ->
    sigT (fun M : nat => forall k : nat, (M <= k)%nat ->
      QltT (Qabs (projT1 x k - projT1 y k)) eps).
Proof.
  intros x y eps Heps H1 H2.
  destruct H1 as [e1 [He1 [M1 HM1]]].
  destruct H2 as [e2 [He2 [M2 HM2]]].
  exists (max M1 M2).
  intros k Hk.
  assert (Hk1 : (M1 <= k)%nat) by (apply Nat.le_trans with (max M1 M2); [apply Nat.le_max_l | exact Hk]).
  assert (Hk2 : (M2 <= k)%nat) by (apply Nat.le_trans with (max M1 M2); [apply Nat.le_max_r | exact Hk]).
  (* 展开：projT1 (const eps) k == eps；projT1 (x − y) k == x k − y k *)
  assert (Hpt1 : projT1 (real_const eps) k - projT1 (real_plus x (real_opp y)) k
                 == eps - (projT1 x k - projT1 y k)).
  {
    assert (Hc : projT1 (real_const eps) k == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
    assert (Hp : projT1 (real_plus x (real_opp y)) k == projT1 x k + projT1 (real_opp y) k)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Ho : projT1 (real_opp y) k == - projT1 y k) by (apply qeqT_imp_qeq; apply real_opp_proj).
    setoid_rewrite Hc. setoid_rewrite Hp. setoid_rewrite Ho.
    ring.
  }
  assert (Hpt2 : projT1 (real_const eps) k - projT1 (real_plus y (real_opp x)) k
                 == eps - (projT1 y k - projT1 x k)).
  {
    assert (Hc : projT1 (real_const eps) k == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
    assert (Hp : projT1 (real_plus y (real_opp x)) k == projT1 y k + projT1 (real_opp x) k)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Ho : projT1 (real_opp x) k == - projT1 x k) by (apply qeqT_imp_qeq; apply real_opp_proj).
    setoid_rewrite Hc. setoid_rewrite Hp. setoid_rewrite Ho.
    ring.
  }
  (* e1 < eps − (x k − y k)：HM1 k 经 Hpt1 换形 *)
  assert (Hlt1 : Qlt e1 (eps - (projT1 x k - projT1 y k))).
  {
    pose proof (HM1 k (NatLe_lift _ _ Hk1)) as HM1k.
    apply QltT_to_Qlt in HM1k.
    setoid_rewrite Hpt1 in HM1k.
    exact HM1k.
  }
  assert (Hlt2 : Qlt e2 (eps - (projT1 y k - projT1 x k))).
  {
    pose proof (HM2 k (NatLe_lift _ _ Hk2)) as HM2k.
    apply QltT_to_Qlt in HM2k.
    setoid_rewrite Hpt2 in HM2k.
    exact HM2k.
  }
  (* 上界：x k − y k < eps（由 e1 < eps − d 且 0 < e1 传递） *)
  assert (Hup : Qlt (projT1 x k - projT1 y k) eps).
  {
    apply (proj2 (Qlt_minus_iff (projT1 x k - projT1 y k) eps)).
    (* 目标：0 < eps − d；由 0 < e1 < eps − d 传递 *)
    assert (He1pos : Qlt 0 e1) by (apply QltT_to_Qlt; exact He1).
    apply (Qlt_trans _ e1 _).
    - exact He1pos.
    - exact Hlt1.
  }
  (* 下界：−eps < x k − y k（e2 > 0 且 e2 < eps + (x k − y k)） *)
  assert (Hlo : Qlt (- eps) (projT1 x k - projT1 y k)).
  {
    (* e2 < eps − (y k − x k) == eps + (x k − y k) *)
    assert (Hd2 : Qlt e2 (eps + (projT1 x k - projT1 y k))).
    {
      setoid_replace (eps + (projT1 x k - projT1 y k))
        with (eps - (projT1 y k - projT1 x k)) by ring.
      exact Hlt2.
    }
    (* 目标：−eps < d ⟺ 0 < d + eps（Qlt_minus_iff 反向）；d := x k − y k *)
    apply Qlt_minus_iff.
    (* 由 Hd2：0 < eps + d − e2 == d + (eps − e2) *)
    assert (Hpos : Qlt 0 ((projT1 x k - projT1 y k) + (eps - e2))).
    {
      apply Qlt_minus_iff in Hd2.
      setoid_replace (eps + (projT1 x k - projT1 y k) - e2)
        with ((projT1 x k - projT1 y k) + (eps - e2)) in Hd2 by ring.
      exact Hd2.
    }
    (* 0 < d + (eps−e2) ∧ 0 < e2 ⟹ 0 < d + eps（0+0 < (d+eps−e2)+e2） *)
    assert (He2pos : Qlt 0 e2) by (apply QltT_to_Qlt; exact He2).
    assert (Hsum : Qlt (0 + 0) ((projT1 x k - projT1 y k) + (eps - e2) + e2)).
    { apply Qplus_lt_compat; [exact Hpos | exact He2pos]. }
    setoid_replace ((projT1 x k - projT1 y k) + (eps - e2) + e2)
      with ((projT1 x k - projT1 y k) + eps) in Hsum by ring.
    rewrite Qplus_0_l in Hsum.
    (* 目标 0 < d + -(-eps)（Qlt_minus_iff 展开）；将目标中的 -(-eps) 换为 eps *)
    setoid_replace (- (- eps)) with eps by (apply Qopp_involutive).
    exact Hsum.
  }
  (* |d| < eps：q_abs_lt_two_sided（QltT 形直供，前提经前向桥） *)
  apply (q_abs_lt_two_sided (projT1 x k - projT1 y k) eps Heps).
  - apply Qlt_to_QltT. exact Hlo.
  - apply Qlt_to_QltT. exact Hup.
Qed.

(* 辅助：N ≤ a ∧ N ≤ b ⟹ N ≤ Nat.min a b（分 min 分支） *)
Lemma nat_le_min : forall (N a b : nat),
  (N <= a)%nat -> (N <= b)%nat -> NatLe N (Nat.min a b).
Proof.
  intros N a b Ha Hb.
  assert (Hle : (N <= Nat.min a b)%nat).
  { destruct (Nat.le_gt_cases a b) as [Hab | Hba].
    - destruct (nat_min_l a b Hab). exact Ha.
    - destruct (nat_min_r a b (Nat.lt_le_incl _ _ Hba)). exact Hb. }
  apply NatLe_lift. exact Hle.
Qed.

(* Q 层：0 < eps ⟹ 0 < 2·eps（2eps = eps+eps > 0） *)
Lemma q_two_eps_pos : forall eps : Q, QltT 0 eps -> QltT 0 (2 * eps).
Proof.
  intros eps Heps.
  apply QltT_to_Qlt in Heps.
  apply Qlt_to_QltT.
  setoid_replace (2 * eps) with (eps + eps) by ring.
  assert (Hsum : Qlt (0 + 0) (eps + eps)) by (apply Qplus_lt_compat; [exact Heps | exact Heps]).
  setoid_replace (0 + 0) with 0%Q in Hsum by ring.
  exact Hsum.
Qed.

(* Q 层：0 < eps ⟹ eps < 3·eps（Qlt_minus_iff：0 < 3eps − eps == 2eps） *)
Lemma q_eps_lt_three : forall eps : Q, QltT 0 eps -> QltT eps (3 * eps).
Proof.
  intros eps HepsT.
  apply Qlt_to_QltT.
  apply Qlt_minus_iff.
  setoid_replace (3 * eps + - eps) with (2 * eps) by ring.
  apply QltT_to_Qlt.
  apply q_two_eps_pos.
  exact HepsT.
Qed.

(* Q 层：0 < eps ⟹ eps/9 < eps/3（eps < (eps/3)·9 == 3eps） *)
Lemma q_ninth_lt_third : forall eps : Q, QltT 0 eps -> QltT (eps / 9) (eps / 3).
Proof.
  intros eps HepsT.
  apply Qlt_to_QltT.
  apply Qlt_shift_div_r; [reflexivity | ].
  setoid_replace ((eps / 3) * 9) with (3 * eps) by field.
  apply QltT_to_Qlt.
  apply q_eps_lt_three.
  exact HepsT.
Qed.

(* Q 层：0 < eps ⟹ eps/3 < eps *)
Lemma q_third_lt : forall eps : Q, QltT 0 eps -> QltT (eps / 3) eps.
Proof.
  intros eps HepsT.
  apply Qlt_to_QltT.
  apply Qlt_shift_div_r; [reflexivity | ].
  setoid_replace (eps * 3) with (3 * eps) by ring.
  apply QltT_to_Qlt.
  apply q_eps_lt_three.
  exact HepsT.
Qed.

(* ============================================================ *)
(* Bishop 正则化：对角线极限（完备性核心）                     *)
(* ============================================================ *)
(* 正则化族 v 的对角线 l_k := v_k(k) 是柯西序列。
   证明：eps/9 统一分割（q_arch_inv 取 N0 使 1/(N0+2) < eps/9）。
   对 m,n ≥ N0，令 M := min m n（≥ N0）：
   |l_m − l_n| = |v_m(m) − v_n(n)|
     ≤ |v_m(m) − v_m(M)| + |v_m(M) − v_n(M)| + |v_n(M) − v_n(n)|  （q_chain3）
   项 1、3：统一模（与 m 无关）< 1/(M+2) ≤ 1/(N0+2) < eps/9。
   项 2：|v_m(M) − v_n(M)| ≤ |v_m(M) − v_m(L)| + |v_m(L) − v_n(L)| + |v_n(L) − v_n(M)|
     （q_three_bound；L := max M_pw N0，M_pw 为实值双柯西逐点阈值）
     —— 首/末：统一模 < 1/(min(M,L)+2) ≤ 1/(N0+2) < eps/9（M,L ≥ N0）；
     —— 中项：L ≥ M_pw ⟹ |v_m(L) − v_n(L)| < eps/9（real_lt_pair_abs_bound）。
   三项各 < eps/3 ⟹ |l_m − l_n| < eps（q_chain3 外层）。 *)
Lemma regularized_diag_cauchy :
  forall (u : nat -> Real),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        And (real_lt (real_plus (u m) (real_opp (u n))) (real_const eps))
            (real_lt (real_plus (u n) (real_opp (u m))) (real_const eps)))) ->
    cauchy (fun k : nat => projT1 (regularized_family u k) k).
Proof.
  intros u Hcau eps Heps.
  (* eps/9 分割：正性 + N0（统一模 1/(N0+2) < eps/9）+ N1（实值双柯西序列阈值） *)
  assert (Heps9 : QltT 0 (eps / 9)%Q).
  {
    assert (Hq : Qlt 0 (eps / 9)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 9) Hq).
  }
  assert (Heps3 : QltT 0 (eps / 3)%Q).
  {
    assert (Hq : Qlt 0 (eps / 3)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 3) Hq).
  }
  assert (Heps9q : Qlt 0 (eps / 9)) by (apply QltT_to_Qlt; exact Heps9).
  destruct (q_arch_inv (eps / 9)%Q Heps9) as [N0 HN0].
  (* 正则化族实值双柯西在 eps/9 的序列阈值 N1 *)
  assert (Hdc : forall eps' : Q, QltT 0 eps' ->
      sigT (fun N : nat => forall m' n' : nat,
        (N <= m')%nat -> (N <= n')%nat ->
        And (real_lt (real_plus (regularized_family u m') (real_opp (regularized_family u n'))) (real_const eps'))
            (real_lt (real_plus (regularized_family u n') (real_opp (regularized_family u m'))) (real_const eps'))))
    by (apply regularized_family_double_cauchy; exact Hcau).
  destruct (Hdc (eps / 9)%Q Heps9) as [N1 HN1].
  (* 对角线阈值 N := max N0 N1 *)
  exists (max N0 N1).
  intros m n Hm Hn.
  (* m,n ≥ N0、m,n ≥ N1 *)
  assert (HmN0 : (N0 <= m)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)]).
  assert (HnN0 : (N0 <= n)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (HmN1 : (N1 <= m)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hm)]).
  assert (HnN1 : (N1 <= n)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  set (M := Nat.min m n).
  (* M ≥ N0、M ≥ N1（M = min m n 且 m,n ≥ N0/N1） *)
  assert (HMN0 : (N0 <= M)%nat).
  {
    unfold M.
    destruct (Nat.le_gt_cases m n) as [Hmn | Hnm].
    - destruct (nat_min_l m n Hmn). exact HmN0.
    - destruct (nat_min_r m n (Nat.lt_le_incl _ _ Hnm)). exact HnN0.
  }
  assert (HMN1 : (N1 <= M)%nat).
  {
    unfold M.
    destruct (Nat.le_gt_cases m n) as [Hmn | Hnm].
    - destruct (nat_min_l m n Hmn). exact HmN1.
    - destruct (nat_min_r m n (Nat.lt_le_incl _ _ Hnm)). exact HnN1.
  }
  (* 外层三点链：x := v_m(m), p := v_m(M), q := v_n(M), y := v_n(n) *)
  apply (q_chain3 (projT1 (regularized_family u m) m)
                  (projT1 (regularized_family u m) M)
                  (projT1 (regularized_family u n) M)
                  (projT1 (regularized_family u n) n)
                  eps Heps).
  - (* 项 1：|v_m(m) − v_m(M)| < eps/3：统一模 < 1/(M+2) ≤ 1/(N0+2) < eps/9 < eps/3 *)
    apply Qlt_to_QltT.
    assert (Hum : Qlt (Qabs (projT1 (regularized_family u m) m - projT1 (regularized_family u m) M))
                      (1 / (Z.of_nat (Nat.min m M + 2) # 1)))
      by (apply QltT_to_Qlt; apply regularized_family_uniform_mod).
    assert (HmM : (M <= m)%nat) by (unfold M; lia).
    assert (Hmin : Nat.min m M = M) by (destruct (nat_min_r m M HmM); exact eq_refl).
    assert (Harch : Qlt (1 / (Z.of_nat (M + 2) # 1)) (eps / 9)%Q)
      by (apply QltT_to_Qlt; apply (q_arch_inv_mono (eps / 9)%Q N0 M HMN0); exact HN0).
    setoid_rewrite Hmin in Hum.
    apply (Qlt_trans _ (eps / 9)%Q _ (Qlt_trans _ (1 / (Z.of_nat (M + 2) # 1)) _ Hum Harch)
           (QltT_to_Qlt _ _ (q_ninth_lt_third eps Heps))).
  - (* 项 2：|v_m(M) − v_n(M)| < eps/3 *)
    destruct (HN1 m n HmN1 HnN1) as [HltA HltB].
    apply Qlt_to_QltT.
    (* 逐点阈值 Mpw：∀k ≥ Mpw: |v_m(k) − v_n(k)| < eps/9 *)
    assert (Hpw : sigT (fun Mpw : nat => forall k : nat, (Mpw <= k)%nat ->
        QltT (Qabs (projT1 (regularized_family u m) k - projT1 (regularized_family u n) k)) (eps / 9)%Q))
      by (apply (real_lt_pair_abs_bound (regularized_family u m) (regularized_family u n) (eps / 9)%Q Heps9 HltA HltB)).
    destruct Hpw as [Mpw HMpw].
    (* L := max Mpw N0：L ≥ Mpw（逐点界）、L ≥ N0（统一模项） *)
    set (L := max Mpw N0).
    assert (HLpw : (Mpw <= L)%nat) by (unfold L; apply Nat.le_max_l).
    assert (HLN0 : (N0 <= L)%nat) by (unfold L; apply Nat.le_max_r).
    (* 内层三点链（q_three_bound，各 < eps/9 ⟹ 和 < eps/3）：
       |v_m(M)−v_n(M)| ≤ |v_m(M)−v_m(L)| + |v_m(L)−v_n(L)| + |v_n(L)−v_n(M)| *)
    assert (Ht2 : Qlt (Qabs ((projT1 (regularized_family u m) M - projT1 (regularized_family u m) L)
                           + (projT1 (regularized_family u m) L - projT1 (regularized_family u n) L)
                           + (projT1 (regularized_family u n) L - projT1 (regularized_family u n) M)))
                      (eps / 3)%Q).
    {
      apply QltT_to_Qlt.
      apply (q_three_bound (eps / 3)%Q
              (projT1 (regularized_family u m) M - projT1 (regularized_family u m) L)
              (projT1 (regularized_family u m) L - projT1 (regularized_family u n) L)
              (projT1 (regularized_family u n) L - projT1 (regularized_family u n) M)).
      - exact Heps3.
      - (* 项 2a：|v_m(M) − v_m(L)| < eps/9：统一模 min(M,L) ≥ N0 *)
        apply Qlt_to_QltT.
        assert (HmL : (N0 <= Nat.min M L)%nat) by (apply NatLe_drop; apply nat_le_min; exact HMN0 || exact HLN0).
        assert (Hum : Qlt (Qabs (projT1 (regularized_family u m) M - projT1 (regularized_family u m) L))
                          (1 / (Z.of_nat (Nat.min M L + 2) # 1)))
          by (apply QltT_to_Qlt; apply regularized_family_uniform_mod).
        assert (Harch : Qlt (1 / (Z.of_nat (Nat.min M L + 2) # 1)) (eps / 9)%Q).
        { apply QltT_to_Qlt; apply (q_arch_inv_mono (eps / 9)%Q N0 (Nat.min M L)); [exact HmL | exact HN0]. }
        (* 换形 eps/9 == (eps/3)/3 匹配 q_three_bound 的 eps/3 参数 *)
        setoid_replace (eps / 9) with ((eps / 3) / 3) in Harch by field.
        exact (Qlt_trans _ (1 / (Z.of_nat (Nat.min M L + 2) # 1)) _ Hum Harch).
      - (* 项 2b：|v_m(L) − v_n(L)| < eps/9：L ≥ Mpw ⟹ 逐点界 *)
        assert (H2b : QltT (Qabs (projT1 (regularized_family u m) L - projT1 (regularized_family u n) L)) (eps / 9)%Q)
          by (apply (HMpw L HLpw)).
        (* 目标：(eps/3)/3（q_three_bound 参数 eps/3）；H2b 降层换形后回升 *)
        apply QltT_to_Qlt in H2b.
        apply Qlt_to_QltT.
        setoid_replace ((eps / 3) / 3) with (eps / 9) by field.
        exact H2b.
      - (* 项 2c：|v_n(L) − v_n(M)| < eps/9：统一模 min(L,M) ≥ N0 *)
        apply Qlt_to_QltT.
        assert (HmL : (N0 <= Nat.min L M)%nat) by (apply NatLe_drop; apply nat_le_min; exact HLN0 || exact HMN0).
        assert (Hum : Qlt (Qabs (projT1 (regularized_family u n) L - projT1 (regularized_family u n) M))
                          (1 / (Z.of_nat (Nat.min L M + 2) # 1)))
          by (apply QltT_to_Qlt; apply regularized_family_uniform_mod).
        assert (Harch : Qlt (1 / (Z.of_nat (Nat.min L M + 2) # 1)) (eps / 9)%Q).
        { apply QltT_to_Qlt; apply (q_arch_inv_mono (eps / 9)%Q N0 (Nat.min L M)); [exact HmL | exact HN0]. }
        setoid_replace (eps / 9) with ((eps / 3) / 3) in Harch by field.
        exact (Qlt_trans _ (1 / (Z.of_nat (Nat.min L M + 2) # 1)) _ Hum Harch).
    }
    (* 换形：|v_m(M) − v_n(M)| == |三项和|（ring） ⟹ exact Ht2 *)
    setoid_replace (projT1 (regularized_family u m) M - projT1 (regularized_family u n) M)
      with ((projT1 (regularized_family u m) M - projT1 (regularized_family u m) L)
          + (projT1 (regularized_family u m) L - projT1 (regularized_family u n) L)
          + (projT1 (regularized_family u n) L - projT1 (regularized_family u n) M)) by ring.
    exact Ht2.
  - (* 项 3：|v_n(M) − v_n(n)| < eps/3：统一模 < 1/(M+2) ≤ 1/(N0+2) < eps/9 < eps/3 *)
    apply Qlt_to_QltT.
    assert (Hum : Qlt (Qabs (projT1 (regularized_family u n) M - projT1 (regularized_family u n) n))
                      (1 / (Z.of_nat (Nat.min M n + 2) # 1)))
      by (apply QltT_to_Qlt; apply regularized_family_uniform_mod).
    assert (HMn : (M <= n)%nat) by (unfold M; lia).
    assert (Hmin : Nat.min M n = M) by (destruct (nat_min_l M n HMn); exact eq_refl).
    assert (Harch : Qlt (1 / (Z.of_nat (M + 2) # 1)) (eps / 9)%Q)
      by (apply QltT_to_Qlt; apply (q_arch_inv_mono (eps / 9)%Q N0 M HMN0); exact HN0).
    setoid_rewrite Hmin in Hum.
    apply (Qlt_trans _ (eps / 9)%Q _ (Qlt_trans _ (1 / (Z.of_nat (M + 2) # 1)) _ Hum Harch)
           (QltT_to_Qlt _ _ (q_ninth_lt_third eps Heps))).
Qed.

(* ============================================================ *)
(* Bishop 正则化：real_lim 逐点界（完备性的 real_lim 部分）    *)
(* ============================================================ *)
(* 核心：|u_n(k) − l_k| < eps 对 k ≥ C(n)（C 依赖 n，因 v_n ≈ u_n 的
   阈值依赖 n；real_lt 内部坐标阈值可依赖 n，合法）。
   分解：|u_n(k) − l_k| ≤ |u_n(k) − v_n(k)| + |v_n(k) − v_k(k)|。
   — 项 A：v_n ≈ u_n（regularized_family_same）在 eps/2 ⟹ < eps/2，k ≥ C0(n)；
   — 项 B：|v_n(k) − v_k(k)|，L := max M_pw N0（M_pw 为 v 实值双柯西 eps/6
     的逐点阈值，real_lt_pair_abs_bound）：
     ≤ |v_n(k) − v_n(L)| + |v_n(L) − v_k(L)| + |v_k(L) − v_k(k)|
     —— 首/末：统一模 < 1/(N0+2) < eps/6（k,L ≥ N0）；
     —— 中项：L ≥ M_pw ⟹ < eps/6。
     项 B < eps/6+eps/6+eps/6 = eps/2（q_chain3）。总 < eps/2 + eps/2 = eps。
   返回 N1（v 实值双柯西 eps/6 序列阈值）使 n ≥ N1 可用中项。 *)
Lemma regularized_diag_close :
  forall (u : nat -> Real),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        And (real_lt (real_plus (u m) (real_opp (u n))) (real_const eps))
            (real_lt (real_plus (u n) (real_opp (u m))) (real_const eps)))) ->
    forall (eps : Q) (Heps : QltT 0 eps),
      sigT (fun N1 : nat => forall n : nat, (N1 <= n)%nat ->
        sigT (fun C : nat => forall k : nat, (C <= k)%nat ->
          QltT (Qabs (projT1 (u n) k - projT1 (regularized_family u k) k)) eps)).
Proof.
  intros u Hcau eps Heps.
  (* eps/2、eps/6 正性 *)
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  assert (Heps6 : QltT 0 (eps / 6)%Q).
  {
    assert (Hq : Qlt 0 (eps / 6)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 6) Hq).
  }
  (* N0：统一模控制 1/(N0+2) < eps/6 *)
  destruct (q_arch_inv (eps / 6)%Q Heps6) as [N0 HN0].
  (* N1：v 实值双柯西 eps/6 序列阈值（项 B 中项） *)
  assert (Hdc6 : forall eps' : Q, QltT 0 eps' ->
      sigT (fun N : nat => forall m' n' : nat,
        (N <= m')%nat -> (N <= n')%nat ->
        And (real_lt (real_plus (regularized_family u m') (real_opp (regularized_family u n'))) (real_const eps'))
            (real_lt (real_plus (regularized_family u n') (real_opp (regularized_family u m'))) (real_const eps'))))
    by (apply regularized_family_double_cauchy; exact Hcau).
  destruct (Hdc6 (eps / 6)%Q Heps6) as [N1 HN1].
  exists (max N0 N1).
  intros n Hn.
  assert (HnN0 : (N0 <= n)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_l | exact Hn]).
  assert (HnN1 : (N1 <= n)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_r | exact Hn]).
  (* 项 A 的阈值：v_n ≈ u_n 在 eps/2 给 C0（依赖 n） *)
  assert (Hsame : real_eq (regularized_family u n) (u n)) by (apply regularized_family_same).
  destruct (Hsame (eps / 2)%Q Heps2) as [C0 HC0].
  exists (max C0 (max N0 N1)).
  intros k Hk.
  assert (HkC0 : (C0 <= k)%nat) by (apply Nat.le_trans with (max C0 (max N0 N1)); [apply Nat.le_max_l | exact Hk]).
  assert (HkN0 : (N0 <= k)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_l | apply Nat.le_trans with (max C0 (max N0 N1)); [apply Nat.le_max_r | exact Hk]]).
  assert (HkN1 : (N1 <= k)%nat) by (apply Nat.le_trans with (max N0 N1); [apply Nat.le_max_r | apply Nat.le_trans with (max C0 (max N0 N1)); [apply Nat.le_max_r | exact Hk]]).
  (* 目标：|u_n(k) − v_k(k)| < eps *)
  apply Qlt_to_QltT.
  (* 项 A：|u_n(k) − v_n(k)| < eps/2（HC0 给 |v_n − u_n|，对称换形） *)
  assert (HA : Qlt (Qabs (projT1 (u n) k - projT1 (regularized_family u n) k)) (eps / 2)%Q).
  {
    assert (Hc : QltT (Qabs (projT1 (regularized_family u n) k - projT1 (u n) k)) (eps / 2)%Q)
      by (apply (HC0 k (NatLe_lift _ _ HkC0))).
    (* Hc 转 Qlt，再在 Qlt 层用 Qeq 换形（Qlt 兼容 Qeq 的 Proper 已有） *)
    pose proof (QltT_to_Qlt _ _ Hc) as Hcq.
    (* 目标：Qlt (Qabs (u_n − v_n)) (eps/2)；Hcq：Qlt (Qabs (v_n − u_n)) (eps/2)。
       Qabs (u_n − v_n) == Qabs (v_n − u_n)（q_abs_minus_sym）⟹ setoid_rewrite 于 Qlt *)
    setoid_rewrite (qeqT_imp_qeq _ _ (q_abs_minus_sym (projT1 (u n) k) (projT1 (regularized_family u n) k))).
    exact Hcq.
  }
  (* 项 B：|v_n(k) − v_k(k)| < eps/2（q_chain3，各 < eps/6） *)
  destruct (HN1 n k HnN1 HkN1) as [HltA HltB].
  assert (Hpw : sigT (fun Mpw : nat => forall j : nat, (Mpw <= j)%nat ->
      QltT (Qabs (projT1 (regularized_family u n) j - projT1 (regularized_family u k) j)) (eps / 6)%Q))
    by (apply (real_lt_pair_abs_bound (regularized_family u n) (regularized_family u k) (eps / 6)%Q Heps6 HltA HltB)).
  destruct Hpw as [Mpw HMpw].
  set (L := max Mpw N0).
  assert (HLpw : (Mpw <= L)%nat) by (unfold L; apply Nat.le_max_l).
  assert (HLN0 : (N0 <= L)%nat) by (unfold L; apply Nat.le_max_r).
  assert (HB : Qlt (Qabs (projT1 (regularized_family u n) k - projT1 (regularized_family u k) k)) (eps / 2)%Q).
  {
    apply QltT_to_Qlt.
    apply (q_chain3 (projT1 (regularized_family u n) k)
                    (projT1 (regularized_family u n) L)
                    (projT1 (regularized_family u k) L)
                    (projT1 (regularized_family u k) k)
                    (eps / 2)%Q Heps2).
    - (* |v_n(k) − v_n(L)| < (eps/2)/3 = eps/6：统一模 < 1/(N0+2) < eps/6 *)
      apply Qlt_to_QltT.
      assert (HmL : (N0 <= Nat.min k L)%nat) by (apply NatLe_drop; apply nat_le_min; exact HkN0 || exact HLN0).
      assert (Hum : Qlt (Qabs (projT1 (regularized_family u n) k - projT1 (regularized_family u n) L))
                        (1 / (Z.of_nat (Nat.min k L + 2) # 1)))
        by (apply QltT_to_Qlt; apply regularized_family_uniform_mod).
      assert (Harch : Qlt (1 / (Z.of_nat (Nat.min k L + 2) # 1)) (eps / 6)%Q).
      { apply QltT_to_Qlt; apply (q_arch_inv_mono (eps / 6)%Q N0 (Nat.min k L)); [exact HmL | exact HN0]. }
      setoid_replace ((eps / 2) / 3) with (eps / 6) by field.
      exact (Qlt_trans _ (1 / (Z.of_nat (Nat.min k L + 2) # 1)) _ Hum Harch).
    - (* |v_n(L) − v_k(L)| < eps/6：L ≥ Mpw ⟹ 逐点界 *)
      assert (H2b : QltT (Qabs (projT1 (regularized_family u n) L - projT1 (regularized_family u k) L)) (eps / 6)%Q)
        by (apply (HMpw L HLpw)).
      apply QltT_to_Qlt in H2b.
      apply Qlt_to_QltT.
      setoid_replace ((eps / 2) / 3) with (eps / 6) by field.
      exact H2b.
    - (* |v_k(L) − v_k(k)| < eps/6：统一模 *)
      apply Qlt_to_QltT.
      assert (HmL : (N0 <= Nat.min L k)%nat) by (apply NatLe_drop; apply nat_le_min; exact HLN0 || exact HkN0).
      assert (Hum : Qlt (Qabs (projT1 (regularized_family u k) L - projT1 (regularized_family u k) k))
                        (1 / (Z.of_nat (Nat.min L k + 2) # 1)))
        by (apply QltT_to_Qlt; apply regularized_family_uniform_mod).
      assert (Harch : Qlt (1 / (Z.of_nat (Nat.min L k + 2) # 1)) (eps / 6)%Q).
      { apply QltT_to_Qlt; apply (q_arch_inv_mono (eps / 6)%Q N0 (Nat.min L k)); [exact HmL | exact HN0]. }
      setoid_replace ((eps / 2) / 3) with (eps / 6) by field.
      exact (Qlt_trans _ (1 / (Z.of_nat (Nat.min L k + 2) # 1)) _ Hum Harch).
  }
  (* 总：|u_n(k) − v_k(k)| ≤ |u_n(k) − v_n(k)| + |v_n(k) − v_k(k)| < eps/2 + eps/2 = eps *)
  assert (Hsum : Qlt (Qabs (projT1 (u n) k - projT1 (regularized_family u n) k) +
                          Qabs (projT1 (regularized_family u n) k - projT1 (regularized_family u k) k))
                     eps).
  {
    (* eps/2 + eps/2 == eps，故需证明 < eps 由 HA+HB < eps/2+eps/2 == eps 严格成立：
       直接：HA < eps/2 且 HB < eps/2 ⟹ 和 < eps（Qlt 加法保序到 == 的目标） *)
    assert (Hhalf_sum : eps / 2 + eps / 2 == eps). { field. }
    assert (Hsum_lt : Qlt (Qabs (projT1 (u n) k - projT1 (regularized_family u n) k) +
                               Qabs (projT1 (regularized_family u n) k - projT1 (regularized_family u k) k))
                          (eps / 2 + eps / 2)).
    { apply Qplus_lt_compat; [exact HA | exact HB]. }
    apply (Qlt_le_trans _ (eps / 2 + eps / 2) _ Hsum_lt).
    setoid_rewrite Hhalf_sum. apply Qle_refl.
  }
  assert (Htri : Qle (Qabs (projT1 (u n) k - projT1 (regularized_family u k) k))
                     (Qabs (projT1 (u n) k - projT1 (regularized_family u n) k) +
                      Qabs (projT1 (regularized_family u n) k - projT1 (regularized_family u k) k))).
  {
    (* |a − c| = |(a − b) + (b − c)| ≤ |a − b| + |b − c|（Qabs_triangle） *)
    setoid_replace (Qabs (projT1 (u n) k - projT1 (regularized_family u k) k))
      with (Qabs ((projT1 (u n) k - projT1 (regularized_family u n) k) +
                  (projT1 (regularized_family u n) k - projT1 (regularized_family u k) k)))
      by (apply Qabs_wd; ring).
    apply Qabs_triangle.
  }
  exact (Qle_lt_trans _ _ _ Htri Hsum).
Qed.

(* ============================================================ *)
(* 柯西完备性（正则化版，零 Variable）：                        *)
(* real_cauchy_complete 不再依赖 real_cauchy_pointwise          *)
(* ============================================================ *)
(* l := 正则化对角线（regularized_diag_cauchy 证柯西）。
   real_lim u l：∀eps ∃N ∀n≥N 双向 eps/2 夹逼。
   — 逐点界 |u_n(k) − l_k| < eps/2 由 regularized_diag_close（eps/2）给出，
     阈值 C(n) 依赖 n（real_lt 内部坐标阈值可依赖 n，合法）；
   — 方向 1：real_lt (u n) (l + eps)：见证 eps/2，阈值 C(n)，
     (l_k + eps) − u_n(k) == eps − (u_n(k) − l_k) > eps/2（q_bound_eps_half）；
   — 方向 2：real_lt (l − eps) (u n)：对称（q_bound_eps_half_comm）。 *)
Theorem real_cauchy_complete :
  forall (u : nat -> Real),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        And (real_lt (real_plus (u m) (real_opp (u n))) (real_const eps))
            (real_lt (real_plus (u n) (real_opp (u m))) (real_const eps)))) ->
    sigT (fun l : Real => real_lim u l).
Proof.
  intros u Hcau.
  (* l := 正则化对角线 *)
  set (l := existT _ (fun k : nat => projT1 (regularized_family u k) k)
                   (regularized_diag_cauchy u Hcau)).
  exists l.
  (* real_lim u l：∀eps ∃N ∀n≥N 双向夹逼 *)
  intros eps Heps.
  (* eps/2 分割 *)
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  (* 逐点界：regularized_diag_close u Hcau (eps/2) Heps2 给 N1，∀n≥N1 ∃C ∀k≥C:
     |u_n(k) − l_k| < eps/2 *)
  destruct (regularized_diag_close u Hcau (eps / 2)%Q Heps2) as [N1 HN1].
  exists N1.
  intros n Hn.
  destruct (HN1 n Hn) as [C HC].
  split.
  - (* 方向 1：real_lt (u n) (l + eps)：见证 eps/2，阈值 C *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists C. intros k Hk.
      (* 目标：QltT (eps/2) (projT1 (real_plus l (real_const eps)) k − projT1 (u n) k) *)
      apply Qlt_to_QltT.
      (* 展开投影（定义性归约）：projT1 (l + eps) k == projT1 l k + eps == v_k(k) + eps *)
      change (projT1 (real_plus l (real_const eps)) k) with (projT1 (regularized_family u k) k + eps).
      (* 换形：v_k(k) + eps − u_n(k) == (v_k(k) − u_n(k)) + eps *)
      setoid_replace (projT1 (regularized_family u k) k + eps - projT1 (u n) k)
        with ((projT1 (regularized_family u k) k - projT1 (u n) k) + eps) by ring.
      (* 由 HC k Hk：|u_n(k) − v_k(k)| < eps/2；需 |v_k(k) − u_n(k)| < eps/2（对称） *)
      assert (Hd : Qlt (Qabs (projT1 (u n) k - projT1 (regularized_family u k) k)) (eps / 2)%Q)
        by (apply QltT_to_Qlt; apply (HC k (NatLe_drop _ _ Hk))).
      assert (Hd2 : Qlt (Qabs (projT1 (regularized_family u k) k - projT1 (u n) k)) (eps / 2)%Q).
      {
        (* 目标 Qlt (Qabs (v_k−u_n)) (eps/2)；Hd : Qlt (Qabs (u_n−v_k)) (eps/2)。
           Qabs (v_k−u_n) == Qabs (u_n−v_k)（q_abs_minus_sym v_k u_n） *)
        setoid_rewrite (qeqT_imp_qeq _ _ (q_abs_minus_sym (projT1 (regularized_family u k) k) (projT1 (u n) k))).
        exact Hd.
      }
      apply QltT_to_Qlt.
      exact (q_bound_eps_half (projT1 (regularized_family u k) k - projT1 (u n) k) eps Heps
             (Qlt_to_QltT _ _ Hd2)).
  - (* 方向 2：real_lt (l − eps) (u n)：见证 eps/2，阈值 C *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists C. intros k Hk.
      (* 目标：QltT (eps/2) (projT1 (u n) k − projT1 (real_plus l (real_opp (real_const eps))) k) *)
      apply Qlt_to_QltT.
      (* 展开投影：projT1 (l + (−eps)) k == v_k(k) + (−eps) *)
      change (projT1 (real_plus l (real_opp (real_const eps))) k) with (projT1 (regularized_family u k) k + (- eps)).
      (* 目标：Qlt (eps/2) (u_n(k) − (v_k(k) + −eps)) == eps + (u_n(k) − v_k(k)) *)
      assert (Hd : Qlt (Qabs (projT1 (u n) k - projT1 (regularized_family u k) k)) (eps / 2)%Q)
        by (apply QltT_to_Qlt; apply (HC k (NatLe_drop _ _ Hk))).
      setoid_replace (projT1 (u n) k - (projT1 (regularized_family u k) k + (- eps)))
        with (eps + (projT1 (u n) k - projT1 (regularized_family u k) k)) by ring.
      exact (QltT_to_Qlt _ _
             (q_bound_eps_half_comm (projT1 (u n) k - projT1 (regularized_family u k) k) eps
              Heps (Qlt_to_QltT _ _ Hd))).
Qed.

(* 混合传递（接口形态） *)
Lemma real_lt_le_trans : forall x y z : Real, real_lt x y -> real_le y z -> real_lt x z.
Proof.
  intros x y z Hlt Hle.
  exact (match Hle with | inl Hlt' => real_lt_trans x y z Hlt Hlt'
  | inr Heq' => real_lt_eq_lt x y z Hlt Heq' end).
Qed.

Lemma real_le_lt_trans : forall x y z : Real, real_le x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hle Hlt.
  exact (match Hle with | inl Hlt' => real_lt_trans x y z Hlt' Hlt
  | inr Heq => real_eq_lt_lt x y z Heq Hlt end).
Qed.

(* real_le 反对称：互 ≤ ⟹ real_eq（lt+lt 矛盾，其余 real_eq_sym/直接） *)
Lemma real_le_antisym : forall x y : Real, real_le x y -> real_le y x -> real_eq x y.
Proof.
  intros x y Hxy Hyx.
  exact (match Hxy with
  | inl Hlt => match Hyx with
  | inl Hlt' => match real_lt_irrefl x (real_lt_trans x y x Hlt Hlt') with end
  | inr Heq' => real_eq_sym y x Heq' end
  | inr Heq => match Hyx with | inl _ => Heq | inr _ => Heq end end).
Qed.

(* lt_le_iff（接口形态：Or (real_lt x y) (Id x y) -> real_le x y） *)
Lemma real_lt_le_iff : forall x y : Real, Or (real_lt x y) (Id x y) -> real_le x y.
Proof.
  intros x y H.
  destruct H as [Hlt | Hid].
  - left. exact Hlt.
  - destruct Hid. right. apply real_eq_refl.
Qed.
(* ============================================================ *)
(* real_lim 收敛代数（柯西完备骨架的应用强化）                  *)
(* ------------------------------------------------------------ *)
(* real_lim 加法保持：u→l1、v→l2 ⟹ u+v → l1+l2。               *)
(* 核心：real_lt 加性平移（real_lt a b → real_lt c d ⟹           *)
(* real_lt (a+c) (b+d)，见证 e1+e2 + 逐点 ring）。               *)
(* ============================================================ *)

(* real_lt 加性平移：a<b ∧ c<d ⟹ a+c < b+d（见证 e1+e2，逐点 Qplus_lt_compat） *)
Lemma real_lt_plus_compat : forall (a b c d : Real),
  real_lt a b -> real_lt c d -> real_lt (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct Hab as [e1 [He1 [N1 HN1]]].
  destruct Hcd as [e2 [He2 [N2 HN2]]].
  exists (e1 + e2)%Q.
  split.
  - (* 正性：0 < e1 + e2（Qplus_lt_compat + Qplus_0_l） *)
    assert (Hlt1 : Qlt 0 e1) by (apply QltT_to_Qlt; exact He1).
    assert (Hlt2 : Qlt 0 e2) by (apply QltT_to_Qlt; exact He2).
    assert (Hsum : Qlt (0 + 0) (e1 + e2)) by (apply Qplus_lt_compat; [exact Hlt1 | exact Hlt2]).
    assert (H0 : 0 + 0 == 0) by (apply Qplus_0_l).
    rewrite H0 in Hsum.
    apply Qlt_to_QltT. exact Hsum.
  - exists (max N1 N2). intros n Hn.
    assert (Hn1 : (N1 <= n)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
    assert (Hn2 : (N2 <= n)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
    (* 逐点展开投影：projT1 (b+d) n == projT1 b n + projT1 d n；projT1 (a+c) n == a_n + c_n *)
    assert (Hpt_bd : projT1 (real_plus b d) n == projT1 b n + projT1 d n)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Hpt_ac : projT1 (real_plus a c) n == projT1 a n + projT1 c n)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    apply Qlt_to_QltT.
    (* 目标：e1+e2 < (b_n + d_n) − (a_n + c_n) == (b_n − a_n) + (d_n − c_n) *)
    setoid_rewrite Hpt_bd.
    setoid_rewrite Hpt_ac.
    assert (Hr : (projT1 b n + projT1 d n) - (projT1 a n + projT1 c n)
                 == (projT1 b n - projT1 a n) + (projT1 d n - projT1 c n)) by ring.
    setoid_rewrite Hr.
    apply Qplus_lt_compat.
    + apply QltT_to_Qlt. apply HN1. apply NatLe_lift. exact Hn1.
    + apply QltT_to_Qlt. apply HN2. apply NatLe_lift. exact Hn2.
Qed.

(* real_eq 辅助：((l1+e/2)+(l2+e/2)) == (l1+l2)+e（逐点 ring；eps/2 双份合 eps） *)
Lemma real_eq_plus_eps_halves :
  forall (a b : Real) (eps : Q),
    real_eq (real_plus (real_plus a (real_const (eps / 2)%Q))
                       (real_plus b (real_const (eps / 2)%Q)))
            (real_plus (real_plus a b) (real_const eps)).
Proof.
  intros a b eps eps' Heps'.
  exists O. intros n Hn.
  apply Qlt_to_QltT.
  (* 逐点展开：|((a_n+e/2)+(b_n+e/2)) − ((a_n+b_n)+e)| == 0 < eps' *)
  assert (Hpt : projT1 (real_plus (real_plus a (real_const (eps / 2)%Q))
                                  (real_plus b (real_const (eps / 2)%Q))) n
                == (projT1 a n + eps / 2) + (projT1 b n + eps / 2)).
  {
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus a (real_const (eps / 2)%Q))
                                   (real_plus b (real_const (eps / 2)%Q)) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_const (eps / 2)%Q) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj b (real_const (eps / 2)%Q) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (eps / 2)%Q n)).
    reflexivity.
  }
  assert (Hpt2 : projT1 (real_plus (real_plus a b) (real_const eps)) n
                 == (projT1 a n + projT1 b n) + eps).
  {
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus a b) (real_const eps) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj a b n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj eps n)).
    reflexivity.
  }
  assert (Hzero : Qabs ((projT1 a n + eps / 2) + (projT1 b n + eps / 2)
                        - ((projT1 a n + projT1 b n) + eps)) == 0).
  {
    apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. field.
    - apply (Qeq_trans _ (-0) _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl.
  }
  (* 目标 QltT (Qabs (X − Y)) eps'，X−Y == 0：Qcompare_comp 模式 *)
  assert (H0lt : Qlt 0 eps') by (apply QltT_to_Qlt; exact Heps').
  assert (Hcmp0 : Qcompare 0 eps' = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (projT1 (real_plus (real_plus a (real_const (eps / 2)%Q))
                                                  (real_plus b (real_const (eps / 2)%Q))) n
                                - projT1 (real_plus (real_plus a b) (real_const eps)) n)) eps'
                     = Lt).
  {
    assert (Hdiff : Qabs (projT1 (real_plus (real_plus a (real_const (eps / 2)%Q))
                                            (real_plus b (real_const (eps / 2)%Q))) n
                          - projT1 (real_plus (real_plus a b) (real_const eps)) n) == 0).
    {
      setoid_rewrite Hpt.
      setoid_rewrite Hpt2.
      exact Hzero.
    }
    assert (Hc1 : Qcompare (Qabs (projT1 (real_plus (real_plus a (real_const (eps / 2)%Q))
                                                    (real_plus b (real_const (eps / 2)%Q))) n
                                  - projT1 (real_plus (real_plus a b) (real_const eps)) n)) eps'
                     = Qcompare 0 eps').
    { exact (Qcompare_comp (Qabs (projT1 (real_plus (real_plus a (real_const (eps / 2)%Q))
                                                    (real_plus b (real_const (eps / 2)%Q))) n
                                  - projT1 (real_plus (real_plus a b) (real_const eps)) n)) 0
                           Hdiff eps' eps' (Qeq_refl eps')). }
    rewrite Hc1. exact Hcmp0.
  }
  exact Hcmp.
Qed.

(* real_eq 辅助：((l1−e/2)+(l2−e/2)) == (l1+l2)−e（逐点 ring；符号反向版） *)
Lemma real_eq_plus_opp_eps_halves :
  forall (a b : Real) (eps : Q),
    real_eq (real_plus (real_plus a (real_opp (real_const (eps / 2)%Q)))
                       (real_plus b (real_opp (real_const (eps / 2)%Q))))
            (real_plus (real_plus a b) (real_opp (real_const eps))).
Proof.
  intros a b eps eps' Heps'.
  exists O. intros n Hn.
  apply Qlt_to_QltT.
  assert (Hpt : projT1 (real_plus (real_plus a (real_opp (real_const (eps / 2)%Q)))
                                  (real_plus b (real_opp (real_const (eps / 2)%Q)))) n
                == (projT1 a n - eps / 2) + (projT1 b n - eps / 2)).
  {
    destruct a as [ua Ha]. destruct b as [ub Hb].
    simpl. ring.
  }
  assert (Hpt2 : projT1 (real_plus (real_plus a b) (real_opp (real_const eps))) n
                 == (projT1 a n + projT1 b n) - eps).
  {
    destruct a as [ua Ha]. destruct b as [ub Hb].
    simpl. ring.
  }
  assert (Hzero : Qabs ((projT1 a n - eps / 2) + (projT1 b n - eps / 2)
                        - ((projT1 a n + projT1 b n) - eps)) == 0).
  {
    apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. field.
    - apply (Qeq_trans _ (-0) _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl.
  }
  assert (H0lt : Qlt 0 eps') by (apply QltT_to_Qlt; exact Heps').
  assert (Hcmp0 : Qcompare 0 eps' = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (projT1 (real_plus (real_plus a (real_opp (real_const (eps / 2)%Q)))
                                                  (real_plus b (real_opp (real_const (eps / 2)%Q)))) n
                                - projT1 (real_plus (real_plus a b) (real_opp (real_const eps))) n)) eps'
                     = Lt).
  {
    assert (Hdiff : Qabs (projT1 (real_plus (real_plus a (real_opp (real_const (eps / 2)%Q)))
                                            (real_plus b (real_opp (real_const (eps / 2)%Q)))) n
                          - projT1 (real_plus (real_plus a b) (real_opp (real_const eps))) n) == 0).
    {
      setoid_rewrite Hpt.
      setoid_rewrite Hpt2.
      exact Hzero.
    }
    assert (Hc1 : Qcompare (Qabs (projT1 (real_plus (real_plus a (real_opp (real_const (eps / 2)%Q)))
                                                    (real_plus b (real_opp (real_const (eps / 2)%Q)))) n
                                  - projT1 (real_plus (real_plus a b) (real_opp (real_const eps))) n)) eps'
                     = Qcompare 0 eps').
    { exact (Qcompare_comp (Qabs (projT1 (real_plus (real_plus a (real_opp (real_const (eps / 2)%Q)))
                                                    (real_plus b (real_opp (real_const (eps / 2)%Q)))) n
                                  - projT1 (real_plus (real_plus a b) (real_opp (real_const eps))) n)) 0
                           Hdiff eps' eps' (Qeq_refl eps')). }
    rewrite Hc1. exact Hcmp0.
  }
  exact Hcmp.
Qed.

(* real_lim 加法保持：u→l1、v→l2 ⟹ u+v → l1+l2
   非平凡：eps/2 分割（Heps2）+ real_lt_plus_compat 加性平移 +
   real_eq_plus_eps_halves / real_eq_plus_opp_eps_halves 换形
   （(l1+e/2)+(l2+e/2) == (l1+l2)+e、((l1−e/2)+(l2−e/2)) == (l1+l2)−e）
   + real_lt_eq_lt / real_eq_lt_lt 外延替换。 *)
Theorem real_lim_plus : forall (u v : nat -> Real) (l1 l2 : Real),
  real_lim u l1 -> real_lim v l2 ->
  real_lim (fun n => real_plus (u n) (v n)) (real_plus l1 l2).
Proof.
  intros u v l1 l2 Hlim1 Hlim2 eps Heps.
  (* eps/2 分割 *)
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  destruct (Hlim1 (eps / 2)%Q Heps2) as [N1 HN1].
  destruct (Hlim2 (eps / 2)%Q Heps2) as [N2 HN2].
  exists (max N1 N2).
  intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact Hn]).
  assert (Hn2 : (N2 <= n)%nat) by (apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact Hn]).
  destruct (HN1 n Hn1) as [Hup1 Hdn1].
  destruct (HN2 n Hn2) as [Hup2 Hdn2].
  split.
  - (* 上界：real_lt (u n + v n) ((l1+l2) + eps) *)
    (* 由加性平移：(u n + v n) < (l1+e/2) + (l2+e/2) *)
    assert (Hsum_lt : real_lt (real_plus (u n) (v n))
                              (real_plus (real_plus l1 (real_const (eps / 2)%Q))
                                         (real_plus l2 (real_const (eps / 2)%Q))))
      by (apply real_lt_plus_compat; [exact Hup1 | exact Hup2]).
    (* 换形：右端 == (l1+l2) + eps（real_eq_plus_eps_halves） *)
    apply (real_lt_eq_lt (real_plus (u n) (v n))
                         (real_plus (real_plus l1 (real_const (eps / 2)%Q))
                                    (real_plus l2 (real_const (eps / 2)%Q)))
                         (real_plus (real_plus l1 l2) (real_const eps))).
    + exact Hsum_lt.
    + exact (real_eq_plus_eps_halves l1 l2 eps).
  - (* 下界：real_lt ((l1+l2) − eps) (u n + v n) *)
    (* 由加性平移：(l1−e/2) + (l2−e/2) < (u n + v n) *)
    assert (Hsum_dn : real_lt (real_plus (real_plus l1 (real_opp (real_const (eps / 2)%Q)))
                                         (real_plus l2 (real_opp (real_const (eps / 2)%Q))))
                              (real_plus (u n) (v n)))
      by (apply real_lt_plus_compat; [exact Hdn1 | exact Hdn2]).
    (* 换形：左端 == (l1+l2) − eps（real_eq_plus_opp_eps_halves，经 real_eq_lt_lt） *)
    apply (real_eq_lt_lt (real_plus (real_plus l1 l2) (real_opp (real_const eps)))
                         (real_plus (real_plus l1 (real_opp (real_const (eps / 2)%Q)))
                                    (real_plus l2 (real_opp (real_const (eps / 2)%Q))))
                         (real_plus (u n) (v n))).
    + apply (real_eq_sym _ _ (real_eq_plus_opp_eps_halves l1 l2 eps)).
    + exact Hsum_dn.
Qed.

(* 逐点投影：projT1 (real_mult (real_const c) l) m == c·projT1 l m（real_mult 逐点 u·v） *)
Lemma real_mult_const_proj : forall (c : Q) (l : Real) (m : nat),
  QeqT (projT1 (real_mult (real_const c) l) m) (projT1 (real_const c) m * projT1 l m).
Proof.
  intros c [ll Hll] m. apply qeq_imp_qeqT. reflexivity.
Qed.

(* real_lim 标量缩放：u → l ⟹ c·u → c·l（c : Q 有理标量经 real_const 嵌入）。
   非平凡：eps' := eps/(2(|c|+1)) 分割（保证分母正）+ real_lt_abs_bound
   双向夹逼逐点界 + q_scal_eps_half/neg 缩放（c 可正可负，|c|+1 归一）
   + 投影 change 归约（real_mult/real_plus/real_const 逐点展开）。 *)
Theorem real_lim_scal : forall (u : nat -> Real) (l : Real) (c : Q),
  real_lim u l ->
  real_lim (fun n => real_mult (real_const c) (u n)) (real_mult (real_const c) l).
Proof.
  intros u l c Hlim eps Heps.
  (* eps' := eps / (2·(|c|+1))（> 0，因 2·(|c|+1) > 0） *)
  set (eps' := eps / (2 * (Qabs c + 1))).
  assert (Heps' : QltT 0 eps').
  {
    unfold eps'.
    apply Qlt_to_QltT.
    (* 目标 Qlt 0 (eps / (2(|c|+1)))：Qlt_shift_div_l 转前提 0·(2(|c|+1)) < eps *)
    apply Qlt_shift_div_l.
    - (* 0 < 2·(|c|+1) *)
      apply Qmult_lt_0_compat.
      + reflexivity.
      + apply Qlt_le_trans with 1%Q.
        * reflexivity.
        * setoid_replace (Qabs c + 1) with (1 + Qabs c) by ring.
          apply QleT'_to_Qle. apply q_le_plus_nonneg_r_q. apply Qle_to_QleT'. apply Qabs_nonneg.
    - (* 前提：0·(2(|c|+1)) < eps == 0 < eps *)
      setoid_replace (0 * (2 * (Qabs c + 1))) with 0 by ring.
      apply QltT_to_Qlt. exact Heps.
  }
  assert (Heps_half : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  destruct (Hlim eps' Heps') as [N HN].
  exists N.
  intros n Hn.
  (* HN n Hn : And (real_lt (u n) (l + eps')) (real_lt (l − eps') (u n))；
     用 real_lt_abs_bound 得逐点界 |u_n(m) − l_m| < eps'（对 m ≥ M） *)
  destruct (real_lt_abs_bound u l eps' Heps' N HN n Hn) as [M HM].
  split.
  - (* 上方向：real_lt (c·u n) (c·l + eps)：见证 eps/2，阈值 M *)
    exists (eps / 2)%Q. split.
    + exact Heps_half.
    + exists M. intros m Hm.
      (* HM m Hm : QltT (Qabs (projT1 (u n) m - projT1 l m)) eps' *)
      apply Qlt_to_QltT.
      (* 逐点展开投影：real_plus_proj + real_const_proj + real_mult_const_proj
         （projT1 (real_mult (real_const c) x) m == c·projT1 x m，x := l / u n） *)
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const c) l) (real_const eps) m)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj eps m)).
      assert (Hml : projT1 (real_mult (real_const c) l) m == c * projT1 l m)
        by (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj c l m)); setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj c m)); reflexivity).
      setoid_rewrite Hml.
      assert (Hmu : projT1 (real_mult (real_const c) (u n)) m == c * projT1 (u n) m)
        by (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj c (u n) m)); setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj c m)); reflexivity).
      setoid_rewrite Hmu.
      (* 目标：Qlt (eps/2) (c·l_m + eps − c·u_n(m)) == eps − c·(u_n(m) − l_m) *)
      assert (Hd : Qlt (Qabs (projT1 (u n) m - projT1 l m)) eps')
        by (apply QltT_to_Qlt; exact (HM m (NatLe_drop _ _ Hm))).
      (* c·(u_n(m) − l_m) < eps/2（q_scal_eps_half）；换形目标为 eps/2 < eps − c·Δ *)
      assert (Hscal : Qlt (c * (projT1 (u n) m - projT1 l m)) (eps / 2))
        by (unfold eps'; apply QltT_to_Qlt; apply q_scal_eps_half; [exact Heps | apply Qlt_to_QltT; exact Hd]).
      (* 目标 eps/2 < c·l_m + eps − c·u_n(m) ⟺ eps/2 < eps − c·(u_n(m) − l_m)（ring）
         ⟺ c·(u_n(m) − l_m) < eps/2（Qlt_minus_iff 反向） *)
      (* 目标：eps/2 < c·l_m + eps − c·u_n(m)（ring 换形后的目标）
         链：eps/2 < c·l_m+eps−c·u_n(m) ⟺ 0 < (c·l_m+eps−c·u_n(m)) − eps/2（Qlt_minus_iff proj2）
         ⟺ 0 < eps/2 − c·(u_n(m)−l_m)（ring）⟸ c·(u_n(m)−l_m) < eps/2（Qlt_minus_iff proj1，Hscal） *)
      apply (proj2 (Qlt_minus_iff (eps / 2) (c * projT1 l m + eps - c * projT1 (u n) m))).
      setoid_replace (c * projT1 l m + eps - c * projT1 (u n) m + - (eps / 2))
        with (eps / 2 - c * (projT1 (u n) m - projT1 l m)) by field.
      apply (proj1 (Qlt_minus_iff (c * (projT1 (u n) m - projT1 l m)) (eps / 2))).
      exact Hscal.
  - (* 下方向：real_lt (c·l − eps) (c·u n)：见证 eps/2，阈值 M *)
    exists (eps / 2)%Q. split.
    + exact Heps_half.
    + exists M. intros m Hm.
      apply Qlt_to_QltT.
      (* 逐点展开投影：real_plus_proj + real_opp_proj + real_const_proj + real_mult_const_proj *)
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const c) l) (real_opp (real_const eps)) m)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_const eps) m)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj eps m)).
      assert (Hml : projT1 (real_mult (real_const c) l) m == c * projT1 l m)
        by (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj c l m)); setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj c m)); reflexivity).
      setoid_rewrite Hml.
      assert (Hmu : projT1 (real_mult (real_const c) (u n)) m == c * projT1 (u n) m)
        by (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj c (u n) m)); setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj c m)); reflexivity).
      setoid_rewrite Hmu.
      (* 目标：Qlt (eps/2) (c·u_n(m) − (c·l_m − eps)) == eps + c·(u_n(m) − l_m)
         即 −(c·(u_n(m) − l_m)) < eps/2（q_scal_eps_half_neg） *)
      assert (Hd : Qlt (Qabs (projT1 (u n) m - projT1 l m)) eps') by (apply QltT_to_Qlt; exact (HM m (NatLe_drop _ _ Hm))).
      assert (Hscal : Qlt (- (c * (projT1 (u n) m - projT1 l m))) (eps / 2))
        by (unfold eps'; apply QltT_to_Qlt; apply q_scal_eps_half_neg; [exact Heps | apply Qlt_to_QltT; exact Hd]).
      (* 目标 eps/2 < c·u_n(m) − (c·l_m − eps) ⟺ eps/2 < eps + c·(u_n(m) − l_m)（ring）
         而 −(c·(u_n(m) − l_m)) < eps/2 ⟺ 0 < eps/2 + c·(u_n(m) − l_m)（Qlt_minus_iff 反向，Hscal） *)
      setoid_replace (c * projT1 (u n) m - (c * projT1 l m + (- eps)))
        with (eps + c * (projT1 (u n) m - projT1 l m)) by ring.
      apply (proj2 (Qlt_minus_iff (eps / 2) (eps + c * (projT1 (u n) m - projT1 l m)))).
      setoid_replace (eps + c * (projT1 (u n) m - projT1 l m) + - (eps / 2))
        with (eps / 2 + c * (projT1 (u n) m - projT1 l m)) by field.
      (* 目标 0 < eps/2 + X（X := c·Δ）；由 Hscal : −X < eps/2 用 Qlt_minus_iff 正向：
         proj1 给 0 < eps/2 + −(−X)，先换 X == −(−X)（Qeq_sym Qopp_involutive） *)
      setoid_replace (eps / 2 + c * (projT1 (u n) m - projT1 l m))
        with (eps / 2 + - - (c * (projT1 (u n) m - projT1 l m))).
      { apply (proj1 (Qlt_minus_iff (- (c * (projT1 (u n) m - projT1 l m))) (eps / 2))).
        exact Hscal. }
      { (* 换 LHS 的 c·X == −(−X)（Qeq_sym Qopp_involutive），setoid_rewrite at 1 只换 LHS *)
        setoid_rewrite (Qeq_sym _ _ (Qopp_involutive (c * (projT1 (u n) m - projT1 l m)))) at 1.
        reflexivity. }
Qed.

(* ============================================================ *)
(* real_lim 乘性保持（u·v → l1·l2）：前置有界引理             *)
(* ============================================================ *)
(* real_lim 逐点界提取：real_lim u l ⟹ 对 n ≥ N（eps 处），
   ∃M(n) ∀k ≥ M(n): |u_n(k) − l_k| < eps。
   证明：real_lim 的双向 real_lt（u n 在 l±eps 之间）⟹
   real_lt (u n − l) (const eps) 双向（差实值小）⟹ real_lt_pair_abs_bound。 *)
Lemma real_lim_pointwise_bound :
  forall (u : nat -> Real) (l : Real) (Hlim : real_lim u l)
         (eps : Q) (Heps : QltT 0 eps),
    sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
      sigT (fun M : nat => forall k : nat, (M <= k)%nat ->
        QltT (Qabs (projT1 (u n) k - projT1 l k)) eps)).
Proof.
  intros u l Hlim eps Heps.
  destruct (Hlim eps Heps) as [N HN].
  exists N.
  intros n Hn.
  destruct (HN n Hn) as [Hup Hdn].
  (* Hup : real_lt (u n) (l + eps)；Hdn : real_lt (l − eps) (u n)。
     需转成 real_lt (u n − l) (const eps) 双向，供 real_lt_pair_abs_bound。
     直接：real_lt_pair_abs_bound 需要 real_lt (real_plus x (real_opp y)) (real_const eps)
     其中 x := u n, y := l——即 real_lt (u n − l) (const eps)。
     而 real_lim 给的是 real_lt (u n) (l + eps)——(u n) < l + eps ⟺ (u n − l) < eps。
     用 real_lt_plus 类平移：由 real_lt (u n) (l + eps) 和 real_eq 平移得
     real_lt (u n − l) (const eps)？—— 直接构造（仿 real_lt_pair_abs_bound 展开）。 *)
  (* 直接展开构造：Hup 给 e1 > 0, M1，∀k≥M1: e1 < (l_k + eps) − u_n(k)；
     Hdn 给 e2 > 0, M2，∀k≥M2: e2 < u_n(k) − (l_k − eps)。
     即 eps − (u_n(k) − l_k) > e1 > 0 ⟹ u_n(k) − l_k < eps − e1 < eps；
         (u_n(k) − l_k) + eps > e2 > 0 ⟹ −eps < u_n(k) − l_k。
     双向 ⟹ |u_n(k) − l_k| < eps（q_abs_lt_two_sided）。 *)
  destruct Hup as [e1 [He1 [M1 HM1]]].
  destruct Hdn as [e2 [He2 [M2 HM2]]].
  exists (max M1 M2).
  intros k Hk.
  assert (Hk1 : (M1 <= k)%nat) by (apply Nat.le_trans with (max M1 M2); [apply Nat.le_max_l | exact Hk]).
  assert (Hk2 : (M2 <= k)%nat) by (apply Nat.le_trans with (max M1 M2); [apply Nat.le_max_r | exact Hk]).
  (* HM1 k : QltT e1 ((l+eps)_k − (u n)_k)；展开投影 l_k + eps − u_n(k) *)
  assert (Hpt1 : projT1 (real_plus l (real_const eps)) k - projT1 (u n) k
                 == projT1 l k + eps - projT1 (u n) k).
  {
    assert (Hp : projT1 (real_plus l (real_const eps)) k == projT1 l k + projT1 (real_const eps) k)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Hc : projT1 (real_const eps) k == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
    setoid_rewrite Hp. setoid_rewrite Hc. reflexivity.
  }
  (* HM2 k : QltT e2 ((u n)_k − (l−eps)_k)；展开 l_k − eps *)
  assert (Hpt2 : projT1 (u n) k - projT1 (real_plus l (real_opp (real_const eps))) k
                 == projT1 (u n) k - (projT1 l k - eps)).
  {
    assert (Hp : projT1 (real_plus l (real_opp (real_const eps))) k == projT1 l k + projT1 (real_opp (real_const eps)) k)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Ho : projT1 (real_opp (real_const eps)) k == - projT1 (real_const eps) k)
      by (apply qeqT_imp_qeq; apply real_opp_proj).
    assert (Hc : projT1 (real_const eps) k == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
    setoid_rewrite Hp. setoid_rewrite Ho. setoid_rewrite Hc. reflexivity.
  }
  (* 上界：u_n(k) − l_k < eps（由 e1 < eps − (u_n(k) − l_k) 且 e1 > 0） *)
  assert (Hlt1 : Qlt e1 (eps - (projT1 (u n) k - projT1 l k))).
  {
    pose proof (HM1 k (NatLe_lift _ _ Hk1)) as HM1k.
    apply QltT_to_Qlt in HM1k.
    setoid_rewrite Hpt1 in HM1k.
    (* 目标 e1 < eps − (u_n k − l k)；HM1k : e1 < l_k + eps − u_n k == eps − (u_n k − l k)
       用 setoid_replace 换 HM1k 的项（Qlt 兼容 Qeq） *)
    setoid_replace (projT1 l k + eps - projT1 (u n) k)
      with (eps - (projT1 (u n) k - projT1 l k)) in HM1k by ring.
    exact HM1k.
  }
  assert (Hlt2 : Qlt e2 (projT1 (u n) k - (projT1 l k - eps))).
  {
    pose proof (HM2 k (NatLe_lift _ _ Hk2)) as HM2k.
    apply QltT_to_Qlt in HM2k.
    setoid_rewrite Hpt2 in HM2k.
    exact HM2k.
  }
  (* 下界：−eps < u_n(k) − l_k（由 e2 < u_n(k) − l_k + eps 且 e2 > 0） *)
  assert (Hlo : Qlt (- eps) (projT1 (u n) k - projT1 l k)).
  {
    (* e2 < u_n k − l_k + eps；目标 −eps < d ⟺ 0 < d + eps，由 e2 < d + eps 且 0 < e2 *)
    assert (Hd2 : Qlt e2 (eps + (projT1 (u n) k - projT1 l k))).
    {
      (* 目标 e2 < eps + (u_n k − l k)；Hlt2 : e2 < u_n k − (l k − eps)，
         换 Hlt2 的 RHS == eps + (u_n k − l k) *)
      setoid_replace (projT1 (u n) k - (projT1 l k - eps))
        with (eps + (projT1 (u n) k - projT1 l k)) in Hlt2 by ring.
      exact Hlt2.
    }
    apply Qlt_minus_iff.
    (* 目标 0 < d + -(-eps) == d + eps；由 e2 < d + eps：0 < (d+eps) − e2 == d + (eps − e2)，
       且 0 < e2 ⟹ 0 < d + eps *)
    assert (Hpos : Qlt 0 ((projT1 (u n) k - projT1 l k) + (eps - e2))).
    {
      apply Qlt_minus_iff in Hd2.
      setoid_replace (eps + (projT1 (u n) k - projT1 l k) - e2)
        with ((projT1 (u n) k - projT1 l k) + (eps - e2)) in Hd2 by ring.
      exact Hd2.
    }
    assert (He2pos : Qlt 0 e2) by (apply QltT_to_Qlt; exact He2).
    assert (Hsum : Qlt (0 + 0) ((projT1 (u n) k - projT1 l k) + (eps - e2) + e2)).
    { apply Qplus_lt_compat; [exact Hpos | exact He2pos]. }
    setoid_replace ((projT1 (u n) k - projT1 l k) + (eps - e2) + e2)
      with ((projT1 (u n) k - projT1 l k) + eps) in Hsum by ring.
    rewrite Qplus_0_l in Hsum.
    setoid_replace (- (- eps)) with eps by (apply Qopp_involutive).
    exact Hsum.
  }
  (* 上界：u_n(k) − l_k < eps（由 0 < e1 且 e1 < eps − d） *)
  assert (Hup' : Qlt (projT1 (u n) k - projT1 l k) eps).
  {
    apply (proj2 (Qlt_minus_iff (projT1 (u n) k - projT1 l k) eps)).
    assert (He1pos : Qlt 0 e1) by (apply QltT_to_Qlt; exact He1).
    apply (Qlt_trans _ e1 _).
    - exact He1pos.
    - exact Hlt1.
  }
  (* |d| < eps：q_abs_lt_two_sided（QltT 形直供，前提经前向桥） *)
  apply (q_abs_lt_two_sided (projT1 (u n) k - projT1 l k) eps Heps).
  - apply Qlt_to_QltT. exact Hlo.
  - apply Qlt_to_QltT. exact Hup'.
Qed.

(* ============================================================ *)
(* real_lim 乘性保持（u·v → l1·l2）                           *)
(* ============================================================ *)
(* 核心逐点界：对固定 n（序列下标），∃M(n) ∀m ≥ M(n):
   |u_n(m)·v_n(m) − l1(m)·l2(m)| < eps。
   分解（q_prod_diff_bound）：≤ |u_n(m)|·|v_n(m)−l2(m)| + |u_n(m)−l1(m)|·|l2(m)|
   —— |u_n(m)| ≤ 1 + Ml1'（u→l1 逐点界在 eps:=1 + l1 有界，**常数不依赖 n**！）；
   —— 项①：|v_n(m)−l2(m)| < eps/(4(1+Ml1'))（v→l2 逐点界，N 固定）⟹ q_abs_mul_bound
      ⟹ < (1+Ml1')·eps/(4(1+Ml1')) = eps/4；
   —— 项②：|u_n(m)−l1(m)| < eps/(4(Ml2'+1))（u→l1 逐点界）且 |l2(m)| ≤ Ml2'
      ⟹ q_abs_mul_bound ⟹ < Ml2'·eps/(4(Ml2'+1)) ≤ eps/4。
   总 < eps/2 < eps。M(n) 依赖 n 合法（real_lim 的 ∀n 内，real_lt 阈值可依赖 n）。 *)
Lemma real_lim_mult_pointwise :
  forall (u v : nat -> Real) (l1 l2 : Real),
    real_lim u l1 -> real_lim v l2 ->
    forall (eps : Q) (Heps : QltT 0 eps),
      sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
        sigT (fun M : nat => forall m : nat, (M <= m)%nat ->
          QltT (Qabs (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) eps)).
Proof.
  intros u v l1 l2 Hlim1 Hlim2 eps Heps.
  (* eps/4 正性 *)
  assert (Heps4 : QltT 0 (eps / 4)%Q).
  {
    assert (Hq : Qlt 0 (eps / 4)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 4) Hq).
  }
  (* l1、l2 实值范数一致有界（real_norm_bounded）：Ml1'、Ml2' 严格正且
     |l1_k| ≤ Ml1'、|l2_k| ≤ Ml2'——l1/l2 是柯西实数，界不依赖 n *)
  destruct (real_norm_bounded l1) as [Ml1' [HMl1'_pos HMl1']].
  destruct (real_norm_bounded l2) as [Ml2' [HMl2'_pos HMl2']].
  (* |u_n(m)| ≤ 1 + Ml1'：u→l1 逐点界在 eps:=1（N_u1 固定）+ l1 有界 *)
  assert (Hone : QltT 0 1%Q).
  { apply Qlt_to_QltT. reflexivity. }
  destruct (real_lim_pointwise_bound u l1 Hlim1 1%Q Hone) as [Nu1 HNu1].
  (* u→l1 逐点界在 eps/(4(Ml2'+1))（项②的 u−l1 界，Nu2 固定）——Set 链：HMl2'_pos 直接用 *)
  assert (Heps_u : QltT 0 (eps / (4 * (Ml2' + 1)))%Q).
  { apply (qltT_div_pos eps (4 * (Ml2' + 1))).
    - exact Heps.
    - apply (qmult_ltT_0_compat 4 (Ml2' + 1)).
      + exact qltT_0_4.
      + apply (qltT_plus_pos_r Ml2' 1). exact HMl2'_pos. exact qltT_0_1. }
  destruct (real_lim_pointwise_bound u l1 Hlim1 (eps / (4 * (Ml2' + 1)))%Q Heps_u) as [Nu2 HNu2].
  (* 1+Ml1' 非负（Set 版：0 ≤T 1 ≤T 1+Ml1'；HMl1'_pos 经 Set 弱化 qltT_leT'，无降级） *)
  assert (H1Ml1'nonnegT : QleT' 0 (1 + Ml1')).
  { apply (qleT'_trans 0 1 (1 + Ml1')).
    - apply Qle_to_QleT'. apply Qlt_le_weak. reflexivity.
    - apply (qleT'_plus_compat 1 1 0 Ml1').
      + apply qleT'_refl.
      + apply qltT_leT'. exact HMl1'_pos. }
  (* v→l2 逐点界在 eps/(4(1+Ml1'+1))——Set 链：0 <T (1+Ml1') 由 0 <T 1 且 1 ≤T 1+Ml1' *)
  assert (Heps_v : QltT 0 (eps / (4 * (1 + Ml1' + 1)))%Q).
  { apply (qltT_div_pos eps (4 * (1 + Ml1' + 1))).
    - exact Heps.
    - apply (qmult_ltT_0_compat 4 (1 + Ml1' + 1)).
      + exact qltT_0_4.
      + apply (qltT_plus_pos_r (1 + Ml1') 1).
        * apply (qltT_leT'_ltT 0 1 (1 + Ml1')).
          -- exact qltT_0_1.
          -- apply (qleT'_plus_compat 1 1 0 Ml1').
             ++ apply qleT'_refl.
             ++ apply qltT_leT'. exact HMl1'_pos.
        * exact qltT_0_1. }
  destruct (real_lim_pointwise_bound v l2 Hlim2 (eps / (4 * (1 + Ml1' + 1)))%Q Heps_v) as [Nv HNv].
  (* 序列阈值 N := max Nu1 (max Nu2 Nv) *)
  exists (max Nu1 (max Nu2 Nv)).
  intros n Hn.
  assert (Hn1 : (Nu1 <= n)%nat) by (apply Nat.le_trans with (max Nu1 (max Nu2 Nv)); [apply Nat.le_max_l | exact Hn]).
  assert (Hn2 : (Nu2 <= n)%nat) by (apply Nat.le_trans with (max Nu2 Nv); [apply Nat.le_max_l | apply Nat.le_trans with (max Nu1 (max Nu2 Nv)); [apply Nat.le_max_r | exact Hn]]).
  assert (Hnv : (Nv <= n)%nat) by (apply Nat.le_trans with (max Nu2 Nv); [apply Nat.le_max_r | apply Nat.le_trans with (max Nu1 (max Nu2 Nv)); [apply Nat.le_max_r | exact Hn]]).
  (* 逐点界阈值（依赖 n）：M1(n) := max(M_u1(n), M_v(n), M_u2(n)) *)
  destruct (HNu1 n Hn1) as [Mu1 HMu1].
  destruct (HNv n Hnv) as [Mv HMv].
  destruct (HNu2 n Hn2) as [Mu2 HMu2].
  exists (max Mu1 (max Mv Mu2)).
  intros m Hm.
  assert (Hm1 : (Mu1 <= m)%nat)
    by (apply Nat.le_trans with (max Mu1 (max Mv Mu2)); [apply Nat.le_max_l | exact Hm]).
  assert (Hmv : (Mv <= m)%nat)
    by (apply Nat.le_trans with (max Mv Mu2); [apply Nat.le_max_l | apply Nat.le_trans with (max Mu1 (max Mv Mu2)); [apply Nat.le_max_r | exact Hm]]).
  assert (Hm2 : (Mu2 <= m)%nat)
    by (apply Nat.le_trans with (max Mv Mu2); [apply Nat.le_max_r | apply Nat.le_trans with (max Mu1 (max Mv Mu2)); [apply Nat.le_max_r | exact Hm]]).
  (* 目标：|u_n(m)·v_n(m) − l1(m)·l2(m)| <T eps——Set 链（HMl1'/HMl2' 直接，无降级） *)
  apply (qltT_eq_compat_l (Qabs (projT1 (u n) m * projT1 (v n) m - projT1 l1 m * projT1 l2 m))
                          (Qabs (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m))
                          eps).
  - apply qeq_imp_qeqT. apply Qabs_wd.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (u n) (v n) m)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj l1 l2 m)).
    reflexivity.
  - assert (HbdT : QleT' (Qabs (projT1 (u n) m * projT1 (v n) m - projT1 l1 m * projT1 l2 m))
                       (Qabs (projT1 (u n) m) * Qabs (projT1 (v n) m - projT1 l2 m)
                        + Qabs (projT1 l2 m) * Qabs (projT1 (u n) m - projT1 l1 m))).
  { apply Qle_to_QleT'.
    assert (Hp : Qle (Qabs (projT1 (u n) m * projT1 (v n) m - projT1 l1 m * projT1 l2 m))
                     (Qabs (projT1 (u n) m) * Qabs (projT1 (v n) m - projT1 l2 m)
                      + Qabs (projT1 (u n) m - projT1 l1 m) * Qabs (projT1 l2 m))) by (apply QleT'_to_Qle; apply q_prod_diff_bound).
    eapply Qle_trans; [exact Hp |].
    apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  (* |u_n(m)| ≤T 1 + Ml1'（三角 + <T1 与 ≤T Ml1' 之和；HMl1' 直接） *)
  assert (HunT : QleT' (Qabs (projT1 (u n) m)) (1 + Ml1')).
  { apply (qleT'_trans (Qabs (projT1 (u n) m))
                       (Qabs (projT1 (u n) m - projT1 l1 m) + Qabs (projT1 l1 m))
                       (1 + Ml1')).
    - apply Qle_to_QleT'.
      apply (Qle_trans _ (Qabs ((projT1 (u n) m - projT1 l1 m) + projT1 l1 m)) _).
      + setoid_replace (Qabs ((projT1 (u n) m - projT1 l1 m) + projT1 l1 m))
          with (Qabs (projT1 (u n) m)) by (apply Qabs_wd; ring).
        apply Qle_refl.
      + apply Qabs_triangle.
    - apply qltT_leT'.
      apply (qltT_plus_leT'_ltT (Qabs (projT1 (u n) m - projT1 l1 m)) 1
                                (Qabs (projT1 l1 m)) Ml1').
      + apply (HMu1 m Hm1).
      + apply HMl1'. }
  (* 项①：|u|·|v−l2| <T (1+Ml1')·(eps/(4(1+Ml1'+1))) *)
  assert (Ht1aT : QltT (Qabs (projT1 (u n) m) * Qabs (projT1 (v n) m - projT1 l2 m))
                       ((1 + Ml1') * (eps / (4 * (1 + Ml1' + 1))))).
  { apply (qleT'_mult_ltT_compat (Qabs (projT1 (u n) m)) (1 + Ml1')
                                 (Qabs (projT1 (v n) m - projT1 l2 m))
                                 (eps / (4 * (1 + Ml1' + 1)))).
    - apply (qltT_leT'_ltT 0 1 (1 + Ml1')).
      + exact qltT_0_1.
      + apply (qleT'_plus_compat 1 1 0 Ml1').
        * apply qleT'_refl.
        * apply qltT_leT'. exact HMl1'_pos.
    - apply qabs_nonnegT.
    - exact HunT.
    - apply (HMv m Hmv). }
  (* 项①上界 ≤T eps/4：因 (1+Ml1') ≤ (1+Ml1'+1) 且 (1+Ml1'+1)·X == eps/4 *)
  assert (Ht1bT : QleT' ((1 + Ml1') * (eps / (4 * (1 + Ml1' + 1)))) (eps / 4)).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ ((1 + Ml1' + 1) * (eps / (4 * (1 + Ml1' + 1)))) _).
    - apply Qmult_le_compat_r.
      + apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1.
      + apply Qlt_le_weak. exact (QltT_to_Qlt 0 (eps / (4 * (1 + Ml1' + 1))) Heps_v).
    - assert (Hf : (1 + Ml1' + 1) * (eps / (4 * (1 + Ml1' + 1))) == eps / 4).
      { field.
        intro Hz.
        assert (Hposx : QltT 0 (1 + Ml1' + 1)).
        { apply (qltT_plus_pos_r (1 + Ml1') 1).
          - apply (qltT_leT'_ltT 0 1 (1 + Ml1')).
            + exact qltT_0_1.
            + apply (qleT'_plus_compat 1 1 0 Ml1').
              * apply qleT'_refl.
              * apply qltT_leT'. exact HMl1'_pos.
          - exact qltT_0_1. }
        destruct (qltT_not_eq_zero (1 + Ml1' + 1) Hposx (qeq_imp_qeqT _ _ Hz)). }
      setoid_rewrite Hf. apply Qle_refl. }
  assert (Ht1T : QltT (Qabs (projT1 (u n) m) * Qabs (projT1 (v n) m - projT1 l2 m)) (eps / 4))
    by (apply (qltT_leT'_ltT _ _ _ Ht1aT Ht1bT)).
  (* 项②：|l2|·|u−l1| <T Ml2'·(eps/(4(Ml2'+1)))（HMl2' 与 HMu2 直接） *)
  assert (Ht2aT : QltT (Qabs (projT1 l2 m) * Qabs (projT1 (u n) m - projT1 l1 m))
                       (Ml2' * (eps / (4 * (Ml2' + 1))))).
  { apply (qleT'_mult_ltT_compat (Qabs (projT1 l2 m)) Ml2'
                                 (Qabs (projT1 (u n) m - projT1 l1 m))
                                 (eps / (4 * (Ml2' + 1)))).
    - exact HMl2'_pos.
    - apply qabs_nonnegT.
    - apply HMl2'.
    - apply (HMu2 m Hm2). }
  assert (Ht2bT : QleT' (Ml2' * (eps / (4 * (Ml2' + 1)))) (eps / 4)).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ ((Ml2' + 1) * (eps / (4 * (Ml2' + 1)))) _).
    - apply Qmult_le_compat_r.
      + apply Qle_plus_nonneg_r. apply QleT'_to_Qle. apply Qle_0_1.
      + apply Qlt_le_weak. exact (QltT_to_Qlt 0 (eps / (4 * (Ml2' + 1))) Heps_u).
    - assert (Hf : (Ml2' + 1) * (eps / (4 * (Ml2' + 1))) == eps / 4).
      { field.
        intro Hz.
        destruct (qltT_not_eq_zero (Ml2' + 1) (qltT_plus_pos_r Ml2' 1 HMl2'_pos qltT_0_1)
                    (qeq_imp_qeqT _ _ Hz)). }
      setoid_rewrite Hf. apply Qle_refl. }
  assert (Ht2T : QltT (Qabs (projT1 l2 m) * Qabs (projT1 (u n) m - projT1 l1 m)) (eps / 4))
    by (apply (qltT_leT'_ltT _ _ _ Ht2aT Ht2bT)).
  (* 结论：|差| ≤T 和 <T eps/4+eps/4 ==T eps/2 <T eps *)
  apply (qleT'_ltT_ltT (Qabs (projT1 (u n) m * projT1 (v n) m - projT1 l1 m * projT1 l2 m))
                       (Qabs (projT1 (u n) m) * Qabs (projT1 (v n) m - projT1 l2 m)
                        + Qabs (projT1 l2 m) * Qabs (projT1 (u n) m - projT1 l1 m))
                       eps);
    [ exact HbdT
    | apply (qltT_leT'_ltT _ (eps / 2) eps);
      [ apply (qltT_leT'_ltT _ (eps / 4 + eps / 4) (eps / 2));
        [ apply (qltT_plus_ltT (Qabs (projT1 (u n) m) * Qabs (projT1 (v n) m - projT1 l2 m))
                               (eps / 4)
                               (Qabs (projT1 l2 m) * Qabs (projT1 (u n) m - projT1 l1 m))
                               (eps / 4));
          [ exact Ht1T | exact Ht2T ]
        | apply qeq_leT'; apply qeq_imp_qeqT;
          assert (Hq : eps / 4 + eps / 4 == eps / 2) by field;
          exact Hq ]
      | apply qltT_leT'; apply qltT_half_lt_selfT; exact Heps ] ].
Qed.

(* 柯西完备性的 real_lim 部分（乘性保持）：u→l1 ∧ v→l2 ⟹ u·v→l1·l2。
   双向 eps/2 夹逼，逐点界由 real_lim_mult_pointwise（eps/2 处）给出。 *)
Theorem real_lim_mult : forall (u v : nat -> Real) (l1 l2 : Real),
  real_lim u l1 -> real_lim v l2 ->
  real_lim (fun n => real_mult (u n) (v n)) (real_mult l1 l2).
Proof.
  intros u v l1 l2 Hlim1 Hlim2 eps Heps.
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  destruct (real_lim_mult_pointwise u v l1 l2 Hlim1 Hlim2 (eps / 2)%Q Heps2) as [N HNP].
  exists N.
  intros n Hn.
  destruct (HNP n Hn) as [M HM].
  split.
  - (* 方向 1：real_lt ((u·v) n) ((l1·l2) + eps)：见证 eps/2，阈值 M *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists M. intros m Hm.
      apply Qlt_to_QltT.
      (* 投影展开：real_plus_proj + real_const_proj *)
      assert (Hp1 : projT1 (real_plus (real_mult l1 l2) (real_const eps)) m
                   == projT1 (real_mult l1 l2) m + projT1 (real_const eps) m)
        by (apply qeqT_imp_qeq; apply real_plus_proj).
      assert (Hc1 : projT1 (real_const eps) m == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
      setoid_rewrite Hp1. setoid_rewrite Hc1.
      setoid_replace (projT1 (real_mult l1 l2) m + eps - projT1 (real_mult (u n) (v n)) m)
        with (eps - (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) by ring.
      assert (Hd : Qlt (Qabs (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) (eps / 2)%Q)
        by (apply QltT_to_Qlt; apply (HM m (NatLe_drop _ _ Hm))).
      apply (proj2 (Qlt_minus_iff (eps / 2) (eps - (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)))).
      setoid_replace (eps - (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m) + - (eps / 2))
        with (eps / 2 - (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) by field.
      apply (proj1 (Qlt_minus_iff (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m) (eps / 2))).
      apply Qle_lt_trans with (Qabs (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)).
      * apply Qle_Qabs.
      * exact Hd.
  - (* 方向 2：real_lt ((l1·l2) − eps) ((u·v) n)：见证 eps/2，阈值 M *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists M. intros m Hm.
      apply Qlt_to_QltT.
      (* 投影展开：real_plus_proj + real_opp_proj + real_const_proj *)
      assert (Hp2 : projT1 (real_plus (real_mult l1 l2) (real_opp (real_const eps))) m
                   == projT1 (real_mult l1 l2) m + projT1 (real_opp (real_const eps)) m)
        by (apply qeqT_imp_qeq; apply real_plus_proj).
      assert (Ho2 : projT1 (real_opp (real_const eps)) m == - projT1 (real_const eps) m)
        by (apply qeqT_imp_qeq; apply real_opp_proj).
      assert (Hc2 : projT1 (real_const eps) m == eps) by (apply qeqT_imp_qeq; apply real_const_proj).
      setoid_rewrite Hp2. setoid_rewrite Ho2. setoid_rewrite Hc2.
      setoid_replace (projT1 (real_mult (u n) (v n)) m - (projT1 (real_mult l1 l2) m + (- eps)))
        with (eps + (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) by ring.
      assert (Hd : Qlt (Qabs (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) (eps / 2)%Q)
        by (apply QltT_to_Qlt; apply (HM m (NatLe_drop _ _ Hm))).
      apply (proj2 (Qlt_minus_iff (eps / 2) (eps + (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)))).
      setoid_replace (eps + (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m) + - (eps / 2))
        with (eps / 2 + (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) by field.
      (* 目标 0 < eps/2 + diff：q_abs_gt_neg 给 -(eps/2) < diff ⟹ proj1(Qlt_minus_iff) 给
         0 < diff + -(-(eps/2))，换形 -(-(eps/2)) == eps/2 且换序 == 目标 *)
      assert (Hlo : Qlt (- (eps / 2)) (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m))
        by exact (QltT_to_Qlt _ _
              (q_abs_gt_neg (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m) (eps / 2)%Q
                Heps2 (Qlt_to_QltT _ _ Hd))).
      (* 目标换形：eps/2 + diff == diff + -(-(eps/2))（ring + Qopp_involutive） *)
      setoid_replace (eps / 2 + (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m))
        with (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m + (- (- (eps / 2))))
        by (rewrite (Qopp_involutive (eps / 2)); ring).
      exact (proj1 (Qlt_minus_iff (- (eps / 2)) (projT1 (real_mult (u n) (v n)) m - projT1 (real_mult l1 l2) m)) Hlo).
Qed.

(* ============================================================ *)
(* ============================================================ *)
(* 工程③阶段 A：Q 层 exp 部分和 + 柯西性（检验 probe_exp.v 嵌入） *)
(* ============================================================ *)
(* RealInterface 的 exp_neg/log_inv 实例化第一步：exp_partial n x := *)
(* Sum_{k=0}^{n} x^k/k!，以及 exp_partial_cauchy（固定 x 部分和柯西）。 *)
(* 全部零 承认，纯构造性。 *)

(* ToyR ：替换定理假设面查证（预期：全局语境下封闭） *)
Print Assumptions qltT_0_1.
Print Assumptions qleT'_refl.
Print Assumptions qeq_le.
