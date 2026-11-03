(* 五字段指针｜模块：LW2SepTransport.v。
   数学使命：柯西等价实数间点态分离的传递定理。若 X 与 Y 柯西等价（real_eq），且 X 与
   有理点 q 具有半径 c 的点态分离（real_lt (real_const c) (real_metric X (real_const q))），
   则 Y 与 q 具有半径 c/2 的点态分离。一般形 lw2t_sep_transport_k 显式携带退化因子 k
   （QleT 2 k，即 k >= 2）：分离半径按 c/k 收缩，等价模量在预算 c/(2k) 处实例化；
   k := 2 为兼容特化形；lw2t_sep_transport_sym 给出反方向传递。证明逐 eps 构造：
   等价模量 N1 与分离模量 N2 取 max，逐点经 lic_metric_proj 两次投影归约后由
   q_abs_abs_triangle 反三角收束；退化内核为 2*(1/k) <= 1 的 c 倍缩放。
   依赖：S01_BaseRing（Set 层 Id/And/Or/NatLe）、S02_CauchyComplete（Real/real_eq/real_lt/
   QltT/QleT/QleT'、real_const_proj、real_eq_sym、NatLe_lift/NatLe_drop、qeq_le、
   QltT_to_Qlt/Qlt_to_QltT）、S03_QExp（real_metric、q_abs_abs_triangle）、
   UpReqIrrationalCriterion（lic_metric_proj 逐点投影归约）。
   对标：Bishop 构造分析中点态分离（逐 eps 独立性）沿柯西等价的传递性；退化因子显式化
   使分离半径沿传递单调不增（c/k，k >= 2，零放大）。
   构造性：语句面全 Set 层（QltT/QleT/real_lt/sigT，恒等取 S01 的 Set 层 Id），零承认、
   零经典逻辑、Require 面不引公理模块；Q 层不等式的线性判定一律用 Lqa；QleT 在 k := 2 处
   的见证由 inr id_refl 显式给出。
   编译配方：rocq c -native-compiler no -q -Q "<世界根>" "" LW2SepTransport.v
   （世界根＝五闸自验世界 /tmp/nw_wfadj33；工具链＝Live/toolchain/opam/live/bin；
   cpu_guard v3 包裹＋ulimit -s 65532；COQLIB 与 ROCQLIB 需同值指向 Rocq 9.1 库根）。
*)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Opaque Qred.

(* k >= 2 蕴含倒数正性：0 < 1/k（Id 分支按定义归约闭合） *)
Lemma lw2t_qinv_pos : forall k : Q, QleT 2 k -> QltT 0 (Qinv k).
Proof.
  intros k Hk. destruct Hk as [Hlt | Hid].
  - apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    apply QltT_to_Qlt in Hlt. lra.
  - destruct Hid. exact id_refl.
Qed.

(* k >= 2 蕴含 2*(1/k) <= 1：退化因子算术内核（两侧同乘正数 1/k） *)
Lemma lw2t_k_inv2_le : forall k : Q, QleT 2 k -> QleT' (2 * Qinv k) 1.
Proof.
  intros k Hk. destruct Hk as [Hlt | Hid].
  - apply QltT_to_Qlt in Hlt.
    assert (Hk0 : (0 < k)%Q) by lra.
    assert (Hinvpos : (0 < Qinv k)%Q) by (apply Qinv_lt_0_compat; exact Hk0).
    apply Qle_to_QleT'.
    apply (Qle_trans _ (k * Qinv k)%Q).
    + apply Qmult_le_compat_r.
      * apply Qlt_le_weak. exact Hlt.
      * apply Qlt_le_weak. exact Hinvpos.
    + assert (Hne : ~ (k == 0)%Q).
      { intro Hz. rewrite Hz in Hk0. exact (Qlt_irrefl 0 Hk0). }
      rewrite (Qmult_inv_r k Hne). apply Qle_refl.
  - destruct Hid. exact id_refl.
Qed.

Theorem lw2t_sep_transport_k : forall (X Y : Real) (q c k : Q),
  QltT 0 c -> QleT 2 k -> real_eq X Y ->
  real_lt (real_const c) (real_metric X (real_const q)) ->
  real_lt (real_const (c / k)%Q) (real_metric Y (real_const q)).
Proof.
  intros X Y q c k Hc Hk Heq Hsep.
  pose proof (lw2t_qinv_pos k Hk) as Hkpos.
  pose proof (lw2t_k_inv2_le k Hk) as Hk2.
  apply QltT_to_Qlt in Hkpos. apply QltT_to_Qlt in Hc.
  destruct Hsep as [eps0 [Heps0 [N2 HN2]]].
  apply QltT_to_Qlt in Heps0.
  assert (Hbinv : (Qinv (2 * k) == (1#2) * Qinv k)%Q).
  { rewrite Qinv_mult_distr.
    assert (Hq2 : (Qinv 2 == (1#2))%Q) by reflexivity.
    rewrite Hq2. reflexivity. }
  assert (Hbud : QltT 0 (c * Qinv (2 * k))%Q).
  { apply Qlt_to_QltT. rewrite Hbinv. apply Qmult_lt_0_compat.
    - exact Hc.
    - apply Qmult_lt_0_compat.
      + lra.
      + exact Hkpos. }
  destruct (Heq (c * Qinv (2 * k))%Q Hbud) as [N1 HN1].
  exists (c * Qinv (2 * k))%Q. split.
  - exact Hbud.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Hn1 : NatLe N1 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
    assert (Hn2 : NatLe N2 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
    pose proof (HN2 n Hn2) as Hx.
    apply QltT_to_Qlt in Hx.
    rewrite (lic_metric_proj X q n) in Hx.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)) in Hx.
    pose proof (HN1 n Hn1) as Hy.
    apply QltT_to_Qlt in Hy.
    destruct X as [u Hu].
    cbn [projT1] in Hx.
    apply Qlt_to_QltT.
    rewrite (lic_metric_proj Y q n).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (c / k) n)).
    destruct Y as [v Hv].
    cbn [projT1] in Hy.
    cbn [projT1].
    assert (Hr : (v n - q == (u n - q) - (u n - v n))%Q) by ring.
    assert (Htri : Qle (Qabs (Qabs (u n - q) - Qabs (u n - v n))) (Qabs (v n - q))).
    { rewrite Hr. apply QleT'_to_Qle. apply q_abs_abs_triangle. }
    destruct (proj1 (Qabs_Qle_condition (Qabs (u n - q) - Qabs (u n - v n))
                                        (Qabs (v n - q))) Htri) as [_ HAB].
    assert (Hbm : Qle (2 * (c * Qinv (2 * k)) + c * Qinv k) c).
    { assert (Hring : (2 * (c * Qinv (2 * k)) + c * Qinv k == c * (2 * Qinv k))%Q).
      { rewrite Hbinv. ring. }
      rewrite Hring.
      apply (Qle_trans _ (c * 1)%Q).
      - apply (proj2 (Qmult_le_l (2 * Qinv k) 1 c Hc)). exact (QleT'_to_Qle _ _ Hk2).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_r. }
    assert (Hchain : Qlt (c + eps0 - (c * Qinv (2 * k))) (Qabs (v n - q))) by lra.
    assert (Hmform : (c / k == c * Qinv k)%Q) by reflexivity.
    rewrite Hmform.
    lra.
Qed.

Theorem lw2t_sep_transport : forall (X Y : Real) (q c : Q),
  QltT 0 c -> real_eq X Y ->
  real_lt (real_const c) (real_metric X (real_const q)) ->
  real_lt (real_const (c / 2)%Q) (real_metric Y (real_const q)).
Proof.
  intros X Y q c Hc Heq Hsep.
  exact (lw2t_sep_transport_k X Y q c 2 Hc (inr id_refl) Heq Hsep).
Qed.

Theorem lw2t_sep_transport_sym : forall (X Y : Real) (q c : Q),
  QltT 0 c -> real_eq X Y ->
  real_lt (real_const c) (real_metric Y (real_const q)) ->
  real_lt (real_const (c / 2)%Q) (real_metric X (real_const q)).
Proof.
  intros X Y q c Hc Heq Hsep.
  exact (lw2t_sep_transport Y X q c Hc (real_eq_sym X Y Heq) Hsep).
Qed.

Print Assumptions lw2t_sep_transport_k.
Print Assumptions lw2t_sep_transport.
Print Assumptions lw2t_sep_transport_sym.
