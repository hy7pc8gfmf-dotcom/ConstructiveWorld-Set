(* 五字段指针｜使命：π 莱布尼茨部分和序列（lp_four * lp_odd）的柯西完备判据适配三件——
   尾控实例 lw0m_tail_bounded_pi（lic_tail_bounded 接口）、窗宽消失实例
   lw0m_vanish_pi（lic_vanish 接口）、度量同余件 lw0m_metric_congr（real_eq 左元
   换代下 real_metric 不变）。依赖：PiEnvelope（pie_tail4/pie_modulus/
   pie_modulus_bound/pie_v_eq/pie_mag_pos/pie_mag_antitone）、
   UpReqIrrationalCriterion（lic_tail_bounded/lic_vanish）、S02_CauchyComplete
   （real_eq/QltT/Real/real_plus/real_opp/QltT_to_Qlt/Qlt_to_QltT/QleT'_to_Qle/
   qeqT_imp_qeq）、S03_QExp（real_metric/real_abs/q_abs_abs_triangle）、
   S10_KVQuantTrig（lp_four/lp_odd）。构造性：零承认式语句（机械核验）；语句面
   全 Set 层承载零 Prop 泄露（lic 两接口与 real_eq 均 Set 值形），证明内 Prop
   （Qlt/Qle/Qeq）仅作脚手架，经 QltT_to_Qlt/QleT'_to_Qle/qeqT_imp_qeq 三桥
   出入，结论面恒 Set。统一窗 lw0m_e n := 5 * pie_mag n 三件共享。
   编译配方：rocq c -native-compiler no -Q /tmp/nw10abl43 "" LW0MLicBridge.v
   （编译经 cpu_guard.sh 温控包裹）。命名：lw0m_ 前缀（全树查重零占用）。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia Lqa.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import UpReqIrrationalCriterion.

(* ============================================================ *)
(* §0 统一窗与 π 投影序列                                          *)
(* ============================================================ *)

(* 统一窗：e n := 5 * pie_mag n（三件共享；系数 5 吸收两处索引抬升） *)
Definition lw0m_e (n : nat) : Q := 5 * pie_mag n.

(* π 投影序列：xL n := lp_four * lp_odd n *)
Definition lw0m_xL (n : nat) : Q := lp_four * lp_odd n.

(* ============================================================ *)
(* §1 尾控桥                                                       *)
(* pie_tail4 非严格 Qle + 1×pie_mag 余量 ⟹ 严格 QltT；            *)
(* 索引抬升 pie_mag(2n+2) ⟹ pie_mag n（pie_mag_antitone）；        *)
(* 序列接缝 pie_v_eq（lp_four * lp_odd ⟹ 4 * pie_partial(2·+2)）。 *)
(* ============================================================ *)
Definition lw0m_tail_bounded_pi : lic_tail_bounded lw0m_xL lw0m_e.
Proof.
  intros n k Hn1 Hnk.
  unfold lw0m_xL, lw0m_e.
  apply Qlt_to_QltT.
  assert (Hanti : QleT' (pie_mag (2 * n + 2)) (pie_mag n))
    by (apply pie_mag_antitone; lia).
  pose proof (QleT'_to_Qle _ _ Hanti) as HantiQ.
  pose proof (QltT_to_Qlt _ _ (pie_mag_pos n)) as Hpm.
  apply (Qle_lt_trans _ (4 * pie_mag (2 * n + 2)) _).
  - rewrite (qeqT_imp_qeq _ _ (pie_v_eq k)).
    rewrite (qeqT_imp_qeq _ _ (pie_v_eq n)).
    apply QleT'_to_Qle. apply (pie_tail4 (2 * n + 2) (2 * k + 2)). lia.
  - lra.
Qed.

(* ============================================================ *)
(* §2 窗宽消失桥                                                   *)
(* 模量重标定 N := pie_modulus (eps / 10)（pie_modulus 天然配      *)
(* 4 系窗，lic 窗是 5 系）；单点界 ⟹ 最终界经 pie_mag_antitone；   *)
(* QltT↔Qlt 双换形器各一处（前提换入＋结论换出）。                 *)
(* ============================================================ *)
Definition lw0m_vanish_pi : lic_vanish lw0m_e.
Proof.
  intros eps Heps.
  pose proof (QltT_to_Qlt 0%Q eps Heps) as Heps0.
  assert (Hd10 : Qlt 0 (eps * (1 # 10))) by lra.
  pose proof (pie_modulus_bound (eps * (1 # 10)) Hd10) as HbT.
  pose proof (QltT_to_Qlt _ _ HbT) as Hb.
  exists (pie_modulus (eps * (1 # 10))).
  intros n Hn.
  unfold lw0m_e.
  apply Qlt_to_QltT.
  assert (Hanti : QleT' (pie_mag n)
                      (pie_mag (pie_modulus (eps * (1 # 10)))))
    by (apply pie_mag_antitone; exact Hn).
  pose proof (QleT'_to_Qle _ _ Hanti) as HantiQ.
  lra.
Qed.

(* ============================================================ *)
(* §3 real_metric 同余件                                           *)
(* 逐 eps 构造：反三角 q_abs_abs_triangle 单步给界；                *)
(* 投影定义性展开 real_metric := real_abs (real_plus x             *)
(* (real_opp z))（real_plus/real_opp/real_abs 均 Defined 透明）。   *)
(* ============================================================ *)
Lemma lw0m_metric_congr : forall (x y z : Real), real_eq x y ->
  real_eq (real_metric x z) (real_metric y z).
Proof.
  intros x y z Hxy.
  destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  intros eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - v n)) _).
  - cbv beta iota delta [real_metric real_abs real_plus real_opp].
    assert (Hr : (u n - v n == u n - w n - (v n - w n))%Q) by ring.
    rewrite Hr.
    apply QleT'_to_Qle. apply q_abs_abs_triangle.
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.
