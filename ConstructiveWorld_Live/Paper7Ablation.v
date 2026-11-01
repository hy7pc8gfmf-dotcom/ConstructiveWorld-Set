(* ============================================================
   Paper7Ablation —— 使命行：论文7《率即算法》§9.1 披露的 AttnDoeblin.v
   Section BoundedSoftmax 全部 Variable 接口假设逐个三分类（A 已实例化
   消解 / B 接口字段 / C 可由已证件导出），并对 C 类逐条给出非平凡定理。
   依赖：S01_BaseRing、fa53_compat_abs。
   内容（本件七定理，前缀 p7a_ 全库防撞已核零命中）：
   §1 expf 迷你接口两件——p7a_expf_wd：同余性从 {expf_plus, expf_zero,
   expf_pos} 经 mult_cancel_l（S01:906）消去链导出（同余性无须独立假设）；
   p7a_expf_mono_le_do：mono_le 从 mono_lt + DecidableOrder（S01:329 三分）
   + p7a_expf_wd 导出——BoundedSoftmax 的 expf 字段面 6 → 5（AttnDoeblin:469
   的 expf_mono_le 语句位在抽象接口层无单向消去，但可选扩展类
   DecidableOrder 一桥闭合，与 fa53_compat_abs 同款闭合原理）；
   §2 有界 softmax 上界件——p7a_lo_lt_one：lo = e^{−Δ/T} < 1 严格上界
   （bs_lo_pos AttnDoeblin:550 的对偶补件；由 lt_zero_opp + expf_mono_lt +
   expf_zero 三步链，字段面比 bs_delta_star_lt_one（:584）更细）；
   p7a_lo_lt_one_instant：invT := inv_pos temp temp_pos 处的字面 lo < 1 形
   （引用 inv_pos_pos）。
   §3 κ := 1−δ* 选择器供给三件（论文 §6.3 闭合的 κ∈(0,1) 前件包，全部从
   B 类接口证书 lo_pos 与 δ*<1 出发）——p7a_delta_star_pos：0 < δ* = lo²
   （引用 mult_positive）；p7a_omd_pos：0 < 1−δ*（Part A u_omd_pos_next
   AttnDoeblin:164 的 softmax 实例形，混合加法保序经
   fa53_lt_plus_compat_lt_le_dec，A 类锚引用）；p7a_omd_lt_one：1−δ* < 1
   （fa53_lt_plus_compat_le_lt_dec 对偶件引用）。
   构造性注记：语句面全 Set 层（Id/Or/Not 用 S01:63-68 Set 层定义，零 Prop
   泄露）；非平凡真证（消去链/三分分解/归谬/平移四段字段链）；原树零改
   （本件新建，只 Require 引用零改）。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================ *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ################ §1 expf 迷你接口精简 ################ *)
(* 对照 AttnDoeblin.v L463-469 的五字段 + mono_le 语句位。         *)
Section P7aExpf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* C1：expf 同余性导出（{plus, zero, pos} ⟹ wd，无须独立假设） *)
Theorem p7a_expf_wd : forall a b : R, Id a b -> Id (expf a) (expf b).
Proof.
  intros a b Hab.
  assert (He := expf_pos (opp b)).
  assert (Ha1 : Id (mult (expf a) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus a (opp b)))).
    apply (id_trans (id_cong expf
             (id_trans (id_cong (fun x => plus x (opp b)) Hab)
                       (plus_opp b)))).
    exact expf_zero. }
  assert (Hb1 : Id (mult (expf b) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus b (opp b)))).
    apply (id_trans (id_cong expf (plus_opp b)) expf_zero). }
  apply (mult_cancel_l (expf (opp b)) (expf a) (expf b) He).
  apply (id_trans (id_trans (mult_comm (expf (opp b)) (expf a)) Ha1)
                  (id_sym (id_trans (mult_comm (expf (opp b)) (expf b)) Hb1))).
Qed.

(* C2：expf_mono_le 导出（mono_lt + 三分 + C1 ⟹ mono_le；字段面 6→5） *)
Theorem p7a_expf_mono_le_do : forall a b : R, le a b -> le (expf a) (expf b).
Proof.
  intros a b Hab.
  destruct (@fa53_lt_dec RI DO a b) as [Hlt | [Heq | Hgt]].
  - (* a < b：严格单调直给，Or 左支升 le *)
    exact (lt_le_iff (expf a) (expf b) (inl (expf_mono_lt a b Hlt))).
  - (* a == b：C1 同余 + 自反 *)
    apply (le_id_l (expf a) (expf b) (expf b) (p7a_expf_wd a b Heq)).
    exact (le_refl (expf b)).
  - (* b < a 与 le a b 冲突：le_antisym 归 Id 再撞 irrefl 归谬 *)
    destruct (lt_irrefl b
      (lt_id_r b a b (le_antisym a b Hab (lt_le_iff b a (inl Hgt))) Hgt)).
Qed.

End P7aExpf.

(* ################ §2 有界 softmax：lo < 1 严格上界 ################ *)
(* 对照 AttnDoeblin.v L544-548 的 lo := expf (invT·opp Delta)。   *)
Section P7aSoftBound.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* C3：lo < 1（bs_lo_pos AttnDoeblin:550 的对偶补件；
   任意正 invT 处的通用形） *)
Theorem p7a_lo_lt_one : forall invT : R,
  lt zero invT -> lt (expf (mult invT (opp Delta))) one.
Proof.
  intros invT Hin.
  assert (Hond := lt_zero_opp Delta Delta_pos).
  (* invT·(oppΔ) < 0：先 oppΔ·invT < 0·invT，再 0·invT 归零 *)
  assert (Hm : lt (mult (opp Delta) invT) zero).
  { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
             (id_trans (mult_comm zero invT) (mult_zero invT))).
    exact (lt_mult_compat (opp Delta) zero invT Hin Hond). }
  apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
  apply (expf_mono_lt (mult invT (opp Delta)) zero).
  apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
                   (mult_comm invT (opp Delta))).
  exact Hm.
Qed.

(* C3'：字面 lo := expf (inv_pos temp temp_pos · opp Delta) 处的 lo < 1 *)
Theorem p7a_lo_lt_one_instant :
  lt (expf (mult (inv_pos temp temp_pos) (opp Delta))) one.
Proof.
  exact (p7a_lo_lt_one (inv_pos temp temp_pos) (inv_pos_pos temp temp_pos)).
Qed.

End P7aSoftBound.

(* ################ §3 κ := 1−δ* 选择器供给 ################ *)
(* 对照 AttnDoeblin.v L548 的 delta_star := mult lo lo 与
   论文 §6.3（闭合前件：κ ∈ (0,1)）。前提恰为 B 类接口证书：
   lo_pos（= bs_lo_pos 之形）与 δ* < 1（= bs_delta_star_lt_one）。 *)
Section P7aKappa.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable lo : R.
Variable lo_pos : lt zero lo.

(* C4：0 < δ* = lo·lo *)
Theorem p7a_delta_star_pos : lt zero (mult lo lo).
Proof.
  exact (mult_positive lo lo lo_pos lo_pos).
Qed.

(* C5：δ* < 1 ⟹ 0 < 1−δ*（u_omd_pos_next AttnDoeblin:164 的
   softmax 实例形；混合加法保序走 fa53 件1） *)
Theorem p7a_omd_pos :
  lt (mult lo lo) one -> lt zero (minus one (mult lo lo)).
Proof.
  intro Hds.
  apply (lt_id_l zero (plus (mult lo lo) (opp (mult lo lo)))
                   (plus one (opp (mult lo lo)))
                   (id_sym (plus_opp (mult lo lo)))).
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO (mult lo lo) one
           (opp (mult lo lo)) (opp (mult lo lo)) Hds
           (le_refl (opp (mult lo lo)))).
Qed.

(* C6：0 < δ* ⟹ 1−δ* < 1（对偶件 fa53 件2 引用） *)
Theorem p7a_omd_lt_one : lt (minus one (mult lo lo)) one.
Proof.
  apply (lt_id_r (plus one (opp (mult lo lo))) (plus one zero) one
                   (plus_zero one)).
  exact (@fa53_lt_plus_compat_le_lt_dec RI DO one one
           (opp (mult lo lo)) zero (le_refl one)
           (lt_zero_opp (mult lo lo) p7a_delta_star_pos)).
Qed.

End P7aKappa.

(* ---- PA 自检段（G1 min-pa 与 G4 审查留痕面；全出节全局名） ---- *)
Print Assumptions p7a_expf_wd.
Print Assumptions p7a_expf_mono_le_do.
Print Assumptions p7a_lo_lt_one.
Print Assumptions p7a_lo_lt_one_instant.
Print Assumptions p7a_delta_star_pos.
Print Assumptions p7a_omd_pos.
Print Assumptions p7a_omd_lt_one.
