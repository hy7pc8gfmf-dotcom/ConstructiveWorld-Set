(* ==========================================================================)
   UpAblP7_LoHiSqueeze.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：lhs_lo_lt_one_hi、lhs_lo_lt_hi、lhs_delta_star_bounded、lhs_omd_bounded、uahl_lo_lt_one_hi、uahl_lo_lt_hi、uahl_delta_star_bounded、uahl_omd_bounded、uahl_omd_bounded_one。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* 【双代同文明认】本件 UahlStar 段与 ToyR_UpAblP7_LoHiSqueeze.v 同名段逐字同文 *)
(* （diff 为空）。平行位明认记录：旧位退役属使用面切换另案裁决范围，     *)
(* 本注不改语句面。 *)
Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* ================= §1 lhs_lo_lt_one_hi 族 ================= *)
(* ################ 段一：合璧包装、夹逼推论、δ*∈(0,1)（无 DO） #### *)
(* 对照  -548：lo := expf(invT·oppΔ)、hi := expf(invT·Δ)。 *)

Section LhsPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* 件 a：合璧包装——lt lo one ∧ lt one hi（Set 层 And = prod）。
   左支使用 p7a_lo_lt_one（剪枝形：Delta/Delta_pos/expf/expf_zero/
   expf_mono_lt 五参＋invT；inv_pos_pos 实例化消解 lt zero invT）；
   右支使用 p7d_hi_gt_one（全称 8 参形，temp 面齐全）。 *)
Theorem lhs_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* 件 b：夹逼推论——lt lo hi（lt_trans 一步，两支皆出自合璧件）。
   语句与基座 AttnDoeblin.bs_lo_lt_hi:565 对齐，前提面同（B 类证书）。 *)
Theorem lhs_lo_lt_hi : lt lo hi.
Proof.
  assert (Hlo : lt lo one).
  { exact (fst lhs_lo_lt_one_hi). }
  assert (Hhi : lt one hi).
  { exact (snd lhs_lo_lt_one_hi). }
  exact (lt_trans lo one hi Hlo Hhi).
Qed.

(* 件 c：0 < δ* < 1 完整包装（Set 层 And）。
   左支：p7a_delta_star_pos（检验签名 forall lo, lt zero lo -> …；
   DO/temp 面均已被出节剪枝，lo_pos := expf_pos(invT·oppΔ) 直接供给）。
   右支（δ*<1 新导）：lo<1（合璧件左支）＋lo>0 ⟹ lo·lo < lo·1
   （lt_mult_compat 右乘 lo 保严格序）＝lo（mult_one 右单位律经
   lt_id_r 降形）<1（再使用 lo<1）——lt_trans 接合。 *)
Theorem lhs_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End LhsPair.

(* ############ 段二：κ := 1−δ* ∈ (0,1) 前件包接合（DO 节） ######## *)
(* p7a_omd_pos/p7a_omd_lt_one 出节保留 DO（fa53 使用链），其隐式参
   不可由结论反推，须 @ RI DO 全参形供给（P7A 卡使用法先例）。 *)

Section LhsStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* 件 d：0 < 1−δ* < 1 完整包装（论文 §6.3 的 κ∈(0,1) 前提包）。
   左支：p7a_omd_pos 使用件 c 右支（δ*<1 ⟹ 0<κ）；
   右支：p7a_omd_lt_one 使用 lo_pos（0<δ* ⟹ κ<1）。
   两支出节前件（δ*<1 前件／lo_pos 前件）分别由段一件 c 与
   expf_pos 字段证书实例化消解。 *)
Theorem lhs_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End LhsStar.

(* ---- PA 自检段（G1 min-pa 与 G4 审查留痕面；全出节全局名） ---- *)
Print Assumptions lhs_lo_lt_one_hi.
Print Assumptions lhs_lo_lt_hi.
Print Assumptions lhs_delta_star_bounded.
Print Assumptions lhs_omd_bounded.
(* ================= §2 uahl_lo_lt_one_hi 族 ================= *)
(* ############ 段一：合取 lo<1∧1<hi、夹逼 lo<hi、δ*∈(0,1)（无序可判定参） ## *)
(* 节变量面与源模块  的 LhsPair 节一致（温度对＋利差对＋指数族四件）。 *)

Section UahlPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* uahl_lo_lt_one_hi（源模块 lhs_lo_lt_one_hi 的独立重证）：左支经              *)
(*   p7a_lo_lt_one，右支经 p7d_hi_gt_one；invT 正性由 inv_pos_pos 提供。      *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* uahl_lo_lt_hi（源模块 lhs_lo_lt_hi 的独立重证）：lt_trans 两步，两支取自 uahl_lo_lt_one_hi 的两肢 *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* uahl_delta_star_bounded（源模块 lhs_delta_star_bounded 的独立重证）：        *)
(*   左支 p7a_delta_star_pos；右支 δ*<1 独立三步：lt_mult_compat、             *)
(*   lt_id_l（经 mult_one）与 lt_trans。 *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ############ 段二：uahl_omd_bounded —— κ:=1−δ*∈(0,1)（带可判定序参节） #### *)
(* 节变量面与源模块  的 LhsStar 节一致；p7a_omd_pos/p7a_omd_lt_one  *)
(* 的可判定序隐式参不可由结论反推，故以 @ 全参显式应用。                       *)

Section UahlStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* uahl_omd_bounded（源模块 lhs_omd_bounded 的独立重证）：左支以 δ*<1 前提       *)
(*   应用 @p7a_omd_pos；右支以 0<lo 应用 @p7a_omd_lt_one——全参显式。 *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End UahlStar.

(* ########## 段三：实例形甲——uahl_omd_bounded/uahl_lo_lt_hi @ 温度:=1、利差:=1 ## *)
(* 温度与利差均取 one（one_pos 提供两处正性位），invT:=inv_pos one one_pos；    *)
(* 指数族保持抽象（全库无具体实数实例）。                                     *)

Section UahlSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* uahl_omd_bounded_one（uahl_omd_bounded 于温度:=1、利差:=1 的实例形）：      *)
(*   p7a_lo_lt_one @ one/one 供 lo<1，expf_pos 供 0<lo，δ*<1 三步内联，@ 全参显式。 *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
             (inv_pos_pos one one_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

(* uahl_lo_lt_hi_one（uahl_lo_lt_hi 于同上实例的实例形）：p7a_lo_lt_one        *)
(*   @ one/one 供 lo<1，p7d_hi_gt_one @ one/one 供 1<hi，lt_trans 合成。 *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))           (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT              (inv_pos_pos one one_pos))           (p7d_hi_gt_one one one_pos one one_pos expf expf_pos expf_zero              expf_mono_lt)).
Qed.

End UahlSbInst.

(* ############ 段四：实例形乙——uahl_omd_bounded @ lo:=二分之一抽象形 ######## *)
(* lo:=inv_pos (plus one one) two_pos（二分之一，two_pos/inv_pos_pos 提供正性）；*)
(* 左支不经 δ*<1 中转，走独立链：half_twice（半＋半=1，半方＋半方=半）与       *)
(* plus_positive（半方>0）及恒等重排，推得 0<1−1/4；                          *)
(* 右支 @p7a_omd_lt_one。                                                     *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* uahl_omd_bounded_half（实例形乙） *)
Theorem uahl_omd_bounded_half :
  And (lt zero (minus one half2)) (lt (minus one half2) one).
Proof.
  assert (Hhp : lt zero half).
  { exact (inv_pos_pos (plus one one) two_pos). }
  assert (Hh2p : lt zero half2).
  { exact (mult_positive half half Hhp Hhp). }
  assert (Hh2p2 : lt zero (plus half2 half2)).
  { exact (plus_positive half2 half2 Hh2p Hh2p). }
  assert (Hq : Id (plus half2 half2) half).
  { exact (half_twice half). }
  assert (Hone : Id (plus half half) one).
  { exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                    (half_twice one)). }
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans (id_sym Hone) (id_sym (id_cong (fun x => plus x x) Hq))). }
  assert (Gup : Id (plus (plus (plus half2 half2) (plus half2 half2))
                         (opp half2))
                   (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (plus_assoc (plus half2 half2) (plus half2 half2)
                       (opp half2)))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_trans (id_sym (plus_assoc half2 half2 (opp half2)))
                      (id_trans
                         (id_cong (fun w => plus half2 w)
                            (plus_comm half2 (opp half2)))
                         (plus_assoc half2 (opp half2) half2))))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_cong (fun w => plus w half2) (plus_opp half2)))
                (id_trans
                   (id_cong (fun x => plus (plus half2 half2) x)
                      (id_trans (plus_comm zero half2) (plus_zero half2)))
                   (id_sym (plus_assoc half2 half2 half2)))))). }
  assert (Gtotal : Id (minus one half2) (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_cong (fun w => plus w (opp half2)) (id_sym Hone2)))
             Gup). }
  split.
  - exact (lt_id_r zero (plus half2 (plus half2 half2)) (minus one half2)
             (id_sym Gtotal)
             (plus_positive half2 (plus half2 half2) Hh2p Hh2p2)).
  - exact (@p7a_omd_lt_one RI DO half Hhp).
Qed.

End UahlHalf.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
