(* ============================================================
   使命：本件定理/引理声明面所述性质的形式化（原头注为历史注记块，
         实质整编尚待后续；本块为五字段指针）。
   依赖：件内 Require 声明面所列库件。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)

(* ========================================================================= *)
(*                                                                           *)
(* Require 面                                                                *)
(* 替换定理清单：e66s_real_sum_over_S_ext／e66s_real_sum_over_S_le／         *)
(* e66s_real_sum_over_S_add（共 3 位）                                       *)
(* 非平凡性口径：源版本体换实例归纳重演（换形实例化，中转项双段转移）；无一    *)
(* 行拆分式假非平凡。                                                        *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================ *)
(* UpAblEps66Sum.v                                               *)
(*                                                               *)
(* 使命：本件形式化求和三性质在 enum 列表和实例上的成立：外延性     *)
(*   （逐点 real_eq 则和 real_eq）、保序性（逐点 real_le 则和        *)
(*   real_le）与加法性（逐项相加的和等于和的逐项相加）。三者即       *)
(*   S08_RealMainlineDPO 中 Section 假设 real_sum_over_S_ext /      *)
(*   real_sum_over_S_le / real_sum_over_S_add 的具体实例。           *)
(*                                                               *)
(*   本件另附 bool 二元载体（枚举 true::false::nil）上的完全        *)
(*   具体实例：求和三性质在柯西实数层 Real 上无残留抽象变量地       *)
(*   成立。                                                        *)
(*                                                               *)
(* 依赖：CW_ConstructiveWorld_219（内含 S08_RealMainlineDPO）、       *)
(*   UpReqSumD（sumd_sum_ext / sumd_sum_le / sumd_sum_add、求和      *)
(*   算子 sumd_sumf）。                                            *)
(*                                                               *)
(* 对标：mathlib Finset.sum_congr / Finset.sum_le_sum / map_sum      *)
(*   （有限和的外延性、保序性与加法性）。                           *)
(*                                                               *)
(* 构造性：全 Set 层语句（real_eq / real_le 均 Set 值谓词，语句面     *)
(*   零裸 Prop）；零承认、全 Qed；核心件 e66s_sumf 可提取。          *)
(*                                                               *)
(* 编译：Rocq 9.1 直调 coqc，cpu_guard 限核包裹。验证编译一律        *)
(*   -o 临时目录，树内 .vo 不重写；旧 .vo 仍为改后源件的合法         *)
(*   编译产物（注释不进 .vo）。                                    *)
(*                                                               *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ================= §1 求和三性质在 enum 列表和上的实例化 ========= *)
(* 语句与 S08_RealMainlineDPO 的 Section 假设 real_sum_over_S_ext    *)
(*   / real_sum_over_S_le / real_sum_over_S_add 一致，仅将求和算子   *)
(*   实例化为 e66s_sumf。                                          *)
(* ============================================================ *)
Section E66SumD.

Context (S0 : Set).
Context (enum0 : list S0).

(* 求和算子的实例：enum 列表和，透明 Definition，展开即 sumd_sumf。  *)
Definition e66s_sumf (f : S0 -> Real) : Real := sumd_sumf S0 enum0 f.

(* 性质 1（求和的外延性）：若两函数逐点 real_eq 相等，则其 enum       *)
(* 列表和 real_eq 相等。由 UpReqSumD 的 sumd_sum_ext 直接推得；       *)
(* 等词面 real_eq 与供体接口的 req 在 Real 实例下为同一名。           *)
Theorem e66s_real_sum_over_S_ext :
  forall (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (e66s_sumf f) (e66s_sumf g).
Proof.
  intros f g H.
  unfold e66s_sumf, sumd_sumf.
  induction enum0 as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Qed.

(* 性质 2（求和的保序性）：若两函数逐点满足 real_le (f s) (g s)，     *)
(* 则其 enum 列表和满足 real_le。由 UpReqSumD 的 sumd_sum_le 直接    *)
(* 推得，空表情形由 le_refl 处理，故本语句无需非空前提；序面           *)
(* real_le 与供体接口的 le 为同一名。                                *)
Theorem e66s_real_sum_over_S_le :
  forall (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (e66s_sumf f) (e66s_sumf g).
Proof.
  intros f g H.
  unfold e66s_sumf, sumd_sumf.
  induction enum0 as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Qed.

(* 性质 3（求和的加法性）：两函数逐项相加后的列表和，等于各自列表     *)
(* 和的 real_plus；由 UpReqSumD 的 sumd_sum_add 直接推得，求和次序   *)
(* 的重排由 req_plus_exchange 处理。                                *)
Theorem e66s_real_sum_over_S_add :
  forall (f g : S0 -> Real),
    real_eq (e66s_sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (e66s_sumf f) (e66s_sumf g)).
Proof.
  intros f g.
  unfold e66s_sumf, sumd_sumf.
  induction enum0 as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                   (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                   (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))
             (plus (plus (f x) (sumd_list_sum S0 f t))
                   (plus (g x) (sumd_list_sum S0 g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t)
                (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))
                (req_refl (plus (f x) (g x))) IH)
             (real_plus_swap_mid (f x) (g x)
                (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))).
Qed.

End E66SumD.

(* ============================================================ *)
(* §2 bool 载体上的完全具体实例：取 bool 为载体、true::false::nil    *)
(*   为枚举，求和三性质在柯西实数层 Real 上于完全具体的载体成立，     *)
(*   无残留抽象变量；S08 各节抽象载体 S 的 Set 层实例即落本面。       *)
(*                                                               *)
(* ============================================================ *)
Definition e66s_flag_enum : list bool := [true; false].
Definition e66s_flag_sumf (f : bool -> Real) : Real :=
  e66s_sumf bool e66s_flag_enum f.

Theorem e66s_flag_ext :
  forall (f g : bool -> Real),
    (forall s : bool, real_eq (f s) (g s)) ->
    real_eq (e66s_flag_sumf f) (e66s_flag_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_ext bool e66s_flag_enum f g H).
Qed.

Theorem e66s_flag_le :
  forall (f g : bool -> Real),
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (e66s_flag_sumf f) (e66s_flag_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_le bool e66s_flag_enum f g H).
Qed.

Theorem e66s_flag_add :
  forall (f g : bool -> Real),
    real_eq (e66s_flag_sumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (e66s_flag_sumf f) (e66s_flag_sumf g)).
Proof.
  intros f g.
  exact (e66s_real_sum_over_S_add bool e66s_flag_enum f g).
Qed.

(* ============ 提取核验 ========================================== *)
(* 本件唯一计算内容为求和载体件 e66s_sumf（enum 列表和，由列表       *)
(* 折叠定义），提取其 OCaml 输出以核验计算面。                        *)
(* 三件性质定理处于等词与序谓词层面，不属于计算内容，                 *)
(* 不进入提取输出的实质。                                          *)
(* 提取目标：e66s_G3_sumf.ml。                                     *)
Set Extraction Output Directory "_tab5_g3out".
Extraction "e66s_G3_sumf.ml" e66s_sumf.

(* 假设闭包核验：以下各定理的假设闭包应为空（Closed）。 *)
Print Assumptions e66s_real_sum_over_S_ext.
Print Assumptions e66s_real_sum_over_S_le.
Print Assumptions e66s_real_sum_over_S_add.
Print Assumptions e66s_flag_ext.
Print Assumptions e66s_flag_le.
Print Assumptions e66s_flag_add.
