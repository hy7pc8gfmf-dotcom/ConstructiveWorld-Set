(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   abl_S05_log_lt_mono（原 L51，1 句玩具证）                            *)
(*   abl_S05_inv_pos_lt_contra（原 L37，2 句玩具证）                      *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 勘定：①证明体与原件现版逐字同文；②原件所引包裹成员不在本编译闭包，②证明体改引同层同面现役定理 real_log_lt_mono 直取（S07:6663，语句面逐字不动）；①节六个 Let 依基座件名 S01_BaseRing 全限定（G05 记号面冲遮 S01 投影名，世系差）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 源版本：S05_AlignmentGRPO.v（原树零改，只读依存）                                *)
(*                                                              *)
(*   ① L2303 inv_pos_lt_contra —— 抽象 RI 层直接代入（N1）                *)
(*      实例化消解件：ipl_inv_pos_lt_compat@InvPosLtCompat.v:68（同层同形；      *)
(*      源版本仅名异形同：参分组 (a b) 括号形，语句逐字同）                  *)
(*      依存位：S05:2330（sigmoid_strict_inc 构造体）                    *)
(*   ② L2314 log_lt_mono —— Real 层实例供给（N3）                     *)
(*      原记 G05 包裹成员不在本编译闭包（G05_LogSmall 世系差）；现役供家        *)
(*      real_log_lt_mono@S07:6663（cw_log 面经 real_log@S07:8011 透明定义换算；同层同面，语句逐字同） *)
(*      依存位：S05:2373（sigmoid_strict_inc 第三步）                    *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层 / 公理面零新增 / 原树零改 /          *)
(*       独立附属引理不并入原模块 / 前缀 abl_ 本件内防撞。               *)
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
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import InvPosLtCompat.
Require Import G05_LogSmall.

(* ################ ① inv_pos_lt_contra（源版本 L2303-2305 逐字参数形） ################ *)
(* 源版本节：Section Alignment（L24 起），抽象 RI 层；副本节与 InvPosLtCompat 同款。 *)
Section AblS05Alignment.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let mult := @S01_BaseRing.mult RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.

Theorem abl_S05_inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

End AblS05Alignment.

(* ################ ② log_lt_mono（源版本 L2314-2315 逐字参数形；Real 层实例供给形） ####### *)
(* 源版本语句为抽象 RI 层 total-log 形（Section Alignment）；实例供给取现役 Real 层 real_log  *)
(* 见证形（S07 real_log_lt_mono 直取；cw_log 结论面仅透明定义换算差；语句面逐字同）。        *)
Theorem abl_S05_log_lt_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (real_log_lt_mono a b Ha Hb Hlt).
Qed.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions abl_S05_inv_pos_lt_contra.
Print Assumptions abl_S05_log_lt_mono.
