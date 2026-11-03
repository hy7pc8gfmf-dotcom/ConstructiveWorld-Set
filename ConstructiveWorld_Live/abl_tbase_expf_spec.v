(* ==========================================================================)
   abl_tbase_expf_spec.v — 基座区上编批 4 施工组（F7 expf 套族 Real 特化闭形
   A 形直供件：S13／AttnDoeblin／S15／G01／UpReqFEPAttn 五宿主 11 必行）
   ── 使命：基座区存疑二审与施工说明（attn/_tbase100_存疑二审与施工说明.md
      §三 施工说明上编批 3，交付标号顺延为上编批 4＝UB4）逐行施工。沿尾百批 5
      既供件 abl_tail_supply_67.v 模板（Id 面槽 W-IDPIN-01 零输入、real_eq
      换面转写为库内现役出路的同族工艺），五段十一行：
      段一 S13_NLiveAudit 构造性指数迷你接口（件内自注 :2740，「Part C 证其
        可满足性」）三行：expf_pos:2742／expf_mono_lt:2745／expf_mono_le:2746；
      段二 AttnDoeblin 同族接口（件内自注 :470，「Part C 消解其可满足性」）
        三行：expf_pos:472／expf_mono_lt:475／expf_mono_le:476——S13/AttnDoeblin
        为 pair-③ 逐字双落（冗余卡 15 ③在案），一次施工覆盖两件；
      段三 S15_TailFEPUp RowView 两行：expf_pos:155／expf_mono_le:156；
      段四 G01_CoreMicro RowView（S15 副本，卡 15 ① 一次覆盖）两行：
        expf_pos:490／expf_mono_le:491；
      段五 UpReqFEPAttn ReqRowView 一行：expf_pos:343（Hypothesis 面）。
   ── 锚复拍登记（ UB4 组 Live 现档实拍，
      /Users/apple/Desktop/ConstructiveWorld/ConstructiveWorld_Live/，与统一
      缓存 vo_local_world_unified_0930 逐字同，cmp 实证）：五宿主槽区全部
      零漂移零勘正——S13:2740-2746／AttnDoeblin:470-476／S15:154-158／
      G01:489-493／FEPAttn:342-344，槽语句面逐字与施工说明实拍列同；根件锚＝
      uabd1x_expf@UpAblD1_expf_pack.v:28／uabd1x_expf_pos:48／
      uabd1x_expf_mono_lt:61-63／uabd1x_expf_mono_le:67-69（real_expf_realizable
      组合件体＝S13:3096-3113／AttnDoeblin:771-787 双落，existT _ cauchy_real_exp
      五字段束）。施工说明容量判订正留痕：单列「10 必行」实拍逐行清点＝11 必行
      （1.1-1.3＋2.1-2.3＋3.1-3.2＋4.1-4.2＋5.1），本件照表全数施工、零越单。
   ── W 排除与条件行降 W 登记（本件零输入零触碰，清单补录见 UB4 交付报告）：
      〔W1/W2〕S13 expf_zero:2743／expf_plus:2744 与 AttnDoeblin expf_zero:473／
      expf_plus:474 四位＝Id 面钉定槽（W-IDPIN-01 族上编域内扩展，勘 3 判例
      同形），零输入；换面出路（real_eq 读法）在役已备（tsp_expf_spec_zero_req
      ＠abl_tail_supply_67、mti_expf_zero_supply＠MixTimeChainIface），本件
      不重述（防重复律）。
      〔3.3/4.3/5.2 降 W〕expf_agree 三条件行经施工说明强制「Check 一击前置
      义务」探查件实证降 W：probe_tbex_agree_chk.v 实拍——对照组 0 过
      （tbex_fn δ-透明＝uabd1x_expf 投影形）、Check A 挂（`Unable to unify
      "cauchy_real_exp x" with "tbex_fn x"`）；根因＝real_expf_realizable
      以 Qed 收束（S13:3113／AttnDoeblin:787 双落实拍），projT1 投影无 ι-归，
      点态面定义性同一不成立；probe_tbex_agree_chk2.v 另证 5.2 闭形在施工说明
      Ordered Require 面内连细化亦不通过（典范实例
      RealInterfaceEnhancedMod.RealEnhancedReal 不在可达面，S10:12215 件内
      自注其为 Mod 隔离内实例）；且五字段 sigT 包对点态函数欠确定
      （pos＋加法同态＋单调五字段不钉死底数，expf_agree 点态义务数学上超出
      包消解力）——三行照单降 W-IDPIN 注记（Id/req 面接口义务，禁硬证），
      本件零施工零 PA 位，PA 审计段＝11 件（条件行 PA 依单移除）。
   ── 依赖：S01_BaseRing、S02_CauchyComplete、UpAblD1_expf_pack、
      S06_DiffSamplingGibbs（exp_pos_fn 定义域只读，条件行降 W 后为在册
      零使用面）、S10_KVQuantTrig（exp_pos_fn_setoid 同）、Stdlib
      Extraction——全部只读引用（UpAblD1_expf_pack 自身 Require 面经统一
      缓存只读加载，含 AttnDoeblin 组合件）；五宿主件零 Require、零字节
      不动、零级联（签名保持式：宿主槽不动，本件为槽外 A 形直供）。
   ── 查重登记：施工说明四已供件零重叠实测成立（本文件开工 grep 复核）；在役
      辖区注记——uabd1x_*（包本体，只引不重述）／tsp_expf_spec_*（尾百域
      落点 abl_tail_supply_67，与本件 tbex_* 为 alpha 同形异落点，宿主异、
      零语义增量，如实登记）／amtr_*（AMT 落点）／mti_*（MTI 落点）；池内
      组 7/8 进行中件辖区实拍核：abl_tbase_logrest.v（F6 log 桥族）与
      abl_tbase_expf_bs_feed.v（下编 5-3 expf B 型输入，宿主＝P7A/MTC/MTI）
      与本件（上编 expf_spec，宿主＝S13/AD/S15/G01/FEPAttn）零交叠；
      tbex_ 前缀族＝本件新族（池/统一缓存/Live 三面 grep 零命中实拍）；
      防重复审计批 5-4 缩口令（下编 T1C/T2b 领地）经核与本批零交集。
   ── 构造性注记：全件 Qed 真构造（exact 直引在役拆包件，N1 零注水），
      零承认式声明、零悬置前提、零经典逻辑；语句面承载位全 Set 形
      （real_lt／real_le 皆 Set 值，零 Prop 泄露、零 Id 面入语句面）；供给
      定理只使用已编内容（UpAblD1_expf_pack 拆包三件），零接口外新前提；
      11 件前提面审计取全 Closed 判据；文件尾提取探查件取 Obj.magic 计 0
      判据，另设对照命令与拆包件原身并排提取比对计数（G3 对照口径，如实
      登记禁虚报；若触提取器硬错，照池内豁免先例处置并逐条登记）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532 && cd 沙箱/现役/abl_tail_supply_pool；道闸核 rocq 进程
      ≤2 方起编；单道顺序；
      nice -19 rocq c -native-compiler no -Q /Users/apple/Desktop/
      ConstructiveWorld/vo_local_world_unified_0930 "" abl_tbase_expf_spec.v
      （统一缓存只读指向，输出 .vo 落本池 cwd；绿判四要素：EXIT=0／日志
      真错行 0（禁词锚 ^Error|Error:）／vo 头 8 字节 436f7121 00015ff4／
      vo 新于 v；第五证 rocqchk）。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置
      前提、零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpAblD1_expf_pack.
Require Import S06_DiffSamplingGibbs.
Require Import S10_KVQuantTrig.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 段〇 前置：函数实例（0.1，零 Qed）                              *)
(*   tbex_fn＝组合件签名投影的定义性转写（uabd1x_expf@UpAblD1_expf_pack:28， *)
(*   底层＝real_expf_realizable@AttnDoeblin:771 的 projT1 投影）。       *)
(* ============================================================ *)

Definition tbex_fn : Real -> Real := uabd1x_expf.

(* ============================================================ *)
(* 段一 S13_NLiveAudit 三行（lt/le 面槽 Real 特化闭形；Id 面          *)
(*   expf_zero:2743／expf_plus:2744 两槽＝W1 排除位，零输入）          *)
(* ============================================================ *)

(* ---- 1.1 逐点严格正（expf_pos:2742 lt 面槽读法）                 ---- *)
Theorem tbex_s13_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 1.2 严格单调（expf_mono_lt:2745 lt 面槽读法）               ---- *)
Theorem tbex_s13_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 1.3 保序（expf_mono_le:2746 le 面槽读法；Or 析取两支已在     ---- *)
(* ----      组合件内逐支消解，S13:3096-3112＋:65-66 件内注）        ---- *)
Theorem tbex_s13_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ============================================================ *)
(* 段二 AttnDoeblin 三行（与 S13 pair-③ 逐字双落，冗余卡 15 ③：     *)
(*   一次施工覆盖两件；Id 面 expf_zero:473／expf_plus:474 两槽＝     *)
(*   W2 排除位，零输入）                                            *)
(* ============================================================ *)

(* ---- 2.1 逐点严格正（expf_pos:472；同 1.1 形）                   ---- *)
Theorem tbex_ad_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 2.2 严格单调（expf_mono_lt:475；同 1.2 形）                 ---- *)
Theorem tbex_ad_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 2.3 保序（expf_mono_le:476；同 1.3 形）                     ---- *)
Theorem tbex_ad_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ============================================================ *)
(* 段三 S15_TailFEPUp RowView 两行（节 :139-148 Context {RI}{SS}{SO} *)
(*   抽象位，本件供给形＝R:=Real 特化闭形；expf_agree:158＝条件行，   *)
(*   经前置 Check 实证降 W，见头注〔3.3/4.3/5.2 降 W〕登记）          *)
(* ============================================================ *)

(* ---- 3.1 逐点严格正（expf_pos:155；同 1.1 形）                   ---- *)
Theorem tbex_s15_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 3.2 保序（expf_mono_le:156；同 1.3 形）                     ---- *)
Theorem tbex_s15_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ============================================================ *)
(* 段四 G01_CoreMicro RowView 两行（S15 副本，卡 15 ① 一次覆盖；     *)
(*   expf_agree:493＝条件行，同 3.3 降 W 处置）                      *)
(* ============================================================ *)

(* ---- 4.1 逐点严格正（expf_pos:490；同 1.1 形）                   ---- *)
Theorem tbex_g01_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 4.2 保序（expf_mono_le:491；同 1.3 形）                     ---- *)
Theorem tbex_g01_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ============================================================ *)
(* 段五 UpReqFEPAttn ReqRowView 一行（RIS 面 :328-344，件头 :324-327 *)
(*   自证 expf_agree 换 req 签名；expf_agree:344＝条件行，经前置     *)
(*   Check 实证降 W，见头注登记）                                    *)
(* ============================================================ *)

(* ---- 5.1 逐点严格正（Hypothesis expf_pos:343 lt 面槽读法；       ---- *)
(* ----      同 1.1 形）                                            ---- *)
Theorem tbex_fepa_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ============================================================ *)
(* 六、审计段：11 定理前提面逐件判读（名清单＝Qed 计数＝PA 语句数，   *)
(*   零差；条件行 3.3/4.3/5.2 依单降 W 后 PA 位移除）                 *)
(* ============================================================ *)
Print Assumptions tbex_s13_expf_pos.
Print Assumptions tbex_s13_expf_mono_lt.
Print Assumptions tbex_s13_expf_mono_le.
Print Assumptions tbex_ad_expf_pos.
Print Assumptions tbex_ad_expf_mono_lt.
Print Assumptions tbex_ad_expf_mono_le.
Print Assumptions tbex_s15_expf_pos.
Print Assumptions tbex_s15_expf_mono_le.
Print Assumptions tbex_g01_expf_pos.
Print Assumptions tbex_g01_expf_mono_le.
Print Assumptions tbex_fepa_expf_pos.

(* ============================================================ *)
(* 七、提取检验区：判据件（计算承载位）＋11 定理＋对照命令            *)
(*   命令甲＝判据件 tbex_fn 单抽（纯计算承载位，判据 Obj.magic 计 0；  *)
(*   AttnDoeblin:791-792 同源提取先例在档）；                        *)
(*   命令乙＝11 定理全量；命令丙＝对照（uabd1x_expf 拆包五件原身＋   *)
(*   函数原身），乙丙计数比对＝本件零新增口径（G3 对照实验口径：     *)
(*   Obj.magic 非零须分解归桶，本件语句面引入逐处归因，如实登记      *)
(*   禁虚报）。施工说明原定三代表件之 tbex_fepa_expf_agree 已降 W，    *)
(*   代表位由 tbex_fepa_expf_pos（段五唯一在件）顶替，留痕。          *)
(* ============================================================ *)
Recursive Extraction tbex_fn.
Recursive Extraction tbex_s13_expf_pos tbex_s13_expf_mono_lt
  tbex_s13_expf_mono_le tbex_ad_expf_pos tbex_ad_expf_mono_lt
  tbex_ad_expf_mono_le tbex_s15_expf_pos tbex_s15_expf_mono_le
  tbex_g01_expf_pos tbex_g01_expf_mono_le tbex_fepa_expf_pos.
Recursive Extraction uabd1x_expf uabd1x_expf_pos uabd1x_expf_zero
  uabd1x_expf_plus uabd1x_expf_mono_lt uabd1x_expf_mono_le.

(* 终验实测登记（ UB4 组如实登记禁虚报）：
   编译 EXIT=0；日志真错行（^Error|Error:）计 0；11 件 Print Assumptions 全
   Closed（计 11＝Qed 计数零差，Axioms 段计 0）；全日志 Obj.magic 计 0——
   判据件单抽、11 定理全量、对照（拆包五件原身＋函数原身）三条提取命令皆
   零 Obj.magic，提取判据取强口径达成；提取器按旁路不透明设定访问了依赖
   闭包内既证定理体（标准告警 extraction-opaque-accessed 计 3，池内 64/67
   号件同形，仅告警面、非承认面）；vo 头 8 字节 436f7121 00015ff4；
   vo 新于 v；rocqchk 第五证 EXIT=0（Modules were successfully checked，
   11 语句全数在查）；编译产物已依律清池（.vo/.glob/.vok/.vos）。 *)
