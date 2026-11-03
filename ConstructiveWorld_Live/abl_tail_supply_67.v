(* ==========================================================================)
   abl_tail_supply_67.v — 批五段：F4 指数族槽 Real 特化闭形供给合件
   ── 使命：上编 F4 指数族 17 槽（P7BoundedSoftmaxDeep 段三 :169-174 六位＋
      段七 :381-383 三位；UpAblP7_WallEpsChain_B 节二 :890-894 五位＋节三
      :994-996 三位）按语句面逐槽分拣后施工：语句面出现 Id 型钉定的五位
      （expf_zero 三位＝P7B:171/WallEps:892/:995、expf_plus 两位＝P7B:172/
      WallEps:893）系 W-IDPIN-01 清单在册的非典范表示接口义务位，本件零输入、
      零触碰；其余 real 面八位（lt/le 类槽：pos 三位＋mono_lt 三位＋mono_le
      两位）与零/加法位的 real_eq 读法，以 AttnDoeblin real_expf_realizable
      组合件经 UpAblD1_expf_pack 拆包五件逐字转写供出——函数实例
      tsp_expf_spec_fn 一件＋投影转写五件（pos/zero_req/plus_req/mono_lt/
      mono_le）＋使用节逐节组封四件（段三束/段七束/节二束/节三束）＝九件 Qed。
   ── 依赖：S01_BaseRing、S02_CauchyComplete、UpAblD1_expf_pack、Stdlib
      Extraction——全部只读引用（UpAblD1_expf_pack 自身 Require 面经加载器
      只读取统一缓存，含 AttnDoeblin 组合件）；使用件 P7BoundedSoftmaxDeep
      与 UpAblP7_WallEpsChain_B 零 Require、零字节不动、零级联。
   ── 对标行：组合件＝real_expf_realizable@AttnDoeblin:771；拆包五件＝
      uabd1x_expf@:28／uabd1x_expf_pos@:48／uabd1x_expf_zero@:52／
      uabd1x_expf_plus@:56／uabd1x_expf_mono_lt@:61／uabd1x_expf_mono_le@:67
      （UpAblD1_expf_pack.v）；逐字引用形工艺＝uabl_attn_full_instance
      Part A（req 面五行，Id 面槽取条件形由使用方提供实例的在役约定）；
      组封形＝uabd1x_pack_fields@UpAblD1_expf_pack:31（Set 层 And 束）；
      配方细节＝池内 _log 配方笔记（）。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑；
      语句面承载位全 Set 形（real_eq／real_lt／real_le／And 皆 Set 值，
      零 Prop 泄露）；供给定理只使用已编内容（组合件与拆包五件），零接口外
      新前提；九定理前提面审计取全 Closed 判据；文件尾提取探查件取 Obj.magic
      计 0 判据，另设对照命令与拆包五件原身并排提取比对计数（如实登记禁虚报；
      若触提取器硬错，照池内豁免先例处置并逐条登记）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      cd 沙箱/现役/abl_tail_supply_pool；道闸核 rocq 进程数 ≤1 方起编；
      单道顺序；ulimit -s 65532；
      nice -19 rocq c -native-compiler no -Q /Users/apple/Desktop/
      ConstructiveWorld/vo_local_world_unified_0930 "" abl_tail_supply_67.v
      （统一缓存只读指向，输出 .vo 落本池 cwd；绿判四要素：EXIT=0／
      日志真错行 0／vo 头 8 字节 436f7121 00015ff4／vo 新于 v）。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpAblD1_expf_pack.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 一、指数函数实例与投影转写五件（Real 面逐字转写，零重证）         *)
(*   函数实例＝组合件签名投影（uabd1x_expf@UpAblD1_expf_pack:28      *)
(*   的定义性转写，底层＝cauchy_real_exp@AttnDoeblin 经              *)
(*   real_expf_realizable:771 的 sigT 组合件 projT1 投影）；          *)
(*   五件证路全部 exact 直引拆包五件（:48/:52/:56/:61/:67）。         *)
(*   零/加法两件取 real_eq 读法——其 Id 面槽形（P7B:171/:172、        *)
(*   WallEps:892/:893/:995）系 W-IDPIN-01 清单在册的接口义务位，      *)
(*   本件零输入；real_eq 读法转写即库内现役的换面供给出路             *)
(*   （uabl_attn_full_instance Part A 在役先例同款）。                *)
(* ============================================================ *)

Definition tsp_expf_spec_fn : Real -> Real := uabd1x_expf.

(* ---- 转写一：逐点严格正（pos 槽 Real 特化闭形；P7B:170/:382、 ---- *)
(* ----      WallEps:891 的 lt 面槽读法）                          ---- *)
Theorem tsp_expf_spec_pos : forall x : Real, real_lt real_zero (tsp_expf_spec_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 转写二：零点幺等（zero 槽 real_eq 读法）                    ---- *)
Theorem tsp_expf_spec_zero_req : real_eq (tsp_expf_spec_fn real_zero) real_one.
Proof. exact uabd1x_expf_zero. Qed.

(* ---- 转写三：加法同态（plus 槽 real_eq 读法）                    ---- *)
Theorem tsp_expf_spec_plus_req : forall a b : Real,
  real_eq (tsp_expf_spec_fn (real_plus a b))
          (real_mult (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)).
Proof. exact uabd1x_expf_plus. Qed.

(* ---- 转写四：严格单调（mono_lt 槽 Real 特化闭形；P7B:173、        ---- *)
(* ----      WallEps:894/:996 的 lt 面槽读法）                      ---- *)
Theorem tsp_expf_spec_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 转写五：保序（mono_le 槽 Real 特化闭形；P7B:174/:383 的      ---- *)
(* ----      le 面槽读法；Or 析取两支已在组合件内逐支消解）          ---- *)
Theorem tsp_expf_spec_mono_le : forall a b : Real,
  real_le a b -> real_le (tsp_expf_spec_fn a) (tsp_expf_spec_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ============================================================ *)
(* 二、使用节逐节组封四件（Set 层 And 束，成员按各节槽现档序）      *)
(*   每束＝对应使用节指数性质槽全单的 Real/req 读法证书，             *)
(*   成员面注记：pos/mono_lt/mono_le 位＝lt/le 面槽的 Real 特化喂形；  *)
(*   zero_req/plus_req 位＝Id 面槽的 real_eq 读法换面转写（在役       *)
(*   换面出路件，非 Id 面槽本体的语句面消解）。                       *)
(* ============================================================ *)

(* ---- 束一：P7BoundedSoftmaxDeep 段三（P7DNoSwap 节，:169-174）      ---- *)
(*   性质槽五位全单：pos:170／zero:171（req 读法）／plus:172（req 读法）／ *)
(*   mono_lt:173／mono_le:174；expf 本体 :169 为参数位，不在束内。        ---- *)
Theorem tsp_p7d_noswap_expf_certs :
  And (forall x : Real, real_lt real_zero (tsp_expf_spec_fn x))
      (And (real_eq (tsp_expf_spec_fn real_zero) real_one)
      (And (forall a b : Real,
            real_eq (tsp_expf_spec_fn (real_plus a b))
                    (real_mult (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)))
      (And (forall a b : Real,
            real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b))
           (forall a b : Real,
            real_le a b -> real_le (tsp_expf_spec_fn a) (tsp_expf_spec_fn b))))).
Proof.
  exact (pair tsp_expf_spec_pos
           (pair tsp_expf_spec_zero_req
           (pair tsp_expf_spec_plus_req
           (pair tsp_expf_spec_mono_lt tsp_expf_spec_mono_le)))).
Qed.

(* ---- 束二：P7BoundedSoftmaxDeep 段七（P7DKernelBand 节，:381-383） ---- *)
(*   性质槽两位：pos:382／mono_le:383；expf 本体 :381 为参数位。      ---- *)
Theorem tsp_p7d_kernelband_expf_certs :
  And (forall x : Real, real_lt real_zero (tsp_expf_spec_fn x))
      (forall a b : Real,
       real_le a b -> real_le (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)).
Proof.
  exact (pair tsp_expf_spec_pos tsp_expf_spec_mono_le).
Qed.

(* ---- 束三：UpAblP7_WallEpsChain_B 节二（P7aKappaPackage，:890-894） ---- *)
(*   性质槽四位全单：pos:891／zero:892（req 读法）／plus:893（req 读法）／ *)
(*   mono_lt:894；expf 本体 :890 为参数位。                              ---- *)
Theorem tsp_walleps_kappa_expf_certs :
  And (forall x : Real, real_lt real_zero (tsp_expf_spec_fn x))
      (And (real_eq (tsp_expf_spec_fn real_zero) real_one)
      (And (forall a b : Real,
            real_eq (tsp_expf_spec_fn (real_plus a b))
                    (real_mult (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)))
           (forall a b : Real,
            real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)))).
Proof.
  exact (pair tsp_expf_spec_pos
           (pair tsp_expf_spec_zero_req
           (pair tsp_expf_spec_plus_req tsp_expf_spec_mono_lt))).
Qed.

(* ---- 束四：UpAblP7_WallEpsChain_B 节三（P7aSbInst，:994-996）     ---- *)
(*   性质槽两位：zero:995（req 读法）／mono_lt:996；                   ---- *)
(*   expf 本体 :994 为参数位。                                          ---- *)
Theorem tsp_walleps_sb_expf_certs :
  And (real_eq (tsp_expf_spec_fn real_zero) real_one)
      (forall a b : Real,
       real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)).
Proof.
  exact (pair tsp_expf_spec_zero_req tsp_expf_spec_mono_lt).
Qed.

(* ============================================================ *)
(* 三、审计段：九定理前提面逐件判读（名清单＝Qed 计数＝PA 语句数，零差） *)
(* ============================================================ *)
Print Assumptions tsp_expf_spec_pos.
Print Assumptions tsp_expf_spec_zero_req.
Print Assumptions tsp_expf_spec_plus_req.
Print Assumptions tsp_expf_spec_mono_lt.
Print Assumptions tsp_expf_spec_mono_le.
Print Assumptions tsp_p7d_noswap_expf_certs.
Print Assumptions tsp_p7d_kernelband_expf_certs.
Print Assumptions tsp_walleps_kappa_expf_certs.
Print Assumptions tsp_walleps_sb_expf_certs.

(* ============================================================ *)
(* 四、提取检验区：判据件（计算承载位）＋九定理＋对照命令               *)
(*   命令甲＝判据件 tsp_expf_spec_fn 单抽（纯计算承载位，判据           *)
(*   Obj.magic 计 0；AttnDoeblin:792 同源提取先例在档）；               *)
(*   命令乙＝九定理全量；命令丙＝对照（拆包五件原身＋函数原身），        *)
(*   乙丙计数比对＝本件零新增口径（如实登记禁虚报）。                    *)
(* ============================================================ *)
Recursive Extraction tsp_expf_spec_fn.
Recursive Extraction tsp_expf_spec_pos tsp_expf_spec_zero_req
  tsp_expf_spec_plus_req tsp_expf_spec_mono_lt tsp_expf_spec_mono_le
  tsp_p7d_noswap_expf_certs tsp_p7d_kernelband_expf_certs
  tsp_walleps_kappa_expf_certs tsp_walleps_sb_expf_certs.
Recursive Extraction uabd1x_expf uabd1x_expf_pos uabd1x_expf_zero
  uabd1x_expf_plus uabd1x_expf_mono_lt uabd1x_expf_mono_le.

(* 终验实测登记（如实登记禁虚报）：
   编译 EXIT=0；日志真错行计 0；九件 Print Assumptions 全 Closed（计 9＝
   Qed 计数零差）；全日志 Obj.magic 计 0——判据件单抽、九定理全量、对照
   （拆包五件原身＋函数原身）三条提取命令皆零 Obj.magic，提取判据取强口径
   达成（AttnDoeblin:791-792 同源提取先例在档）；coqchk 第五证 EXIT=0 且
   环境摘要在案判公理位为 none（空）。
   提取器按旁路不透明设定访问了依赖闭包内既证定理体（标准告警
   extraction-opaque-accessed，池内 64 号件同形），仅告警面、非承认面。 *)
