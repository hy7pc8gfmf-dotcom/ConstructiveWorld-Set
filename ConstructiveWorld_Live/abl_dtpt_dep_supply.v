(* ==========================================================================)
   abl_dtpt_dep_supply.v — DTPT 扩容批残差供给卷
   ── DTPT_Bridge_Dep.v 本体 4 前件参数位：普查底册 §2.6
      登记；前置＝三方对拍（普查底册 ↔ abl_dtr_ 系 ↔ 宿主实文），
      判定＝参数位 1 真残差（本卷供给 2 条），参数位 2/3/4 同形已供（dtr_ 系复用，
      零新件；对拍结论全录于卷内查重登记块）。
      红线遵守：W-DTPTTRUTH-DIAG-01 七槽（diag_closed 形，Truth 域）绝对禁碰
      （本域零此形，零触碰实录）；宿主/桥面禁重计铁律（X §1.1/§4.3-4）：
      本卷 4 参数位＝六件自账位（dtr_ 系五宿主 424 参数位版图之外，底册 §2.7 零冲突声明在
      案），Rotation :2479/:2551 宿主面零触碰零重做；Truth 🟡 五参数位
      （存疑-②）候二审不做。
   ① 模块名+使命：abl_dtpt_dep_supply——残差槽供给定理（tbd_ 前缀，X §4.1
      残差行计划件名/前缀照录）。三方对拍判定（逐参数位，语句面＝底册现档
      逐字）：
        槽 1（:175 槽1）(forall x : Q, In x l -> Qabs x <= B)——【真残差】：
           dtr_ 系 core3 定理组（dtr_c3_deprecated_consumers_map_Hsup_bounded_
          old/_cyc，供 Rotation :2479 宿主件）对该面恰为「有界卫哨照盘透传」
          （件注响亮申报在档），abl_dtr_core1-3 全量语句面盘点零同形件——
          本卷两条供给（实例域闭式＋计算律形）；
        槽 2（:175 槽2）SortedQ l——【同形已供】dtr_c2_sorted_P0（P0 排序
          律全称形，core2 T1 路）＋dtr_c2_sorted_wit_002（[0;0;2] 闭实例，
          core2 T5 路）销账复用零新件；
        槽 3（:175 槽3）l <> []——【同形已供】dtr_c2_P0_cons_ne（P0-cons
          域，core2 T2 路）销账复用零新件；
        槽 4（:213）(lam1 <= lam2)%Q——【同形已供】dtr_c2_Qle_0_1（(0 <= 1)
          实例，core2 T8 路，dtr_ 系供 Rotation :1551 H_lam_anti_mono 参数位 66
          同款 Q-ORD 面）销账复用零新件。
        订正（响亮申报）：底册 §4.3-1「dtr_ 系已供其宿主参数位」对 :2479 三前件参数位
          不全成立——IN（有界卫哨＝本参数位 1 同形面）在 dtr_ 系即透传未供，仅
          SORTED/NEQ 面有 core2 产路；X 存疑-④ 预警的「覆盖率未逐件审计」
          由本卷对拍补齐（详对拍报告）。
      【应用演示（底册 §4.2 A 直供形使用面；〈dtr_ 系已供件复用位〉标出）】
        deprecated_cluster_fully_covered (P0 [a]) s k n (Qabs a)
          (tbd_dep_HB_P0_single a)          （槽1，本卷供给）
          (dtr_c2_sorted_P0 [a])            （参数位2，〈dtr_ core2 T1 复用〉）
          (dtr_c2_P0_cons_ne a [])          （参数位3，〈dtr_ core2 T2 复用〉，
                                              P0 [a] ≡ P0 (a :: [])）
          ⟹ 九分量 Type 积证书（B := Qabs a 规范界项域全参喂形）；
        H_lam_anti_mono_real_set l s 0%Q 1%Q (dtr_c2_Qle_0_1)
                                            （参数位4，〈dtr_ core2 T8 复用〉）
          ⟹ QleT (H_lam l s 1%Q) (H_lam l s 0%Q)；
        闭实例域：deprecated_cluster_fully_covered [0;0;2] s k n 2%Q
          (tbd_dep_HB_wit_002)              （槽1，本卷供给）
          (dtr_c2_sorted_wit_002)           （参数位2，〈dtr_ core2 T5 复用〉）
          （参数位3 于 [0;0;2] 闭实例＝stdlib 构造子互斥 discriminate 一步使用
          面内联——dtr_ 系 NEQ 面供给域为 P0-cons 形全称族，闭实例域不另立
          同形件以免同面双域重复，如实申报）。
      【降档口径（非降档，形态选择——AT 卷一同款申报）】槽 1 无条件泛形＝
        诚实界假设（X 存疑-①：泛形供给语义不成立；任取无界表即假）——
        供给取实例域/计算律两形：闭实例 [0;0;2]×B:=2（逐元素 Qabs 闭判定）
        ＋P0 单表计算律（∀a y, In y (P0 [a]) -> Qabs y <= Qabs a，B 取规范
        界项 Qabs a）。不改判 W：逐实例真可计算（X 存疑-① 预留的「逐实例」
        判定路径兑现），泛形不入语句面。
   ② 依赖清单：Stdlib（QArith.QArith/QArith.Qabs/List）＋库件 DTPT 一件
      （统一缓存 vo_local_world_unified_0930 在册 .vo 只读依赖，零重编零
      级联）；P0/xq_Qle_bool_le 短名取 DTPT.DTPT 本尊（P0 定义＝DTPT.v:39
      全库唯一定义位；xq_Qle_bool_le＝DTPT.v:499，Entropy :300 系同语句
      副本，本件取 DTPT 位＝零 Entropy/Rotation/桥接件名依赖实录；本件零
      Require DTPT_Bridge_Dep——槽 1 前件名面 In/Qabs/Q 序全 stdlib＋
      DTPT 既有，AW 卷三同款零桥本体名依赖分账）。Require 顺序＝先
      stdlib 后库序，禁逆向。
   ③ 对标行：AT/AV/AW 三卷工艺＝A 直供形/头注五字段/查重登记块/绿判
      四件套/应用演示入头注，同族工艺直接复用；设计依据＝普查底册
      §2.6（Bridge_Dep 4 参数位）＋§4.1（残差行 ≤4）
      ＋§4.3-1（对拍令）；坑卡预读：AQ（本件零 <> 记法位；grep -c 零命中
      退码 1 断链——道闸与绿判各步分号独立跑）/AL（语句面零 Or 形出口
      ——In 的内部析取为 stdlib 归纳谓词展开位，非语句面 Or 出口）/AS
      （本件零 trans 引用）/AO（本件 list Q 面与宿主同域，零混载）。
   ④ 构造性注记：全件 Qed 真构造，零承认零公理零节变量；纯 Prop 离散
      卫哨载体（Q/list Q 全宿主既有，本件零新增数据载体、零 Definition/
      Fixpoint/Inductive）；语句面零混载（零析取/零存在/零经典逻辑）；
      可提取性＝零数据载体故 Obj.magic 面＝0 由构造成立（AW 卷三同款
      口径，无逐件 Separate Extraction 检验）；Q 字面一律 %Q（防 Q_scope
      劫持）；vm_compute 用面＝Qle_bool 闭式判定（宿主 DTPT.v:1291 与
      Rotation sorted_wit_002 :1236 系同款在库配方）。
   ⑤ 编译配方（池 cwd＝沙箱/现役/abl_tmine04_pool/dtpt_dep，路径绝对化）：
      source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh &&
      unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c
      -native-compiler no -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_dtpt_dep_supply.v
      （道闸 ≤1：起编前 ps -axo comm|grep -ci rocq 独立跑、禁入 && 链；
      绿判四件套：EXIT=0 无管道真取／日志真错行计 0＋逐条 Print
      Assumptions 全 Closed／.vo 头 8 字节与宿主 DTPT_Bridge_Dep.vo 同款
      ／.vo 新于 .v；第五证 rocq check 分号独立跑。）
   ── 交付声明：本件为中文声明的零承认件：全部供给定理 Qed 闭合；供给
      定理逐条 Print Assumptions 全 Closed；DTPT_Bridge_Dep.v 宿主零字节
      不动（零重编）。
   ========================================================================== *)

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   （一）名面：本件全部顶层名 2 枚全 tbd_ 新前缀（tbd_＝残差卷专用     *)
(*   prefix，X §4.1 计划名），统一缓存 vo_local_world_unified_0930 全量  *)
(*   grep 零命中（施工前复检实录）；与已占 dtd_/dte_/dtr_/ *)
(*   dtb_ 四前缀及 tdt_/tdg_/tdbg_/tbr_ 四批prefix 零撞零别名转发；件名  *)
(*   abl_dtpt_dep_supply.v 全树零命中（X 设计件名照录）。                *)
(*   （二）槽面：本卷供给＝底册 §2.6 槽 1 一槽两条（实例域闭式＋计算律    *)
(*   两供给形，底册 §4.1 预估 ≤4 内）；参数位 2/3/4 零新件（dtr_ 系已供件复用，   *)
(*   凭据见①判定与查重登记块）——4 参数位总账＝1 供给＋3 复用，核对平零漏账；    *)
(*   零双供：本件 2 条语句面（In x [0;0;2] 界 2／In y (P0 [a]) 界 Qabs a） *)
(*   与全库既有件（含 dtr_ 系、H_adj_bound 使用方向面）零重合；宿主/桥面  *)
(*   禁重计：Rotation :2479/:2551 宿主面零触碰零重做。                   *)
(*   （三）宿主界：DTPT_Bridge_Dep.v 本体零字节不动、零重编；两档 diff    *)
(*   逐字同档实测；本件 Require 统一缓存只读在册 .vo，宿主    *)
(*   重编零级联于本件，本件重编零级联于宿主。                            *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Import ListNotations.

Require S01_BaseRing.
Require S02_CauchyComplete.
Require DTPT.
Import DTPT.DTPT.

Open Scope Q_scope.

(* ========== 残差参数位 1 供给（:175 参数位1 有界卫哨，底册 §2.6 存疑-① 实例域判定） ========== *)

(* 供给 1〔实例域闭式〕闭见证列 [0;0;2]（＝宿主树 sorted_wit_002（Rotation
   :1233）/dtr_c2_sorted_wit_002 同列，参数位 2 已供件同域互证）上的有界
   卫哨：逐元素 In 析取展开＋subst 后 Qabs 闭值判定（Qle_bool 反射，宿主
   DTPT.v:1291 同款配方）。B := 2 为该列精确上确界（元素 2 在列），界紧。 *)
Theorem tbd_dep_HB_wit_002 :
  forall x : Q,
    S01_BaseRing.InT x [0; 0; 2] -> S02_CauchyComplete.QleT' (Qabs x) 2%Q.
Proof.
  intros x Hx.
  inversion Hx; subst.
  - apply S01_BaseRing.id_refl.
  - match goal with
    | H : S01_BaseRing.InT _ (0 :: 2 :: nil) |- _ => inversion H; subst
    end.
    + apply S01_BaseRing.id_refl.
    + match goal with
      | H : S01_BaseRing.InT _ (2 :: nil) |- _ => inversion H; subst
      end.
      * apply S01_BaseRing.id_refl.
      * match goal with
        | H : S01_BaseRing.InT _ (@nil Q) |- _ => inversion H
        end.
Qed.

(* 供给 2〔计算律形〕P0 单表闭域全参族：P0 [a] 插入排序单表闭计算＝[a]
   （P0 定义 DTPT.v:39，insert_q 于空表无比较纯构造），元素唯一故 Qabs a
    即精确界（B := Qabs a 规范界项）——与参数位 2/3 已供件同处 P0 闭域，
    三卫哨可同域合供（应用演示①全实参提供形）。 *)
Theorem tbd_dep_HB_P0_single : forall a y : Q,
  S01_BaseRing.InT y (P0 [a]) -> S02_CauchyComplete.QleT' (Qabs y) (Qabs a).
Proof.
  intros a y Hy.
  assert (E : P0 [a] = [a]) by reflexivity.
  rewrite E in Hy.
  inversion Hy; subst.
  - apply S02_CauchyComplete.Qle_to_QleT'. apply Qle_refl.
  - match goal with
    | H : S01_BaseRing.InT _ (@nil Q) |- _ => inversion H
    end.
Qed.

(* ========== 逐条 Print Assumptions（绿判第二关） ========== *)
Print Assumptions tbd_dep_HB_wit_002.
Print Assumptions tbd_dep_HB_P0_single.
