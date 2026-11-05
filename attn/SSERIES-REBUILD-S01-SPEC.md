# SSERIES-REBUILD-S01-SPEC — S 系重建役 · S01 输入规格书（骨架）

> **状态**：骨架（skeleton），随 `#C-SREBUILD-0` 立卷（2026-11-05，分支
> `rebuild/sseries-s01-informative`，基线 main@7b3ced9）。
> 波次计划（§5）为占位；设计席产物（§6）＝`attn/_s01_v2_design.md`（随本分支
> 入卷）与裁勘席产物（§7）＝钉版规范 commit `ca315c0`
> （`attn/_natle_site_inventory.md`·CENSUS-CANON-GEN2），联络员搬运补入骨架。
> **政策锚**：`CONSTRAINTS.md` §11「Prop-face extraction policy — consumption
> dichotomy」（本 commit 起生效）——data-carrying（(a) 类·informative 载体强制·
> `__` 擦除=violation）vs proof-bridge（(b) 类·Prop 面合法·必须入 proof-bridge
> registry·`__` 擦除=accepted-not-violation）二分判据。

## 1. 上位裁定（用户裁定 20261105，以裁定原文为准）

1. **S 系非正典**：S01–S15 现状禁充正典/判据；判据唯一合法来源＝第一手控制实验＋非 S 系判例
   （`abl_qpoly_divmod_gen` `qpg_degge1` `@Id` bool 形 `abl_qpoly_divmod_gen.v:82`；
   `UpReqSymplecticBridge` L304 `Qle_to_QleT'` 桥形；
   `UpReqAlign3.v:91-99` Notation 形；
   S02 `qeqT_imp_qeq`／`z2v_idS_eq` S01-Id-to-eq 桥）。
2. **甲方案（plan A）**：S01 NatLe 族重建时**原生 informative 重铸**（非补丁形），
   消费者一次重写、零双付。
3. **验收**：红线律 4a/4b/4c/4d **全梯终判**——可提取→可执行→能用（实跑输出对表·
   禁 exit 0 充能料证）→好用（性能合格线·卡顿同罪·例外唯登记册四件套）。
4. **PR 制**：禁直 push main。

## 2. 重建输入规格书指针（权威底本）

- **总账／重建输入规格书**：`/Users/apple/Desktop/_tsetpkg_20261104/_s-series-cleanse-ledger-20261105.md`
  - §「★重建输入规格书（20261105 用户裁定·甲方案＋终判阶梯锁定）」＝权威底本
    （4a–4d 阶梯 NatLe 具体化表＋四缺口＋预算并入职）。
  - §「S01 种子债登记（20261105 升级裁决·重建役头号种子）」＝种子债账。

## 3. S01 种子债事实面（2026-11-05 本席在 rebuild worktree 第一手复核）

| 项 | 值 | 取证 |
|---|---|---|
| 位点 | `NatLe_drop`＝`ConstructiveWorld_Live/S01_BaseRing.v:91`；`NatLe_lift`＝`:100` | worktree grep（本日实跑） |
| 提取面擦除证据 | `val coq_NatLe_drop : __`（**仅 drop 擦除**；`NatLe_lift` 提取为 `nat -> nat -> coq_NatLe` informative 形——伴生半泄露，逐点判归裁勘席） | `_wt93_ssa/_gate7probe_S01_work/_gate7probe_S01_BaseRing.mli:38`／`:40`（本日 sed 实读；全提取体存活件＝同工作面 `S01_BaseRing.ml:52-62`） |
| gate7 magic 尺度 | 0/0（不阻闸·深层 Prop 泄漏） | 总账 §S01 种子债登记 |
| 已验证补丁（**仅语义参照·非施工蓝本**） | `_wt93_ssa/_gate7probe_S01_work/_s01_natle_bridge_rewrite.patch.txt`（compile rc=0／probe magic 0/0 informative／PA 99 Closed／gate4 PASS＋gate6 GREEN） | 本日 ls＋head 实读；**注**：总账所记 `ConstructiveWorld_Live/` 前缀路径不存在，以本实路径为准 |
| 消费位点与闭包（**Gen2 正典**） | **2,059 消费位点（drop 1,033＋lift 1,024＋DEF 2）／消费文件 103／下游 Require 闭包 353 件（宇宙=order.txt 375）；lift 提取活体 176 处/44 模块·drop=0；族形 apply-fwd 936＋apply-in 351＋term-syntax 660（＋bare 94＋ltac-embed 14）** | Gen2 程序化普查正典·钉版规范 commit `ca315c0`（`attn/_natle_site_inventory.md`·数据源 `_census_extlib.json`＋`_natle_sites_v3.json`）；上役 Gen1 总账口径（355/376/2,147·drop 1,084＋lift 1,069·apply 前置 560＋apply-in 332＋term 级 455）已存照作废、禁作验收口径 |
| 三硬核消费者 | `ConstructiveWorld_Live/b1_denom_control.v:80`／`abl_Pr_core_01.v:148`／`S02_CauchyComplete.v:447` | worktree sed 逐行实读（本日） |
| 零适配收敛形 | 双向第一手排除（保旧签名=漏必留；换 Set 面=消费者 lia 必断）——两约束数学互斥（旧形下成立；桥对接口形下已解除——钉版规范 `ca315c0` §三硬核总评） | 总账 §S01 种子债登记 |

## 4. 原则约束（施工禁则，承 CONSTRAINTS.md §11）

- (a) 类语句（信息位消费）一律 informative 载体（bool/`Id` 形），`__` 擦除＝violation；
- (b) 类语句（纯证明位消费）Prop 面合法但逐条入 proof-bridge registry（消费位证据在同 PR）；
- 判据引用只认第一手控制实验＋非 S 系判例；S 系现状禁充判据；
- 一切编译经 cpu_guard 包裹（9.3 通路见任务书）；禁直 push main；禁 `git add -A`。

## 5. 波次计划（**占位**——设计席产物，联络员补入）

<!-- 占位：波次表（波次｜范围｜交付物｜验收梯级｜证据面），W0 勘形/adjudication 起步，后续波次随设计席产物落定 -->

## 6. 重建设计（**占位**——设计席产物，联络员补入）

<!-- 占位：NatLe 族 informative 载体形（bool/Id 原生接口）、Id→Prop 消去桥对
     （正典判例形：S02 qeqT_imp_qeq／abl_z2_valbridge z2v_idS_eq）、
     2,059 消费位点「单行桥调用」机械形（Gen2 正典·钉版规范 ca315c0）、
     三硬核降阶案、性能线（4d）定标 -->

## 7. 位点 adjudication（**占位**——裁勘席产物，联络员补入）

<!-- 占位：NatLe_lift（值级信息位真消费→(a) 类·informative 载体强制——
     提取活体 176 处/44 模块，一律由新原生形恒等 exact H 形供血）／
     NatLe_drop（纯证明位→(b) 类 proof-bridge registry 登记即可——
     全库 drop 提取调用=0 机械实证）逐点判词＋全 2,059 消费位分类证据面。
     裁勘席产物已钉版：commit `ca315c0`（attn/_natle_site_inventory.md·
     CENSUS-CANON-GEN2·含 §一·乙 EXE-VERIFIED 活体表与附录 A 口径小账）。 -->

## 8. 验收与交割

- 一切产出按 4a→4d **全梯第一手终判**（官方法全名普查＋ocamlc＋样例实跑输出对表＋
  性能线入档）；任一层不达＝禁标绿禁冻完成；卡顿/超线无登记＝违规。
- 交割走 PR 制；本分支 `rebuild/sseries-s01-informative`，本地 commit 不 push。
