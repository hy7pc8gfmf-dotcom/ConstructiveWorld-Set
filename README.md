# ConstructiveWorld — 构造性数学库（Rocq/Coq）

[![Coq CI](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/workflows/coq.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

本仓库是论文《π 的构造性三表示定理》（Constructive three representations of π）配套的构造性数学库：全库在 Set 层以 `sigT` 显式见证给出存在型结论，不引入任何公理，且整链可提取。英文版见 [README.en.md](README.en.md)。

## 作者与贡献者（Authors）

| 作者 | ORCID |
|---|---|
| Baojun Wang | [0009-0001-4240-9045](https://orcid.org/0009-0001-4240-9045) |
| Guangzhao Zu | [0009-0006-7811-6638](https://orcid.org/0009-0006-7811-6638) |
| Wanlan Xia | [0009-0008-7359-044X](https://orcid.org/0009-0008-7359-044X) |
| Baiyuan Zeng | [0009-0005-9811-5598](https://orcid.org/0009-0005-9811-5598) |
| Zhinong Zhou | [0009-0001-3206-5824](https://orcid.org/0009-0001-3206-5824) |
| Xuefeng Gao | [0009-0007-9904-1599](https://orcid.org/0009-0007-9904-1599) |

## 1. 库概述

- **规模**：537 个在册模块（注册序 `ConstructiveWorld_Live/order.txt`，注册行 537 行·批次 `#R0`–`#R153`；文件无空行共 537 行，2026-11-11 实测；随注册演进而增长，以现势为准）。注册序是库的权威引用面：每个在册件一行，形如 `S01_BaseRing.v#R0-d66910`，`#` 之后为注册批次指纹；树内 `.v`（537 件）与注册序（537 行）零差集（2026-11-11 实测）。
- **内容面**：S01–S15 构造性实数与分析基座；Banach 范数与 Padé 逼近的上界需求族（`UpReqBanach*`／`UpReqPade*`）；Boltzmann/Gibbs、GRPO/DPO 对齐与熵面（S05/S06/S08/S09）；注意力链界（`Attn*`）；以及机械件伴生面（`b1_*`、`mach_fold_q`、`abl_z2/z3_pointwise`、`abl_Hqarch_*`、`fib_machine`）。
- **纯构造性**：全库不使用 `Axiom`/`Admitted`/经典逻辑；内核级 `coqchk -o` 复核口径为 `Axioms: <none>`（本仓口径要求；云端落定状态以 §2「CI 认证」行为准，不预支审计结论）。
- **Set 层 `sigT` 显式见证**：存在型结论一律给出可计算见证（有理数端点、近似根等），不停留于命题层。
- **可提取**：以 `Separate Extraction` 生成目标语言代码并机械检查 `Obj.magic` 计数为零（计数非零即示 Prop 层内容泄入提取面）。
- **「率即算法」范式**：可执行件（`Defined` 计算器）与其正确性证书（`Qed` 证明）同体共存——定理与程序是同一件东西的两面。

**姊妹仓分工**：全库完整大库（认证面 1021 件，含 π 阶梯、五常数族与 ZZ 测度路线）见 [ConstructiveWorld-Main](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main)；Main 已于 Rocq 9.3.0 完成内核全闭包收官认证（2026-11-07 run #9·`coqchk` 14 组·`Axioms: <none>`，GPG 签名 tag `GREEN-CERTIFIED-v1`——发布面详见其 README §2）。本仓为 Set 层精简注册面。

**π 支柱独立包**：π 的构造性强无理闭合已以独立 Rocq 包 [rocq-pi-leibniz](https://github.com/hy7pc8gfmf-dotcom/rocq-pi-leibniz) 发布（Leibniz 窗法·Set 载体·零公理·见证可提取），版本面 `v1.0.4`（tag 解引用 commit `e1891fce`；该包 CI 状态与本仓无涉，以 rocq-pi-leibniz 仓库页面现势为准），Zenodo 归档 DOI：[10.5281/zenodo.23656983](https://doi.org/10.5281/zenodo.23656983)（集成线，concept 23656982）；v1.0.0 批已合并进 Rocq opam 仓（rocq-prover/opam #3884），v1.0.1–1.0.4 合并式 PR [#3899](https://github.com/rocq-prover/opam/pull/3899)（supersedes #3896/#3897/#3898）状态以上游 PR 页现势为准。早期其通用逃逸窗判据引擎曾以 Issue #312／PR #313 提交上游标准库 rocq-prover/stdlib，后按维护者意见转为独立库发布路线（即上述包）。

## 2. 版本与认证记录

| 项 | 值 |
|---|---|
| 库版本 | `2f1ffbaf`（`main` 分支，2026-11-11 实测） |
| CI 认证 | 最新落定绿炉 run **#293**（2026-11-11·win+mac 双道全步绿·`COQCHK_ALL_PASS`·gate2 CLEAN 公理 0）——认证结论以 Actions 页现势为准（Actions 页为唯一现势源），本仓不预支其后任何绿。本表此前所载绿面止于 run #55（head `5293f1b`，2026-10-29）；#55 与 #293 之间的 run 状态本表不逐个追述 |
| 公理审计 | 口径要求：`coqchk -o` 全库复核须得 `Axioms: <none>`。最新绿炉落定 run #293（2026-11-11）：gate2 CLEAN 公理 0；审计结论以 Actions 页现势为准，本仓不预支其后任何审计结论 |
| 注册序 | `order.txt` 注册行 537 行·文件无空行共 537 行（`#R0`–`#R153`；2026-11-11 实测） |
| 许可 | Apache-2.0（见 `LICENSE`） |

持续集成（`.github/workflows/coq.yml`）在每次推送时执行（Windows 认证 job；macOS 观察 job `coq-build-macos` 已于 2026-11-03 解闸）：gate1 毒 token 守卫 → gate4 注释哨兵 → gate6 语句普查（红即增长）→ vo 信任缓存起步播种（fail-open）→ 全树编译（单 Live 树·order 拓扑·温控包裹）→ gate7 提取执行（红即增长）→ gate5 vo 二进制检疫（token＋digest·对照校准）→ `coqchk` 全树内核复核（共享闭包单遍·温控包裹）→ gate2 公理哨兵（块状态机解析 `coqchk` 日志判定 `Axioms: <none>`）。gate3 跨树 diff 已随 2026-10-07 单树化（#C-S00c）撤除。哨兵脚本位于 `scripts/gates/`。CI 工具链代际钉 `Welcome to Chicken 9.3.0`（Rocq 9.3.0·2026-11-02 换基）——工具链代际不等于认证结论，后者见上行 CI 认证行。

## 3. 环境前置

- **Rocq / Coq 9.3.0**（本仓 CI 代际——`.github/workflows/coq.yml` gate2 钉 `Welcome to Chicken 9.3.0`）。旧版未验证；更换验证环境后须重跑下方四步。
- **姊妹仓认证口径（交叉引用）**：ConstructiveWorld-Main 已于 Rocq 9.3.0 完成内核全闭包收官认证（tag `GREEN-CERTIFIED-v1`·`coqchk` 14 组·`Axioms: <none>`，2026-11-07）；该认证属 Main 仓，不代表本仓 CI 现势——本仓现势绿炉为 run #293（2026-11-11 落定），Set 侧认证状态以本仓 Actions 页现势为准。
- 无外部 OCaml 依赖；提取产物为普通 OCaml 源码，仅作审计对象，不要求可编译执行环境。

## 4. 复现：四步验证

与论文 §6「四步命令形态」逐字一致。以下命令在 `ConstructiveWorld_Live/` 内执行；采用 `-Q . ""` 扁平命名空间。全树驱动见 `.github/workflows/coq.yml`。

```sh
# ① 全量编译：按 order.txt 注册序逐件（本机直调；全树 driver 见 CI workflow）
rocq compile -Q . "" S01_BaseRing.v
# ② 公理审计：**审计语句即源件内逐字书写的 `Print Assumptions <语句名>.` 命令**（例：S14_B5BatchBlock.v 对 `b5d1_Heps4` 与 `b5dE_zero_le_one` 各一条），随编译自动复验，预期输出 Closed under the global context
# ③ 提取审计：Separate Extraction 产出的 .ml 中 Obj.magic 计数应为零
coqtop -q -Q . "" <件>.v            # 内执行 Separate Extraction <语句>.
grep -c Obj.magic <件>.ml           # 预期 0
# ④ 内核复核：逻辑库名取自 <件>.glob 头部（-Q . "" 下的实际前缀），勿用文件名替代
coqchk -silent -Q . "" <逻辑库名>.<件名>
```

注意事项：

- 逻辑库名**不等于**文件名。例如 `S01_BaseRing.v` 的逻辑库名是 `FS01_BaseRing`（取自 `S01_BaseRing.glob` 第 2 行）。第 ④ 步若误用文件名，`coqchk` 将报库不存在。
- 第 ① 步按 `order.txt` 行序逐件执行即满足依赖序；单件失败先行解决再续。
- 四步覆盖注册面全部在册件（现势 537 件）。

## 5. 仓库布局

本仓为单树形制：`ConstructiveWorld_vo/` 产物树已于 2026-10-07 基线裁剪（#C-S00）移除，gate3 跨树 diff 随之撤除。

| 路径 | 内容 |
|---|---|
| `ConstructiveWorld_Live/` | 源码树：全树 `.v` 源件（树内 537 件／在册 537 件，2026-11-11 实测）＋`order.txt`（537 行·无空行）＋`_CoqProject`（549 行，`-Q . ""`） |
| `order.txt` | 注册序，权威引用面。`scripts/` 留有维护用历史副本（671 行·止于 #R172 波·2026-10-07 定格）——定格早于当晚单树化与后续现注册面重建，其行数与批号序列同现注册面（#R0–#R153）不可直接对照，仅存史备查 |
| `scripts/` | 注册序维护脚本与 `scripts/gates/` 哨兵（毒 token 守卫、公理解析、注释哨兵、语句普查、vo 依赖检疫、提取执行） |
| `.github/workflows/coq.yml` | CI 全树驱动（编译＋`coqchk`＋哨兵·Rocq 9.3.0 代际钉） |
| `docs/` | 设计与规划文档 |
| `releases/` | 历史单文件合并版（220 版，见附录） |

## 6. 许可、引用与作者

- **许可**：Apache-2.0。提取产物（`.ml`/`.mli`）与源件同许可。
- **引用锚**：引用库内语句时，建议以「件名＋`order.txt` 行号＋批次指纹」定位。批次指纹随注册批固化，可用于核对所引版本。
- **姊妹仓认证发布面**：tag／Release／Zenodo 见 [ConstructiveWorld-Main](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main) README §2/§7（属 Main 仓认证面，与本文所述本仓 CI 状态相互独立）。
- **作者**：见文首「作者与贡献者」表。

## 7. 公开范围与例外

引用面所在件全量公开。现势（2026-11-11 实测）：树内 `.v`（537 件）与注册序（537 行）零差集，无在册外源件——此前注册面外的供给件已于 2026-11-08 批量入册（commit `95e7631`·message 自述补注册 31 件·去重 5 行；`git show` 实测 numstat +62 行／−6 行，其中注册行 +32 行、批次间空行 +30 行，落既有 #R0／#R97 批次、未开新批号）；10a2402b 落定时树内已有而在册序之外的 7 件（`PA_TempSoftmaxInstantiation.v`、`UpAblP6_GibbsFamilyExt.v`、`abl_div_chisq_twopoint.v`、`abl_z2_decay.v`、`u5c_pr_mertens_nat.v`、`u5c_zeta2_a1_sign11.v`、`u5c_zeta2_gapB.v`）已于 2026-11-11 经 commit `2f1ffbaf` 全数回补入册（恢复 #R97 批次锚；其 message 自述这七行属 `9a51c74` 所披露的 Pool erratum）。若后续出现未在册件，其去留随仓库公开前置批次的裁定结果在此登记；当前注册序（537 行）为唯一权威引用面，未在册件不构成库的引用承诺。

## 附录：220 版历史说明（2026-09-07/08）

以下为仓库早期（220 版）的 README 内容，描述当时的模块化布局；现已由上文的注册序体系取代，原文保留备查。

---

# ConstructiveWorld220 — 构造世界 220 版模块化代码库

220 版 = 219 基座（信任缓存）+ 28 个独立模块（本工作流 2026-09-07/08 交付件）。

## 设计目标（用户规划）
后续开发直接调用本地库 & 云端镜像的**编译产物**实现快速编译与快速锁定问题：
- 每个模块一个 .v + 一个 .vo——**坏哪块，锁哪块**（产物名 = 问题位置）
- 基座 `CW_ConstructiveWorld_219.vo` 走信任缓存，永不重编（6MB 级编译在部分上下文会阻塞）
- `docs/BLOCKERS-220.md` 记录单文件 220 版的全部阻塞点及模块级映射

## 目录
| 路径 | 内容 |
|---|---|
| `ConstructiveWorld_Live/` | 活源码树：基座 .v + 28 模块 .v + _CoqProject + build.sh |
| `ConstructiveWorld_vo/` | 产物树：同上 + 每模块 .vo（基座 .vo = 信任缓存直拷） |
| `releases/` | 单文件全量合并版 CW_ConstructiveWorld_220.v（129K 行） |
| `docs/` | 合并指引、甄别报告、阻塞图谱 |

## 编译
```bash
cd ConstructiveWorld_vo
bash build.sh        # 拓扑序增量编译（.vo 已存在则跳过）
```
全量重编基座（可选，建议在交互终端跑）：`coqc -Q . "" CW_ConstructiveWorld_219.v`

## 模块清单（28，依赖拓扑序）
第 0 层：UpCS UpHlogZ UpDebtSqrtAbs UpDebtDual UpEntropyGain UpSigMigrate UpMinP UpAlignId UpProj UpFirewall UpTempWindow UpKVEv UpAuditBridge UpPredRelax UpPLA UpStepKLM3 UpRecast UpCLQuery UpSLM
第 1 层：UpBudgetReal↑UpHlogZ · UpArchAttn↑BudgetReal · UpConstitution↑BudgetReal · UpProjBPC↑Proj · UpEvictId · UpDebtGibbsT · UpDPOLip
第 2 层：UpDissip↑Constitution · UpStopTime↑BudgetReal+Constitution

已吸收进基座（勿重编）：UpStepKL UpLogMono AttnDoeblin AttnHardLimit218 AttnSqrt UpFEP UpPPO UpGRPO(→UpGRPO219) UpExtras(→UpExtras219)
