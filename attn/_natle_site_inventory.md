# S01 NatLe_drop / NatLe_lift 全仓消费位点施工图（adjudication inventory）

- **版本=Gen2 程序化普查（唯一正典版）**：本卷全部口径数以第三源全量提取普查＋静态扫描 v3 为唯一正本——数据源 `attn/_natle_probe/_census_extlib.json`（lift 提取活体 **176 处/44 模块·drop=0**·程序化实测，本席复算同值）＋`attn/_natle_probe/_natle_sites_v3.json`（九面分账·附录 A）。**钉版 commit=本 commit（消息 CENSUS-CANON-GEN2）；SPEC／设计书／约束卷交叉引用一律指本哈希。**Gen1 上役卷账（2,147 系）仅作背景对照存照（§一注），禁作验收口径。
- 落盘：20261105 · 消费面裁勘席 · worktree `_wt93_rebuild` @ `rebuild/sseries-s01-informative`（普查运行时 HEAD=`0edada3`＝`7b3ced9`＋政策卷；该政策卷仅动 `CONSTRAINTS.md`/`attn/SSERIES-REBUILD-S01-SPEC.md` 两文件，`.v` 宇宙与 `7b3ced9` 零差）
- 宇宙：`ConstructiveWorld_Live/order.txt` **375 件**（正典·`-Q . ""` 扁平命名空间；`_CoqProject` 376 行系含 `-Q . ""` 选项行·扫描器目录口径 378 系含 3 探针件——口径全账见附录 A）· S01 消费闭包=103 消费文件＋S01 本体（下游 Require 闭包 353 件）
- 方法=三源合取：①词面 grep 全量（`grep -rn "NatLe_drop\|NatLe_lift"`）②静态扫描（注释剥除＋Proof..Qed/Defined 状态机＋宿主语句结论面 Set/Prop 判定，脚本 `attn/_natle_probe/_scan_v3.py`）③**全量提取普查**（104/104 消费模块 `Extraction Library` 一一实提，产物 `attn/_natle_probe/{extlib_ws,_extr_debris,term_ws,extlib_ws2}`，调用点 grep 机械判读）＋首尾位点亲验（206 位点逐一目验，清单 `_firstlast_verify.txt`）

## 一·总账

| 面 | 位点数 | 说明 |
|---|---|---|
| S01 消费位点合计 | 2059 | drop 1033 ＋ lift 1024 ＋ DEF 2 |
| **PB 证明位** | 1335 | drop 全体＋Prop 宿主内 lift——提取面擦除/死代码消除，零运行时足迹 |
| **INFO 信息位** | 717 | Set 宿主内 lift——提取普查 44 模块 176 处调用存活（静态 717 为含 DCE 的上界，见 §五判读列） |
| SLOT（term 面 drop） | 3 | SumInvFactEscape.v:442/462×2——ltac: 内 Prop 槽，提取后裁剪 |
| DEF 定义面 | 2 | S01_BaseRing.v:91/100 |
| 分账：DTPT 本地族 | 11 | DTPT.v（自有定义 2＋本地消费 5）＋DTPT_Truth.v（本地消费 4）＝同名异族·零本库依赖 twin（`DTPT.v:8`「零本库依赖」/`DTPT_Truth.v:21`「本件不 Require S01」头注自证） |
| 注释提及 CMT | 67 | 注释面，非消费 |
| 选择性导入清单 REQ | 17 | `Require Import S01_BaseRing (…, NatLe_drop, NatLe_lift, …)` 形——迁移需同步清单 |
| 命令提及 CMD | 3 | Check/Separate Extraction 清单提及面 |

背景卷账面数（drop 1084/lift 1069/合计 2147）系上役 Gen1 口径**存照**（token/行混合·未剔 DTPT 同名族·未剔注释），已被本 Gen2 普查取代、禁作验收口径；本席 Gen2 正典口径以本表为准：**S01 消费位点 2059（drop 1033/lift 1024/DEF 2；drop/lift 两数内含 DTPT 自有定义 DEF-LOCAL 2——成分注见附录 A）＋DTPT 本地消费分账 9＋非消费面 87（CMT 67/REQ 17/CMD 3·CMD 3＝宇宙内 1＋探针件提及 2，见下注）＝裸词面 2155 项**（2059＋9＋87＝2155·程序化复核闭合）。〔裸词面 2155 含**探针件提及 2**（`_natle_adjud_probe.v:8` CMD×2·宇宙外 untracked 探针）——分账注记，迁移预算不含此 2。〕

### 一·乙 EXE-VERIFIED 活体表（Gen2 census 正典·176/44 逐条在卷）

> 唯一权威口径＝`_census_extlib.json` 程序化实测（104/104 模块 `Extraction Library` 全提后逐模块 grep `coq_NatLe_lift (` 调用计数）；下表逐条在卷，合计 **176 处/44 模块**，drop 全库 **0** 调用。表值经本席（修复席·20261105）`json.load` 复算＝同值。§五判读列的『调用存活 N』系模块级计数的逐行标注，逐模块唯一权威值以本表为准。

| # | 模块 | 活体 lift 调用 | 备注 |
|---|---|---|---|
| 1 | DTPT_Entropy | 20 | |
| 2 | abl_cw220_step_calc | 14 | |
| 3 | abl_s06_step_calc | 14 | |
| 4 | abl_Pr_enum_02 | 12 | |
| 5 | abl_loeb_d3 | 9 | |
| 6 | UpReqCauchyLogBound | 9 | |
| 7 | BeukersLists | 8 | |
| 8 | S06_DiffSamplingGibbs | 7 | |
| 9 | S02_CauchyComplete | 7 | 硬核 γ（`real_plus` 模数传输） |
| 10 | abl_Pr_recip_sum | 6 | |
| 11 | S04_RealExpLogConv | 5 | |
| 12 | u5c_aux_natpow | 4 | |
| 13 | abl_Pr_core_01 | 4 | 硬核 β（`pr_prime_bool_true` 证书槽） |
| 14 | abl_z2_dub3 | 4 | |
| 15 | abl_Pr_euclid_03 | 3 | G5 值体（drop 槽已擦除·lift 3 活体） |
| 16 | abl_Pr_lcmdecomp_04 | 3 | |
| 17 | abl_qpoly_divmod_gen | 3 | **G4 值体正位点 :667（`Nat.le_refl` 信息位消费）** |
| 18 | Ln2Bridge | 3 | |
| 19 | DTPT_Truth | 3 | **同名异族 twin**（自有 `NatLe_lift`·`DTPT_Truth.v:21`「本件不 Require S01」）——此 3 调用非 S01 消费 |
| 20 | UpReqQExpTail | 3 | |
| 21 | abl_loeb_d3_ext | 2 | |
| 22 | abl_W9_Afamily_08 | 2 | |
| 23 | abl_Pr_lcm_eq | 2 | |
| 24 | b1_denom_control | 2 | 硬核 α（归纳阶梯） |
| 25 | abl_dmdnf2_oddlcm | 2 | |
| 26 | S12_B5RecycleSF | 2 | |
| 27 | S13_NLiveAudit | 2 | |
| 28 | Ln2Escape | 2 | |
| 29 | S10_KVQuantTrig | 2 | |
| 30 | LW2Hermite | 2 | |
| 31 | AttnHardLimit218 | 2 | |
| 32 | u5c_aux_natpow_discharge | 1 | |
| 33 | dig_machine | 1 | |
| 34 | b1_linform_machine | 1 | |
| 35 | UpReqPadeTailPos | 1 | |
| 36 | Arch_ToyR_04 | 1 | |
| 37 | S09_EntropyReal | 1 | |
| 38 | G07_KLWall | 1 | |
| 39 | BetaLower | 1 | |
| 40 | ToyR_SupplyAssembly | 1 | |
| 41 | KLWallClosed | 1 | |
| 42 | UpReqBanachCauchyD | 1 | |
| 43 | S07_RealSetoidExpLog | 1 | |
| 44 | S14_B5BatchBlock | 1 | |
| **合计** | **44 模块** | **176** | S01 域 43 模块 173 调用＋DTPT_Truth 同名异族 1 模块 3 调用；drop=0 |


## 二·两位点裁定（任务 3）

### 裁定 1：NatLe_drop ＝ **纯证明位（全部位点）·按政策①登记即可——消费面零信息位需求**

**类型论铁证**：`NatLe_drop n m h : (n <= m)%nat` 调用表达式类型恒为 Prop。Prop 型项在任何宿主任何位置都被提取器裁剪或化为 `__` 字面量——**数学上不可能存在信息位 drop 消费**。

**全量机械实证**：104/104 模块提取普查中 `coq_NatLe_drop (` 调用点 = **0**（`_census_extlib.json` 全量 grep）。
唯三 term 面 drop 位点逐一核验均为擦除形：
- `abl_Pr_euclid_03.v:106`（`Definition peu_next` 体内喂 `pr_min_factor_exists` 第二参）→ 提取体 `abl_Pr_euclid_03.ml:9-10` `let peu_next n = projT1 (pr_min_factor_exists (add (fact n) (S O)))`——**调用整体消失**（Prop 参位被裁剪）；`peu_fact1_ge2` 证明输入亦不进运行时。
- `SumInvFactEscape.v:442`/`:462`（`Fixpoint sif_enum` 内 ltac: 块 pose proof）→ Prop 槽（False_rect 证明参），提取后擦除。

**模块接口面债仍在**：S01 正本语句面 `Lemma NatLe_drop : NatLe n m -> (n<=m)%nat` 提取= `val coq_NatLe_drop : __`（存量全提取签名 `_wt93_ssa/_gate7probe_S01_work/_gate7probe_S01_BaseRing.mli:38`；运行时体同工作面 `S01_BaseRing.ml:52-55` `let coq_NatLe_drop = __`。〔漂移注记：本席开工探针 `attn/_natle_probe/S01_BaseRing.mli` 已被后续残桩探针覆盖（现 md5 `764d66880a15a0810eeb7696c4d55c76` 仅型面 77 字节·无 val 行）——证据链以 _wt93_ssa 存活件为准，详见 §六.8〕）——这是 S01 自身语句面擦除（4a 失名），属重建役语句面 informative 重铸范围（甲方案已覆盖），**不是消费位病**。

### 裁定 2：NatLe_lift ＝ **信息位真消费（真病·需 informative 原生形）**——伴生面为证明位

**类型论**：`NatLe_lift n m h : NatLe n m = Id (Nat.leb n m) true`（Set·Id 载体）——Set 型调用在 Set 承载宿主中**作为值存活**。

**全量机械实证**：`coq_NatLe_lift (` 调用存活于 **44 模块**（含 DTPT_Truth 本地族 1，S01 域 43）·合计 **176 处运行时调用**（提取普查实数；静态 INFO 717 为含提取期死代码消除的上界——§五判读列逐文件给出实存/DCE 分账）。代表证据（逐一亲验提取体）：
- `abl_Pr_core_01.ml:46-47`：`let pr_prime_bool_true n = Coq_pair ((coq_NatLe_lift (S (S O)) n), …)` ——素性证书 `And@Set` 第一分量=**运行时值位**（源位点 `abl_Pr_core_01.v:148`）。
- `SumInvFactEscape.ml:55`：`| Coq_right -> g n (coq_NatLe_lift n m) hcc` ——逃逸判定分支运行时值（源位点 `:462`）。
- `abl_qpoly_divmod_gen.ml:147`：`(coq_NatLe_lift (length p) (length p))` ——正典判例件 `qpg_divmod_gen` 交付证书值位（源位点 `:667`，喂 `qpg_engine_sound` 第四参 `NatLe (length p) fuel`＝Set 载体槽，`abl_qpoly_divmod_gen.v:541-543`）。
- `S02_CauchyComplete.ml`：real_plus 族模数传输 7 调用（源位点 `:447-451` 等）。

**旧 lift 运行时病**（重建动因第一手）：现状提取体 `attn/_natle_probe/term_ws/S01_BaseRing.ml:13-17`（本席探针产物的存量全提取件；顶层同名件已被残桩覆盖·漂移注记见 §六.8）
```ocaml
let coq_NatLe_lift n m =
  let b = Nat.leb n m in
  (match b with Coq_true -> Coq_id_refl | Coq_false -> assert false)
```
——擦掉的 Prop 前提使提取器**凭空重算 leb、假分支 assert false 崩溃**＝伴生半泄露（语句面存活·前提擦除·`val coq_NatLe_lift : nat -> nat -> coq_NatLe` 假值签名 `term_ws/S01_BaseRing.mli:11`；同体亦存活于 `_wt93_ssa/_gate7probe_S01_work/S01_BaseRing.ml:57-62`）。补丁 NEW 形提取=恒等函数 `let coq_NatLe_lift _ _ h = h`（前役产物 `_gate7probe_S01_work/_gate7probe_S01_BaseRing.ml.after-rewrite:57-58`）——消病且 4d 性能占优（零重算）。

**裁定小结**：甲方案『原生 informative 重铸』的信息位压力**全部落在 lift 侧**（提取实存 **176 调用/44 模块**＝S01 域 43 模块 173 调用＋DTPT_Truth 同名异族 1 模块 3 调用·§一·乙表逐条在卷）；drop 消费面零信息位需求、纯登记。重建接口形：新 `NatLe_drop : NatLe n m -> @Id bool (Nat.leb n m) true`（Id-bool 面输出）＋新 `NatLe_lift : @Id bool (Nat.leb n m) true -> NatLe n m`（Id-bool 面输入）＋登记册桥引理对 `NatLe_drop_le : NatLe n m -> (n<=m)%nat`（Prop 桥·政策①）与 `NatLe_lift_le : (n<=m)%nat -> NatLe n m := fun H => NatLe_lift n m (lebT_of_le H)`（Prop→Id 组合桥·缺口③正典 S02 `qeqT_imp_qeq`/`z2v_idS_eq` 同构）——证明位消费者**纯改名零结构变**，信息位消费者（§一·乙 176 活体）一律由新 informative 原生形供血（恒等 exact H 形），旧 Prop 形仅作 proof-bridge registry 条目服务证明位。

## 三·三硬核难度定性（任务 4）

### 硬核 α：`b1_denom_control.v:80`（`Theorem b1_dfact_odd_le_even` 内）
- 位点形态：`:79` `apply NatLe_lift.`＋`:80-83` `apply (Nat.le_trans …)` 链＋`:96` `apply NatLe_drop. exact IH.`——Set 承载结论（`NatLe (b1_dfact_odd n) (b1_dfact_even n)`）的**归纳证明**内 lift/drop 阶梯；提取面 `b1_denom_control.ml` 实测 2 处 lift 调用存活=真信息位。
- 周边结构：自足 nat 侧二项式折叠件（奇偶阶乘支配），`Nat.le_trans`＋`Nat.mul_le_mono_*`＋lia 链，无 Q 层纠缠。
- 预估改法：桥对改名即解——`:79` `apply NatLe_lift`→`apply NatLe_lift_le`；`:96` `apply NatLe_drop`→`apply NatLe_drop_le`；归纳 IH 结构零动。难度=**机械·低**（纯改名迁移·两行）。

### 硬核 β：`abl_Pr_core_01.v:148`（`Theorem pr_prime_bool_true` 内）
- 位点形态：`apply NatLe_lift. exact Hleb.` 的产物直接落入素性证书 `And@Set`（`pr_prime`）第一分量运行时槽——提取铁证 `abl_Pr_core_01.ml:46-47`（上文引用）；同文件 `:175` `pose proof (Hall d (NatLe_lift _ _ Hd2) (NatLe_lift _ _ Hdlt2))` 双 lift 喂 Hall 的 NatLe 参数（提取面 DCE 后 `_ _` 空槽，签名槽仍 `coq_NatLe`）。
- 周边结构：素数机器（`pr_prime_bool` 决断器＋`pr_min_factor` 计算核＋`pr_min_factor_exists` sigT 交付），bool/Id 双面互推。
- 预估改法：`:148` 改 `apply NatLe_lift_le. exact Hleb.`（一行）；`:175` 两参改名 `NatLe_lift_le`（一行）；下游 `peu_next`/`peu_next_prime` 消费链零动（其 drop 调用已被提取裁剪）。难度=**中低**（证书槽值位需正确入桥·改后须重验提取 informative 0/0）。

### 硬核 γ：`S02_CauchyComplete.v:447`（`Definition real_plus` 体内，:447-451 四连）
- 位点形态：**`Definition real_plus (x y : Real) : Real.` ＋ tactic 证明＋`Defined.` 透明定义＝实数加法本体进提取面**；`cauchy` 协议（`:407-410`）模数位=`NatLe N m -> NatLe N n -> …`（Set·Id 载体），:447-451 四个 `apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l/r | exact (NatLe_drop _ _ Hm/Hn)]` ＝ **模数传输的运行时值位**（HN1/HN2 的 NatLe 槽喂入；本模块提取实存 7 调用）。
- 周边结构：S02 为全库最深枢纽（下游 353 件闭包的必经层），`Real`/`cauchy`/`real_eq` 全系 NatLe 模数协议；`Defined.` 透明=改面即改运行时核。
- 预估改法：四行改名（lift→`NatLe_lift_le`、drop→`NatLe_drop_le`），`max N1 N2` 传输链零动；改后该定义提取形从『调用重算 leb＋assert false 危点』变『恒等传递调用方 Id』——4d 层性能中性偏优。难度=**中低·但闭包最重**（机械改名本身低难，风险全在 353 件级联重编预算与 4a-4d 全梯终判；建议重建役把 S02 排为桥对落地第一站，其余模块按拓扑序批量跟进）。

**三硬核总评**：无数学性硬墙——三者皆是『Set 承载证书/协议槽的 lift 值位』，桥对改名文法（缺口③）可全部机械降阶；真正成本在 E949 闭包重编与全梯验收，不在证明重构。上役『三件 only-S01 消费者真红·零适配收敛形双向排除』的数学互斥，在桥对接口形下解除（这正是缺口③的降阶设计意图）。

**〔复核轮 1 补注（修复席 20261105·G4 病根改判衔接）〕**上列三硬核「预估改法」中改名桥（`_le`）路线仅适用其**纯证明位**；三者名下的**提取活体值位**（α 2 调用／β 证书槽 4 调用／γ `real_plus` 族 7 调用——§一·乙表逐条在卷）按改判**一律由新 informative 原生形供血**（恒等 exact H／`NatLe_refl` 反射形），禁以 `NatLe_lift_le` 的 leb 重算＋assert false 体供血活位（基线危形实证 `term_ws/S01_BaseRing.ml:13-17`）。本补注不改本卷 census 数系；施工面细则以设计书 §3.4 G4 改判＋§3.5 衔接注为准。

## 四·迁移文法代号表

| 代号 | 位面 | 机械改写 | 位点数 |
|---|---|---|---|
| W-D0(提取槽重写) | | | 3 |
| W-D1(改名桥) | | | 281 |
| W-D2(改名桥) | | | 329 |
| W-D3(改名桥) | | | 419 |
| W-L1(改名桥) | | | 306 |
| W-L2(改名桥→原生) | | | 503 |
| W-L3(原生face重铸) | | | 214 |
| W-Z | 注释/命令/DTPT 本地族 | 零迁移 | 81 |
| W-X | 选择性导入清单 | 清单加桥件名 | 17 |

## 五·全量位点逐条表

说明：`提取判读`=第三源普查该模块 .ml 的 `coq_NatLe_lift/drop(` 调用计数——drop 全库 0 调用（行值『擦除(mli `__`)』＝该模块实提后 drop 零调用）；lift 行值『调用存活 N』＝实存运行时调用，『DCE简化』＝静态 INFO 位存在但提取期死代码消除（签名槽 `coq_NatLe` 仍存活，例 `pow_fact_geom_iter`：`_extr_debris/S03_QExp.ml:180-184`）。行号=现势源面。

### Arch_Banach_01.v（9 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 418 | `NatLe_lift` | INFO | apply-fwd | Lemma bxae_etab_small | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 430 | `NatLe_lift` | INFO | bare | Lemma bxae_etab_small | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 431 | `NatLe_drop` | PB | ltac-embed | Lemma bxae_etab_small | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1306 | `NatLe_drop` | PB | term-syntax | Lemma bxae_lim_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1307 | `NatLe_lift` | PB | term-syntax | Lemma bxae_lim_shift | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1311 | `NatLe_drop` | PB | term-syntax | Lemma bxae_lim_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1312 | `NatLe_lift` | PB | term-syntax | Lemma bxae_lim_shift | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1346 | `NatLe_drop` | PB | term-syntax | Theorem bxae_exp_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1553 | `NatLe_drop` | PB | term-syntax | Theorem s3c_exp_add_plain | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### Arch_PA_02.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 715 | `NatLe_drop` | PB | term-syntax | Theorem sa_A_nonzeroT | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 716 | `NatLe_drop` | PB | ltac-embed | Theorem sa_A_nonzeroT | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 717 | `NatLe_drop` | PB | ltac-embed | Theorem sa_A_nonzeroT | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 832 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 840 | `NatLe_drop` | PB | term-syntax | Lemma sa_q2_le_mul | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 841 | `NatLe_drop` | PB | ltac-embed | Lemma sa_q2_le_mul | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 846 | `NatLe_lift` | INFO | apply-fwd | Lemma sa_q2_le_mul | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### Arch_ToyR_04.v（14 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 445 | `NatLe_lift` | INFO | apply-fwd | Theorem bv_term_pos | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 446 | `NatLe_drop` | PB | apply-fwd | Theorem bv_term_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 613 | `NatLe_lift` | PB | apply-fwd | Theorem bv_zeros_int0 | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 614 | `NatLe_drop` | PB | apply-fwd | Theorem bv_zeros_int0 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 817 | `NatLe_drop` | PB | term-syntax | Theorem bv_delannoy_eq_qtilde | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 818 | `NatLe_lift` | INFO | term-syntax | Theorem bv_delannoy_eq_qtilde | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1186 | `NatLe_lift` | INFO | apply-fwd | Theorem pi_Qn_le_8pow | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1199 | `NatLe_lift` | INFO | bare | Theorem pi_Qn_le_8pow | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1199 | `NatLe_drop` | PB | bare | Theorem pi_Qn_le_8pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1215 | `NatLe_drop` | PB | term-syntax | Theorem pi_Qn_le_8pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1256 | `NatLe_drop` | PB | term-syntax | Lemma pi_qtilde_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1272 | `NatLe_drop` | PB | term-syntax | Lemma pi_Qn_nz | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1566 | `NatLe_lift` | PB | apply-fwd | Lemma bk_Qn_ge_3pow_nat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1567 | `NatLe_drop` | PB | apply-fwd | Lemma bk_Qn_ge_3pow_nat | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### AttnHardLimit218.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 335 | `NatLe_lift` | INFO | apply-fwd | Lemma remove_length_le_aux | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 337 | `NatLe_lift` | INFO | apply-fwd | Lemma remove_length_le_aux | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 338 | `NatLe_drop` | PB | apply-fwd | Lemma remove_length_le_aux | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 339 | `NatLe_drop` | PB | apply-fwd | Lemma remove_length_le_aux | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 821 | `NatLe_drop` | PB | apply-fwd | Lemma nonm_mass_le_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 907 | `NatLe_drop` | PB | apply-fwd | Lemma hsum_nonm_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### BetaLower.v（13 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 36 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 36 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 48 | `NatLe_lift` | INFO | apply-fwd | Lemma bl_mul_ge1 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 223 | `NatLe_lift` | INFO | apply-fwd | Lemma bl_nat_core16 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 273 | `NatLe_lift` | INFO | apply-fwd | Lemma bl_nat_core14 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 349 | `NatLe_drop` | PB | ltac-embed | Lemma bl_half_pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 352 | `NatLe_drop` | PB | ltac-embed | Lemma bl_half_pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 382 | `NatLe_drop` | PB | ltac-embed | Lemma bl_opt_pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 385 | `NatLe_drop` | PB | ltac-embed | Lemma bl_opt_pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 401 | `NatLe_drop` | PB | ltac-embed | Theorem bl_beta_lower | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 405 | `NatLe_drop` | PB | term-syntax | Theorem bl_beta_lower | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 417 | `NatLe_drop` | PB | ltac-embed | Theorem bl_beta_lower_opt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 421 | `NatLe_drop` | PB | term-syntax | Theorem bl_beta_lower_opt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### BeukersIdentity.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 49 | `NatLe_drop` | PB | apply-fwd | Lemma bi_D_eq_qtilde | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 49 | `NatLe_lift` | INFO | apply-fwd | Lemma bi_D_eq_qtilde | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 157 | `NatLe_drop` | PB | apply-fwd | Lemma bi_half_gt_nat | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 185 | `NatLe_drop` | PB | term-syntax | Theorem bi_Qn_half_gt1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### BeukersLists.v（41 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 51 | `NatLe_drop` | PB | term-syntax | Lemma bkC_out | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 55 | `NatLe_drop` | PB | term-syntax | Lemma bkC_out | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 60 | `NatLe_lift` | INFO | term-syntax | Lemma bkC_out | **是（信息位）** | 调用存活8 | W-L3(原生face重铸) |
| 62 | `NatLe_lift` | INFO | term-syntax | Lemma bkC_out | **是（信息位）** | 调用存活8 | W-L3(原生face重铸) |
| 75 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_diag | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 84 | `NatLe_drop` | PB | term-syntax | Lemma bkC_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 85 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 87 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 91 | `NatLe_drop` | PB | apply-fwd | Lemma bkC_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 91 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 93 | `NatLe_drop` | PB | apply-fwd | Lemma bkC_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 93 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 94 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 95 | `NatLe_drop` | PB | apply-fwd | Lemma bkC_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 99 | `NatLe_drop` | PB | apply-fwd | Lemma bkC_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 99 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 100 | `NatLe_lift` | INFO | apply-fwd | Lemma bkC_pos | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 119 | `NatLe_drop` | PB | term-syntax | Lemma bk_Qn_sym | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 122 | `NatLe_drop` | PB | term-syntax | Lemma bk_Qn_sym | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 129 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_Qn_sym | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 131 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_Qn_sym | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 166 | `NatLe_drop` | PB | term-syntax | Lemma bk_psd_ext | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 167 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_psd_ext | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 170 | `NatLe_lift` | INFO | bare | Lemma bk_psd_ext | **是（信息位）** | 调用存活8 | W-L3(原生face重铸) |
| 247 | `NatLe_lift` | INFO | bare | Lemma bk_psd_binom | **是（信息位）** | 调用存活8 | W-L3(原生face重铸) |
| 258 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_psd_mono | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 261 | `NatLe_drop` | PB | apply-fwd | Lemma bk_psd_mono | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 262 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_psd_mono | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 263 | `NatLe_drop` | PB | apply-fwd | Lemma bk_psd_mono | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 265 | `NatLe_drop` | PB | apply-fwd | Lemma bk_psd_mono | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 265 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_psd_mono | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 266 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_psd_mono | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 285 | `NatLe_drop` | PB | term-syntax | Lemma bk_Qn_ge_3pow_nat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 287 | `NatLe_lift` | INFO | term-syntax | Lemma bk_Qn_ge_3pow_nat | **是（信息位）** | 调用存活8 | W-L3(原生face重铸) |
| 288 | `NatLe_drop` | PB | apply-in | Lemma bk_Qn_ge_3pow_nat | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 289 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_Qn_ge_3pow_nat | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 304 | `NatLe_drop` | PB | apply-fwd | Lemma bk_Qle_nat | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 390 | `NatLe_drop` | PB | apply-in | Lemma bk_nth_map_lt | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 394 | `NatLe_drop` | PB | apply-fwd | Lemma bk_nth_map_lt | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 394 | `NatLe_lift` | INFO | apply-fwd | Lemma bk_nth_map_lt | **是（信息位）** | 调用存活8 | W-L2(改名桥→原生) |
| 405 | `NatLe_drop` | PB | apply-fwd | Lemma bk_nth_map_seq | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### BeukersVariant.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 59 | `NatLe_lift` | INFO | apply-fwd | Theorem bv_term_pos | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 60 | `NatLe_drop` | PB | apply-fwd | Theorem bv_term_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 245 | `NatLe_lift` | INFO | apply-fwd | Theorem bv_zeros_int0 | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 246 | `NatLe_drop` | PB | apply-fwd | Theorem bv_zeros_int0 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 483 | `NatLe_drop` | PB | term-syntax | Theorem bv_delannoy_eq_qtilde | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 484 | `NatLe_lift` | INFO | term-syntax | Theorem bv_delannoy_eq_qtilde | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### DTPT.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 41 | `NatLe_drop` | DEF-LOCAL | local-copy | — | 本地定义 | — | W-Z(DTPT本地族·独立) |
| 49 | `NatLe_lift` | DEF-LOCAL | local-copy | — | 本地定义 | — | W-Z(DTPT本地族·独立) |
| 2088 | `NatLe_drop` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 2181 | `NatLe_drop` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 3284 | `NatLe_drop` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 4227 | `NatLe_drop` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 4227 | `NatLe_lift` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |

### DTPT_Entropy.v（65 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 1013 | `NatLe_lift` | INFO | apply-fwd | Lemma count_val_le_length | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 1024 | `NatLe_drop` | PB | term-syntax | Lemma count_val_Zle_length | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1477 | `NatLe_lift` | INFO | apply-fwd | Lemma freq_q_le_length | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 1525 | `NatLe_drop` | PB | term-syntax | Lemma freq_q_full_count | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1530 | `NatLe_drop` | PB | term-syntax | Lemma freq_q_full_count | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1573 | `NatLe_lift` | INFO | apply-fwd | Lemma nsum_bound | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 1578 | `NatLe_drop` | PB | term-syntax | Lemma nsum_bound | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1592 | `NatLe_drop` | PB | term-syntax | Lemma nsum_bound_eq | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1622 | `NatLe_drop` | PB | apply-fwd | Lemma sqsum_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1653 | `NatLe_drop` | PB | bare | Lemma sqsum_eq_all_same | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1693 | `NatLe_drop` | PB | apply-fwd | Theorem H_freq_nonneg | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1776 | `NatLe_lift` | INFO | apply-fwd | Lemma nsum_le | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 1781 | `NatLe_drop` | PB | term-syntax | Lemma nsum_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1810 | `NatLe_lift` | INFO | apply-fwd | Lemma freq_q_map_ge | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 1812 | `NatLe_drop` | PB | apply-fwd | Lemma freq_q_map_ge | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1829 | `NatLe_drop` | PB | apply-fwd | Theorem sqsum_map_ge | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1899 | `NatLe_drop` | PB | apply-fwd | Theorem H_freq_dpi | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1901 | `NatLe_drop` | PB | apply-fwd | Theorem H_freq_dpi | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2049 | `NatLe_lift` | INFO | apply-fwd | Lemma qlen_pos | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 2057 | `NatLe_drop` | PB | apply-fwd | Lemma qlen_mul_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2057 | `NatLe_drop` | PB | apply-fwd | Lemma qlen_mul_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2110 | `NatLe_lift` | INFO | apply-fwd | Lemma nmax_bound | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 2115 | `NatLe_drop` | PB | apply-fwd | Lemma nmax_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2122 | `NatLe_lift` | INFO | apply-fwd | Lemma nmax_le_bound | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 2127 | `NatLe_drop` | PB | term-syntax | Lemma nmax_le_bound | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2158 | `NatLe_lift` | INFO | apply-fwd | Lemma freq_q_ge1 | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 2166 | `NatLe_drop` | PB | apply-fwd | Lemma freq_q_ge1 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2173 | `NatLe_lift` | INFO | apply-fwd | Lemma nsum_ge_const | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 2178 | `NatLe_drop` | PB | term-syntax | Lemma nsum_ge_const | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2186 | `NatLe_drop` | PB | bare | Lemma sqsum_ge_length | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2216 | `NatLe_drop` | PB | apply-fwd | Theorem collide_upper | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2234 | `NatLe_drop` | PB | bare | Theorem collide_lower | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2237 | `NatLe_drop` | PB | apply-fwd | Theorem collide_lower | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2279 | `NatLe_drop` | PB | bare | Theorem collide_le_maxfreq | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2283 | `NatLe_drop` | PB | apply-fwd | Theorem collide_le_maxfreq | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2284 | `NatLe_drop` | PB | apply-fwd | Theorem collide_le_maxfreq | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2313 | `NatLe_drop` | PB | term-syntax | Theorem maxfreq_lower | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2317 | `NatLe_drop` | PB | term-syntax | Theorem maxfreq_lower | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2322 | `NatLe_drop` | PB | apply-fwd | Theorem maxfreq_lower | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2336 | `NatLe_drop` | PB | apply-fwd | Theorem maxfreq_upper | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2337 | `NatLe_drop` | PB | apply-fwd | Theorem maxfreq_upper | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2339 | `NatLe_drop` | PB | apply-fwd | Theorem maxfreq_upper | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2351 | `NatLe_drop` | PB | apply-fwd | Theorem maxfreq_all_same_one | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2352 | `NatLe_drop` | PB | apply-fwd | Theorem maxfreq_all_same_one | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2359 | `NatLe_drop` | PB | term-syntax | Theorem maxfreq_all_same_one | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2366 | `NatLe_drop` | PB | bare | Theorem maxfreq_all_same_one | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2433 | `NatLe_drop` | PB | apply-fwd | Theorem H_max_q_le_one | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2479 | `NatLe_drop` | PB | bare | Theorem H_freq_eq_bridge | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2601 | `NatLe_lift` | INFO | apply-fwd | Lemma me2_dedup_len_ge1 | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 2722 | `NatLe_drop` | PB | apply-fwd | Theorem mkMEval_Hms_ge1 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3273 | `NatLe_lift` | INFO | apply-fwd | Theorem sqsum_app_ge_l | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3276 | `NatLe_drop` | PB | apply-fwd | Theorem sqsum_app_ge_l | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3283 | `NatLe_lift` | INFO | apply-fwd | Theorem sqsum_app_ge_r | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3286 | `NatLe_drop` | PB | apply-fwd | Theorem sqsum_app_ge_r | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3316 | `NatLe_lift` | INFO | apply-fwd | Corollary sqsum_app_ge_sum | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3330 | `NatLe_lift` | INFO | apply-fwd | Lemma nmax_le_app_l | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3335 | `NatLe_lift` | INFO | apply-fwd | Lemma nmax_le_app_r | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3341 | `NatLe_lift` | INFO | apply-fwd | Lemma nmax_mono | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3346 | `NatLe_drop` | PB | term-syntax | Lemma nmax_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3351 | `NatLe_lift` | INFO | apply-fwd | Theorem maxcount_app_ge_l | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3355 | `NatLe_drop` | PB | apply-fwd | Theorem maxcount_app_ge_l | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3359 | `NatLe_drop` | PB | term-syntax | Theorem maxcount_app_ge_l | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3364 | `NatLe_lift` | INFO | apply-fwd | Theorem maxcount_app_ge_r | **是（信息位）** | 调用存活20 | W-L2(改名桥→原生) |
| 3368 | `NatLe_drop` | PB | apply-fwd | Theorem maxcount_app_ge_r | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3372 | `NatLe_drop` | PB | term-syntax | Theorem maxcount_app_ge_r | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### DTPT_Truth.v（8 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 19 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 19 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 748 | `NatLe_lift` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 752 | `NatLe_drop` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 914 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 915 | `NatLe_lift` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |
| 979 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 982 | `NatLe_lift` | LOCAL | local-copy | — | 本地族 | — | W-Z(DTPT本地族·独立) |

### ExpOneEnvelope.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 124 | `NatLe_drop` | PB | apply-in | Theorem enpf_eventual_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 450 | `NatLe_drop` | PB | apply-in | Lemma eoe_diff_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 465 | `NatLe_drop` | PB | apply-in | Lemma eoe_tail_explicit | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 511 | `NatLe_drop` | PB | apply-in | Theorem eoe_two_sided | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 627 | `NatLe_drop` | PB | apply-in | Theorem eoe_cauchy_modulus | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 628 | `NatLe_drop` | PB | apply-in | Theorem eoe_cauchy_modulus | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |

### G07_KLWall.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 120 | `NatLe_drop` | PB | term-syntax | Lemma klst_exp_tangent_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 127 | `NatLe_lift` | PB | apply-fwd | Lemma klst_exp_tangent_pos | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1230 | `NatLe_lift` | PB | apply-fwd | Lemma powb_mono_dec | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1234 | `NatLe_drop` | PB | term-syntax | Lemma powb_mono_dec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2431 | `NatLe_lift` | PB | term-syntax | Lemma klst_exp_tangent_neg | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2664 | `NatLe_drop` | PB | term-syntax | Lemma klst_exp_tangent_neg | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2675 | `NatLe_drop` | PB | term-syntax | Lemma klst_exp_tangent_neg | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### G08_Gibbs.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 1101 | `NatLe_lift` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1102 | `NatLe_drop` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1104 | `NatLe_lift` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1105 | `NatLe_drop` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### G10_LoebFam.v（36 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 1978 | `NatLe_lift` | INFO | term-syntax | Lemma real_lt_pt_le | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 1993 | `NatLe_lift` | INFO | term-syntax | Lemma real_le_pt_ev_plus | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2117 | `NatLe_lift` | INFO | term-syntax | Lemma sq_bound_from_eq | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2147 | `NatLe_lift` | INFO | term-syntax | Lemma sqrt_dim_ge_quarter | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2161 | `NatLe_lift` | INFO | term-syntax | Lemma sqrt_dim_ge_quarter | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2217 | `NatLe_drop` | PB | apply-in | Lemma root_d_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2285 | `NatLe_drop` | PB | apply-fwd | Lemma abs_mult_pos_eps | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2288 | `NatLe_drop` | PB | apply-fwd | Lemma abs_mult_pos_eps | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2294 | `NatLe_lift` | PB | term-syntax | Lemma abs_mult_pos_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 2303 | `NatLe_lift` | PB | term-syntax | Lemma abs_mult_pos_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 2410 | `NatLe_lift` | INFO | term-syntax | Lemma root_abs_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2417 | `NatLe_lift` | INFO | term-syntax | Lemma root_abs_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2429 | `NatLe_lift` | INFO | term-syntax | Lemma root_abs_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2434 | `NatLe_lift` | INFO | term-syntax | Lemma root_abs_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2476 | `NatLe_lift` | INFO | term-syntax | Lemma prod_tail_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2482 | `NatLe_lift` | INFO | term-syntax | Lemma prod_tail_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2596 | `NatLe_drop` | PB | apply-fwd | Lemma qk_pair_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2599 | `NatLe_drop` | PB | apply-fwd | Lemma qk_pair_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2605 | `NatLe_lift` | PB | term-syntax | Lemma qk_pair_bound | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 2633 | `NatLe_lift` | INFO | term-syntax | Lemma rd_pos_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2646 | `NatLe_lift` | INFO | bare | Lemma rd_pos_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2690 | `NatLe_lift` | INFO | term-syntax | Lemma rd_ge_one_minus_delta | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2722 | `NatLe_lift` | INFO | term-syntax | Lemma qk_rd_loss | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2730 | `NatLe_lift` | INFO | term-syntax | Lemma qk_rd_loss | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2841 | `NatLe_drop` | PB | apply-fwd | Theorem real_logit_bound_of_norm_bounds | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2844 | `NatLe_drop` | PB | apply-fwd | Theorem real_logit_bound_of_norm_bounds | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2849 | `NatLe_lift` | PB | term-syntax | Theorem real_logit_bound_of_norm_bounds | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 2881 | `NatLe_drop` | PB | apply-fwd | Theorem real_logit_bound_of_norm_bounds | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2884 | `NatLe_drop` | PB | apply-fwd | Theorem real_logit_bound_of_norm_bounds | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2889 | `NatLe_lift` | PB | term-syntax | Theorem real_logit_bound_of_norm_bounds | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 2973 | `NatLe_lift` | INFO | term-syntax | Theorem qk_logits_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2989 | `NatLe_lift` | INFO | term-syntax | Theorem qk_logits_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 3049 | `NatLe_drop` | PB | apply-fwd | Theorem qk_logits_bounded | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3067 | `NatLe_drop` | PB | apply-fwd | Theorem qk_logits_bounded | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3070 | `NatLe_drop` | PB | apply-fwd | Theorem qk_logits_bounded | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3081 | `NatLe_lift` | INFO | term-syntax | Theorem qk_logits_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### KLWallClosed.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 387 | `NatLe_lift` | PB | apply-fwd | Lemma klc_powb_mono_weak | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 391 | `NatLe_drop` | PB | term-syntax | Lemma klc_powb_mono_weak | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### LW0LeibWindow.v（10 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 1540 | `NatLe_drop` | PB | apply-in | Lemma leiblw_glue_band_S | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1636 | `NatLe_drop` | PB | apply-in | Lemma leiblw_win_even | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1662 | `NatLe_drop` | PB | apply-in | Lemma leiblw_win_odd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1810 | `NatLe_drop` | PB | apply-fwd | Lemma leiblw_t_vanish | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1841 | `NatLe_lift` | PB | apply-fwd | Lemma leiblw_S_cauchy | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1984 | `NatLe_lift` | INFO | apply-fwd | Lemma leiblw_S_tail_two_sided | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1985 | `NatLe_lift` | INFO | apply-fwd | Lemma leiblw_S_tail_two_sided | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 2006 | `NatLe_lift` | INFO | apply-fwd | Lemma leiblw_S_tail_two_sided | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 2007 | `NatLe_lift` | INFO | apply-fwd | Lemma leiblw_S_tail_two_sided | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 2035 | `NatLe_lift` | PB | apply-fwd | Theorem leiblw_S_real_lim | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### LW2Hermite.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 490 | `NatLe_lift` | INFO | apply-fwd | Lemma lw2_len_deriv | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 498 | `NatLe_drop` | PB | term-syntax | Lemma lw2_len_deriv_iter | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 507 | `NatLe_lift` | INFO | apply-fwd | Lemma lw2_len_deriv_iter | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 557 | `NatLe_drop` | PB | term-syntax | Lemma lw2_eval_di_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 559 | `NatLe_drop` | PB | term-syntax | Lemma lw2_eval_di_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 628 | `NatLe_drop` | PB | term-syntax | Lemma lw2_eval_di_scalar | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 630 | `NatLe_drop` | PB | term-syntax | Lemma lw2_eval_di_scalar | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### LW2IntegMachine.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 17 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 161 | `NatLe_drop` | PB | term-syntax | Lemma lw2_exp_int_parts | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### LW2SepTransport.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 10 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 10 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 84 | `NatLe_lift` | PB | apply-fwd | Theorem lw2t_sep_transport_k | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 85 | `NatLe_drop` | PB | apply-fwd | Theorem lw2t_sep_transport_k | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 87 | `NatLe_lift` | PB | apply-fwd | Theorem lw2t_sep_transport_k | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 88 | `NatLe_drop` | PB | apply-fwd | Theorem lw2t_sep_transport_k | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### LW4EPiContrast.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 348 | `NatLe_drop` | PB | term-syntax | Theorem lw4c_shape_separation_intro | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 351 | `NatLe_drop` | PB | term-syntax | Theorem lw4c_shape_separation_intro | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 351 | `NatLe_drop` | PB | term-syntax | Theorem lw4c_shape_separation_intro | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### Ln2Bridge.v（12 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 135 | `NatLe_lift` | INFO | term-syntax | Lemma ln2b_le_pt_slack | **是（信息位）** | 调用存活3 | W-L3(原生face重铸) |
| 160 | `NatLe_lift` | INFO | term-syntax | Lemma ln2b_le_pt_slack | **是（信息位）** | 调用存活3 | W-L3(原生face重铸) |
| 252 | `NatLe_lift` | INFO | apply-fwd | Lemma ln2b_pow_ge1 | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 253 | `NatLe_lift` | INFO | apply-fwd | Lemma ln2b_pow_ge1 | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 254 | `NatLe_drop` | PB | apply-fwd | Lemma ln2b_pow_ge1 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 263 | `NatLe_lift` | INFO | apply-fwd | Lemma ln2b_pow_bern | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 264 | `NatLe_lift` | INFO | apply-fwd | Lemma ln2b_pow_bern | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 268 | `NatLe_drop` | PB | apply-fwd | Lemma ln2b_pow_bern | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 292 | `NatLe_lift` | INFO | apply-fwd | Lemma ln2b_pow_core | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 299 | `NatLe_drop` | PB | term-syntax | Lemma ln2b_pow_core | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 300 | `NatLe_drop` | PB | term-syntax | Lemma ln2b_pow_core | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 357 | `NatLe_drop` | PB | term-syntax | Lemma ln2b_decay | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### Ln2Escape.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 131 | `NatLe_lift` | INFO | apply-fwd | Lemma lne_fact_ge1 | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 395 | `NatLe_lift` | INFO | apply-fwd | Lemma lne_nat_core | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 428 | `NatLe_lift` | INFO | apply-fwd | Lemma lne_pow_ge1 | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 501 | `NatLe_drop` | PB | term-syntax | Theorem lne_B_le_p4 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 503 | `NatLe_drop` | PB | term-syntax | Theorem lne_B_le_p4 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 506 | `NatLe_drop` | PB | term-syntax | Theorem lne_B_le_p4 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 540 | `NatLe_drop` | PB | term-syntax | Theorem lne_B_int | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### PA_ExpOneEnvelope.v（5 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 300 | `NatLe_drop` | PB | apply-in | Lemma eoe_diff_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 315 | `NatLe_drop` | PB | apply-in | Lemma eoe_tail_explicit | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 361 | `NatLe_drop` | PB | apply-in | Theorem eoe_two_sided | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 477 | `NatLe_drop` | PB | apply-in | Theorem eoe_cauchy_modulus | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 478 | `NatLe_drop` | PB | apply-in | Theorem eoe_cauchy_modulus | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |

### PadeErrorIntegral.v（15 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 99 | `NatLe_lift` | INFO | apply-fwd | Lemma bts_sum_nonneg_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 100 | `NatLe_drop` | PB | apply-fwd | Lemma bts_sum_nonneg_bounded | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 103 | `NatLe_lift` | INFO | apply-fwd | Lemma bts_sum_nonneg_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 169 | `NatLe_drop` | PB | apply-fwd | Lemma bts_coeff_abs_self | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 227 | `NatLe_drop` | PB | term-syntax | Lemma bts_exp_partial_diff_tail | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 241 | `NatLe_lift` | INFO | apply-fwd | Lemma bts_exp_partial_diff_tail | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 241 | `NatLe_drop` | PB | apply-fwd | Lemma bts_exp_partial_diff_tail | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 242 | `NatLe_drop` | PB | apply-fwd | Lemma bts_exp_partial_diff_tail | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 320 | `NatLe_lift` | INFO | apply-fwd | Lemma bts_sum_upto_mono | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 321 | `NatLe_drop` | PB | apply-fwd | Lemma bts_sum_upto_mono | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 322 | `NatLe_lift` | INFO | apply-fwd | Lemma bts_sum_upto_mono | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 340 | `NatLe_lift` | INFO | apply-fwd | Lemma bts_den_abs_le_num_abs | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 340 | `NatLe_drop` | PB | apply-fwd | Lemma bts_den_abs_le_num_abs | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 361 | `NatLe_drop` | PB | term-syntax | Lemma bts_num_abs_nonneg | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 397 | `NatLe_lift` | INFO | bare | Lemma bts_rem_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### PiEnvelope.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 695 | `NatLe_drop` | PB | apply-in | Theorem pie_modulus_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 704 | `NatLe_drop` | PB | apply-in | Theorem pie_modulus_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 778 | `NatLe_drop` | PB | apply-in | Lemma pie_real_lower_gen | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |

### PowRealCompat.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 162 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 169 | `NatLe_drop` | PB | term-syntax | Lemma prc_powb_anti_mono_real_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### S01_BaseRing.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 91 | `NatLe_drop` | DEF | definition | — | 定义面 | — | — |
| 100 | `NatLe_lift` | DEF | definition | — | 定义面 | — | — |

### S02_CauchyComplete.v（120 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 447 | `NatLe_lift` | INFO | apply-fwd | Definition real_plus | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 447 | `NatLe_drop` | PB | apply-fwd | Definition real_plus | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 448 | `NatLe_lift` | INFO | apply-fwd | Definition real_plus | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 448 | `NatLe_drop` | PB | apply-fwd | Definition real_plus | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 450 | `NatLe_lift` | INFO | apply-fwd | Definition real_plus | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 450 | `NatLe_drop` | PB | apply-fwd | Definition real_plus | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 451 | `NatLe_lift` | INFO | apply-fwd | Definition real_plus | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 451 | `NatLe_drop` | PB | apply-fwd | Definition real_plus | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 508 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_trans | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 508 | `NatLe_drop` | PB | apply-fwd | Lemma real_lt_trans | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 512 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_trans | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 512 | `NatLe_drop` | PB | apply-fwd | Lemma real_lt_trans | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 555 | `NatLe_drop` | PB | term-syntax | Lemma Qabs_in_sum_abs_prefix | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 557 | `NatLe_drop` | PB | term-syntax | Lemma Qabs_in_sum_abs_prefix | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 561 | `NatLe_lift` | INFO | apply-fwd | Lemma Qabs_in_sum_abs_prefix | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 593 | `NatLe_lift` | INFO | apply-fwd | Lemma cauchy_bounded | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 598 | `NatLe_lift` | INFO | term-syntax | Lemma cauchy_bounded | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 598 | `NatLe_lift` | INFO | term-syntax | Lemma cauchy_bounded | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 739 | `NatLe_lift` | INFO | apply-fwd | Definition real_mult | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 739 | `NatLe_drop` | PB | apply-fwd | Definition real_mult | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 740 | `NatLe_lift` | INFO | apply-fwd | Definition real_mult | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 740 | `NatLe_drop` | PB | apply-fwd | Definition real_mult | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 749 | `NatLe_lift` | INFO | apply-fwd | Definition real_mult | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 749 | `NatLe_drop` | PB | apply-fwd | Definition real_mult | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 750 | `NatLe_lift` | INFO | apply-fwd | Definition real_mult | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 750 | `NatLe_drop` | PB | apply-fwd | Definition real_mult | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 837 | `NatLe_lift` | PB | apply-fwd | Theorem real_square_not_negative | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 959 | `NatLe_lift` | INFO | term-syntax | Lemma real_lt_abs_bound | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 960 | `NatLe_lift` | INFO | term-syntax | Lemma real_lt_abs_bound | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 1074 | `NatLe_drop` | PB | term-syntax | Theorem real_lim_unique | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1075 | `NatLe_drop` | PB | term-syntax | Theorem real_lim_unique | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1076 | `NatLe_drop` | PB | term-syntax | Theorem real_lim_unique | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1077 | `NatLe_drop` | PB | term-syntax | Theorem real_lim_unique | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1115 | `NatLe_lift` | PB | apply-fwd | Theorem real_lim_unique | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1115 | `NatLe_lift` | PB | apply-fwd | Theorem real_lim_unique | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1117 | `NatLe_lift` | PB | apply-fwd | Theorem real_lim_unique | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1117 | `NatLe_lift` | PB | apply-fwd | Theorem real_lim_unique | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1371 | `NatLe_lift` | INFO | apply-fwd | Lemma pow2_ge_one | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1378 | `NatLe_lift` | INFO | apply-fwd | Lemma pow2_ge | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1380 | `NatLe_drop` | PB | apply-fwd | Lemma pow2_ge | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1388 | `NatLe_lift` | INFO | apply-fwd | Lemma pow2_gt | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1390 | `NatLe_drop` | PB | apply-fwd | Lemma pow2_gt | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1406 | `NatLe_drop` | PB | bare | Lemma step_seq_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1415 | `NatLe_drop` | PB | bare | Lemma step_seq_ge | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1507 | `NatLe_drop` | PB | term-syntax | Lemma step_real_double_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1509 | `NatLe_drop` | PB | term-syntax | Lemma step_real_double_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1510 | `NatLe_lift` | INFO | apply-fwd | Lemma step_real_double_cauchy | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1511 | `NatLe_lift` | INFO | apply-fwd | Lemma step_real_double_cauchy | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1536 | `NatLe_drop` | PB | term-syntax | Lemma step_real_double_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1538 | `NatLe_drop` | PB | term-syntax | Lemma step_real_double_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1539 | `NatLe_lift` | INFO | apply-fwd | Lemma step_real_double_cauchy | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1540 | `NatLe_lift` | INFO | apply-fwd | Lemma step_real_double_cauchy | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1597 | `NatLe_drop` | PB | apply-fwd | Theorem step_not_unif_pointwise | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1603 | `NatLe_lift` | PB | apply-fwd | Theorem step_not_unif_pointwise | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1605 | `NatLe_lift` | PB | apply-fwd | Theorem step_not_unif_pointwise | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1609 | `NatLe_drop` | PB | apply-fwd | Theorem step_not_unif_pointwise | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1693 | `NatLe_lift` | PB | apply-fwd | Theorem step_not_lim_zero | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 1827 | `NatLe_lift` | INFO | apply-fwd | Lemma nat_min_l | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1830 | `NatLe_lift` | INFO | apply-fwd | Lemma nat_min_l | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1833 | `NatLe_lift` | INFO | apply-fwd | Lemma nat_min_l | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1834 | `NatLe_drop` | PB | apply-fwd | Lemma nat_min_l | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1849 | `NatLe_lift` | INFO | apply-fwd | Lemma reg_index_ge | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1849 | `NatLe_lift` | INFO | apply-fwd | Lemma reg_index_ge | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1853 | `NatLe_drop` | PB | apply-fwd | Lemma reg_index_ge | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1863 | `NatLe_lift` | INFO | apply-fwd | Lemma reg_index_fmod | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1863 | `NatLe_lift` | INFO | apply-fwd | Lemma reg_index_fmod | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1907 | `NatLe_drop` | PB | apply-fwd | Lemma regularize_uniform_mod | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1908 | `NatLe_drop` | PB | apply-fwd | Lemma regularize_uniform_mod | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1914 | `NatLe_lift` | INFO | bare | Lemma regularize_uniform_mod | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 1915 | `NatLe_lift` | INFO | apply-fwd | Lemma regularize_uniform_mod | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1927 | `NatLe_drop` | PB | apply-fwd | Lemma regularize_uniform_mod | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1928 | `NatLe_drop` | PB | apply-fwd | Lemma regularize_uniform_mod | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1932 | `NatLe_lift` | INFO | bare | Lemma regularize_uniform_mod | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 1933 | `NatLe_lift` | INFO | apply-fwd | Lemma regularize_uniform_mod | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 1954 | `NatLe_drop` | PB | term-syntax | Lemma regularize_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1956 | `NatLe_drop` | PB | term-syntax | Lemma regularize_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1989 | `NatLe_drop` | PB | bare | Lemma regularize_same_real | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1990 | `NatLe_drop` | PB | apply-fwd | Lemma regularize_same_real | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1994 | `NatLe_lift` | INFO | apply-fwd | Lemma regularize_same_real | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 2353 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_trans | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2353 | `NatLe_drop` | PB | apply-fwd | Lemma real_eq_trans | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2355 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_trans | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2355 | `NatLe_drop` | PB | apply-fwd | Lemma real_eq_trans | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2469 | `NatLe_lift` | PB | term-syntax | Lemma real_lt_irrefl | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2507 | `NatLe_lift` | PB | apply-fwd | Lemma real_le_refl | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2507 | `NatLe_drop` | PB | apply-fwd | Lemma real_le_refl | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2510 | `NatLe_lift` | PB | apply-fwd | Lemma real_le_refl | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2510 | `NatLe_drop` | PB | apply-fwd | Lemma real_le_refl | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2550 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_lt_lt | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2550 | `NatLe_drop` | PB | apply-fwd | Lemma real_eq_lt_lt | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2553 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_lt_lt | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2553 | `NatLe_drop` | PB | apply-fwd | Lemma real_eq_lt_lt | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2609 | `NatLe_drop` | PB | term-syntax | Lemma real_eq_minus_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2610 | `NatLe_drop` | PB | term-syntax | Lemma real_eq_minus_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2632 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_minus_compat | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2634 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_minus_compat | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 2736 | `NatLe_lift` | INFO | term-syntax | Lemma real_lt_pair_abs_bound | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 2743 | `NatLe_lift` | INFO | term-syntax | Lemma real_lt_pair_abs_bound | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 2804 | `NatLe_lift` | INFO | apply-fwd | Lemma nat_le_min | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 2906 | `NatLe_drop` | PB | term-syntax | Lemma regularized_diag_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2907 | `NatLe_drop` | PB | term-syntax | Lemma regularized_diag_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2908 | `NatLe_drop` | PB | term-syntax | Lemma regularized_diag_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2909 | `NatLe_drop` | PB | term-syntax | Lemma regularized_diag_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2971 | `NatLe_drop` | PB | apply-fwd | Lemma regularized_diag_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2990 | `NatLe_drop` | PB | apply-fwd | Lemma regularized_diag_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3087 | `NatLe_lift` | INFO | apply-fwd | Lemma regularized_diag_close | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 3114 | `NatLe_drop` | PB | apply-fwd | Lemma regularized_diag_close | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3131 | `NatLe_drop` | PB | apply-fwd | Lemma regularized_diag_close | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3223 | `NatLe_drop` | PB | apply-fwd | Theorem real_cauchy_complete | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3244 | `NatLe_drop` | PB | apply-fwd | Theorem real_cauchy_complete | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3311 | `NatLe_drop` | PB | term-syntax | Lemma real_lt_plus_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3312 | `NatLe_drop` | PB | term-syntax | Lemma real_lt_plus_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3326 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_plus_compat | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 3327 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_plus_compat | 否（证明位） | 调用存活7 | W-L1(改名桥) |
| 3578 | `NatLe_drop` | PB | apply-fwd | Theorem real_lim_scal | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3609 | `NatLe_drop` | PB | apply-fwd | Theorem real_lim_scal | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3690 | `NatLe_lift` | INFO | term-syntax | Lemma real_lim_pointwise_bound | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 3701 | `NatLe_lift` | INFO | term-syntax | Lemma real_lim_pointwise_bound | **是（信息位）** | 调用存活7 | W-L3(原生face重铸) |
| 3979 | `NatLe_drop` | PB | apply-fwd | Theorem real_lim_mult | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 4003 | `NatLe_drop` | PB | apply-fwd | Theorem real_lim_mult | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### S03_QExp.v（89 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 280 | `NatLe_lift` | INFO | apply-fwd | Lemma pow_fact_geom_iter | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 300 | `NatLe_lift` | INFO | apply-fwd | Lemma pow_fact_geom_iter | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 473 | `NatLe_drop` | PB | apply-in | Lemma q_arch_geom | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 815 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 815 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 824 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 824 | `NatLe_lift` | INFO | apply-in | Lemma exp_partial_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 841 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 841 | `NatLe_lift` | INFO | apply-in | Lemma exp_partial_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1196 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1196 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1202 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1202 | `NatLe_lift` | INFO | apply-in | Lemma exp_partial_cauchy_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1214 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1214 | `NatLe_lift` | INFO | apply-in | Lemma exp_partial_cauchy_bounded | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1261 | `NatLe_drop` | PB | apply-in | Lemma exp_series_arch | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1261 | `NatLe_lift` | INFO | apply-in | Lemma exp_series_arch | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1342 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_exp | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1342 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1343 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_exp | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1343 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1351 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_exp | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1351 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1352 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_exp | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 1352 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2955 | `NatLe_lift` | INFO | bare | Lemma sum_upto_ext_below | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2955 | `NatLe_drop` | PB | bare | Lemma sum_upto_ext_below | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2956 | `NatLe_lift` | INFO | bare | Lemma sum_upto_ext_below | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 3042 | `NatLe_drop` | PB | apply-in | Lemma ksum_diff_nat_eq | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3182 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_row_succ | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3216 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_col_succ | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3229 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_col_succ | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3463 | `NatLe_drop` | PB | apply-in | Lemma corr_diff_expand | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3644 | `NatLe_drop` | PB | apply-in | Lemma excess_col_tail | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3677 | `NatLe_drop` | PB | apply-in | Lemma excess_col_tail | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3704 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_tri_swap_min | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3714 | `NatLe_drop` | PB | term-syntax | Lemma sum_upto_tri_swap_min | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3763 | `NatLe_drop` | PB | apply-in | Lemma col_shift_right | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3815 | `NatLe_drop` | PB | apply-in | Lemma q_ring_reorder | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3874 | `NatLe_drop` | PB | apply-in | Lemma c1_col_mid | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3921 | `NatLe_drop` | PB | apply-in | Lemma supp_col | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3935 | `NatLe_drop` | PB | apply-in | Lemma supp_col | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4000 | `NatLe_drop` | PB | apply-in | Lemma c1_assembly | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4088 | `NatLe_drop` | PB | apply-in | Lemma c1 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4121 | `NatLe_drop` | PB | apply-in | Lemma c1 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4158 | `NatLe_drop` | PB | apply-in | Lemma c1 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4542 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_mirror_even | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4547 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_mirror_even | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4547 | `NatLe_lift` | INFO | apply-in | Lemma sum_upto_mirror_even | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 4569 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_mirror_odd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4574 | `NatLe_drop` | PB | apply-in | Lemma sum_upto_mirror_odd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4574 | `NatLe_lift` | INFO | apply-in | Lemma sum_upto_mirror_odd | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 4633 | `NatLe_drop` | PB | apply-in | Lemma vander_4m2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4661 | `NatLe_drop` | PB | apply-in | Lemma vander_4m2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4838 | `NatLe_drop` | PB | apply-in | Lemma vander_4m4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4855 | `NatLe_drop` | PB | apply-in | Lemma vander_4m4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5241 | `NatLe_drop` | PB | apply-in | Lemma esq_row_diff_closed | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5258 | `NatLe_drop` | PB | apply-in | Lemma esq_row_diff_closed | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5326 | `NatLe_drop` | PB | apply-in | Lemma osq_row_diff_closed | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5343 | `NatLe_drop` | PB | apply-in | Lemma osq_row_diff_closed | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5480 | `NatLe_drop` | PB | apply-in | Lemma row_pair_high6 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5515 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5519 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5540 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5544 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5597 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5601 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5641 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5645 | `NatLe_drop` | PB | apply-in | Lemma row_pair_mid2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5791 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5798 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5801 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5838 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5845 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5890 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5900 | `NatLe_drop` | PB | apply-in | Lemma row_pair_main | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5964 | `NatLe_drop` | PB | apply-in | Lemma ksum_diff_row | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6465 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_tail_small | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6549 | `NatLe_lift` | INFO | term-syntax | Lemma exp_partial_odd_lower | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 6652 | `NatLe_drop` | PB | apply-in | Lemma cauchy_real_exp_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6900 | `NatLe_drop` | PB | apply-in | Definition real_inv_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6900 | `NatLe_drop` | PB | apply-in | Definition real_inv_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6910 | `NatLe_lift` | INFO | apply-fwd | Definition real_inv_pos | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 6913 | `NatLe_lift` | INFO | apply-fwd | Definition real_inv_pos | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 6926 | `NatLe_lift` | INFO | apply-fwd | Definition real_inv_pos | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 6974 | `NatLe_lift` | PB | apply-fwd | Lemma real_inv_pos_correct | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 6995 | `NatLe_drop` | PB | apply-in | Lemma real_inv_pos_correct | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7035 | `NatLe_lift` | PB | apply-fwd | Lemma real_inv_pos_pos | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 7058 | `NatLe_drop` | PB | apply-in | Lemma real_inv_pos_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |

### S04_RealExpLogConv.v（17 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 493 | `NatLe_lift` | PB | apply-fwd | Lemma sum_R_le | 否（证明位） | 调用存活5 | W-L1(改名桥) |
| 494 | `NatLe_drop` | PB | apply-fwd | Lemma sum_R_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 499 | `NatLe_lift` | PB | apply-fwd | Lemma sum_R_le | 否（证明位） | 调用存活5 | W-L1(改名桥) |
| 511 | `NatLe_lift` | INFO | apply-fwd | Lemma sum_R_zero | **是（信息位）** | 调用存活5 | W-L2(改名桥→原生) |
| 512 | `NatLe_drop` | PB | apply-fwd | Lemma sum_R_zero | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 515 | `NatLe_lift` | INFO | bare | Lemma sum_R_zero | **是（信息位）** | 调用存活5 | W-L3(原生face重铸) |
| 835 | `NatLe_drop` | PB | apply-fwd | Lemma iterate_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 836 | `NatLe_drop` | PB | apply-fwd | Lemma iterate_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 925 | `NatLe_drop` | PB | apply-fwd | Theorem iterate_cauchy_explicit_N | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 926 | `NatLe_drop` | PB | apply-fwd | Theorem iterate_cauchy_explicit_N | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1106 | `NatLe_drop` | PB | term-syntax | Lemma grad_squeeze_zero | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1340 | `NatLe_lift` | PB | apply-fwd | Theorem gradient_iterate_abs_decay | 否（证明位） | 调用存活5 | W-L1(改名桥) |
| 1342 | `NatLe_lift` | PB | apply-fwd | Theorem gradient_iterate_abs_decay | 否（证明位） | 调用存活5 | W-L1(改名桥) |
| 1372 | `NatLe_lift` | PB | apply-fwd | Theorem grad_decay_positive_iter | 否（证明位） | 调用存活5 | W-L1(改名桥) |
| 1373 | `NatLe_drop` | PB | apply-fwd | Theorem grad_decay_positive_iter | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1378 | `NatLe_lift` | PB | apply-fwd | Theorem grad_decay_positive_iter | 否（证明位） | 调用存活5 | W-L1(改名桥) |
| 1379 | `NatLe_drop` | PB | apply-fwd | Theorem grad_decay_positive_iter | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### S06_DiffSamplingGibbs.v（19 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 4533 | `NatLe_drop` | PB | apply-fwd | Theorem attention_iterate_converges | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5152 | `NatLe_lift` | INFO | apply-fwd | Lemma id_false_true | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5156 | `NatLe_drop` | PB | apply-fwd | Lemma id_false_true | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5156 | `NatLe_lift` | INFO | apply-fwd | Lemma id_false_true | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5157 | `NatLe_drop` | PB | apply-fwd | Lemma id_false_true | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5157 | `NatLe_lift` | INFO | apply-fwd | Lemma id_false_true | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5172 | `NatLe_drop` | PB | apply-fwd | Lemma id_false_true | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5172 | `NatLe_lift` | INFO | apply-fwd | Lemma id_false_true | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5191 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 5191 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 5192 | `NatLe_drop` | PB | term-syntax | Lemma count_heavier_succ_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5193 | `NatLe_lift` | INFO | apply-fwd | Lemma count_heavier_succ_le | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5214 | `NatLe_drop` | PB | apply-fwd | Lemma count_heavier_succ_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5214 | `NatLe_lift` | INFO | apply-fwd | Lemma count_heavier_succ_le | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5215 | `NatLe_drop` | PB | apply-fwd | Lemma count_heavier_succ_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5215 | `NatLe_lift` | INFO | apply-fwd | Lemma count_heavier_succ_le | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5228 | `NatLe_drop` | PB | apply-fwd | Lemma count_heavier_succ_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5228 | `NatLe_lift` | INFO | apply-fwd | Lemma count_heavier_succ_le | **是（信息位）** | 调用存活7 | W-L2(改名桥→原生) |
| 5246 | `NatLe_drop` | PB | term-syntax | Theorem top_k_majorization | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### S07_RealSetoidExpLog.v（177 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 248 | `NatLe_drop` | PB | term-syntax | Lemma real_eq_plus_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 249 | `NatLe_drop` | PB | term-syntax | Lemma real_eq_plus_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 265 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_plus_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 266 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_plus_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 335 | `NatLe_drop` | PB | term-syntax | Lemma real_eq_mult_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 337 | `NatLe_drop` | PB | term-syntax | Lemma real_eq_mult_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 381 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_mult_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 390 | `NatLe_lift` | PB | apply-fwd | Lemma real_eq_mult_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1304 | `NatLe_drop` | PB | apply-in | Lemma q_binom_S | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1362 | `NatLe_drop` | PB | apply-in | Lemma q_binom_S | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1508 | `NatLe_drop` | PB | apply-in | Lemma exp_cauchy_swap | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1542 | `NatLe_drop` | PB | apply-in | Lemma exp_cauchy_double | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1550 | `NatLe_drop` | PB | apply-in | Lemma exp_cauchy_double | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1604 | `NatLe_drop` | PB | apply-in | Lemma exp_trunc_step1 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1622 | `NatLe_drop` | PB | apply-in | Lemma exp_trunc_step2 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1685 | `NatLe_lift` | INFO | apply-fwd | Lemma sum_upto_le_ext | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1685 | `NatLe_drop` | PB | apply-fwd | Lemma sum_upto_le_ext | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1686 | `NatLe_lift` | INFO | apply-fwd | Lemma sum_upto_le_ext | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1916 | `NatLe_drop` | PB | apply-in | Lemma exp_trunc_band_up | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1923 | `NatLe_drop` | PB | apply-in | Lemma exp_trunc_band_up | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2152 | `NatLe_drop` | PB | apply-in | Lemma exp_trunc_arch | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2179 | `NatLe_lift` | INFO | apply-fwd | Lemma exp_trunc_arch | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2179 | `NatLe_drop` | PB | apply-fwd | Lemma exp_trunc_arch | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2233 | `NatLe_drop` | PB | apply-in | Lemma exp_trunc_arch_seq | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2257 | `NatLe_lift` | INFO | apply-fwd | Lemma exp_trunc_arch_seq | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2257 | `NatLe_drop` | PB | apply-fwd | Lemma exp_trunc_arch_seq | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2337 | `NatLe_drop` | PB | apply-in | Lemma cauchy_real_exp_plus | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2354 | `NatLe_lift` | PB | apply-fwd | Lemma cauchy_real_exp_plus | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2355 | `NatLe_lift` | PB | apply-fwd | Lemma cauchy_real_exp_plus | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2367 | `NatLe_lift` | PB | apply-fwd | Lemma cauchy_real_exp_plus | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2436 | `NatLe_drop` | PB | apply-in | Lemma cauchy_real_exp_gt_one | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2444 | `NatLe_lift` | PB | apply-fwd | Lemma cauchy_real_exp_gt_one | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2529 | `NatLe_lift` | PB | apply-fwd | Lemma real_mult_pos_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2529 | `NatLe_drop` | PB | apply-fwd | Lemma real_mult_pos_compat | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2535 | `NatLe_lift` | PB | apply-fwd | Lemma real_mult_pos_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2535 | `NatLe_drop` | PB | apply-fwd | Lemma real_mult_pos_compat | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2695 | `NatLe_lift` | PB | apply-fwd | Lemma cauchy_real_exp_wd | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2695 | `NatLe_drop` | PB | apply-fwd | Lemma cauchy_real_exp_wd | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2841 | `NatLe_lift` | INFO | apply-fwd | Lemma real_arch | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2855 | `NatLe_lift` | INFO | apply-fwd | Lemma real_arch | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2909 | `NatLe_drop` | PB | apply-in | Lemma cauchy_real_exp_gt_const | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2943 | `NatLe_drop` | PB | apply-in | Lemma cauchy_real_exp_unbounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3341 | `NatLe_drop` | PB | term-syntax | Lemma log_testA_true_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3342 | `NatLe_drop` | PB | term-syntax | Lemma log_testA_true_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3347 | `NatLe_lift` | PB | term-syntax | Lemma log_testA_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3348 | `NatLe_lift` | PB | apply-fwd | Lemma log_testA_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3352 | `NatLe_lift` | PB | term-syntax | Lemma log_testA_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3353 | `NatLe_lift` | PB | apply-fwd | Lemma log_testA_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3391 | `NatLe_drop` | PB | term-syntax | Lemma log_testB_true_gt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3392 | `NatLe_drop` | PB | term-syntax | Lemma log_testB_true_gt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3397 | `NatLe_lift` | PB | term-syntax | Lemma log_testB_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3398 | `NatLe_lift` | PB | apply-fwd | Lemma log_testB_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3402 | `NatLe_lift` | PB | term-syntax | Lemma log_testB_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3403 | `NatLe_lift` | PB | apply-fwd | Lemma log_testB_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3471 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 3472 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 3476 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 3477 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 3529 | `NatLe_lift` | PB | apply-fwd | Lemma real_abs_diff_le_lift | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3529 | `NatLe_drop` | PB | apply-fwd | Lemma real_abs_diff_le_lift | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3530 | `NatLe_lift` | PB | apply-fwd | Lemma real_abs_diff_le_lift | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3533 | `NatLe_lift` | PB | apply-fwd | Lemma real_abs_diff_le_lift | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3534 | `NatLe_lift` | PB | apply-fwd | Lemma real_abs_diff_le_lift | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3534 | `NatLe_drop` | PB | apply-fwd | Lemma real_abs_diff_le_lift | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 3760 | `NatLe_lift` | PB | apply-fwd | Lemma exp_lower_lipschitz_q | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3774 | `NatLe_lift` | PB | apply-fwd | Lemma exp_lower_lipschitz_q | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3877 | `NatLe_drop` | PB | apply-in | Lemma real_inv_lt_contra | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3887 | `NatLe_lift` | PB | apply-fwd | Lemma real_inv_lt_contra | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3896 | `NatLe_lift` | PB | apply-fwd | Lemma real_inv_lt_contra | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3951 | `NatLe_lift` | PB | apply-fwd | Lemma real_inv_lt_contra | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3975 | `NatLe_drop` | PB | apply-in | Lemma exp_upper_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4113 | `NatLe_drop` | PB | term-syntax | Lemma log_testA_eps_true_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4114 | `NatLe_drop` | PB | term-syntax | Lemma log_testA_eps_true_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4119 | `NatLe_lift` | PB | term-syntax | Lemma log_testA_eps_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4120 | `NatLe_lift` | PB | apply-fwd | Lemma log_testA_eps_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4124 | `NatLe_lift` | PB | term-syntax | Lemma log_testA_eps_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4125 | `NatLe_lift` | PB | apply-fwd | Lemma log_testA_eps_true_lt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4163 | `NatLe_drop` | PB | term-syntax | Lemma log_testB_eps_true_gt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4164 | `NatLe_drop` | PB | term-syntax | Lemma log_testB_eps_true_gt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4169 | `NatLe_lift` | PB | term-syntax | Lemma log_testB_eps_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4170 | `NatLe_lift` | PB | apply-fwd | Lemma log_testB_eps_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4174 | `NatLe_lift` | PB | term-syntax | Lemma log_testB_eps_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4175 | `NatLe_lift` | PB | apply-fwd | Lemma log_testB_eps_true_gt | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4225 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound_eps | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 4226 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound_eps | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 4230 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound_eps | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 4231 | `NatLe_lift` | INFO | apply-fwd | Lemma log_test_mid_bound_eps | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 4440 | `NatLe_drop` | PB | apply-in | Lemma exp_lower_q | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4510 | `NatLe_drop` | PB | apply-in | Lemma exp_upper_q | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4544 | `NatLe_drop` | PB | term-syntax | Lemma log_interval_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4545 | `NatLe_drop` | PB | term-syntax | Lemma log_interval_lt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4770 | `NatLe_lift` | PB | apply-fwd | Lemma exp_lower_lipschitz_real | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4784 | `NatLe_lift` | PB | apply-fwd | Lemma exp_lower_lipschitz_real | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4806 | `NatLe_lift` | PB | apply-fwd | Lemma exp_lower_lipschitz_real | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 4920 | `NatLe_drop` | PB | term-syntax | Lemma approx_span_pt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4921 | `NatLe_drop` | PB | term-syntax | Lemma approx_span_pt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4932 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4933 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4936 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4937 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4938 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4939 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4992 | `NatLe_lift` | PB | apply-fwd | Lemma real_abs_lift | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5062 | `NatLe_drop` | PB | apply-in | Lemma approx_root | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5062 | `NatLe_drop` | PB | apply-in | Lemma approx_root | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5161 | `NatLe_drop` | PB | apply-in | Lemma approx_root | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5289 | `NatLe_drop` | PB | term-syntax | Lemma lower_lipschitz_pt | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5356 | `NatLe_lift` | INFO | apply-fwd | Lemma lower_lipschitz_combine3 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5395 | `NatLe_lift` | INFO | term-syntax | Lemma lower_lipschitz_combine3 | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 5402 | `NatLe_lift` | INFO | term-syntax | Lemma lower_lipschitz_combine3 | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 5414 | `NatLe_lift` | INFO | apply-fwd | Lemma lower_lipschitz_combine3 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5493 | `NatLe_drop` | PB | apply-in | Lemma log_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5493 | `NatLe_drop` | PB | apply-in | Lemma log_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5714 | `NatLe_lift` | PB | apply-fwd | Lemma cw_log_exp_right | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5714 | `NatLe_lift` | PB | apply-fwd | Lemma cw_log_exp_right | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5728 | `NatLe_drop` | PB | term-syntax | Lemma cw_log_exp_right | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5729 | `NatLe_drop` | PB | term-syntax | Lemma cw_log_exp_right | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5761 | `NatLe_lift` | PB | term-syntax | Lemma cw_log_exp_right | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5803 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_not_eq | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5805 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_not_eq | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5891 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5891 | `NatLe_drop` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5892 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5895 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5895 | `NatLe_drop` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5896 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5953 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5953 | `NatLe_drop` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5954 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5957 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5957 | `NatLe_drop` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 5958 | `NatLe_lift` | PB | apply-fwd | Lemma real_weak_trich | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6005 | `NatLe_drop` | PB | term-syntax | Lemma real_weak_trich | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6134 | `NatLe_drop` | PB | term-syntax | Lemma real_mult_lt_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6135 | `NatLe_drop` | PB | term-syntax | Lemma real_mult_lt_compat | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6145 | `NatLe_lift` | PB | apply-fwd | Lemma real_mult_lt_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6165 | `NatLe_lift` | PB | apply-fwd | Lemma real_mult_lt_compat | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6408 | `NatLe_lift` | INFO | apply-fwd | Lemma log_mid_sign | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6424 | `NatLe_lift` | INFO | apply-fwd | Lemma log_mid_sign | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6435 | `NatLe_lift` | INFO | apply-fwd | Lemma log_mid_sign | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6480 | `NatLe_lift` | INFO | term-syntax | Lemma log_mid_sign | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 6549 | `NatLe_lift` | INFO | apply-fwd | Lemma log_mid_diff | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6563 | `NatLe_lift` | INFO | apply-fwd | Lemma log_mid_diff | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6572 | `NatLe_lift` | INFO | apply-fwd | Lemma log_mid_diff | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6769 | `NatLe_drop` | PB | term-syntax | Lemma real_log_lt_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6770 | `NatLe_drop` | PB | term-syntax | Lemma real_log_lt_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6771 | `NatLe_drop` | PB | term-syntax | Lemma real_log_lt_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6773 | `NatLe_lift` | PB | apply-fwd | Lemma real_log_lt_mono | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6773 | `NatLe_lift` | PB | apply-fwd | Lemma real_log_lt_mono | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6775 | `NatLe_lift` | PB | apply-fwd | Lemma real_log_lt_mono | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6775 | `NatLe_lift` | PB | apply-fwd | Lemma real_log_lt_mono | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7365 | `NatLe_lift` | INFO | apply-fwd | Definition real_min | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7365 | `NatLe_drop` | PB | apply-fwd | Definition real_min | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7366 | `NatLe_lift` | INFO | apply-fwd | Definition real_min | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7366 | `NatLe_drop` | PB | apply-fwd | Definition real_min | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7369 | `NatLe_lift` | INFO | apply-fwd | Definition real_min | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7369 | `NatLe_drop` | PB | apply-fwd | Definition real_min | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7370 | `NatLe_lift` | INFO | apply-fwd | Definition real_min | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7370 | `NatLe_drop` | PB | apply-fwd | Definition real_min | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7395 | `NatLe_lift` | INFO | apply-fwd | Definition real_max | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7395 | `NatLe_drop` | PB | apply-fwd | Definition real_max | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7396 | `NatLe_lift` | INFO | apply-fwd | Definition real_max | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7396 | `NatLe_drop` | PB | apply-fwd | Definition real_max | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7399 | `NatLe_lift` | INFO | apply-fwd | Definition real_max | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7399 | `NatLe_drop` | PB | apply-fwd | Definition real_max | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7400 | `NatLe_lift` | INFO | apply-fwd | Definition real_max | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 7400 | `NatLe_drop` | PB | apply-fwd | Definition real_max | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7728 | `NatLe_lift` | PB | apply-fwd | Lemma real_min_pos | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7728 | `NatLe_drop` | PB | apply-fwd | Lemma real_min_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7736 | `NatLe_lift` | PB | apply-fwd | Lemma real_min_pos | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7736 | `NatLe_drop` | PB | apply-fwd | Lemma real_min_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 8557 | `NatLe_drop` | PB | apply-in | Lemma exp_partial_ge_linear_aux4 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8607 | `NatLe_drop` | PB | term-syntax | Lemma real_exp_ge_linear_eps | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 8608 | `NatLe_drop` | PB | term-syntax | Lemma real_exp_ge_linear_eps | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 8611 | `NatLe_lift` | PB | apply-fwd | Lemma real_exp_ge_linear_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 8646 | `NatLe_drop` | PB | apply-in | Lemma real_exp_ge_linear_eps | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8648 | `NatLe_lift` | PB | apply-fwd | Lemma real_exp_ge_linear_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |

### S08_RealMainlineDPO.v（34 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 3911 | `NatLe_drop` | PB | apply-in | Lemma real_quad_div_le_two_eps | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3928 | `NatLe_lift` | PB | term-syntax | Lemma real_quad_div_le_two_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 3940 | `NatLe_lift` | PB | term-syntax | Lemma real_quad_div_le_two_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4273 | `NatLe_drop` | PB | apply-in | Lemma real_abs_le_quad_ll | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4290 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ll | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4297 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ll | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4304 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ll | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4345 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ll | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4352 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ll | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4429 | `NatLe_drop` | PB | apply-in | Lemma real_abs_le_quad_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4446 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4453 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4460 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4503 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4512 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4615 | `NatLe_drop` | PB | apply-in | Lemma real_abs_le_quad_ee | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4632 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ee | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4639 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ee | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4646 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ee | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4689 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ee | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4698 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_ee | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4791 | `NatLe_drop` | PB | apply-in | Lemma real_abs_le_quad_el | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4808 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_el | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4815 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_el | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4822 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_el | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4866 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_el | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 4873 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_le_quad_el | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 5025 | `NatLe_drop` | PB | apply-in | Lemma real_quad_t_le_h_eps | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5044 | `NatLe_lift` | PB | term-syntax | Lemma real_quad_t_le_h_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 5054 | `NatLe_lift` | PB | term-syntax | Lemma real_quad_t_le_h_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 5097 | `NatLe_lift` | PB | term-syntax | Lemma real_quad_t_le_h_eps | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 5523 | `NatLe_drop` | PB | apply-in | Lemma real_log_differentiable | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5545 | `NatLe_lift` | PB | term-syntax | Lemma real_log_differentiable | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 5552 | `NatLe_lift` | PB | term-syntax | Lemma real_log_differentiable | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### S09_EntropyReal.v（74 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 621 | `NatLe_drop` | PB | apply-in | Lemma real_abs_prod_le_eps | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 637 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_prod_le_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 656 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_prod_le_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 660 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_prod_le_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1054 | `NatLe_drop` | PB | apply-in | Lemma real_le_eps_Kone | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1065 | `NatLe_lift` | PB | term-syntax | Lemma real_le_eps_Kone | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1073 | `NatLe_lift` | PB | term-syntax | Lemma real_le_eps_Kone | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1082 | `NatLe_lift` | PB | term-syntax | Lemma real_le_eps_Kone | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1125 | `NatLe_drop` | PB | apply-in | Lemma real_abs_h_sq_le_eps | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1138 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_h_sq_le_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1153 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_h_sq_le_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1163 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_h_sq_le_eps | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1251 | `NatLe_drop` | PB | apply-in | Lemma real_scal_sum_ge | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1271 | `NatLe_lift` | PB | term-syntax | Lemma real_scal_sum_ge | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1283 | `NatLe_lift` | PB | term-syntax | Lemma real_scal_sum_ge | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1295 | `NatLe_lift` | PB | term-syntax | Lemma real_scal_sum_ge | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1307 | `NatLe_lift` | PB | term-syntax | Lemma real_scal_sum_ge | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1497 | `NatLe_drop` | PB | apply-in | Lemma real_inv_proj | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1544 | `NatLe_drop` | PB | apply-fwd | Lemma q_fact_two | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1631 | `NatLe_drop` | PB | apply-in | Lemma exp_minus_one_linear | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1659 | `NatLe_lift` | INFO | term-syntax | Lemma exp_minus_one_linear | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1664 | `NatLe_lift` | INFO | term-syntax | Lemma exp_minus_one_linear | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1682 | `NatLe_lift` | INFO | term-syntax | Lemma exp_minus_one_linear | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1691 | `NatLe_lift` | INFO | bare | Lemma exp_minus_one_linear | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1750 | `NatLe_lift` | INFO | term-syntax | Lemma exp_minus_one_linear | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1768 | `NatLe_lift` | INFO | term-syntax | Lemma exp_minus_one_linear | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1878 | `NatLe_drop` | PB | apply-in | Lemma real_abs_scaling_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1904 | `NatLe_lift` | PB | bare | Lemma real_abs_scaling_le | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1922 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_scaling_le | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1929 | `NatLe_lift` | PB | term-syntax | Lemma real_abs_scaling_le | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2693 | `NatLe_drop` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2778 | `NatLe_drop` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2783 | `NatLe_drop` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2790 | `NatLe_drop` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2797 | `NatLe_drop` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2846 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2862 | `NatLe_lift` | PB | apply-fwd | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 2879 | `NatLe_lift` | PB | apply-fwd | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3178 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3189 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3200 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3222 | `NatLe_lift` | PB | apply-fwd | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3235 | `NatLe_lift` | PB | apply-fwd | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3244 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3256 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3336 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3485 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3493 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3512 | `NatLe_lift` | PB | term-syntax | Lemma real_differentiable_mult | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5085 | `NatLe_lift` | PB | apply-fwd | Theorem real_gradient_iterate_abs_decay | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5087 | `NatLe_lift` | PB | apply-fwd | Theorem real_gradient_iterate_abs_decay | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5116 | `NatLe_drop` | PB | apply-in | Theorem real_grad_decay_positive_iter | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5116 | `NatLe_lift` | PB | apply-in | Theorem real_grad_decay_positive_iter | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5121 | `NatLe_drop` | PB | apply-in | Theorem real_grad_decay_positive_iter | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5121 | `NatLe_lift` | PB | apply-in | Theorem real_grad_decay_positive_iter | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5313 | `NatLe_drop` | PB | apply-in | Theorem real_sign_preservation_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5324 | `NatLe_lift` | PB | term-syntax | Theorem real_sign_preservation_pos | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5335 | `NatLe_lift` | PB | term-syntax | Theorem real_sign_preservation_pos | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5351 | `NatLe_lift` | PB | term-syntax | Theorem real_sign_preservation_pos | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5485 | `NatLe_drop` | PB | apply-in | Theorem real_sign_preservation_neg | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5495 | `NatLe_lift` | PB | term-syntax | Theorem real_sign_preservation_neg | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5509 | `NatLe_lift` | PB | term-syntax | Theorem real_sign_preservation_neg | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 5524 | `NatLe_lift` | PB | term-syntax | Theorem real_sign_preservation_neg | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6196 | `NatLe_lift` | PB | apply-fwd | Theorem real_gradient_iterate_abs_decay_neg | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6221 | `NatLe_drop` | PB | apply-in | Theorem real_grad_decay_negative_iter | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6221 | `NatLe_lift` | PB | apply-in | Theorem real_grad_decay_negative_iter | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6225 | `NatLe_drop` | PB | apply-in | Theorem real_grad_decay_negative_iter | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6225 | `NatLe_lift` | PB | apply-in | Theorem real_grad_decay_negative_iter | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6831 | `NatLe_drop` | PB | apply-in | Lemma real_exp_ge_linear | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6842 | `NatLe_lift` | PB | apply-fwd | Lemma real_exp_ge_linear | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6885 | `NatLe_drop` | PB | apply-in | Lemma real_exp_le_inv_one_minus | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6895 | `NatLe_lift` | PB | term-syntax | Lemma real_exp_le_inv_one_minus | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6903 | `NatLe_lift` | PB | apply-fwd | Lemma real_exp_le_inv_one_minus | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6912 | `NatLe_lift` | PB | apply-fwd | Lemma real_exp_le_inv_one_minus | 否（证明位） | 调用存活1 | W-L1(改名桥) |

### S10_KVQuantTrig.v（154 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 1647 | `NatLe_drop` | PB | bare | Lemma sc_sin_diff_bound2 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1673 | `NatLe_drop` | PB | bare | Lemma sc_cos_diff_bound2 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1689 | `NatLe_lift` | INFO | apply-fwd | Lemma sc_sin_partial_cauchy_bounded | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1695 | `NatLe_drop` | PB | apply-in | Lemma sc_sin_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1695 | `NatLe_drop` | PB | apply-in | Lemma sc_sin_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1706 | `NatLe_drop` | PB | bare | Lemma sc_sin_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1719 | `NatLe_drop` | PB | bare | Lemma sc_sin_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1735 | `NatLe_lift` | INFO | apply-fwd | Lemma sc_cos_partial_cauchy_bounded | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1741 | `NatLe_drop` | PB | apply-in | Lemma sc_cos_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1741 | `NatLe_drop` | PB | apply-in | Lemma sc_cos_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1750 | `NatLe_drop` | PB | bare | Lemma sc_cos_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1763 | `NatLe_drop` | PB | bare | Lemma sc_cos_partial_cauchy_bounded | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 2299 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_sin | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2299 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_sin | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2300 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_sin | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2300 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_sin | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2309 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_sin | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2309 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_sin | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2310 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_sin | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2310 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_sin | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2396 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_cos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2396 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_cos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2397 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_cos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2397 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_cos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2406 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_cos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2406 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_cos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2407 | `NatLe_lift` | INFO | apply-fwd | Definition cauchy_real_cos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2407 | `NatLe_drop` | PB | apply-fwd | Definition cauchy_real_cos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2560 | `NatLe_drop` | PB | apply-in | Lemma real_cos_two_neg | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2673 | `NatLe_drop` | PB | apply-in | Lemma real_cos_one_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2689 | `NatLe_drop` | PB | apply-in | Lemma real_sin_one_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3025 | `NatLe_drop` | PB | apply-in | Definition cauchy_real_pi_leibniz | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3048 | `NatLe_drop` | PB | apply-in | Definition cauchy_real_pi_leibniz | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3085 | `NatLe_drop` | PB | apply-in | Lemma real_pi_leibniz_gt_three | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3180 | `NatLe_drop` | PB | apply-in | Lemma real_cos_one_lt_one | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3311 | `NatLe_drop` | PB | apply-in | Lemma real_cos_three_halves_pos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3328 | `NatLe_drop` | PB | apply-in | Lemma real_cos_five_thirds_neg | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4335 | `NatLe_drop` | PB | term-syntax | Lemma real_sin_lt_x | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4336 | `NatLe_drop` | PB | term-syntax | Lemma real_sin_lt_x | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4337 | `NatLe_drop` | PB | term-syntax | Lemma real_sin_lt_x | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4338 | `NatLe_lift` | PB | term-syntax | Lemma real_sin_lt_x | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4339 | `NatLe_lift` | PB | term-syntax | Lemma real_sin_lt_x | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4389 | `NatLe_drop` | PB | term-syntax | Lemma real_x_minus_cube_lt_sin | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4390 | `NatLe_drop` | PB | term-syntax | Lemma real_x_minus_cube_lt_sin | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4391 | `NatLe_drop` | PB | term-syntax | Lemma real_x_minus_cube_lt_sin | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4392 | `NatLe_lift` | PB | term-syntax | Lemma real_x_minus_cube_lt_sin | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4393 | `NatLe_lift` | PB | term-syntax | Lemma real_x_minus_cube_lt_sin | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4668 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_lt_one | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4669 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_lt_one | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4670 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_lt_one | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4671 | `NatLe_lift` | PB | term-syntax | Lemma real_cos_lt_one | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4672 | `NatLe_lift` | PB | term-syntax | Lemma real_cos_lt_one | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4723 | `NatLe_drop` | PB | term-syntax | Lemma real_one_minus_half_lt_cos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4724 | `NatLe_drop` | PB | term-syntax | Lemma real_one_minus_half_lt_cos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4725 | `NatLe_drop` | PB | term-syntax | Lemma real_one_minus_half_lt_cos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 4726 | `NatLe_lift` | PB | term-syntax | Lemma real_one_minus_half_lt_cos | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4727 | `NatLe_lift` | PB | term-syntax | Lemma real_one_minus_half_lt_cos | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4911 | `NatLe_drop` | PB | apply-in | Lemma real_sin_one_lt_one | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4936 | `NatLe_drop` | PB | apply-in | Lemma real_sin_one_gt_five_six | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4970 | `NatLe_drop` | PB | apply-in | Lemma real_cos_one_gt_half | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5410 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_cdeg_sum | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5429 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_ddeg_sum | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5492 | `NatLe_drop` | PB | term-syntax | Lemma sc_sq_rect_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 5532 | `NatLe_drop` | PB | term-syntax | Lemma sc_sin_sq_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6134 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_band_c_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6156 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_band_c_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6304 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_band_d_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6313 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_band_d_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6537 | `NatLe_lift` | INFO | apply-in | Lemma sc_div2_le | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6537 | `NatLe_drop` | PB | apply-in | Lemma sc_div2_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6555 | `NatLe_lift` | INFO | apply-in | Lemma sc_div2_ge | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6555 | `NatLe_drop` | PB | apply-in | Lemma sc_div2_ge | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6588 | `NatLe_drop` | PB | apply-fwd | Lemma sc_cs_sq_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 6588 | `NatLe_drop` | PB | apply-fwd | Lemma sc_cs_sq_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 6591 | `NatLe_drop` | PB | term-syntax | Lemma sc_cs_sq_err_bound | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6598 | `NatLe_lift` | INFO | apply-fwd | Lemma sc_cs_sq_err_bound | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6598 | `NatLe_drop` | PB | apply-fwd | Lemma sc_cs_sq_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 6830 | `NatLe_drop` | PB | term-syntax | Lemma real_sin_pos_lt_two | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6831 | `NatLe_drop` | PB | term-syntax | Lemma real_sin_pos_lt_two | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 6832 | `NatLe_lift` | PB | term-syntax | Lemma real_sin_pos_lt_two | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 6833 | `NatLe_lift` | PB | term-syntax | Lemma real_sin_pos_lt_two | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 6934 | `NatLe_drop` | PB | apply-in | Lemma sc_qpow_diff_factor | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7035 | `NatLe_drop` | PB | apply-in | Lemma sc_A_succ | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7519 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 7520 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 7521 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 7522 | `NatLe_drop` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 7523 | `NatLe_lift` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7524 | `NatLe_lift` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7525 | `NatLe_lift` | PB | term-syntax | Lemma real_cos_strict_decr | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7681 | `NatLe_lift` | PB | apply-fwd | Lemma cos_testA_eps_true_lt | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7728 | `NatLe_lift` | PB | apply-fwd | Lemma cos_testB_eps_true_gt | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7778 | `NatLe_lift` | INFO | apply-fwd | Lemma cos_test_mid_bound | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7779 | `NatLe_lift` | INFO | apply-fwd | Lemma cos_test_mid_bound | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7933 | `NatLe_drop` | PB | apply-fwd | Lemma cos_scan_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 8076 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt_cos | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8077 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt_cos | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8080 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt_cos | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8081 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt_cos | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8082 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt_cos | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8083 | `NatLe_lift` | INFO | term-syntax | Lemma approx_span_pt_cos | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8261 | `NatLe_lift` | INFO | apply-fwd | Lemma approx_root_cos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 8472 | `NatLe_drop` | PB | term-syntax | Lemma cos_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 8476 | `NatLe_drop` | PB | term-syntax | Lemma cos_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 8511 | `NatLe_lift` | INFO | term-syntax | Lemma cos_seq_cauchy | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8512 | `NatLe_lift` | INFO | term-syntax | Lemma cos_seq_cauchy | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8531 | `NatLe_lift` | INFO | term-syntax | Lemma cos_seq_cauchy | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8532 | `NatLe_lift` | INFO | term-syntax | Lemma cos_seq_cauchy | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 8617 | `NatLe_lift` | PB | term-syntax | Lemma real_cos_pi_half_zero | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 8620 | `NatLe_drop` | PB | apply-in | Lemma real_cos_pi_half_zero | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8631 | `NatLe_lift` | PB | apply-fwd | Lemma real_cos_pi_half_zero | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 8631 | `NatLe_lift` | PB | apply-fwd | Lemma real_cos_pi_half_zero | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 8722 | `NatLe_lift` | INFO | apply-fwd | Lemma cos_eq_zero_diag_bound | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 8742 | `NatLe_lift` | INFO | apply-fwd | Lemma real_lt_lower_pt | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 8759 | `NatLe_lift` | INFO | apply-fwd | Lemma real_lt_upper_pt | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 8789 | `NatLe_drop` | PB | term-syntax | Lemma cos_pi_half_unique | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 8790 | `NatLe_drop` | PB | term-syntax | Lemma cos_pi_half_unique | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 9080 | `NatLe_drop` | PB | term-syntax | Lemma real_sq_eq_one_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 9081 | `NatLe_drop` | PB | term-syntax | Lemma real_sq_eq_one_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 9082 | `NatLe_lift` | PB | apply-fwd | Lemma real_sq_eq_one_pos | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 9083 | `NatLe_lift` | PB | apply-fwd | Lemma real_sq_eq_one_pos | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 9349 | `NatLe_drop` | PB | apply-fwd | Lemma real_lt_three_halves_cos_pi_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 9356 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_three_halves_cos_pi_half | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 9482 | `NatLe_drop` | PB | apply-fwd | Lemma real_lt_cos_pi_half_five_thirds | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 9488 | `NatLe_lift` | PB | apply-fwd | Lemma real_lt_cos_pi_half_five_thirds | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 9649 | `NatLe_drop` | PB | term-syntax | Lemma cos_pi_half_unique_widened | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 9650 | `NatLe_drop` | PB | term-syntax | Lemma cos_pi_half_unique_widened | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 10356 | `NatLe_drop` | PB | apply-in | Lemma sc_add_sin_diag_term | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 10366 | `NatLe_drop` | PB | apply-in | Lemma sc_add_sin_diag_term | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 10433 | `NatLe_drop` | PB | apply-in | Lemma sc_add_cos_diag_term | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 10444 | `NatLe_drop` | PB | apply-in | Lemma sc_add_cos_diag_term | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 10629 | `NatLe_drop` | PB | apply-in | Lemma sc_band_top_FT | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 10697 | `NatLe_drop` | PB | apply-in | Lemma sc_band_right_FT | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11034 | `NatLe_drop` | PB | apply-in | Lemma sc_add_band_abs | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11055 | `NatLe_drop` | PB | apply-in | Lemma sc_add_band_abs | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11280 | `NatLe_drop` | PB | apply-in | Lemma sc_add_sin_err_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11286 | `NatLe_lift` | INFO | apply-fwd | Lemma sc_add_sin_err_bound | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 11299 | `NatLe_drop` | PB | apply-fwd | Lemma sc_add_sin_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 11302 | `NatLe_drop` | PB | apply-fwd | Lemma sc_add_sin_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 11382 | `NatLe_drop` | PB | apply-in | Lemma rs_add_sin | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11403 | `NatLe_lift` | PB | apply-fwd | Lemma rs_add_sin | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 11404 | `NatLe_lift` | PB | apply-fwd | Lemma rs_add_sin | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 11408 | `NatLe_lift` | PB | apply-fwd | Lemma rs_add_sin | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 11507 | `NatLe_drop` | PB | bare | Lemma sc_cos_add_tri_step | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 11976 | `NatLe_drop` | PB | apply-in | Lemma sc_add_cos_anti_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11992 | `NatLe_drop` | PB | term-syntax | Lemma sc_add_cos_anti_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 12207 | `NatLe_drop` | PB | apply-in | Lemma sc_add_cos_err_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 12213 | `NatLe_lift` | INFO | apply-fwd | Lemma sc_add_cos_err_bound | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 12226 | `NatLe_drop` | PB | apply-fwd | Lemma sc_add_cos_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 12230 | `NatLe_drop` | PB | apply-fwd | Lemma sc_add_cos_err_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 12330 | `NatLe_drop` | PB | apply-in | Lemma rs_add_cos | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 12356 | `NatLe_lift` | PB | apply-fwd | Lemma rs_add_cos | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 12357 | `NatLe_lift` | PB | apply-fwd | Lemma rs_add_cos | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 12361 | `NatLe_lift` | PB | apply-fwd | Lemma rs_add_cos | 否（证明位） | 调用存活2 | W-L1(改名桥) |

### S11_TP3B5.v（91 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 460 | `NatLe_drop` | PB | apply-in | Lemma arctan_partial_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 473 | `NatLe_drop` | PB | apply-in | Lemma arctan_partial_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 855 | `NatLe_drop` | PB | apply-in | Definition cauchy_real_arctan | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 856 | `NatLe_drop` | PB | apply-in | Definition cauchy_real_arctan | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 899 | `NatLe_lift` | INFO | apply-in | Definition cauchy_real_arctan | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 899 | `NatLe_drop` | PB | apply-in | Definition cauchy_real_arctan | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 900 | `NatLe_lift` | INFO | apply-in | Definition cauchy_real_arctan | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 900 | `NatLe_drop` | PB | apply-in | Definition cauchy_real_arctan | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1628 | `NatLe_drop` | PB | apply-in | Lemma a3_h4_value_bridge | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2051 | `NatLe_drop` | PB | apply-in | Lemma real_sin_zero_linear_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2077 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2082 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2100 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2106 | `NatLe_lift` | INFO | bare | Lemma real_sin_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2129 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2153 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2219 | `NatLe_drop` | PB | apply-in | Lemma real_cos_zero_linear_bound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2245 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2250 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2268 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2274 | `NatLe_lift` | INFO | bare | Lemma real_cos_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2297 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2319 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_zero_linear_bound | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2771 | `NatLe_drop` | PB | apply-in | Lemma real_sin_deriv_linear | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2823 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2844 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2872 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2881 | `NatLe_lift` | INFO | term-syntax | Lemma real_sin_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 2887 | `NatLe_lift` | INFO | apply-fwd | Lemma real_sin_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 3080 | `NatLe_drop` | PB | apply-in | Lemma real_cos_deriv_linear | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3134 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 3155 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 3183 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 3192 | `NatLe_lift` | INFO | term-syntax | Lemma real_cos_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 3198 | `NatLe_lift` | INFO | apply-fwd | Lemma real_cos_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 4494 | `NatLe_drop` | PB | apply-in | Lemma b3r_geom_decay | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4701 | `NatLe_drop` | PB | apply-in | Lemma real_arctan_deriv_linear | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4717 | `NatLe_lift` | INFO | term-syntax | Lemma real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 4726 | `NatLe_lift` | INFO | term-syntax | Lemma real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 4732 | `NatLe_lift` | INFO | apply-fwd | Lemma real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 4753 | `NatLe_lift` | INFO | apply-fwd | Lemma real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 4804 | `NatLe_lift` | INFO | term-syntax | Lemma real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 4835 | `NatLe_lift` | INFO | apply-fwd | Lemma real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 5096 | `NatLe_drop` | PB | apply-in | Lemma b3rr_qdecay | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5650 | `NatLe_drop` | PB | apply-in | Lemma b3rr_real_arctan_deriv_linear | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5666 | `NatLe_lift` | INFO | term-syntax | Lemma b3rr_real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 5675 | `NatLe_lift` | INFO | term-syntax | Lemma b3rr_real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 5681 | `NatLe_lift` | INFO | apply-fwd | Lemma b3rr_real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 5708 | `NatLe_lift` | INFO | apply-fwd | Lemma b3rr_real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 5759 | `NatLe_lift` | INFO | term-syntax | Lemma b3rr_real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 5790 | `NatLe_lift` | INFO | apply-fwd | Lemma b3rr_real_arctan_deriv_linear | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 6581 | `NatLe_drop` | PB | apply-in | Lemma b4_arch_step | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7005 | `NatLe_drop` | PB | term-syntax | Lemma b5b_ap_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 7145 | `NatLe_drop` | PB | term-syntax | Lemma b5b_ap_uniform | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 7234 | `NatLe_drop` | PB | apply-in | Lemma b5b_arctan_cont_unit | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7263 | `NatLe_lift` | INFO | term-syntax | Lemma b5b_arctan_cont_unit | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 7278 | `NatLe_lift` | INFO | bare | Lemma b5b_arctan_cont_unit | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 8159 | `NatLe_drop` | PB | apply-in | Lemma b5c_inv_half_two | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8161 | `NatLe_lift` | PB | apply-fwd | Lemma b5c_inv_half_two | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 8657 | `NatLe_drop` | PB | apply-in | Lemma b5c_d_proj_le_one | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8657 | `NatLe_lift` | INFO | apply-in | Lemma b5c_d_proj_le_one | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 9573 | `NatLe_drop` | PB | apply-in | Lemma b5i_abs_le_pointwise | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 9587 | `NatLe_lift` | INFO | term-syntax | Lemma b5i_abs_le_pointwise | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 9600 | `NatLe_lift` | INFO | term-syntax | Lemma b5i_abs_le_pointwise | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 9611 | `NatLe_drop` | PB | apply-in | Lemma b5i_abs_le_pointwise | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 9630 | `NatLe_lift` | INFO | term-syntax | Lemma b5i_abs_le_pointwise | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 9646 | `NatLe_lift` | INFO | term-syntax | Lemma b5i_abs_le_pointwise | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 9941 | `NatLe_drop` | PB | apply-in | Lemma b5i_h_inv_quarter | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 9942 | `NatLe_lift` | INFO | apply-fwd | Lemma b5i_h_inv_quarter | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 9943 | `NatLe_lift` | INFO | apply-fwd | Lemma b5i_h_inv_quarter | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 9944 | `NatLe_lift` | INFO | apply-fwd | Lemma b5i_h_inv_quarter | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 11309 | `NatLe_drop` | PB | apply-in | Lemma b5b_sin_cont | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11325 | `NatLe_lift` | INFO | term-syntax | Lemma b5b_sin_cont | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 11358 | `NatLe_lift` | INFO | term-syntax | Lemma b5b_sin_cont | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 11568 | `NatLe_drop` | PB | apply-in | Lemma b5b_cos_cont | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11583 | `NatLe_lift` | INFO | term-syntax | Lemma b5b_cos_cont | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 11617 | `NatLe_lift` | INFO | term-syntax | Lemma b5b_cos_cont | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 11880 | `NatLe_drop` | PB | apply-in | Lemma b5b_endpoint | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11907 | `NatLe_lift` | PB | term-syntax | Lemma b5b_endpoint | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 11914 | `NatLe_lift` | PB | term-syntax | Lemma b5b_endpoint | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 12370 | `NatLe_drop` | PB | apply-in | Lemma b5n_absorbQ | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 12371 | `NatLe_lift` | INFO | apply-fwd | Lemma b5n_absorbQ | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12372 | `NatLe_lift` | INFO | apply-fwd | Lemma b5n_absorbQ | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12373 | `NatLe_lift` | INFO | apply-fwd | Lemma b5n_absorbQ | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12867 | `NatLe_drop` | PB | apply-in | Lemma b5a_sin_atan_diff | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 12872 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12873 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12874 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12875 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12876 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 12898 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_sin_atan_diff | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### S12_B5RecycleSF.v（112 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 76 | `NatLe_drop` | PB | apply-in | Lemma b5c_inv_pos_cert_eq | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 79 | `NatLe_lift` | PB | term-syntax | Lemma b5c_inv_pos_cert_eq | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 79 | `NatLe_lift` | PB | term-syntax | Lemma b5c_inv_pos_cert_eq | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 437 | `NatLe_drop` | PB | apply-in | Lemma b5a_sin_atan_diff_closed_r | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 442 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 443 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 444 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 445 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 446 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_sin_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 468 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_sin_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 1830 | `NatLe_drop` | PB | apply-in | Lemma b5a_cos_atan_diff_closed_r | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1835 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_cos_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1836 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_cos_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1837 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_cos_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1838 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_cos_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1839 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_cos_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 1862 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_cos_atan_diff_closed_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 2323 | `NatLe_drop` | PB | apply-in | Lemma b5a_E_diff_closed_r | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2328 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2329 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2330 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2331 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2332 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2333 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 2436 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_E_diff_closed_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 2946 | `NatLe_drop` | PB | apply-in | Lemma b5f_log_diff_dx | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2968 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_log_diff_dx | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 2974 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_log_diff_dx | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 3151 | `NatLe_drop` | PB | apply-in | Lemma b5f_Du_abs_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3190 | `NatLe_lift` | PB | term-syntax | Lemma b5f_Du_abs_le | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 3259 | `NatLe_lift` | PB | term-syntax | Lemma b5f_Du_abs_le | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 3664 | `NatLe_drop` | PB | apply-in | Lemma b5f_Du_act_delta | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3676 | `NatLe_lift` | PB | term-syntax | Lemma b5f_Du_act_delta | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 3690 | `NatLe_lift` | PB | term-syntax | Lemma b5f_Du_act_delta | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 3717 | `NatLe_lift` | PB | term-syntax | Lemma b5f_Du_act_delta | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 3851 | `NatLe_drop` | PB | apply-in | Lemma b5f_gdiff_pts_r | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3852 | `NatLe_lift` | INFO | apply-fwd | Lemma b5f_gdiff_pts_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 3872 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_gdiff_pts_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 3878 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_gdiff_pts_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 3888 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_gdiff_pts_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 3909 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_gdiff_pts_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 3928 | `NatLe_lift` | INFO | term-syntax | Lemma b5f_gdiff_pts_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 4322 | `NatLe_drop` | PB | apply-in | Lemma b5j_real_le_m_pts | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4332 | `NatLe_lift` | INFO | term-syntax | Lemma b5j_real_le_m_pts | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 4353 | `NatLe_lift` | INFO | term-syntax | Lemma b5j_real_le_m_pts | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 4360 | `NatLe_drop` | PB | apply-in | Lemma b5j_real_le_m_pts | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4381 | `NatLe_lift` | INFO | term-syntax | Lemma b5j_real_le_m_pts | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 4393 | `NatLe_lift` | INFO | term-syntax | Lemma b5j_real_le_m_pts | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 4803 | `NatLe_drop` | PB | apply-in | Lemma b5j_v_abs_bd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 4825 | `NatLe_lift` | PB | term-syntax | Lemma b5j_v_abs_bd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4838 | `NatLe_lift` | PB | term-syntax | Lemma b5j_v_abs_bd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4841 | `NatLe_lift` | PB | term-syntax | Lemma b5j_v_abs_bd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4867 | `NatLe_lift` | PB | term-syntax | Lemma b5j_v_abs_bd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 4995 | `NatLe_drop` | PB | apply-in | Lemma b5j_v_act_lt | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5012 | `NatLe_lift` | PB | term-syntax | Lemma b5j_v_act_lt | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 6048 | `NatLe_drop` | PB | apply-in | Lemma b5a_S_diff_closed_r | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6053 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_S_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6054 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_S_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6055 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_S_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6056 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_S_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6057 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_S_diff_closed_r | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6339 | `NatLe_drop` | PB | apply-in | Lemma b5m_J_dec_proj | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6348 | `NatLe_lift` | INFO | term-syntax | Lemma b5m_J_dec_proj | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 6352 | `NatLe_lift` | INFO | term-syntax | Lemma b5m_J_dec_proj | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 6366 | `NatLe_lift` | INFO | term-syntax | Lemma b5m_J_dec_proj | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 6367 | `NatLe_lift` | INFO | term-syntax | Lemma b5m_J_dec_proj | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 6853 | `NatLe_drop` | PB | apply-in | Lemma b5a_J_deriv_zero | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6865 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6866 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6867 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6868 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6869 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6870 | `NatLe_lift` | INFO | apply-fwd | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 6886 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 6888 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 7179 | `NatLe_lift` | INFO | term-syntax | Lemma b5a_J_deriv_zero | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 7310 | `NatLe_drop` | PB | apply-fwd | Definition b5m_tailtrunc | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7314 | `NatLe_drop` | PB | apply-fwd | Definition b5m_tailtrunc | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7316 | `NatLe_lift` | INFO | apply-fwd | Definition b5m_tailtrunc | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7318 | `NatLe_drop` | PB | apply-fwd | Definition b5m_tailtrunc | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7320 | `NatLe_lift` | INFO | apply-fwd | Definition b5m_tailtrunc | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7322 | `NatLe_drop` | PB | apply-fwd | Definition b5m_tailtrunc | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7346 | `NatLe_drop` | PB | apply-in | Lemma b5m_tailtrunc_ge | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7387 | `NatLe_lift` | INFO | term-syntax | Lemma b5m_tailtrunc_r | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 7405 | `NatLe_lift` | INFO | apply-fwd | Lemma b5m_plus_tailtrunc_unit | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7451 | `NatLe_drop` | PB | apply-in | Lemma b5m_arctan_wd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 7464 | `NatLe_lift` | PB | apply-fwd | Lemma b5m_arctan_wd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7466 | `NatLe_lift` | PB | apply-fwd | Lemma b5m_arctan_wd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 7957 | `NatLe_lift` | INFO | apply-fwd | Lemma b5p2_clamp01_cert_tail | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7958 | `NatLe_drop` | PB | apply-fwd | Lemma b5p2_clamp01_cert_tail | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 7975 | `NatLe_lift` | INFO | apply-fwd | Lemma b5p2_clamp01_cert_tail | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 7976 | `NatLe_drop` | PB | apply-fwd | Lemma b5p2_clamp01_cert_tail | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 8040 | `NatLe_drop` | PB | apply-in | Lemma b5p2_arctan_wd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8057 | `NatLe_lift` | PB | apply-fwd | Lemma b5p2_arctan_wd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 8059 | `NatLe_lift` | PB | apply-fwd | Lemma b5p2_arctan_wd | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 11462 | `NatLe_drop` | PB | term-syntax | Theorem sf_ewc_pos_eps | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 11467 | `NatLe_drop` | PB | term-syntax | Theorem sf_ewc_pos_eps | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 11599 | `NatLe_drop` | PB | term-syntax | Theorem sf_ewc_mono_fisher | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 11604 | `NatLe_drop` | PB | term-syntax | Theorem sf_ewc_mono_fisher | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 12977 | `NatLe_drop` | PB | term-syntax | Lemma sf_argmax_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 12980 | `NatLe_lift` | INFO | bare | Lemma sf_argmax_aux_dom | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 12990 | `NatLe_drop` | PB | term-syntax | Lemma sf_argmax_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 12992 | `NatLe_lift` | INFO | term-syntax | Lemma sf_argmax_aux_dom | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 13010 | `NatLe_drop` | PB | term-syntax | Lemma sf_argmax_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 13012 | `NatLe_lift` | INFO | term-syntax | Lemma sf_argmax_aux_dom | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 13042 | `NatLe_drop` | PB | term-syntax | Lemma sf_argmax_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 13043 | `NatLe_lift` | INFO | term-syntax | Lemma sf_argmax_aux_dom | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 13075 | `NatLe_drop` | PB | term-syntax | Theorem sf_argmax_dominates | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 13083 | `NatLe_lift` | INFO | bare | Theorem sf_argmax_dominates | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 13085 | `NatLe_lift` | INFO | apply-fwd | Theorem sf_argmax_dominates | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 14526 | `NatLe_lift` | INFO | apply-fwd | Lemma sf_natle2_tail | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 14527 | `NatLe_drop` | PB | apply-in | Lemma sf_natle2_tail | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |

### S13_NLiveAudit.v（15 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 819 | `NatLe_drop` | PB | apply-in | Theorem sf_sub_cx_descent | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 819 | `NatLe_drop` | PB | apply-in | Theorem sf_sub_cx_descent | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 853 | `NatLe_drop` | PB | apply-in | Theorem sf_decompose_descent | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 924 | `NatLe_drop` | PB | apply-in | Theorem sf_run_done_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 926 | `NatLe_drop` | PB | apply-in | Theorem sf_run_done_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 961 | `NatLe_drop` | PB | term-syntax | Theorem sf_search_counter_complete | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 966 | `NatLe_drop` | PB | term-syntax | Theorem sf_search_counter_complete | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1437 | `NatLe_drop` | PB | term-syntax | Lemma nat_pick_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1438 | `NatLe_drop` | PB | term-syntax | Lemma nat_pick_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1446 | `NatLe_drop` | PB | term-syntax | Lemma nat_pick_aux_dom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 3708 | `NatLe_lift` | INFO | apply-fwd | Lemma remove_length_le_aux | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 3710 | `NatLe_drop` | PB | apply-in | Lemma remove_length_le_aux | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3711 | `NatLe_lift` | INFO | apply-fwd | Lemma remove_length_le_aux | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 4192 | `NatLe_drop` | PB | apply-fwd | Lemma nonm_mass_le_bound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 4278 | `NatLe_drop` | PB | apply-fwd | Lemma hsum_nonm_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### S14_B5BatchBlock.v（146 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 178 | `NatLe_drop` | PB | apply-in | Lemma b5d1_b3rr_atan_deriv_lin | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 194 | `NatLe_lift` | INFO | term-syntax | Lemma b5d1_b3rr_atan_deriv_lin | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 203 | `NatLe_lift` | INFO | term-syntax | Lemma b5d1_b3rr_atan_deriv_lin | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 209 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d1_b3rr_atan_deriv_lin | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 235 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d1_b3rr_atan_deriv_lin | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 285 | `NatLe_lift` | INFO | term-syntax | Lemma b5d1_b3rr_atan_deriv_lin | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 316 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d1_b3rr_atan_deriv_lin | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 915 | `NatLe_drop` | PB | apply-in | Lemma b5dG_sin_atan_diff_closed_r_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 920 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 921 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 922 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 923 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 924 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 946 | `NatLe_lift` | INFO | term-syntax | Lemma b5dG_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1183 | `NatLe_drop` | PB | apply-in | Lemma b5dG_cos_atan_diff_closed_r_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1188 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1189 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1190 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1191 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1192 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dG_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1214 | `NatLe_lift` | INFO | term-syntax | Lemma b5dG_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1536 | `NatLe_lift` | PB | apply-fwd | Lemma b5dI_real_mult_positive_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1537 | `NatLe_drop` | PB | apply-fwd | Lemma b5dI_real_mult_positive_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1542 | `NatLe_lift` | PB | apply-fwd | Lemma b5dI_real_mult_positive_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 1543 | `NatLe_drop` | PB | apply-fwd | Lemma b5dI_real_mult_positive_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 1760 | `NatLe_drop` | PB | apply-in | Lemma b5dI_sin_atan_diff_closed_r_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1765 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1766 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1767 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1768 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1769 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1791 | `NatLe_lift` | INFO | term-syntax | Lemma b5dI_sin_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 2035 | `NatLe_drop` | PB | apply-in | Lemma b5dI_cos_atan_diff_closed_r_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2040 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2041 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2042 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2043 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2044 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2066 | `NatLe_lift` | INFO | term-syntax | Lemma b5dI_cos_atan_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 2234 | `NatLe_drop` | PB | apply-in | Lemma b5dI_E_diff_closed_r_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2239 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2240 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2241 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2242 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2243 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2244 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 2342 | `NatLe_lift` | INFO | term-syntax | Lemma b5dI_E_diff_closed_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 2489 | `NatLe_drop` | PB | apply-fwd | Lemma b5dJ_log_diff_dx_exp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 2496 | `NatLe_lift` | INFO | term-syntax | Lemma b5dJ_log_diff_dx_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 2788 | `NatLe_drop` | PB | apply-in | Lemma b5dJ_log_diff_dx_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 2810 | `NatLe_lift` | INFO | term-syntax | Lemma b5dJ_log_diff_dx_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 2816 | `NatLe_lift` | INFO | term-syntax | Lemma b5dJ_log_diff_dx_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3060 | `NatLe_drop` | PB | apply-in | Lemma b5d3_exp_arch4_C_all | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3128 | `NatLe_drop` | PB | apply-in | Lemma b5d3_exp_arch4_C7_all | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3190 | `NatLe_drop` | PB | apply-in | Lemma b5d3_exp_minus_one_linear_closed | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3217 | `NatLe_lift` | INFO | term-syntax | Lemma b5d3_exp_minus_one_linear_closed | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3236 | `NatLe_lift` | INFO | term-syntax | Lemma b5d3_exp_minus_one_linear_closed | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3299 | `NatLe_lift` | INFO | term-syntax | Lemma b5d3_exp_minus_one_linear_closed | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3317 | `NatLe_lift` | INFO | term-syntax | Lemma b5d3_exp_minus_one_linear_closed | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3388 | `NatLe_drop` | PB | apply-in | Lemma b5dK_real_mult_positive_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3389 | `NatLe_lift` | PB | apply-fwd | Lemma b5dK_real_mult_positive_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3390 | `NatLe_lift` | PB | apply-fwd | Lemma b5dK_real_mult_positive_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3512 | `NatLe_drop` | PB | apply-in | Lemma b5dK_real_abs_scaling_le_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3538 | `NatLe_lift` | PB | bare | Lemma b5dK_real_abs_scaling_le_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3556 | `NatLe_lift` | PB | term-syntax | Lemma b5dK_real_abs_scaling_le_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3563 | `NatLe_lift` | PB | term-syntax | Lemma b5dK_real_abs_scaling_le_exp | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 3714 | `NatLe_drop` | PB | apply-in | Lemma b5dK_exp_minus_one_linear_closed_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3741 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_exp_minus_one_linear_closed_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3760 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_exp_minus_one_linear_closed_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3823 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_exp_minus_one_linear_closed_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3841 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_exp_minus_one_linear_closed_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 3984 | `NatLe_drop` | PB | apply-in | Lemma b5dK_gdiff_pts_r_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 3985 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dK_gdiff_pts_r_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 4005 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_gdiff_pts_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4011 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_gdiff_pts_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4021 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_gdiff_pts_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4042 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_gdiff_pts_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 4061 | `NatLe_lift` | INFO | term-syntax | Lemma b5dK_gdiff_pts_r_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 5820 | `NatLe_drop` | PB | apply-in | Lemma b5d7_J_deriv_zero_exp | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 5832 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5833 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5834 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5835 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5836 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5837 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5840 | `NatLe_lift` | INFO | apply-fwd | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 5853 | `NatLe_lift` | INFO | term-syntax | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 6145 | `NatLe_lift` | INFO | term-syntax | Lemma b5d7_J_deriv_zero_exp | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 6673 | `NatLe_drop` | PB | apply-in | Lemma b5dE_S_ub_tail_q | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6675 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dE_S_ub_tail_q | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6677 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dE_S_ub_tail_q | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 6844 | `NatLe_drop` | PB | apply-in | Lemma b5dF_E_one_zero_of_rational | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 6871 | `NatLe_lift` | PB | term-syntax | Lemma b5dF_E_one_zero_of_rational | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 6878 | `NatLe_lift` | PB | term-syntax | Lemma b5dF_E_one_zero_of_rational | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7492 | `NatLe_lift` | PB | term-syntax | Lemma b5dL_telescope_premise | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7497 | `NatLe_lift` | PB | term-syntax | Lemma b5dL_telescope_premise | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7698 | `NatLe_lift` | PB | term-syntax | Lemma b5dL_J_grid_premise | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 7724 | `NatLe_lift` | PB | term-syntax | Lemma b5dL_J_grid_premise | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 8009 | `NatLe_drop` | PB | term-syntax | Lemma b5dL_E_rational_zero_premise | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 8180 | `NatLe_drop` | PB | apply-in | Lemma b5dP_S_diff_closed_r_M_exp_tail | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8185 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_S_diff_closed_r_M_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8186 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_S_diff_closed_r_M_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8187 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_S_diff_closed_r_M_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8188 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_S_diff_closed_r_M_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8189 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_S_diff_closed_r_M_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8190 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_S_diff_closed_r_M_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8656 | `NatLe_drop` | PB | apply-in | Lemma b5dP_J_deriv_zero_exp_tail | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 8668 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8669 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8670 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8671 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8672 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8673 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8676 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8677 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 8690 | `NatLe_lift` | INFO | term-syntax | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 8982 | `NatLe_lift` | INFO | term-syntax | Lemma b5dP_J_deriv_zero_exp_tail | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 9108 | `NatLe_drop` | PB | apply-in | Lemma b5dQ_min_lb | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 9109 | `NatLe_lift` | PB | apply-fwd | Lemma b5dQ_min_lb | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 9110 | `NatLe_lift` | PB | apply-fwd | Lemma b5dQ_min_lb | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 11046 | `NatLe_drop` | PB | apply-in | Lemma b5dQ_min_lb_3 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 11047 | `NatLe_lift` | PB | apply-fwd | Lemma b5dQ_min_lb_3 | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 11048 | `NatLe_lift` | PB | apply-fwd | Lemma b5dQ_min_lb_3 | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 11049 | `NatLe_lift` | PB | apply-fwd | Lemma b5dQ_min_lb_3 | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 13127 | `NatLe_drop` | PB | apply-in | Lemma b5dQ_p4g_J_tail_lb_var | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 13139 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13140 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13141 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13142 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13143 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13144 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13147 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13148 | `NatLe_lift` | INFO | apply-fwd | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 13161 | `NatLe_lift` | INFO | term-syntax | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 13455 | `NatLe_lift` | INFO | term-syntax | Lemma b5dQ_p4g_J_tail_lb_var | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 13639 | `NatLe_lift` | INFO | bare | Lemma b5dQ_Hstep | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 13756 | `NatLe_lift` | INFO | term-syntax | Lemma b5dQ_Hmod | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 13772 | `NatLe_drop` | PB | term-syntax | Lemma b5dQ_Hmod | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 13802 | `NatLe_lift` | INFO | bare | Lemma b5dQ_Hmod | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 14418 | `NatLe_lift` | PB | term-syntax | Lemma b5dS_E_zero_on_unit | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 14424 | `NatLe_lift` | PB | term-syntax | Lemma b5dS_E_zero_on_unit | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 14436 | `NatLe_drop` | PB | apply-in | Lemma b5dS_E_zero_on_unit | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 14469 | `NatLe_lift` | PB | apply-fwd | Lemma b5dS_E_zero_on_unit | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 14473 | `NatLe_lift` | PB | apply-fwd | Lemma b5dS_E_zero_on_unit | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 14474 | `NatLe_lift` | PB | apply-fwd | Lemma b5dS_E_zero_on_unit | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 14491 | `NatLe_lift` | PB | term-syntax | Lemma b5dS_E_zero_on_unit | 否（证明位） | 调用存活1 | W-L1(改名桥) |

### SumInvFactEscape.v（5 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 442 | `NatLe_drop` | SLOT | ltac-embed | — | 否（擦除槽） | 擦除(mli `__`) | W-D0(提取槽重写) |
| 462 | `NatLe_lift` | INFO | apply-fwd | — | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 462 | `NatLe_drop` | SLOT | apply-fwd | — | 否（擦除槽） | 擦除(mli `__`) | W-D0(提取槽重写) |
| 498 | `NatLe_lift` | INFO | apply-fwd | Theorem sif_escape | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 521 | `NatLe_lift` | INFO | apply-fwd | Theorem sif_escape | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### ToyR_SupplyAssembly.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 22 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 70 | `NatLe_drop` | PB | term-syntax | Theorem sa_A_nonzeroT | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 76 | `NatLe_drop` | PB | ltac-embed | Theorem sa_A_nonzeroT | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 199 | `NatLe_drop` | PB | term-syntax | Theorem sa_theta_leg_scaffold | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 214 | `NatLe_lift` | INFO | bare | Theorem sa_theta_leg_scaffold | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 232 | `NatLe_drop` | PB | term-syntax | Theorem sa_clo_in_theta_window | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### TrueNumerator.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 177 | `NatLe_drop` | PB | term-syntax | Lemma tn_Pn_list_nth | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 186 | `NatLe_drop` | PB | term-syntax | Lemma tn_Pn_list_nth | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 190 | `NatLe_lift` | INFO | term-syntax | Lemma tn_Pn_list_nth | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### UpAblD1S14_UpReqCauchy.v（9 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 186 | `NatLe_lift` | INFO | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 189 | `NatLe_drop` | PB | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 191 | `NatLe_lift` | INFO | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 194 | `NatLe_drop` | PB | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 195 | `NatLe_drop` | PB | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 199 | `NatLe_drop` | PB | bare | Theorem uabd1s14_cau_lim_metric_supply | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 207 | `NatLe_drop` | PB | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 209 | `NatLe_lift` | INFO | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 212 | `NatLe_drop` | PB | apply-fwd | Theorem uabd1s14_cau_lim_metric_supply | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpAblHalfPowFeed.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 270 | `NatLe_lift` | CMD | cmd-mention | — | 命令面 | — | W-Z(零迁移) |

### UpAblLogWall.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 269 | `NatLe_lift` | PB | apply-fwd | Theorem lgw_lpo_of_min_sel | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpBudgetReal.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 21 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 665 | `NatLe_drop` | PB | term-syntax | Lemma real_pow_anti_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### UpCS.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 422 | `NatLe_lift` | PB | term-syntax | Theorem real_cauchy_schwarz_reversed_false | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 436 | `NatLe_lift` | PB | term-syntax | Theorem real_cauchy_schwarz_reversed_false | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpConstitution.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 338 | `NatLe_lift` | INFO | apply-fwd | Theorem uc_growth_breaks | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 626 | `NatLe_lift` | INFO | apply-fwd | Theorem valid_claim_yields_breakthrough | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 895 | `NatLe_drop` | PB | term-syntax | Theorem claim_chain | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 897 | `NatLe_lift` | INFO | apply-fwd | Theorem claim_chain | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### UpReqBanachCauchyD.v（48 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 14 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 107 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_bsum_pad_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 116 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_bsum_pad_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 149 | `NatLe_lift` | PB | apply-fwd | Lemma bxcd_bsum_pad_split | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 331 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_binom_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 334 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_binom_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 350 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_binom_pos | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 352 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_binom_pos | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 361 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_binom_fact2 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 363 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_binom_fact2 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 388 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_binom_fact2 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 392 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_binom_fact2 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 461 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_binom_fact | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 553 | `NatLe_lift` | PB | apply-fwd | Lemma bxcd_dline_binom_term | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 626 | `NatLe_lift` | PB | apply-fwd | Lemma bxcd_prod_split | 否（证明位） | 调用存活1 | W-L1(改名桥) |
| 852 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_qtail_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 854 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_qtail_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 859 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_qtail_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 879 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_qtail_add | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 888 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_qtail_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 889 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_qtail_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 983 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_row_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1047 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_Q2_bound | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1051 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1103 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1103 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1108 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1109 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1147 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1147 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1193 | `NatLe_drop` | PB | term-syntax | Lemma bxcd_Q2_bound_M | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1197 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1212 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1212 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1239 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1240 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1244 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1244 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1262 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1262 | `NatLe_lift` | INFO | apply-fwd | Lemma bxcd_Q2_bound_M | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1417 | `NatLe_lift` | INFO | apply-fwd | Theorem bxcd_prod_near_one | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1418 | `NatLe_lift` | INFO | apply-fwd | Theorem bxcd_prod_near_one | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1432 | `NatLe_lift` | INFO | apply-fwd | Theorem bxcd_prod_near_one | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1433 | `NatLe_lift` | INFO | apply-fwd | Theorem bxcd_prod_near_one | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1510 | `NatLe_drop` | PB | apply-in | Theorem bxcd_prod_near_one | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 1525 | `NatLe_lift` | INFO | bare | Theorem bxcd_prod_near_one | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |
| 1528 | `NatLe_drop` | PB | bare | Theorem bxcd_prod_near_one | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1540 | `NatLe_lift` | INFO | bare | Theorem bxcd_prod_near_one | **是（信息位）** | 调用存活1 | W-L3(原生face重铸) |

### UpReqBanachExp.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 431 | `NatLe_lift` | PB | apply-fwd | Lemma exp_series_cauchy | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 438 | `NatLe_drop` | PB | apply-in | Lemma exp_series_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 438 | `NatLe_drop` | PB | apply-in | Lemma exp_series_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 462 | `NatLe_drop` | PB | bare | Lemma exp_series_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 467 | `NatLe_drop` | PB | bare | Lemma exp_series_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 481 | `NatLe_drop` | PB | bare | Lemma exp_series_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 486 | `NatLe_drop` | PB | bare | Lemma exp_series_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### UpReqBanachExpAdd.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 279 | `NatLe_drop` | PB | apply-in | Lemma bxadd_bmult_lim | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 282 | `NatLe_lift` | PB | term-syntax | Lemma bxadd_bmult_lim | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 283 | `NatLe_lift` | PB | term-syntax | Lemma bxadd_bmult_lim | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpReqBanachExpBasic.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 228 | `NatLe_lift` | INFO | term-syntax | Lemma bxb_expdef_exp_zero_close | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### UpReqBanachExpDef.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 165 | `NatLe_lift` | INFO | term-syntax | Lemma bxdef_exp_zero_close | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### UpReqBanachInst.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 123 | `NatLe_drop` | PB | apply-fwd | Lemma bxin_scalar_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 125 | `NatLe_drop` | PB | apply-fwd | Lemma bxin_scalar_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqBanachLimUniq.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 201 | `NatLe_lift` | INFO | term-syntax | Lemma bxuq_lim_diff_small | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 204 | `NatLe_lift` | INFO | term-syntax | Lemma bxuq_lim_diff_small | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### UpReqCStarDef.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 470 | `NatLe_drop` | PB | term-syntax | Lemma cst_pow14_anti | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 477 | `NatLe_drop` | PB | term-syntax | Lemma cst_pow14_anti | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 493 | `NatLe_lift` | INFO | apply-fwd | Lemma cst_pow14_anti | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 501 | `NatLe_drop` | PB | term-syntax | Lemma cst_pow12_anti | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 508 | `NatLe_drop` | PB | term-syntax | Lemma cst_pow12_anti | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 521 | `NatLe_lift` | INFO | apply-fwd | Lemma cst_pow12_anti | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### UpReqCauchyLogBound.v（29 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 121 | `NatLe_drop` | PB | apply-fwd | Lemma cl_qle_bool_of_qle | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 203 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 203 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 208 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 211 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 211 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 213 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 213 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 219 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 222 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 222 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 243 | `NatLe_lift` | INFO | bare | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L3(原生face重铸) |
| 248 | `NatLe_lift` | INFO | bare | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L3(原生face重铸) |
| 248 | `NatLe_lift` | INFO | bare | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L3(原生face重铸) |
| 256 | `NatLe_drop` | PB | apply-in | Theorem cl_bsearch_dual | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 266 | `NatLe_lift` | INFO | bare | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L3(原生face重铸) |
| 280 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 280 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 293 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 296 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 296 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 309 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_dual | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 321 | `NatLe_lift` | INFO | apply-fwd | Lemma cl_fuel_ge_pos | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 336 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_log_return_bound | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 361 | `NatLe_lift` | INFO | bare | Lemma cl_fuel_sub | **是（信息位）** | 调用存活9 | W-L3(原生face重铸) |
| 364 | `NatLe_lift` | INFO | apply-fwd | Lemma cl_fuel_sub | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 391 | `NatLe_lift` | INFO | bare | Theorem cl_bsearch_log_bound | **是（信息位）** | 调用存活9 | W-L3(原生face重铸) |
| 394 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_log_bound | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 396 | `NatLe_lift` | INFO | apply-fwd | Theorem cl_bsearch_log_bound | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |

### UpReqConstEnvelope.v（9 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 201 | `NatLe_drop` | PB | apply-fwd | Theorem c3e_env_mother | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 203 | `NatLe_lift` | INFO | apply-fwd | Theorem c3e_env_mother | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 205 | `NatLe_drop` | PB | apply-fwd | Theorem c3e_env_mother | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 234 | `NatLe_drop` | PB | apply-fwd | Theorem c3e_env_mother | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 236 | `NatLe_lift` | INFO | apply-fwd | Theorem c3e_env_mother | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 238 | `NatLe_drop` | PB | apply-fwd | Theorem c3e_env_mother | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 468 | `NatLe_drop` | PB | apply-fwd | Definition c3e_ln2_real | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 473 | `NatLe_drop` | PB | apply-fwd | Definition c3e_ln2_real | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 543 | `NatLe_drop` | PB | apply-fwd | Theorem c3e_env_e | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqG05WallClass.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 113 | `NatLe_lift` | PB | apply-fwd | Theorem g05w_rlpo_to_b_lift | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 114 | `NatLe_drop` | PB | apply-fwd | Theorem g05w_rlpo_to_b_lift | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 116 | `NatLe_lift` | PB | apply-fwd | Theorem g05w_rlpo_to_b_lift | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 117 | `NatLe_drop` | PB | apply-fwd | Theorem g05w_rlpo_to_b_lift | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqGibbsE2.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 700 | `NatLe_lift` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 701 | `NatLe_drop` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 703 | `NatLe_lift` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 704 | `NatLe_drop` | PB | apply-fwd | Lemma gibbe2_le_b_antisym | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqGibbsWallEquiv.v（5 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 104 | `NatLe_lift` | PB | apply-fwd | Lemma gwe_lt_congr_r | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 106 | `NatLe_drop` | PB | apply-fwd | Lemma gwe_lt_congr_r | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 108 | `NatLe_lift` | PB | apply-fwd | Lemma gwe_lt_congr_r | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 110 | `NatLe_drop` | PB | apply-fwd | Lemma gwe_lt_congr_r | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 224 | `NatLe_lift` | PB | apply-fwd | Lemma gwe_diag_no_gap | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpReqIrrationalCriterion.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 258 | `NatLe_drop` | PB | apply-in | Lemma lic_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 258 | `NatLe_drop` | PB | apply-in | Lemma lic_seq_cauchy | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 315 | `NatLe_drop` | PB | apply-in | Theorem lic_irrational_criterion | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |

### UpReqKLStrict.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 118 | `NatLe_drop` | PB | term-syntax | Lemma klst_exp_tangent_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 125 | `NatLe_lift` | PB | apply-fwd | Lemma klst_exp_tangent_pos | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpReqNormConv.v（8 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 797 | `NatLe_lift` | INFO | apply-fwd | Lemma ncv_conv_rect_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 799 | `NatLe_drop` | PB | apply-fwd | Lemma ncv_conv_rect_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 801 | `NatLe_lift` | INFO | apply-fwd | Lemma ncv_conv_rect_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 803 | `NatLe_drop` | PB | apply-fwd | Lemma ncv_conv_rect_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 805 | `NatLe_lift` | INFO | apply-fwd | Lemma ncv_conv_rect_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 807 | `NatLe_drop` | PB | apply-fwd | Lemma ncv_conv_rect_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 809 | `NatLe_lift` | INFO | apply-fwd | Lemma ncv_conv_rect_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 811 | `NatLe_drop` | PB | apply-fwd | Lemma ncv_conv_rect_cauchy | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqPadeLower.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 304 | `NatLe_drop` | PB | apply-fwd | Theorem cpl_lower_even | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqPadeTailPos.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 167 | `NatLe_lift` | INFO | apply-fwd | Lemma pbp_den_index_ge1 | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 1424 | `NatLe_drop` | PB | apply-fwd | Theorem qtr_exp_gt_partial | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### UpReqQExpTail.v（5 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 47 | `NatLe_lift` | INFO | apply-fwd | Lemma qtail_two_pow_ge | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 55 | `NatLe_lift` | INFO | apply-fwd | Lemma qtail_fact_ge_pow | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 56 | `NatLe_lift` | INFO | apply-fwd | Lemma qtail_fact_ge_pow | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 67 | `NatLe_drop` | PB | term-syntax | Lemma qtail_fact_ge_pow | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 187 | `NatLe_drop` | PB | term-syntax | Lemma qtail_half_pow_le_invT | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### UpReqRealLtShiftBridge.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 64 | `NatLe_lift` | PB | term-syntax | Lemma rlsb_zero_ne_one | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpReqResidWallEquiv.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 190 | `NatLe_lift` | PB | apply-fwd | Lemma rwl_le_eq_transfer_r | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 191 | `NatLe_drop` | PB | apply-fwd | Lemma rwl_le_eq_transfer_r | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 193 | `NatLe_lift` | PB | apply-fwd | Lemma rwl_le_eq_transfer_r | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 194 | `NatLe_drop` | PB | apply-fwd | Lemma rwl_le_eq_transfer_r | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 293 | `NatLe_lift` | PB | term-syntax | Theorem rwl_cmp_to_snw_wall | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 370 | `NatLe_lift` | PB | apply-fwd | Theorem rwl_s14_tail_plus_head | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### UpReqScTrigEps.v（5 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 198 | `NatLe_drop` | PB | apply-fwd | Lemma sce_half_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 310 | `NatLe_drop` | PB | apply-fwd | Lemma sce_cos_partial_tail_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 326 | `NatLe_lift` | INFO | apply-fwd | Lemma sce_cos_partial_tail_le | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 341 | `NatLe_drop` | PB | apply-fwd | Lemma sce_sin_partial_tail_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 357 | `NatLe_lift` | INFO | apply-fwd | Lemma sce_sin_partial_tail_le | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### UpTempWindow.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 604 | `NatLe_lift` | PB | apply-fwd | Lemma tw_abs_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 605 | `NatLe_drop` | PB | apply-fwd | Lemma tw_abs_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 607 | `NatLe_lift` | PB | apply-fwd | Lemma tw_abs_le | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 608 | `NatLe_drop` | PB | apply-fwd | Lemma tw_abs_le | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### _natle_adjud_probe.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 8 | `NatLe_drop` | CMD | cmd-mention | — | 命令面 | — | W-Z(零迁移) |
| 8 | `NatLe_lift` | CMD | cmd-mention | — | 命令面 | — | W-Z(零迁移) |

### abl_Pr_core_01.v（20 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 16 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 16 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 33 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 33 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 148 | `NatLe_lift` | PB | apply-fwd | Theorem pr_prime_bool_true | 否（证明位） | 调用存活4 | W-L1(改名桥) |
| 150 | `NatLe_drop` | PB | apply-fwd | Theorem pr_prime_bool_true | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 151 | `NatLe_drop` | PB | term-syntax | Theorem pr_prime_bool_true | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 165 | `NatLe_drop` | PB | apply-fwd | Theorem pr_prime_bool_false | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 175 | `NatLe_lift` | INFO | term-syntax | Theorem pr_prime_bool_false | **是（信息位）** | 调用存活4 | W-L3(原生face重铸) |
| 175 | `NatLe_lift` | INFO | term-syntax | Theorem pr_prime_bool_false | **是（信息位）** | 调用存活4 | W-L3(原生face重铸) |
| 219 | `NatLe_lift` | INFO | apply-fwd | Lemma pr_min_factor_sound | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 220 | `NatLe_lift` | INFO | apply-fwd | Lemma pr_min_factor_sound | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 221 | `NatLe_drop` | PB | apply-in | Lemma pr_min_factor_sound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 221 | `NatLe_drop` | PB | apply-in | Lemma pr_min_factor_sound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 230 | `NatLe_lift` | INFO | apply-fwd | Lemma pr_min_factor_sound | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 231 | `NatLe_lift` | INFO | apply-fwd | Lemma pr_min_factor_sound | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 232 | `NatLe_drop` | PB | apply-in | Lemma pr_min_factor_sound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 232 | `NatLe_drop` | PB | apply-in | Lemma pr_min_factor_sound | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 258 | `NatLe_drop` | PB | term-syntax | Theorem pr_min_factor_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 296 | `NatLe_drop` | PB | term-syntax | Theorem pr_factor_exists | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_Pr_enum_02.v（55 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 15 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 16 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 18 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 18 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 34 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 34 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 175 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_count_mono | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 177 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_count_mono | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 181 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_count_mono | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 181 | `NatLe_drop` | PB | apply-fwd | Lemma pen_count_mono | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 195 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_count_upto_largest | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 206 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_count_upto_largest | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 206 | `NatLe_drop` | PB | apply-fwd | Lemma pen_count_upto_largest | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 222 | `NatLe_drop` | PB | term-syntax | Lemma pen_count_lt_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 223 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_count_lt_prime | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 237 | `NatLe_drop` | PB | term-syntax | Lemma pen_count_inj | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 242 | `NatLe_drop` | PB | term-syntax | Lemma pen_count_inj | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 280 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_next_prime_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 281 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_next_prime_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 301 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_next_prime_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 301 | `NatLe_drop` | PB | apply-fwd | Lemma pen_next_prime_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 302 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_next_prime_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 302 | `NatLe_drop` | PB | apply-fwd | Lemma pen_next_prime_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 306 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_next_prime_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 306 | `NatLe_drop` | PB | apply-fwd | Lemma pen_next_prime_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 317 | `NatLe_drop` | PB | term-syntax | Lemma pen_count_next_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 318 | `NatLe_drop` | PB | term-syntax | Lemma pen_count_next_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 329 | `NatLe_drop` | PB | term-syntax | Lemma pen_count_next_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 330 | `NatLe_lift` | INFO | bare | Lemma pen_count_next_prime | **是（信息位）** | 调用存活12 | W-L3(原生face重铸) |
| 387 | `NatLe_drop` | PB | term-syntax | Theorem pen_nth_prime_spec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 417 | `NatLe_drop` | PB | term-syntax | Theorem pen_nth_prime_spec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 419 | `NatLe_drop` | PB | term-syntax | Theorem pen_nth_prime_spec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 490 | `NatLe_drop` | PB | term-syntax | Lemma pen_primes_upto_S | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 491 | `NatLe_drop` | PB | term-syntax | Lemma pen_primes_upto_S | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 498 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_primes_upto_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 507 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_primes_upto_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 507 | `NatLe_drop` | PB | apply-fwd | Lemma pen_primes_upto_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 512 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_primes_upto_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 512 | `NatLe_drop` | PB | apply-fwd | Lemma pen_primes_upto_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 516 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_primes_upto_S | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 516 | `NatLe_drop` | PB | apply-fwd | Lemma pen_primes_upto_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 517 | `NatLe_drop` | PB | apply-fwd | Lemma pen_primes_upto_S | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 532 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_fold_mul_pos | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 533 | `NatLe_lift` | INFO | apply-fwd | Lemma pen_fold_mul_pos | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 538 | `NatLe_drop` | PB | term-syntax | Lemma pen_fold_mul_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 553 | `NatLe_drop` | PB | term-syntax | Lemma pen_primorial_pos | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 575 | `NatLe_lift` | PB | apply-fwd | Lemma pen_primorial_divide | 否（证明位） | 调用存活12 | W-L1(改名桥) |
| 602 | `NatLe_drop` | PB | term-syntax | Theorem pen_euclid_new_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 607 | `NatLe_lift` | INFO | apply-fwd | Theorem pen_euclid_new_prime | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 609 | `NatLe_drop` | PB | apply-fwd | Theorem pen_euclid_new_prime | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 637 | `NatLe_drop` | PB | term-syntax | Theorem pen_coprime_of_neq | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 638 | `NatLe_drop` | PB | term-syntax | Theorem pen_coprime_of_neq | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 659 | `NatLe_lift` | INFO | apply-fwd | Theorem pen_coprime_of_neq | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 659 | `NatLe_lift` | INFO | apply-fwd | Theorem pen_coprime_of_neq | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |
| 681 | `NatLe_lift` | INFO | apply-fwd | Theorem pen_coprime_of_neq | **是（信息位）** | 调用存活12 | W-L2(改名桥→原生) |

### abl_Pr_euclid_03.v（13 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 15 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 16 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 19 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 19 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 33 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 33 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 39 | `NatLe_lift` | INFO | apply-fwd | Lemma peu_fact_pos | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 42 | `NatLe_drop` | PB | apply-fwd | Lemma peu_fact_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 42 | `NatLe_lift` | INFO | apply-fwd | Lemma peu_fact_pos | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 106 | `NatLe_drop` | SLOT | bare | — | 否（擦除槽） | 擦除(mli `__`) | W-D0(提取槽重写) |
| 113 | `NatLe_drop` | PB | bare | Lemma peu_next_pair | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 127 | `NatLe_lift` | PB | apply-fwd | Theorem peu_next_prime | 否（证明位） | 调用存活3 | W-L1(改名桥) |
| 131 | `NatLe_drop` | PB | apply-fwd | Theorem peu_next_prime | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### abl_Pr_lcm_eq.v（19 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 19 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 20 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 38 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 38 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 54 | `NatLe_lift` | INFO | apply-fwd | Lemma plq_lcm_pos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 91 | `NatLe_drop` | PB | term-syntax | Lemma plq_gcd_1_of_nondvd | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 109 | `NatLe_lift` | INFO | apply-fwd | Lemma plq_gcd_1_of_nondvd | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 109 | `NatLe_lift` | INFO | apply-fwd | Lemma plq_gcd_1_of_nondvd | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 163 | `NatLe_drop` | PB | term-syntax | Lemma plq_pen_nodup | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 221 | `NatLe_lift` | INFO | apply-fwd | Lemma plq_v_mono | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 329 | `NatLe_drop` | PB | term-syntax | Lemma plq_num_dvd_powprod | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 374 | `NatLe_lift` | PB | apply-fwd | Lemma plq_num_dvd_powprod | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 387 | `NatLe_drop` | PB | apply-fwd | Lemma plq_num_dvd_powprod | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 388 | `NatLe_drop` | PB | apply-fwd | Lemma plq_num_dvd_powprod | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 397 | `NatLe_lift` | PB | apply-fwd | Lemma plq_num_dvd_powprod | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 398 | `NatLe_lift` | PB | apply-fwd | Lemma plq_num_dvd_powprod | 否（证明位） | 调用存活2 | W-L1(改名桥) |
| 438 | `NatLe_drop` | PB | apply-fwd | Theorem pr_lcm_eq_decomp | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 442 | `NatLe_drop` | PB | term-syntax | Theorem pr_lcm_eq_decomp | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 445 | `NatLe_drop` | PB | term-syntax | Theorem pr_lcm_eq_decomp | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_Pr_lcmdecomp_04.v（24 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 15 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 15 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 21 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 21 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 33 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 33 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 190 | `NatLe_drop` | PB | term-syntax | Lemma plm_prime_gcd_1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 191 | `NatLe_drop` | PB | term-syntax | Lemma plm_prime_gcd_1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 211 | `NatLe_lift` | INFO | apply-fwd | Lemma plm_prime_gcd_1 | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 223 | `NatLe_lift` | INFO | apply-fwd | Lemma plm_prime_gcd_1 | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 223 | `NatLe_lift` | INFO | apply-fwd | Lemma plm_prime_gcd_1 | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 384 | `NatLe_drop` | PB | term-syntax | Lemma plm_prime_dvd_mul | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 399 | `NatLe_lift` | PB | apply-fwd | Lemma plm_prime_dvd_mul | 否（证明位） | 调用存活3 | W-L1(改名桥) |
| 399 | `NatLe_lift` | PB | apply-fwd | Lemma plm_prime_dvd_mul | 否（证明位） | 调用存活3 | W-L1(改名桥) |
| 454 | `NatLe_drop` | PB | term-syntax | Lemma plm_hit_find_spec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 465 | `NatLe_lift` | INFO | apply-fwd | Lemma plm_hit_find_spec | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 467 | `NatLe_lift` | INFO | apply-fwd | Lemma plm_hit_find_spec | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 478 | `NatLe_lift` | INFO | apply-fwd | Lemma plm_hit_find_spec | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 478 | `NatLe_drop` | PB | apply-fwd | Lemma plm_hit_find_spec | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 519 | `NatLe_drop` | PB | term-syntax | Theorem plm_lcm_pow_prod_dvd | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 564 | `NatLe_drop` | PB | term-syntax | Theorem plm_peu_next_outside_lcm | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 574 | `NatLe_drop` | PB | term-syntax | Theorem plm_peu_next_outside_lcm | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 578 | `NatLe_drop` | PB | apply-fwd | Theorem plm_peu_next_outside_lcm | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 579 | `NatLe_drop` | PB | apply-fwd | Theorem plm_peu_next_outside_lcm | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### abl_Pr_recip_sum.v（46 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 15 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 15 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 17 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 17 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 23 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 23 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 34 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 34 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 53 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_S | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 77 | `NatLe_drop` | PB | apply-in | Lemma prs_pow_div | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 82 | `NatLe_drop` | PB | apply-in | Lemma prs_pow_div | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 102 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_mul_div_le | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 103 | `NatLe_drop` | PB | apply-in | Lemma prs_mul_div_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 117 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_div_lower | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 118 | `NatLe_drop` | PB | apply-in | Lemma prs_div_lower | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 118 | `NatLe_drop` | PB | apply-in | Lemma prs_div_lower | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 145 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_block | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 149 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_block | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 151 | `NatLe_drop` | PB | apply-fwd | Lemma prs_hsum_block | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 152 | `NatLe_lift` | INFO | apply-in | Lemma prs_hsum_block | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 152 | `NatLe_drop` | PB | apply-in | Lemma prs_hsum_block | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 154 | `NatLe_drop` | PB | apply-fwd | Lemma prs_hsum_block | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 155 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_block | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 155 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_block | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 165 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_scale2 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 170 | `NatLe_drop` | PB | apply-fwd | Lemma prs_hsum_scale2 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 171 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_scale2 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 172 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_scale2 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 174 | `NatLe_drop` | PB | apply-fwd | Lemma prs_hsum_scale2 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 174 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_scale2 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 191 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_harm_dyad | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 202 | `NatLe_drop` | PB | apply-fwd | Lemma prs_harm_dyad | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 205 | `NatLe_drop` | PB | apply-fwd | Lemma prs_harm_dyad | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 208 | `NatLe_drop` | PB | apply-fwd | Lemma prs_harm_dyad | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 217 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_harm_dyad | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 228 | `NatLe_drop` | PB | apply-fwd | Lemma prs_harm_dyad | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 230 | `NatLe_lift` | INFO | apply-in | Lemma prs_harm_dyad | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 230 | `NatLe_drop` | PB | apply-in | Lemma prs_harm_dyad | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 231 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_harm_dyad | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 233 | `NatLe_drop` | PB | apply-fwd | Lemma prs_harm_dyad | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 269 | `NatLe_lift` | INFO | apply-fwd | Theorem prs_harm_diverge | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 270 | `NatLe_drop` | PB | apply-in | Theorem prs_harm_diverge | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 298 | `NatLe_drop` | PB | apply-in | Lemma prs_geo_S | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 340 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_4_16 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 343 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_4_16 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |
| 346 | `NatLe_lift` | INFO | apply-fwd | Lemma prs_hsum_4_16 | **是（信息位）** | 调用存活6 | W-L2(改名桥→原生) |

### abl_W9_Afamily_08.v（41 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 14 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 44 | `NatLe_lift` | INFO | term-syntax | Lemma abl08_idx1 | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 47 | `NatLe_lift` | INFO | term-syntax | Lemma abl08_idx1 | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 50 | `NatLe_lift` | INFO | term-syntax | Lemma abl08_idx1 | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 63 | `NatLe_drop` | PB | bare | Lemma abl08_idx1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 72 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_eo_raw_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 83 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_dpair_form_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 83 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_dpair_form_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 93 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_deg_van_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 104 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_tri_d_eval_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 116 | `NatLe_drop` | PB | bare | Theorem abl08_sc_cs_d_tail_diff_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 116 | `NatLe_drop` | PB | bare | Theorem abl08_sc_cs_d_tail_diff_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 129 | `NatLe_drop` | PB | bare | Theorem abl08_sc_cs_sq_err_tail_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 129 | `NatLe_drop` | PB | bare | Theorem abl08_sc_cs_sq_err_tail_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 140 | `NatLe_drop` | PB | bare | Theorem abl08_sc_A_succ_bound_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 154 | `NatLe_drop` | PB | bare | Theorem abl08_sc_A_ge_q_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 163 | `NatLe_drop` | PB | bare | Theorem abl08_sc_A_ge_p_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 174 | `NatLe_drop` | PB | bare | Theorem abl08_sc_t_dec_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 184 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_sin_err_abs_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 200 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_cos_diag_swap_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 213 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_cos_err_decomp_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 226 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_cos_anti_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 239 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_cos_err_abs_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 252 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_cos_err_tail_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 265 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_q_pow_zero_ge1_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 273 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_sin_alt_hlt_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 281 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cos_alt_hlt_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 290 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_sin_alt_decr_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 300 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cos_alt_decr_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 309 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_sin_odd_ge3_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 318 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cos_odd_ge3_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 329 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_ddeg_sum_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 341 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cs_deg_van_x_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 349 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_sin_alt_hlt2_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 355 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_M_ge8_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 361 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_q_pow_pred_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 367 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_neg_sign_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 377 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_d_tail_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 388 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_sin_err_tail_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 399 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_add_cos_ss_swap_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 410 | `NatLe_drop` | PB | term-syntax | Theorem abl08_sc_cos_add_W_le_i1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_W9_pi_widen_13.v（11 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 264 | `NatLe_drop` | PB | apply-fwd | Lemma abl13_a_decr | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 376 | `NatLe_drop` | PB | apply-in | Lemma abl13_cp_even_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 380 | `NatLe_drop` | PB | apply-in | Lemma abl13_cp_even_le | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 419 | `NatLe_lift` | INFO | apply-fwd | Lemma abl13_cp_even_le | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 470 | `NatLe_lift` | INFO | apply-fwd | Lemma abl13_cp_even_le | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 483 | `NatLe_drop` | PB | apply-fwd | Lemma abl13_cp_le_s4 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 485 | `NatLe_lift` | INFO | apply-fwd | Lemma abl13_cp_le_s4 | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 487 | `NatLe_lift` | INFO | apply-fwd | Lemma abl13_cp_le_s4 | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 750 | `NatLe_drop` | PB | term-syntax | Lemma abl13_cos_pi_half_unique_widened2 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 752 | `NatLe_drop` | PB | term-syntax | Lemma abl13_cos_pi_half_unique_widened2 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 881 | `NatLe_lift` | PB | bare | Lemma abl13_cos_pi_half_unique_widened2 | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### abl_arctan_diff_19.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 107 | `NatLe_drop` | PB | apply-in | Lemma abl9_atan_incr_step_cond | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 125 | `NatLe_lift` | PB | term-syntax | Lemma abl9_atan_incr_step_cond | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 135 | `NatLe_lift` | PB | term-syntax | Lemma abl9_atan_incr_step_cond | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 144 | `NatLe_lift` | PB | apply-fwd | Lemma abl9_atan_incr_step_cond | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 176 | `NatLe_lift` | PB | apply-fwd | Lemma abl9_atan_incr_step_cond | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 230 | `NatLe_lift` | PB | term-syntax | Lemma abl9_atan_incr_step_cond | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 261 | `NatLe_lift` | PB | apply-fwd | Lemma abl9_atan_incr_step_cond | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### abl_audit_base_v4.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 26 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 222 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 223 | `NatLe_lift` | INFO | term-syntax | Theorem abd_iterate_converges_via_twice | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 254 | `NatLe_lift` | INFO | bare | Theorem abd_iterate_converges_via_twice | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |

### abl_audit_base_v5.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 106 | `NatLe_drop` | PB | term-syntax | Theorem abe_consensus_iter_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_audit_base_v7.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 154 | `NatLe_drop` | PB | term-syntax | Theorem abg_gnprf_replay_2624 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_cw220_step_calc.v（62 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 25 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 57 | `NatLe_drop` | PB | term-syntax | Lemma cw2_ceil_div_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 62 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_ceil_div_le | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 110 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_pow_iter_exact_ge | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 111 | `NatLe_drop` | PB | apply-fwd | Lemma cw2_pow_iter_exact_ge | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 112 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_pow_iter_exact_ge | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 118 | `NatLe_drop` | PB | term-syntax | Lemma cw2_pow_iter_exact_ge | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 139 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 142 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_k_enum_correct | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 145 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 147 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 157 | `NatLe_lift` | INFO | term-syntax | Theorem cw2_k_enum_correct | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 176 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 179 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 182 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 186 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_k_enum_minimal | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 190 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_k_enum_minimal | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 196 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 198 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 204 | `NatLe_lift` | INFO | term-syntax | Theorem cw2_k_enum_minimal | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 240 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_logface | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 241 | `NatLe_drop` | PB | term-syntax | Theorem cw2_k_enum_logface | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 242 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_k_enum_logface | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 261 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_decay | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 262 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_decay | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 274 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_iter_lt_decay | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 284 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_half | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 285 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_half | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 286 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_half | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 288 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_iter_lt_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 289 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_iter_lt_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 304 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_q | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 305 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_q | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 306 | `NatLe_drop` | PB | term-syntax | Lemma cw2_iter_lt_q | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 308 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_iter_lt_q | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 309 | `NatLe_lift` | INFO | apply-fwd | Lemma cw2_iter_lt_q | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 333 | `NatLe_drop` | PB | term-syntax | Theorem cw2_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 337 | `NatLe_lift` | INFO | term-syntax | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 338 | `NatLe_drop` | PB | term-syntax | Theorem cw2_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 341 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 342 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 346 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 347 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 349 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 351 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 352 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 354 | `NatLe_lift` | INFO | term-syntax | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 357 | `NatLe_drop` | PB | term-syntax | Theorem cw2_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 358 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 375 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 376 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_fuel_sufficient_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 377 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_fuel_sufficient_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 393 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_fuel_sufficient_qbound | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 394 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_fuel_sufficient_qbound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 395 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_fuel_sufficient_qbound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 410 | `NatLe_lift` | INFO | apply-fwd | Theorem cw2_k_enum_auto_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 410 | `NatLe_drop` | PB | apply-fwd | Theorem cw2_k_enum_auto_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 456 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 469 | `NatLe_drop` | PB | bare | Lemma cw2_r_pow_anti_mono_set | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 587 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 615 | `NatLe_drop` | PB | term-syntax | Theorem cw2_conv_step_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 659 | `NatLe_drop` | PB | bare | Theorem cw2_min_tail_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_diffbridge_incr.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 218 | `NatLe_lift` | PB | apply-fwd | Lemma dbi_abs_lt_half_add_pos | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 220 | `NatLe_drop` | PB | apply-fwd | Lemma dbi_abs_lt_half_add_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 222 | `NatLe_lift` | PB | apply-fwd | Lemma dbi_abs_lt_half_add_pos | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 224 | `NatLe_drop` | PB | apply-fwd | Lemma dbi_abs_lt_half_add_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### abl_dmdnf2_oddlcm.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 123 | `NatLe_lift` | INFO | apply-fwd | Lemma dnf2_oddlcm_le_odprod | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 139 | `NatLe_lift` | INFO | apply-fwd | Lemma dnf2_odprod_le_fact | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 145 | `NatLe_drop` | PB | term-syntax | Theorem dnf2_oddlcm_le_odprod_t | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 150 | `NatLe_drop` | PB | term-syntax | Theorem dnf2_odprod_le_fact_t | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_e_irrational2.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 25 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 368 | `NatLe_drop` | PB | term-syntax | Theorem eir2_kernel_witness | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 394 | `NatLe_drop` | PB | term-syntax | Theorem eir2_kernel_witness | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_lipschitz_bridge.v（18 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 152 | `NatLe_drop` | PB | term-syntax | Lemma lbr_r_pow_dec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 157 | `NatLe_lift` | PB | apply-fwd | Lemma lbr_r_pow_dec | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 160 | `NatLe_drop` | PB | term-syntax | Lemma lbr_r_pow_dec | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 640 | `NatLe_lift` | INFO | bare | Lemma lbr_rsum_ext | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 641 | `NatLe_drop` | PB | bare | Lemma lbr_rsum_ext | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 643 | `NatLe_lift` | INFO | bare | Lemma lbr_rsum_ext | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 656 | `NatLe_lift` | PB | apply-fwd | Lemma lbr_rsum_mono | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 657 | `NatLe_drop` | PB | apply-fwd | Lemma lbr_rsum_mono | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 658 | `NatLe_lift` | PB | apply-fwd | Lemma lbr_rsum_mono | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1031 | `NatLe_drop` | PB | term-syntax | Lemma lbr_iter_cauchy | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1046 | `NatLe_lift` | INFO | term-syntax | Lemma lbr_iter_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 1052 | `NatLe_lift` | INFO | term-syntax | Lemma lbr_iter_cauchy | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 1075 | `NatLe_lift` | INFO | term-syntax | Theorem lbr_banach_fixed_point | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 1076 | `NatLe_drop` | PB | bare | Theorem lbr_banach_fixed_point | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1078 | `NatLe_lift` | INFO | term-syntax | Theorem lbr_banach_fixed_point | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 1079 | `NatLe_drop` | PB | bare | Theorem lbr_banach_fixed_point | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 1212 | `NatLe_lift` | PB | term-syntax | Lemma lbr_iter_cauchy_closed | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 1213 | `NatLe_drop` | PB | term-syntax | Lemma lbr_iter_cauchy_closed | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_loeb_d3.v（76 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 12 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 12 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 16 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 98 | `NatLe_drop` | PB | apply-in | Lemma lbd_unp2_self_bounds | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 98 | `NatLe_drop` | PB | apply-in | Lemma lbd_unp2_self_bounds | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 98 | `NatLe_drop` | PB | apply-in | Lemma lbd_unp2_self_bounds | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 99 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_unp2_self_bounds | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 99 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_unp2_self_bounds | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 103 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_unp2_self_bounds | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 103 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_unp2_self_bounds | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 123 | `NatLe_drop` | PB | apply-in | Lemma lbd_dT2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 123 | `NatLe_drop` | PB | apply-in | Lemma lbd_dT2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 134 | `NatLe_drop` | PB | apply-in | Lemma lbd_dT2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 134 | `NatLe_drop` | PB | apply-in | Lemma lbd_dT2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 138 | `NatLe_drop` | PB | apply-in | Lemma lbd_dT2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 138 | `NatLe_drop` | PB | apply-in | Lemma lbd_dT2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 169 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 169 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 173 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 173 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 188 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 188 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 192 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 192 | `NatLe_drop` | PB | apply-in | Lemma lbd_dF2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 224 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 224 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 228 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 228 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 243 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 243 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 247 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 247 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 247 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 263 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 263 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 267 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 267 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 267 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 272 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 272 | `NatLe_drop` | PB | apply-in | Lemma lbd_dP2_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 304 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_pairp_gt_snd | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 305 | `NatLe_lift` | INFO | apply-in | Lemma lbd_pairp_gt_snd | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 305 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_gt_snd | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 313 | `NatLe_lift` | INFO | apply-in | Lemma lbd_pairp_mono | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 313 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 314 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_pairp_mono | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 316 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 316 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 318 | `NatLe_lift` | INFO | apply-in | Lemma lbd_pairp_mono | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 318 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 319 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_pairp_mono | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 320 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 321 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_pairp_mono | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 324 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 324 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 331 | `NatLe_lift` | INFO | apply-in | Lemma lbd_pairp_mono_snd_lt | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 331 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono_snd_lt | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 332 | `NatLe_lift` | INFO | apply-fwd | Lemma lbd_pairp_mono_snd_lt | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 333 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono_snd_lt | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 333 | `NatLe_drop` | PB | apply-in | Lemma lbd_pairp_mono_snd_lt | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 450 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 454 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_HBL3 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 456 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL3 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 458 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_HBL3 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 460 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL3 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 461 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL3 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 466 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_HBL3 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 469 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL3 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 524 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_HBL2 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 528 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL2 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 531 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_HBL2 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 535 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL2 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 536 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL2 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 543 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_HBL2 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 548 | `NatLe_lift` | INFO | apply-fwd | Theorem lbd_HBL2 | **是（信息位）** | 调用存活9 | W-L2(改名桥→原生) |
| 592 | `NatLe_drop` | PB | apply-fwd | Theorem lbd_diag_necessitation | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### abl_loeb_d3_ext.v（33 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 24 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 24 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 122 | `NatLe_drop` | PB | term-syntax | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 123 | `NatLe_drop` | PB | term-syntax | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 124 | `NatLe_drop` | PB | term-syntax | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 125 | `NatLe_drop` | PB | term-syntax | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 134 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 134 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 145 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 145 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 149 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 149 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 160 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 160 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 164 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 164 | `NatLe_drop` | PB | apply-in | Lemma lbe_dF2b_fuel_inv | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 172 | `NatLe_lift` | INFO | bare | Lemma lbe_dF2b_fuel_inv | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 172 | `NatLe_lift` | INFO | bare | Lemma lbe_dF2b_fuel_inv | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 174 | `NatLe_lift` | INFO | bare | Lemma lbe_dF2b_fuel_inv | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 174 | `NatLe_lift` | INFO | bare | Lemma lbe_dF2b_fuel_inv | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 184 | `NatLe_lift` | INFO | term-syntax | Corollary lbe_dF2b_norm | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 197 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 198 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 199 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 207 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 208 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 225 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 226 | `NatLe_drop` | PB | term-syntax | Theorem lbe_gnF2_fuel | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 238 | `NatLe_lift` | INFO | bare | Theorem lbe_gnF2_fuel | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 239 | `NatLe_lift` | INFO | bare | Theorem lbe_gnF2_fuel | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 248 | `NatLe_lift` | INFO | term-syntax | Corollary lbe_dec_gnF2 | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |
| 290 | `NatLe_drop` | PB | term-syntax | Lemma lbe_dF2_norm_aux | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 301 | `NatLe_lift` | INFO | bare | Lemma lbe_dF_gnF2_none | **是（信息位）** | 调用存活2 | W-L3(原生face重铸) |

### abl_normconv_real.v（5 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 562 | `NatLe_drop` | PB | term-syntax | Theorem rnv_compare_cauchy_partial | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 563 | `NatLe_drop` | PB | term-syntax | Theorem rnv_compare_cauchy_partial | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 586 | `NatLe_lift` | PB | term-syntax | Theorem rnv_compare_cauchy_partial | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 599 | `NatLe_lift` | PB | bare | Theorem rnv_compare_cauchy_partial | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |
| 624 | `NatLe_drop` | PB | term-syntax | Theorem rnv_m_test_geom | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_qpoly_divmod_gen.v（25 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 15 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 15 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 338 | `NatLe_drop` | PB | term-syntax | Lemma qpg_length_align | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 340 | `NatLe_lift` | INFO | apply-fwd | Lemma qpg_length_align | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 340 | `NatLe_drop` | PB | apply-fwd | Lemma qpg_length_align | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 352 | `NatLe_drop` | PB | term-syntax | Lemma qpg_length_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 354 | `NatLe_drop` | PB | term-syntax | Lemma qpg_length_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 362 | `NatLe_lift` | INFO | apply-fwd | Lemma qpg_length_shift | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 362 | `NatLe_drop` | PB | apply-fwd | Lemma qpg_length_shift | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 375 | `NatLe_drop` | PB | term-syntax | Lemma qpg_eval_align | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 377 | `NatLe_lift` | INFO | apply-fwd | Lemma qpg_eval_align | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 377 | `NatLe_drop` | PB | apply-fwd | Lemma qpg_eval_align | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 393 | `NatLe_drop` | PB | term-syntax | Lemma qpg_eval_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 395 | `NatLe_drop` | PB | term-syntax | Lemma qpg_eval_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 404 | `NatLe_lift` | INFO | apply-fwd | Lemma qpg_eval_shift | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 404 | `NatLe_drop` | PB | apply-fwd | Lemma qpg_eval_shift | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 442 | `NatLe_lift` | INFO | apply-fwd | Lemma qpg_length_deg | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 498 | `NatLe_lift` | INFO | apply-fwd | Lemma qpg_lead_shift | **是（信息位）** | 调用存活3 | W-L2(改名桥→原生) |
| 540 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 548 | `NatLe_drop` | PB | term-syntax | Lemma qpg_engine_sound | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 595 | `NatLe_lift` | PB | apply-fwd | Lemma qpg_engine_sound | 否（证明位） | 调用存活3 | W-L1(改名桥) |
| 606 | `NatLe_drop` | PB | term-syntax | Lemma qpg_engine_sound | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 619 | `NatLe_lift` | PB | bare | Lemma qpg_engine_sound | 否（证明位） | 调用存活3 | W-L1(改名桥) |
| 662 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 667 | `NatLe_lift` | INFO | bare | — | **是（信息位）** | 调用存活3 | W-L3(原生face重铸) |

### abl_s06_step_calc.v（58 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 59 | `NatLe_drop` | PB | term-syntax | Lemma sdc_ceil_div_le | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 64 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_ceil_div_le | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 113 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_pow_iter_exact_ge | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 114 | `NatLe_drop` | PB | apply-fwd | Lemma sdc_pow_iter_exact_ge | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 115 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_pow_iter_exact_ge | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 121 | `NatLe_drop` | PB | term-syntax | Lemma sdc_pow_iter_exact_ge | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 142 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 145 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_k_enum_correct | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 148 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 150 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_correct | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 160 | `NatLe_lift` | INFO | term-syntax | Theorem sdc_k_enum_correct | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 179 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 182 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 185 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 189 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_k_enum_minimal | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 193 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_k_enum_minimal | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 199 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 201 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_minimal | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 207 | `NatLe_lift` | INFO | term-syntax | Theorem sdc_k_enum_minimal | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 243 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_logface | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 244 | `NatLe_drop` | PB | term-syntax | Theorem sdc_k_enum_logface | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 245 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_k_enum_logface | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 264 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_decay | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 265 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_decay | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 277 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_iter_lt_decay | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 287 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_half | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 288 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_half | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 289 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_half | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 291 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_iter_lt_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 292 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_iter_lt_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 307 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_q | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 308 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_q | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 309 | `NatLe_drop` | PB | term-syntax | Lemma sdc_iter_lt_q | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 311 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_iter_lt_q | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 312 | `NatLe_lift` | INFO | apply-fwd | Lemma sdc_iter_lt_q | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 336 | `NatLe_drop` | PB | term-syntax | Theorem sdc_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 340 | `NatLe_lift` | INFO | term-syntax | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 341 | `NatLe_drop` | PB | term-syntax | Theorem sdc_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 344 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 345 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 349 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 350 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 352 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 354 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 355 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 357 | `NatLe_lift` | INFO | term-syntax | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L3(原生face重铸) |
| 360 | `NatLe_drop` | PB | term-syntax | Theorem sdc_fuel_sufficient_gen | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 361 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_gen | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 378 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 379 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_fuel_sufficient_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 380 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_fuel_sufficient_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 396 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_fuel_sufficient_qbound | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 397 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_fuel_sufficient_qbound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 398 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_fuel_sufficient_qbound | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 413 | `NatLe_lift` | INFO | apply-fwd | Theorem sdc_k_enum_auto_half | **是（信息位）** | 调用存活14 | W-L2(改名桥→原生) |
| 413 | `NatLe_drop` | PB | apply-fwd | Theorem sdc_k_enum_auto_half | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 516 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 524 | `NatLe_drop` | PB | bare | Lemma sdc_r_pow_dec_iter_set | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_z2_dub3.v（11 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 13 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 13 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 33 | `NatLe_lift` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 33 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 59 | `NatLe_lift` | INFO | apply-fwd | Lemma z2d_sylv_P_pos | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 66 | `NatLe_drop` | PB | term-syntax | Lemma z2d_sylv_a_neq0 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 106 | `NatLe_lift` | INFO | apply-fwd | Lemma z2d_div_mul_le | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 175 | `NatLe_lift` | INFO | apply-fwd | Lemma z2d_sylv_sum_density | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 211 | `NatLe_lift` | INFO | apply-fwd | Lemma z2d_sylv_sum_lt | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 212 | `NatLe_drop` | PB | apply-fwd | Lemma z2d_sylv_sum_lt | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 234 | `NatLe_drop` | PB | term-syntax | Theorem z2d_sylv_floor_t | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### abl_z2_itg_carrier.v（2 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 219 | `NatLe_drop` | PB | apply-fwd | Lemma zb2_term_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 219 | `NatLe_lift` | INFO | apply-fwd | Lemma zb2_term_pos | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### abl_z2_truncfam.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 82 | `NatLe_drop` | PB | apply-fwd | Lemma zb2_bkC_Q_nonneg | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 82 | `NatLe_lift` | INFO | apply-fwd | Lemma zb2_bkC_Q_nonneg | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |
| 85 | `NatLe_lift` | INFO | bare | Lemma zb2_bkC_Q_nonneg | **是（信息位）** | DCE简化(签名槽存活) | W-L3(原生face重铸) |
| 203 | `NatLe_lift` | PB | bare | Lemma zb2_shift | 否（证明位） | DCE简化(签名槽存活) | W-L1(改名桥) |

### abl_z2_valbridge.v（15 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 36 | `NatLe_drop` | REQ | import-list | — | 导入清单 | — | W-X(导入清单) |
| 175 | `NatLe_drop` | PB | term-syntax | Lemma z2v_pow_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 244 | `NatLe_drop` | PB | term-syntax | Lemma z2v_v_add | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 351 | `NatLe_drop` | PB | term-syntax | Lemma z2v_cnt_min | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 397 | `NatLe_drop` | PB | term-syntax | Lemma z2v_fact_ex | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 401 | `NatLe_drop` | PB | term-syntax | Lemma z2v_fact_ex | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 419 | `NatLe_drop` | PB | ltac-embed | Lemma z2v_fact_ex | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 460 | `NatLe_drop` | PB | term-syntax | Lemma z2v_den_val | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 471 | `NatLe_drop` | PB | ltac-embed | Lemma z2v_den_val | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 614 | `NatLe_drop` | PB | term-syntax | Theorem z2v_v_C_ge | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 646 | `NatLe_drop` | PB | term-syntax | Theorem z2v_ppow_dvd_C | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 677 | `NatLe_drop` | PB | term-syntax | Lemma z2v_dvd_pow_split | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 716 | `NatLe_drop` | PB | term-syntax | Lemma z2v_gcd_pow_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 732 | `NatLe_drop` | PB | term-syntax | Lemma z2v_gcd_pow_prime | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 755 | `NatLe_drop` | PB | term-syntax | Theorem z2v_m_dvd_C | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### b1_denom_control.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 79 | `NatLe_lift` | INFO | apply-fwd | Lemma b1_dfact_odd_unfold | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 83 | `NatLe_drop` | PB | apply-in | Lemma b1_dfact_odd_unfold | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 93 | `NatLe_lift` | INFO | apply-fwd | Theorem b1_dfact_odd_pos | **是（信息位）** | 调用存活2 | W-L2(改名桥→原生) |
| 96 | `NatLe_drop` | PB | apply-fwd | Theorem b1_dfact_odd_pos | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### b1_linform_machine.v（6 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 99 | `NatLe_lift` | INFO | apply-fwd | Lemma b1_1leS | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 239 | `NatLe_drop` | PB | bare | Lemma b1_z_lform_core | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 241 | `NatLe_drop` | PB | bare | Lemma b1_z_lform_core | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 298 | `NatLe_drop` | PB | bare | Lemma b1cf_q_ge1 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 354 | `NatLe_drop` | PB | bare | Theorem b1cf_q_mono | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 407 | `NatLe_drop` | PB | bare | Lemma b1_z_sq_shift | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### d7_family.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 55 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |

### dig_machine.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 751 | `NatLe_drop` | PB | term-syntax | Lemma dig_comp_verdict | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 756 | `NatLe_lift` | INFO | apply-fwd | Lemma dig_comp_verdict | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 757 | `NatLe_drop` | PB | apply-fwd | Lemma dig_comp_verdict | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |

### gcl_famsym.v（1 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 651 | `NatLe_drop` | PB | bare | Theorem gcl_famseq_sep | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### piu1891_eggeom_release.v（4 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 10 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 63 | `NatLe_drop` | PB | apply-fwd | Theorem piu1891_exp_series2_le8 | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 107 | `NatLe_drop` | PB | apply-fwd | Theorem piu1891_egcos_lit | 否（证明位） | 擦除(mli `__`) | W-D1(改名桥) |
| 113 | `NatLe_lift` | INFO | apply-fwd | Theorem piu1891_egcos_lit | **是（信息位）** | DCE简化(签名槽存活) | W-L2(改名桥→原生) |

### u4a_budget_flip.v（3 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 105 | `NatLe_drop` | PB | apply-in | Lemma u4a_pi_leibniz_gt_31_10 | 否（证明位） | 擦除(mli `__`) | W-D2(改名桥) |
| 284 | `NatLe_drop` | PB | term-syntax | Lemma u4a_unique_widened_eps4 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 285 | `NatLe_drop` | PB | term-syntax | Lemma u4a_unique_widened_eps4 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### u5c_aux_natpow.v（14 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 16 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 16 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 19 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 19 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 52 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow2_shift | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 65 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow12 | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 66 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow12 | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 72 | `NatLe_drop` | PB | term-syntax | Lemma u5c_pow12 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 90 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow4 | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 91 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow4 | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 97 | `NatLe_drop` | PB | term-syntax | Lemma u5c_pow4 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 119 | `NatLe_drop` | PB | term-syntax | Lemma u5c_pow2b | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |
| 134 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow64 | **是（信息位）** | 调用存活4 | W-L2(改名桥→原生) |
| 142 | `NatLe_drop` | PB | term-syntax | Lemma u5c_pow64 | 否（证明位） | 擦除(mli `__`) | W-D3(改名桥) |

### u5c_aux_natpow_discharge.v（7 位点）

| 行 | 名 | 面 | 形态族 | 宿主语句 | informative? | 提取判读 | 迁移文法 |
|---|---|---|---|---|---|---|---|
| 18 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 18 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 22 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 22 | `NatLe_drop` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 25 | `NatLe_lift` | CMT | comment | — | 注释 | — | W-Z(零迁移) |
| 49 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow12' | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |
| 76 | `NatLe_lift` | INFO | apply-fwd | Lemma u5c_pow4' | **是（信息位）** | 调用存活1 | W-L2(改名桥→原生) |

## 附录 A·Gen2 分账口径小账（数据源 `attn/_natle_probe/_natle_sites_v3.json`＋`_census_extlib.json`·修复席 20261105 程序化复算）

**A1 九面全账**（v3 json `sites` 逐位点 face 计数·裸词面合计 2155）：

| 面 | 位点数 | 说明 |
|---|---|---|
| INFO | 717 | 信息位（Set 宿主内 lift） |
| PB | 1335 | 证明位 |
| CMT | 67 | 注释提及 |
| REQ | 17 | 选择性导入清单 |
| SLOT | 3 | term 面 drop Prop 槽 |
| DEF | 2 | S01_BaseRing.v:91/:100 |
| LOCAL | 9 | DTPT 本地消费 5＋DTPT_Truth 本地消费 4 |
| DEF-LOCAL | 2 | DTPT.v:41/:49 自有同名定义（同名异族） |
| CMD | 3 | **宇宙内 1（UpAblHalfPowFeed.v:270）＋探针件提及 2（`_natle_adjud_probe.v:8` CMD×2）** |
| **合计** | **2155** | 宇宙内 2153＋探针件 2 |

**A2 消费位点 2059 成分注**：drop 1033＝PB-drop 1029＋SLOT 3＋DEF-LOCAL-drop 1；lift 1024＝INFO 717＋PB-lift 306＋DEF-LOCAL-lift 1；DEF 2＝S01_BaseRing 定义面。即 2059＝INFO+PB+SLOT（2055）＋DEF-LOCAL（2）＋DEF（2）——故 §一「DTPT 本地消费分账 9」不含自有定义 2（已计入 drop/lift 两数内），2059＋9＋87＝2155 闭合。

**A3 迁移触及面 2062**：消费位点 2059＋CMD 3＝2062（程序化恒等式：裸词面 2155−CMT 67−REQ 17−LOCAL 9＝2062）。其中 **176 活体信息位**（§一·乙表）由新 informative 原生形供血；其余 2062−176＝1886 为纯证明位/提及面（旧 Prop 形改名桥服务·零原生形迁移）。

**A4 文件数口径**（三档全对齐，正典=order.txt）：

| 口径 | 数 | 成分 |
|---|---|---|
| **正典宇宙** | **375** | `ConstructiveWorld_Live/order.txt` 375 行（`#R` 锚列在卷） |
| _CoqProject 行数 | 376 | ＝正典 375＋`-Q . ""` 选项行 1 |
| 扫描器 file_stats | 378 | ＝正典 375＋3 探针件（`_natle_adjud_probe{,2,3}.v`·untracked 宇宙外） |
| 消费文件 | 103 | 含消费位点（INFO/PB/SLOT/DEF 至少 1）的文件 |
| 实位点文件 | **106** | 含非注释位点（107−d7_family.v）——**迁移实改文件数口径** |
| 全位点文件 | 107 | ＝106＋d7_family.v（仅注释提及 1 处·:55 CMT·单列非迁移） |

**A5 闭包口径**：下游 Require 闭包 **353 件**（正典）；上役 Gen1 总账 355（Gen1 口径存照）；设计席 Require 行解析 351/直连 333（交叉参考·批次预算以 coqdep 复核为准）。

**A6 W 表口径注**：§四 W 表合计 2153＝W-D0..L3 2055＋W-Z 81＋W-X 17，其中 W-Z 81＝CMT 67＋CMD 3（含探针 2）＋LOCAL 9＋DEF-LOCAL 2、DEF 2 单列于总账——探针 2 与 DEF 2 在表合计内互抵，逐面唯一权威以本附录 A1 为准。

## 六·过程登记（本席作业留痕）

1. **tracked 误移事故（当场修复）**：Extraction Library 普查产物落 worktree 根后，本席两次 `mv` 归集时把 root 在册 tracked 历史提取产物（24 件小写 .ml/.mli，如 `alignid.ml`/`upcs.ml`）一并移入 `extlib_ws`＝删改 tracked 面——当即 `git checkout --` 全数还原（`attn/_natle_probe/_moved_tracked.txt` 名单在卷；git status 复验 D 项清零）。此系 ledger §上半场「S14_B5BatchBlock 误删判例」同型陷阱，已按判例处置。root 现势＝git 正本字节；`extlib_ws` 内同名件＝本席普查再生产物（供第三源判读，非 tracked 面）。
2. **普查产物被清扫**：本席 Extraction Library 批次产物（约 60 件）一度被同 worktree 并发进程移至 `attn/_natle_probe/_extr_debris/`（142 件·mtime 12:23-12:24 恰本席批次窗口）——已并回第三源普查 corpus，覆盖率 104/104 不受影响。
3. **并发同题席位在册**：`ConstructiveWorld_Live/_natle_adjud_probe{,2,3}.v` 与 `attn/_natle_adjud_ws/` 系并发席位工作面（本席未触碰、不销毁、分账登记）。inventory 落盘路径 `attn/_natle_site_inventory.md` 为本席任务书指定路径。
4. **附带 .vo 新建**：`abl_z2_valbridge.vo`/`abl_arctan_diff_19.vo` 两件系第三源普查需要、本席经 cpu_guard 现编（rc=0）——.vo 系 gitignore 信任缓存面，不入提交。
5. **工作面清单**（全部在 `attn/_natle_probe/`）：`_scan_natle_sites.py`（v2）/`_scan_v3.py`（v3 终版）/`_natle_sites.json`/`_natle_sites_v3.json`/`_census_extlib.json`/`_firstlast_verify.txt`/`_run_extlib_census.sh`/`extlib_ws`·`_extr_debris`·`term_ws`·`extlib_ws2`（提取 corpus）/`S01_BaseRing.ml`·`S01_BaseRing.mli`（基线机理探针产物——见 .8 漂移注记）/`probe.log`。
6. **releases/ 域**：`releases/CW_ConstructiveWorld_220.v` 等休眠归档含 2572 处词面提及——非编译宇宙（权威清单=Live `order.txt` 375 件·附录 A4），不计入位点账，重建役无需迁移（归档域）。
7. **未竟如实登记**：静态宿主判定为**近似法**（STRONG_SET/STRONG_PROP token 表＋forall 剥离），存在已证两处已知偏差族：①carrier 名表盲区（`real_le_b` 类名缺表→保守判 PROOF；实证=KLWallClosed `klc_powb_mono_weak` 静态 PB 而提取实存调用）；②提取期 DCE（静态 INFO 717 位对提取活体 176 调用/44 模块——〔修复席复算注：§五判读列 DCE简化 标注行 155、调用存活标注行 562，均系模块级计数的逐行标注，非位点级 DCE 计数；本登记初版「237 位」与现表不可复算闭合，已按 census 正典口径改写〕——语义面以 §五判读列与 §一·乙 EXE-VERIFIED 表为准）。信息位终审口径=第三源提取普查（本表判读列），非静态列。
8. **顶层探针件漂移注记（修复席 20261105 补登）**：本席开工探针产物 `attn/_natle_probe/S01_BaseRing.ml`/`.mli`（基线 assert-false 体面＋`val coq_NatLe_drop : __` 签名面）已被后续 12:28 残桩探针覆盖（现 md5 双件同值 `764d66880a15a0810eeb7696c4d55c76` 系 77 字节仅型面残桩·无 val 行）——**全提取体存活件**＝`term_ws/S01_BaseRing.ml:13-17`（lift 体）＋`_wt93_ssa/_gate7probe_S01_work/S01_BaseRing.ml:52-62`（drop `__` 体＋lift 体）＋`_wt93_ssa/_gate7probe_S01_work/_gate7probe_S01_BaseRing.mli:38/:40`（双 val 签名面）；本卷 §二 引用路径已全部改指存活件。
