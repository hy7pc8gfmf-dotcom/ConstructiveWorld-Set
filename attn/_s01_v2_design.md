# _s01_v2_design.md — S01 v2 NatLe 族 informative 重建施工蓝图

> **席位**：S01 v2 设计席（施工蓝本级）· 2026-11-05 · worktree
> `/Users/apple/Desktop/_wt93_rebuild`（分支 `rebuild/sseries-s01-informative`，
> 基线 main@7b3ced9 + 政策卷 0edada3）。
> **上位裁定**：用户裁定 20261105 四条（S 系非正典／甲方案原生 informative／4a-4d
> 全梯终判／PR 制）——见 `attn/SSERIES-REBUILD-S01-SPEC.md` §1 与
> `CONSTRAINTS.md` §11。**消费方式**：本蓝图 §3→§6 依次填入 SPEC 骨架 §5/§6/§7
> 占位（联络员搬运）；§11 registry 三行随 Wave2 PR 落库。
> **判据合法性声明**：本蓝图一切语句面/桥形/文法判据只来自两类来源——
> ①本席今日在 rebuild worktree 的**第一手控制实验**（§0 凭据面，全部命令与输出在卷）；
> ②**用户点名判例**（qpg_degge1 @Id bool 形 abl_qpoly_divmod_gen.v:82·本席实读；
> UpReqSymplecticBridge.v:304 `apply Qle_to_QleT'` 桥形·本席读自主工作区世界副本；
> UpReqAlign3.v:94,:100-102 Notation 形·本席实读；
> qeqT_imp_qeq S02:147·z2v_idS_eq abl_z2_valbridge.v:91-96·均本席实读）。
> 零 S 系现状判据引用
> （S01 现状只作**施工对象**与**反例展品**引用）。

---

## §0 凭据面（本席第一手实验登记·全部 2026-11-05 实跑）

| # | 实验 | 命令（cpu_guard 包裹，cwd=worktree 根） | 结果 |
|---|---|---|---|
| A | 基线提取擦除复现 | `…/cpu_guard.sh -MaxWaitSec 120 -- …/rocq93/bin/coqc -native-compiler no -q -Q ConstructiveWorld_Live "" attn/_natle_probe/_probe_natle_extract.v` | RC=0；产物 `attn/_natle_probe/S01_BaseRing.mli`（md5 eeb441fef133de369775ad1f1c4e93fb）：`val coq_NatLe_drop : __`＋`val coq_NatLe_lift : nat -> nat -> coq_NatLe`；Obj.magic 计数 ml=0/mli=0；PA 2×`Closed under the global context` |
| B | v2 桥件探针（对真实 S01 世界） | 同通路，`attn/_natle_probe/_probe_v2_bridges.v` | RC=0；6/6 `Closed under the global context`；产物 `_probe_v2_bridges.mli/.ml`：**Obj.magic 双面 0**；val 面见 §2 表 |
| C | OCaml witness 4b/4c/4d | `…/rocq93/bin/ocamlc -o _natle_witness.exe Datatypes.mli Datatypes.ml PeanoNat.mli PeanoNat.ml S01_BaseRing.mli S01_BaseRing.ml ProbeNatLeV2.mli ProbeNatLeV2.ml _natle_witness.ml`＋实跑 | 编译 RC=0；实跑 RC=0；**对表 11/11 MATCH**；桥面 off-contract 实证 `Assert_failure`；native 面实证 `None`（total）；计时见 §2.4 |
| C2 | 迁移文法端到端（G1-G6） | 同 B 通路，`attn/_natle_probe/_probe_v2_consumer.v` | RC=0；6/6 Closed（G1-G6 全形编译过＋PA Closed）；提取产物移入 probe 目录 |
| — | 位点普查 | **Gen2 程序化普查（正典）**＝裁勘席静态扫描 v3（`attn/_natle_probe/_scan_v3.py`）＋104/104 消费模块 `Extraction Library` 全量实提；本席早期 v2 扫描（`_scan_natle_sites.py`·2,086／族形 apply-fwd 873／apply-in 354／term-syntax 729／bare 129·PROOF 2,058＋TERM 28）系另一词界 token 口径、无独立证据面，**已由 Gen2 普查取代作废存照、禁作验收口径** | **正典（钉版规范 commit `ca315c0`）**：消费位点 **2,059**（drop 1,033＋lift 1,024＋DEF 2）／消费文件 103／实位点文件 106（grep 文件集 107 含 d7_family.v 仅注释提及 1 处·单列非迁移）／下游 Require 闭包 353；族形（v3 json 宇宙口径）apply-fwd **936**／apply-in **351**／term-syntax **660**／bare 94＋ltac-embed 14（`_natle_sites_v3.json`）；**lift 提取活体 176 处/44 模块·drop=0**（数据源 `_census_extlib.json` 程序化实测·钉版规范 §一·乙表逐条在卷） |
| — | 反向闭包 | python Require 行解析＋reverse-BFS（闭包含传递层） | **S01_BaseRing 消费闭包 351 件**（直连 Require 333 件）——**正典＝下游 Require 闭包 353（钉版规范 commit `ca315c0`）**；本席 Require 行解析 351 系交叉参考（批次预算以 coqdep 复核为准；上役 Gen1 总账 355 已存照作废） |
| — | 值级消费裁定（缺口④） | `ConstructiveWorld_Live/_natle_adjud_probe.v` 提取（前任裁勘席 workspace，本席复读产物） | `abl_qpoly_divmod_gen.mli`：`qpg_engine_sound : … -> qpg_divisor_ok -> coq_NatLe -> …`（**NatLe 载体在值签名在役**）；`SumInvFactEscape.mli`：`sif_enum : … (nat -> coq_NatLe -> …) sigT`（同上）；`abl_Pr_euclid_03.mli`：`peu_next : nat -> nat`（drop 只在其**证明槽**） |
| — | 事故两起（本席自伤，已全部还原） | 根目录 `.ml/.mli` 清扫/提取覆盖误伤 tracked 历史提取产物 | 第一起 30 件 `D`、第二起 8 件 `M`——`git restore` 后 `git status --short` 恢复至本席开工前 5 个 untracked 探针区；**教训入 §5 坑位 K1** |

实验 A 与前任席（12:09）产物互证一致（同 mli 面）。实验 B/C/C2 为本席独立新增。

### §0.1 并发设计席合并账（2026-11-05 第二实例合并·E 组实验为该席独立实跑）

> **并发事实**：本蓝图首版（12:35）落盘后，同任务书并发实例（第二设计席）在
> `attn/_s01v2_probe/{r0,r1}/` 完成了独立控制实验（自含探针＋双提取配方＋ocamlc
> 驱动）。经逐项对拍：**两实验集结论互证一致**（原生面 informative 非 `__`／
> magic 双面 0／PA Closed／`__` 由签名决定），第二实例无推翻本蓝图任何裁定，
> 其互补增量按 E 组并入；本蓝图保持单一正本，命名裁定（原生面占正典名＋`_le`
> 降格注册桥）不变。

| # | 实验（第二实例·全部 2026-11-05 实跑） | 命令（cpu_guard 包裹，cwd=`attn/_s01v2_probe/r0|1`） | 结果 |
|---|---|---|---|
| E1 | 自含探针编译＋内核证 | `…/coqc -native-compiler no -q -Q . "" s01v2_design_probe.v`（r0/r1 双配方） | 双配方 RC=0；**.vo 头字节 `436f7121 000160bc`＝`43 6f 71 21 00 01 60 bc`（9.3 第一手实测；修复席对本树 `ConstructiveWorld_Live/S01_BaseRing.vo` 头字节复核同值——SOP 9.1 口径字面 `…5ff4` 勘误在案·§4.1 锚点已同步）**；PA 探针 16/16 `Closed under the global context`；`coqchk -o` → EXIT=0＋successfully checked＋`Axioms: <none>` |
| E2 | **对照组实验（签名决定论）** | 同探针含 `NatLe_drop_ctl`/`NatLe_lift_ctl`（基线签名＋基线含 lia 证明）与新桥（同签名＋无 lia 重铸）对提 | 提取形**逐字同一**（`_ctl` mli:17/21 = 新桥 mli 行）——**`__` 擦除由签名决定、与证明无关**：证明重写不治愈 Prop 结论面，类 (a) 治愈唯一途径＝informative 面（registry 证据位＋B2 无 lia 变体的合法性边界依据） |
| E3 | **消费者擦除边界律** | 同探针 famA/famB/famC/famD/famE（五族消费形态复刻） | **结论 sort 决定消费者语句提取面**：结论 NatLe/Id 者全部非 `__`（`famA_lift_apply : nat -> coq_NatLe`、`famE_contract : … -> coq_NatLe -> coq_NatLe -> bool coq_Id -> bool coq_Id`），即使证明体消费桥；结论 Prop 者擦除 ⇒ mass 批 4a 预期表机械判据（§4.2 锚点补充） |
| E4 | **4d 双配方计时** | r0 默认 unary 配方＋r1 `ExtrOcamlNatInt`＋`Extract Inlined Constant Nat.leb => "(<=)"`（stdlib 判例 ExtrOcamlNatInt.v:64 同形——该 realizer 系 stdlib 现行行，非新造） | r1：1,000,000 判定＝0.019664s→**19.7ns/判定 O(1)**；r0 unary：1000 判定（100..249）＝47.9ms（≈48µs/判定）、单判定 (50000,60000)＝0.9ms → O(min)；两配方提取件 magic 均 0；驱动契约表各 7/7 MATCH＋见证链结构等价回读 true（`CONTRACT_TABLE_ALL_MATCH=true`、RUN_EXIT=0） |
| E5 | tracked 树普查交叉（与 A 组 token 精扫口径互证） | `grep -l/-o NatLe_drop\|NatLe_lift *.v`（裸词面口径） | 实改文件 **106**（grep 文件集 107 含 d7_family.v 仅注释提及 1 处——单列非迁移·钉版规范 `ca315c0` 附录 A4）；drop 1084＋lift 1069＝2,153 裸词面——与上役 Gen1 总账 2,147 同为裸词面量级；扫描域 378 件系含 3 探针件、正典宇宙=order.txt 375；**验收口径唯一＝钉版规范 Gen2 普查（commit `ca315c0`·消费位点 2,059／活体 176/44）**，本行与 A 组 token 精扫（2,061）均存照禁作验收 |

第二实例补充验证件：`NatLe_refl`（见 §1.1 F4 行）与 B2 无 lia 变体（见 §1.2 注）、
4d realizer 配方（见 §2.4 增补）——均已按本蓝图「禁未验证入库」律先验证后并入。

---

## §1 新语句面（NatLe 族 informative 原生签名·逐条）

> 命名裁定：**原生面占用正典名** `NatLe_drop`／`NatLe_lift`（补丁形语义，本席独立
> 第一手验证——见实验 B；补丁文件仅作语义参照不作施工蓝本，符合用户裁定）；
> 旧签名降格为注册桥，加 `_le` 后缀让位。载体 `NatLe` 不动（基线 S01_BaseRing.v:88
> 已是 informative 形，零迁移）。

### §1.1 原生面（(a) 类 data-carrying·不注册·签名即契约）

```coq
(* N0 载体 — 与基线 S01_BaseRing.v:88 逐字同形，零迁移 *)
Definition NatLe (n m : nat) : Set := Id (Nat.leb n m) true.

(* N1 消去面（值级可用的方向判定读出）—— 对齐 qpg_degge1 @Id bool 形
   （abl_qpoly_divmod_gen.v:82）；提取面 nat -> nat -> coq_NatLe -> bool coq_Id *)
Lemma NatLe_drop : forall n m : nat, NatLe n m -> @Id bool (Nat.leb n m) true.
Proof. intros n m H. exact H. Qed.

(* N2 注入面（值级可用的方向判定写入）—— N1 的镜像 *)
Lemma NatLe_lift : forall n m : nat, @Id bool (Nat.leb n m) true -> NatLe n m.
Proof. intros n m H. exact H. Qed.

(* N3 通用 Set-Id → Prop-eq 消除器 —— z2v_idS_eq 正典形
   （abl_z2_valbridge.v:91-96 逐字同构）；桥对证明的支点件 *)
Lemma id_eq_S : forall (A : Set) (x y : A), Id x y -> x = y.
Proof. intros A x y H.
  exact (match H in Id _ z return x = z with id_refl => eq_refl end). Qed.

(* F4 反射面（第二实例补席验证件·E1-E3 实跑）—— 符号 n=n 直闭免绕 Prop，
   正典 destruct+reflection 形无 lia；提取面 nat -> coq_NatLe 非 __，
   不可达分支 assert false 零 magic（E1） *)
Lemma NatLe_refl : forall n : nat, NatLe n n.
Proof.
  intros n. unfold NatLe. destruct (Nat.leb n n) eqn:E.
  - exact id_refl.
  - exfalso. exact (Nat.lt_irrefl n (proj1 (Nat.leb_gt n n) E)).
Qed.
```

**逐条签名（提取面，实验 B 第一手）**：

| 件 | Coq 签名 | 提取面（.mli val） | 分类（§11） |
|---|---|---|---|
| `NatLe` | `nat -> nat -> Set`（`Id (Nat.leb n m) true`） | `type coq_NatLe = bool coq_Id` | (a) |
| `NatLe_refl`（补席验证件） | `forall n, NatLe n n` | `val coq_NatLe_refl : nat -> coq_NatLe`（E1 第一手：非 `__`、不可达分支 assert false、零 magic） | (a) |
| `NatLe_drop` | `forall n m, NatLe n m -> @Id bool (Nat.leb n m) true` | `val coq_NatLe_drop : nat -> nat -> coq_NatLe -> bool coq_Id`（体＝投影，**total**） | (a) |
| `NatLe_lift` | `forall n m, @Id bool (Nat.leb n m) true -> NatLe n m` | `val coq_NatLe_lift : nat -> nat -> bool coq_Id -> coq_NatLe`（体＝投影，**total**） | (a) |
| `id_eq_S` | `forall (A:Set) (x y:A), Id x y -> x = y` | `val coq_id_eq_S : __`（纯逻辑件） | (b) 注册 |

### §1.2 桥件（(b) 类注册·旧 Prop 面等价物的**去留判定**）

**缺口④逐点判词**（本席第一手，修正总账预判）：

- **旧 `NatLe_drop`（S01_BaseRing.v:91，结论 `(n<=m)%nat` : Prop）**：结论 Prop ⇒
  类型学上**不可能**被任何值位消费（Prop 结果不能占 Set 槽）；Gen2 正典 2,059 位点
  中 drop 侧 1,033 位全部在证明位或 term 内 Prop 槽（euclid:106 实证形；
  `_census_extlib.json` 全库 drop 调用=0 机械实证）。**判定＝纯证明工具**：不重铸为
  数据件，**保留 Prop 面降格注册**为 `NatLe_drop_le`。同时 N1 原生面补上值级读出
  能力（旧树缺失的能力，非替代旧用例）。
- **旧 `NatLe_lift`（S01_BaseRing.v:100，前提 Prop、结论 informative）**：**半泄露
  实锤＝提取值面 partial**：实验 A 体面 `match leb n m with true -> id_refl |
  false -> assert false`——**前提擦除后值路径 off-contract 即崩**（实验 C 实跑
  `(5,3)` 抛 `Assert_failure`）。**判定＝证明工具＋值面 partial**：保留 Prop 面
  降格注册为 `NatLe_lift_le`（注册行**必须记载 partiality**）；值路径由 N2
  （total 投影）接管。

```coq
(* B1 消去桥 —— qeqT_imp_qeq 正典形（S02_CauchyComplete.v:147）
   证明思路一句：Id 面经 id_eq_S 还原 bool 方程，Nat.leb_le 投影为 Prop 序。 *)
Lemma NatLe_drop_le : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  apply (proj1 (Nat.leb_le n m)).
  exact (id_eq_S bool (Nat.leb n m) true (NatLe_drop n m H)).
Qed.

(* B2 注入桥 —— Qle_to_QleT' 方向正典形（UpReqSymplecticBridge 桥形 L304，
   apply 形）；证明思路一句：计算 Nat.leb n m，true 支 id_refl 收，
   false 与前提经 Nat.leb_gt 矛盾 lia 收。 *)
Lemma NatLe_lift_le : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H. unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - exact id_refl.
  - exfalso. apply (proj1 (Nat.leb_gt n m)) in E. lia.
Qed.
```

> **B2 无 lia 变体（第二实例补席验证·E1 实跑·实现席可选）**：false 支可免 lia 以
> 反射引理闭——`exfalso. exact (Nat.lt_irrefl n (Nat.le_lt_trans n m n H
> (proj1 (Nat.leb_gt n m) E))).`——与 qeqT_imp_qeq「反射引理＋不可达分支」工艺
> 同律（判据优先·零 solver）；提取形与 lia 版逐字同面（E2 签名决定论实证：
> 擦除/体面由签名与计算结构决定，证明内 solver 差异不入提取件）。B1 无 lia 形
> 即上文正文（destruct+inversion，基线同形）。两变体任选其一落库，均须 born-in-place
> 五证绿＋PA Closed 后入账。

| 件 | 提取面（实验 B/C2 第一手） | §11 分类与注册要点 |
|---|---|---|
| `NatLe_drop_le` | `val coq_NatLe_drop_le : __` | (b) **注册**；`__`=accepted；登记消费位证据（Gen2 正典 2,059 位点中 drop 侧 1,033 位） |
| `NatLe_lift_le` | `val coq_NatLe_lift_le : nat -> nat -> coq_NatLe`（**无 `__`**；体＝`let b = Nat.leb n m in match b with true -> id_refl \| false -> assert false`） | (b) **注册**；非擦除语句（Prop 前提 informative 结论＝qeq_imp_qeqT 族正典形）；注册行**记载 partiality＋值路径调用契约**（仅 leb-true 对；Coq 侧受型守卫，提取侧只对手写 OCaml 构成约束） |
| `id_eq_S` | `val coq_id_eq_S : __` | (b) 注册（纯逻辑支点件） |

**去留判定总表**：

| 旧件（基线） | 处置 | 理由（第一手锚） |
|---|---|---|
| `NatLe`（:88） | **留**（逐字不动） | 已 informative；实验 A `type coq_NatLe = bool coq_Id` |
| 旧 `NatLe_drop` 签名（:91） | **改名降格注册**→`NatLe_drop_le` | 结论 Prop 纯证明工具（缺口④判词）；正典名让位给原生面 |
| 旧 `NatLe_lift` 签名（:100） | **改名降格注册**→`NatLe_lift_le`＋partiality 记载 | 值面 partial 实证（Assert_failure）；正典名让位 |
| Class 字段位 `NatLe N m -> NatLe N n`（:184 等） | **留**（零迁移） | 载体不动；字段面 informative |
| 具体值站点 `exact id_refl`（如 b1_denom_control.v:77） | **留**（零迁移） | leb 具体计算后 id_refl 可闭（G6 探针验证） |

**候补成员（非本蓝图验收面·本席未验证）**：`NatLe_dec : forall n m, Or (NatLe n m)
(Not (NatLe n m))`（Set 层 sum 判定器，值级人体工学件）。实现席可选增补，增补则
4a-4d 全梯同验并补 registry。**禁未验证入库。**

---

## §2 桥引理对（4a-4d 自身达标声明）

### §2.1 签名与证明思路
见 §1.2 代码块（B1/B2 全文）＋N3 支点件（§1.1）。方向命名律承 §1·H 门名口诀：
**门名前半＝来源面，后半＝目标面**——`NatLe_drop_le`＝NatLe(→Id)→le(Prop)，
`NatLe_lift_le`＝le(Prop)→NatLe；两向不可换。

### §2.2 自身 4a 达标声明（实验 B 第一手）
- 编译：RC=0，绿判四件套齐（EXIT=0 无管道真取／日志零 Error／.vo 落盘／PA）；
- PA：6/6 `Closed under the global context`（drop/lift/id_eq_S/drop_le/lift_le/roundtrip）；
- 官方法口径的提取普查（本席探针为单命令多名全提：`Separate Extraction` 一条命令
  七名）：**Obj.magic .ml=0 / .mli=0**；
- `__` 分账：`NatLe_drop_le`／`id_eq_S`＝`(b)` 注册预期擦除（accepted）；
  `NatLe_lift_le`＝**val 面无 `__`**（informative val）；
  原生面 `NatLe_drop`/`NatLe_lift`＝informative val 非擦除。
- **边界声明**：本声明基于探针模块（7 名）；Wave2 落库件须对 S01 v2 全语句名重跑
  官方法全名普查（gate7_extract_run.py，驱动覆盖数=statement_scan 全名数逐字报数），
  探针绿不代落库绿（§1·J scope 假绿病四律适用）。

### §2.3 自身 4b/4c 达标声明（实验 C 第一手）
- 4b 可执行：ocamlc 编译 RC=0；实跑 RC=0 不崩。
- 4c 能用（对表即证据，禁 exit 0 充证）——11 对全 MATCH：
  `(0,0)/(0,5)/(3,3)/(3,5)/(3,4)/(12,12)/(1,1000)/(999,1000)` 出具
  `witness=Coq_id_refl expected=true MATCH=true`；
  `(5,3)/(7,2)/(1000,999)` 出具 `no-witness expected=false MATCH=true`；
  负例契约双实证：桥面（旧 lift 体）off-contract `(5,3)` → `Assert_failure`；
  native 面 off-contract → `None`（total 不崩）。
- 对表独立可核验：期望值由 `Nat.leb` 独立重算，与 witness 链（`leb → lift → drop`）
  交叉对拍。

### §2.4 自身 4d 达标声明（实验 C 第一手计时）
- 判定成本＝**O(首参数)**（`Nat.leb` 一元线性遍历）：实测 10⁶ 次原生往返
  （预构 nat 池，a∈[0,500)，a≤b）＝**5.092s ≈ 5.1µs/判定（≈20ns/一元步）**；
  单次大判定 `(1000000,1000000)`＝**0.3366s**（深链缓存效应，≈337ns/步量级）。
- **性能合格线入档文案**（Wave2 写入模块文档）：NatLe 判定 O(首参数) 一元遍历，
  ~20ns/步（浅链）~337ns/步（10⁶ 深链）量级；**lia 回退仅证明面，禁入热路径**；
  热路径值判定一律 native 面（total）。
- 桥面不入热路径的机械面：`_le` 后缀名＋§11(b) 注册＋提取面为投影/计算（无数据
  槽），值路径误用被 witness 契约表显式证伪。

**4d 配方增补（第二实例补席·E4 实跑·建议采纳为 prescribed recipe）**：提取配方加一行
`Extract Inlined Constant Nat.leb => "(<=)"`（stdlib 正典判例
`ExtrOcamlNatInt.v:64` 对旧面 `Compare_dec.leb` 的现行同形行，非新造 realizer；
ExtrOcamlNatInt 自带 nat=>int 映射）——判定降至 **O(1) 实测 19.7ns/判定**
（1,000,000 判定 0.019664s，`driver_r1`），见证链 roundtrip (50000,60000)
0.000003s；r1 提取件 magic 仍双面 0、契约表 7/7 MATCH。缺省 unary 配方即上文
O(首参数) 线（E4 复测同量级）。**模块文档 4d 线两态并列**：prescribed（int
realizer·O(1)）与 fallback（unary·O(首参数)），实现席按认证管线配方择一并实测入档。

---

## §3 迁移文法（三族位点旧形→新形机械规则）

> **口径锚（Gen2 正典·钉版规范 commit `ca315c0`）**：消费位点 **2,059**＝apply-fwd
> **936**＋apply-in **351**＋term-syntax **660**＋bare 94＋ltac-embed 14＋DEF 2
> （`_natle_sites_v3.json` 宇宙口径·数据源 `_census_extlib.json` 活体 176/44）；
> 迁移 W 码分账（W-D0..W-X）以钉版规范 §四为唯一权威。本节 §3.1-3.3 计数一律
> Gen2 普查实数，设计席早期 v2 扫描数（873/354/729/129）作废存照。

> **总律（改名律）**：`NatLe_drop`→`NatLe_drop_le`、`NatLe_lift`→`NatLe_lift_le`，
> 实参表逐字不动（含 `_ _` 显式参纪律，承 §1·H 两参显式）。**漏改位点必然编译红**
> （类型面可判定：旧用位的 Prop 面与原生面 Id 面不统一；G1-G6 反向验证），不存在
> 静默绿——编译驱动收敛，残余位点以 grep 残余账=0 复核（见 §5 批闸）。
> **零迁移白名单**：载体 `NatLe` 本身、具体值 `exact id_refl` 站点（G6）、
> Require 提及行/注释提及（词界扫描剥注释后=0）。

### §3.1 G1 apply 前置形（Gen2 普查 936 位·apply-fwd·`_natle_sites_v3.json`）

- **旧形**（b1_denom_control.v:79 实样）：`apply NatLe_lift.`（目标 NatLe 面，
  后续 lia/Prop 链）／`apply NatLe_drop.`（目标 le 面）
- **新形规则**：桥名替换——`apply NatLe_lift_le.` ／ `apply NatLe_drop_le.`
  后续 lia/Prop 链**逐字不动**（桥对签名与旧件同面，故链零改）。
- **模板**：
  ```
  - apply NatLe_lift_le.        (* was: apply NatLe_lift. *)
    <原有 Prop/lia 链逐字不动>
  ```
- **探针验证**：G1（`_probe_v2_consumer.v`）`intros k. apply NatLe_lift_le. lia.` RC=0。

### §3.2 G2 apply-in 形（Gen2 普查 351 位·apply-in）

- **旧形**（b1_denom_control.v:83 实样）：`apply NatLe_drop in IH. apply Nat.mul_le_mono_l. exact IH.`
- **新形规则**：`apply NatLe_drop_le in H` ／ `apply NatLe_lift_le in H`——后续
  链零改。
- **模板**：
  ```
  apply NatLe_drop_le in H.     (* was: apply NatLe_drop in H. *)
  <原有链逐字不动>
  ```
- **探针验证**：G2（含 lift 目标前置＋drop-in 中段双桥链）RC=0。

### §3.3 G3 term 级形（Gen2 普查 660 位·term-syntax）

- **旧形**（S02_CauchyComplete.v:447 实样逐字）：
  `apply NatLe_lift. apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hm)].`
- **新形规则**：term 内桥名替换＋桥调用模板——`exact (NatLe_drop_le _ _ H)`／
  `pose proof (NatLe_lift_le _ _ H)`／`rewrite` 位同置换；嵌套 ltac: 内位
  （SumInvFactEscape.v:442 `ltac:(pose proof (NatLe_drop _ _ Hn0); lia)`）同规则，
  桥调用插入即替换原调用名，不增行。
- **模板**（term 槽桥调用插入形）：
  ```
  exact (NatLe_drop_le _ _ H).        (* was: exact (NatLe_drop _ _ H). *)
  pose proof (NatLe_lift_le _ _ Hx).  (* was: pose proof (NatLe_lift _ _ Hx). *)
  ```
- **探针验证**：G3（S02:447 逐字战术行换名）＋G4/G5（Definition 体）RC=0。

### §3.4 特殊形补则（term 级的值体变种）

- **G4 lift-in-Def-body**（abl_qpoly_divmod_gen.v:666-668 实样）：
  **〔复核轮 1 改判（Issue-②·用户「徒有其名」禁令）〕**G4 系**真病活位**——
  `:667` `NatLe_lift _ _ (Nat.le_refl (length p))` 向 `qpg_engine_sound` 第四参
  `NatLe (length p) fuel`（Set 载体槽·`abl_qpoly_divmod_gen.v:541-543`）喂
  **运行时值**；基线提取 `Nat.leb` 凭空重算＋假分支 `assert false` 危形在卷
  （`attn/_natle_probe/term_ws/S01_BaseRing.ml:13-17`；提取活体
  `abl_qpoly_divmod_gen.ml:147` census 在案·钉版规范 §一·乙 #17 行）。
  **禁以旧 Prop 形改名桥 `NatLe_lift_le` 供血此位**——其提取体保留 leb 重算＋
  assert false＝真病活位上徒有其名。**改判：全部 176 活体位点**（钉版规范
  `ca315c0` §一·乙 EXE-VERIFIED 表逐条在卷·含本点 :667 `Nat.le_refl` 信息位
  消费）**一律由新 informative 原生形供血（恒等 exact H 形）**——
  `NatLe_lift n m H`（提取面 `nat -> nat -> bool coq_Id -> coq_NatLe` 全投影
  total·实验 B 第一手）；本点 `:667` 的槽型＝`NatLe (length p) (length p)`
  （`fuel`＝`length p`），原生形供血样＝**`NatLe_refl (length p)`**（§1.1 F4
  验证件·E1 实跑：`forall n, NatLe n n` 恰交付槽型·提取 `nat -> coq_NatLe`
  非 `__`·零 magic。注：Prop 形 `Nat.le_refl` 系 `length p <= length p` : Prop，
  不入原生 lift——原生面入参系 Id 面非 Prop 面）；**旧 Prop 形（`NatLe_lift_le`/`NatLe_drop_le`）
  仅作 proof-bridge registry 条目服务证明位**（迁移触及面 2062＝消费位点 2,059＋
  CMD 3，其中 2062−176＝1,886 纯证明/提及位点零原生形迁移——恒等式与成分注见
  钉版规范 `ca315c0` 附录 A3）。活体位点不入 `_le` 注册行、4a 验收取
  「提取面零 magic＋值面 total」。（原「改名律直接适用＋入 `NatLe_lift_le` 值体
  消费证据列」方案作废存照。）
- **G5 drop-in-Def-body**（abl_Pr_euclid_03.v:105-107 实样）：`Definition` 体内
  向 sigT 的 **Prop 槽**喂 drop——改名律适用（`NatLe_drop_le 2 (fact n + 1) …`），
  提取后该槽整体擦除（peu_next : nat -> nat 实证）——无数据入值位，(b) 合法。
- **G6 具体值位**：零迁移白名单（leb 具体计算后 `exact id_refl` 照闭）。

### §3.5 三硬核专属改法草案（改名律展开到站）

1. **b1_denom_control.v**（:75 语句／:79／:83；硬核一）：语句面 `NatLe
   (b1_dfact_odd n) (b1_dfact_even n)` 不动；基例 `exact id_refl` 不动（G6）；
   :79 `apply NatLe_lift.` → `apply NatLe_lift_le.`；:83 `apply NatLe_drop in IH`
   → `apply NatLe_drop_le in IH`；`replace … by lia` 链不动。**草案=2 处改名**。
2. **abl_Pr_core_01.v**（:142-167；硬核二）：:148 `apply NatLe_lift. exact Hleb.`
   → `apply NatLe_lift_le. exact Hleb.`；:150-151 两处
   `pose proof (NatLe_drop _ _ Hd2/Hdlt)` → `NatLe_drop_le`；:165
   `apply (NatLe_drop _ _ H2)` → `apply (NatLe_drop_le _ _ H2)`；其下 lia 链不动。
   **草案=4 处改名**（:148/:150/:151/:165）。
3. **S02_CauchyComplete.v**（:447-452＋:508/:512 同形；硬核三·最大体量 120 位）：
   每行双桥——`apply NatLe_lift.`→`apply NatLe_lift_le.`＋
   `exact (NatLe_drop _ _ Hm/Hn)`→`exact (NatLe_drop_le _ _ Hm/Hn)`；行内
   `Nat.le_trans with (max N1 N2)` 结构逐字不动。本件**排在 pilot 末位**（其
   Require 被大量下游依赖，born-in-place 后世界撕裂窗最长）。件内
   `qeqT_imp_qeq`（:147 正典判例）**零触碰**。

> **〔复核轮 1 衔接注（Issue-② 改判对 §3.5 的约束·⑨ 一致性）〕**上列三草案中
> 纯证明位照走改名律（`_le` 桥·registry 服务）；但其**提取活体值位**（b1 2 调用
> /abl_Pr_core_01 证书槽·4 调用/S02 `real_plus` 族·7 调用——§一·乙 EXE-VERIFIED
> 表逐条在卷）落位时**一律由新 informative 原生形供血**（恒等 exact H 形／
> F4 `NatLe_refl` 反射形／destruct+reflection·E3 律），**禁以 `NatLe_lift_le`
> 的 leb 重算＋assert false 体供血活位**（§3.4 G4 改判同律）；改名律余文对
> 纯证明位点不变。实现席逐活位重验 4a（提取面零 magic＋值面 total）后入账。

---

## §4 波次计划（Wave2 / Wave3+ / 终局）与 4a-4d 逐层锚点

> 通用纪律：一切编译经 cpu_guard（9.3 通路）；PR 制（禁直 push main，禁
> `git add -A`，白名单逐件 add＋推送前 diff 面断言＝恰为目标件集）；每件绿判
> 四件套＋PA 锚定计数；E949 触树即按 coqdep 闭包预算，批 ≤80。

### §4.0 Wave1（已就位，不重做）
基线 7b3ced9＋政策卷 0edada3（§11 政策＋SPEC 骨架）＋勘形/普查/裁勘探针
（本席 §0 凭据面为其输入）。

### §4.1 Wave2 = S01 v2 实现＋pilot 批（三硬核＋5 机械文件）全梯终判

**范围与序**（born-in-place 序，撕裂预期见 K3）：
1. `S01_BaseRing.v` 重建落位：§1.1 原生面 N0-N3（N0 逐字不动）＋§1.2 桥件 B1/B2；
   件内自有位点（:184 Class 字段照旧；:1040 等族内位点按 §3 文法改名）；
   **§11 registry 三行**（NatLe_drop_le／NatLe_lift_le／id_eq_S）随同 PR 携
   消费位证据入库；模块文档写入 §2.4 性能合格线段。
2. 机械 5 件：`abl_z2_valbridge.v`（drop 位点 ：175/:244/:351 pose 形）→
   `abl_qpoly_divmod_gen.v`（G4 值体 ：667）→ `abl_Pr_euclid_03.v`（G5 值体
   :106）→ `SumInvFactEscape.v`（G3 嵌套 ltac: :442/:462）→ `BeukersLists.v`
   （41 位批量机械·批工具实战）。选择理由：覆盖 G1-G5 全形＋一典型批文件，
   全部为 abl/lib 中低拓扑件（撕裂窗短）。
3. 三硬核：`b1_denom_control.v` → `abl_Pr_core_01.v` → `S02_CauchyComplete.v`
   （§3.5 草案展开，S02 末位）。
4. 落位面含 §1.1 全件：N0-N3＋**F4 `NatLe_refl`（补席验证件·E1 实跑）**＋
   §1.2 桥件 B1/B2；提取配方随认证管线择定 4d 配方（§2.4 增补）并实测入档。

**Wave2 每件验收锚点（4a→4d 逐层，禁降梯）**：

| 梯 | 锚点（逐件第一手） |
|---|---|
| **4a 可提取** | ①绿判四件套（EXIT=0 无管道真取／日志零 Error／.vo 落盘／PA）；**魔数锚（本树 9.3 实测·修复席 vo 头字节复核同值）**：`.vo` 头字节＝**`436f7121 000160bc`**（＝`43 6f 71 21 00 01 60 bc`；SOP 绿判四件套的 `43 6f 71 21 00 01 5f f4` 系 9.1 口径字面——**9.3 通路一律以 `436f7121 000160bc` 为准，禁回用 5ff4**）／mtime 新于源②PA 行首锚定计数申报（S01 v2 目标=99/99 守恒改口后重报）③**官方法 gate7 全名普查**（`scripts/gates/gate7_extract_run.py`，驱动名数=statement_scan 全名数逐字报数，单命令多名全提）：.ml/.mli 双面 **Obj.magic=0** ④`__` 分账对 registry：原生族名（NatLe/NatLe_drop/NatLe_lift/NatLe_refl）**非 `__`**；drop_le/id_eq_S `__`=注册行在卷；lift_le val informative；**消费者语句预期表（第二实例 E3 律）＝结论 NatLe/Id 者非 `__`、结论 Prop 者擦除——增量偏离逐名裁勘**⑤语句名存活差分零失名 |
| **4b 可执行** | witness 程序（§0 实验械具同款）ocamlc 编译 rc=0＋样本实跑 rc=0 不崩 |
| **4c 能用** | 对表 ≥11 对（含边界 (0,0)/(12,12)＋负例 (5,3)/(7,2)/(1000,999)）逐行 MATCH 落日志；桥面 off-contract `Assert_failure` 实证＋native 面实证在卷；期望值由 `Nat.leb` 独立重算交叉对拍；**对表行=能用料证，exit 0 不算数** |
| **4d 好用** | 计时入档：10⁶ 次往返 ns/判定＋单次大判定秒数＋O(首参数) 量级线写入模块文档；热路径 native-only 断言（witness 热路径不含 `_le` 名）；实测超线（无）→无需例外登记；若实现席改用非 leb 载体则重测重登记 |

**Wave2 批级闸**（8 件齐后）：gate1 毒 token／gate4 注释（`--file` 显式过探针件）／
gate6 `--gate --baseline`／gate7 CI 模式全绿；残余账：`grep -n
"NatLe_drop\b\|NatLe_lift\b"`（剥注释）在 8 件中命中=0（除 S01 v2 定义位与
G6 白名单——白名单逐条具名列出）。

### §4.2 Wave3+ = mass 批（bottom-up 拓扑·每批 gates）

- **批次序**：**下游 Require 闭包 353 件**（正典·钉版规范 commit `ca315c0`；本席
  Require 解析 351／直连 333 系交叉参考，以 coqdep 复核为准）按 **bottom-up 拓扑序**（叶先行）分批 ≤80（E949 批帽）；S02 下游
  波（DTPT/DTPT_Entropy 等）殿后。
- **每批动作**：§3 文法批改（改名律＋白名单）→逐件 born-in-place→批闸四件
  （gate1/gate4/gate6/gate7）→E949 闭包重编对账（compiled≤批内件数＋真波新增）。
- **提取级联特别锚**：`DTPT.v:4222-4227` 有 `Separate Extraction … NatLe_drop
  NatLe_lift …` 语句（本席第一手实录）——该件过文法批后**其提取契约面变化**
  （drop 名下 `__`→informative），PR 正文强制披露提取面 delta＋对账新 mli。
- **每批 4a-4d 锚点**：4a 同 Wave2 逐件（批量 gate7 全名普查按模块）；
  4b/4c：每批至少 1 件跑 witness 对表（批代表制，S02 下游批必含 1 件）；
  4d：批代表件计时复查＋文档线抽查。
- **批间**：撕裂愈合对账（本批消费者 `Unable to locate library`/`inconsistent
  assumptions` 红清零才进下批）；停滞件按 §1 红件六桶。

### §4.3 终局 = 全树五门＋coqchk＋CI

1. 全树 build 不动点：build.sh 循环收敛（EXIT=0＋全件 SKIP＋零重编）；
2. coqchk 全树（`-o`，禁 `-silent`）：`Axioms: <none>`＋`Modules were successfully
   checked`＋`COQCHK_ALL_PASS`；
3. **五门**：gate1 毒 token／gate2 Axioms／gate4 注释卫生／gate6 语句面普查
   （--gate --baseline，红在增量=0）／gate7 提取执行（全树普查·增量=0·registry
   三行对账在卷）；
4. CI：#320 模板对齐管线，run success＋`COQCHK_ALL_PASS` 字样；推前闸门四件套
   （runner online／最新 run completed／head_sha==父／本地哨兵全套预演）；
5. **PR 交割**：PR 正文四披露——§11 registry 三行＋消费位证据、提取面 delta
   （`val coq_NatLe_drop : __` 消失→informative；lift_le 契约）、4a-4d 四梯
   证据链接、本蓝图 §6 坑位两起事故（见 §5 K1）。

### §4.4 预算口径
总账「25-40 席/2.5-4 天」旧预算**并入重建役不单列**（用户裁定）；本蓝图新增量=
Wave2 的 registry＋witness 械具（械具已成型于 probe 目录，实现席即取即用）。

---

## §5 施工坑位登记（本席两起自伤＋环境实勘）

- **K1 tracked 根目录提取产物**：worktree 根的 `*.ml/.mli` 中混有 **tracked 历史
  提取产物**（30+ 件，如 `S14_B5BatchBlock.ml`/`upstoptime.ml`）——本席清扫/再
  提取两次误伤（30 `D`＋8 `M`），均 `git restore` 还原（终态 git status 复核=0）。
  **铁律**：①一切清扫/移动前 `git ls-files --error-unmatch` 逐件判 tracked；
  ②一切提取探针 `Set Extraction Output Directory`（或 `-output-directory`）钉入
  `_` 前缀探针目录，禁写 cwd（coqc 默认目录 warning 即红线）；③推送前 diff 面
  断言（§1·J scope 假绿病③）。
- **K2 Notation 别名弃用**：Rocq 9.3 对 `Notation X := t` 缩词形报 deprecation
  （建议 `Abbreviation`）——文法探针中作名字绑定实验可容，**落库件禁用别名绑定
  绕签名**（直接具名）。
- **K3 pilot 撕裂窗**：Wave2 born-in-place 后，未批改的 343 消费件 .vo 与新
  S01.vo 必然撕裂（E963 咬合性）——**pilot 期禁 coqchk_all/全树 build**，批闸
  只跑逐件与批级四门；撕裂归 Wave3 序 heals。
- **K4 并发席共享 worktree**：本席开工时根目录无探针，作业中涌现邻席探针区
  （`attn/_s01v2_probe/` 等）——根目录提取产物互踩风险真实发生；后续席必须
  遵 K1-②钉目录。
- **K5 扫描器闭包缺陷**：`_scan_natle_sites.py` 的 `closure_size=1`（Require 闭包
  计算坏）——批次拓扑**不得**消费该字段；以 coqdep 为准（正典闭包 353·本席独立解析 351 为交叉参考）。

---

## §6 位点 adjudication 输入（裁勘席接口·本席已备第一手）

- 判词一：旧 drop＝**纯证明工具**（类型学排除值位消费；Gen2 正典 drop 侧 1,033 位
  全证明位/Prop 槽·`_census_extlib.json` 全库 drop 调用=0，值体证据仅 euclid:106
  Prop 槽形）→ (b) 注册，值能力由 N1 补齐。
- 判词二：旧 lift＝**证明工具＋提取值面 partial**（Assert_failure 实证）→
  (b) 注册＋partiality 记载，值能力由 N2 接管（total 投影）。
- 判词三：NatLe 载体＝**值级在役**（qpg_engine_sound／sif_enum 签名实证）→
  (a) 不注册，零迁移。
- 全 2,059 位点分类证据面（Gen2 正典）：**钉版规范 commit `ca315c0`**
  （`attn/_natle_site_inventory.md`——含 §一·乙 EXE-VERIFIED 活体表 176/44 逐条、
  附录 A 九面分账/口径小账）＋`attn/_natle_probe/_natle_sites_v3.json`
  （sites 逐位）＋`_natle_probe/_census_extlib.json`（活体实测）＋邻席首尾亲验材料
  `_natle_firstlast_verify.md`（若联络员归档）。
- **口径对账勘误（复核轮 1 升格·Gen2 正典钉版）**：本文早期行文用数（2,086／
  drop 1,048＋lift 1,038／106 文件／闭包 351）系本席 v2 扫描快照，**已全部作废存照**；
  正典＝**Gen2 程序化普查（钉版规范 commit `ca315c0`）**：消费位点 **2,059**
  （drop 1,033＋lift 1,024＋DEF 2）／消费文件 103／下游闭包 353／活体 176 处
  ·44 模块·drop=0（`_census_extlib.json` 程序化实测）；早期 v2 aggregate
  （2,061／1,034＋1,027／103/353·`_natle_sites.json`）、裸词面口径（grep
  1,084＋1,069＝2,153）与上役 Gen1 总账（2,147）均存照禁作验收口径——Wave2
  验收一律以钉版规范 Gen2 普查为唯一口径（数账成分与互抵关系见钉版规范附录 A）。
