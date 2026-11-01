# 有限状态单步目标理论的构造性机器检查统一：RLHF、DPO、PPO 代理目标与 GRPO 组统计量

**英文标题**：A Constructive Machine-Checked Library for Finite-State RLHF/DPO/PPO/GRPO Objective Theory


**作者**：王宝军、夏挽岚（通讯作者，xiawanlan33@163.com）、祖光照、周志农、高雪峰

**Authors**: Baojun Wang, Wanlan Xia, Guangzhao Zu, Zhinong Zhou, Xuefeng Gao. *Corresponding author: Wanlan Xia (xiawanlan33@163.com).*

**Artifact 双轨声明**：本文行号锚与定理编号以 ConstructiveWorld 219 基线为唯一基准；artifact 当前状态为 ConstructiveWorld@39d81aa（246 编译模块、Live_X（实验成果目录）356 个 .v、CI 认证面 246，各波 coqchk 全绿；CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；219 锚服务正文行号与定理定位，当前快照服务认证与复现；正文分层验证口径（81 条 PA@198/206+维持面）不变。版本标识、行号索引、模块清单、构建日志与审计记录见补充材料 S1。

**单一版本对照表**（正文出现的版本数字/标识一次性收拢于此，读者无需多处拼合）：

| 数字/标识 | 指称对象 |
|---|---|
| 198/206 | 主定理/主定义 Print Assumptions 全量 CLEAN 审计的基态快照（分层验证口径的审计面） |
| 219 | 正文行号锚唯一基准（ConstructiveWorld 219 基线；内容锚 SHA-1 见 §9.1.1） |
| 39d81aa | artifact 当前认证态（246 编译模块、CI 认证面 246，各波 coqchk 全绿） |
| 356（Live_X） | artifact 实验成果目录 Live_X 的 .v 文件计数 |


---

## 摘要（Abstract）

本文在 Rocq/Coq 9.0/9.1 中给出 RLHF、DPO、PPO、GRPO 四族对齐算法在有限离散状态空间上的单步目标理论的构造性机器检查统一。全部结果满足零全局公理、零 Admitted、零 Abort。81 条主定理/主定义在基态 198/206 上经 Print Assumptions 批量审计为 CLEAN；其后新增内容以行首禁词零命中、全量编译与 coqchk 内核校验维持，完整重跑范围见补充材料。库的签名迁移工程（将抽象 Id 签名陈述系统迁移到 setoid/req 实例签名）已全部处置（清单见补充材料）；其方法论教训——构造性实数上 Id 陈述的不可实例化、序编码是库级一次性决策——在正文正面陈述（§3.6、§9.5）。代表性结果集中于四族对齐目标理论：在显式步长 KL 接口 `step_kl_eta_bound` 下，策略迭代的向后 KL 几何收缩率为 (1−η)^t；该接口的单步 Real 层 eps 对应物（`real_step_kl_eta_bound_eps` 等）与迭代率的 Real 层逐 eps 镜像（模块层，§10.2 第 1 项 (h)）均已机器检查；GRPO 组统计量与无重复枚举前提不可去反例。采样管道层结果（Top-k/Min-P/KV 驱逐）属姊妹论文正文范围，本文仅在统一视角节延伸引用，不构成四族对齐目标理论主张。本文严格区分机器检查定理、模块层附加证据与开放项；"首次"收窄表述为：据检索，在任意证明助手中覆盖该四族单步目标理论的形式化尚属首次——其中构造性立场（纯构造性 Coq、零全局公理、Set 层信息性证明）为本文独有；该主张的意义主要在构造性立场本身，而非优先权竞争（完整条件见 §2.3）。

---

**Abstract (English)**

We present a constructive, machine-checked unification of single-step objective theory for RLHF, DPO, PPO, and GRPO over finite discrete state spaces in Rocq/Coq 9.0/9.1. All results satisfy zero global axioms, zero Admitted, and zero Abort. The 81 principal theorems/definitions passed a batch Print Assumptions audit, last fully CLEAN at baseline 198/206; items added afterwards are maintained by zero banned-token hits, full compilation, and coqchk kernel checking, and the complete re-run scope is given in the supplementary material. The signature-migration effort (systematically migrating abstract Id-signature statements to setoid/req instance signatures) has been fully dispositioned, with the itemized list in the supplementary material; its methodological lesson — the non-instantiability of Id-statements over constructive reals, and order encoding as a one-time library-level decision — is stated explicitly in the body (§3.6, §9.5). Representative results are concentrated on the four families of alignment objective theory: under the explicit step-size KL interface `step_kl_eta_bound`, policy iteration attains a backward-KL geometric contraction rate of (1−η)^t; the single-step Real-layer eps counterpart of this interface is proved (`real_step_kl_eta_bound_eps` et al.) and the Real-layer eps mirror of the iterative rate is machine-checked at the module layer (§10.2 item 1(h)); and GRPO group-statistic identities together with a machine-checked counterexample showing that the no-duplicate-enumeration premise is irreducible. Sampling-pipeline results (Top-k/Min-P/KV eviction) belong to the body of a companion paper and are only cited in the unified-perspective section; they do not constitute claims of the four-family alignment objective theory. We strictly distinguish machine-checked theorems, module-layer supporting evidence, and open items; the "first" claim is narrowed to: to the best of our retrieval, this is the first formalization in any proof assistant covering these four families of single-step objective theory — the constructive stance (constructive Coq, zero global axioms, Set-layer informational proofs) being unique to this work; the significance of the claim lies primarily in the constructive stance itself rather than in priority competition (full conditions in §2.3).

---

## 1 引言

### 1.1 动机

RLHF（Reinforcement Learning from Human Feedback）、DPO（Direct Preference Optimization）、PPO（Proximal Policy Optimization）和 GRPO（Group Relative Policy Optimization）构成了当前大语言模型对齐的主流算法族。它们的优化理论基础在机器学习文献中已十分成熟：RLHF 的最优解可写成 Boltzmann 形式，DPO 将奖励隐式参数化为策略对数比，PPO 通过裁剪代理目标控制策略更新幅度，GRPO 通过组相对优势降低方差；其中组统计量对组枚举无重复性的依赖在纸笔陈述中通常隐去，本文以机器检查反例定理化该前提的不可去性（§7.2 定理 7.2/7.3）。然而，就 §2.3 的系统检索所及，在纯构造性 Coq（现名 Rocq）形式化的范围内，这些定理的统一机器检查形式化尚不存在；Isabelle/HOL（AFP）与 Lean（mathlib）生态中的相邻工作——MDP 动态规划算法的收敛验证与测度论信息论工具——均不覆盖本文的"对齐目标理论族"，逐条对照与排除见 §2.3。

形式化的价值不仅在于"验证已知结论"。对齐算法的部署场景日益安全关键，而现有纸笔证明存在三类常见漏洞：
1. 分布正性、归一化、KL 有限性等前提被隐式假设；
2. 存在性结论可能依赖排中律；
3. 多个算法族的符号约定和前提不一致，导致跨算法组合时产生隐藏假设冲突。

ConstructiveWorld 项目的目标是在同一逻辑立场（纯构造性、零 Axiom）内，把统计力学、信息论、语言模型与对齐算法统一为单一机器检查库，从而暴露并最小化上述漏洞。

### 1.2 贡献
**术语约定**：CLEAN 指 Print Assumptions 返回 Closed under the global context。假设分三类：全局 Axiom（本文为零）、接口 Variable、Class 字段；正文不用库内任务编号指称数学对象。签名迁移：抽象签名到实例签名的系统化迁移；setoid 实例：以 setoid 相等关系实例化接口；双层并行冻结条目：抽象层陈述与实例层复刻并行承载同一数学内容。

本文贡献分为三层：**C1 构造性基座**：零公理柯西实数（逐点 eps 判定 + sigT 完备性见证）、exp/log 全族与逐 eps 技术（见下「基座三层」与 §3）；**C2 四族单步对齐目标理论**：RLHF 最优性、DPO 隐式奖励恢复、GRPO 组统计量与 NoDup 反例三族目标理论，外加 PPO 裁剪机制的静态结构性质（定位为「结构性质三定理」，不与前三族并列，见下条 5）——其中精确等式与统计恒等类结论多为初等数学（标注），其增量价值在构造性机器检查（前提显式化、零排中律、可提取见证），策略迭代几何收敛率（定理 4.5–4.8，几何收缩率 (1−η)^t）为该层核心定量结果；**C3 基础设施**：setoid 接口族、实例化与签名迁移工程（已全部处置；其方法论教训的正面陈述——构造性实数上 Id 陈述的不可实例化、序编码应于库第 0 天选定——见 §3.6、§9.1 开头与 §9.5）。定义性后承与初等复述另列支撑层，不计入并列贡献；下文「基座三层」为 C1 的展开，「应用层定理」为 C2 的逐族陈述。

**基座三层（第一类贡献的展开）**

- **零公理构造性实数**：自建 `Real` = 有理数 Cauchy 序列 + 逐点 eps 判定（Set 层 `QltT`/`QleT`）+ sigT 打包完备性见证（存在性结论携带可计算见证，§3.1/§9.3）；全库零 `Axiom`、零 `Admitted`。
- **exp/log 构造**：`cauchy_real_exp` 全族（级数构造、正性 `cauchy_real_exp_pos`、等式/序理论、两点凸性 `real_exp_two_point_cvx_eps`）与 log 的正参数构造（`cw_log`），为 Boltzmann/自由能层提供全部分析燃料（§3.1/§3.3）。
- **逐 eps 技术**：Bishop 形态方法学——构造性有序域无三分律，非严格序以逐 eps 余量陈述（`real_le = Or (lt) (req)`），误差以「单点引入 → 常数加权 → 末端完成」账目管理（附录 C.2）；该技术是抽象层定理在实数层获得对应物的系统性工具（§9.2）。

**应用层定理（第二类贡献：基座之上的目标理论演示）**

1. **RLHF 最优性闭合（该条实质为闭式解与唯一性）**：KL 正则化对齐目标的最优策略 π* ∝ π_ref·exp(r/β) 的闭式解（定理 4.1）与唯一性（定理 4.2）（§4）。显式次优间隙恒等式 J* − J(π) == β·KL(π‖π*)（定理 4.3）与近优单调刻画（定理 4.4）不属独立新不等式，按支撑层（见下）处理：定理 4.3 是自由能分解的一次移项重写（附录 B.1 自评），其价值在为间隙单调（定理 4.7）、聚合损失轨道单调（定理 5.10）与能量耗散型论证提供间隙恒等通道；定理 4.4 是「前向 KL 到 π* 不增 ⟹ 目标单调」的支撑性质。
2. **策略迭代精确动力学**：相对熵镜像下降单步 π_{t+1} ∝ π_t^{1−η}·(π*)^η（几何插值形式，§4.3.1）的向后 KL 精确加权递推与显式收缩因子 κ = 1−η（定理 4.5）、间隙显式恒等式（定理 4.6）、间隙单调（定理 4.7）与诚实接口 `step_kl_eta_bound` 下向后 KL 的**真几何率上界 (1−η)^t**（定理 4.8，κ := 1−η、c := 0）。状态一句话：定理 4.8 在诚实接口 `step_kl_eta_bound`（Section Variable）下已证；该接口的单步 Real 层 eps 对应物已在库内证明（`real_step_kl_eta_bound_eps` 等），迭代率 (1−η)^t 的 Real 层逐 eps 镜像（`KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps`）亦已机器检查（模块层，§10.2 第 1 项 (h)）——接口的数学地位、纸笔论证与机器状态的全部细节统一收拢于 §4.3.2。该族把「静态最优性（π* 闭式）」推进为「动态迭代的精确量化」，是全文收敛率内容的核心。
3. **DPO 隐式奖励恢复族 + 审计 = KL 投影（对齐审计的双定理结构，§5）**：隐式奖励精确恢复真实奖励至配分函数基线（定理 5.4）、奖励差分无偏（定理 5.5）、对数比差分等价（定理 5.6）——对齐审计的**测量基座**：DPO 隐式奖励确为真实奖励的仿射像；审计的**作用形式**由 §5.3 定理化：布尔安全过滤器 + 通过集重归一化恰为到通过分布的 KL 投影（`projected_distribution_minimizes_kl`，L95587，附精确分解 `kl_sum_split`）——DPO 恢复定理提供「审什么」的基座，KL 投影定理给出「审计如何作用」的形式；两定理各自独立成立，审计桥为二者的串联使用而非新的联合定理。
4. **统一自由能视角**：RLHF/DPO/PPO/GRPO 共享同一自由能-KL 基座（`rlhf_free_energy_kl`为数学锚点），"统一"有定理支撑而非口号（§8）。

**支撑性质（初等统计与界引理——初等性标注）**：除下列编号条目外，§4 的次优间隙恒等（定理 4.3）与近优单调（定理 4.4）亦归本层——前者是自由能分解的一次移项重写（附录 B.1 自评），后者是「前向 KL 到 π* 不增 ⟹ 目标单调」的支撑性质（见应用层定理 1 的定位说明）；两者均不列入应用层并列贡献。

5. **PPO 裁剪机制的静态结构性质（范围限定：单步 Bandit 设定，非"PPO 算法端到端验证"）**：本章主结果为**三件单侧组合定理（定理 6.8–6.10，§6.3）**：`ppo_is_decomp`/`clip_error_nonneg`/`ppo_clipped_improvement`（已在库内证明，L112398/L112408/L112439）——IS 目标 == 裁剪代理 + clip 误差的无前提精确分解、clip 误差非负、裁剪代理非负 ⟹ 价值改进——「裁剪代理非负蕴含价值改进」是 PPO 裁剪机制安全性的非平凡形式化；其保守性对照面为：非标准形式的静态保守性（定理 6.1，需优势非负前提）与标准形式的无前提保守性（定理 6.7，**定义性后承**——`min_le_l` 的定义性直接推论，与裁剪结构无关，与定理 5.3 同等口径，不计入并列贡献）；另有**未裁剪代理目标**的单调改进条件（定理 6.3/6.4/6.5）。反向界在无界比率下为假（反例），不宣称（§6.3 边界说明），本文不宣称 PPO 算法的端到端验证（§6 范围界定与边界声明一/二/三与此一致）。该章在四族中的实质篇幅相对较小、主结果聚焦为三件单侧分解定理；四族统一的价值在共享构造性基座与前提显式化，不以各族分量篇幅均衡为前提（分量分层汇总清单见 §9.6）。
6. **GRPO 组统计量与前提不可去反例**：组相对优势零均值（定理 7.1）、中心二阶矩恒等式（定理 7.4）与基线方差归约（定理 7.5）——初等代数，其价值在把"减均值降方差"的部署前提（组枚举覆盖、正性、平方非负的构造性边界）显式化；本章主结果为**无重复枚举前提不可去性的机器检查反例（定理 7.2/7.3）**：双副本枚举下 indicator 求和 == 2 ≠ 1、常数奖励总计 == 2c ≠ c——均匀均值解读在无 `NoDup` 前提时失效且该失效不可去已定理化，这是 GRPO 章区别于教科书推演的实质内容、也是形式化"暴露隐藏假设"价值的直接体现（§7.2）。
7. **Real 层逐 eps 复刻与界引理**：部分核心定理在具体柯西实数层的 eps 化版本（定理 4.9、5.8、5.9、5.11 族、6.6、7.6——即 Real 层逐 eps 复刻覆盖的精确清单，见 §9.2；其余如唯一性 4.2、间隙 4.3/4.4、迭代族 4.5–4.8/5.10、GRPO 中心二阶矩/方差族 7.4/7.5、DPO 相对精确 5.5/5.6 暂无 Real 版），承载抽象接口定理的具体数学内容——抽象定理经 setoid 实例的直接消费已随签名迁移主体闭合（例外：64 件冻结双层件，见 §9.1.1 与 §10.2 第 1 项），本条的 Real 层逐 eps 复刻路径与之并存。

**基础设施（Set 层桥梁与实例化）**

8. **统一形式化基座**：Cauchy 实数、Boltzmann 分布、自由能、KL 散度[32]的构造性定理化与 softmax/Gibbs 等价性；Set 层 `And`/`sigT` 信息性证明与可提取 OCaml 路线（§3）。
9. **构造性纪律与实例化**：全库零 `Axiom`、零 `Admitted`（即无任何未闭合证明；审计口径含小写 `admitted`），仅依赖 Coq stdlib（验证面口径在此限定一句：`Print Assumptions` 批量审计 81 条主定理/主定义最近一次全量 CLEAN 复核于基态 198/206，其后新增内容以行首禁词零命中、编译通过与内核校验维持，未整体重跑——完整口径见 §9.1.1 与附录 D）；接口假设显式分类（§3.4、§9.1），Setoid 系接口实例字段实值化（§9.1.1）。抽象定理签名向 setoid 实例的迁移已分五批推进并主体闭合（迁移总清单 734 件中 670 件已交付，余 64 件为 (d) 冻结双层并行条目——逐项冻结理由均有记录，无遗留项；该工程的教训定位见 §9.1 开头与 §9.5）——其工作量与摩擦点分析及迁移完成后的可用性影响见 §9.1.1「Setoid 签名迁移的状态与影响」段与 §10.2 第 1 项。

分层同时回答"形式化一段易证的数学有什么用"：DPO 恢复定理（5.4/5.5）是对齐审计（隐式奖励 = 真实奖励的仿射像）的机器检查依据；PPO 保守性是裁剪安全性的形式化；GRPO 统计量与界引理的价值在前提显式化——论文对支撑层的初等性标注（§7.2 术语说明、§4.3.1 定理 4.8 定位段），不把高中代数与核心定理并列为同层贡献。

**表 1：定理状态总表（定理 × 库内标识符 × 状态 × 条件性前提）**。表 1 按状态（**已证**/**开放**两级）、层级（抽象层/Real 层/反例，行内标注）、条件（显式前提/接口假设，记入条件性前提列）三列口径登记；"已证"不区分是否带显式前件，带前件者在条件性前提列注明。本表所列各行均为已证级；各定理的开放面集中管理如下——Real 层逐 eps 复刻的覆盖清单与逐族阻碍分析见 §9.2，签名迁移与冻结双层件的状态见 §9.1.1，行号锚与逐字陈述见附录 A（以 §9.1.1 登记的 219 基线为唯一行号基准）。两件定义性后承（定理 5.3、6.7）不入本表，见 §5.2 与 §6.2 的定义备注。

| 定理 | 库内标识符 | 状态 | 条件性前提（显式前件/诚实接口） |
|---|---|---|---|
| 4.1 | `rlhf_optimal` | 已证 | 归一化+逐点正、`beta_pos`/`Z_align_pos` |
| 4.2 | `rlhf_optimal_unique` | 已证 | 两策略归一化且正 |
| 4.3 | `rlhf_suboptimality_gap` | 已证 | 前向 KL 方向（§4.3 告示） |
| 4.4 | `rlhf_policy_improvement` | 已证 | 前向 KL 序前提 |
| 4.5 | `policy_iter_backward_kl_iter_le` | 已证 | `eta_pos`/`eta_le_one`、π_t 逐点正 |
| 4.6 | `policy_iter_gap_diff` | 已证 | 同迭代族前提 |
| 4.7 | `policy_iter_gap_mono` | 已证 | 同迭代族前提 |
| 4.8 | `policy_iter_kl_geom_iter` | 已证 | 诚实接口 `step_kl_eta_bound`（显式前件）；0 < η ≤ 1 |
| 4.9 | `real_rlhf_optimal_eps` | 已证（Real 层） | 诚实接口 `real_kl_decomp_full` 等（零公理） |
| 5.1 | `dpo_loss_at_pi_star` | 已证 | π* 闭式前提 |
| 5.2 | `dpo_optimal` | 已证 | 同 4.1 |
| 5.4 | `dpo_reward_recovers_up_to_baseline` | 已证 | π* 闭式 |
| 5.5 | `dpo_reward_relative_exact` | 已证 | 基线消去 |
| 5.6 | `dpo_reward_diff_is_log_ratio_diff` | 已证 | 同 5.4 |
| 5.7 | `dpo_total_loss_monotone` | 已证 | 逐对损失逐项不增（fold 泛单调；命名注 §5.2） |
| 5.8 | `real_dpo_loss_pi_star_bounded_both` | 已证（Real 层） | 前提 `r_l < r_w` |
| 5.9 | `real_dpo_reward_recovers_up_to_baseline` | 已证（Real 层） | — |
| 5.10 | `dpo_loss_iter_step_le`/`_mono` | 已证 | 迭代族前提 |
| 5.11 族 | `real_dpo_logit` 族 | 已证（Real 层） | 各自前提 |
| §5.3 投影主定理 | `projected_distribution_minimizes_kl` | 已证 | `Hq_fail`/`HlogZ` 显式前件 |
| §5.3 精确分解 | `kl_sum_split` | 已证 | 同上 |
| 6.1 | `ppo_conservative` | 已证 | `advantage_nonneg` + `pi_old_pos` |
| 6.2 | `exact_improvement_identity` | 已证 | 无（恒等式） |
| 6.3 | `ppo_monotonic_improvement` | 已证 | 代理优势非负 |
| 6.4 | `kl_penalty_sufficient` | 已证 | `KL ≤ eps`、`E ≥ β·eps` |
| 6.5 | `ppo_surrogate_raw_is_value_improvement` | 已证 | 归一化 + 正性 |
| 6.6 | `real_ppo_conservative_eps` | 已证（Real 层） | 诚实接口 `real_min_le_l_eps` 等 |
| 6.8 | `ppo_is_decomp` | 已证 | 无前提（恒等式） |
| 6.9 | `clip_error_nonneg` | 已证 | 无前提 |
| 6.10 | `ppo_clipped_improvement` | 已证 | 裁剪代理非负 |
| 7.1 | `grpo_advantage_zero_mean` | 已证 | `group_cover`、`group_size_pos` |
| 7.2 | `counter_ex_indicator_sum_two` | 已证（反例） | 双副本枚举（覆盖成立、`NoDup` 缺失） |
| 7.3 | `counter_ex_reward_sum_two_c` | 已证（反例） | 同上 |
| 7.4 | `grpo_variance_identity` | 已证 | 组枚举覆盖 |
| 7.5 | `group_variance_le_raw_second_moment` | 已证 | 诚实接口 `square_nonneg` |
| 7.6 | `real_grpo_advantage_zero_mean` | 已证（Real 层） | — |
| NoDup 均匀均值三件 | `grpo_count_one`/`grpo_indicator_sum_one`/`grpo_uniform_mass` | 已证 | 覆盖 + 无重复枚举 |
| σ 见证 | `real_sigma_witness` | 已证 | `Var > 0` 证书 |


### 1.3 论文结构

§2 介绍相关工作；§3 描述构造性基座；§4–§7 分别展开四个算法族；§8 给出统一视角；§9 讨论边界与局限；§10 总结并展望未来。

**记法与术语约定（首现集中定义）**：
- **`Id`**：Leibniz 命题相等（Coq 的 `eq`）；**`req`**：setoid 等价（本库实数上的规范相等关系 `real_eq`，非 Leibniz 等式——柯西实数的相等须以商/等价关系表述）。
- **Set 层**：Coq 的信息性证明层（数据与计算见证所在层，可提取为可执行 OCaml）；**Prop 层**：命题层（证明对象在提取时被擦除）。本库的存在性见证一律置于 Set 层（§9.1.1）。
- **诚实接口**：显式声明为 Section 前件的未消解假设（标准术语对应 explicit premise / undischarged hypothesis）；其 A/B/C 三分类见 §3.4，消解状态三分类表见 §9.6。
- **Real 层逐 eps 复刻**：把抽象层定理的结论以逐 eps 余量形态在柯西实数层直接证明的定理件；同族多件合称**复刻簇**。
- **模块件/追加层**：以独立模块形态交付、经独立验证（禁词扫描、编译、内核校验）的定理件；正文定理的陈述与证明不消费它们（§9.1 信用结构说明）。**存档件**：未进入主构建入口的独立验证形态（引用时须注明形态归属）。
- **冻结双层件**：定理级签名未迁移的件——其数学内容由 Id 层陈述与 Real 层逐 eps 复刻两条路径并行承载（§9.1.1、§9.5）。
- **装配**：由既有已证引理按组合路线组装、无新分析机器的证明。
- **eps**：误差余量参数（正实数）；**Bishop 形序**：`∀eps>0, x < y + eps` 型非严格序谓词（§9.4 例二）。
- **行号锚**：本文正文 §1–§8 的行号引用已替换为定理/引理标识符；行号以 §9.1.1 登记的 219 基线为唯一基准，映射表见附录 A（含补充锚表）。

---

## 2 相关工作

### 2.1 机器学习对齐理论

RLHF 的 KL 正则化最优解 π* ∝ π_ref·exp(r/β) 源自相对熵策略搜索（Peters et al. [1]）与线性可解 MDP（Todorov [2]）；RLHF 本身——以人类偏好训练奖励模型的研究路线——的开山文献为 Christiano et al. (2017) [21]，对人类反馈学习的通用理论分析（含 KL 正则化目标下奖励估计与直接偏好学习的刻画）见 Azar et al. (2023) [25]，其工程实践锚点为 InstructGPT（Ouyang et al., 2022 [26]）——本文 §4 的 RLHF 目标理论沿此谱系，差异在将其置于构造性机器检查之下并显式化全部前提。DPO 通过隐式奖励 r(s)=β(log π(s)−log π_ref(s)) 绕过显式奖励建模（Rafailov et al., 2023 [4]）。PPO 的裁剪目标与单调改进条件见 Schulman et al. (2017) [3]：其中单调改进条件的理论源头为保守策略迭代 CPI（Kakade & Langford, 2002 [22]），其 CPI/πPI 分析是本文 §6 改进条件定理族（定理 6.3–6.5）的直接前身；PPO 理论证明的实际所在为信赖域策略优化 TRPO（Schulman et al., 2015 [23]）。GRPO 的组相对优势与二阶矩性质见 DeepSeek-AI (2024) [5]。

### 2.2 形式化工作

- **C-CoRN / NuPRL** [16][17]：构造性分析学的先驱，但规模与主题均未触及 ML 对齐。
- **Bishop & Bridges 1985** [24]：*Constructive Analysis*（Springer），构造性分析的方法论出处——本文「逐 eps 方法」「Bishop 形态」（非严格序以逐 eps 余量陈述、误差以 eps/2 簿记管理，§3.1、§9.3）承袭该书的经典路线；本书为文本出处，无机器形式化，亦不涉及 ML 对齐。
- **mathlib / Lean**：分析、测度、信息论覆盖面广，但基于经典逻辑，与本库的构造性立场不同。
- **coq-proba / Infotheo**（Affeldt 等 [8]）：离散概率、KL、互信息、AEP 的形式化，但未涉及 RLHF / DPO / PPO / GRPO。
- **构造性概率论一线**：coq-proba 的 monoid 概率框架 [8] 即在构造性逻辑内组织离散概率；系统性的构造性概率论重构（Bishop 型概率论、双否定/Glivenko 式概率逻辑一线）与本库的 LPO 规避机制（弱三分、逐 eps 余量，§9.4）同向，但对象为概率论自身而非对齐目标理论。
- **神经网络安全性质形式化**（如 CoqNNet、NeuralNetCert）：聚焦鲁棒性、可验证控制器，而非对齐算法的优化理论。
- **CompCert**（Leroy et al. [29]）：Coq/Rocq 生态中经形式化验证的 C 编译器——大型验证工程按多 pass 模块化架构组织的代表性先例（本文模块化维护形态的参照，见附录 D.9）；与本文主题（对齐目标理论）不同域，不影响 §2.3 的 scoped claim。

据 §2.3 系统检索与逐条排除，本文为首个（据检索）在任意证明助手中覆盖 RLHF/DPO/PPO/GRPO 四族单步目标理论的形式化——其中构造性立场（纯构造性 Coq、零全局公理、Set 层信息性证明与可提取 OCaml）为本文独有；该 claim 的意义主要在构造性立场本身，非优先权竞争；"首次"不延伸至采样管道层、连续状态空间或神经网络参数化。**与现有形式化工作的对比**（“—”表示不涉及）：

| 工作 | 逻辑立场 | 实数基座 | 状态空间 | 期望类型 | 覆盖内容 | 对齐目标理论 |
|---|---|---|---|---|---|---|
| Infotheo / coq-proba | 经典 | 有理数 / 离散 | 有限离散 | 离散和 | KL、互信息、AEP；不含对齐算法 | 无（信息论工具层） |
| C-CoRN / NuPRL | 构造性 | 构造性实数 | 一般 | — | 分析学基础；不含对齐算法 | 无（分析基础层） |
| mathlib / Lean | 经典 | 经典实数 | 一般（测度空间） | 测度论积分 | 信息论工具（KL 散度 `klDiv`、Gibbs 不等式、测度指数倾斜）；不含对齐目标理论 | 无（`Tilted`/`klDiv` 已覆盖 Boltzmann 权重与几何插值结构，但定位为分析工具，未进对齐目标理论——本工作增值在「分析工具→算法优化理论」的垂直贯通） |
| CoqNNet / NeuralNetCert | 经典 | 经典实数 | 连续 | 积分 | 神经网络鲁棒性；非对齐 | 无（非优化理论） |
| AFP `Markov_Models`（Hölzl & Nipkow 2012） | 经典（HOL） | 经典实数 | 有限/可数 | 轨迹 pmf/测度 | Markov 链/MDP、pCTL 模型检验、可达性；不含一般奖励优化准则与对齐目标理论 | 无（轨迹性质与模型检验） |
| AFP `MDP-Rewards` / `MDP-Algorithms`（Schäffeler & Abdulaziz 2021） | 经典（HOL） | 经典实数 | 有限 | 折扣期望回报（轨迹） | Bellman 算子最优性方程、值迭代/策略迭代（含修正/GS 加速）收敛到最优策略；无 KL 正则化等目标理论 | 无 KL 正则化最优性/隐式奖励恢复/裁剪代理保守性（折扣回报动态规划准则，非本工作目标理论族） |
| Chevallier & Fleuriot 2021（Isabelle/HOL） | 经典（HOL） | 经典实数 | 有限 | 折扣期望回报（轨迹） | 有限 MDP 基础：Bellman 方程、ε-最优值迭代、最优策略迭代；无对齐目标理论 | 无 KL 正则化最优性/隐式奖励恢复/裁剪代理保守性（同左） |
| 本文 | 构造性、零 Axiom | Cauchy 实数（Setoid 实例） | 有限离散 | 全状态精确和 | RLHF 最优性、DPO 隐式奖励恢复、PPO 裁剪上界、GRPO 组统计量 | 有：KL 正则化最优性/唯一性（§4）、隐式奖励恢复（§5）、裁剪代理保守性与改进条件（§6）、组统计量（§7） |

**注（对齐目标理论列）**：本列标注各条目是否形式化 RLHF/DPO/PPO/GRPO 的**目标理论**（KL 正则化最优性、隐式奖励恢复、裁剪代理保守性、组相对优势统计量）。mathlib 的 `Tilted`（测度指数倾斜）与 `klDiv` 已覆盖本工作所用 Boltzmann 权重/几何插值结构的分析工具层面（§2.3(b) 详述），但未进入对齐算法目标理论；本工作的增值恰在把该类分析工具垂直贯通为算法优化理论（§4–§7），而非停留于工具本身。

**mathlib 行框架差异补注**：mathlib 的 `Tilted`/`klDiv` 工作于**一般测度论框架**——`klDiv` 以 Lebesgue 积分定义、取值于 ℝ≥0∞，需管理绝对连续性与可积性；本库的对齐目标理论限定于**有限离散状态空间上的全状态精确和**（`sum_over_S`，Set 层逐点精确求和，无测度论积分与可积性机制）。这一框架差异（测度论积分 vs 全状态精确和）恰是本库无需重复测度论工具层、而在有限离散精确和框架内垂直贯通对齐目标理论（§4–§7）的原因，也是其 scoped claim（§2.3）成立的范围依据。就分析工具层面的数学内容而言，本库的 KL/倾斜工具与 mathlib 的 `klDiv`/`Tilted` 的关系可概括为：同一数学内容在更强逻辑约束下的重形式化（可证性形态之差，非数学内容之差）——读者不应由本表推得本库在分析工具层面的数学创新性。

**逻辑立场列注**：表中「逻辑立场」列标注各工作所用逻辑：本库与 C-CoRN/NuPRL 为**构造性**（不依赖排中律与三分律），mathlib / Infotheo / AFP 条目为**经典**（可自由使用排中律/选择公理）。该列差异不是口号而是可观察的定理形态差异：经典库可陈述精确序结论（如 `min(x,y) ≤ x` 无余量），构造性编码须把序关系以逐 eps 余量陈述并把前提显式化、给存在性结论以构造见证（§3.1、§9.4 实例、§9.1.1）——本库与 mathlib 的核心差异正在于此；本库与 C-CoRN 虽同为构造性立场，但主题不同（C-CoRN 为分析学基础、本库为对齐算法优化理论，见「覆盖内容」列），差异不在逻辑立场而在主题与目标理论覆盖。

**本文不覆盖的方面（与现有工作的互补）**：本文不做一般测度论积分框架（mathlib 的 `klDiv`/`Tilted` [14] 覆盖绝对连续性与可积性机制）、不做连续状态/动作空间与轨迹级 MDP（AFP `Markov_Models` [10] 与 `MDP-Algorithms` [12] 覆盖轨迹 pmf 与折扣回报算法验证）、不做神经网络参数化的鲁棒性验证、不做样本复杂度与泛化界（该方向已有机器检查工作：PAC 可学习性[37]、随机逼近[36]、一阶优化算法收敛率的 Lean 4 形式化[35]）——相应能力由所引工作承载，本文在其覆盖之外建立有限离散精确和框架下的对齐目标理论族（§9.2 为完整边界清单）。

### 2.3 Isabelle/HOL 与 Lean 生态相邻工作的系统检索与排除

我们按三个主题对 Isabelle AFP、Lean mathlib 与 Coq/Rocq 生态作了系统检索（检索截至 2026-09-14；库认证面更新至 187 后未发现冲突条目；条目与 URL 见参考文献 [9]–[15]），逐一说明其与本文的关系：

**检索协议**：DBLP 与 Google Scholar 的检索式为算法族关键词（`RLHF`、`DPO`、`PPO`、`GRPO`、`relative entropy policy search`、`mirror descent policy iteration`）与形式化关键词（`Coq`、`Rocq`、`Isabelle/HOL`、`Lean`、`machine-checked`、`formalization`）的布尔组合；GitHub 代码检索以 `Coq`/`Rocq` 语言过滤叠加算法族关键词、逐一核对命中仓库的定理覆盖面；mathlib4 文档站与 AFP 全目按主题（信息论、Markov 决策过程、概率）浏览并核对相邻条目。各平台检索与逐条排除的完成时点为 2026-09。

**（a）MDP 动态规划：值迭代/策略迭代的机器检查（Isabelle AFP 与非 AFP 条目）。**

- `Markov_Models`（Hölzl & Nipkow，AFP 2012 [10]；期刊版 Hölzl 2016 [9]）：离散时间 Markov 链与有限 MDP、pCTL 模型检验与可达性分析；未引入一般奖励与优化准则，主题是轨迹性质。
- `MDP-Rewards`（Schäffeler & Abdulaziz，AFP 2021 [11]）：在 Hölzl 的 MDP 之上加入奖励，验证无限视界折扣总回报准则下 Bellman 算子的迭代规则、最优性方程与最优平稳确定策略的存在性。
- `MDP-Algorithms`（Schäffeler & Abdulaziz，AFP 2021 [12]）：把 Bellman 算子导出为可执行的值迭代、策略迭代及其 Gauss-Seidel/修正策略迭代（MPI）加速版，在有限 MDP 上验证其收敛到最优解（覆盖 Puterman 第 6 章），并附带代码导出。
- Chevallier & Fleuriot（arXiv:2112.05996，2021 [13]）：在 Isabelle/HOL 中自建有限 MDP + 奖励模型，从第一性原理导出 Bellman 方程，证明折扣因子 < 1 时普遍最优策略存在，并证明值迭代/策略迭代在有限时间内分别给出 ε-最优与最优策略。
- CertRL（Vajjha et al.，CPP 2021 [30]）：在 Coq 中形式化有限状态 MDP 的值迭代与策略迭代收敛证明（折扣无限视界设定下的渐近收敛分析）——Coq 生态中与本文主题最相邻的强化学习形式化。二者的区隔在优化范式与目标理论：CertRL 的收敛对象为折扣 Bellman 动态规划范式下的值/策略迭代算子，本文对象为 KL 正则化目标理论族（闭式最优性、隐式奖励恢复、裁剪代理保守性、组统计量）与相对熵镜像下降的几何收缩（KL 镜像下降范式）；其定理族与本文 §4–§7 的目标理论不重叠，不触及本节末 scoped 主张的四条件合取。

这些条目与本文 §4.3.1 主题相邻，但验证对象是**轨迹级动态规划算法**（折扣期望回报的 Bellman 方程/最优性/算法收敛），而非 RLHF 的 KL 正则化最优性（闭式 π* 与唯一性）、DPO 的隐式奖励恢复、PPO 裁剪代理目标的保守性、GRPO 组统计量——即本文 §4–§7 的"对齐目标理论族"。

**（b）信息论与指数族工具（Lean mathlib）。**

- `Mathlib.InformationTheory.KullbackLeibler` [14]（Mathlib 概率/熵/KL 形式化的权威记述见[38]）：在一般测度上定义 KL 散度 `klDiv`（取值于 ℝ≥0∞），含 Gibbs 不等式（KL ≥ 0，`integral_llr_add_sub_measure_univ_nonneg`）与"KL = 0 ⟺ 测度相等"（`klDiv_eq_zero_iff`）；`Mathlib.MeasureTheory.Measure.Tilted` 形式化测度的指数倾斜（`μ_tilted ∝ e^{f}·μ`）——与本文的 Boltzmann 权重/几何插值结构数学上同源。其定位于一般测度空间上的分析工具（经典逻辑、需管理绝对连续性与可积性），未进入有限状态对齐算法目标理论；本库与之的关系为同一数学内容在更强逻辑约束下的重形式化（可证性形态之差，非数学内容之差）。

**（c）构造性实数/分析（Coq/Rocq 生态）。**

C-CoRN、NuPRL 与 O'Connor 2008（见 §9.3）之外，Coq 8.12 起标准库随附构造性 Cauchy 实数模块 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` [15]（**Rocq 9.1 实测存留**：`Require Import Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 通过），其收敛/完备性路线与本库 Set 层自建 Cauchy 实数并行；构造性分析方向上未见覆盖对齐算法目标理论的条目。

**（d）基座对照：为何自建柯西实数（回答"基座为何不复用"）。** 上文 (c) 登记了 stdlib `ConstructiveCauchyReals` 与 C-CoRN 的存在；本段正面回答"自建的必要增量何在"。下表按字段对照三条构造性实数路线（行为维度，列为路线）：

| 维度 | 本库 `Real` | stdlib `ConstructiveCauchyReals` [15] | C-CoRN [16] |
|---|---|---|---|
| 实数表示 | 有理数 Cauchy 序列（`Q` 基） | 有理数 Cauchy 序列（`Q` 基） | C1 集 + 代数完备化（§9.3） |
| 相等关系 | setoid `real_eq` + Set 层逐点 eps 判定（`QltT`/`QleT`，Set 值） | setoid（Prop 层陈述为主） | setoid |
| 序形态 | `real_le = Or (lt) (req)` 构造性析取 + Bishop 形逐 eps 谓词 `real_le_b`（§9.4 例二） | 构造性序（严格序 `CRlt` 为 Set 值线序；非严格序 `CRle` 为 `CRlt y x -> False` 的 Prop 否定形） | 构造性序 |
| exp/log 全族 | 库内自建：级数构造 `cauchy_real_exp`、正性、等式/序理论、两点凸性（§3.1） | **不含**（模块提供域结构与极限/完备性，未附超越函数构造） | 有分析基建，但未以本文所需字段形态（log 带正性前提的 setoid 接口族，§3.5）供给 |
| 完备性见证 | sigT 打包（存在性结论携带可计算见证，§3.1） | sigT 见证形（`CR_complete` 携带极限见证） | Prop 层为主 |
| 提取路线 | 全库 Set 层，信息性证明可提取 OCaml（主要定理链零类型级 `__`，附录 D 第 3 项） | 未按 Set 层信息性提取组织 | 需跨生态适配 |
| 依赖面 | 仅 Coq stdlib，单文件 SHA-1 内容锚定（§9.1.1） | stdlib 内建 | 第三方生态（mathcomp 系） |

三条路线的**分析学内容同构**（同为构造性 Cauchy 实数，§9.3）；自建的决定性动机不是数学必要性，而是两点工程必要性：其一，**Set 层信息性提取路线**——本文的存在性结论以 sigT 见证给出并可提取为可执行 OCaml（§9.1.1），这要求非严格序判定取 Set 值（`QltT`/`QleT`）而非 Prop 值，stdlib 模块与 C-CoRN 均未按此组织；其二，**接口签名控制**——本文的对齐目标理论消费一族特定形态的字段（log 族带正性前提的 setoid 接口、逐 eps 度量字段，§3.5），stdlib 缺 exp/log 全族，C-CoRN 的字段形态与本文接口不同构。若接受 Prop 层陈述与第三方依赖，基于 stdlib 模块补全 exp/log 或复用 C-CoRN 亦是可行路线；本文选择按统一接口族自建以同时满足上述两点，并承认这属于表示工程与消费接口层面的决策，而非分析学内容之差（与 §9.3 技术差异段一致）。

**量化对账**：为使上表的「不含/缺口」判断可检验，此处给出件数级盘点。量化口径为**声明级件数的 grep/wc 实测**（以 219 基线归档快照 ConstructiveWorld.v 为对象，窗口按命名 Section/Module 划定，逐窗可复现；不含工时与难度估算）。本库自建面五窗实测：Cauchy 实数构造与序判定（`Real` 的 sigT 定义、`real_le` 的 Or 编码、`QltT`/`QleT` 的 Set 值逐点判定）**64 件**；完备性与实层极限技术（`real_lim` 定义、`real_lim_unique`、`real_cauchy_complete` 及极限代数）**101 件**；exp 全族（Q 层级数部分和与缺环、Real 层级数收敛、正性/可加性/良定义性/保序与 `cauchy_real_exp_plus`）**366 件**；log 全族（值域二分构造 `cw_log`、互逆、单调与接口字段材料）**165 件**；接口族与实例回填（Id 系接口 Class、setoid 接口模块、三个实例）**97 件**——**合计 793 件**。该口径与 §9.1.1 件数口径注的「基座 Id 系 62 区段 683 件」（签名迁移普查口径，仅计 Id 系迁移核对范围）系两个口径，不可相加比较。

stdlib 一侧（[15]，本地实取，Rocq 9.1 与 [15] 的标准库文档核对登记同版本口径）：`Stdlib.Reals.Cauchy` 族 7 文件合计 4,228 行（主文件 1,001 行、91 个行首声明），Abstract 层另备域结构（环运算、偏逆 `CRinv`、Set 值严格序 `CRlt`、min/max/abs、自然数次幂）与极限完备性（`CR_cv`/`CR_cauchy`/`CR_complete`，见证实为 sigT 形）；**exp/log 全族零定义**（全目录按 `CRexp`/`CRlog` 与 exp/log 定义式检索零命中）。欲在该基座上达到本库接口面，件类缺口清单为五类：① exp 全族构造（级数定义、正性、可加性、良定义性、保序）；② log 全族（构造、正参数前提接口形态、互逆、单调）；③ Set 值非严格序判定（stdlib 的 `le` 为 Prop 否定形而非 `Or (lt) (req)` 的 Set 值析取与逐点判定谓词形态）；④ log 带正性前提的 setoid 接口族（§3.5 两系接口的字段构成与实例回填）；⑤ 逐 eps 度量字段接口化（`metric` 逐 eps 族与 `lim`/`lim_unique`/`cauchy_complete` 字段形）。以本库同面实测为量级参照：①② 同面为本库 exp/log 两族合计 531 件（含本库 Q 层底座部分，stdlib 的 Q 层设施已具相邻基础，故仅为同面规模参照读数而非缺口件数的估算）；④⑤ 同面为接口组织面 97 件。stdlib 侧各件类的实际件数须先在该基座上完成实际构造方可断言，本文不作估算；此类基座对照属独立实验范畴。

**C-CoRN 不采用的工程理由**（「适配不可行」的准确形态：适配等于全接口面重接线，本文不采用）：其一，**字段形态不同构**——本库对齐目标理论消费的接口族（log 族带正性前提的 setoid 接口、逐 eps 度量字段、Set 层 sigT 见证）与 C-CoRN 的 C1 集/函数空间加代数完备化路线在字段形态上不同构（§9.3 技术差异段）；其二，**完备化路线不同**——代数完备化与有理数 Cauchy 序列加逐点 eps 判定在完备性见证、序判定与提取行为上均不同形，适配后须按本库 Set 层组织重跑验证链（信息性提取、假设闭包检查、内核校验）；其三，**依赖面改变**——本库仅依赖 Coq 标准库（上表「依赖面」行），引入 C-CoRN 即引入第三方生态依赖，与零外部依赖的内容锚定维护形态（§9.1.1、附录 D.9）冲突。

**排除结论与 scoped 主张。** 上述检索未发现同时满足以下四点的条目：(i) 对齐算法（RLHF/DPO/PPO/GRPO）单步目标理论；(ii) KL 正则化最优性/隐式奖励恢复/裁剪代理保守性/组统计量这一族定理；(iii) 纯构造性逻辑（零 Axiom）；(iv) Set 层 `sigT` 信息性证明与可提取 OCaml 路线。故本文的"首次"应读作有条件的 scoped claim：**据我们所检索，在任意证明助手中同时覆盖上述四族目标理论的形式化为首次，其中纯构造性立场（零 Axiom、Set 层信息性证明、可提取 OCaml）为本文独有**；该 claim 的意义主要在构造性立场本身，非优先权竞争——四条件合取使"首次"近乎按构造成立，其价值主张落在构造性形式化所暴露的前提显式化与构造性边界（§9.4），而非与既有工作的优先权排序。库形态为单文件基座加追加模块伴生件，「单一文件」不作为本 claim 的构成条件（该形态选择与模块化路线的权衡见 §9.1.1 与附录 D.9）。同一范围内的相邻工作在 (a)–(c) 中逐一对照与排除（汇总表见 §2.2）。

---

## 3 构造性基座与库设计

### 3.1 Cauchy 实数与等式类型

本库不引入经典实数公理，而是从有理数 Cauchy 序列构造实数 `Real`，并显式使用 setoid 等式 `Id`（Leibniz 等价的构造性版本）以及可计算序 `le`/`lt`。所有存在性结论均要求给出构造性见证；例如 `inv_pos` 要求输入正性证明，避免非构造性的"x>0 或 x≤0"判断。

### 3.2 概率分布与信息论

有限状态空间 `S` 上的分布由函数 `S -> R` 表示，配合归一化 `normalized` 与正性 `positive_dist` 假设。核心定义包括：
- `sum_over_S`：有限求和算子。
- `relative_entropy p q`：KL 散度 `Σ p(s)·(log p(s) − log q(s))`。
- `boltzmann_dist energy beta`：Boltzmann 分布 `exp(−energy(s)/β) / Z`。

### 3.3 自由能与 Boltzmann 最小化

对齐目标被嵌入自由能框架：

```
Definition free_energy (energy : S -> R) (beta : R) (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (energy s))
  + mult beta (sum_over_S (fun s => mult (p s) (log (p s)))).
```

库内已证：
- `free_energy_kl_decomp`：`F[p] = F[p_b] + β·KL(p‖p_b)`。
- `gibbs_inequality`：`KL(p‖q) ≥ 0`。
- `min_free_energy_is_boltzmann`：Boltzmann 分布是自由能全局最小点。

这些结果构成 RLHF 与 DPO 最优性证明的共享基础。

**req 签名版与「无条件」的参照系（签名迁移迁移第二阶段交付）**：`min_free_energy_is_boltzmann` 的 setoid（req 系）签名版 `req_min_free_energy_is_boltzmann` 已交付（模块 `UpReqDist.v`；`Print Assumptions` Closed）。其类型签名要旨如下（Section 前提位从略，见下句说明），作为 §4.3/§9.1.1「req 无条件形态」一词的核验参照——**「无条件」的准确含义是零全局公理（Closed）且分布前提（逐点正性 `positive_dist`、归一化 `normalized`）以显式 forall 前件形态内嵌于语句，并非分布前提的消去**；须补充（修订对齐）：该定理处于携带 SumOver 对接面（求和算子 `sumf` 与 `sum_le`/`sum_zero_nonneg` 等六条 Section 假设）与自由能常数位（`D`/`D_pos`/`Z`/`Z_pos`）的 Section 内，这些前提随 Section 泛化进入定理显式前件——「Closed」指零公理，非零前提；其精确 `le` 序结论因此是**接口假设相对的**，与「无前提 Real 层 Or 形不可达」的构造性边界（§9.4 例二）分层并存，消解见 §3.6 末段：

```coq
Theorem req_min_free_energy_is_boltzmann :
  forall (p : S -> R) (Hp : positive_dist p), normalized p ->
    le (free_energy boltzmann_dist req_boltzmann_positive) (free_energy p Hp).
```

即序结论为精确 `le` 形（§9.1.1 (c) 的精确构造性序），证明链消费 `req_free_energy_kl_decomp` + `req_gibbs_inequality` + `req_boltzmann_normalized`（均为迁移第二阶段交付的 req 形；`req_gibbs_inequality` 的证明消费 SumOver 单调假设 `sum_le`，见上句与 §3.6 的前提位说明）。`UpReqDist` 91 件与 `UpReqTempEntropy` 14 件的对账表位置：`UpReqDist.v` 文件头覆盖对账（req 件名 → Id 原件 @ 219 基线行号，逐条至文件尾合计行「89 Qed + 2 Defined = 91 证明件」）与 `UpReqTempEntropy.v` 定理清单（要点摘录及各簇语义保真度三分类见附录 D.8）。


### 3.4 诚实接口纪律

库内所有未证假设均显式声明为 `Variable` 并分类管理：A 类（接口字段）、B 类（Section 局部假设）、C 类（已证定理）。本文中引用的定理均来自 C 类；仍在使用的假设将在 §9 显式列出。

### 3.5 实数接口族与实例化

本库不以实数公理为起点，而把实数抽象为满足一组代数、序与完备性条件的接口。接口族按相等谓词分为两系：以命题相等 `Id` 表述的 `RealInterface`及其增强版`RealInterfaceEnhanced`，以及以 setoid 等价 `req` 表述的 `RealInterfaceSetoid` 系。两系的字段构成一一对应，实质差别在于**超越函数字段是否携带正性前提**：柯西实数上的对数只能在正参数上构造（`cw_log`），因此 log 族带前提的 setoid 系可由具体 `Real` 满足。本文的实例化全部落在该系上。

| 接口 | 定义 | 字段构成 | `Real` 实例 |
|---|---|---|---|
| `RealSetoidCore.RealInterfaceSetoidCore` | Class | setoid 核心（req 自反/对称/传递）；常数与运算；Proper 原理；环律；序律；正元求逆；metric 逐 eps 族；lim / lim_unique / cauchy_complete | `Real_RealInterfaceSetoidCore` |
| `RealSetoid.RealInterfaceSetoid` | Class | Core 全部字段 + exp 族（exp_neg / exp_neg_pos / exp_neg_zero / exp_neg_plus）+ log 族（log_inv 及三条恒等，带正性前提）+ metric 逐 eps 与完备性 | `Real_RealInterfaceSetoid` |
| `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid` | Class | Setoid 全部字段 + 正性与保序（one_pos / lt_mult_compat / inv_pos_le_compat 等）+ min / r_max / pos_test / pos_part / r_if + abs 族 + exp_neg 族 + log 族（带正性前提）+ metric 与完备性 | `RealEnhancedReal` |

log 族的前提是两系的分水岭。setoid 系的相应字段为：

```coq
(* RealInterfaceSetoid，L32672 *)
log_inv : forall x, lt zero x -> R;
(* RealInterfaceEnhancedSetoid（L40464）log 族字段：log L40570 / log_inv L40578 / exp_neg_log_inv L40580 *)
log : forall x, lt zero x -> R;
log_inv : forall x, lt zero x -> R;
exp_neg_log_inv : forall x Hx, req (exp_neg (log_inv x Hx)) x;
```

即 `exp_neg` 与 `log_inv` 的互逆性只在正参数上要求——这与构造性对数的定义域一致，
也是该系接口能够实例化的原因。

三个实例的字段逐一取自 `Real` 层已证引理，不含任何公理。例如`RealInterfaceEnhancedMod.RealEnhancedReal`的回填包括`req := real_eq`、`plus := real_plus`、`req_plus_compat := RealSetoid.real_eq_plus_compat_adapt`；完整版实例 `Real_RealInterfaceSetoid`则把`exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log`等超越函数字段填为实值。度量与完备性方面，`metric_pos` 与 `metric_triangle` 采用**逐 eps 余量形式**：构造性 `le` 以 `Or (lt) (req)` 编码，无法表达「非严格且不趋近」，故以 `∀ eps > 0` 的余量陈述，这是该编码下可达的最强形式。

### 3.6 序编码的语义分层与权衡（`le` 的四层角色）

§3.5 交代了两系接口的字段构成与实例回填；本节再把序编码本身收拢为一处：实数层的两个非严格序谓词、接口 `le` 字段的回填实况、以及 Or 形与 Bishop 形的设计权衡。这一编码选择是全文「抽象层—实例层」双层架构的根源，值得在进入定理陈述前一次性向读者交代。

**四层角色对照表**：

| 谓词/字段 | 定义 | 所在层 | 角色 |
|---|---|---|---|
| `real_le` | `Or (real_lt x y) (real_eq x y)`——构造性析取（严格小或相等，各支携带显式见证） | 柯西实数层 | 实数层精确序本体；setoid 接口 `le` 字段在 Real 实例中的回填值 |
| `real_le_b` | `forall eps, lt zero eps -> real_lt x (y + eps)`——Bishop 形（全称化逐 eps 严格余量，Set 层 forall 型） | Real 层补齐路线（独立模块 `UpRealLeB.v`） | Real 层 eps/Bishop 形定理的目标序：可填充、无需分支见证（§9.4 例二） |
| setoid 接口 `le` 字段 | `RealInterfaceSetoidCore`/`RealInterfaceSetoid` 的序投影字段 | 抽象 setoid 接口层 | Real 实例（`Real_RealInterfaceSetoidCore`/`Real_RealInterfaceSetoid`）中回填为 **Or 形 `real_le`**（两实例同一选择） |
| req 系精确 `le` 结论 | req 系定理（如 §3.3 `req_min_free_energy_is_boltzmann`）的 `le` 结论 | req 签名定理层 | 经接口投影继承 Or 语义，但以显式接口前提位（SumOver 对接面 `sum_le` 等、log 切线精确形）承载——是**接口假设相对的**精确序，非无条件 Real 层定理 |

**Or 形与 Bishop 形的权衡（正面陈述）**。Or 形非严格序在构造上强于 Bishop 形：`real_le ⟹ real_le_b` 平凡（单向桥 `real_le_to_le_b`：lt 支直取、eq 支换形），反向不可证（§9.4 例二 (i) 的分支不可判定论证）。本文以 Or 形为接口序语义，收益在**前提侧与抽象层**：Or 形正性证书携带析取信息（如 `beta_pos : lt zero beta`），`le x (x + z)` 型加法封闭律可由对证书作案例分析证得，抽象层定理证明流畅、主定理陈述保持数学可读性（精确序而非处处带余量）。代价集中在**结论侧的非负性类判定**：`KL ≥ 0` 的 Or 形要求交出「`KL > 0` ∨ `KL = 0`」的显式分支见证，等价于判定 `p = q`，对构造性柯西实数不可证——于是 Real 层为不可判定的非负性结论支付逐 eps 余量税，税单即「逐 eps 复刻 + 双层并行 + 冻结件」（§9.2、§9.5）。对偶路线（全库 Bishop 形：陈述处处带余量、实例化零摩擦，CoRN 式）同样可行；本文选择「抽象层精确、Real 层付税」路线的理由是主定理陈述的数学可读性优先，而 Bishop 形补齐路线（`real_le_closure_b` 完成引理族）已把该税的大头转化为机器检查的升格（§9.4 例二 (ii)/(iv)）。

**表面张力消解（`req_gibbs_inequality` 的精确 `le` 结论 vs 定理 4.9 注「Or 形不可达」）**。§3.3 的 `req_min_free_energy_is_boltzmann`（证明链消费 `req_gibbs_inequality`）以精确 `le` 为结论且 `Print Assumptions` Closed，而定理 4.9 完成状态注（§9.4 例二）称「结论取 Or 编码时完成一般不可达」——二者并不矛盾，关键的分层事实有二。其一（回填实况）：setoid 接口的 `le` 字段确以 Or 形 `real_le` 回填；但 req 系精确 le 定理的证明链所消费的 SumOver 对接面（`sum_le`/`sum_zero_nonneg`）与 log 切线精确形在 setoid 接口中仅备逐 eps 形式或 Section 假设位（接口缺口桥，§9.1.1），随 Section 泛化为定理显式前件——「Closed」指零公理，非零前提；该精确 `le` 结论因此是**接口假设相对的**，不是无前提 Real 层定理。其二（不可达的指称）：定理 4.9 注所述「不可达」针对的是**无接口假设位可消费的无条件 Real 层 Or 形非负性结论**（如无前提的 `min(a,b) ≤ a`、无前提 KL ≥ 0）；「带显式前提可证」与「无前提不可达」并存不悖。补齐线：Bishop 形目标序下，逐点 Gibbs 切线经 `real_log_le_linear_B` 无条件闭合，`real_gibbs_inequality_B`（KL ≥ 0 的 Bishop 形）与 `real_rlhf_optimal_B`（定理 4.9 的 Bishop 形对应物，`D_pos` 证书既有）已机器检查。于是同一数学内容的可併形态各有明确边界：接口假设相对的精确 Or 形（req 系）、无前提 eps 形（Real 层复刻）、无前提或带证书的 Bishop 形（补齐路线）——汇总见 §9.4 例二与 §9.6 三分类表。`Z_align_pos` 的分层实况同此口径：抽象层与 Real 层均为 Section Variable 显式前件（表 1 已列，Real 层未 discharge）；req 层经配分条件正性路线已把该槽位消去为非空 datum 前提（`zpfinal` 族，机器检查 Closed，登记见 §10.2 第 1 项 (f)）。


## 4 RLHF：KL 正则化对齐的最优性

**KL 方向约定**：全文 `KL(p‖q)` 一律指前向 KL `Σ_s p(s)·(log p(s) − log q(s))`（§3.2 `relative_entropy p q` 定义），方向由符号顺序决定、KL 不对称：`KL(π‖π*)` 为**前向** KL（π 相对 π*），`KL(π*‖π)` 为**后向** KL（π* 相对 π）。方向敏感告示：间隙恒等取前向（定理 4.3：`J*−J(π) == β·KL(π‖π*)`），迭代收缩取后向（定理 4.8：`KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0)`），两方向在单纯形上不可比、不可互换，目标间隙的几何率亦不可由二者直接组装（见 §4.3 定理 4.3 注、§4.3.1 定位注与 §10.2 第 4 项注记）；读者核对各定理陈述时请以符号顺序为准。

### 4.1 问题设定

**先决问题（定理的接口锚定与真值承载——读者必读）**：本章与 §5–§7 的全部定理陈述于抽象接口 `RealInterfaceEnhanced`（Id 等式系）之上；该接口的 setoid 对应物已由具体柯西实数实例化（字段级回填全部完成，见 §9.1.1），但**定理签名的定理级迁移已分五批推进并主体闭合**——对齐理论主体（RLHF/DPO/PPO/GRPO 与策略迭代收敛率，§4–§7）的 req 系签名版已随迁移第三阶段闭合交付，主体定理可经实例 `RealEnhancedReal` 直接落在柯西实数上（例外列出：几何收缩定理的 req 桥接件为接口假设的同位重述，见 §4.3.2；PPO 保守性族的 req 版已随最终裁决经 plain-le 接口路径交付）；其具体数学内容仍由两条路径完整承载，其一为接口字段的实例回填（实例级事实），其二为部分核心定理的 **Real 层逐 eps 复刻**（定理级，人工对齐，清单见 §9.2）。相应地，§4.3.1 的诚实接口 `step_kl_eta_bound` 在抽象层为定理的**显式前件**（Section Variable，非待证假设），其真值证据在 Real 层（统一陈述见 §4.3.2）。这不是可后续打磨的表述边界，而是有效性层面的先决问题；本文的解法与路线已立项：签名迁移工程的迁移总清单共 734 件（普查汇总清单口径：可机械平移约 584 件、需新分析机器约 86 件、已有 req 对应件 8 件、冻结双层并行 56 件；734 与分批状态表件数的对账关系见 §9.1.1 口径注）、分五批推进，其中迁移第三阶段为 §4 定理对齐主体（规划约 140 件，含 `req_step_kl_eta_bound` 等桥接件），已闭合交付——上述定理即可经 `RealEnhancedReal` 直接落在柯西实数上；注意力/采样伴件（迁移第四阶段）与最终裁决（迁移第五阶段）亦已闭合——五批主体全数闭合、无遗留项（迁移总清单 734 件中 670 件已交付，余 64 件为冻结双层并行冻结条目，详见 §9.1.1 与 §10.2 第 1 项）；64 件冻结双层件不经 req 签名消费，读者应把其「Id 层陈述 + Real 层复刻」的双层并行读作同一数学内容的两层陈述。

给定奖励函数 `r : S -> R`、参考策略 `pi_ref : S -> R`、温度参数 `beta > 0`，定义对齐目标：

```
Definition align_objective (pi : S -> R) : R :=
  sum_over_S (fun s => mult (pi s) (reward s))
  - mult beta (kl_to_ref pi).
```

其中 `kl_to_ref pi = KL(pi‖pi_ref)`。目标是找到最大化 `align_objective` 的策略 π。

### 4.2 最优策略闭式

最优策略的闭式定义如下（逐字抽取自代码库）：

```coq
(* L18761 *)
Definition Z_align : R :=
  sum_over_S (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* L18766 *)
Definition pi_star (s : S) : R :=
  mult (inv_pos Z_align Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
```

`exp_neg x` 表示 e^(−x)，因此 `exp_neg (opp (r(s)/β))` = e^(+r(s)/β)，与标准 RLHF 最优策略 π\* ∝ π_ref·e^{r/β} 一致。（标识符按「取负指数」读：`exp_neg x = e^{−x} = 1/e^{x}`，即乘法逆语义 `exp_inv`；「neg」修饰**指数**而非函数值——下游引用请勿按字面读作 e^{x} 的相反数。标识符重命名（`exp_inv`，或引入包装 `exp_pos := exp_neg ∘ opp`）列为 artifact 发布窗口的可选项，以避免破坏既有下游引用。）`Z_align` 为配分函数（其正性 `Z_align_pos` 为 Section 变量），保证 `pi_star` 归一化且正（`pi_star_pos`与 `pi_star_normalized`）。

### 4.3 核心定理

**定理 4.1**（`rlhf_optimal`）：对任意归一化且正的概率分布 `pi`，
```
le (align_objective pi) (align_objective pi_star).
```

**证明概要**：
1. 由 `min_free_energy_is_boltzmann`，Boltzmann 分布在自由能上最小化；
2. 由 `align_boltzmann_is_pi_star`，Boltzmann 分布逐点等于 `pi_star`；
3. 取负（`opp_le_compat`）将对齐目标的不等式反向，得到结论。

**定理 4.2**（`rlhf_optimal_unique`）：若 `pi_star` 与另一策略给出相同对齐目标值，则两者逐点相等。

**证明概要**：由自由能分解恒等式 `F[p] = F[p_b] + β·KL(p‖p_b)`，若 `F[p]=F[p_b]` 则 `KL(p‖p_b)=0`；再由 `gibbs_equality` 得 `p=p_b`。

**定理 4.3**（`rlhf_suboptimality_gap`）：对任意归一化且正分布 `pi`，对齐目标的次优间隙可显式写成**前向** KL 的形式：
```
Id (minus (align_objective pi_star) (align_objective pi))
   (mult beta (relative_entropy pi pi_star)).
```
即 `J* − J(π) == β·KL(π‖π*)`（方向注意：本恒等是**前向** KL `KL(π‖π*)`，与定理 4.8 收缩的**后向** KL `KL(π*‖π_t)` 方向不同，见 §4.3.1 与 §10.2 注记）。

**定理 4.4**（`rlhf_policy_improvement`）：对任意归一化且正的两策略 `p_old`、`p_new`（`normalized`/`positive_dist`），若新策略到最优策略的**前向** KL 不增，则对齐目标单调：
```
le (relative_entropy p_new pi_star) (relative_entropy p_old pi_star) ->
le (align_objective p_old) (align_objective p_new).
```
即 `KL(p_new‖π*) ≤ KL(p_old‖π*) ⟹ J(p_old) ≤ J(p_new)`——「越接近 π*（前向 KL 意义下）目标越高」（L20591–L20596 ）。注意：本定理与附录 B.2 的「改进条件」推导是**两回事**——4.4 的前提是两策略到 π* 的 KL 序，不含优势函数与 `advantage_nonneg`；附录 B.2 的 `exact_improvement_identity` 路线对应的是 §6 的 `ppo_monotonic_improvement`（定理 6.3）/`kl_penalty_sufficient`（定理 6.4），与定理 4.4 的路线无关（`rlhf_policy_improvement` 实测 L20591，见 §4.3 正文）。

**证明概要**：把定理 4.3 的次优间隙恒等分别用于 `p_old` 与 `p_new`（`J*−J(p) == β·KL(p‖π*)`）；由前提与 `β > 0` 的保序（`le_mult_compat_r`）得 `J*−J(p_new) ≤ J*−J(p_old)`；差分翻转（`le_plus_compat` + `minus`/`opp` 消去，约 20 步装配完成）即 `J(p_old) ≤ J(p_new)`。

**前件簇的 setoid 签名版（签名迁移迁移第二阶段交付）**：本章前件——自由能最小化（`min_free_energy_is_boltzmann`）、Gibbs 不等式/等号（`gibbs_inequality`/`gibbs_equality`）与温度分解（`entropy_temp_explicit`/`relative_entropy_temp_decomp` 族）——的 setoid（req 系）签名版已交付（模块 `UpReqDist` 与 `UpReqTempEntropy`；`req_min_free_energy_is_boltzmann` 为 req 无条件形态，Print Assumptions Closed）。定理 4.1/4.2 证明链消费的基座前件自此在 req 签名下有机器检查对应物；本章定理的 req 系签名版已随阶段三交付（五批主体闭合：迁移总清单 734 件中 670 件已交付，余 64 件为设计性冻结双层并行条目，见 §9.1.1），可经 `RealEnhancedReal` 直接消费；策略迭代族 4.5–4.8/5.10 的 Real 层迭代镜像属另列开放项（§10.2 第 1 项 (h)），不属签名迁移未闭合；「抽象层定理 + Real 层复刻」的两层陈述不变。

### 4.3.1 策略迭代的更新规则

定理 4.5–4.8 依赖以下显式定义（逐字对应代码库 `Section Alignment` 的 policy 定义区）。步长参数与正则性假设：

```coq
Variable eta         : R.
Variable eta_pos     : lt zero eta.        (* 0 < η *)
Variable eta_le_one  : le eta one.         (* η ≤ 1 *)
```

增广优势与相对熵镜像下降单步（对 `pi_t` 的 KL 信任域步）：

```coq
Definition advantage_aug (pi_t : S -> R) (s : S) : R :=
  minus (reward s) (mult beta (minus (log (pi_t s)) (log (pi_ref s)))).

Definition Z_rel (pi_t : S -> R) : R :=
  sum_over_S (fun s => mult (pi_t s)
    (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).

Definition pi_next (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)) (s : S) : R :=
  mult (inv_pos (Z_rel pi_t) (Z_rel_pos pi_t pi_t_pos))
       (mult (pi_t s) (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos)) (advantage_aug pi_t s))))).
```

即 `pi_next(pi_t)(s) ∝ pi_t(s)·exp(+(η/β)·A_aug(pi_t, s))`——Boltzmann 更新权重。**指数内的符号是"+"**：代码写作 `exp_neg (opp (mult …))`，依 §4.2 约定 `exp_neg x = e^{−x}`，`exp_neg (opp x) = e^{+x}`，故散文公式应为 `exp(+(η/β)·A_aug)` 而非 `exp(−(η/β)·A_aug)`。若取相反符号，则权重随优势递减、更新背离 π*，与定理 4.5–4.8 的全部机器检查恒等式矛盾；代码语义与 §4.2 π* ∝ π_ref·e^{r/β} 同一符号约定，单步即向 π* 的**几何插值桥**（见下），恒等式族全部成立。几何插值的指数化含义：对权重取对数得 `log π_{t+1}(s) = log π_t(s) + (η/β)·A_aug(π_t, s) − log Z_rel(π_t)`；代入 `A_aug := r − β·(log π_t − log π_ref)` 与 `log π*(s) = log π_ref(s) + r(s)/β − log Z_align`（定理 5.1 证明概要）即得 `log π_{t+1}(s) = (1−η)·log π_t(s) + η·log π*(s) + const`，亦即

π_{t+1} ∝ π_t^{1−η}·(π*)^η

——策略在对数几率空间中向 π* 作 (1−η):η 的凸插值（0 < η ≤ 1；η = 1 一步到 π*，η → 0 原地不动）。同一计算解释两个结构事实：其一，π* 是单步不动点——代换得 `A_aug(π*, ·) ≡ β·log Z_align` 为常数（与状态无关），于是 `Z_rel(π*) = Z_align^η` 且 `pi_next(π*)(s) = π*(s)`；其二，向后 KL 递推的收缩系数正来自该几何插值——机器检查的单步引理 `policy_iter_backward_kl_step_le`为 `KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1})`（等号恒等版含可弃项 `−η·KL(π_t‖π*) ≤ 0`，见代码 `policy_iter_backward_kl_step`恒等版与 L22780 的 le 版注释），第一项系数 1−η 即 `log π_t` 的插值权重，第二项为单步 KL 残差、即 `step_kl_weighted` 的来源。迭代打包与加权步长 KL 和：

```coq
Fixpoint policy_iterate (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s))
  : { pi' : S -> R & forall s : S, lt zero (pi' s) } := ...   (* L22879 起 *)

Fixpoint step_kl_weighted (t : nat) (pi : S -> R) (pi_pos : forall s : S, lt zero (pi s)) : R :=
  (* S(0) = 0;  S(S m) = KL(pi_m‖pi_{S m}) + (1−η)·S(m) *)   (* L22903 起 *)
```

步长诚实接口（升级后唯一接口：步长 KL 被**前向** KL 到最优控制；本前提的数学地位、纸笔论证与 Real 层机器状态统一见 §4.3.2）：

```coq
Variable step_kl_eta_bound : forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s)),
  le (relative_entropy pi_t (pi_next pi_t pi_t_pos))
     (mult eta (relative_entropy pi_t pi_star)).               (* L23114 *)
```

**定理 4.5**（`policy_iter_backward_kl_iter_le`）：策略迭代 `pi_{t+1} := pi_next pi_t`（相对熵镜像下降单步）的向后 KL 满足**精确加权递推上界**：
```
le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos)))
   (plus (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi))
         (step_kl_weighted t pi pi_pos)).
```
即 `KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0) + Σ_{i<t} (1−η)^{t−1−i}·KL(pi_i‖pi_{i+1})`——κ := 1−η 显式收缩因子，步长 KL 加权和显式保留（`step_kl_weighted` Fixpoint；迭代打包 `policy_iterate`，sigT 正性内嵌`policy_iter_norm`，归一化保持）。

**证明概要**：归纳组装 `policy_iter_backward_kl_step_le`（单步递推）——归纳前提乘 κ（`le_mult_compat_weak` + `mult_comm` 换形，κ ≥ 0 由 `le_minus_nonneg`(η≤1)）→ `le_plus_compat` 加步长 KL → `distrib`/`plus_assoc`/`plus_comm`/`mult_assoc` 四步代数完成。

**定理 4.6**（`policy_iter_gap_diff`）：间隙单步**显式恒等式**——策略改进量恰为 β·加权 KL 对：
```
Id (minus (align_objective (pi_next pi_t pi_t_pos)) (align_objective pi_t))
   (mult beta (plus (mult (minus (inv_pos eta eta_pos) one)
                          (relative_entropy (pi_next pi_t pi_t_pos) pi_t))
                    (mult (inv_pos eta eta_pos)
                          (relative_entropy pi_t (pi_next pi_t pi_t_pos))))).
```
即 `J(pi_{t+1}) − J(pi_t) == β·[(1/η−1)·KL(pi_{t+1}‖pi_t) + (1/η)·KL(pi_t‖pi_{t+1})]`——把 `policy_improvement_mono`证明体内的 `Hbeta_form` 链（`surrogate_diff_identity` + `inv_pos` 左逆 + 分配/减法分布）提取为独立定理（单步改进 ≤ 的定量恒等强化；注意它强化的是 REPS 型单步改进 `policy_improvement_mono`，与定理 4.4 的 KL-到-π* 序陈述是两回事）。

**证明概要**：J 分解（`J_pi_t_t12`/`J_pi_next_t12`）→ `surrogate_diff_identity` ÷η（`inv_pos_correct` 吸收）→ 减法重组（`plus_assoc`/`plus_comm`）→ β 分配（`distrib` + `mult_minus_distr_r_t12`）完成。

**定理 4.7**（`policy_iter_gap_mono`）：间隙单调不增——`gap_{t+1} := J* − J_{t+1} ≤ J* − J_t =: gap_t`。

**证明概要**：`policy_improvement_mono` + `opp_le_compat` + `le_plus_compat`（`minus` 定义展开即闭）。

**定理 4.8**（`policy_iter_kl_geom_iter`）：诚实接口 `step_kl_eta_bound`（步长 KL 被前向 KL 控制：`KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`；≡ 插值不等式 `log Z ≤ 0`；假设地位与 Real 层 discharge 状态见下方标注与 §4.3.2；零公理）下，向后 KL **真几何收缩率 κ := 1−η（c := 0）**：
```
le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos)))
   (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi)).
```
即 `KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)`——单步真几何收缩（`policy_iter_kl_geom_step`：`KL(pi*‖pi_{t+1}) ≤ (1−η)·KL(pi*‖pi_t)`）归纳组装；因 0 < η ≤ 1 有 κ ∈ [0,1)，`(1−η)^t` 为显式指数衰减，**无需**附加 `c < η` 假设。

**假设地位标注**：`step_kl_eta_bound` 在 `RealInterfaceEnhanced` 抽象层为 Section 假设（B 类接口假设，非公理，随 Section 泛化为定理显式前件）；其在 Real 层的对应定理 `real_step_kl_eta_bound_eps`已在库内证明；其 **req 系同位桥接件 `req_step_kl_eta_bound` 亦已交付**（迁移第三阶段，四项验证通过）——即桥接件以 req 系 setoid 签名直接实现的更强形态已兑现。**假设位诚实注**：`req_step_kl_eta_bound` 为抽象层 Variable 的 req 签名**同位重述（桥接假设）**，非无条件定理；backward KL 无条件版（`req2_backward_kl_step`）已另行交付（`UpReqAlign3.v` 终版，六件 Print Assumptions 全 Closed——前置条件 P-1 达成）。抽象层签名对接（§10.2 第 1 项）完成前，定理 4.8 的抽象层陈述维持诚实接口表述——`(1−η)^t` 结论在该接口前提下成立；完整对应定理清单与证明路线见 §4.3.2。〔（该维护形态说明的现行状态见补充材料 S2。）本段「同位重述（桥接假设）、非无条件定理」的定性据此刷新：接口路径已具无条件供给链，定理 4.8 的抽象层陈述与 `(1−η)^t` 结论不变。〕

**证明概要**：单步：精确三 KL 恒等 `policy_iter_backward_kl_step`给出 `KL(pi*‖pi_{t+1}) == (1−η)·KL(pi*‖pi_t) − η·KL(pi_t‖pi*) + KL(pi_t‖pi_{t+1})`，`step_kl_eta_bound` 保证 `KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`，两 η 项抵消（`plusA_opp_cancel_le` 辅助完成）即得单步收缩；迭代：归纳前提乘 κ（κ ≥ 0 由 `le_minus_nonneg`（η ≤ 1）保证；`le_mult_compat_weak` + `mult_comm` 换形）→ `r_pow` 结合换形完成。


### 4.3.2 定理 4.8 的诚实接口：数学地位、纸笔草图与 Real 层对应定理（统一小节）

本小节把定理 4.8 唯一剩余诚实接口 `step_kl_eta_bound` 的分散信息（接口选择的定位论证、数学地位的等价性、纸笔草图、Real 层证明路线与机器状态）收拢为一处；正文与脚注的四层互指自此收敛为本节的顺序陈述。

**定理 4.8 的准确定位**：`policy_iter_kl_geom_step`/`policy_iter_kl_geom_iter`陈述**真几何率 κ := 1−η（c := 0）**，即下文的 `KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)`——无需附加 `c < η` 假设的收敛率定理。其关键是接口选择：比值型接口 `step_kl_ratio_bound`（「前向 KL ≤ c·向后 KL」）对任意常数 c 并非定理——两方向 KL 在单纯形上不可比，前向 KL 可无界而 `KL(pi*‖pi_t)` 有界，比值无界（反例论证见代码 L23102–L23113 注释）；本文采用单一诚实接口 `step_kl_eta_bound`把步长 KL 控到**同向**（前向）KL：`KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`，数学上为真（≡ 插值不等式 `log Z ≤ 0`，Z := Σ_s pi_t(s)^{1−η}·pi*(s)^η；该接口的数学地位、纸笔论证与 Real 层对应定理统一见 §4.3.2）。

**该前提的数学地位与 discharge 状态**：接口升级（`step_kl_ratio_bound` → `step_kl_eta_bound`）已在代码层完成：新接口 + 真几何率 `(1−η)^t`（`policy_iter_kl_geom_step`/`iter`，L23146/L23181）。`step_kl_eta_bound` 在纸笔文献中对应相对熵（镜像）下降三点引理族把步长 KL 控到前向 KL 的收缩估计——本节更新律即单纯形上的**熵镜像下降**（Nemirovski–Yudin 框架 [18]；镜像下降的标准形式化见 Beck–Teboulle [19]），`(1−η)^t` 型指数收缩率与镜像下降在线凸优化中的经典率分析同族（Hazan et al. [20]）；本文的增量不在该率本身，而在其零公理构造性机器检查、显式步长接口与前提的分类显式化——其数学真值 ≡ 插值不等式 `log Z ≤ 0`（Z := Σ_s pi_t(s)^{1−η}·pi*(s)^η，几何插值 π_{t+1} ∝ π_t^{1−η}(π*)^η 的配分函数；π* 为单步不动点，残差 `KL(pi_t‖pi_{t+1})` 可经 `Z_rel` 展开为 log-sum-exp，见本节定义处）。其 Real 层对应定理已在库内证明，抽象层陈述维持诚实接口表述（完整对应定理清单、组装路线与状态见 §4.3.2）。

**与镜像下降及 PMD 线性率文献的对照**：在策略优化一侧，本更新律对应乘性权重/指数权重在单纯形上的经典几何收敛，与 policy mirror descent（PMD）线性收敛率文献同族：Xiao [27] 在无限折扣 MDP 的表格型 softmax 策略上给出锐利的次线性率，并在熵正则化更新下给出线性率；Khodadadian et al. [28] 证明常数步长下自然策略梯度的线性（几何）收敛。本文的贡献不在于该率本身——(1−η)^t 是镜像下降谱系的标准率形——而在其零公理构造性机器检查、显式步长接口 `step_kl_eta_bound` 的前提显式化，以及该率在柯西实数层上的 eps/Bishop 形对应物（见下文机器状态）。引用上述文献即为把定位说清：本文不主张新的优化率，主张的是该率在构造性逻辑下被机器检查且全部前提显式。三者的逐条对照如下表（文献行为其原文率形的定性转录，前提列非逐条件完整清单；本文行按库内已证事实填写，机器状态见本节状态脚注）：

| 文献 | 设定 | 率形 | 前提 | 逻辑立场 | 机器检查 |
|---|---|---|---|---|---|
| Xiao [27] | 无限折扣 MDP（折扣因子 <1），表格型 softmax 策略 | 次线性率（无正则化）；熵正则化更新下线性（几何）率 | 折扣因子 <1、期望意义梯度、步长条件 | 经典（纸笔证明） | 无 |
| Khodadadian et al. [28] | 自然策略梯度（表格型 softmax、常数步长） | 线性（几何）渐近收敛；另有超线性变体与改进的有限时间界 | 常数步长条件、表格型参数化 | 经典（纸笔证明） | 无 |
| 本文（定理 4.8） | 有限状态空间、全状态精确和的单步 KL 正则化目标：相对熵镜像下降单步，几何插值 π_{t+1} ∝ π_t^{1−η}·(π*)^η | KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0)，κ := 1−η（c := 0）真几何率 | 0 < η ≤ 1，加诚实接口 `step_kl_eta_bound`（≡ 插值不等式 log Z ≤ 0） | 纯构造性、零 Axiom（序取 Or 编码、余量逐 eps，Bishop 形对应物已建） | 定理 4.8 在接口前提下机器检查；单步 eta-bound 的 Real 层对应物已证——eps 形 `real_step_kl_eta_bound_eps`、Bishop 形 `real_step_kl_eta_bound_B`、接口假设的无条件 eps 形放电 `geod_policy_iter_kl_geom_step_eps`（eps 形件的证书前提见本节状态脚注）；迭代率 (1−η)^t 的抽象层陈述维持诚实接口表述，其 Real 层迭代镜像为开放项（§10.2 第 1 项 (h)） |

三条路线的设定不可直接互比：[27][28] 的率以折扣 MDP 的期望回报为对象、允许端到端迭代优化变量；本文对象为有限状态全状态精确和的单步目标理论，迭代镜像属独立模块形态（§10.2 第 1 项 (h)），抽象层迭代率维持接口表述——故本表主张的对照点是**同一率形（几何收缩）在不同逻辑立场下的可达形态**，而非率的强弱排序。


**`step_kl_eta_bound` 的几何插值直觉与 `log Z ≤ 0` 纸笔草图（纸笔论证，非机器检查）**：为何几何插值 `π_{t+1} ∝ π_t^{1−η}·(π*)^η` 蕴含单步 KL 上界 `KL(π_t‖π_{t+1}) ≤ η·KL(π_t‖π*)`？因为该单步 KL 恰可展开为「η 倍前向 KL 到 π* + 插值配分函数的对数」，而后者 ≤ 0 由 log-sum-exp（Boltzmann 归一化）的凸性保证。非形式直觉：对数几率空间中的插值 `log π_{t+1} = (1−η)·log π_t + η·log π* − log Z`（见本节定义处的几何插值推导）把 `π_t` 沿指数族测地线向 `π*` 平移 η 比例，被跳过的 KL 残差不超过整段前向 KL 的 η 倍——KL 到插值点的距离沿插值凸方向收缩，这正是 log 配分函数凸性（等价于 Hölder/加权 Young）的体现。形式上，把 `A_aug` 展开并利用 `π* ∝ π_ref·e^{r/β}`（定理 5.1 概要）代入配分函数定义（L21240 区）：

```
Z_rel(π_t) = Σ_s π_t(s)·exp((η/β)·A_aug(π_t, s))                      （§4.3.1 定义）
           = Σ_s π_t(s)^{1−η}·π_ref(s)^η·exp((η/β)·r(s))               （A_aug 展开，π_t^{−η} 吸收）
           = Z_align^η · Σ_s π_t(s)^{1−η}·π*(s)^η                      （π* 闭式代换，归一化吸收）
```

记 `Z := Σ_s π_t(s)^{1−η}·π*(s)^η = Z_rel(π_t)/Z_align^η`（即本节定位注中 `log Z ≤ 0` 的 `Z`；退化端 η = 1 时 `Z = Σ_s π* = 1`、η = 0 时 `Z = Σ_s π_t = 1`，两端平凡）。由归一化 `Σ_s π_{t+1}(s) = 1` 得逐点形 `π_{t+1}(s) = π_t(s)^{1−η}·π*(s)^η / Z`，代回单步 KL：

```
KL(π_t‖π_{t+1}) = Σ_s π_t(s)·[log π_t(s) − log π_{t+1}(s)]
                = Σ_s π_t(s)·[η·(log π_t(s) − log π*(s)) + log Z]
                = η·KL(π_t‖π*) + log Z                                 （Σ_s π_t = 1）
```

故 `step_kl_eta_bound ⟺ log Z ≤ 0`。而 `log Z ≤ 0` 是 log-sum-exp 凸性的直接推论（p := 1/(1−η)、q := 1/η 的 Hölder/加权 Young 同族）：

```
log Z = log Σ_s exp((1−η)·log π_t(s) + η·log π*(s))
      ≤ (1−η)·log Σ_s exp(log π_t(s)) + η·log Σ_s exp(log π*(s))       （log-sum-exp 凸性）
      = (1−η)·log Σ_s π_t(s) + η·log Σ_s π*(s)
      = (1−η)·log 1 + η·log 1 = 0                                       （π_t、π* 均归一化）
```

等号当且仅当 `π_t = π*` 逐点（log-sum-exp 严格凸侧）。上述推导为纸笔层面论证，用于解释诚实接口 `step_kl_eta_bound`的数学地位与 Real 层证明的路线。**Real 层机器状态**：本不等式在 Real 层的对应定理已在库内证明（插值不等式 `real_interp_Z_le_one_eps`与 eta-bound 对应定理 `real_step_kl_eta_bound_eps`，连同支撑件 `real_exp_two_point_cvx_eps`/`real_amgm_pointwise_eps`，见 §10.2 第 1 项 (a)）；证明组装为 exp 两点凸性 + 逐点 AM-GM + 求和保序（种子 `real_exp_ge_linear_eps`）；该形态为 Real 层 eps 定理，不改变定理 4.8 的抽象层陈述（诚实接口表述，见本节末机器状态）。

**`step_kl_eta_bound` 的 Real 层 Proof Outline（已在库内兑现）**：把上面纸笔草图扩展为 Real 层闭合的证明计划（对应定理清单见本节末机器状态）。目标：在 Real 层（柯西实数、逐 eps 余量）证明插值不等式 `log Z ≤ 0`（Z := Σ_s π_t(s)^{1−η}·π*(s)^η），为诚实接口 `step_kl_eta_bound` 提供 Real 层 eps 对应物（定理 4.8 的抽象层陈述因此维持不变，见本节末机器状态）。所需 Real 层引理清单（原列 1–3 的有限和 Jensen/log-sum-exp 凸性/Hölder 在本几何插值特形统一坍缩为「逐点 AM-GM + 求和保序」；原引理 4 维持为组装步）：
1. **exp 两点凸性（Real 层 eps 化）**：`(1−η)·e^x + η·e^y ≥ e^{(1−η)x+ηy} − eps`——Varberg 锥论证：记 `z := (1−η)x + ηy`，则 `x−z = η(x−y)`、`y−z = (1−η)(y−x)`；由种子得 `e^{x−z} ≥ 1 + η(x−y)` 与 `e^{y−z} ≥ 1 − η(x−y)`（Bishop 逐 eps 形态），乘正元 `e^z > 0` 加权合并即完成——**只用已证种子 `real_exp_ge_linear_eps`（e^t ≥ 1+t，对全部 t 含负），无符号分支、无三分、无需新建 Jensen 基建**（两处 eps 簿记：各 `eps/2` 或正乘加权，模板同附录 C.2）；
2. **逐点 AM-GM**：`a^{1−η}·b^η ≤ (1−η)·a + η·b`（a、b > 0）——第 1 条在 `(x,y) := (log a, log b)` 的实例，经 `real_pow_pos` 定义（`a^α := exp(α·log a)`）与 `cauchy_real_exp_plus/wd`（既有）换形；
3. **求和保序与归一化吸收**：`Z := Σ_s π_t^{1−η}·π*^η ≤ 1 + eps`——逐点 AM-GM 逐点求和（`real_sum_over_S_le` 接口既有）+ 归一化 `Σπ_t == Σπ* == 1` 吸收；
4. **log 侧严格化与组装**：由 `Z ≤ 1 + eps/2` 与 `1 + eps/2 < e^{eps}`（种子在 t := eps/2 的严格化）得 `Z < e^{eps}`，经 log 单调 lt 版（`cw_log` 路线既有）得 `log Z < eps`；代回单步 KL 展开 `KL(π_t‖π_{t+1}) == η·KL(π_t‖π*) + log Z`（见上纸笔草图）→ 以 `real_le` 的 inl（lt）支完成为 `real_step_kl_eta_bound_eps`；随后沿 §4.3.1 迭代组装（定理 4.5–4.8 同型路线）即可闭合定理 4.8 的 `(1−η)^t` 上界在 Real 层的对应物。上述引理均为标准事实的有限和/eps 化形态，组装无潜在逻辑障碍；该路线已在库内兑现（四模块行号见本节末机器状态）。



**状态脚注**：`step_kl_eta_bound` 的**数学真值已确认**——其 ≡ 插值不等式 `log Z ≤ 0` 的等价与纸笔论证见本节上文（定理 4.8 定位注、discharge 注、纸笔草图与 Proof Outline）；**机器检查 discharge 路线**——所需基建在本几何插值特形坍缩为逐点 AM-GM + 求和保序（种子 `real_exp_ge_linear_eps`（e^t ≥ 1+t）已在库内；另有 `real_expf_realizable`供 expf 迷你接口放电），Real 层核心不等式族（插值不等式 `Z ≤ 1 + eps` 与 eta-bound 对应物及其支撑件）已在库内证明：`real_exp_two_point_cvx_eps`（exp 两点凸性）、`real_amgm_pointwise_eps`（逐点 AM-GM）、`real_interp_Z_le_one_eps`（插值不等式 `Z ≤ 1 + eps`）与 `real_step_kl_eta_bound_eps`（eta-bound 对应定理）——均以自然数步进枚举（`seq 0 n`）为载体、以归一化 `real_eq` 前提（Σ==1）与显式证书前提（HZ：插值配分函数正性；Hqv：逐点正性）接口化。定理 4.8 的抽象层陈述维持「诚实接口下成立」的现有表述（Real 层 eps 定理与抽象接口分属两层，接口的抽象层消解仍受 Set 层接口公理集限制，见定位注），其 `(1−η)^t` 结论不变；其 req 系同位桥接件 `req_step_kl_eta_bound` 已随迁移第三阶段交付（假设位同位重述，见假设地位标注）。**层级口径（修订对齐，务必）**：上列 Real 层各件均为**单步** eta-bound 的 eps 对应物；定理 4.8 的迭代率 (1−η)^t 的 Real 层**逐 eps 迭代镜像亦已机器检查**（模块层 `UpStepKLM3` 的 `real_iter_kl_geom`：`KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps`，单步收缩件对 `t` 归纳、误差按 `t` 步算术累积；Real 载体闭端全域单调 `(1−η)^{t₁} ≤_B (1−η)^t` 另见 `KLWallClosed` 的 `klc_closed_powb_mono`）——该结果位于模块层而非 219 锚，故本文对 (1−η)^t 的**正文**主张仍仅及抽象层（接口前提下）与 Real 层单步，模块层镜像不并入正文主张（两层口径见 §9.1.1，登记见 §10.2 第 1 项 (h)）。英文脚注原文：*The mathematical truth of `step_kl_eta_bound` (equivalently `log Z ≤ 0`) is established by pen-and-paper argument in §4.3.1. For this geometric-interpolation special case, the required infrastructure collapses to pointwise AM-GM assembled from the machine-checked seed `real_exp_ge_linear_eps` (L40962, e^t ≥ 1+t) together with sum order-preservation. The Real-layer core inequalities are proved in the library: the two-point convexity lemma `real_exp_two_point_cvx_eps`, the pointwise AM-GM lemma `real_amgm_pointwise_eps`, the interpolation bound `real_interp_Z_le_one_eps` (L112890, Z ≤ 1 + eps over a normalized finite enumeration with explicit positivity certificates) and the eta-bound counterpart theorem `real_step_kl_eta_bound_eps` (L113142, the pointwise-epsilon form of the step-KL bound with explicit positivity certificates HZ/Hqv), all stated over natural-number initial segments `seq 0 n`. These Real-layer results are single-step counterparts; the Real-layer eps-wise iterative mirror of the (1−η)^t rate is also machine-checked at the module layer (`real_iter_kl_geom`, module `UpStepKLM3`: KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps), but is not consumed by the body statements (§10.2, item 1(h)). Theorem 4.8 itself remains stated under the honest-interface formulation at the abstract layer; its (1−η)^t bound is unchanged.***定理 4.9**（`real_rlhf_optimal_eps`）：RLHF 最优性的 **Real 层复刻（eps 化）**——柯西实数层对齐目标满足：
```
real_le (real_opp (real_free_energy pi Hpi))
        (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos))
                   (real_mult D eps)).
```
即 `J(π) ≤ J(π*) + D·eps`（eps 加权残差形态；Real 层 KL ≥ 0 只有 eps 版 `real_gibbs_sum_eps`，构造性边界注记）。

**证明概要**：熵侧 KL 分解经诚实接口 `real_kl_decomp_full`（常数消去桥：F(p) == F(p_b) + D·Σkl）——逐点 `log p == log p_b + kl_term` 抵消链 + Σ ext + sum_add + `real_kl_term_equiv` → 自由能 KL 分解接口 → gibbs eps（0 ≤ Σkl + eps）→ D 正乘（`real_le_mult_compat` + comm 换形）→ `le_plus_compat`（F(p_b) ≤ F(π) + D·eps）→ opp 取负（`real_opp_le_compat` + 环恒等 A == (A+oppC)+C 完成）。诚实接口（零公理）：`real_boltzmann_log_decomp`/`real_boltzmann_normalized`/`real_kl_term_equiv`/`real_pi_star_align`/`real_gibbs_sum_eps`/`real_kl_decomp_full`——全部 Real 层可实例化（`real_rlhf_optimal_eps` 的证明实际消费 `real_kl_decomp_full`）。

**完成状态注**：本定理 eps 余量形态与「精确形态」的关系已在 §9.4 例二显式分析——结论取本库 `real_le` 的 Or 编码时完成一般不可达（理由与 `real_min_le_l_eps` 同源），结论取 Bishop 形非严格序（`∀eps>0, x < y + eps`）时完成构造性可达（eps/2 簿记，权系数 `D` 需显式正性证书）；对应引理族已实现（独立模块 `UpRealLeB.v`，四项验证通过，§10.2 第 1 项 (g)）：完成引理 `real_le_closure_b` 与本定理的 Bishop 形对应物 `real_rlhf_optimal_B` 已机器检查——`D` 的正性证书 `D_pos` 为本定理节内既有变量，对应物为**完整升格**（零新增前提）；本定理在主文件的 eps 形陈述不变，Bishop 形对应物为独立模块形态追加的更强表述（Or 形「精确版」不可达，§9.4 例二 (i)/(iv)）。

---

## 5 DPO：隐式奖励的精确恢复

### 5.1 DPO 损失与隐式奖励

DPO 将奖励函数隐式定义为：

```coq
Definition dpo_implicit_reward (pi : S -> R) (s : S) : R :=
  mult beta (minus (log (pi s)) (log (pi_ref s))).
```

聚合形式的 DPO 损失为对齐目标的负值：

```coq
(* L19090 *)
Definition dpo_loss (pi : S -> R) : R :=
  opp (align_objective pi).
```

### 5.1.1 逐对 Bradley-Terry 损失

对数几率比与逐对 DPO 损失定义如下：

```coq
(* L20880 *)
Definition log_ratio (pi : S -> R) (s : S) : R :=
  minus (log (pi s)) (log (pi_ref s)).

(* L20885：成对 DPO 损失，偏好 s_w ≻ s_l *)
Definition dpo_loss_pair (pi : S -> R) (s_w s_l : S) : R :=
  opp (log (sigmoid (minus (mult beta (log_ratio pi s_w))
                           (mult beta (log_ratio pi s_l))))).
```

即标准 DPO 的 Bradley-Terry 形式[31]（RLHF 侧以偏好微调语言模型的早期工作见[39]）

\[
\mathcal{L}_{\text{DPO}}(\pi; s_w, s_l) = -\log\sigma\!\left(\beta\log\frac{\pi(s_w)}{\pi_{\text{ref}}(s_w)} - \beta\log\frac{\pi(s_l)}{\pi_{\text{ref}}(s_l)}\right).
\]

**定理 5.1**（`dpo_loss_at_pi_star`）：在最优策略处，逐对损失精确退化为真实奖励差的对数几率：

```coq
forall s_w s_l : S,
  Id (dpo_loss_pair pi_star s_w s_l)
     (opp (log (sigmoid (minus (reward s_w) (reward s_l))))).
```

**证明概要**：由 `log_pi_star` 展开 `log (pi_star s)` = `−log Z_align + log (pi_ref s) + r(s)/β`；`π_ref` 项与 `Z_align` 项在差分中严格消去，`β·(1/β) = 1` 由 `inv_pos_correct` 完成。约 30 步构造性代数链。

**边界声明**：本工作形式化了 DPO 的**逐对损失在最优策略处的精确取值**与**隐式奖励恢复**。尚未形式化：偏好数据集上的期望总损失、梯度、以及优化算法的收敛性。两个「单调」陈述的对象须分清：(i) 定理 5.7（`dpo_total_loss_monotone`）的「总损失单调」指**有限偏好列表 fold 求和** `dpo_total_loss`的泛单调性——逐对损失 `dpo_pair_loss`逐项不增 ⟹ 列表和不增，语句**不含 π***、**不含改进方向**；(ii) **聚合损失** `dpo_loss`（`opp (align_objective)`，定义 L19090）沿策略改进轨道单调不增见定理 5.10（`dpo_loss_iter_step_le`/`dpo_loss_iter_mono`，L23244/L23256）——「沿改进方向单调」的准确所指。二者均不是逐对偏好损失的期望。

### 5.2 核心定理

**定理 5.2**（`dpo_optimal`）：对任意归一化正分布 `pi`，
```
le (dpo_loss pi_star) (dpo_loss pi).
```

**证明概要**：直接复用 `rlhf_optimal`，并对不等式取负。

**定理 5.3**（`dpo_reward_is_implicit`）——命名桥引理（定义性后承，reflexivity 级）：显式对数形式与隐式奖励定义逐点相等。两定义（`dpo_reward_explicit` / `dpo_implicit_reward`）实为同一项，证明即 `unfold dpo_reward_explicit, dpo_implicit_reward; reflexivity`——按 §1.2 分层属**定义性后承**而非独立结果，列此仅为命名对应，不计入恢复定理族并列贡献。

**定理 5.4**（`dpo_reward_recovers_up_to_baseline`）：在最优策略 `pi_star` 处，隐式奖励满足
```
r_DPO(pi*, s) = r(s) − beta·log Z_align.
```

即 DPO 隐式奖励精确恢复真实奖励，差一个与状态无关的配分函数基线。

**定理 5.5**（`dpo_reward_relative_exact`）：对任意状态 s, s'，
```
Id (minus (dpo_implicit_reward pi_star s) (dpo_implicit_reward pi_star s'))
   (minus (reward s) (reward s')).
```

**证明概要**：基线项在差分中严格消去，因此相对奖励无偏。

**定理 5.6**（`dpo_reward_diff_is_log_ratio_diff`）：DPO 隐式奖励差分等于最优策略与参考策略对数比之差，差分形式下的等价性为 DPO 损失与 Bradley-Terry 偏好模型[31]的一致性提供形式化基础。

**定理 5.7**（`dpo_total_loss_monotone`）：在有限偏好列表上（fold 求和，非数据集期望），总损失满足 **fold-plus 的泛单调性**：若对列表内每个偏好样本都成立 `le (dpo_pair_loss pi2 pref) (dpo_pair_loss pi1 pref)`，则 `le (dpo_total_loss pi2) (dpo_total_loss pi1)`——语句**不含 π*** 也**不含改进方向**（它只把逐对损失逐项不增抬升为 fold 求和不增；`dpo_pair_loss`（偏好列表版，与 §5.1.1 的状态对版 `dpo_loss_pair`为两个不同定义）、`dpo_total_loss`）。「π* 处总损失取显式闭式值」见 `dpo_total_loss_at_star`；「沿策略改进轨道单调不增」是**聚合损失** `dpo_loss`的性质（定理 5.10），勿与本节混淆。

**证明概要**：对偏好列表归纳（fold 结构归纳）：基例 `zero ≤ zero`；归纳步把逐点前提与归纳假设经 `le_plus_compat` 相加（约 10 步）。

**定理 5.8**（`real_dpo_loss_pi_star_bounded_both`）：Real 层 DPO 逐对损失在 `pi_star` 处满足**双侧定量界**——对任意赢/输样本 `s_w, s_l`，
```
real_lt (reward s_l) (reward s_w) ->
And (real_lt real_zero (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l))
    (real_lt (real_dpo_loss_pair real_pi_star real_pi_star_pos s_w s_l)
             (real_log (real_plus real_one real_one) real_two_pos)).
```
即 `r_l < r_w ⟹ 0 < L_DPO(π*, s_w, s_l) < log 2`。

**证明概要**：上界复用 `real_dpo_sigmoid_loss_bounded`；下界链为 `1 < 1+e^{−x}`（平移）→ `σ(x) < 1`（inv 反序 + inv 1 == 1）→ `log σ < log 1 == 0`（log 严格递增）→ `0 < −log σ`（opp 反向）→ 经 `real_dpo_loss_at_pi_star`换形。`inv 1 == 1` 块内自证（`real_inv_one_local`，走 `real_inv_unique` 路线：`inv_pos_correct` + `real_mult_one` 两前提）。零新增公理、纯构造性、Set 层（`And` 为 Set 值）。

**定理 5.9**（`real_dpo_reward_recovers_up_to_baseline`）：DPO 隐式奖励恢复的 **Real 层复刻**——柯西实数层 `pi_star` 处隐式奖励精确恢复真实奖励（差配分基线偏移）：
```
real_eq (real_dpo_reward_explicit real_pi_star real_pi_star_pos s)
        (real_plus (reward s) (real_opp (real_mult beta (real_log Z_align Z_align_pos)))).
```
即 `β·(log π*(s) − log π_ref(s)) == r(s) − β·log Z_align`——抽象层定理 5.4（`dpo_reward_recovers_up_to_baseline`，基线恢复）的 Real 值域版（`real_dpo_reward_explicit` 定义 L42756）。

**证明概要**：`real_log_pi_star`（闭式解 log 形式）→ 消去 `log π_ref`（`real_plus_assoc`/`real_plus_comm`/`real_plus_opp` 抵消链）→ `real_distrib` 分配 → `β·opp(logZ) == opp(β·logZ)`（`real_mult_comm` + `real_opp_mult_r` 反向 + `RealSetoid.real_eq_opp_compat`）→ `β·((1/β)·r) == r`（`real_mult_assoc` + `real_inv_pos_correct` + 1·r）→ `real_plus_comm` 完成。零新增公理、纯构造性。

**定理 5.10**（`dpo_loss_iter_step_le` / `dpo_loss_iter_mono`）：**聚合损失 `dpo_loss` 沿策略改进轨道单调不增**——把 DPO 从"π* 处损失有界"升级为"沿改进轨道损失动态单调"：
```
le (dpo_loss (pi_next pi_t pi_t_pos)) (dpo_loss pi_t)        （单步）
le (dpo_loss (projT1 (policy_iterate (S t) pi pi_pos)))
   (dpo_loss (projT1 (policy_iterate t pi pi_pos)))          （迭代轨道）
```
即沿相对 Boltzmann 改进算子 `pi_{t+1} := pi_next pi_t`（定理 4.5 的策略迭代），聚合损失（`dpo_loss := opp (align_objective)`）单调不增——与定理 4.7（间隙单调）互为对偶：`policy_improvement_mono` + `opp_le_compat` 一步组装，迭代版经 `policy_iter_norm` 保持归一化后逐点应用。零新增公理、纯构造性。

**定理 5.11**（Real 层 DPO logit 损失形状族）：单样本 DPO 损失 `ℓ(x) := −log σ(x)`（`real_dpo_logit`）的构造性形状刻画：

1. **softplus 连接**（`real_softplus_sigmoid_eq`）：`−log σ(x) == log(1+e^{−x})`——BT 损失与 softplus 形态的机器检查恒等（inv 对合 + `log(inv x) == −log x` + log 等价替换组装）；
2. **二阶导正性证据**（`real_sigmoid_deriv_mass_pos`）：`σ(x)·(1−σ(x)) > 0`——经典二阶导 `σ(1−σ)` 的构造性正性（`σ(x) > 0` 与 `1−σ(x) > 0`正乘）；
3. **损失严格单调**（`real_dpo_logit_loss_decr`）：`x < y ⟹ ℓ(y) < ℓ(x)`——偏好 logit 越强损失越低（sigmoid 严格增 + log 严格增 + 取负反序），DPO 梯度下降收敛论证的单调前提。

边界说明：完整 t-参数化凸性（Young/加权 Jensen）需要非 eps 的 `(a−b)² ≥ 0`（构造性边界：实数上三分不可判定）与 log 的 eps-连续性——二阶导正性证据与严格单调已机器检查闭合。零新增公理、纯构造性。

### 5.3 对齐审计与安全投影：审计 = KL 投影

贡献 3 把 DPO 恢复定理族定位为对齐审计的测量基座（DPO 隐式奖励是真实奖励的仿射像，定理 5.4/5.5）。本小节把审计的**作用形式**定理化：对策略分布做布尔安全过滤（拒绝集置零）+ 通过集上重归一化，恰为到通过分布的 **KL 投影**（该构造的经典对应是 Csiszár 的 I-投影理论[33]——最小判别信息问题即把分布投影到凸集上，本文在此给出了同一构造在构造性 Set 层编码下的机器检查版本）——机器检查主定理 `projected_distribution_minimizes_kl` 于库内 `Section KLProjection`（L95420 起；215/216/217/218/219 基底逐字未动，行号）。本小节定理族的 **req 系消费版已随迁移第三阶段交付**（KLProjection req 簇，四项验证通过；见 §9.1.1 状态表）——投影主定理与 KL 代价分解在 req 系 setoid 签名下直接可消费（两层口径照旧：正文不消费、见 §9.1.1）。

**定义**（`Section KLProjection`）：安全过滤器为布尔谓词 `post_aud : S -> bool`（`true` = 通过）。给定参考分布 `p`（归一化 `Hp_norm`、逐点正 `Hp_pos`），通过集质量为
```
Z_aud := Σ_s (if post_aud s then p s else zero)              （L95442）
```
（`HZ : lt zero Z_aud` 保证通过集质量严格正），审计输出（投影分布）为
```
projected_distribution(s) := if post_aud s then mult (p s) (inv_pos Z_aud HZ) else zero   （L95446）
```
——在通过集上按 p 重归一化、在拒绝集上置零。库内已证：`projected_normalized`（投影分布归一化）、`Z_aud_le_one`（通过集质量 ≤ 总质量 1，p 归一化时 ≤ 1）。

**审计投影主定理**（`projected_distribution_minimizes_kl`）：对任意与审计兼容的分布 `q`（归一化 `Hq_norm`、逐点正 `Hq_pos`，且 `Hq_fail : forall s, Id (post_aud s) false -> Id (q s) zero`——q 在拒绝集上质量为零），只要 `HlogZ : le (log Z_aud) zero`：
```
le (relative_entropy q projected_distribution) (relative_entropy q p)
```
即 `KL(q‖proj(p)) ≤ KL(q‖p)`——审计不增加任意兼容分布 q 到 p 的 KL 代价（且按下方分解，在 `Z_aud < 1` 的意义下严格减少）。

**精确分解（审计的信息成本）**（`kl_sum_split`，L95527 + `kl_tail_eval`；`kl_minus_split`（`a−c == (a−b)+(b−c)`）为证明中的通用 R 层恒等式）：同一前提组下
```
relative_entropy q p == relative_entropy q projected_distribution + opp (log Z_aud)
```
即 `KL(q‖p) == KL(q‖proj) + (−log Z_aud)`——审计的 KL 代价恰等于通过集质量亏损的对数：`Z_aud ≤ 1`（`Z_aud_le_one`）且 `log Z_aud ≤ 0`（`HlogZ`）时 `−log Z_aud ≥ 0` 为审计的信息成本（通过集越小、被拒质量越多，成本越大）。

**注记**：
- `HlogZ : le (log Z_aud) zero` 为定理**显式前件**（定理语句未改）。消解路线已闭合（219）：`Z_aud_le_one`（+ p 归一化 ⟹ `Z_aud ≤ 1`）+ log 单调 le 版（`real_log_le_mono` 已在库内证明：lt 支 `real_log_lt_mono` / eq 支 `real_log_wd` 逐支组装）+ `real_log_le_zero_of_le_one`（`Z ≤ 1 ⟹ log Z ≤ 0` 的直用形态）——见 §10.2 第 1 项 (e)；
- `Hq_fail` 语义须显式：主定理对**与审计兼容**的 q 成立（q 不含被拒质量），不声称无条件成立；
- 可选蓝图 `free_energy_with_audit_decomp`（把审计接入 §8 统一自由能视角的分解：`F[proj] == F[p] + (−log Z_aud)` 型）未实现（代码注释原文），列 §10.2 第 1 项 (e)；
- **DPO 审计桥**：定理 5.4/5.5（隐式奖励 = 真实奖励的仿射像）+ 本小节投影定理 ⟹ 对 DPO 模型执行安全过滤等价于对其隐式奖励诱导分布做 KL 投影——「DPO 恢复定理（审计的测量基座）+ KL 投影定理（审计的作用形式）」构成贡献 3 的双定理结构。

**Real 层实例面（追加模块层注记；本文正文定理不消费）**：库内另有本节定理族的 Real 层实例化模块——`UpAuditBridge`（27 处 Qed（`^\s*Qed\.` 宽口径），经内核校验）提供 `real_minp_kernel_is_projection`（`UpAuditBridge.v:L564`，Min-P 截断核 == 到通过集的 KL 投影）、`real_minp_kl_cost`（`UpAuditBridge.v:L1017`，截断侧恒等 KL(minp‖full) == −log Z_aud）与 `real_minp_projection_eps`（`UpAuditBridge.v:L1068`，投影侧不等式：对与截断兼容的 q——被截集上质量为零，`Hq_fail` 同款语义显式——KL(q‖minp) ≤ KL(q‖full) + eps，精确分解同型为 KL(q‖p) == KL(q‖minp(p)) + (−log Z_kept)）；`UpMinP`（31 处 Qed（`^\s*Qed\.` 宽口径））提供截断的熵刻画 `entropy_ge_neg_log_p_max`（`UpMinP.v:L728`）与弃置质量界 `dropped_le_one_minus_exp_neg_S`（`UpMinP.v:L830`，dropped ≤ 1 − e^{−S}）、`dropped_le_one_minus_inv_n`（`UpMinP.v:L895`）。上述 KL 方向与本节主定理一致；这些采样管道层实例不改变 §2.3 scoped claim，亦不构成本节定理的新证明。本节定理族的投影主定理模块化亦已在 220 追加层交付（论文正文不消费，scoped claim 不变）：模块 `UpProj`（32 处 Qed）——`proj_kl_cost`（精确代价恒等 `KL(q‖f) == KL(q‖Proj) + (−log ZK)`，与本节 `kl_sum_split` 同型、Hq_fail 前件同款显式）、`proj_normalized`、`proj_keep_ge`、`proj_minor_uncond`（minorization 无条件传送），并以实例回收收编三个截断对象（KV 逐出 / 安全过滤 / Min-P——主定理一次证明三处消费）；模块 `UpProjBPC`（17 处 Qed，依赖 UpProj）给出级联形态：`Z_compound_mul`（两级掩码配分函数乘法分解 Z₁₂ == Z₁·Z_c）、`proj_kl_chain`（KL 代价链可加 KL₁₂ == KL₁ + (−log Z_c)）与 `proj_cost_interval`（双侧代价区间）。与本节蓝图的关系：`free_energy_with_audit_decomp`（本节注记所列，仍未实现）的实现路径可改为该投影主定理——精确代价恒等的 Real 层替代承载已现（逐出实例另见模块 `UpEvictId`（14 处 Qed）：`eviction_db_breaking_zero`（破缺项恒为零）、`evicted_boltzmann_steady_exact`（截断核稳态方程精确式）、`eviction_partition_increment`；逐出核基座见 `UpKVEv`（11 处 Qed）六件）。

---

## 6 PPO 裁剪机制的静态结构性质（单步 Bandit 设定）：单侧分解、保守性与改进条件

**范围界定与本章定位**：**本章的定位是 PPO 裁剪机制的静态结构性质三定理（定理 6.8–6.10）**——在四族贡献中，本章不与 RLHF/DPO/GRPO 的目标理论并列为第四族（§1.2 贡献预告同此口径）：RLHF/DPO/GRPO 三章给出各自的目标理论定理族，本章给出的是裁剪代理目标的组合结构性质（精确分解、clip 误差非负、裁剪代理非负蕴含价值改进），其实质篇幅在四族中相对较小，价值在裁剪安全性的非平凡形式化与前提显式化。本章是 PPO 裁剪机制的抽象（结构）形式化，而非工程 PPO 算法的端到端验证；章名取「静态结构性质」意在避免读者期待 Schulman et al. 式单调改进定理的端到端版本。其边界有三：其一，代理目标与保守性定理对任意符号的优势函数成立（保守性指 clipped surrogate ≤ IS surrogate 的逐点上界性质，非统计学含义；定理 6.7 虽无前提、但其级别为定义性平凡推论，见 §6.2 的注记），改进条件定理（6.3/6.4）则把步长可接受性化为 KL 惩罚的显式充分条件；其二，全部求和均在有限状态空间上精确进行，不含采样与 minibatch 估计误差；其三，重要性比率的分子固定为 `pi_star`（"单步向最优策略靠近"的受限设定），策略参数空间上的迭代优化不在本章范围内（见 §10.2）。本章的实质主结果是 §6.3 的三件单侧组合定理（定理 6.8–6.10：IS 目标的精确分解、clip 误差非负、裁剪代理非负蕴含价值改进）；三条边界的精确形态如下：

**边界声明一（代理目标形式）**：库内采用 `min(r, clip(r)) · A` 形式，而非标准 PPO 的 `min(r·A, clip(r)·A)`。区别在于 `min` 与优势 `A` 的运算次序：标准形式对任意符号的 `A` 均满足保守性；本形式在 `A < 0` 时不等号会反转。

**边界声明二（优势非负前提）**：库中 `advantage_nonneg : forall s, le zero (advantage_fn s)`是显式声明的 Section 变量，定理 6.1 在该前提下成立，此时 `min(r, clip(r))·A` 与标准形式等价。实际 PPO 中优势函数可取负值，因此本定理刻画的是**优势非负的受限设定**，不是一般 PPO 的保守性。

**边界声明三（比率分子）**：`importance_ratio`的分子是 `pi_star`，而不是标准 PPO 中可优化的当前策略 `pi_new`（后者在本库中未定义）。这是「单步向最优策略靠近」的受限设定，代理目标在给定 `pi_star` 下为常量；本工作不形式化策略参数空间上的迭代优化。

### 6.1 定义

PPO 在单步 bandit 设定下使用重要性采样比率：

```coq
(* L19502 *)
Definition importance_ratio (s : S) : R :=
  mult (pi_star s) (inv_pos (pi_old s) (pi_old_pos s)).

(* L19506 *)
Definition clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (minus one epsilon).

(* L19510 *)
Definition ppo_objective : R :=
  sum_over_S (fun s => mult (pi_old s)
    (mult (min (importance_ratio s) (clip (importance_ratio s))) (advantage_fn s))).
```

未裁剪 IS 目标为：

```coq
(* L19515 *)
Definition is_objective : R :=
  sum_over_S (fun s => mult (pi_old s)
    (mult (importance_ratio s) (advantage_fn s))).
```

另库内定义 `advantage pi s`（以给定策略计算的优势），与 Section 变量 `advantage_fn`不同；定理 6.2/6.3/6.5 使用前者。

### 6.2 核心定理

**定理 6.1**（`ppo_conservative`）：在 `advantage_nonneg`（即 `forall s, le zero (advantage_fn s)`）与 `pi_old_pos` 下，
```
le ppo_objective is_objective.
```

**证明概要**：对每一点，由 `min_le_l` 得 `min(r, clip(r)) ≤ r`；由 `advantage_nonneg` 与 `pi_old_pos` 知乘因子非负，故逐点保序；再由 `sum_over_S_le` 提升为全局不等式。

（上述结论在 `advantage_nonneg`下成立，该前提由 `End Section` 自动泛化为定理前件。）

**定理 6.2**（`exact_improvement_identity`）：
```
Id (minus (align_objective pi_new) (align_objective pi_ref))
   (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
          (mult beta (kl_to_ref pi_new))).
```

该恒等式将真实对齐目标改进分解为期望优势减去 KL 惩罚。

**定理 6.3**（`ppo_monotonic_improvement`）：若代理优势非负，即
```
le zero (minus (sum_over_S (fun s => mult (pi_new s) (advantage pi_ref s)))
            (mult beta (kl_to_ref pi_new)))
```
则 `align_objective pi_ref ≤ align_objective pi_new`。

**证明概要**：应用 `exact_improvement_identity` 将真实改进替换为代理优势，再利用代理优势非负得到结论。

**定理 6.4**（`kl_penalty_sufficient`）：若 `KL(pi_new‖pi_ref) ≤ eps` 且 `E_{pi_new}[A_ref] ≥ beta·eps`，则策略改进成立。该定理给出了 PPO 步长可接受的一个充分条件。

**定理 6.5**（`ppo_surrogate_raw_is_value_improvement`）：裁剪代理目标的改进与真实对齐目标改进满足显式恒等关系，即代理目标优化可直接控制策略价值改进。

**定理 6.6**（`real_ppo_conservative_eps`）：PPO 保守性的 **Real 层复刻（eps 化）**——柯西实数层裁剪代理目标不超过未裁剪目标加 eps 加权残差：
```
real_le (real_sum_over_S (fun s => real_mult (real_pi_old s)
                                   (real_mult (real_min (real_importance_ratio_ s) (real_ppo_clip_ (real_importance_ratio_ s))) (real_advantage_fn s))))
        (real_plus (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult (real_importance_ratio_ s) (real_advantage_fn s))))
                   (real_sum_over_S (fun s => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))).
```
即 `ppo_objective ≤ is_objective + Σ π_old·(eps·adv)`——eps 加权残差形态：Real 层 `real_min` 只有 eps 界（`real_min_le_l_eps`），无精确 `min ≤ r`，构造性边界注记。**完成状态注**：本定理 eps 形态与精确形态的关系同定理 4.9（§9.4 例二：Or 形完成不可达；Bishop 形完成可达但需残差权系数 `E := Σ π_old·adv` 的显式正性证书，`E == 0` 与 `E > 0` 情形构造性不可分——见 §9.4 例二 (iii)）；已实现（独立模块 `UpRealLeB.v`，四项验证通过，§10.2 第 1 项 (g)）：本定理的 Bishop 形对应物 `real_ppo_conservative_B` 为**条件升格**——残差权系数 `E := Σ π_old·adv` 在接口面无内在正性供给链（`E == 0` 与 `E > 0` 构造性不可分，§9.4 例二 (iii)），对应物语句补 `E > 0` 显式证书前提（该模块唯一新增前提）；无证书情形本定理维持 eps 形陈述不变（Or 形「精确版」不可达，§9.4 例二 (i)/(iv)）。**req 面对照**：本定理族的 req 版已随最终裁决交付（`rpl_ppo_surrogate_conservative`，`UpReqPPOPlain.v`，plain-le 接口路径），原 setoid `min` 冻结因经 `ReqDiffPlain` 接口扩展解除——本定理在柯西实数上的 req 系消费与 Real 层逐 eps 复刻路径并存。

**证明概要**：逐点 `min ≤ ρ+eps`（eps 界）→ ×adv（strict 正乘 `real_le_mult_compat`，前提 `real_advantage_pos`）→ 右分配（`real_mult_comm` + `real_distrib` 链）→ ×π_old（strict 正乘 + comm 换形）→ Σ 保序（`real_sum_over_S_le` 接口）→ `real_sum_over_S_add` 拆项 + ext（`real_distrib` 逐点）完成。诚实接口（零公理）：`real_sum_over_S_ext/le/add` + `real_advantage_pos`/`real_pi_old_pos`。

**定理 6.7**（`std_ppo_conservative`）——定义性后承（定义备注口径；分量定位见 §9.6）：标准 PPO 代理目标 `std_ppo_objective := E_pi_old[min(r·A, clip(r)·A)]`（标准形式）满足
```
le std_ppo_objective is_objective.
```
该结论**无需 `advantage_nonneg`**，但其数学内容是空的：`min(rA, clip(rA)) ≤ rA` 是 `min_le_l` 的定义性直接推论（min 恒不超过第一参数），既与优势符号无关，也未用到 `clip` 的任何结构（`clip` 换成任意函数结论仍成立）——故边界声明一（代理目标形式非标准）并未由此获得实质消除；标准形式与 §6.1 的非标准形式并存：前者无前提但属定义性后承，后者需 `advantage_nonneg`（定理 6.1）。本定理不计入并列贡献，列此仅为命名对应与定理 6.8–6.10 的对照基线。**可达性澄清（Or 编码语义）**：本结论在抽象层可达，是因其证明仅消费接口字段 `min_le_l`（A 类字段，由接口直接供给），无需在实数层构造 Or 序分支见证；实数层的对应精确形（`real_min_le_l` 的 Or 形）不可达、eps 形已证（定理 6.6 与 §9.4 例一），两层口径不同、互不矛盾。库内同时具备：带自由变量 `pi` 的标准形式代理 `ppo_surrogate`（分子任意策略）、其保守性 `ppo_surrogate_conservative` 与未裁剪对照封装 `is_objective_of`——定理 6.8–6.10 的陈述即以 `ppo_surrogate`/`is_objective_of`/`clip_error` 为对象。

### 6.3 裁剪机制的单侧分解定理（本章主结果）

本章的实质主结果是以下三件单侧组合定理（Section `PPOClipDecomp`）：它们把「裁剪代理」与「价值改进」之间的通道以**单侧**形式机器检查闭合——「裁剪代理非负 ⟹ 价值改进」才是 PPO 裁剪机制安全性的非平凡形式化（对照：定理 6.7 的无前提保守性为定义性后承，见 §6.2 注记）。

**定理 6.8**（`ppo_is_decomp`）：IS 目标的**精确分解**（无前提恒等式）——未裁剪 IS 目标 `is_objective_of` == 裁剪代理 `ppo_surrogate` + clip 误差 `clip_error`（逐点 `u == min(u,c) + (u − min(u,c))` 拆分 + `sum_over_S_add`；无优势符号前提）。

**定理 6.9**（`clip_error_nonneg`）：**clip 误差非负**（min 在乘积内部，**无优势符号前提**）。

**定理 6.10**（`ppo_clipped_improvement`）：**裁剪代理非负 ⟹ 价值改进**——若裁剪代理 `ppo_surrogate` 非负，则 `V(p_old) ≤ V(pi)`（组装：定理 6.8 + 定理 6.9 + 未裁剪 IS 恒等 `V(pi) − V(p_old)`（定理 6.5）+ 序代数）。

三件合取即「裁剪代理 + 保守性 + 改进条件」的**单侧**形态：定理 6.8 给出精确账目（IS 目标被裁剪代理与 clip 误差无剩余地分摊）、定理 6.9 给出误差符号、定理 6.10 给出安全含义——三件齐备的**单侧**闭合由此在库内完成（Section `PPOClipDecomp` 自 L112330、三件声明 L112398–L112439）。

**边界说明（单侧闭合；反向不可闭）**：**反向界维持不宣称**：不存在常数 C 使「价值改进 ≤ 裁剪代理 + C·eps」型上界成立——比率无界（ρ → ∞）时 clip 误差 `A·(ρ − 1 − ε)` 无界（经典反例，源模块头注原文）。改进条件定理（6.3/6.4，对象为 `align_objective` 的改进，路线经 `exact_improvement_identity`）与裁剪代理之间的组合通道由定理 6.8–6.10 单侧接通；端到端策略参数空间迭代不在本章范围（见范围界定与 §10.2 第 2 项）。零新增公理、纯构造性。

**PPO 裁剪代理的两种形式与保守性定理覆盖范围（示意图，对应 §6.1 定义与定理 6.1/6.7）**（排版批注：LaTeX 化时本 ASCII 示意图改为两列对照表或 TikZ 图，内容与行号锚不变）：

```
设 r(s) := importance_ratio(s)（L19502，分子为 π*），clip(r) := r_max (min r (1+ε)) (1−ε)（L19506），
A := advantage_fn（L19496）。逐点形式：

非标准形式（库内 ppo_objective，L19510）        标准形式（库内 std_ppo_objective，L19553）
    min(r, clip(r)) · A                            min(r·A, clip(r·A))
        │                                              │
        │ 需 advantage_nonneg（A ≥ 0，L19497）        │ 无需 A 的符号前提（min 在乘积内部）
        ▼                                              ▼
定理 6.1 ppo_conservative（L19526）            定理 6.7 std_ppo_conservative（L19559）
  ppo_objective ≤ is_objective                     std_ppo_objective ≤ is_objective
  （前提：A ≥ 0 且 π_old > 0）                      （无前提；min_le_l 定义性直接推论）
```

**覆盖注**：定理 6.1 覆盖**非标准形式**（§6.1 的 `min(r, clip(r))·A`，需优势非负前提）；定理 6.7 覆盖**标准形式**（`min(r·A, clip(r·A))`，无前提——但属定义性后承，见 §6.2 注记），二者均以未裁剪 IS 目标 `is_objective`为上界，即「裁剪代理 ≤ 未裁剪代理」的保守性。定理 6.1 与 6.7 的保守性本身**不**覆盖裁剪代理上的改进条件——该缺口的**单侧**闭合由 §6.3 的定理 6.8–6.10 给出（`ppo_is_decomp`/`clip_error_nonneg`/`ppo_clipped_improvement`，已在库内证明）；改进条件定理（6.3/6.4）作用对象是真实对齐目标 `align_objective`（经 `exact_improvement_identity`），其与裁剪代理之间的组合通道现经定理 6.8–6.10 接通（单侧）。

**未覆盖区**：本示意图的未覆盖区 = 两列定理（6.1/6.7）的保守性覆盖之外、裁剪代理与价值改进之间的区域——其**单侧**半边已由定理 6.8–6.10 闭合（裁剪代理非负 ⟹ 价值改进，见 §6.3 与覆盖注）；**反向**半边（价值改进 ≤ 裁剪代理 + 常数·eps 型上界）在无界比率设定下为假（反例：ρ → ∞ 时误差无界），维持不宣称——该区未全覆盖是数学事实而非可闭缺口，与零新增公理、纯构造性的纪律一致。

---

## 7 GRPO：组相对优势的统计量

### 7.1 定义

GRPO 对同一问题采样一组输出 `Group`，奖励函数为 `reward_group : Group -> R`，组大小为 `group_size`，组均值为：

```coq
Definition group_mean : R :=
  mult (inv_pos (of_nat group_size) group_size_pos)
       (list_sum_g reward_group group_enum).
```

组相对优势定义为：

```coq
Definition grpo_advantage (i : Group) : R :=
  minus (reward_group i) group_mean.
```

**枚举假设（显式列出，`Section GRPO`）**：本节全部定理依赖以下 Section 变量与定义——`Group : Set`；`group_enum : list Group`；`group_cover : forall i : Group, InT i group_enum`（覆盖）；**`group_size` 定义为 `length group_enum`**（非独立假设）；`group_size_pos : lt zero (of_nat group_size)`；`reward_group : Group -> R`。两点诚实说明：其一，`NoDup group_enum` 当前**未**假设——若枚举含重复元素，组均值按列表计权（无重复前提的**不可去性**已机器检查定理化，见 §7.2 定理 7.2/7.3——本章主结果），均匀均值解读即失效；把组均值解读为 `Group` 上的均匀均值需补无重复假设。该前提的计数刻画与均匀均值定理已在根完成——词表计数机器族（`count_token`/`removeT`/`split_count_one` 等，对元素类型完全泛型——仅依赖可判定相等与 list 归纳）平移至 GRPO 枚举 + Set 层无重复前提（`nodup_g`）后的三件均匀均值定理已在库内证明：`UpGRPO219.grpo_count_one`（覆盖 + 无重复 ⟹ 每元素恰计一次）、`UpGRPO219.grpo_indicator_sum_one`（indicator 求和 == 1）与 `UpGRPO219.grpo_uniform_mass`（组均值中每 delta_j 的质量恰为 1/G）。其二，实际 GRPO 常用标准化优势 `A_i = (r_i − mean)/std`；本节零均值定理对任意常数缩放成立（可取 `c = 1/std`）。population-std 下 `(1/G)·Σ A_i^2 = 1` 的单位二阶矩**全装配尚未在库内实现**（开放计划，精化项）；其构造性 σ 见证核心已在库内证明——`real_sqrt_exists`（`forall d, real_le real_zero d -> sigT (fun r => And (real_le real_zero r) (real_eq (real_mult r r) d))`，经 `exp(½·log d)` 拼装，Or 前提左支携带正间隙证书、右支给 r := 0 精确相等）使 σ := √Var **可构造**：σ sigT 见证 `UpGRPO219.real_sigma_witness`（`0 < σ ∧ σ² == Var`）与投影 `UpGRPO219.proj_sigma`/`proj_sigma_pos`/`proj_sigma_sq`（L113948/L113953/L113961）已在库内，σ > 0 的正性证书与除法所需正性衔接由 sqrt 的 Or 形态供给（单位矩精化装配见 §10.2 第 1 项 (c)）。

### 7.2 核心定理

本章的编排以**前提不可去性的机器检查反例（定理 7.2/7.3，本章主结果）**居先、组统计量恒等式（定理 7.4–7.6，初等代数）随后的次序呈现——GRPO 章区别于教科书推演的实质内容是前者：形式化在此暴露了一个纸笔陈述通常隐去、且在部署中真实存在的隐藏前提（组枚举无重复），并机器检查了该前提的不可去性。

**定理 7.1**（`grpo_advantage_zero_mean`）：对任意缩放因子 `c`，
```
Id (list_sum_g (fun i => mult (grpo_advantage i) c) group_enum) zero.
```

**证明概要**：求和线性化后，`Σ(r_i − μ) = Σr_i − group_size·μ`；代入 `group_mean` 的定义并化简 `group_size·inv_pos(group_size)=1`，得到 `Σr_i − Σr_i = 0`。

注意定理 7.1 的零均值**不依赖**枚举无重复（重复元素在差分中成对抵消），但把 `group_mean` 解读为 `Group` 上的**均匀均值**（每个元素权重恰为 1/G）则依赖 `NoDup group_enum`——该前提的不可去性由以下两件机器检查反例定理化：

**定理 7.2（本章主结果）**（`UpExtras219.counter_ex_indicator_sum_two`）：**无重复前提不可去性反例（indicator 求和）**——对同一元素的**双副本枚举**（`Group` 中每个元素在 `group_enum` 中出现两次，覆盖前提 `group_cover` 仍成立），indicator 求和给质量 **2 ≠ 1**：即「每个元素在组均值中的质量恰为 1」在无 `NoDup` 前提下**为假**，且该失效已被构造性否证固定为库内定理（非口头注记）。

**定理 7.3（本章主结果）**（`UpExtras219.counter_ex_reward_sum_two_c`）：**无重复前提不可去性反例（常数奖励总计）**——同一双副本枚举下，常数奖励 `c` 的列表总计为 **2c ≠ c**：即「组均值 = 算术平均」的均匀均值语义在无 `NoDup` 前提下系统性加倍失效。

两件反例与正向均匀均值定理三件（`UpGRPO219.grpo_count_one` / `grpo_indicator_sum_one` / `grpo_uniform_mass` L113832，覆盖 + 无重复前提下每元素恰计一次 ⟹ indicator 求和 == 1 ⟹ 每 delta_j 质量恰为 1/G，见 §7.1）合取，完整刻画了 `NoDup` 前提的双侧边界：**有此前提则均匀均值成立、无此前提则均匀均值失效，两个方向均为机器检查定理**——这是形式化"暴露隐藏假设"价值的直接体现（库内登记见 §10.2 第 1 项 (b)）。本小节为论文级前置呈现，定理陈述与行号锚照库内实录，零新增机器检查断言。

**定理 7.4**（`grpo_variance_identity`）：**中心二阶矩恒等式**（组内平方偏差和 `Σ_i (r_i − μ)^2`，**未除以组大小 G**，故按下方术语说明不称"方差"——"方差"一词保留给归一化版本 `group_variance_identity`，见定理 7.5 与术语说明）：
```
Id group_centered_second_moment
   (minus group_raw_second_moment
          (mult (of_nat group_size) (mult group_mean group_mean))).
```

即：
```
Σ_i (r_i − μ)^2 = Σ_i r_i^2 − G·μ^2.
```

**术语说明**：标识符仍命名为 `grpo_variance_identity`，但严格而言本定理是**中心二阶矩恒等式**（或平方和恒等式），因为库内 `group_centered_second_moment`定义为 `list_sum_g (fun i => mult (grpo_advantage i) (grpo_advantage i)) group_enum`，**未除以组大小 G**，故不是方差恒等式。**归一化版本亦已实现**：库内另有 `group_variance := mult (inv_pos (of_nat group_size) group_size_pos) group_centered_second_moment` 及其恒等式 `group_variance_identity`（Var == (1/G)·Σr² − μ²，由 `grpo_variance_identity` 两侧乘 inv(G) + `mult_minus_distr_l` 分配 + `inv_G_absorb` 消去推导，零 `Admitted`/`admit`（审计口径含小写）、纯构造性）。

**证明概要**：逐点展开 `(r−μ)^2 = r^2 − 2rμ + μ^2`（约 20 步构造性代数链，库内引理 `grpo_square_expand`），求和线性化，交叉项 `Σ r_i` 用零均值性质消去，最终合并为 `−G·μ^2`。

**定理 7.5**（`group_variance_le_raw_second_moment`）：**基线方差归约**——归一化组方差不超过原始二阶矩均值：
```
le group_variance
   (mult (inv_pos (of_nat group_size) group_size_pos)
         (group_raw_second_moment)).
```
即 `Var ≤ (1/G)·Σ r_i²`，归约量恰为 `μ²`（`group_variance_identity` 中 Var == (1/G)·Σr² − μ² 与平方非负 `square_nonneg` 组装）；这形式化了 GRPO 的核心动机"**组相对优势（减均值）降低二阶矩**"。

**证明概要**：`group_variance_identity` 给出 Var == (1/G)·Σr² − μ²；`grpo_le_minus`（0 ≤ b ⟹ a−b ≤ a，自证辅助）把减项消去；`square_nonneg` 为诚实接口 Variable（构造性有序域无三分律，通用平方非负需接口字段，同 NaturalGradient 模式），等号情形（组均值为零）未单独定理化。另注：正向 eps 形式 `real_square_nonneg_eps`已在 Real 层证明（`Qsquare_nonneg` 逐点成立 + 极限保 eps 余量），可作为该假设在 Cauchy 实数上的正向 discharge 证据。零经典、纯构造性。

**定理 7.6**（`real_grpo_advantage_zero_mean`）：组相对优势零均值的 **Real 层复刻**——柯西实数层：
```
real_eq (real_list_sum_g (fun i => real_mult (real_grpo_advantage i) c) group_enum) real_zero.
```
即 `Σ_i (r_i − μ)·c == 0`（对任意缩放 c）——抽象层定理 7.1 的 Real 值域版（`real_grpo_advantage`/`real_group_mean` 定义于 RealGrpoMain Section）。

**证明概要**：`Σ(r_i − μ) == Σr − Σμ`（`real_list_sum_g_minus`）→ `Σμ == G·μ`（`real_list_sum_g_const`，G := length group_enum）→ `G·μ == Σr`（`real_mult_assoc` + `real_inv_pos_correct` 吸收 G·(1/G) == 1 + 1·Σr 换形）→ `Σr − Σr == 0`（`real_plus_opp`）→ 主链（`real_mult_comm` 换序 → `real_list_sum_g_linear` 提取 c → `real_mult_zero` 完成）。基础设施：`real_of_nat`（nat→Real 嵌入）+ `real_list_sum_g` 族（ext/add/linear/opp/minus/const 六引理，归纳组装）+ `real_distrib_r_local`（右分配自证，避前向引用）。诚实接口（零公理）：`Group` 有限集 + `group_enum` + `group_cover`（InT 枚举覆盖）+ `real_group_size_pos` + `reward_group`。

**GRPO 簇的 setoid 签名版（签名迁移迁移第二阶段交付）**：GRPO 簇 14 件的 setoid（req 系）签名版已在模块 `UpReqDist`（ReqGRPO 节，与 Id 原件逐位对位）交付——`req_grpo_advantage_zero_mean`/`req_grpo_variance_identity`/`req_group_variance_identity`/`req_group_variance_le_raw_second_moment` 等；其中归约定理的 req 版经 Real 层正向 eps 证据桥承载，`square_nonneg` 保持抽象层出口假设位同构。本节定理（7.1–7.4）的 req 系签名版已随阶段三交付（五批主体闭合，见 §9.1.1）；两套签名并存期为逐位对应的重述、假设位同构，不构成新增数学主张。

---

## 8 统一视角：对齐即自由能最小化

四个算法族可纳入同一自由能框架：
- **RLHF**：最大化 `E_π[r] − β·KL(π‖π_ref)`，等价于最小化以 `−r` 为能量的自由能；最优解为 Boltzmann 分布。
- **DPO**：负对齐目标作为损失，隐式奖励恢复定理保证其最优解与 RLHF 一致。
- **PPO**：在参考策略附近用代理目标近似真实对齐改进，裁剪保证保守性，KL 惩罚保证改进条件。
- **GRPO**：组相对优势的零均值与中心二阶矩恒等式为基线估计提供无偏性与二阶矩控制。

库内定理 `rlhf_free_energy_kl`将 RLHF 目标显式连接到自由能-KL 分解，构成统一视角的数学锚点。

---

**签名迁移方法论**：把抽象 Id 签名陈述迁移到 setoid/req 实例签名，方法由等价重述、复刻与对账引理三件套构成；无损性由编译期 reflexivity 对账引理机器化保证。签名迁移总清单 734 条：670 条已交付，64 条为设计性冻结双层并行条目；交付条目均通过全量编译、行首禁词零命中与 coqchk，81 条主定理/主定义另经 Print Assumptions 批量审计（分层口径见 §9.1.1 与补充材料 S2/S4）。边界：statement-level 机器对齐仍开放，逐条账目见补充材料 S2。
## 9 形式化边界与前提

### 9.1 接口假设与实例化状态

**教训定位（本节与 §9.5 的方法论结论，先于一切账目给出）**：下文的迁移工程账目，其可迁移的方法论结论不是进度数字，而是一条设计教训——**初版以 Leibniz `Id` 陈述的定理族与柯西实数的 setoid 本性不兼容：凡以 `Id` 陈述含实数等式的定理都无法在构造性实数上实例化，setoid 陈述应在库的第 0 天选定**。签名迁移本身（等价重述、复刻与对账引理三件套，§1.2）是对这一初始设计决策的系统化事后补救；本文据此把它定位为教训与经验报告，而非核心方法论贡献。与之同根的第二个教训是序编码（§3.6）：`real_le` 的 Or 形选择决定了哪些精确结论在 Real 层不可达、eps 税落在哪里——序与相等的编码都是库级一次性决策，选定前应先确认目标实例的谓词形态（完整复盘见 §9.5）。

**信用结构说明（一次性声明；后文各处不再反复自设边界）**：本文正文定理的证明信用**完全自持于 §9.1.1 登记的 219 内容锚**——正文定理的陈述与证明不消费任何追加层模块。模块层（`UpGRPO219`/`UpExtras219`/`UpReqDist`/`UpReqTempEntropy`/`UpReqAlign`/`UpStepKLM3` 等）与签名迁移各批提供的是**状态证据与对接路径**，而非正文证明依赖：诚实接口的 Real 层真值证据（定理 4.8 状态脚注）、req 前件簇的签名对应物（迁移第二阶段，见 §3.3/§4.3/§7.2）、GRPO 前提不可去反例与 NoDup 均匀化三件（§7.2 定理 7.2/7.3 及其 discharge）、σ 见证族、迭代族 Real 层同型镜像等——均为独立模块形态、经内核校验在案，供核验与迁移消费。读者信任链条此一次性说明后，正文各处「模块形态、正文不消费」的局部标注均可回溯本段。


本形式化依赖以下 `Variable`（诚实接口假设；**A/B/C 类打标**：按下文 §3.4 的编码给每项假设标注——A 类=接口字段（`RealInterfaceEnhanced` Class 字段）、B 类=Section 局部假设（待证明/discharge）、C 类=已证定理（该假设若已由 Real 层证据消解即入 C 类；可消解候选与已消解证据在条内注明）；下列清单以 A/B 类为主，C 类为各假设的消解状态，均在正文与 §9.2 标注）：
- `reward : S -> R`，`pi_ref : S -> R` 及其正性（`pi_ref_pos`，L18757）、归一化（`pi_ref_norm`，L18758）〔B 类：Section 局部假设，Real 层逐 eps 复刻时逐一实值化〕；
- `beta_pos : lt zero beta`（L18755）、`Z_align_pos : lt zero Z_align`（L18764；注：`Z_align_pos` 与 Real 层对应假设均为 Variable（Real 层 `Z_align_pos`（L42308））〔B 类：Section 局部假设；可消解候选（C 类方向）：同形状的 `Z_rel_pos`（L21253）路径表明，`Z_align_pos` 可由 `sum_over_S_pos` 型接口（L21245，Variable）与 `exp_neg_pos`（L182，接口字段）推出——即「消解」实为把该假设换成另一组接口假设，两假设的 Real 层实例化均待列表和正性回填（见 §9.1.1 的 exp_neg_pos 回填说明：exp_neg_pos 已回填，列表和正性未回填）〕；
- `exp_neg_pos` 接口字段（L182）等实函数正性〔A 类：接口字段；已消解（C 类证据）：`exp_neg_positive`（L1872）已在语言模型实例中证明；Real 层通用字段已由 setoid 系接口实例回填（`exp_neg_pos := cauchy_real_exp_pos`，L39450，见 §9.1.1）；
- `log_differentiable`（L26365）等实函数可微性假设〔B 类：Section 局部假设（诚实接口字段，Real 层解析证明待闭合，见 §9.1.1/§10.2）〕；
- **策略迭代族（§4.3.1，支撑定理 4.5–5.10 全体）**：`sum_over_S_pos`（L21245）、`eta`/`eta_pos`/`eta_le_one`（L21240–L21242）、`step_kl_eta_bound`（L23114；升级后唯一诚实接口，旧 `step_kl_ratio`/`step_kl_ratio_pos`/`step_kl_ratio_bound` 三件套已停用）〔均 B 类：Section 局部假设；`step_kl_eta_bound` 为唯一剩余诚实接口，其 Real 层对应定理已在库内证明（`real_interp_Z_le_one_eps` L112890 / `real_step_kl_eta_bound_eps` L113142 等，见定理 4.8 状态脚注）；其 req 系同位桥接件 `req_step_kl_eta_bound` 已随迁移第三阶段交付（假设位同位重述，见定理 4.8 假设地位标注）〕；
- PPO 中的 `pi_old`、`pi_old_pos`、`advantage_fn`（L19496）、`advantage_nonneg`（L19497）、`epsilon`（L19498）〔B 类：Section 局部假设〕；
- GRPO 中的 `reward_group`、`group_size_pos`〔B 类：Section 局部假设；`square_nonneg`（L24301）同列，Real 层正向证据 `real_square_nonneg_eps`（L44842）见 §7.2/§10.2 第 1 项 (f)；σ := √Var 的构造性见证核心已在库内证明——`real_sqrt_exists`（L96475）之上装配的 σ sigT 见证 `UpGRPO219.real_sigma_witness`（L113928）与投影三件（`UpGRPO219.proj_sigma`/`proj_sigma_pos`/`proj_sigma_sq`，L113948/L113953/L113961），见 §10.2 第 1 项 (c)〕。

这些假设对应于纸笔文献中通常默认的前提；显式声明它们是本库「诚实接口纪律」的一部分。

### 9.1.1 假设的封装方式

所有接口假设均以构造性方式封装，不构成隐藏公理：

1. `RealInterfaceEnhanced` 是 **Class**（L217），以 `Context {RI : RealInterfaceEnhanced}.` 引入（如 L347、L1285、L1456 等），不是顶层自由 `Variable`；
2. `End Section` 后 Coq 自动对 `RI` 泛化，接口字段成为定理的显式（隐式）前件；
3. 实证：Rocq 9.0/9.1 `Print Assumptions rlhf_optimal` 返回 **`Closed under the global context`**——零 Axiom、零未封装 Variable（对 `dpo_optimal`、`boltzmann_factor_pos`、`minp_markov_kernel_normalized` 审计结果相同）。

因此本工作的核心定理应读作：`forall {RI : RealInterfaceEnhanced}, <结论>`，即**对任意满足接口的实例成立**。

**接口与实例化**：本文定理在抽象接口 `RealInterfaceEnhanced` 上陈述。该接口的 setoid 对应物 `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid`（L40464，log 族带正性前提）已由具体柯西实数实例化为 `RealInterfaceEnhancedMod.RealEnhancedReal`（L41115），字段逐一取自 `Real` 层已证引理；同属 Setoid 系接口的基础版 `Real_RealInterfaceSetoidCore`（L33433）与完整版 `Real_RealInterfaceSetoid`（L39407）亦已装配（57 字段全实值）。**具体数学内容的 Real 层承载经两条路径实现**：其一是上述实例的字段回填（exp 族、log 族、度量与完备性全部实值化），其二是 **Real 层逐 eps 复刻**路径上对**部分核心定理**的直接证明（覆盖清单：定理 4.9、5.8、5.9、5.11 族、6.6、7.6——见 §1.2 贡献 7 与 §9.2；该路径上的 KL 不等式 `real_gibbs_inequality_eps`、log 可微性 `real_log_differentiable`、compose/entropy 可微性等是支撑复刻的 Real 层**基座引理**，而非核心定理镜像）——即本文抽象定理的数学内容在构造性实数上已有对应物。**可提取性**：全库定义均置于 Set 层：sigT/`And` 中的有理数序谓词一律使用 Set 值判定谓词 `QltT`/`QleT`，`And` 不实例化到 Prop；`real_mult`、`cauchy_real_exp` 等核心构造可提取为不含 Prop 残留的 OCaml 代码（提取验证在独立验证文件中完成）。本库使用自定义 Set 层合取 `And (A B : Set) : Set := A * B`（L68），非 Coq 标准的 Prop 层 `and`。**Artifact 与行号基底（细节见附录 D.9）**：单文件库 ConstructiveWorld.v（114,222 行，内容锚 SHA-1 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`）经 Rocq 9.1 编译通过、仅依赖 Coq stdlib；全库禁词扫描（`Axiom`/`Admitted`/`Abort`/`Classical_Prop.classic`）零命中（全量而非抽样；行首扫描取标准格式，禁词清单本体含 `Notation` 包装与模块级 `Parameter` 扩展面，禁词扫描的禁词清单与扫描命令随 artifact 提供于补充材料 S3），全部声明以 `Qed.`/`Defined.` 闭合（计数与审计口径、早期版本 SHA-1 清单、追加层块清单、验证面与提取验证状态：见附录 D.9）。**行号基底稳定性**：本文全部行号引用以本段登记内容锚为唯一基准（219 基线；模块化树维护形态下逐字节未动，见附录 D.9）。**单文件设计决策**：单文件形态保证零外部依赖与可审计的内容锚定（SHA-1），便于 artifact 复现与完整性核验；未来按语义边界的模块化重构在抽象层签名对接（§10.2 第 1 项）完成后考虑——与已实现的追加式工程模块化的区分见附录 D.9。

**220 起的维护形态（artifact 现状；模块拓扑、Qed 计数、Extensions 汇聚件、单文件拼接阻塞与未入汇聚件口径见附录 D.9）**：219 内容锚在模块化树中逐字节未动，本文行号引用零平移；追加式工程模块化 ≠ 「按语义边界切分基座」的重构 ≠ 定理级签名迁移（§10.2 第 1 项，已闭合）（两层口径不得混写）。

**当前库状态**：论文行号锚为 219 基线；artifact 当前为 ConstructiveWorld@39d81aa，编译清单 246 模块，Live_X 356 个 .v，CI 连续 success，认证面 246，各波 coqchk 全绿（CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；81 条 PA@198/206+维持面口径不变。Banach 推广与第八波 Strong 为范围外认证进展，不属本文四族贡献面。详表见补充材料 S1。**「内核校验通过」的断言强度（区分两档）**：本文现主张的「coqchk 全绿」指内核一致性校验通过，不等同于「全部常量的假设摘要为空」；后者要求对全部主定理在投稿冻结态重跑 `Print Assumptions` 并把假设摘要断言在 CI 固化——该固化随投稿冻结态执行（81 条的审计口径见本节上文与附录 D）。

`exp_neg_pos` 等字段的构造性实例化依赖正性链证明工作，其状态如下：

| 环节 | 状态 | 行号 |
| --- | --- | --- |
| `esq_eq_corr`（主恒等式） | **已证 `Lemma`** | L12837 → `Qed` L12868 |
| `exp_even_neg_pos` | 已证 | L12969 |
| `exp_partial_tail_pos` | 已证 | L13011 |
| `cauchy_real_exp_zero` | 已证 | L8348 |
| **`cauchy_real_exp_pos`（Real 层 exp 正性）** | **已证 `Lemma`** | L13383 |
| **setoid 系接口实例** | **已完成**：`Real_RealInterfaceSetoidCore`（L33433）/ `Real_RealInterfaceSetoid`（L39407）/ `RealEnhancedReal`（L41115），全部字段实值化（exp 族、log 族、度量与完备性） | L33433 / L39407 / L41115 |

即：该正性链全链（含 Real 层 `cauchy_real_exp_pos`）已闭合，为 `exp_neg_pos` 字段在具体 `Real` 上的实例化提供了完整的构造性材料；该字段经 setoid 系接口实例的字段回填（`exp_neg_pos := cauchy_real_exp_pos`，L39450）与 Real 层逐 eps 定理完成（见 §9.1.1 上文接口与实例化段，及正文定理 4.9、5.8、5.9、5.11 族、6.6、7.6 的 Real 层复刻）。

**Setoid 签名迁移的状态与影响**：本文定理的签名仍在抽象 Id 等式系接口 `RealInterfaceEnhanced`（Class，L217）上，其结论"对任意满足该接口的实例成立"（见本节上文）；`Real` 目前实例化的是 **req** 等式系 setoid 接口族（`Real_RealInterfaceSetoidCore`（L33433）/`Real_RealInterfaceSetoid`（L39407）/`RealEnhancedReal`（L41115），全部字段实值化），抽象定理与实例分属 Id/req 两套签名族的这一缝隙，已由签名迁移（§10.2 第 1 项）的五批主体闭合消除——已交付 670 件可经 `RealEnhancedReal` 直接消费；64 件冻结双层件不经 req 签名消费，其数学内容由 Id 层陈述与 Real 层逐 eps 复刻双层并行承载。

**签名迁移分批状态表（五批主体完成）**：setoid 代数地基、分布/自由能/温度层与对齐理论主体（§4–§7）均已交付；注意力/采样伴件与最终裁决亦已完成——迁移汇总清单共 734 条目：670 条已交付，64 条为设计性冻结的双层并行条目，无遗留项。交付条目均通过全量编译、行首禁词零命中与 coqchk；其中 81 条主定理/主定义另经 Print Assumptions 批量审计，最近一次全量 CLEAN 为基态 198/206，其后新增内容维持同等禁词、编译与内核校验口径。逐条验证类型见补充材料 S2/S4。逐条账目、阶段划分与验证记录见补充材料 S2。

| 批次 | 内容 | 交付物 | 状态 |
| --- | --- | --- | --- |
| 阶段零 | 试点对账 | `UpSigMigrate`（13 件）+ 基内 `AttentionGibbsBridgeSetoid`（7 件） | 已闭合 |
| 迁移第一阶段| req 代数地基 | `UpReqAlgebra`（56 件 Qed） | **已闭合** |
| 迁移第二阶段| 分布/自由能/温度层 | `UpReqDist`（91 件）+ `UpReqTempEntropy`（14 件） | **已闭合** |
| 迁移第三阶段| 对齐理论主体（规划约 140 件，含 `req_step_kl_eta_bound` 等桥接件） | 八模块全量交付（`UpReqAlign`/`UpReqAlign2`/`UpReqAlignRestA`/`UpReqAlignRestB`/`UpSigMigrate2`/`UpReqPPO`/`UpReqDpoLoss`/`UpReqAlign3`，见下方状态表） | **已闭合**（最终裁决见汇总清单） |
| 迁移第四阶段| 注意力/采样/模块伴件（约 247 件） | 模块伴件全量交付（逐项见汇总清单迁移第四阶段章） | **已闭合** |
| 迁移第五阶段| 完成与冻结判定 | 最终裁决与汇总清单终版：未完成项解决与解冻（`clip_lower` 走路线 (a)、`ppo_clipped_improvement` 随簇解锁），无遗留项；冻结条目终值 64 件双层并行 | **已闭合** |

**件数口径**：迁移总清单 734 条目与本表件数的对账关系见补充材料 S2。

**迁移状态状态表（防快照漂移；逐次修订登记）**：本表状态截至 **2026-09-09**，对应模块快照（SHA-1 经标准库文档核对）——`UpReqAlgebra.v`（1,645 行 / 56 Qed，`fea1e840e247684008cacbbc0407be4b501e3b81`）、`UpReqDist.v`（3,571 行 / 91 证明件 = 89 Qed + 2 Defined，`4bcd34556e2f3b5cb7aba7b23ec1437bbc6d8fad`）、`UpReqTempEntropy.v`（1,565 行 / 14 Qed，`3f8ed00662c0d95429b229f1a6430386a5dada71`）、迁移第三阶段首批 `UpReqAlign.v`（1,419 行 / 41 Qed，`9693f790f662893262d190725b28704df6955252`）、迁移第三阶段（续） `UpReqAlign2.v`（1,425 行 / 40 Qed，`51c02e05a98c6417de4318a54a8a48f031a17d7e`）、迁移第三阶段余量 `UpReqAlignRestA.v`（706 行 / 23 Qed，`1acdf9cf256165fa9935c7838cbc40537782e3be`）、迁移第三阶段收尾余量 `UpReqAlignRestB.v`（2,642 行 / 55 Qed，`d85b534203298deb238c46f6b4a91b544a6ef7db`；其 MinP/TopP 宇宙件按汇总清单计入迁移第四阶段章）、迁移第三阶段m2 件 `UpSigMigrate2.v`（1,731 行 / 49 Qed，`b9f6e4f26a066d44dde8a464d55dd0cf379af24a`）、迁移第三阶段收尾模块 `UpReqPPO.v`（1,108 行 / 22 Qed，`044776ce0f6f87abcf0ee77933e910771b2d8d9a`）、`UpReqDpoLoss.v`（226 行 / 6 Qed，`1356d75df98039abd4d8da66f17c596c795931aa`）与收尾 `UpReqAlign3.v`（3,762 行 / 76 Qed，`bf60cace1510f5b2d574e676fe5a7f5b6feb1252`）。据此快照，迁移第三阶段已有首批交付：RLHF/DPO 核心（`req_rlhf_optimal` 等）、`req_step_kl_eta_bound` 同位桥、`req_policy_iter_kl_geom_step`/`_iter` 主要定理链、KLProjection 簇、PPO 分解对照件与 NaturalGradient 件（四项验证通过）；深层依赖链残余（汇总清单迁移第三阶段的 22 件未结项）已由 `UpReqAlign3.v` 全数完成——旗舰 `req2_backward_kl_step`（向后 KL 无条件三点恒等式，无 B 类桥接假设）与 `r2_backward_kl_step_le`/`r2_rlhf_policy_improvement`/`r2_step_kl_weighted`/`r2_backward_kl_iter_le`/`req2_gap_mono` 等六件 Print Assumptions 全 Closed、四项验证通过（2026-09-09）；`ppo_conservative` 族与三件单侧组合定理的 req 版因 setoid `min` 输出 eps 化而冻结双层（plain 形不可导出，迁移第五阶段统一裁决）——迁移第三阶段整体转「**已闭合**」，与上表一致。**快照终态（五批主体闭合）**：本表状态刷新为五批全数闭合——全局 670/0/64/0/0（和 = 734，无遗留项）。终版模块快照（磁盘实测）：`UpReqPPO.v`（1,259 行 / 25 处 `Qed.`，md5 `66bf55f5619b4263d79a60ac7327c312`——`rppo_align_objective_advantage_decomp` 未结项已清偿，替代其早前 1,108 行/22 Qed 快照计数）与 `UpReqPPOPlain.v`（662 行 / 14 处 `Qed.`，md5 `120d23e91a7e67bcc76b3e4c2e2ba2ee`——plain-le 保守性族解冻交付）；上文「`ppo_conservative` 族冻结双层（plain 形不可导出）」的早前判定由此解除——冻结经 `ReqDiffPlain` 接口扩展解除，六件 `rpl_` 对应定理随最终裁决交付；冻结双层件终值 64 件（规划普查口径 (d) 56 件为预测值，执行期逐项判定后终值 64）。

(a) **预计工作量**：该迁移预计为**数日至数周级的机械性工程**，无新数学内容、无预期逻辑障碍。工作量主体不是定理内容而是装配：把定理签名与证明链中的 `Id` 等式批量替换为 `req`，并逐一验证/补注册所用代数与序引理在 `req` 上的 Proper 兼容性（注册面规模取决于被定理链引用的引理数，见 (b)）。**迁移顺序建议**：按依赖序自底向上——先 §3 基座层（自由能分解、KL、有限和与逐点提升）定理，再 §4–§7 各算法族核心（每族以其 Real 层逐 eps 版定理 4.9/5.8/5.9/5.11 族/6.6/7.6 为语义对照），最后支撑性质与界引理。

(b) **主要摩擦点**：其一，`eq_ind`（Leibniz 归纳原理）在 `req` setoid 等价下的**消除受限**——`req` 非 Leibniz 等式，凡现证明链中以 `eq_ind`/Leibniz 等式消去（`rewrite` 直通）的步骤，在 `req` 下不能作 Leibniz 归纳，须改为 setoid 重写并依赖对应 Proper 实例；其二，`rewrite`→`setoid_rewrite` 的**自动化适配**——`req` 上下文中 `rewrite` 需换成 `setoid_rewrite`，且每个被重写位置须有 Proper/`req` 兼容实例，否则自动化停摆；其三，**Proper 实例注册面**——`RealSetoid` 上乘加、min/max、exp/log 与 `sum_over_S` 逐点提升、`le`/`lt` 对 `req` 的 Proper 实例需系统化注册（Q 层已有先例 `Qinv_comp_proper`（L8370）/`q_pow_comp_proper`（L8373），但抽象层定理链所引引理在 `req` 上的注册尚未铺开）。三者均为工程性适配，不涉及新的数学内容（与 §10.2 第 1 项一致）。

(c) **迁移完成后的可用性影响**：现状——抽象定理的数学内容落到具体柯西实数上，目前经两条路径承载：req 系接口实例的**字段回填**（接口级事实，exp/log 族、度量与完备性字段在 `Real` 上实值）与**部分核心定理的 Real 层逐 eps 复刻**（清单见 §9.2）；逐 eps 复刻路径逐条证明，是"按定理逐个落数系"。迁移完成后——定理签名直接落在 req 系 setoid 接口上，可**直接经 `RealEnhancedReal`（L41115）实例化消费**其全字段回填，全库定理在具体柯西实数上统一直接可用，无需再为每条定理走逐 eps 复刻（逐 eps 版定理仍保留：实数序的 eps 余量形态是构造性表述的固有部分，两者并存而非互斥；迁移消除的是"每定理逐条复刻"的必要性，不改变任何定理的数学内容）。**序精确性升格（迁移的附加价值，N6）**：接口层的 `le`/`lt` 在 `Real` 实例上是**精确构造性序**——`real_le = Or (real_lt) (real_eq)` 的构造性析取（序算子层面非 eps 余量；eps 余量的所在为 setoid 接口的个别序字段定义（如 `min_le_l` 的逐 eps 形）与 Real 层逐 eps 复刻两路，见 §9.4 例二的分层分析）。因此迁移第三阶段完成后，抽象定理经 `RealEnhancedReal` 实例化得到的序结论是**精确构造性序**：以定理 4.1 为例，实例化结论为 `J(π) ≤ J(π*)` 的精确序——比 Real 层复刻的 `J(π) ≤ J(π*) + D·eps` 更强（在该定理上）。迁移的价值因此不只是省去逐条复刻，还包括**序结论从 eps 余量到精确构造性序的升格**——这直接回应「为什么要做签名迁移」的读者疑问，也与 §9.4 完成路线的路线 (ii)（迁移自动解决序精确性）为同一事实。

**已验证的降压通道**：对个别卡在 Id→req 替换上的假设密集区，AttnDoeblin 模块提供了一条已验证的替代架构——「最小假设接口 + `sigT` 可满足性放电」：`real_expf_realizable`（L96364）把 expf 五字段迷你接口（pos/zero/plus/mono_lt/mono_le）整体放电到具体柯西实数 `cauchy_real_exp`（mono_le 经 `real_le = Or (real_lt) (real_eq)` 的构造性析取逐支组装，见 §4.3.1 放电注与 §10.2 第 1 项 (a)）。这使假设可先重述为迷你接口并在 Real 层放电，绕开全量 Proper 实例注册面——是迁移期的**缓解**而非替代（第 1 项的签名迁移收尾仍是主线）。

### 9.2 不覆盖的内容

**实例化与承载路径（接口族细节见 §9.1.1 上文，此处不再重复叙述；本条为 §4.1 先决问题段的详表版。）** 全库核验：Setoid 系接口 `Instance` 声明为 **3 处**——`Real_RealInterfaceSetoidCore`（L33433）、`Real_RealInterfaceSetoid`（L39407）、`RealEnhancedReal`（L41115，实例化 `RealInterfaceEnhancedSetoid`（L40464）），三者均属 Setoid 系接口（以 setoid 相等 `req` 与带正性前提的 `log_inv : forall x, lt zero x -> R` 表述），**全部字段已由具体 `Real` 实值化**。其余 14 处为 Section 内的 `Local Existing Instance RI_base` 超类解析注册与 Q 层 Proper 实例（`Qinv_comp_proper`（L8370）/`q_pow_comp_proper`（L8373）），不构成实数接口实例。Real 层承载路径为**部分核心定理的逐 eps 复刻**，其精确覆盖清单如下——**核心定理中已有 Real 层逐 eps 版本的**：定理 4.9（`real_rlhf_optimal_eps`，L43804）、5.8（`real_dpo_loss_pi_star_bounded_both`，L42715）、5.9（`real_dpo_reward_recovers_up_to_baseline`，L42761）、5.11（`real_dpo_logit` 族，L54982/L55026/L55038/L55075）、6.6（`real_ppo_conservative_eps`，L43556）、7.6（`real_grpo_advantage_zero_mean`，L43100）；KL 不等式 `real_gibbs_inequality_eps`（L41704）、log 可微性 `real_log_differentiable`（L46386）、compose/entropy 可微性等是支撑上述复刻的 **Real 层基座引理**（主文件 `^\s*Qed\.` 宽口径 2,930 处，零 Axiom），**不是**核心定理本身的镜像。尚未有 Real 层版本的：唯一性（4.2）、间隙恒等（4.3/4.4）、策略迭代族（4.5–4.8、5.10）、GRPO 中心二阶矩/方差族（7.4/7.5）、DPO 相对精确（5.5/5.6）——**此处「尚未有」限定于 219 锚的内容范围**；其中策略迭代族的 Real 层迭代率已在模块层机器检查（见下条阻碍分析），其未列入上表的原因是该结果位于模块层而非 219 锚，并非数学内容缺失。**量化口径与阻碍分析（计数口径：族内多件按族计、5.11 族计为族，同 §1.2 贡献 7，不另立外部「核心定理总数」式计数；全定理状态一览视图见 §1.2 尾表 1）**：核心定理中 Real 层逐 eps 复刻覆盖 4.9/5.8/5.9/5.11 族/6.6/7.6（族内多件，如 5.11 族 4 件），未复刻 4.2/4.3/4.4/4.5–4.8/5.10/5.5/5.6/7.4/7.5。对未复刻各族的阻碍分析——均为**工作量/基建依赖型缺口，无潜在逻辑障碍**：

- 唯一性 4.2：需 `gibbs_equality` 逐点化的接口装配（纯装配型）；
- 策略迭代族 4.5–4.8/5.10：依赖诚实接口 `step_kl_eta_bound`（L23114）的 Real 层镜像——接口的 Real 层对应定理已在库内证明（见定理 4.8 状态脚注）；**Real 层迭代率本身已在模块层机器检查**（定理 4.8 的逐 eps 复刻：`KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps`，模块 `UpStepKLM3` 的 `real_iter_kl_geom`，由单步收缩件对 t 归纳、误差按 t 步算术累积；Real 载体闭端全域版 `(1−η)^{t₁} ≤_B (1−η)^t`（`0 ≤ η ≤ 1`，退化支 η=1 由弱乘法单调吸收）另见模块 `KLWallClosed`），故该项**不属开放问题**——其未并入上段载体清单的原因是结果位于模块层而非 219 锚（两层口径见 §9.1.1）；req 消费版已随迁移第三阶段交付——`req_policy_iter_kl_geom_step`/`req_policy_iter_kl_geom_iter`（主要定理链，四项验证通过）与 `req_dpo_loss_iter_mono` 等已把 4.5–4.8/(1−η)^t 几何率链落到 req 系 setoid 签名上（经 `RealEnhancedReal` 可直接在柯西实数上消费；两层口径不变：正文定理的陈述与证明不消费它们，见 §9.1.1 信用结构说明）；
- GRPO 方差族 7.4/7.5：依赖 `square_nonneg` 接口在 Real 层的装配（正向 eps 证据 `real_square_nonneg_eps`（L44842）已证，见 §7.2）；
- DPO 相对精确 5.5/5.6：需 Real 层比例缩放（差分消去/基线抵消）基建；
- 间隙恒等 4.3/4.4：逐点化装配型工作量（Real 层 KL 分解接口与 eps 链模板已有，见定理 4.9/附录 C.2）。

这意味着：

- 本工作证明了「对任意满足接口的实例，RLHF/DPO/PPO/GRPO 定理成立」，而该接口的 setoid 对应物已由具体 `Real` 实例化（`Real_RealInterfaceSetoid` / `RealEnhancedReal`）；
- 上述清单中的部分核心定理另有 `Real` 层逐 eps 版本直接证明（见上），其余核心定理的 Real 层承载留待抽象层签名对接后的逐 eps 复刻（见 §10.2 第 1 项）。

因此本工作的准确定性是「**抽象接口层的形式化与部分核心定理的 Real 层逐 eps 复刻**」——抽象定理为结构性推演，其 setoid 对应物已实例化，部分核心定理在构造性实数上的逐 eps 对应物已独立证明。抽象层与实例层之间的签名对接为后续工程（见 §10.2）。

其余不覆盖的内容：

1. **神经网络近似**：策略 `pi` 是抽象函数，未绑定到 Transformer 参数化。
2. **连续动作空间**：当前形式化限定于有限离散状态/动作空间。
3. **样本复杂度与泛化界**：未涉及有限样本下的统计学习理论。
4. **经典逻辑结论**：所有存在性结论均为构造性；未与经典逻辑版本做等价比较。
5. **偏好数据集级损失**：`dpo_total_loss` 定义在**有限偏好列表**上（fold），不是数据集上的期望；未定义 `list Preference` 上的期望损失，也未形式化梯度下降的收敛性。
6. **采样管道层**：注意力 softmax 的温度动力学与硬注意力极限属于采样管道层，**不是本文目标理论本体**——库内 AttnDoeblin 采样层定理族（有界 logits softmax 核的显式 TV 收缩族，L95611–L96383）、AttnSqrt（构造性平方根 `real_sqrt_exists`，L96386–L96641）、AttnHardLimit（词表计数/温度权重族，L96643–L97556；硬注意力 TV 完成链至 L97866，39 处行首 Qed）均不改变本文 §2.3 scoped claim，本文定理的陈述与证明不消费它们；其与本文的关联仅为 §10.2 第 5 项的温度两极陈述（T→0 半边的 `hard_attention_limit` 现已在库内机器检查，见该项）与 §9.1.1 Artifact 段的行号基底记录。

**表 2：与标准算法差异对照（给 ML 读者的范围导引）**

| 算法 | 本文形式化对象 | 与标准算法的关键差异 | 定理名锚 |
| --- | --- | --- | --- |
| RLHF | 单步 KL 正则化对齐目标 | KL 方向前向/后向不可互换；间隙恒等取前向 KL | `rlhf_optimal`；`rlhf_suboptimality_gap` |
| DPO | 逐对 Bradley-Terry 损失与隐式奖励恢复 | 审计=KL 投影为解释性串联；损失为有限偏好列表 fold 和 | `dpo_optimal`；`dpo_reward_recovers_up_to_baseline`；`projected_distribution_minimizes_kl` |
| PPO | 单步 bandit 裁剪代理 | 比率分子固定为 pi_star；非端到端 PPO；主结果为单侧分解 | `ppo_conservative`；`ppo_is_decomp`；`ppo_clipped_improvement` |
| GRPO | 组相对优势统计量 | 组统计量需 NoDup 前提；未做标准化优势；σ 见证已证、单位矩未全装配 | `grpo_advantage_zero_mean`；`counter_ex_indicator_sum_two`；`group_variance_identity` |

220 起追加的治理与新算法模块层（改进声明宪法、熵防火墙、投影记账、逐出动力学、耗散币制、停时原语等）同属本文范围之外——本文定理的陈述与证明不消费它们，scoped claim 不变；其中与本文相邻的仅有实例面注记两处：§5.3 的 Real 层审计实例族（UpAuditBridge/UpMinP，见该节实例面注记）与 §10.2 第 5 项的温度窗口 T→∞ 半边（UpTempWindow，见该项注）。模块化树当前以 HEAD 39d81aa 为准：编译清单 246 模块，Live_X 成果区 356 个 .v；云认证 CI 连续 success，认证面 246，各波 coqchk 全绿（CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；早期模块拓扑与认证单元口径、五新件未入 Extensions 等描述为早期版本记录；现态模块拓扑、汇聚件与未入汇聚清单按 HEAD 39d81aa 重列于补充材料 S1。论文行号锚仍为 219，不随模块树扩波平移。引用未入汇聚形态的定理时，仍须注明形态归属，但清单须按当前树核对后列示。新增件同属本文范围之外。库内另有条件化的 softplus Lipschitz 界（显式 `Or (le) (le)` 前提）等敏感性素材，同属追加层、本文不消费。

**注**：`dpo_total_loss_monotone`（L20181）的「总损失」实为有限偏好列表上的 fold 和（`dpo_total_loss`，L20153），非数据集期望；该定理只陈述逐对损失单调 ⟹ fold 和单调，**不含 π*** 亦**不含改进方向**——「沿改进轨道单调」是聚合损失 `dpo_loss`（L19090）的性质（定理 5.10，L23244/L23256）。保留原标识符以免破坏下游引用；重命名建议 `dpo_fold_loss_mono_pointwise`，随 artifact 发布窗口执行（投稿版为重命名时机），以免下游按「总损失单调」直觉误引。

### 9.3 与 O'Connor 2008 等先例的关系

构造性分析学已有丰富先例（C-CoRN、NuPRL、O'Connor 2008 [6][7]；形式化实数分析的库间综述见 [34]）。本文「逐 eps 方法」与「Bishop 形态」的方法论出处为 Bishop & Bridges 的《Constructive Analysis》（1985）[24]——构造性有序域中非严格序的余量化陈述与误差簿记路线承袭于此（§2.2）；该书为经典文本出处，不含机器形式化，亦不涉及 ML 对齐。本库的贡献不在于分析学本身，而在于将对齐算法优化理论置于构造性分析基座上，并揭示它们共享的自由能-KL 结构。本库 `Real` 与 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 独立构建、构造路径并行；未来工作将评估二者等价性，以促进社区复用与互操作。

**技术差异**：自建 `Real` 与既有构造性实数路线的差异集中在**实数表示与完备性证明策略**。本库 `Real` 采用**有理数 Cauchy 序列 + 逐点 eps 判定（Set 层 `QleT`/`QltT` 判定谓词）的收敛/完备性证明、并以 sigT 打包完备性见证**（存在性结论携带构造见证，见 §3.1/§9.1.1）；O'Connor 2008 采用**正则函数表示**（以 Lipschitz 界函数控制收敛的序列表示实数）；C-CoRN 采用 **C1 集/函数空间 + 代数完备化**的构造路线。三者差异是表示与完备性证明策略的选择，逻辑立场同为构造性（均不依赖排中律，见 §9.4 的经典解释相容性说明）。本库的表示选择服务于 Set 层可提取性（信息性证明可直接提取 OCaml，见 §9.1.1）与 eps 化接口消费（接口与定理以逐 eps 余量陈述，如定理 4.9/6.6 形态）——与 O'Connor/C-CoRN 的"另起炉灶"系表示工程与消费接口之差，而非分析学内容之差。

### 9.4 与经典逻辑版本的对比

对齐算法领域的主流分析以经典逻辑（含排中律与三分律）陈述。本节说明本库构造性版本与这类经典版本的关系，口径与 §9.2 项 4、§10.2 项 4 一致：

- **前提更强（显式化）**：经典证明常隐式假设分布正性、归一化、KL 有限性与函数可微性；本库把这些前提逐一显式声明为 Section `Variable` 或接口字段（§9.1），正性必须给出构造性见证（如 `pi_ref_pos`、`Z_align_pos`）。因此本库定理的假设集在表述上比经典文献更细、更显式。
- **结论在经典解释下成立**：纯构造性逻辑是经典逻辑的子系统——任何在构造性规则下完成的证明，其推导步骤亦均为经典逻辑接受的有效推导（经典逻辑仅在构造性公理之上增加排中律等，不删除任何可证命题）。故凡本库以抽象接口假设陈述并证明的定理，把接口前提原样读作经典实数分析（或任一经典意义下满足这些前提的结构）中的相应条件，其结论在经典解释下依然成立——本库结论的存在性均由显式 witness 给出（如闭式 `pi_star`、`policy_iterate` 的 sigT 打包），不依赖排中律的析取/存在形态，故不存在"构造性证明在经典解释下失效"的问题。
- **不作等价性主张**：上述"结论在经典解释下成立"是单向的（构造性可证 ⟹ 经典可证），本库**未**形式化经典逻辑版本，也未机器检查"构造性 ⟺ 经典"或经典 ⟹ 构造性的反向传递（后者一般需排中律，数三分，见 §9.2 项 4 与 §10.2 项 4）——读者不应把本库表述理解为对经典版本的等价比对或超越。
- **经典解释下可增强的形态**：若干以 eps 余量或诚实接口陈述的构造性边界（如 Real 层 `real_min` 只有 eps 界 `real_min_le_l_eps`（定理 6.6）、`square_nonneg` 为接口 Variable（定理 7.5））源于构造性有序域无三分律，且 `le` 以 `Or (lt) (req)` 编码、非严格序只能以逐 eps 余量陈述（接口实例化的语义说明，见 §9.1.1）。在经典解释下（三分律可用）这些可增强为精确形式；本库按构造性编码下可达的最强形式陈述，不把经典增强冒充为库内定理。

**例（`real_min_le_l_eps`；解释性实例，不新增任何机器检查断言）**：以 Real 层的 eps 余量界 `real_min_le_l_eps`（L40023，219 基态实测；定理 6.6 所引）为例说明上述原则。该引理陈述 `forall a b eps, real_lt real_zero eps -> real_le (real_min a b) (real_plus a eps)`——即 `min(a,b) ≤ a + eps`，**须带 eps > 0 的余量**（无精确 `min ≤ r`，见定理 6.6/附录 A 行）。经典解释下（三分律/排中律可用）同一事实可增强为精确形式：`forall a b, real_le (real_min a b) a`——`min(a,b) ≤ a` 恒真且无需 eps，因为经典逻辑可对「`a ≤ b` 或 `b < a`」作排中分支：前者 `min(a,b) = a`（精确等号成立）、后者 `min(a,b) = b < a`（严格小）。但该精确形式在**本库的构造性编码下不可达**：本库的 `le`/`real_le` 以 `Or (lt) (req)` 编码（需显式分支选择，见 §9.1.1 接口实例化说明），证明 `min(a,b) ≤ a` 必须交出显式析取见证——`min(a,b) < a`（需 `b < a` 的见证）或 `min(a,b) == a`（需 `a ≤ b` 的见证）；而「`a ≤ b` 还是 `b < a`」对构造性实数不可判定（序三分律缺失，判定 `x == 0` 之类无构造性判别程序），析取见证无法构造性产生。库内可达的最强形式因此是 `real_min_le_l_eps` 的 eps 余量形态：以 eps 吸收「分支不可判定」的缝隙。本库未形式化「精确版不可证」这一元理论判断（§9.4 为解释性说明），仅陈述库内可达形态——这正是本节的抽象原则：同一数学事实在经典解释下可精确陈述、在构造性编码下以 eps 余量陈述，二者不矛盾，本库只陈述后者。

**例二（Real 层 eps 余量形态与精确形态的完成分析；解释性实例，不新增任何机器检查断言）**：定理 4.9/6.6 的 Real 层结论以 `x ≤ y + D·eps`（逐 eps 余量，`D` 为定理内固定权系数）形态陈述。自然的问题是：对柯西实数，`∀eps>0, x ≤ y + D·eps ⟹ x ≤ y` 型的完成引理能否在构造性逻辑内成立、从而把上述定理强化为精确形态？本例给出双侧答案——**可完成的形态与不可完成的形态必须分开陈述**：

- **（i）不可及形态：结论取本库 `real_le` 的 Or 编码（`Or (real_lt) (real_eq)`）时，完成一般不可达。** 理由与例一（`real_min_le_l_eps`）同源：`∀eps>0` 前提给出的是一个**逐 eps 变化的 Or 见证族**，构造性逻辑不允许从该见证族中提取单一析取见证。具体地，若该完成引理（Or 形结论）成立，取 `(x, y) := (real_min a b, a)`、`D := 1` 即得精确的 `real_min_le_l`（`min(a,b) ≤ a`）——其 Or 见证需在「`b < a`」（左支）与「`a ≤ b` ⟹ `min == a`」（右支）之间作分支选择，而该分支对构造性实数不可判定（例一已述）。故 Or 形的「精确版」4.9/6.6 不在本库编码下主张（与例一的抽象原则一致：本库只陈述构造性编码下可达的最强形式）。这一不可达性不依赖 `D` 是否依赖 `eps`——即便 `D` 为常数，见证族的分支不可判定性依旧；真正的关键是**结论侧的编码形态**。
- **（ii）可及形态：结论取 Bishop 形非严格序（逐 eps 严格余量）时，完成构造性可达、不需排中律。** 引入 Bishop 形谓词 `real_le_b x y := ∀eps>0, real_lt x (real_plus y eps)`（全称化可计算判定，Set 层可提取形态），则完成引理为：**`D` 带显式正性证书、且 `∀eps>0, real_le x (real_plus y (real_mult D eps))` ⟹ `real_le_b x y`**。构造路径（eps/2 簿记，无需稠密性论证）：任给 `eps' > 0`，取 `eps := eps'·inv(2·D)`（`D > 0` 证书保证 `inv` 正性可构造）；前提实例给出 `real_le x (y + eps'/2)`，按 Or 编码分两支：左支 `real_lt x (y + eps'/2)` 经 lt 保序加法（`eps'/2 < eps'`）得 `x < y + eps'`；右支 `real_eq x (y + eps'/2)` 经等式换形得同一严格不等式。两支均在 Or 编码内闭合，`real_le_b x y` 得证。配套单向桥 `real_le x y ⟹ real_le_b x y`（lt 支平凡；eq 支经 `x == y` 与 `0 < eps/2` 换形）后，定理 4.9/6.6 可在**不改动任何既有定理陈述**的前提下追加 Bishop 形对应物：`J(π) ≤_B J(π*)`、`ppo_objective ≤_B is_objective`——该形态即构造性语义中非严格序的标准读法（对全部 eps 一致成立、不绑定权系数 `D`），比单点 `D·eps` 形态的表述更强。该完成引理族已在库内实现（独立模块 `UpRealLeB.v`：`real_le_closure_b` 即本条完成引理的机器检查形态，四项验证通过；状态详注见（iv））。
- **（iii）定理 6.6 的求和层面账目（部分可达，前提补强）**：6.6 的残差权系数为 `E := Σ_s π_old·adv`，在 `advantage_pos` 前提下仅有 `E ≥ 0`、不必然 `> 0`，故（ii）的完成在 6.6 上需补 `E > 0` 的显式正性证书方可逐 eps 分摊；`E == 0` 情形（全部优势为零时两目标精确相等）与 `E > 0` 情形对构造性逻辑不可分，故账目改良的诚实完成是：**在补 `E > 0` 证书前提下给 6.6 的 Bishop 形对应物；无证书情形维持 eps 形陈述**（逐点层面 `min ≤ a` 的不可判定性不受求和账目影响，可改良的只是余量的计权方式）。
- **（iv）状态与双侧结论**：（ii）的完成引理族（`real_le_b` 定义、单向桥 `real_le_to_le_b`、eps/2 完成引理 `real_le_closure_b`、4.9/6.6 的 Bishop 形对应物 `real_rlhf_optimal_B`/`real_ppo_conservative_B`）**已在库内实现**（独立模块 `UpRealLeB.v`，392 行，四项验证通过：禁词零命中/编译零告警/提取零 `Obj.magic`/`coqchk` 内核校验通过，单向桥、完成引理与两应用件的 `Print Assumptions` 均 Closed；实现所需前提核查（`D` 与 `E` 的正性证书供给链）已随实现完成——定理 4.9 的 `D` 正性证书 `D_pos` 为节内既有变量，对应物**完整升格**、零新增前提；定理 6.6 的 `E := Σ π_old·adv` 在接口面无内在正性供给链（`E == 0` 与 `E > 0` 构造性不可分，见（iii）），对应物语句补 `E > 0` 显式证书前提、为**条件升格**）。关于一种常见预期——「对柯西实数，`∀eps>0, x ≤ y + D·eps ⟹ x ≤ y` 在构造性逻辑内可证（有理稠密性）」——本文的结论为**双侧结论，二者并存**：该判断对 **Bishop 形结论编码**成立——本文已照此实现（实现以 `e₀ := eps'·inv(2·D)` 换形完成 eps/2 簿记，零稠密性消费，强于稠密性路线）；该判断对**本库 `real_le` 的 Or（lt/eq）结论编码**不成立——若 Or 形完成可证，取 `(x, y, D) := (real_min a b, a, 1)`（常量 1 的正性证书既有）配 eps 形逐点界即得精确 `min(a,b) ≤ a` 的单一 Or 见证，与例一的构造性不可判定论证直接相抵；且该不可达性与 `D` 是否依赖 `eps` 无关（（i）条论证），故所举两种可能失效情形（`D` 依赖 eps、正性证书不可统一）均非要害，真正的关键是结论侧编码形态。据此：Or 形「精确版」不主张，Bishop 形对应物以独立模块形态交付（§9.1.1 两层口径：正文定理的陈述与证明不消费它）；定理 4.9/6.6 的既有 eps 形陈述不变。该双侧结论另有同框对证（谓词级封装并行）：`min a b ≤ a` 的 Or 形精确版构造性不可证、同一语句的 Bishop 形（`real_min_le_l_B`）可证（`UpRealLeB.v` 尾注记录 2/7）——「逐 eps 余量」机制现已由序谓词 `real_le_b` 完成谓词级封装（Set 层 forall 型，零 Prop 泄露），并以完成引理族覆盖 28 件 plain/D·eps 余量件。

**注**：本节为解释性说明，不新增任何机器检查断言（例一、例二同此）；其内容不改变 §9.1–§9.3 的边界声明。

### 9.5 架构演化与教训

本节把散落于 §4.1、§9.1.1 与 §10.2 的架构史信息收拢为一处方法论总结。这对后续库设计的参考价值，本文认为不低于其中任何单条定理。

**演化史**：本库定理最初陈述于 Id（Leibniz）等式系接口 `RealInterfaceEnhanced`；而柯西实数只有 setoid 等式 `real_eq` 可实例化，抽象定理与具体实例因此分属两套签名族。弥合该缝隙的签名迁移工程分五批推进执行完毕（迁移总清单 734 件：670 件已交付、64 件冻结双层并行冻结条目，§9.1.1），对齐理论主体（§4–§7）的定理级迁移已闭合。

**根因链（单一决策的系统性代价）**：上述双系的深层根源是实数序编码的一次性选择——`real_le = Or (lt) (req)`。该编码下每条无余量的 le 形结论都须交出显式析取分支见证，而等号情形（如 π_t == π* 逐点）对构造性柯西实数不可判定，于是：`square_nonneg`（定理 7.5 接口）、exp 两点凸性与逐点 AM-GM 的精确形、`log Z ≤ 0` 的精确形（定理 4.8 的接口）、`min ≤ r` 的精确形（定理 6.6）、KL ≥ 0 的精确形（§9.4）全部不可证，只能以诚实接口或 eps 形呈现——全文的"诚实接口税"由此单一编码决策系统性生成（§9.4 例一/例二为该机制的两份解释性档案）。

**若从零重来的设计**：以单 setoid 系（`RealInterfaceSetoid` 族 + 柯西实例）为唯一起点、以 Bishop 形非严格序（`∀eps>0, x < y + eps`，可填充、无需分支见证）为库的主序，Or 序降为可选精化层（在 req 成立时给出精确等式）。在该设计下：定理 4.8 的实数层实现链无缺口、定理 7.5 无需 `square_nonneg` 接口、定理 6.6 有精确 Bishop 形——这正是 Bishop & Bridges [24] 的标准路线，也是本库 `UpRealLeB.v`（`real_le_closure_b`/`real_rlhf_optimal_B`/`real_ppo_conservative_B`，§9.4 例二 (ii)/(iv)）已验证的升格方向。

**教训四条**：
1. **相等与序编码是库级一次性决策**，其代价随定理数线性放大；选定前应先确认目标实例（此处：柯西实数）的相等谓词与序谓词形态。
2. **抽象接口的相等谓词必须与目标实例同系**（同为 setoid 或同为 Leibniz），否则任何实现都需要签名迁移工程；Id 系层是历史路径依赖，其代价即上述五批工程与 64 件冻结双层。
3. **构造性非严格序应取 Bishop 形（全称化逐 eps 余量）而非 Or 析取形**：前者可填充、可提取（Set 层 forall 型），后者要求不可判定的分支见证。本库的混合方案数学上自洽，但系统性付出了接口税。
4. **双层并行承载（Id 层陈述 + Real 层逐 eps 复刻）是可审计的过渡形态，不宜作为终态**；冻结件的判据（哪些 Id 陈述形态不可平移到 req：函数外延性依赖、Id-dependent rewriting 等）应公开，本节与 §9.1.1 的对账表即为该公开的载体。

### 9.6 分量分层与注记汇总清单

本文的注记（初等性、定义性后承、支撑层归属）统一由本节集中管理；正文各处仅保留指针，不再重复自我降级语句。标注的用语取中性口径：**定义性后承**（证明为定义展开或单条接口字段的直接推论）、**支撑层**（为其他定理提供通道的移项/装配性质）、**初等复述**（教科书事实的构造性机器检查）。例外列出的原则不变；标注服务于精确界定贡献边界，而非系统性自我否定。

| 定理/章节 | 分量定位 | 集中标注位置 |
|---|---|---|
| 定理 4.3/4.4 | 支撑层：4.3 为自由能分解的一次移项重写（附录 B.1 自评），4.4 为其单调性通道 | 附录 B.1 |
| 定理 5.3 | 定义性后承：reflexivity 级命名桥 | §5.2 |
| 定理 6.7 | 定义性后承：`min_le_l` 的直接推论，与裁剪结构无关 | §6.2 定义备注 |
| 定理 7.1/7.4/7.5 | 初等复述：组统计量的代数恒等式，价值在前提显式化 | §7.2 术语说明 |
| softmax=Boltzmann、自由能分解、Gibbs 不等式 | 初等复述：统计力学标准事实的构造性机器检查 | §1.2 分层、§3.3 |
| **定理 4.5–4.8** | **全文数学含量最高者**：策略迭代的精确动力学与几何收缩率 | §4.3.1 |
| 定理 6.8–6.10 | PPO 裁剪机制的组合定理（非平凡形式化） | §6.3 |
| 定理 7.2/7.3 | 前提不可去反例：形式化暴露隐藏假设的实质内容 | §7.2 |

**诚实接口的三分类表**（"诚实接口"一词的标准术语对应：显式前提/explicit premise，即随 Section 泛化为定理显式前件的未消解假设，§3.4）：

| 分类 | 含义 | 实例 |
|---|---|---|
| 已证-in-Real（消解证据在案） | 接口假设的 Real 层对应定理已在库内证明 | `step_kl_eta_bound` → `real_step_kl_eta_bound_eps` 等（定理 4.8 状态注）；`HlogZ` 消解材料（§5.3） |
| 可证未做（组装型开放） | 无逻辑障碍，属工作量/基建依赖型缺口 | 4.2/4.3/4.4 的 Real 层镜像（§9.2 阻碍分析） |
| 真开放（构造性边界） | 本库序编码下不可达精确形，仅 eps/Bishop 形可达 | `real_min_le_l` 的 Or 形（§9.4 例一）；`square_nonneg` 的抽象层 discharge（§10.2 第 1 项） |

---

## 10 结论与未来工作

### 10.1 结论

本文的主要贡献是在构造性柯西实数基座上，对 RLHF/DPO/PPO/GRPO 四族单步对齐目标理论给出零全局公理的机器检查统一（PPO 章定位为裁剪机制的静态结构性质三定理，不与前三族并列）；库的签名迁移工程已全部处置，其方法论教训的正面陈述——构造性实数上 Id 陈述的不可实例化、序与相等的编码是库级一次性决策——见 §3.6、§9.1 开头与 §9.5。辅助贡献包括自由能–KL 统一视角与部分核心定理的 Real 层逐 eps 复刻。采样管道层结果（Top-k/Min-P/KV 驱逐）属姊妹论文正文范围，本文仅在统一视角节延伸引用，不构成四族对齐目标理论主张。全部机器检查均在 Rocq/Coq 中完成，不引入全局公理；"首次"主张的完整条件见 §2.3。该工作为对齐算法的安全关键部署提供了可审计的数学基础。

### 10.2 未来工作

（以下按优先级压缩为 5 项；各旧的细分项全文、定理名与行号锚见附录 D.10 与 §9.1.1，本节只保留面向读者的主线。）**口径说明**：追加层的独立模块与正文定理为独立模块形态的同族结果——它们不构成正文定理的镜像闭合，正文定理的陈述与证明不消费它们；吸收为正文内容须按 §9.1.1 的两层口径分别标注。

1. **实数层实现与签名迁移收尾**。签名迁移主体已闭合：迁移总清单 734 件中 **670 件已交付**（670/734 = **91.3%**；交付件以行首禁词零命中、全量编译与内核校验为验证闸，其中 81 条主定理/主定义另经 Print Assumptions 批量审计（分层验证口径见 §9.1.1）），余 **64 件为 (d) 冻结双层并行冻结条目**——其 Id 层陈述与 Real 层逐 eps 复刻按双层并行承载，属终态定性而非未完成项，逐项冻结理由均有记录（分批状态表与件数口径注见 §9.1.1）。收尾面按子项管理：
   (a) `step_kl_eta_bound` 的 Real 层对应物——已证（`real_interp_Z_le_one_eps`/`real_step_kl_eta_bound_eps` 及支撑件，定理 4.8 状态注）；
   (b) GRPO 均匀均值 NoDup discharge 与前提不可去反例——已证（定理 7.2/7.3 及三件均匀均值定理）；
   (c) GRPO σ 见证核心——已证（`real_sigma_witness` 与投影三件），单位矩全装配 `(1/G)·Σ(A_i/σ)² == 1` 仍开放；
   (d) PPO clip 单侧误差恒等式三件——已证（定理 6.8–6.10；反向界维持不宣称）；
   (e) 审计前提 HlogZ 消解路径——闭合；审计自由能蓝图 `free_energy_with_audit_decomp` 未实现（实现路径可改为投影主定理 `UpProj`）；
   (f) `Z_align_pos`/`square_nonneg` 的 Real 层镜像——尚未实现（7.5 镜像即 `real_group_variance_le_raw_eps`，经已证的 `real_square_nonneg_eps` 装配；`square_nonneg` 的抽象层 discharge 不可行——Or 编码需分支见证，构造性边界）。分层登记（Q8 口径）：`Z_align_pos` 在抽象层与 Real 层均为 Section Variable 显式前件（Real 层未 discharge）；req 层同形槽位已在四个站点（对齐/对齐2/RestA/DpoLoss 簇）经配分条件正性路线（`zposd` 键）前提消去——槽位 `Z_align_pos` 替换为非空 datum 前提（枚举非空 + 既有 `pi_ref_pos`/`beta_pos`），产出件 `*_zpfinal_*` 族 `Print Assumptions` 全 Closed；Real 层的无条件 discharge 仍开放；
   (g) Real 层 eps→精确（Bishop 形）完成引理族——已实现（独立模块 `UpRealLeB.v`，§9.4 例二 (iv)）；
   (h) 策略迭代族 4.5–4.8/5.10 的 Real 层迭代镜像——**已机器检查（模块层，不属开放项）**：模块 `UpStepKLM3` 的 `real_iter_kl_geom` 给出定理 4.8 的 Real 层逐 eps 复刻——`KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps`（单步收缩件 `real_iter_step_geom_eps` 对 `t` 归纳，误差按 `t` 步算术累积）；模块 `KLWallClosed` 另给出两件：Real 载体闭端全域版 `klc_closed_powb_mono`（`0 ≤ η ≤ 1` 下 `(1−η)^{t₁} ≤_B (1−η)^t`，退化支 `η=1` 由弱乘法单调 `klc_le_mult_r_weak` 吸收、无需 `1−η` 严格正性证书）与 Q 载体严格收缩支 `klc_strict_branch`（构造性取得 `1−η > 0` 的正性证书，正对判定「Real 层 `1−η==0` 与 `1−η>0` 不可分」所缺）。本文未将该结果并入 §9.2 载体清单，因其位于模块层而非 219 锚（两层口径见 §9.1.1）；
   (i) 冻结双层件的长期处置与按语义边界的模块化拆分——拆分不改变任何定理内容；单文件设计决策与模块化优先级评估见 §9.1.1 与附录 D.9。
   exp 正性链已完整闭合（`esq_eq_corr` 簇 + `cauchy_real_exp_pos` + setoid 系接口实例回填），无剩余面。

2. **形式化范围扩展**：策略参数空间上的迭代优化（补齐 `pi_new`，把 §6 的「单步向最优策略靠近」升级为带优化变量的 PPO 迭代；归一化 `group_variance` 与方差恒等式已实现，见 §7.2 术语说明）、连续动作空间上的测度形式化、策略函数到神经网络架构的参数化绑定、样本复杂度与泛化界（PAC-Bayes / 信息论工具）。

3. **经典逻辑互操作**：构造性版本与经典版本的等价性比较，便于与现有经典分析库互操作（单向传递已明：构造性可证 ⟹ 经典可证，§9.4；反向传递一般需排中律，未形式化）。

4. **目标间隙几何率需 Pinsker 型材料（注记）**：定理 4.3 的次优间隙恒等 `J*−J(π) == β·KL(π‖π*)` 是**前向** KL，定理 4.8 的几何收缩是**后向** KL；两方向 KL 在单纯形上不可比（前向 KL 可无界，§4.3.1 定位注反例），**目标间隙 `J*−J(π_t)` 的几何率不能由定理 4.3 与 4.8 直接组装**——其闭合需 KL 强凸性/Pinsker 型传递（把 KL 间隙控到 TV 或二次下界）。**库内已有该方向的部分材料**：二点形 TV-KL 下界 `p2_pinsker_witness_b`/`p2_kl2_nonneg_b`（模块 `PinskerTwoPoint`，给出显式闭式常数 `c := KL·inv(TV²)` 并满足 `c·TV² == KL`，Bishop 形出口）与 `sup_p KL(p‖q)` 上界 `skb_sup_kl_log_inv_min`（模块 `SupKLBound`，补库内该上界缺口）；但**经典 Pinsker 常数 2 的完整传递（`KL ≥ 2·TV²`）未做**——其需 log 的调和型下界，构成该路线（二点形）的显式降档边界。故本文不主张该率已证。辨析：第 1 项 (a) 的坍缩（逐点 AM-GM）只针对 `step_kl_eta_bound` 的插值不等式 `Z ≤ 1`；库内已证的有界 softmax 核 TV 收缩率 `(1−e^{−2Δ/T})ⁿ` 属采样管道层、轨道对象不同，不构成该传递。

5. **采样层温度窗口双端合一**（属采样管道层，不改变 §2.3 scoped claim，§9.2 第 6 项）：T→0 半边（`hard_attention_limit`，∃T₀ sigT 量词翻转已机器检查）与 T→∞ 半边（`UpTempWindow.temp_window_T_infty`）均已机器检查；两半 TV 极限对象不同质（δ_m 点质量 vs 均匀分布 U）、「∃T₁T₂ 双端合一」单一陈述未合成，仍属开放。边界约束（与第 4 项同口径）：上述 TV 层几何率不构成目标间隙 `J*−J(π_t)` 的收敛材料，不写入 §4.3.1 收敛主张。

## 参考文献

1. Peters, J., Mülling, K., & Altun, Y. (2010). Relative Entropy Policy Search. *AAAI*.
2. Todorov, E. (2006). Linearly-solvable Markov decision problems. *Advances in Neural Information Processing Systems 18 (NIPS 2005)*. MIT Press.
3. Schulman, J., Wolski, F., Dhariwal, P., Radford, A., & Klimov, O. (2017). Proximal Policy Optimization Algorithms. *arXiv:1707.06347*.
4. Rafailov, R., Sharma, A., Mitchell, E., Ermon, S., Manning, C. D., & Finn, C. (2023). Direct Preference Optimization: Your Language Model is Secretly a Reward Model. *NeurIPS*.
5. DeepSeek-AI. (2024). DeepSeekMath: Pushing the Limits of Mathematical Reasoning in Open Language Models. *arXiv:2402.03300*.
6. Geuvers, H., Niqui, M., & Wiedijk, F. (2000). Constructive Reals in Coq: Axioms and Categoricity. *TYPES*.
7. O'Connor, R. (2008). Certified Exact Transcendental Real Number Computation in Coq. *TPHOLs*.
8. Affeldt, R., & Hagiwara, M. (2014). Formalization of Shannon's Theorems. *Journal of Automated Reasoning* 53(1):63–103. https://doi.org/10.1007/s10817-013-9298-1（前身：Affeldt, R., & Hagiwara, M. (2012). Formalization of Shannon's Theorems in SSReflect-Coq. *ITP 2012*, LNCS 7406, Springer, 233–249。库：coq-proba / Infotheo，https://github.com/affeldt-aist/infotheo ；另见 Affeldt, R., Garrigue, J., et al. (2020). Reasoning with Conditional Probabilities and Joint Distributions in Coq. *JSSST* 37(3):79–95. https://doi.org/10.11309/jssst.37.3_79）
9. Hölzl, J. (2016). Markov Chains and Markov Decision Processes in Isabelle/HOL. *Journal of Automated Reasoning*, 59(3), 345–387. https://doi.org/10.1007/s10817-016-9401-5
10. Hölzl, J., & Nipkow, T. (2012). Markov Models. *Archive of Formal Proofs*. https://isa-afp.org/entries/Markov_Models.html
11. Schäffeler, M., & Abdulaziz, M. (2021). Markov Decision Processes with Rewards. *Archive of Formal Proofs*. https://isa-afp.org/entries/MDP-Rewards.html
12. Schäffeler, M., & Abdulaziz, M. (2021). Verified Algorithms for Solving Markov Decision Processes. *Archive of Formal Proofs*. https://isa-afp.org/entries/MDP-Algorithms.html
13. Chevallier, M., & Fleuriot, J. (2021). Formalising the Foundations of Discrete Reinforcement Learning in Isabelle/HOL. *arXiv:2112.05996*. https://arxiv.org/abs/2112.05996
14. The mathlib Community (leanprover-community/mathlib4，持续更新). Mathlib.InformationTheory.KullbackLeibler（`klDiv`、Gibbs 不等式）与 Mathlib.MeasureTheory.Measure.Tilted（测度指数倾斜）. https://leanprover-community.github.io/mathlib4_docs/Mathlib/InformationTheory/KullbackLeibler/Basic.html
15. The Coq Development Team. Coq.Reals.Cauchy.ConstructiveCauchyReals（构造性 Cauchy 实数，Coq 8.12+ 标准库随附；Rocq 9.1 以 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 存留，标准库文档核对（2026-09-03））. https://coq.inria.fr/doc/stdlib/Stdlib.Reals.Cauchy.ConstructiveCauchyReals.html
16. The C-CoRN Project. C-CoRN: the Constructive Coq Repository at Nijmegen（构造性 Coq 仓库：实数与分析学基础）. https://github.com/coq-community/corn
17. Constable, R. L., et al. (1986). *Implementing Mathematics with the Nuprl Proof Development System*. Prentice Hall.
18. Nemirovski, A. S., & Yudin, D. B. (1983). *Problem Complexity and Method Efficiency in Optimization*. Wiley.
19. Beck, A., & Teboulle, M. (2003). Mirror Descent and Nonlinear Projected Subgradient Methods for Convex Optimization. *Operations Research Letters*, 31(3), 167–175.
20. Hazan, E., Agarwal, A., & Kale, S. (2007). Logarithmic Regret Algorithms for Online Convex Optimization. *Machine Learning*, 69(2–3), 169–192.
21. Christiano, P. F., Leike, J., Brown, T. B., Martic, M., Legg, S., & Amodei, D. (2017). Deep Reinforcement Learning from Human Preferences. *Advances in Neural Information Processing Systems 30 (NIPS 2017)*.
22. Kakade, S., & Langford, J. (2002). Approximately Optimal Approximate Reinforcement Learning. *Proceedings of the 19th International Conference on Machine Learning (ICML 2002)*.
23. Schulman, J., Levine, S., Abbeel, P., Jordan, M., & Moritz, P. (2015). Trust Region Policy Optimization. *Proceedings of the 32nd International Conference on Machine Learning (ICML 2015)*.
24. Bishop, E., & Bridges, D. (1985). *Constructive Analysis*. Grundlehren der mathematischen Wissenschaften 279. Springer-Verlag.
25. Azar, M. G., Rowland, M., Piot, B., et al. (2023). A General Theoretical Paradigm to Understand Learning from Human Feedback. *arXiv:2310.12036*. https://arxiv.org/abs/2310.12036
26. Ouyang, L., Wu, J., Jiang, X., et al. (2022). Training Language Models to Follow Instructions with Human Feedback. *Advances in Neural Information Processing Systems 35 (NeurIPS 2022)*.
27. Xiao, L. (2022). On the Convergence Rates of Policy Gradient Methods. *Journal of Machine Learning Research*, 23(282), 1–36.
28. Khodadadian, S., Jhunjhunwala, P. R., Varma, S. M., & Maguluri, S. T. (2022). On Linear and Super-Linear Convergence of Natural Policy Gradient Algorithm. *Systems & Control Letters*, 163, 105632. https://www.sciencedirect.com/science/article/abs/pii/S0167691122000500
29. Leroy, X. (2009). Formal Verification of a Realistic Compiler. *Communications of the ACM*, 52(7), 107–115；CompCert 项目（多 pass 模块化架构的验证编译器；官网 2026-08 发布 3.18）. https://compcert.org
30. Vajjha, K., Shinnar, A., Trager, B., Pestun, V., & Fulton, N. (2021). CertRL: Formalizing Convergence Proofs for Value and Policy Iteration in Coq. *Certified Programs and Proofs (CPP 2021)*. https://doi.org/10.1145/3437992.3439927
31. Bradley, R. A., & Terry, M. E. (1952). Rank Analysis of Incomplete Block Designs: I. The Method of Paired Comparisons. *Biometrika* 39(3/4):324–345. https://doi.org/10.2307/2334029 （§5 隐式奖励所依据的偏好模型）
32. Kullback, S., & Leibler, R. A. (1951). On Information and Sufficiency. *Annals of Mathematical Statistics* 22(1):79–86. https://doi.org/10.1214/aoms/1177729694 （KL 散度的原始文献）
33. Csiszár, I. (1975). I-Divergence Geometry of Probability Distributions and Minimization Problems. *The Annals of Probability* 3(1):146–158. https://doi.org/10.1214/aop/1176996454 （I-投影；§5.3 KL 投影主定理的经典对应）
34. Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437
35. Li, C., Wang, Z., He, W., Wu, Y., Xu, S., & Wen, Z. (2025). Formalization of Convergence Rates of Four First-order Algorithms for Convex Optimization. *Journal of Automated Reasoning* 69(4):28. https://doi.org/10.1007/s10817-025-09741-w （Lean 4 / Mathlib）
36. Vajjha, K., Trager, B. M., Shinnar, A., & Pestun, V. (2022). Formalization of a Stochastic Approximation Theorem. *ITP 2022*, LIPIcs 237, 31:1–31:18. arXiv:2202.05959. https://arxiv.org/abs/2202.05959 （§10.2 随机收敛方向的已有形式化）
37. Tassarotti, J., Vajjha, K., Banerjee, A., & Tristan, J.-B. (2021). A Formal Proof of PAC Learnability for Decision Stumps. *CPP 2021*, 5–17. https://doi.org/10.1145/3437992.3439915 （§10.2 泛化界方向的已有形式化）
38. Degenne, R. (2025). Markov Kernels in Mathlib's Probability Library. arXiv:2510.04070. https://arxiv.org/abs/2510.04070 （Mathlib 概率/熵/KL 形式化的权威记述）
39. Ziegler, D. M., Stiennon, N., Wu, J., et al. (2019). Fine-Tuning Language Models from Human Preferences. arXiv:1909.08593. https://arxiv.org/abs/1909.08593

---

## 附录 A：核心定理清单（完整行号索引见补充材料 S1）

> 本表按族列出库内标识符与行号锚；各定理的抽象层/Real 层证明状态、条件性前提与开放项的一览视图见 §1.2 尾「表 1：定理状态总表」。

**补充锚表（正文 §1–§8 行号引用存档）**：正文 §1–§8 的行号引用已按标识符引用规范替换为定理/引理标识符，被移除的锚点逐条存档如下（行号基准 = §9.1.1 登记的 219 基线）：

三次清理补遗：

| 行号 |
|---|
| L112106 |
| L113775 |
| L113793 |
| L19086 |
| L19613 |
| L20153 |
| L20187 |
| L22903 |
| L23114 |
| L23146 |
| L23244 |
| L23828 |
| L40962 |
| L95498 |
| L95527 |
| L95551 |
| L96475 |


二次清理补遗（范围/接口定义/代码引用锚）：

| 行号 |
|---|
| L112330 |
| L18761 |
| L20554 |
| L20599 |
| L20607 |
| L21240 |
| L2263 |
| L23793 |
| L32576 |
| L32672 |
| L33417 |
| L40464 |
| L41819 |


| 标识符/上下文 | 行号 |
|---|---|
| `RealInterface` | L133 |
| `RealInterfaceEnhanced` | L217 |
| `proj_normalized` | L296 |
| `eviction_partition_increment` | L313 |
| `cauchy_real_exp_pos` | L13383 |
| `free_energy_kl_decomp` | L16259 |
| `gibbs_inequality` | L16629 |
| `min_free_energy_is_boltzmann` | L16838 |
| `pi_star_pos` | L18771 |
| `pi_star_normalized` | L18783 |
| `dpo_loss` | L19090 |
| `advantage_fn` | L19496 |
| `e zero (advantage_fn s)`` | L19497 |
| `importance_ratio` | L19502 |
| `is_objective` | L19515 |
| `dpo_implicit_reward` | L19620 |
| `exact_improvement_identity` | L19904 |
| `dpo_pair_loss` | L20111 |
| `dpo_total_loss` | L20153 |
| `dpo_total_loss_at_star` | L20171 |
| `rlhf_free_energy_kl` | L20290 |
| `对数几率比与逐对 DPO 损失定义如下` | L20880 |
| `dpo_loss_pair` | L20885 |
| `policy_improvement_mono` | L22065 |
| `policy_iter_backward_kl_step` | L22686 |
| `policy_iter_backward_kl_step_le` | L22790 |
| `policy_iterate` | L22879 |
| `policy_iter_norm` | L22890 |
| `step_kl_eta_bound` | L23114 |
| `policy_iter_kl_geom_step` | L23146 |
| `policy_iter_kl_geom_iter` | L23181 |
| `group_centered_second_moment` | L23972 |
| `group_variance_identity` | L24264 |
| `**逐 eps 余量形式**` | L32748 |
| `Real_RealInterfaceSetoidCore` | L33433 |
| `Real_RealInterfaceSetoid` | L39407 |
| `:= cauchy_real_exp_pos`` | L39450 |
| `:= cauchy_real_exp_plus`` | L39452 |
| `452）、`log_inv := cw_log`` | L39453 |
| `RealEnhancedReal` | L41115 |
| `real_dpo_loss_at_pi_star` | L42439 |
| `real_square_nonneg_eps` | L44842 |
| `real_expf_realizable` | L96364 |
| `real_exp_two_point_cvx_eps` | L112669 |
| `real_amgm_pointwise_eps` | L112817 |
| `real_interp_Z_le_one_eps` | L112890 |
| `real_step_kl_eta_bound_eps` | L113142 |


| 定理 | 文模块行号 | 内容摘要 | 前提/备注 |
|---|---|---|---|
| `rlhf_optimal` | L19049 | 对齐目标在 π* 处最大 | π 归一化且正（`normalized`/`positive_dist`）；接口前件 `beta_pos`/`Z_align_pos` 等 |
| `rlhf_optimal_unique` | L19128 | 最优策略唯一 | 同 `rlhf_optimal`（两策略均归一化且正） |
| `rlhf_suboptimality_gap` | L20554 | 次优间隙 = β·KL（前向 KL） | π 归一化且正；前向 KL 方向（与定理 4.8 的后向 KL 不同，见 §4.3/§10.2） |
| `rlhf_policy_improvement` | L20591 | 前向 KL 到 π* 不增 ⟹ 目标单调 | `p_old`/`p_new` 归一化且正；不含优势函数前提（勿与定理 6.3/6.4 混淆） |
| `policy_iter_backward_kl_step_le` | L22790 | 单步向后 KL 收缩上界：`KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1})`（定理 4.5 单步引理） | 策略迭代族 Section 变量：`eta_pos`/`eta_le_one`、`pi_t` 逐点正（§4.3.1） |
| `policy_iter_backward_kl_iter_le` | L22915 | 策略迭代向后 KL 加权递推上界（定理 4.5） | 同 `policy_iter_backward_kl_step_le`（迭代打包 `policy_iterate` 保归一化/正性） |
| `policy_iter_gap_diff` | L23000 | 间隙单步显式恒等式：改进量 == β·加权 KL 对（定理 4.6） | 同策略迭代族；`pi_t` 逐点正 |
| `policy_iter_gap_mono` | L23086 | 间隙单调不增（定理 4.7） | 同策略迭代族（经 `policy_improvement_mono`） |
| `policy_iter_kl_geom_step` | L23146 | 单步真几何收缩：`KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t)`（定理 4.8 前提，诚实接口 `step_kl_eta_bound`（L23114）下） | **诚实接口 `step_kl_eta_bound`（Variable，L23114）**；0 < η ≤ 1 |
| `policy_iter_kl_geom_iter` | L23181 | 向后 KL 真几何率上界 `(1−η)^t`（定理 4.8） | 同 `policy_iter_kl_geom_step`（诚实接口表述；接口的 Real 层对应物已在库内证明——`real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142），见 §4.3.1 状态脚注） |
| `real_rlhf_optimal_eps` | L43804 | RLHF 最优性 Real 层逐 eps 复刻（定理 4.9） | Real 层复刻；诚实接口 `real_kl_decomp_full` 等（零公理，全部可实例化） |
| `pi_star` | L18766 | 闭式最优策略（含 `opp`，即 e^{+r/β}） | 定义；依赖 `Z_align_pos` 正性前件（L18764） |
| `dpo_optimal` | L19096 | DPO 损失在 π* 处最小 | π 归一化且正（推论自 `rlhf_optimal` 取负） |
| `log_ratio` | L20880 | 对数几率比 log π − log π_ref | 定义；log 定义域隐含正性 |
| `dpo_loss_pair` | L20885 | 逐对 Bradley-Terry DPO 损失 | 定义 |
| `dpo_loss_at_pi_star` | L20892 | π* 处逐对损失 = 真实奖励差的对数几率 | 前提：`pi_ref` 正且归一化、`Z_align_pos`（π* 闭式） |
| `dpo_reward_is_implicit` | L19616 | 显式/隐式奖励逐点相等（命名桥引理：定义性后承，reflexivity；非独立结果） | 无前提（定义性后承，不计入并列贡献） |
| `dpo_reward_recovers_up_to_baseline` | L19626 | π* 处隐式奖励恢复真实奖励至基线 | 前提：π* 闭式（`log_pi_star`） |
| `dpo_reward_relative_exact` | L19717 | 隐式奖励差分 = 真实奖励差分 | 同 `dpo_reward_recovers_up_to_baseline`（基线消去） |
| `dpo_reward_diff_is_log_ratio_diff` | L19802 | DPO 隐式奖励差分 = 对数比差分 | 同 5.4（差分形式等价） |
| `dpo_total_loss_monotone` | L20181 | 逐对损失单调 ⟹ fold 总损失单调（不含 π*/改进方向） | 前提：逐对损失逐点不增（fold 泛单调；有限偏好列表） |
| `real_dpo_loss_pi_star_bounded_both` | L42715 | Real 层 π* 处损失双侧定量界：`r_l < r_w ⟹ 0 < L < log 2` | Real 层；前提 `r_l < r_w` |
| `real_dpo_reward_recovers_up_to_baseline` | L42761 | Real 层 π* 处隐式奖励恢复真实奖励至基线（定理 5.9） | Real 层复刻（定理 5.4 的 Real 值域版） |
| `dpo_loss_iter_step_le` | L23244 | 聚合损失 `dpo_loss` 单步沿改进轨道单调不增（定理 5.10） | 策略迭代族前提（同 4.5 区） |
| `dpo_loss_iter_mono` | L23256 | 聚合损失沿迭代轨道单调不增（定理 5.10） | 同 `dpo_loss_iter_step_le`（经 `policy_iter_norm` 保归一化） |
| `real_dpo_logit` | L54982 | Real 层单样本 DPO logit 损失 `ℓ(x) := −log σ(x)`（定理 5.11 定义锚） | Real 层定义 |
| `real_softplus_sigmoid_eq` | L55038 | Real 层损失形态连接：`−log σ(x) == log(1+e^{−x})` | Real 层恒等（无附加前提） |
| `real_sigmoid_deriv_mass_pos` | L55026 | `σ(x)·(1−σ(x)) > 0`（−log σ 二阶导的构造性正性证据） | Real 层（`σ(x)>0`、`1−σ(x)>0` 已证：L41819/L55017） |
| `real_dpo_logit_loss_decr` | L55075 | logit 损失严格递减：`x < y ⟹ ℓ(y) < ℓ(x)`（DPO 收敛单调前提） | Real 层；前提 `x < y` |
| `projected_distribution_minimizes_kl` | L95587 | 审计投影主定理：`KL(q‖proj(p)) ≤ KL(q‖p)`（§5.3；214-KL 块，219 复核未动） | 前提：`post_aud`/`Hp_norm`/`Hp_pos`/`HZ` + `Hq_fail`/`HlogZ`（显式前件；HlogZ 消解材料已在库内证明——`real_log_le_mono` L112106/`real_log_le_zero_of_le_one` L112121，见 §10.2 第 1 项 (e)） |
| `kl_sum_split` | L95527 | 审计精确分解：`KL(q‖p) == KL(q‖proj) + (−log Z_aud)`（§5.3） | 同主定理前提组（尾项求值 `kl_tail_eval` L95551） |
| `ppo_conservative` | L19526 | 裁剪目标 ≤ 未裁剪目标（前提 `advantage_nonneg`（L19497）） | **前提：`advantage_nonneg`（A ≥ 0，L19497）+ `pi_old_pos`** |
| `exact_improvement_identity` | L19904 | 真实改进 = 期望优势 − KL 惩罚 | 恒等（无附加序前提） |
| `ppo_monotonic_improvement` | L19940 | 代理优势非负 ⟹ 真实改进 | 前提：代理优势非负（`le zero (E−β·KL)`） |
| `kl_penalty_sufficient` | L19967 | KL 约束 + 优势条件 ⟹ 改进 | 前提：`KL ≤ eps` 且 `E ≥ β·eps`（定理 6.3 的显式 eps 形式） |
| `ppo_surrogate_raw_is_value_improvement` | L20720 | 代理目标改进控制价值改进（仅未裁剪代理） | 前提：`pi` 归一化且正、`p_old` 正；仅未裁剪代理（裁剪代理侧单侧组合 三件单侧组合定理已在库内证明，见 §6.3） |
| `real_ppo_conservative_eps` | L43556 | PPO 保守性 Real 层逐 eps 复刻（定理 6.6） | Real 层 eps 版；诚实接口 `real_min_le_l_eps` 等（`real_min` 无精确 `min ≤ r`） |
| `std_ppo_conservative` | L19559 | 标准 PPO 代理目标保守性（定理 6.7）——**定义性后承**（`min_le_l` 定义性直接推论，与裁剪结构无关；§6.2 注记） | **无前提**（正因定义性后承；任意符号 A） |
| `ppo_is_decomp` | L112398 | IS 目标 == 裁剪代理 + clip 误差的精确分解（定理 6.8，§6.3 主结果） | 无前提（恒等式） |
| `clip_error_nonneg` | L112408 | clip 误差非负（定理 6.9） | 无前提（min 在乘积内部） |
| `ppo_clipped_improvement` | L112439 | 裁剪代理非负 ⟹ 价值改进 `V(p_old) ≤ V(pi)`（定理 6.10；反向界为假不宣称） | 前提：裁剪代理非负（E1+E2+定理 6.5 组装） |
| `grpo_advantage_zero_mean` | L23915 | 组相对优势零均值 | 前提：`group_enum` 覆盖（`group_cover`）、`group_size_pos`；任意缩放 `c` |
| `grpo_variance_identity` | L24096 | 组**中心二阶矩**恒等式（非方差，未除以 G；定理 7.4） | 同 7.1（组枚举覆盖；未除 G，见 §7.2 术语说明） |
| `group_variance_le_raw_second_moment` | L24327 | 基线方差归约：`Var ≤ (1/G)·Σr²`（减均值降低二阶矩；定理 7.5） | **诚实接口 `square_nonneg`（Variable，L24301）**；`real_square_nonneg_eps`（L44842）为 Real 层正向证据 |
| `UpExtras219.counter_ex_indicator_sum_two` | L114140 | 无重复前提不可去反例：双副本枚举 indicator 求和 == 2 ≠ 1（定理 7.2，§7.2 主结果） | 双副本枚举（覆盖前提成立、`NoDup` 缺失） |
| `UpExtras219.counter_ex_reward_sum_two_c` | L114151 | 无重复前提不可去反例：双副本常数奖励总计 == 2c ≠ c（定理 7.3） | 同上 |
| `real_grpo_advantage_zero_mean` | L43100 | GRPO 组相对优势零均值 Real 层复刻（定理 7.6） | Real 层复刻（定理 7.1 的 Real 值域版；`real_group_size_pos` 等） |

**补充陈述一**（`ppo_surrogate_raw_is_value_improvement`，L20720）：

```coq
forall (pi p_old : S -> R) (Hpos : positive_dist p_old) (Hnorm : normalized pi),
  Id (sum_over_S (fun s => mult (p_old s)
     (mult (policy_ratio pi p_old s (Hpos s)) (advantage p_old s))))
     (minus (state_value pi) (state_value p_old)).
```

即未裁剪代理目标的期望恰为状态价值改进量 `V(pi) − V(p_old)`（逐点消去 `p_old·(pi/p_old) = pi` 后由和的线性完成）。

**补充陈述二**（归一化方差恒等式 `group_variance_identity`，L24264）：`Var == (1/G)·Σ r_i^2 − μ^2`，其中 `Var := (1/G)·Σ (r_i − μ)^2`；由中心二阶矩恒等式（定理 7.4）两侧乘 `inv(G)` 经分配与逆元消去推得。

---

## 附录 B：间隙恒等与改进条件定理的代数推导

以下给出 `rlhf_suboptimality_gap`（L20554）与 `ppo_monotonic_improvement`/`kl_penalty_sufficient`（L19940/L19967）的完整代数骨架：B.1 补足 §4.3 定理 4.3 的证明概要；B.2 给出 §6.2 改进条件定理（6.3/6.4）的推导（**注**：RLHF 定理 4.4 `rlhf_policy_improvement`（L20591）走次优间隙恒等 ×2 路线，见 §4.3 正文，与本附录 B.2 的 `exact_improvement_identity` 路线无关）。

### B.1 `rlhf_suboptimality_gap`

**目标**：`align_objective pi_star − align_objective pi == β · KL(pi ‖ pi_star)`。

推导：

1. 由 `rlhf_free_energy_kl`（L20290）把对齐目标改写为自由能形式：
   `align_objective p == −F[p]`（能量取 `−r`，温度为 `β`）。
2. 由 `free_energy_kl_decomp`（L16259）对 `p = pi`、Boltzmann 分布 `p_b = pi_star` 展开：
   `F[pi] == F[pi_star] + β·KL(pi ‖ pi_star)`。
3. 两侧取 `opp`，得
   `−F[pi_star] − (−F[pi]) == β·KL(pi ‖ pi_star)`，即
   `align_objective pi_star − align_objective pi == β·KL(pi ‖ pi_star)`。
4. 非负性由 `gibbs_inequality`（L16629）给出；`β > 0`（`beta_pos` L18755）保证间隙非负。

**要点**：该定理**不是**独立的新不等式，而是 `free_energy_kl_decomp` 在 RLHF 参数化下的一次移项重写。真正的数学内容已在 §3.3 的自由能分解中。

### B.2 `ppo_monotonic_improvement`（定理 6.3）与 `kl_penalty_sufficient`（定理 6.4）

**目标**：`E_{pi_new}[A_ref] − β·KL(pi_new ‖ pi_ref) ≥ 0` ⟹ `align_objective pi_ref ≤ align_objective pi_new`（定理 6.3，L19940）；其显式 `eps` 形式：`KL(pi_new‖pi_ref) ≤ eps` 且 `E_{pi_new}[A_ref] ≥ β·eps` ⟹ 同上（定理 6.4，L19967）。

推导（eps 形式；直接形式只需第 1、4 步）：

1. 由 `exact_improvement_identity`（L19904）：
   `align_objective pi_new − align_objective pi_ref == E_{pi_new}[A_ref] − β·KL(pi_new ‖ pi_ref)`。
2. 由 `β > 0` 与 `KL ≤ eps` 得 `β·KL ≤ β·eps`（`lt_mult_compat` / `le_mult_compat_weak`）。
3. 由假设 `E_{pi_new}[A_ref] ≥ β·eps ≥ β·KL` 得右端 `≥ 0`。
4. 故 `align_objective pi_new − align_objective pi_ref ≥ 0`，即改进成立（`le_minus_nonneg` 完成）。

**要点**：这是 `exact_improvement_identity` 与一次线性序传递的直接组合；`kl_penalty_sufficient`（定理 6.4）是 `ppo_monotonic_improvement`（定理 6.3）在显式 `eps` 条件（`KL ≤ eps`、`E ≥ β·eps`）下的重述。二者在数学内容上等价，保留两个陈述分别对应「恒等式形式」与「充分条件形式」的引用需求。

**归因注**：定理 4.4 的前提是「新策略到 π* 的前向 KL 不增」（证明经次优间隙恒等 ×2 + β 保序，见 §4.3 正文），本附录推导的对象是 PPO 改进条件定理（6.3/6.4），两者路线无关（`rlhf_policy_improvement` 实测 L20591）。

---

## 附录 C：Coq 证明骨架

> 本附录以「目标 → 关键引理 → 子目标 → 完成」的证明图形式，给出两个代表性定理的 Coq 层组装路径（tactics 级序列见代码库；此处给出关键引理调用链与每步的构造性要点，行号以 §9.1.1 登记锚为基准）。

### C.1 `policy_iter_backward_kl_step_le`（L22790）与 `policy_iter_kl_geom_iter`（L23181）的组装

**定理 4.5 单步引理 `policy_iter_backward_kl_step_le`（L22790）**：

- **目标**：`le (relative_entropy pi_star (pi_next pi_t pi_t_pos)) (plus (mult (minus one eta) (relative_entropy pi_star pi_t)) (relative_entropy pi_t (pi_next pi_t pi_t_pos)))`
- **关键引理**：恒等版 `policy_iter_backward_kl_step`（L22686）给出三 KL 精确分解
  `KL(pi*‖pi_{t+1}) == (1−η)·KL(pi*‖pi_t) − η·KL(pi_t‖pi*) + KL(pi_t‖pi_{t+1})`；
- **子目标 1**：可弃项非正——由 `gibbs_inequality`（L16629，KL ≥ 0）与 `eta_pos` 得 `le (opp (mult eta (relative_entropy pi_t pi_star))) zero`；
- **子目标 2**：恒等右端按环律重排（`plus_assoc`/`plus_comm`/`mult_comm`/`minus` 定义展开），使形如 `A == B + C` 且 `C ≤ 0`；
- **完成**：`le_plus_compat` + `plusA_opp_cancel_le` 型辅助（A == B + C、C ≤ 0 ⟹ A ≤ B）把恒等降为 le 版。

**迭代归纳 `policy_iter_kl_geom_iter`（L23181，定理 4.8）**（「归纳 + 代数」案例）：

- **目标**：`le (relative_entropy pi_star (projT1 (policy_iterate t pi pi_pos))) (mult (r_pow (minus one eta) t) (relative_entropy pi_star pi))`
- **归纳结构**：对 `t` 归纳；基例 `t = 0` 由 `policy_iterate` 定义与 `refl`/`le` 自反闭合；
- **归纳步（t → S t）**：
  - 关键引理 1：单步真几何收缩 `policy_iter_kl_geom_step`（L23146）——`KL(pi*‖pi_{t+1}) ≤ (1−η)·KL(pi*‖pi_t)`，其内部把 C.1 的 le 版递推与诚实接口 `step_kl_eta_bound`（L23114，`KL(pi_t‖pi_{t+1}) ≤ η·KL(pi_t‖pi*)`）组合，两 η 项抵消（`plusA_opp_cancel_le` 完成）；
  - 关键引理 2：归纳假设 IH：`KL(pi*‖pi_t) ≤ (1−η)^t·KL(pi*‖pi_0)`；
  - 子目标：两侧乘 κ := 1−η——κ ≥ 0 由 `le_minus_nonneg`（前提 `eta_le_one`）保证，保序乘用 `le_mult_compat_weak`，`mult_comm` 换形把因子放右端；
  - 关键引理 3：`r_pow` 结合律换形（`r_pow κ (S t)` 展开为 `mult κ (r_pow κ t)`，`mult_assoc` 重结合）；
- **完成**：序传递链：`KL(pi*‖pi_{t+1}) ≤ κ·KL(pi*‖pi_t) ≤ κ·(κ^t·KL(pi*‖pi_0)) == κ^{S t}·KL(pi*‖pi_0)`（`le` 传递性 + `r_pow` 结合换形）。

### C.2 `real_rlhf_optimal_eps`（L43804）的 Real 层 eps 证明模板

**目标**：`real_le (real_opp (real_free_energy pi Hpi)) (real_plus (real_opp (real_free_energy real_boltzmann_dist_r real_boltzmann_dist_r_pos)) (real_mult D eps))`，即 `J(π) ≤ J(π*) + D·eps`。

- **关键引理 1（常数消去桥）**：诚实接口 `real_kl_decomp_full`（L43730）把熵侧 KL 分解的常数差吸收进 `D`（`F(p) == F(p_b) + D·Σkl` 型），避免逐项常数额外 eps；
- **子目标 1（逐点抵消链）**：`log p == log p_b + kl_term` 逐点展开，经 Σ ext + `real_sum_over_S_add` + `real_kl_term_equiv` 把 KL 项收拢为 `Σkl`；
- **关键引理 2（KL ≥ 0 的 eps 版）**：`real_gibbs_sum_eps`——Real 层 KL 非负只有 eps 余量形式 `le zero (plus Σkl eps)`（构造性边界：非严格序不可判定，Real 层序关系以逐 eps 余量陈述）；
- **子目标 2**：`D` 正乘（`real_le_mult_compat` + comm 换形）把 `0 ≤ Σkl + eps` 提升为 `0 ≤ D·(Σkl + eps)` 的加权余量；
- **关键引理 3**：`le_plus_compat` 把 `F(p_b) ≤ F(π) + D·eps` 与自由能分解接口合并；
- **完成**：`real_opp_le_compat` 取负并消环恒等（`A == (A + opp C) + C` 型），得 `real_le (real_opp F(π)) (real_opp F(p_b) + D·eps)`。

**模板要点（"eps/3" 结构的库内实例）**：本定理的 eps 余量只在 `real_gibbs_sum_eps` 一步引入一次，由常数 `D` 加权为单一残差（误差源唯一）；单误差源定理采用单点引入策略，多误差源组合（如逐点 log 抵消与 gibbs 各自带余量）才需 eps/3 式分割——构造性实数中每引入一个 eps 余量即须在后续步骤显式管理其传播，误差账目越短越好。

### C.3 `rlhf_optimal_unique`（L19128，定理 4.2）的构造性唯一性骨架

- **目标**：`pi` 与 `pi_star` 均归一化且正、对齐目标值相同 ⟹ 两者逐点相等；
- **关键引理 1**：自由能分解 `free_energy_kl_decomp`（L16259）把「目标值相同」化为 `F[pi] == F[pi_star]`，再经分解恒等式得 `KL(pi‖pi_star) == 0`；
- **关键引理 2**：`gibbs_equality`（L16629，KL == 0 ⟹ 逐点相等，正分布前提）——构造性内容所在：KL 逐项和为零与逐项非负给出逐点相等的构造性提取（无排中分支）；
- **完成**：`pi_star` 闭式逐点等于 Boltzmann 分布（`align_boltzmann_is_pi_star`），故 `pi == pi_star` 逐点。
（完整战术序列见代码库；本骨架给出引理调用链与构造性要点。）

## 附录 D：验证脚本与构建日志（完整脚本与日志见补充材料 S4）

> 本附录给出 §9.1.1 Artifact 段所引验证的脚本与复现步骤（主文件 `ConstructiveWorld.v`：114,222 行，内容锚 SHA-1 `7BBE…`，.vo 锚 `B883…`；开发期路径为仓库内部基准，投稿版随 artifact 归档——含主库、模块层、验证脚本与日志，附 LICENSE 与 README——届时以包内相对路径与登记 DOI 为准；早期版本归档清单见 §9.1.1 Artifact 段）。

云认证状态：CI 连续 success，认证面自 143/144 逐波扩至 161→166→167→168→173→187→196→201→221→228→246，各波 coqchk 全绿（CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；波次明细以随论文 artifact 的变更记录为准。本文正文仍维持分层验证口径：81 条主定理/主定义最近一次全量 Print Assumptions CLEAN 于基态 198/206；其后新增内容以行首禁词零命中、全量编译与 coqchk 内核校验维持，未整体重跑；二者为不同验证面，不互相替代。完整认证波次见补充材料 S1/S4。「内核校验通过」与「假设摘要为空」是两个强度的断言（前者为本文现主张）；后者（冻结态全量 `Print Assumptions` 重跑 + CI 假设摘要断言固化）随投稿冻结态执行，口径见 §9.1.1。

1. **audit_full.ps1 审计（行首闭合标记 + 禁词扫描）**：脚本位于 `演变\.ablation\规划\audit_full.ps1`（单文件，无外部依赖）。复现：`pwsh -File 演变\.ablation\规划\audit_full.ps1 -Path ConstructiveWorld.v -Label 219`，输出口径 `lines=114222 Qed=2930 Defined=51 Admitted/admit=0 Axiom=0 Abort=0` （脚本 Qed 口径 = `^\s*Qed\.` 含缩进合计，与 §9.1.1 Artifact 段一致；2,930 与 51 为两类独立计数，不可相加）。
2. **`Print Assumptions` 批量验证**：验证文件与断言脚本位于验证脚本目录（`probe_full.v` 为 81 条主定理/主定义的 `Print Assumptions` 验证源；断言脚本打包定稿名 `assert_print_assumptions.ps1` 为 CI 化断言脚本：生成验证文件 → `coqc` 编译（`-Q` 映射仓库根为 `CW`）→ 扫描 log 断言无 `Axioms:` 非空段；`parse_pa_log.ps1` 为 log 解析器）。批量结果与判定规则：81/81 CLEAN（`Closed under the global context`）最近一次全量复核于基态 198/206；其后新增内容未整体重跑该 81 条批量（——新增内容经行首零命中 + `coqc` rc=0 + `coqchk` 维持；判定规则见包内文档与 §9.1.1 Artifact 段）。
3. **提取验证（Set 层可提取 OCaml）**：提取验证文件（历史产物，随包归档；`Extraction Language OCaml`，提取 `real_mult`/`cauchy_real_exp`/`cauchy_real_sin`/`cauchy_real_cos` 等主要定理链）。ocamlc 4.14.2 编译与数值样例运行步骤随 artifact 交付（脚本化复核口径：主要定理链提取 OCaml 零类型级 `__`、`ocamlc` 通过、数值样例运行）。**`__` 语义说明**：Coq 提取 OCaml 时，`__` 占位符通常对应不可计算/被擦除的内容——典型为 Prop 层证明残留或依赖不可计算字段的类型。主要定理链提取结果中**零类型级 `__`** 表明这些构造不含 Prop 残留，即 Set 层信息性证明（sigT/`And` 见证）成功提取为可执行 OCaml 代码（§9.1.1 可提取性段）。
4. **编译命令（独立环境复现）**：仓库根执行 `coqc -Q . CW ConstructiveWorld.v`（Rocq 9.0/9.1，RC=0，约 3–5 分钟）；`coqchk` 校验与全库禁词全量扫描（`Axiom / Admitted / Abort / Classical_Prop.classic` 零命中）随同一 artifact 链交付。**红线**：所有验证文件只 `Require + Print Assumptions`/`Extraction`，不修改源文件；`coqc` 输出以重定向（`*>>`）落 log，不走管道（沙箱边界，见断言脚本头部注释）。
5. **一键复现路径（部分执行）**：一键复现 = 依序运行 (i) **audit_full.ps1 审计**（本条第 1 项）与 (ii) **根验证文件三连**——**内容 Check**：`演变\.ablation\sc2_210_final\check210.v`（`Require Import CW.ConstructiveWorld` + 关键引理/定义 `Check`，210 快照关键符号在位核验；文件名与目录为 210 基态历史事实，219 基态下 `check210.v` 直接 `Require` 当前根 `ConstructiveWorld.v`（219）作同型核验亦可）；**`Print Assumptions` 验证文件**：`演变\.ablation\sc2_parallel\sL_assumptions\`（本条第 2 项，`probe_full.v` 与断言脚本）；**提取验证文件**：`演变\.ablation\sc2_210_final\probe_210.v`（本条第 3 项，210 基态历史目录）。四项均照本条第 1–3 项的命令与口径执行、`coqc` RC=0 即复现成功。把该步骤链封装为单一 `make audit` 命令（makefile/dune 集成，供 CI 复用）属工具侧任务，由库维护方另行产出——本附录先给出手工可逐条执行的路径链。

6. **模块化树复现路径（220 起的维护基线）**：仓库 `ConstructiveWorld-Main\`。① 锚核验：`ConstructiveWorld_Live\CW_ConstructiveWorld_219.v` 的 SHA-1 应为 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`（114,222 行）——与本文 §9.1.1 登记锚一致，保证全部行号引用有效；② 拓扑序增量编译：`ConstructiveWorld_vo\` 内 `bash build.sh`（.vo 已存在则跳过；基座 .vo 为信任缓存直拷，不在后台上下文全量重编）；③ 单模块重验：`coqc -Q . "" Up<Name>.v`；④ 内核校验：9.0 平台 coqchk（注意 .vo 不可跨构建复用、一律从 .v 重建）；⑤ 追加层汇聚件（`CW220_Extensions.v` 精简后形态）与未入汇聚清单按 HEAD 84e2de2 现态重列于补充材料 S1，可按第 1 项口径独立审计；⑥ **禁入项**：单文件拼接形态 `releases\CW_ConstructiveWorld_220.v` 的全量编译未闭合（顶层同名声明冲突等，登记于 `docs/BLOCKERS-220.md`），不得用作复现入口。本文正文引用仍以 219 锚为唯一行号基准（零平移）。

   7. **维护形态说明**：① 的锚核验现指归档原件——模块化树中的 `CW_ConstructiveWorld_219.v` 已改为 Require Export S01–S15 的薄壳聚合，114,222 行原文以归档形态承载（SHA-1 不变），行号引用经 S01–S15 分片累积偏移映射（保序、去头正文逐字节一致）。维护形态现按 HEAD 84e2de2 组织：编译清单 221 模块，Live_X 成果区 333 个 .v；云认证 CI 连续 success，认证面 221，各波 coqchk 全绿，全树构建与内核校验由 CI 认证面覆盖，拓扑序编译依 `order.txt`（S 系 → 219 壳 → 拓扑序独立件与 G 组）执行；旧汇聚件精简前形态与历史 CI 记录为早期形态记录，见补充材料 S1；

### D.7 req 代数地基对照（签名迁移第一阶段；自附录 C.4 移入——附录 C 保持证明骨架纯粹性）

签名迁移迁移第一阶段交付的 req 系代数地基模块 `UpReqAlgebra`（1,645 行，56 件 Qed，纯 term-mode、零 `Morphisms` 依赖）为后续各批的机械平移提供代数与序引理面；地基件与 Id 原件的代表性对照如下（完整对账见该模块文件头覆盖对账表，Id 原模块行号以 §9.1.1 登记锚为基准）：

| 地基簇 | 代表 req 件 | Id 原件 @ 行号 |
| --- | --- | --- |
| SimpleAlgebra（5 件） | `req_plus_zero_r` / `req_plus_opp_r` / `req_mult_one_r` / `req_mult_zero_r` / `req_mult_comm_rewrite` | L27894 / L27898 / L27902 / L27906 / L27910 |
| RingLemmas 代数核（代表件） | `req_opp_plus` / `req_mult_plus_distr_r` / `req_double_neg` / `req_two_pos` / `req_log_div` / `req_mult_minus_distr_l` | L369 / L389 / L437 / L489 / L652 / L837 |
| AlgHelpers（6 件） | `req_lt_id_r_loc` / `req_plus_exchange` / `req_minus_plus_congr_l` / `req_minus_factor`（`_pt`） / `req_inv_pos_mult_distr` | L95645 / L95651 / L95663 / L95675–L95684 / L95695 |
| 接口缺口桥（假设位保留） | `log_req_compat` / `log_inv_exp_neg_req`（模板形态①；Real 实例化留待接口扩展批） | setoid 接口缺字段（非 Id 平移件） |
| (c) 新机器（3 件） | `req_inv_pos_cancel` / `req_log_cancel` / `req_lt_plus_compat_{lt_le,le_lt}`（后者为**迁移第三阶段预留**：对齐定理链的序兼容位，本文正文定理未消费） | CW219 L21013/21018/21020 同位桥 |
| (d) 冻结（不迁，注记在案） | `attn_nat_to_R_pos`（nat 归纳件，双层并行） | L95724（随 `attn_nat_to_R` L95718） |

迁移第二阶段（分布/自由能/温度层，`UpReqDist` 91 件 + `UpReqTempEntropy` 14 件）直接消费该地基；两批的闭合状态与分批状态表见 §9.1.1。

### D.8 req 签名版清单对账位置与语义保真度分类（签名迁移第二阶段）

**清单对账表位置（91 + 14 件）**：迁移第二阶段交付的 req 系清单的对账表为模块源文件内的机器可对账记录——`UpReqDist.v`（3,571 行）：文件头覆盖对账（req 件名 → Id 原件 @ CW219 行号，如 `req_min_free_energy_is_boltzmann<-16838`、`req_gibbs_inequality<-16629`、GRPO 簇「req_grpo_* 14 件<-23828..24096..24264..24327」）与文件尾逐节合计行（FEP 基座 26 + FEP 续建 13 + KL 特化 2 + 温度层 4 + 稳态 1 + 概率分布 2 + 第二定律 1 + U2 辅件 2 + SqrtWitness 5 + 能量-交叉熵 1 + 代数补件 4 + 对偶 3 =「89 Qed + 2 Defined = 91 证明件」）；`UpReqTempEntropy.v`（1,565 行 / 14 Qed）：温度严格层余件的定理清单。迁移第三阶段交付件的对账同构（`UpReqAlign.v` 文件头盘点结论 + 签名迁移规划书附录 D 三列对账）。

**语义保真度三分类（每簇 req 版相对 Id 原件的语义关系）**：

| 分类 | 含义 | 迁移第二阶段代表簇 |
| --- | --- | --- |
| 精确对位 | 语句与 Id 版逐位同构，等式/序结论均为精确形态 | FEP/Gibbs 簇（`req_free_energy_kl_decomp`/`req_gibbs_inequality`/`req_gibbs_equality`/`req_min_free_energy_is_boltzmann`——序结论为精确 `le`，分布前提以显式 forall 前件内嵌，见 §3.3 签名）；GRPO 簇 14 件（`req_grpo_advantage_zero_mean`/`req_grpo_variance_identity`/`req_group_variance_identity` 等，等式为精确 `req` 形） |
| 假设位同构 | 序结论精确，但诚实接口假设以显式 forall 参数位保留（T2 形态①），非假设消去 | 归约簇 `req_group_variance_le_raw_second_moment`（`square_nonneg` 保持 Id 出口假设位） |
| eps 弱化对位 | 结论带 eps 余量（Id 版无） | 迁移第二阶段内无整簇落此分类；归约簇的 `square_nonneg` 前件其 Real 层正向 discharge 证据为 eps 形（`real_square_nonneg_eps`，L44842）——「经 Real 层正向 eps 证据桥承载」一词指该**前件 discharge 证据形态**，非定理结论形态（§7.2 迁移第二阶段标注的精确化） |

冻结件（plain 形不可导出、迁移第五阶段统一裁决）如 `ppo_conservative` 族与三件单侧组合定理的 req 版，见 §9.1.1。

### D.9 模块化树拓扑与追加层资产（artifact 现状；自 §9.1.1/§10.2 移入的审计细节）

**Artifact 登记细节**：单文件库 ConstructiveWorld.v（114,222 行，内容锚 SHA-1 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`，.vo 锚 SHA-1 `B8838C418A2CD2719FC295FEA1A1B8224E020C21`，发布锚登记 anchors L13；同源归档快照 `演变\代码库归档\ConstructiveWorld-219.v`；早期版本：218 版 112,462 行 / SHA-1 `409A8F10BD09C90925EA51ADA2628B67022CB9F0`（归档 `演变\代码库归档\ConstructiveWorld-218.v`）、217 版 111,775 行 / SHA-1 `131A7318BC2D2BCC014D906A5E30A4FFA2E76B04`（217 staging 工作副本 `演变\.ablation\sc2_217_stage\ConstructiveWorld.v`）、212 版 79,608 行 / SHA-1 `0503C05B5E11916DA6C570D95FFECAFC4C3932DF`（归档 `演变\代码库归档\ConstructiveWorld-212.v`）、210 版 71,223 行 / SHA-1 `CA52225CAA6F2AE7EBE5E201AF8105FCEB3D04F4`）。Rocq 9.1 编译通过（`coqc -Q . CW ConstructiveWorld.v` rc=0，.vo 已生成）；全部声明以 `Qed.`/`Defined.` 闭合（audit_full.ps1 审计：`^\s*Qed\.` 宽口径 2,930 处（严格行首 2,917 + 缩进 13）、行首 `Defined.` 51 处（两类独立计数，不可相加），零 Abort）；验证面口径（与本附录第 2 项一致）：`Print Assumptions` 批量（81 条主定理/主定义）最近一次全量 CLEAN 于基态 198/206 复核，其后新增内容以行首零命中、编译通过与 `coqchk` 维持，未整体重跑；`coqchk` 内核校验当前可用；提取验证最近产物为 210 基态历史产物，当前基线同型复核随 artifact 交付。

**末尾追加层块清单（行号基准 = 219）**：末尾追加层（L112,463–114,222）：Real 层插值不等式族（`real_exp_two_point_cvx_eps` L112669 / `real_amgm_pointwise_eps` L112817 / `real_interp_Z_le_one_eps` L112890 / `real_step_kl_eta_bound_eps` L113142，见定理 4.8 状态脚注与 §10.2 第 1 项 (a)）、GRPO NoDup 均匀化与 σ 见证族（Module `UpGRPO219`——`grpo_count_one` L113775 / `grpo_indicator_sum_one` L113793 / `grpo_uniform_mass` L113832 / `real_sigma_witness` L113928）与前提不可去反例（Module `UpExtras219`——`counter_ex_indicator_sum_two` L114140 / `counter_ex_reward_sum_two_c` L114151）。更早追加层（L79,609 起）：KLProjection 块（L95,420–95,604，§5.3 审计小节引用）、采样层三族（AttnDoeblin L95611–L96383 / AttnSqrt L96386–L96641 / AttnHardLimit L96643–L97866，含 `eq_inv2_double` L97558 与 TV 完成链 `tv_hard_le_decay_scale` L97618 / `hard_attention_limit` L97679，见附录 D.10 第 9 项）与 Real 层支撑族（`real_log_le_mono` L112106 / `real_log_le_zero_of_le_one` L112121 / `ppo_is_decomp` L112398 / `clip_error_nonneg` L112408 / `ppo_clipped_improvement` L112439）。

**220 起的维护形态（artifact 面现状，按 HEAD 39d81aa 重列）**：220 起维护形态已演进至 HEAD 39d81aa——编译清单 246 模块，Live_X 成果区 356 个 .v；云认证 CI 连续 success，认证面 246，各波 coqchk 全绿（CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；219 内容锚在模块化树中逐字节未动（本地 `CW_ConstructiveWorld_219.v` SHA-1 与本文登记一致，114,222 行）；早期模块拓扑、CI 记录与汇聚件形态不再作为现态，重列于补充材料 S1。两点口径须分清：其一，该模块化是**基座不动的工程打包**，不是「按语义边界切分基座」的重构，亦不是定理级签名迁移（§10.2 第 1 项，已闭合）（两层口径不得混写）；其二，单文件全量拼接形态 `CW_ConstructiveWorld_220.v`（129,396 行）目前**仅为源码合并形态**——其全量编译未闭合，阻塞点为追加文本与基座吸收内容的顶层同名声明冲突（如 `sqrt_witness`，L114786）及同类跨件同名 8 件、Q_scope 泄漏、6MB 级编译的上下文阻塞（登记于 `docs/BLOCKERS-220.md`），该形态不得表述为「编译通过」。论文行号锚保持 219，不随认证面扩波平移；模块拓扑、Qed 计数、Extensions 汇聚件与未入汇聚清单见补充材料 S1（按 HEAD 39d81aa 重列）。

**范围外库状态披露**（不属本文四族对齐目标理论贡献面）：截至 HEAD b657aff，B 路 Banach 推广已闭合至实例面——UpReqBanachExpAddEq（exp 加法交换性）已闭合并云认证，ExpOppOne/InstPre/InstEMult 与 BanachCauchyD 均已认证，实例面 UpReqBanachInstReal 与 BanachNoHyp/BanachNoHypNorm、UpReqBanachNormOpp/UpReqBanachSepThm/UpReqB4TwoStage 已闭合；同两波含 C 路 Padé 正尾线（闭合至 n=2 旗舰 cpf_exp_pos_final_n2）、UpReqLpoEquiv（LPO 等价）等新数学，及消融验证工作完成（S 系 Psatz 源侧移除、实例非空性 Real 载体 39/39 终态）与 HV 第三方件本地重编验证收讫。上述结果不进入本文 RLHF/DPO/PPO/GRPO 四族单步目标理论的 scoped claim，亦不改变 §2.3 首次条件；列此仅为 artifact 状态完整性披露；详表见补充材料 S1。

**维护形态说明**：维护形态现按 HEAD 39d81aa 组织——基座拆为 S01–S15 保序分片（219 原文逐字节保真）、小件并入 G 系合并组、枢纽/大型件保持原名；全树构建与内核校验由云认证覆盖（CI 连续 success，认证面 246，各波 coqchk 全绿；CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；S 系拆分为保序机械拆分，不改动任何定理内容；「工程打包 ≠ 语义边界重构」的口径区分在新树下同样适用。

**模块化重构的优先级评估（建议性质，非已排期工程；自 §10.2 移入）**：单文件形态（114,222 行〔219 基态〕，见 §9.1.1 Artifact 段）保证零外部依赖与 SHA-1 内容锚定，但阅读/编译/并入的维护成本随库增长。**优先级取舍**：若把模块化拆分放在签名迁移（§10.2 第 1 项，已闭合）之前，可先行降低单文件维护成本，但拆分将增大签名迁移的跨文件追踪与 Proper 注册协调面（迁移为 Id→req 的全库机械替换，在单文件内一次成型最易审计与逐族回归，见 §10.2 第 1 项）；若把模块化拆分放在签名迁移之后，则可先在已锚定（SHA-1）的单文件上完成签名迁移与回归，再按稳定后的语义边界机械拆分，拆分不改变任何定理内容。**本文建议维持「先签名迁移（已闭合）、后模块化拆分」的既成顺序**——与 §9.1.1 单文件设计决策一致；模块化按「抽象层签名对接完成后按语义边界切分（§3 基座 / §4–§7 算法族 / §9 边界与实例）」启动，属路线图建议而非承诺排期；模块化组织在 Coq/Rocq 大型验证工程中的代表性先例为 CompCert [29] 的多 pass 架构。


---

### D.10 未来工作（详述；§10.2 各项的完整文本）

- **（§10.2 第 1 项尾注）已闭合项**：主恒等式 `esq_eq_corr`（L12837）及收尾簇 `exp_even_neg_pos`（L12969）`exp_partial_tail_pos`（L13011）已证明，Real 层 `cauchy_real_exp_pos`（L13383）亦已闭合，exp 正性链至此完整；`exp_neg_pos` 字段已由 setoid 系接口实例回填（`Real_RealInterfaceSetoid`（L39407）中 `exp_neg_pos := cauchy_real_exp_pos`），Boltzmann 分布的构造性基底已实例化——余下仅第 0 项的抽象层签名对接（消费该实例）。
- **（§10.2 第 5 项）**：**采样层的温度两极与硬注意力极限（注记：属采样管道层，非本文目标理论本体，不改变 §2.3 scoped claim——§9.2 第 6 项）**：库内已证的两族采样层定理（AttnDoeblin 与 AttnHardLimit；T→∞ 端与 T→0 端，L95611–L97866），为注意力 softmax 的温度动力学提供显式界。**T→∞ 端（有界 logits softmax 核的显式 Doeblin/TV 收缩，AttnDoeblin 族）**：`u_tv_contraction`（L95931——双点 TV 收缩 `tv(Kμ,Kν) ≤ (1−δ)·tv(μ,ν)`，参考分布只需归一化，免平稳性/免详细平衡/免 transition 非负前提）、`u_tv_iter`（L96019——几何率 `(1−δ)ⁿ`）、`bs_minorization`（L96286——显式 Doeblin 下界 `δ*·U ≤ K(s,·)`，δ* := `lo·lo` = `e^{−2Δ/T}`，经 `bs_lo_hi_eq`（L96181）精确化、无 eps 损耗）、`bounded_softmax_tv_contraction`/`bounded_softmax_tv_iter`（L96331/L96344——有界 logits（−Δ ≤ z ≤ Δ）softmax 核的收缩率 `(1−e^{−2Δ/T})ⁿ`）：T 增大则单步近全混合。**T→0 端（硬注意力极限，AttnHardLimit 族，已闭合）**：词表/计数机器（`count_token` L96860/`removeT` L96871/`split_count_one` L96992/`sum_pos_nonempty_aux` L97061 等）与温度权重定义（`factor_T`/`ZT`/`w_T`/`tv_hard`，L97146–L97177；`decay_T` := `e^{−γ/T}`，L97173）及 `vocab_len_pos`（L97540）已在库内；**TV 完成链**——`eq_inv2_double`（L97558，根域自足化）、`tv_hard_le_decay_scale`（L97618，逐固定 T 的上界 `tv_hard T ≤ |vocab|·e^{−γ/T}`）与 `hard_attention_limit`（L97679：T→0 的 TV 收敛、**∃T₀ sigT 量词翻转**——`∀ eps>0, ∃T₀>0, ∀T（0<T<T₀）, tv_hard T ≤ eps`，Qed L97864）——**量词翻转已机器检查**，T→0 半边由「未闭合/闭合中」状态升格为库内定理（该族计 39 处行首 Qed）；可选温度窗口定理（`∃T₁T₂`：`T < T₁ ⟹ TV(w_T, δ_m) ≤ eps` 且 `T > T₂ ⟹ TV(w_T, U) ≤ eps`）的两半现已分别机器检查——T→0 半边即上述 `hard_attention_limit`（在根）；T→∞ 半边为 220 模块化树追加件 `UpTempWindow.temp_window_T_infty`（`∀eps>0, ∃T₂>0, ∀T>T₂, tv_unif T ≤ eps`，sigT 量词翻转；69 处 Qed（`^\s*Qed\.` 口径），经内核校验，并收入 `CW220_Extensions.v`）。两半的 TV 极限对象不同质（δ_m 点质量 vs 均匀分布 U）、分居根与模块，「∃T₁T₂ 双端合一」的单一陈述未合成，仍属开放。**红线（与第 7 项同口径）**：上述 TV 层几何率**不构成**目标间隙 `J*−J(π_t)` 的收敛材料——目标间隙几何率需 KL↔TV 的 Pinsker 型传递（库内该方向已有部分材料，其与降档边界见现行 §10.2 第 4 项），TV 率仅作采样层独立陈述，不写入 §4.3.1 收敛主张。
- **（§10.2 第 1 项 (a)–(g)）**：**库内新增定理的 discharge 与消费路线（除已注明在库内证明者外均为开放计划，非已证）**：(a) **`step_kl_eta_bound` Real 层对应物**（核心 discharge——已在库内证明：`real_interp_Z_le_one_eps`（L112890）/`real_step_kl_eta_bound_eps`（L113142）等四件，见第 8 项）；(b) **GRPO 均匀均值（NoDup discharge——已在库内证明）**：`UpGRPO219.grpo_count_one`（L113775）/`UpGRPO219.grpo_indicator_sum_one`（L113793）/`UpGRPO219.grpo_uniform_mass`（L113832）（每元素在无重复枚举中恰计一次 ⟹ indicator 求和 == 1 ⟹ 每 delta_j 在组均值中质量恰为 1/G）已机器检查——构件（词表计数机器族 `count_token`/`removeT`/`split_count_one`（L96992，唯一元素计数拆分）等，对元素类型泛型、仅依赖可判定相等与 list 归纳）平移至 GRPO `Group` 枚举 + NoDup（Set 层 `nodup_g`）前提后机械闭合；前提不可去反例已定理化——双副本枚举下 indicator 求和 == 2 ≠ 1 且常数奖励总计 == 2c ≠ c（`UpExtras219.counter_ex_indicator_sum_two`（L114140）/`UpExtras219.counter_ex_reward_sum_two_c`（L114151），§7.2 定理 7.2/7.3 的库内登记）；(c) **GRPO 标准化优势的单位二阶矩（σ 见证核心已在库内，单位矩全装配仍开放）**：`real_grpo_standardized_second_moment`（`∃σ>0`：σ² == 中心二阶矩 ∧ `(1/G)·Σ(A_i/σ)² == 1`）尚未在库内实现；其构造性 σ 见证核心已在库内——`real_sqrt_exists`（L96475）使 σ := √Var 可构造（Or 前提左支携带正间隙证书，恰与除法所需正性衔接），σ sigT 见证 `UpGRPO219.real_sigma_witness`（L113928：`forall Hvar : real_lt real_zero Var, sigT (fun sigma => And (real_lt real_zero sigma) (real_eq (real_mult sigma sigma) Var))`，Var 为组内中心二阶矩）与投影三件 `UpGRPO219.proj_sigma`/`proj_sigma_pos`/`proj_sigma_sq`（L113948/L113953/L113961）及四因子交换辅助 `UpGRPO219.real_mult_exchange`（L113872）；单位矩全装配（`(1/G)·Σ(A_i/σ)² == 1`，经 `inv_pos_mult_distr`（L95695）吸收 Var）为精化开放项（§7.1 注记同步）；(d) **PPO clip 单侧误差恒等式（已在库内证明，§6.3 定理 6.8–6.10）**：`ppo_is_decomp`（L112398，IS 目标 == 裁剪代理 + clip 误差的无前提恒等式）、`clip_error_nonneg`（L112408，clip 误差非负，无优势符号前提）与 `ppo_clipped_improvement`（L112439，裁剪代理非负 ⟹ 价值改进——三件齐备的**单侧**闭合）已机器检查（组合：逐点恒等 `u == min(u,c) + (u − min(u,c))` + `sum_over_S_add` + 定理 6.5，无优势符号前提）；**反向界维持不宣称**——无界比率（ρ → ∞）下误差 `A·(ρ − 1 − ε)` 无界，无常数 C 使「价值改进 ≤ 裁剪代理 + C·eps」型上界成立（经典反例，源模块头注原文）；(e) **审计前提 discharge（§5.3 的 HlogZ——消解路径已在库内闭合）**：`le (log Z_aud) zero` 的消解材料——log 单调 le 版 `real_log_le_mono`（L112106：lt 支 `real_log_lt_mono` / eq 支 `real_log_wd` 逐支组装）与直用形态 `real_log_le_zero_of_le_one`（L112121：`Z ≤ 1 ⟹ log Z ≤ 0`），配既有 `Z_aud_le_one`（L95459，+ p 归一化 ⟹ `Z_aud ≤ 1`）与 `log 1 == 0`（`real_log_one`）——HlogZ 消解路径闭合；`free_energy_with_audit_decomp` 蓝图（审计接入 §8 统一自由能视角：`F[proj] == F[p] + (−log Z_aud)` 型）未实现；(f) **`Z_align_pos` 与 `square_nonneg` 的 Real 层镜像**：`Z_align_pos` 的 Real 层装配可经 `sum_pos_nonempty_aux`（L97061，非空表逐项正 ⟹ 和正，Real 层 list 形态）+ `cauchy_real_exp_pos` 平移；`square_nonneg` 的诚实完成为 Real 层镜像 `real_group_variance_le_raw_eps`（见第 8 项）——两件均尚未在库内实现；(g) **Real 层 eps→精确形态完成引理族（已实现，独立模块 `UpRealLeB.v`，四项验证通过）**：`real_le_b`（Bishop 形非严格序谓词，`∀eps>0, x < y + eps`）定义、单向桥 `real_le_to_le_b`（`real_le ⟹ real_le_b`）、eps/2 完成引理 `real_le_closure_b`（前提：残差权系数的显式正性证书；`e₀ := eps'·inv(2·D)` 换形路线，零稠密性消费）与定理 4.9/6.6 的 Bishop 形对应物 `real_rlhf_optimal_B`（完整升格：定理 4.9 的 `D` 正性证书 `D_pos` 为节内既有变量，零新增前提）/`real_ppo_conservative_B`（条件升格：定理 6.6 的 `E := Σ π_old·adv` 无内在正性供给链，对应物语句补 `E > 0` 显式证书前提——该模块唯一新增前提；无证书情形定理 6.6 维持 eps 形陈述）——证书供给链核查（`D` 与 `E`）已随实现完成；Or 形「精确版」不可证论证（取 `(x, y, D) := (real_min a b, a, 1)`，与 §9.4 例一相抵）入该模块尾注备注。数学路径、可及/不可及形态的分界与前提分析见 §9.4 例二（Or 形「精确版」不可达，(i) 条论证；双侧结论的详注见 (iv) 条）；本项闭合不改动任何既有定理陈述，仅以独立模块形态追加更强表述形态。**补注**：本条详述止于 (g)；§10.2 第 1 项另含 (h) 与 (i)——其中 (h) 策略迭代族的 Real 层迭代镜像已由模块层机器检查（`UpStepKLM3.real_iter_kl_geom`、`KLWallClosed.klc_closed_powb_mono`），登记见 §10.2 第 1 项 (h)。

## 附录 E：中英术语对照表

本文中文正文与库内英文标识符/标准术语的固定映射如下（按正文出现序）：

| 中文术语 | 英文/库内对应 | 备注 |
|---|---|---|
| 诚实接口 | honest interface（explicit premise / undischarged hypothesis） | 显式声明为 Section 前件的未消解假设，§1.3/§3.4 |
| 双层并行 | dual-layer parallel carrying | Id 层陈述与 Real 层逐 eps 复刻并行承载同一数学内容，§1.3/§9.1.1 |
| 冻结双层件 | design-frozen dual-layer item | 签名未迁移、双层并行承载的定理件，§9.1.1 |
| 签名迁移 | signature migration | 抽象 Id 签名到 setoid/req 实例签名的系统迁移，§1.2 |
| Real 层逐 eps 复刻 | Real-layer pointwise-eps replica | 柯西实数层上的逐 eps 余量形态直接证明，§1.3 |
| 逐 eps 技术 / eps 余量 | pointwise-eps technique / epsilon slack | Bishop 形态方法学，§3.1/§9.3 |
| Or 形序（析取序） | disjunctive order encoding（`real_le = Or lt eq`） | §3.6 四层角色表 |
| Bishop 形序 | Bishop-style order（`∀eps>0, x < y + eps`） | §3.6/§9.4 例二 |
| 闭合引理 | closing lemma（`real_le_closure_b`） | 逐 eps 余量族到 Bishop 形的完成，§9.4 例二 |
| Set 层信息性证明 | Set-layer informational proof | 可提取（OCaml）的证明层，§1.3/§9.1.1 |
| 归一化/逐点正 | normalized / pointwise positive | 分布前提 `normalized`/`positive_dist`，§3.2 |
| 反例定理（前提不可去） | counterexample theorem（irreducible premise） | GRPO NoDup 反例，§7.2 |
| 分层验证口径 | layered verification account | 81 条 PA 审计面 + 其后维持面，§9.1.1/附录 D |
| 版本对照 | version cross-reference | 198/206、219、39d81aa、356（Live_X）四标识，文首对照表 |
