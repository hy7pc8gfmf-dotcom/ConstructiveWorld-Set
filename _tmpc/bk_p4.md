# 构造性梯度动力学的显式迭代预算收敛定理：PCT 必要条件侧参照

**英文标题**：Constructive Convergence Theorems with Explicit Iteration Budgets for Gradient Dynamics: A Necessary-Condition-Side Reference for PCT


**作者**：王宝军、夏挽岚（通讯作者，xiawanlan33@163.com）、祖光照、周志农、高雪峰

**Authors**: Baojun Wang, Wanlan Xia, Guangzhao Zu, Zhinong Zhou, Xuefeng Gao. *Corresponding author: Wanlan Xia (xiawanlan33@163.com).*

---

**基线与验证状态（双轨）**：本文行号、定理名与附录索引以冻结基线为基准；验证、认证、CI、模块数与 PA 挂账状态以当前真态快照为准。当前真态快照：HEAD=39d81aa（成果接入与注册收尾波），编译清单 246 模块，Live_X 356 个 .v，CI 连续 success，认证面 CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证；其后另有成果接入与注册收尾波推进中，当前基态以随论文 artifact 的变更记录为准。补充材料 S1 记录冻结基线分片、当前真态快照与逐项实测。

**双版体系**：中文规范版为母版；正式版为投稿面（送审对象）。本文为正式版，术语、数字与开放/闭合状态与母版逐项一致；差异以母版为准。

**关于标题术语的说明**：本文在正文中使用「资源受限」时，均取严格含义：**显式迭代预算**（该词不出现在正式标题中）——定理 4.10（`ConvergenceCauchy.iterate_cauchy_explicit_N`）构造性地给出满足闭式条件 `log(a·κ^N) ≤ log ε` 的显式迭代预算 N（其中 a := |η|·|g(E_A)|·S，S := 1/(1−κ)），使「资源受限」成为库内可核验的形式化事实（§4.8）。该词**不**覆盖位精度、内存或计算复杂性类资源：本工作未讨论有限精度算术下的误差传播，也不涉及复杂度类上界/下界分析（§6.2 第 5 条）。标题中的「必要条件侧参照」指本文定理族对命题汇聚理论（PCT）「吸引子 ⟹ 真值」主张的定位：只承担该主张必要条件一侧（动力学收敛构件）的机器检查，不声称任意能量景观上的充分性（术语定义见 §1.1 末）。



---

## 摘要（Abstract）

本文中「资源受限」按 §1.1 术语（显式迭代预算）理解：对给定容差 ε>0，定理 4.10 在抽象接口层经 r_arch_pow 见证构造 N(ε)，其具体 Real 层对应物（显式预算、闭式对数判据与尾界）已在库内以独立模块形态机器检查并产出可执行实现（§7.2 登记）。不覆盖位精度、内存或复杂度类资源。在这一含义下，本工作报告 ConstructiveWorld 库中一维梯度下降动力学的构造性收敛定理族。全部结论在零全局公理、零 Admitted、零 Abort 的构造性纪律下给出：该纪律指库内无 `Axiom`、无 `Admitted`，不等于无假设——定理对显式声明的 Section Variables 与接口字段成立，所有分析前提（严格凹性、Lipschitz 连续性、几何衰减 `gradient_abs_decay`、几何击穿 `r_arch_pow`、完备性 `cauchy_complete` 等）均显式声明为 Section `Variable`，随 Section 关闭自动泛化为定理前件。验证按四项纪律执行：全量编译退出码为 0，Print Assumptions 返回 Closed under the global context，提取验证无证明残留，coqchk 内核校验通过（合称四项验证纪律）。收敛链完整机器检查：梯度迭代序列柯西（`iterate_cauchy`）、极限存在（`iterate_lim_exists`）、极限处熵梯度为零（`grad_squeeze_zero` 与组装定理 `dynamics_converges`）；主贡献是显式闭式预算定理 `iterate_cauchy_explicit_N`：给出 N 使 `log(a·κ^N) ≤ log ε` 且对任意 m,n ≥ N 有 `metric(x_m,x_n) < ε`，其中 a := |η|·|g(E_A)|·(1/(1−κ))。本文将定理族定位为 PCT「吸引子 ⟹ 真值」主张必要条件侧的可核验参照：在一维严格凹设定、初始梯度非零前提的起点范围内，两处结构差距（驻点 ≠ 全局最优、单轨收敛 ≠ 全局吸引）均在 `lim` 语义层闭合；不声称充分性，也不声称 PCT 主张本身成立。全部存在性结论为 Set 层构造（sigT/And）；可提取性在抽象接口层经 `r_arch_pow` 前提见证，提取验证覆盖 Real 层核心构造，模块层 Real 载体（§7.2 登记）另有独立提取实现。显式性语义限定见 §1.1 术语，前提范围注见 §5.2.1，「资源受限」严格含义的边界见 §6.2。

**Abstract (English)**

We report a constructive formalization, in the ConstructiveWorld library, of a family of explicit-iteration-budget theorems for one-dimensional gradient-descent dynamics. Under the zero-global-axiom, zero-Admitted, zero-Abort discipline, the theorems are proved relative to explicitly declared Section variables and interface fields. Verification follows four disciplines: full compilation exits with code 0; Print Assumptions returns Closed under the global context; extraction has no proof residue (Obj.magic = 0); and coqchk kernel checking passes. "Explicit iteration budget" means: for any ε>0, a natural number N is constructed from library-proved lemmas such that d(x_m,x_n)<ε for all m,n≥N, parameterized via the geometric-domination premise r_arch_pow; N depends on ε, κ, η, |g(E_A)| and S=1/(1−κ), while L enters only indirectly through the theoremization of the contraction factor. Its concrete-Real counterpart (explicit budget, closed-form logarithmic criterion, tail bound) is machine-checked in the library as a separate module with an executable extraction (§7.2); the body keeps the abstract-interface statement, and that counterpart is therefore not an open item. Bit precision, memory, and complexity-class resources are not covered. Proposition Convergence Theory (PCT) is used only as a necessary-condition-side reference: we machine-check dynamical convergence components and do not claim sufficiency, nor do we claim that the PCT thesis itself holds. To the authors' knowledge, within the zero-global-axiom, zero-Admitted discipline, this yields an explicit budget with the closed-form logarithmic condition log(a·κ^N) ≤ log ε in the stated setting. See the main text for precise boundaries.

---

## 1 引言

### 1.1 动机

梯度下降及其随机变体是机器学习优化的基础。经典分析通常依赖紧致性、Bolzano–Weierstrass 定理或经典实数的完备性公理；这些论证在构造性框架中要么不可用，要么需要把依赖的前提显式化。ConstructiveWorld 项目的目标之一，是在同一零公理基座内为梯度动力学提供可审计的收敛定理，并把它们连接到更广泛的纲领。

命题汇聚理论（Proposition Convergence Theory, PCT）主张：受约束的梯度流会收敛到吸引子，而吸引子对应于命题的真值。这一「以动力学实现语义」的方向与自由能最小化纲领同构——把认知/物理过程看作能量景观上的动力学、把稳态解释为最小自由能结构（free-energy principle, Friston 2010 [6]）；PCT 进一步要求吸引子处的损失取全局最优（真值）。把该纲领从哲学/隐喻提升为机器检查的形式化，需要先在低维能量景观上建立收敛定理与可核验的差距地图（§5.2.2），再推广到高维/层级命题景观；本文承担前者。

**术语（首次出现的严格定义）**：

- **几何击穿（archimedean breakthrough）**：接口前提 `r_arch_pow` 所断言的几何击穿性质——对任意正的 a 与 eps，存在 N 使 `a·κ^N < eps`，即「任意正量乘以几何衰减因子 κ^N 终将跨过任意小阈值」；它是柯西收尾步骤中代替经典阿基米德性/紧致性论证的构造性接口（行号见附录 B）。
- **显式迭代预算**：对给定 ε > 0，预算 N(ε) 是由库内已证引理构造、满足 ∀m,n ≥ N(ε) 有 `metric(x_m,x_n) < ε`、并附带闭式条件 `log(a·κ^{N(ε)}) ≤ log ε` 的自然数。**显式性限定**：N(ε) 的显式性是**抽象接口层**（Section `ConvergenceCauchy`，`Context {RI : RealInterfaceEnhanced}`）的 Set 层 sigT 存在性见证——经 `r_arch_pow_log_budget` 由几何击穿前提 `r_arch_pow`（附录 B）的见证供给，故「随定义可提取为 OCaml」指以该接口前提为输入参数的构造提取（提取验证覆盖 Real 层核心构造，见 §6.3）；在具体 Real 层，不依赖该前提的对应物已在库内以独立模块形态机器检查——几何击穿显式定理 `r_arch_pow_real`、闭式对数判据 `budget_cond_sufficient`、尾界 `geo_tail_budget`/`budget_min_tail`（模块 `UpBudgetReal`，并经代码提取产出可执行实现），故该项**不属开放问题**，登记见 §7.2；本文正文陈述维持在抽象接口层，模块层载体不并入正文主张。本工作中「资源受限」的严格含义即迭代预算意义上的资源。
- **必要条件侧参照（necessary-condition-side reference）**：本文只机器检查 PCT 主张「吸引子 ⟹ 真值」中动力学侧（收敛到驻点、驻点处梯度为零、驻点唯一）的构件并给出其显式预算，不声称在任意能量景观上「全局吸引 ⟹ 全局最优」的充分性；故本文定理族是该主张的必要条件一侧的可核验参照，而非对主张本身的确认（§5.2）。

### 1.2 贡献
**术语约定**：Print Assumptions 返回 Closed under the global context 指该定理在全局上下文中无任何公理依赖。前提分三类：全局 Axiom（本文无）、接口 Variable、Class 字段；后两者是定理的显式前件，与全局公理不同。显式迭代预算的定义与限定见 §1.1 术语。库内验证记录编号仅用于补充材料中的审计对照，不作为数学对象名。

1. **显式迭代预算（主贡献，「资源受限」的严格含义）**：显式预算定理（库内名称 `ConvergenceCauchy.iterate_cauchy_explicit_N`）把存在性柯西点升级为满足闭式条件 `log(a·κ^N) ≤ log ε` 的显式预算 N(ε, κ, L, η)（a := |η|·|g(E_A)|·S，S := 1/(1−κ)，经 `r_arch_pow_log_budget` 击穿，对数单调性由 `log_lt_mono_cc` 供给；N 的显式性为抽象接口层经前提 `r_arch_pow` 见证的 Set 层构造；Real 层不依赖该前提的对应物已在库内以独立模块形态机器检查（模块 `UpBudgetReal`，§7.2 登记）——语义限定见 §1.1 术语；L 经 κ 定理化的收缩因子进入预算，见 §6.3.1）。详细陈述见 §4.8。
2. **收敛链的完整机器检查**：柯西性 `iterate_cauchy`、极限存在 `iterate_lim_exists`（经抽象完备性字段 `cauchy_complete`）、梯度夹逼为零 `grad_squeeze_zero` 与组装 `dynamics_converges` 构成完整链，每条路径的前提链显式、可审计（§4）。
3. **κ 定理化（把几何衰减前提从 Variable 提升为定理的实质步骤）**：正分支与符号已知情形已在库内实现——μ-强凹接口 `strong_concavity` 下 `gradient_step_contraction`、`gradient_step_abs_contraction`（κ := 1−ημ）、`gradient_iterate_abs_decay`、`grad_decay_positive_iter`；Real 层全套平移见 Section `RealKappa`，符号已知双分支见 Section `RealKappaSignReal`，条件化全符号版 `real_grad_decay_full_sign_iter`（需显式三分假设 `real_sign_dec`）。全符号无条件版需整体三分律（LPO），构造性实数不可实例化——此边界如实记录于 §6.3.1（状态表见 §6.3.1，行号见附录 A）。
4. **PCT 差距闭合**：差距一（驻点 ≠ 全局最优）经切线不等式接口 `entropy_tangent` 闭合：`gradient_zero_entropy_max` 与 `gradient_zero_neg_entropy_truth`；差距二（单轨收敛 ≠ 全局吸引）经弱三分 `weak_trich` 闭合：`gradient_zero_unique`、`unique_attractor`、`attractor_converges_unique_truth`。在一维严格凹设定、以接口谓词 `lim` 表述的收敛语义中、初始梯度非零前提的起点范围内，差距一与差距二已闭合；但将闭合结论组装为 `CoreClaim2` 字面实例的内容层 corollary 仍开放（§5.2.1、§5.2.2；前提范围见 §5.2.1 前提范围注）。
5. **PCT 必要条件侧参照（次级定位，与第 1 条并存不互斥）**：上述定理族是 PCT「吸引子 ⟹ 真值」主张在构造性基座上的必要条件侧参照（定义见 §1.1 末）；PCT 抽象谓词 `clim` 现可经 `StateSpace` 实例（S := R，clim := lim，`RealSelfSS`）在**定义层**与本库接口谓词 `lim` 正式桥接——定义层双向桥定理 `pct_attractor_is_lim`/`pct_truth_is_global_min` 机器检查了 `is_attractor`/`is_truth` 在该实例下分别 ↔ lim 序列收敛/全局最小——两条桥定理的证明即谓词定义的展开（`intro h; exact h` 形态），属定义层/词表层等价，本身不含收敛或最优性推理（**定义层闭合 ≠ 内容定理成立**，层面对应见 §5.2）；内容层 corollary（把 §5.2.1/§5.2.2 闭合结论实例化为 `CoreClaim2` 字面实例）仍开放（§5.2、§7.2 开放工作 1）。
6. **接口纪律**：零全局公理、零 Admitted、零 Abort——该纪律指库内无 `Axiom`、无 `Admitted`，不等于无假设：全部分析前提为 Section `Variable` 与 Class 接口字段，随 Section 泛化为定理显式前件（§6.1 类别概述、§6.3；实证：`Print Assumptions dynamics_converges` 返回 `Closed under the global context`，批量审计口径见 §6.3）。

---

## 2 相关工作

- **O'Connor (2008) [1]**：在 Coq 中构造并形式化了精确的超越实数计算（含 exp 的可计算框架），属于构造性分析基础；未涉及梯度动力学收敛到驻点或迭代预算的形式化。更具体地，O'Connor 聚焦于可计算实数的算术与超越函数，本文聚焦于可计算实数上的迭代过程与复杂度界——后者属于构造性泛函分析/可计算分析的迭代侧，与前者互补。
- **Coquelicot [3] / MathComp-Analysis [4] / C-CoRN [2]**：经典或半构造性分析库，提供完备性、度量空间与不动点机制；与本文的关系正面比较于 §2.5。形式化实数分析的库间综述见[10]。
- **优化理论**：Bubeck (2015) [5] 系统分析凸优化算法的迭代复杂度（含梯度下降在收缩型假设下的预算形式）；本文 §4.8 的闭式预算与该类复杂度界在构造性接口下对应。形式化侧的相邻工作另见：一阶优化算法收敛率的 Lean 4 形式化[12]与优化的经验证归约[13]（均属经典逻辑路线，与本文的构造性接口不同层）。
- **证明挖掘（proof mining）**：Kohlenbach[7][8] 与 Kohlenbach–Leuştean[9] 研究如何从（常为非构造的）数学证明中**提取显式界与收敛率**，应用域涵盖度量不动点理论、遍历论与凸优化。本文的显式迭代预算（§4.8）在**目标上与该纲领同向**（都要「显式收敛率」），但取径不同：本文不把预算当作对既有经典证明做逻辑分析（proof interpretation）的产物，而是在构造性逻辑内**直接构造**——`N` 由 Real 层阿基米德性（`real_arch`）解出、经 Bernoulli 幂下界与倒数反变回接，且保证 Set 层可提取性。差别因此在「证明变换提取」与「构造性直证＋提取」之间，非对象之别；本文不主张显式可提取率这一**方向**的新颖性。
- **PCT（本文所属纲领）与相邻外部工作**：命题汇聚理论（Proposition Convergence Theory, PCT）是本文所属研究纲领的形式化主张（`CoreClaim2`，§5.1）：受约束的梯度流收敛到吸引子，吸引子对应命题的真值。据我们所知，PCT 尚无系统的已发表形式化文献；其动力学动机与自由能原理同构（Friston 2010 [6]）。本文为其一维情形提供机器检查的必要条件侧参照。

### 2.5 与 Banach 不动点形式化的关系

本工作的核心链（收缩假设 ⟹ 柯西 ∧ 极限存在 ∧ 极限处梯度为零）在数学上是 Banach 不动点定理 / Picard 迭代论证的特例；已有 Coq/Rocq 生态确实提供相关机制：**Coquelicot**（Boldo, Lelay, Melquiond, 2015 [3]）是 Coq 标准库经典实数公理的扩展，提供全函数式极限/导数/积分/级数 API 与对应定理；**MathComp-Analysis**（Affeldt et al., 2020 [4] 及其维护版本）基于 Mathematical Components，包结构含显式经典推理层（rocq-mathcomp-classical）与实数理论；**C-CoRN**（Geuvers, Cruz-Filipe, Niqui, Wiedijk et al. [2]，维护仓库 rocq-community/corn）构造了具体的实数结构并发展构造性实分析，其 ODE 目录含 Banach 不动点形式化（`BanachFixpoint.v`）。我们不直接实例化这些库，理由有三，并附带对 C-CoRN 显式速率问题的核验结论：

1. **基线不同（具体化）**：本库纪律为零经典公理、零全局公理——完备性、几何击穿、Lipschitz 收缩等一律作为显式 Section `Variable`（§6.1）。Coquelicot 建立在标准库经典实数之上，而标准库对经典实数的引入本身以公理方式给出（实数完备性即其一例）；MathComp-Analysis 的度量/完备性机器位于显式经典推理层（rocq-mathcomp-classical，含经典选择与排中）之上。直接复用上述库会把「完备性公理 / 经典推理层」作为全局依赖潜入证明，与本库「零全局公理、前提全部 Section 化」的纪律不可调和——这正是 §6.1.1 分别以抽象接口字段与具体实例定理记录完备性的原因。
2. **编码不同（例证）**：本库 `RealInterface` 的 `le` 以构造性 `Or (lt) (req)` 编码（`a ≤ b` 即 `a < b ∨ a ≈ b`），非严格序无法在同一命题中携带「严格分离」的排他信息；故许多序/度量的闭式性质在具体层只能以**逐 ε 余量族**陈述。例证：具体 `Real` 层的度量正性引理是 `real_metric_pos_eps`——对任意 a、b 与任意 ε > 0，`le zero (metric a b + ε)`——并以该余量形式装配为 setoid 接口的 `metric_pos` 字段（§3.4）；而在 Coquelicot 中同一性质是经典序上的闭式命题。因此把本文的 ε-N 链整体翻译进上述库的谓词语言需要逐条重建证明（逐 eps 版本化），而非单点实例化定理。库内对该编码约束现已给出系统化处理：`real_le_b` 谓词（逐 eps 全称化的非严格序，Set 层）与完成引理族把「逐 eps 余量」机制谓词化（库内验证文件 `UpRealLeB.v`）；Or 形精确完成的构造性不可证性有机器论证级同框对照（逆向桥若可证，则 min 的单 Or 见证需对不可判定分支作选择）——「逐 eps 版本化」由临时形态升级为具名谓词形态。
3. **结论形状不同（具体化）**：Banach 不动点定理的标准输出是不动点的存在性（迭代极限），而本文主链端点需要的是「极限处梯度为零」与「显式闭式预算 N(ε)」：前者要求额外的梯度界（Lipschitz/几何衰减）与对数单调性论证，后者（§4.8）不是 Banach 定理的直接输出。进一步，本文差距一/二的闭合（驻点 = 全局最大点、驻点唯一、非零初始梯度起点的任意两轨道极限相同，§5.2.1）给出了 Banach 不动点存在性之外的全局结构，这一结构正是 PCT 参照所需的。

**对 C-CoRN 显式速率的核验**：为澄清与已有构造性不动点工作的关系，我们核验了 `rocq-community/corn` 的 `ode/BanachFixpoint.v`：其确实**构造了显式柯西模**——`cauchy_x` 给出 `N(e) = ⌈d/(e·(1−q)²)⌉`（d := msd(x₀, f(x₀))，q 为收缩常数），并证明 `f fp = fp`（fp := lim 迭代序列）。

故本文的贡献不应表述为「生态内首个显式预算」，而应精确为三点：其一，以**闭式对数条件** `log(a·κ^N) ≤ log ε` 陈述预算（与经典凸优化复杂度界的形状 N ≈ log(ε/a)/log κ 同构，§4.8）；其二，预算 N 为随几何击穿前提 `r_arch_pow` 参数化的 Set 层构造、可提取为 OCaml（显式性语义限定见 §1.1 术语；实证 §6.3）；其三，预算结论与「极限处梯度为零 + 非零初始梯度起点间唯一吸引子」链（§4、§5.2）在**同一零公理 Section-Variable 纪律**内机器检查。这三点在 C-CoRN 的 BanachFixpoint 中均不直接可得（对照须注意：本库正文 N 的显式性以接口前提 `r_arch_pow` 的实现为载体，而 Real 层不依赖该前提的对应物已另行以模块形态机器检查，见 §7.2）。

任何复用都必须经过本文记录的接口桥接（setoid 桥、`real_cauchy_complete_metric_natle`、逐 eps 完备性桥等，§6.1.1）；「接口桥接的设计与代价」本身即本工作的工程贡献——这正是对「为什么不直接实例化已有 Banach 形式化」的回答。

---

## 3 构造性基座与问题设定

### 3.1 接口与前提的假设声明

库中 `RealInterface` / `RealInterfaceEnhanced` 两个 Class 封装构造性实数 `R` 的字段（`plus`、`mult`、`le`、`lt`、`abs`、`inv_pos`、`metric`、`lim`、`cauchy_complete` 等）。所有未在库内证明的标准分析性质均显式声明为 `Variable`，例如（完整类别清单见 §6.1，逐条详表见附录 B）：

- `strict_concavity`：熵梯度严格递减；
- `gradient_lipschitz`：梯度 Lipschitz 连续（常数 L）；
- `gradient_abs_decay`：梯度绝对值几何衰减（κ 幂衰减前提）；
- `r_arch_pow`：几何击穿；
- `metric_abs`、`metric_refl_zero`：度量由绝对值诱导、自反零等；
- `lt_plus_compat_lt_le` / `lt_plus_compat_le_lt`：序加法保序。

### 3.2 动力学定义

```coq
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
```

`dynamics x` 表示一步梯度上升/下降：`x_{n+1} = x_n + η·g(x_n)`；`entropy_gradient` 即梯度 `g`。以上变量位于 Section `ConvergenceCauchy` 内（命名空间与行号见附录 A）。

### 3.3 收敛目标

证明迭代序列 `iterate dynamics n E_A` 收敛到某 `E_star` 且 `entropy_gradient E_star == 0`；进一步给出显式迭代预算 N(ε)（§4.8）。

### 3.4 实数接口族与实例化

本库不以实数公理为起点，而把实数抽象为满足一组代数、序与完备性条件的接口。接口族按相等谓词分为两系：以命题相等 `Id` 表述的 `RealInterface` 与 `RealInterfaceEnhanced`，以及以 setoid 等价 `req` 表述的 setoid 系（Module `RealSetoidCore` / `RealSetoid` / `RealInterfaceEnhancedMod`）。两系字段一一对应，实质差别在于**超越函数字段是否携带正性前提**：柯西实数上的对数只能在正参数上构造（`cw_log`），因此 log 族带正性前提的 setoid 系可由具体 `Real` 满足，本文的实例化全部落在该系上。

**表 1**：实数接口族两系封装与实例化对照（§3.4）
| 接口（Module.Class） | 说明 | `Real` 实例 |
|---|---|---|
| `RealSetoidCore.RealInterfaceSetoidCore` | setoid 核心：req 自反/对称/传递，常数与运算，Proper 原理，环律，序律，正元求逆，metric/lim/完备性 | `Real_RealInterfaceSetoidCore` |
| `RealSetoid.RealInterfaceSetoid` | Core 字段 + exp 族与 log 族（带正性前提）+ 逐 eps metric 与完备性 | `Real_RealInterfaceSetoid` |
| `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid` | Setoid 字段 + 正性保序、min/r_max/pos_part、abs 族、exp_neg/log 族（带正性前提）、metric 与完备性 | `RealEnhancedReal` |

（上述 Class 与实例的库内行号见附录 A。）log 族的前提是两系的分水岭：`exp_neg` 与 `log_inv` 的互逆性只在正参数上要求（如 `RealInterfaceEnhancedSetoid` 的 `log : forall x, lt zero x -> R`），这与构造性对数的定义域一致，也是该系接口能够实例化的原因。三个实例的字段逐一取自 `Real` 层已证引理、不含公理；例如 `Real_RealInterfaceSetoid` 把 `exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log`、`metric_pos := real_metric_pos_eps`、`metric_triangle := real_metric_triangle_eps`、`lim := real_lim`、`cauchy_complete := real_cauchy_complete_metric_natle` 等填为实值。度量与完备性采用逐 eps 余量形式：构造性 `le` 以 `Or (lt) (req)` 编码，无法表达「非严格且不趋近」，故以「∀ eps > 0 的余量」陈述，这是该编码下可达的最强形式（例证见 §2.5 理由 2）；该论断在 Or 编码下成立不变——同一余量族现已另有谓词级封装：`real_le_b x y := ∀eps>0, x < y+eps`（库内验证文件 `UpRealLeB.v`），`real_metric_pos_B`/`real_metric_triangle_B` 为其直接实例（完成器 `real_le_closure_b_one` 单步＋源件直连，四项验证纪律均通过），并与 Or 形不可证的同框对照（`min a b ≤ a` 精确版不可证、`real_min_le_l_B` 可证）一并交付。接口完备性（`cauchy_complete`）即要求对每个 eps 给出 NatLe 索引的柯西点。

---

## 4 核心定理

（本节定理均位于 Section `ConvergenceCauchy`，命名空间为 `ConvergenceCauchy.<定理名>`；各定理的数学内容、状态与依赖前提列于附录 A；库内行号、版本哈希与逐条定位见补充材料 S1。）

### 4.1 几何衰减迭代

**引理 4.1**（`ConvergenceCauchy.grad_decay_iter`）：对任意 `n, k`，

```
|g(x_{n+k})| ≤ κ^k · |g(x_n)|.
```

**证明概要**：对 `k` 归纳，基例用 `mult_one`/`mult_comm` 换形；归纳步用 `gradient_abs_decay` 单步衰减与 `mult_assoc` 合并幂。

### 4.2 度量尾界

**引理 4.2**（`ConvergenceCauchy.iterate_metric_tail_bound`）：

```
metric (x_{n+m}) (x_n) ≤ |η| · |g(x_n)| · S,
```

其中 `S = 1/(1−κ)` 是几何级数和。

**引理 4.3**（`ConvergenceCauchy.geom_sum_bound`）：几何级数 `Σ_{i=0}^{m} κ^i` 以 `1/(1−κ)`（即 `inv_pos (minus one kappa) one_minus_kappa_pos`）为一致上界。

**引理 4.4**（`ConvergenceCauchy.iterate_metric_min_bound`）：

```
metric (x_m) (x_n) ≤ a · κ^{min m n},
```

其中 `a = |η| · |g(x_0)| · S`。

### 4.3 柯西性

**引理 4.5**（`ConvergenceCauchy.iterate_cauchy`）：对任意 `E_A` 与 `eps > 0`，若初始梯度非零 `0 < |g(E_A)|`，则存在 `N`，使得 `m,n ≥ N` 时 `metric (x_m) (x_n) < eps`。

**证明概要**：利用 `iterate_metric_min_bound` 将 `metric(x_m,x_n)` 控制为 `a·κ^{min m n}`；由 `r_arch_pow` 取 `N0` 使 `a·κ^{N0} < eps`，取 `N = N0` 即可。

### 4.4 极限存在性

**引理 4.6**（`ConvergenceCauchy.iterate_lim_exists`）：若 `0 < |g(E_A)|`，则存在 `E_star` 使得 `lim (fun n => x_n) E_star`。

**证明概要**：`iterate_cauchy` 给出柯西序列；完备性字段 `cauchy_complete` 将其提升为构造性极限（`ExistsT`/sigT 存在）。

### 4.5 梯度绝对值单调衰减

**定理 4.7**（`ConvergenceCauchy.iterate_grad_abs_mono`）：若 `0 < η`、`0 < g(x_n)`、`0 < g(x_{n+1})`，则

```
|g(x_{n+1})| ≤ |g(x_n)|.
```

**证明概要**：由 `x_{n+1} = x_n + η·g(x_n)`、`mult_positive` 与 `lt_plus_compat` 得 `x_n < x_{n+1}`；`strict_concavity` 给出 `g(x_{n+1}) < g(x_n)`；正值递减经 `gradient_abs_mono` 转化为绝对值递减。

**定位注**：该定理假设两处梯度正值 `0 < g(x_n)`、`0 < g(x_{n+1})`，属**符号已知**情形下的辅助定理——在无条件全符号设置下不可直接使用。无条件符号保持依赖步长约束 η < 1/L 与 Lipschitz 前提，作为 κ 定理化的一部分在 Real 层 Section `RealKappaSignReal` 给出；条件化全符号版本为 `real_grad_decay_full_sign_iter`（需显式三分假设 `real_sign_dec`）。主链（引理 4.5/4.6 与定理 4.9）不依赖本定理。

### 4.6 梯度夹逼为零

**引理 4.8**（`ConvergenceCauchy.grad_squeeze_zero`）：若 `lim x_n E_star` 且 `0 < |g(E_A)|`，则 `entropy_gradient E_star == 0`。

**证明概要**：对任意 `eps > 0`，将 `|g(E_star)|` 拆分为

```
|g(E_star) − g(x_n)| + |g(x_n)|.
```

第一项由 `gradient_lipschitz` 与 `lim_metric_approx` 控制为 eps/2；第二项由 `grad_decay_iter` 与 `r_arch_pow` 控制为 eps/2。利用 `le_all_eps_zero` 得到 `|g(E_star)| ≤ 0`，再由度量正性得到等式。

### 4.7 组装收敛定理

**定理 4.9**（`ConvergenceCauchy.dynamics_converges`）：对任意 `E_A`，若初始梯度非零（`0 < |g(E_A)|`），则存在 `E_star` 使得

```
lim x_n E_star  ∧  entropy_gradient E_star == 0.
```

**证明概要**：直接调用 `iterate_lim_exists` 与 `grad_squeeze_zero`。

**注（前提的显式罗列）**：本定理的前提由「初始梯度非零 `0 < |g(E_A)|`」与 §6.1 所列分析前提组成：严格凹性 `strict_concavity`、梯度 Lipschitz 连续 `gradient_lipschitz`、几何衰减 `gradient_abs_decay`（含收缩因子 κ ∈ (0,1)）、几何击穿 `r_arch_pow`、完备性 `cauchy_complete`、度量与序的接口性质（`metric_abs`、`metric_refl_zero`、`lt_plus_compat_*`、`eta_abs_pos`、`lim_metric_approx`、`le_all_eps_zero`），不含任何额外步长/`Hstep` 类条件。只要 `gradient_abs_decay` 仍是 `Variable`，该定理的论证就是「几何衰减假设 ⟹ 几何衰减迭代收敛」；其优化论内容（从强凹+Lipschitz+步长约束推出几何衰减）的定理化状态见 §6.3.1。**setoid 签名版本注**：本定理族的 setoid 签名版本已交付（对应定理名与签名说明见定理 4.10 意义段；两层口径不变——setoid 伴件为状态证据与对接路径，正文定理的陈述与证明不消费它们）。

### 4.8 显式迭代预算（资源受限的严格含义）

**定理 4.10**（`ConvergenceCauchy.iterate_cauchy_explicit_N`）：对任意 `E_A`，若 `0 < |g(E_A)|`，则对任意 `eps > 0` 存在 N，使得

```
log(a·κ^N) ≤ log eps   ∧   ∀m,n ≥ N: metric (x_m) (x_n) < eps,
```

其中 `a := |η| · |g(E_A)| · S`，`S := 1/(1−κ)`。

**纯数学陈述**（与上列 Coq 陈述同一内容的数学表述）：

> **定理（显式预算）**。设 κ ∈ (0,1)，S := 1/(1−κ)，a := |η| · |g(E_A)| · S。若初始梯度非零 `0 < |g(E_A)|`，则对任意 ε > 0 存在自然数 N（其显式构造在抽象接口层经几何击穿前提 `r_arch_pow` 的见证实现，并在具体 Real 层以独立模块形态给出——显式性语义限定见 §1.1 术语）使得：
> 1. `log(a · κ^N) ≤ log ε`；
> 2. 对任意 m, n ≥ N，`d(x_m, x_n) < ε`（d 为该接口的度量）。
>
> 此外，N 的构造仅依赖接口字段与 §6.1 所列前提，以 Set 层 sigT 见证给出（随定义可提取为 OCaml 的语义限定见 §1.1 术语）；在具体 Real 层，不依赖接口前提的对应物另有独立模块形态（§7.2 登记），其 N 由 `real_arch` 解出、经 Bernoulli 幂下界与倒数反变回接，并经代码提取产出可执行实现。

**证明概要**：`r_arch_pow_log_budget` 对任意正 a、eps 由 `r_arch_pow` 取 N0 使 `a·κ^{N0} < eps`，并借对数严格单调（`log_lt_mono_cc`）把几何击穿改写为闭式预算 `log(a·κ^{N0}) ≤ log eps`；随后用 `iterate_metric_min_bound` 把任意 m,n ≥ N0 的度量差控制为 `a·κ^{min m n} ≤ a·κ^{N0}`，收尾于 `r_pow_dec_iter` 与几何击穿。全证明零 `Admitted`、纯构造性（sigT/Set 层），N 的构造只依赖接口字段与 §6.1 前提（可提取性语义限定见 §1.1 术语；实证 §6.3）。

**具体 Real 层对应物（模块层，本节登记，不并入正文主张）**：抽象接口层之上，具体柯西实数（`Real := sigT (fun u : Qseq => cauchy u)`）上的对应物已由独立模块给出，四件均为纯构造性、零全局公理、零 `Admitted`，并经内核校验：

1. `r_arch_pow_real`：对任意 `0<κ<1`、`0<a`、`0<eps`，构造性地给出显式自然数见证 `N` 使 `a·κ^N < eps`——即几何击穿在具体 Real 层的显式形式，不再以接口前提为载体；构造路线为 `i := 1/κ`、`c := i−1`，由 Bernoulli 不等式 `i^N ≥ 1 + (N#1)·c` 给出幂下界，预算实数 `(a/eps)/c` 经 Real 层阿基米德性求解 `N`，再经倒数反变与幂-逆恒等式回接。
2. `budget_cond_sufficient`：闭式对数判据的充分性——若 `log a − log eps < N·(−log κ)`，则 `a·κ^N < eps`，即定理 4.10 条件 1 的对数形式在具体 Real 层成立（经对数多项式恒等与指数严格单调、`cw_log_exp_right` 反演）。
3. `geo_tail_budget`：尾界形态——若 `N ≤ min m n` 且 `a·κ^N < eps`，则 `a·κ^{min m n} < eps`，将定理 4.10 条件 2 的 `κ^{min}` 尾界归约为单点预算。
4. `budget_min_tail`：上述三者的组装——显式预算 `N` 的存在性与 `min` 尾界的一次性消解，即定理 4.10 在具体 Real 层的对应陈述。

该模块并已通过代码提取产出可执行实现（提取目标为上述四件），故其计算的显式性不止于 Set 层见证，而具备可运行的载体。**两层口径**：本文 §4 正文定理的陈述与证明不消费该模块；本段为模块层对应物的登记，抽象接口层陈述与具体 Real 层对应物并存，二者不互相替代（口径见 §6.3）。

**意义**：引理 4.5 只断言存在性柯西点；定理 4.10 进一步给出满足闭式条件 `log(a·κ^N) ≤ log ε`、随接口前提参数化的显式预算 N(ε, κ, L, η)（显式性语义限定见 §1.1 术语）——此即 §1.1 术语（显式迭代预算）所指的「资源受限」严格含义。与经典凸优化迭代复杂度分析（收缩/梯度下降预算 N ≈ log(ε/a)/log κ 量级，Bubeck 2015 [5]）相比，本定理给出同一形状预算的构造性、可机器检查版本：其每个参数（η、κ、|g(E_A)|、1/(1−κ)）都以 Section 变量或已证引理显式出现，且不依赖经典实数、三分律或紧致性（经典复杂度界通常隐含这些前提）；预算本身为随接口前提参数化可提取的构造（语义限定见 §1.1 术语），而经典纸笔界不可执行；在具体 Real 层，预算的显式性已由独立模块给出并具备可运行载体（本段上文登记），故本文的开放项清单不含「Real 层预算载体」一项。L 经 κ 定理化进入预算的途径见 §6.3.1。本定理族的 **setoid 签名版本已交付**，包括 `req_iterate_cauchy`、`req_iterate_cauchy_explicit_N`、`req_iterate_lim_exists`、`req_grad_squeeze_zero` 与 `req_dynamics_converges` 等对应定理——收敛链与显式预算已落到 setoid 签名上，其验证记录见补充材料 S1。**签名注**：附录 B 所列分析前提在 setoid 签名版本中逐位保留；`log_lt_mono_cc` 消费位前提化（setoid log 带 `lt zero` 前提）；`abs_nonneg_plain`/`metric_pos_plain`/`metric_triangle_plain` 采用节内自持的非严格余量形式——非严格序的逐 ε 余量形式无法由接口的 ε 形字段直接导出，因为非严格序不具备消去律；该边界条件的验证记录见补充材料 S1。两层口径不变：setoid 伴件为状态证据与对接路径，正文定理的陈述与证明不消费它们。

---

## 5 与 PCT 的连接

### 5.1 PCT 中的吸引子与真值

库内 Module `PropositionConvergenceCore` 中定义了 PCT 的核心谓词与主张（命名空间与行号见附录 A）：

```coq
Definition is_truth (L : S -> R) (s : S) : Set :=
  forall s' : S, le (L s) (L s').

Definition is_attractor (L : S -> R) (s : S) : Set :=
  forall s0 : S, clim (fun n => iterate (dynamics L) n s0) s.

Definition CoreClaim2 : Set :=
  forall L : S -> R, forall s : S,
    is_attractor L s -> is_truth L s.
```

`CoreClaim2` 是 PCT 核心哲学主张的形式化：吸引子是真值。这里的抽象收敛谓词 `clim` 是库内状态空间接口（Class `StateSpace`）的一个字段，类型为 `(nat -> S) -> S -> Set`，即「序列 ⟹ 点」的收敛关系；它只承诺唯一性（`clim_unique`）与相应完备性（`cauchy_complete_S`），不规定具体实现——逐点、度量或序收敛均可作为其合法实例（见 §7.2 开放工作 1）。PCT 的动机叙述见 §1.1（与自由能最小化纲领同构，Friston 2010 [6]）。库内另有高维抽象 Section `GradientDescentAndAttractor`（§6.2 第 1–2 条），其亦以同一批谓词名（`is_truth`/`is_attractor`）定义随机步进 `sgd_step` 的 omega-limit 版本收敛（语义为 `omega_limit (sgd_step L)`，与 PCT 的 `clim (iterate (dynamics L))` 版本不同）；本文所指均为 Module `PropositionConvergenceCore` 中的定义，不与前者混淆。

### 5.2 一维构造性参照：表述与层面对应

`dynamics_converges` 与 `CoreClaim2` 的对应设定如下（**概念层面对应**）：

- 状态空间 `S` 退化为实数 `R`；
- 损失 `L` 即熵 `entropy`（真值侧以 `L := −entropy` 表达）；
- 抽象收敛谓词 `clim` 由接口层收敛谓词 `lim` + `metric` 的 eps-N 语义承担；
- `is_truth`（全局最小点）退化为驻点处 `entropy_gradient == 0` 结合差距一闭合（驻点 = 全局最大点，损失 = 负熵时即全局最小点，§5.2.1）。

**层面对应声明**（本声明全文仅此一处，后文不再重复）：§4 的收敛证明使用 `RealInterface` 的 `lim` 与 `metric`；`PropositionConvergenceCore.is_attractor` 使用抽象谓词 `clim`。两者的**定义层桥接已在库内完成**：`StateSpace` 实例 `RealSelfSS`（抽象接口层实例——定义于 `Context {RI : RealInterface}`，S := @R RI、clim := @lim RI，S 是抽象接口实数，**非**具体柯西实数 `Real`；桥在抽象接口字段 `lim` 上进行）把抽象 `clim` 实例化为抽象接口层的收敛谓词 `lim`。

`lim` 在具体 Real 层的实值由 `real_lim` 承担并经 setoid 实例（`Real_RealInterfaceSetoid`、`RealEnhancedReal`，§3.4/附录 A）装配，属签名对接（§7.2 开放工作 4），非本桥内容。定义层双向桥定理 `pct_attractor_is_lim` 与 `pct_truth_is_global_min` 机器检查了 PCT 的 `is_attractor`/`is_truth` 在该实例下分别 ↔ lim 序列收敛 / 全局最小（零全局公理；形态见 §7.2 开放工作 1）。

两条桥定理的证明即谓词定义的双向展开（`intro h; exact h` 形态），属定义层/词表层等价、不含任何收敛或最优性推理（**定义层闭合 ≠ 内容定理成立**）。**内容层 corollary 仍开放**：§5.2.1/§5.2.2 的全部闭合结论**在 `lim` 表述的收敛语义层**成立；把它们包装为 `CoreClaim2` 在 (S := R, clim := lim) 下的**字面实例**（内容层 corollary）尚未完成——定义层桥提供谓词层面的双向等价，把 `attractor_converges_unique_truth` 等组装定理实例化进 `CoreClaim2` 签名是独立的剩余证明工作（见 §7.2 开放工作 1）。

### 5.2.1 与 `CoreClaim2` 的两处结构差距及其闭合

`dynamics_converges` 与 `CoreClaim2` 存在两个结构差距；两者的闭合均在库内完成（lim 语义层，见 §5.2 声明）：

**差距一：驻点 ≠ 全局最优。** `is_truth` 要求 `forall s' : S, le (L s) (L s')`，即全局最小点；而 `dynamics_converges` 只给出 `entropy_gradient E_star == 0`，即驻点。闭合：引入凹性切线不等式接口 `entropy_tangent`（`le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x)))`），证明

```
strict_concavity 下：entropy_gradient x == 0  ⟹  ∀y, entropy y ≤ entropy x
```

即驻点是熵的全局最大点（`gradient_zero_entropy_max`）；以损失 = 负熵（`L := −entropy`）即得 `is_truth` 形式（`gradient_zero_neg_entropy_truth`）。

**差距二：单轨收敛 ≠ 全局吸引。** `is_attractor` 要求任意初值收敛到同一个 `s`；而 `iterate_lim_exists` 对每个初值分别给出极限。闭合链（弱三分 + 严格递减；零经典）：

- `gradient_zero_unique`：两驻点必相等（`weak_trich` + `strict_concavity`，不使用排中律）；
- `unique_attractor`：非零初始梯度（`0 < |g(E_A)|` ∧ `0 < |g(E_A')|`）的任意两轨道，其极限相同；
- `attractor_converges_unique_truth`：PCT 组装——非零初始梯度的任意两轨道极限相等 ∧ 极限处梯度为零 ∧ 该点为 −entropy 的全局最小点（`And` 为 Set 层合取）。

**前提范围注（零梯度起点）**：本节收敛定理（`iterate_lim_exists`、`dynamics_converges`、`unique_attractor`、`attractor_converges_unique_truth`）的前提均为初始梯度非零 `0 < |g(E_A)|`（前两者单起点；后两者对两条轨道各一）——故上列「任意两轨道极限相同」按代码前提应读作**非零初始梯度的任意两轨道**。零梯度起点（`g(s0) == 0`，即驻点）不在现链覆盖内：由 `dynamics_gradient_step` 与环律（`mult_zero`/`plus_zero`）有 `dynamics s0 == s0`、轨道恒驻 s0；但把该常驻序列写成 `lim` 收敛证书需常序列收敛引理（抽象层缺位，无 `lim_const` 类引理），与「由 `gradient_zero_unique` 驻点唯一推出 s0 == 唯一驻点」的组装同属 `is_attractor` 的 ∀s0 字面覆盖（内容层 corollary）所需补足的小引理族（见 §7.2 开放工作 1 注）；在补足前，本文把差距二闭合结论限定表述为「非零初始梯度的任意两轨道收敛至同一极限（唯一吸引子）」。

**闭合后的准确表述**：在一维、严格凹设定、`lim` 语义层、初始梯度非零前提的起点范围内，`dynamics_converges` 及其差距闭合构成 PCT「吸引子 ⟹ 真值」主张的**必要条件侧参照的实例语义**：非零初始梯度的任意轨道收敛、极限唯一、极限 = 驻点 = −entropy 的 `is_truth` 点（零梯度起点见上注）。抽象 `CoreClaim2`（Definition）保持为 PCT 纲领的共享主张；其高维/随机推广仍开放（§5.2.2），`clim` 版本的定义层桥接已闭合（`RealSelfSS` + `pct_attractor_is_lim`/`pct_truth_is_global_min`，机器检查），内容层 corollary（`CoreClaim2` 字面实例）仍开放（见 §7.2 开放工作 1）。

### 5.2.2 PCT 差距一览（开放问题与已闭合结果）

`dynamics_converges` → `CoreClaim2` 的差距全景（当前快照；差距一/二已闭合，高维/随机推广仍开放）：

| 差距 | 内容 | 状态 | 闭合材料 / 说明 |
|---|---|---|---|
| 差距一 | 驻点 ≠ 全局最优（`is_truth` 要求全局最小点） | **已闭合** | `entropy_tangent`（凹性切线不等式接口）+ `gradient_zero_entropy_max` + `gradient_zero_neg_entropy_truth`（L := −entropy） |
| 差距二 | 单轨收敛 ≠ 全局吸引（`is_attractor` 要求任意初值收敛到同一极限） | **已闭合**（前提范围：非零初始梯度起点，见 §5.2.1 前提范围注） | 闭合链：`gradient_zero_unique`（弱三分 `weak_trich` + 严格递减；零经典）、`unique_attractor`（非零初始梯度的任意两轨道极限相同）、`attractor_converges_unique_truth`（PCT 组装） |
| 高维推广 | 状态空间由一维 `R` 放宽到多维 | **开放** | 需多维严格凹 + 弱三分的高维形态（构造性多变量驻点唯一性） |
| 随机推广 | 确定性动力学 → 随机/噪声动力学（SGD/采样） | **开放** | 需构造性随机近似收敛机器（Robbins–Monro 类）；该方向已有机器检查工作（随机逼近形式化[11]），本文未并入 |
| 抽象 `CoreClaim2` | PCT 纲领共享的核心主张（Definition） | **保持定义** | 一维严格凹、`lim` 语义层实例已闭合；`clim` 定义层已桥接：`StateSpace` 实例（S := R，clim := lim，`RealSelfSS`）+ 定义层双向桥定理 `pct_attractor_is_lim`/`pct_truth_is_global_min`（机器检查）；内容层 corollary（`CoreClaim2` 字面实例）仍开放。抽象主张留作形式化纲领 |

**setoid 签名版本对照**：本闭合链的 setoid 签名版本已交付——`req_unique_attractor`/`req_attractor_converges_unique_truth`（`UpReqCauchy.v`）等对应定理，PCT 定义层桥接定理亦已在 setoid 签名版本中给出（`UpReqPCT.v`：`reqRealSelfSS` 实例＋`req_pct_attractor_is_lim`/`req_pct_truth_is_global_min`）；验证状态见补充材料 S1。定义层桥后 setoid 侧「桥即定义展开」（exact h 级），**内容层 corollary（CoreClaim2 字面实例）仍为开放项**——开放定性不变。

**定位**：两条差距已闭合（在非零初始梯度起点与 `lim` 语义层范围内，见 §5.2.1 前提范围注；闭合材料的库内定位见附录 A 行号表），两条推广方向为开放工作；`clim`/`lim` 桥的定义层已闭合（`RealSelfSS` + 两条定义层双向桥定理，机器检查），内容层 corollary（PCT `CoreClaim2` 字面实例）仍开放（§5.2、§7.2 开放工作 1）。该表如实反映现状，不夸大不省略。

**库内相关构件**：库内另有 Section `HierarchicalPropositions` 定义命题层级与聚合函数（`softmax_aggregation`、`weighted_sum_aggregation`），以及 Module `ThermodynamicsInstance` 把 PCT 的 CoreClaim 实例化到热力学系统（含 `core_claim3_holds`、`core_claim5_holds` 等证明）。把一维收敛定理经聚合函数的 Lipschitz/凹性条件推广到层级损失景观，以及闭合热力学版 `CoreClaim2`（熵增），均属开放工作（§7.2），本文不将其计入已闭合差距。

---

## 6 形式化边界与假设声明

### 6.1 分析前提的类别与接口纪律

本文收敛定理的全部分析前提均以 Section `Variable` 显式声明于 `ConvergenceCauchy` 内，随 `End Section` 自动泛化为定理前件。按数学角色可分为六类：

1. **凹性**：`strict_concavity`（熵梯度严格递减；差距一闭合与驻点唯一性亦依赖它）；
2. **Lipschitz 连续**：`gradient_lipschitz`（梯度以常数 L 的 Lipschitz 连续）；
3. **几何衰减**：`gradient_abs_decay`（梯度绝对值以因子 κ ∈ (0,1) 幂衰减；见 §6.3.1 的定理化状态）；
4. **几何击穿**：`r_arch_pow`——对任意正 a、eps 存在 N 使 `a·κ^N < eps`。其数学意义是**几何击穿**：任意正量乘以几何衰减因子 κ^N 终将跨过任意小的阈值。它替代经典构造中依赖阿基米德性/紧致性完成的「选 N」步骤，使柯西收尾与显式预算（§4.8）成为纯构造性命题；
5. **度量性质**：`metric_abs`（度量由绝对值诱导）、`metric_refl_zero`（自反零）、逐 eps 度量语义相关性质、`eta_abs_pos`（步长绝对值正）、序加法保序（`lt_plus_compat_lt_le` / `lt_plus_compat_le_lt`）、`lim_metric_approx`（lim 的 eps-N 语义）与 `le_all_eps_zero`（夹逼收尾）；
6. **完备性**：`cauchy_complete`——柯西序列完备性字段（其轨道归属——接口假设还是已证定理——见 §6.1.1）。

此外，μ-强凹族（`strong_concavity` / `mu` / `mu_pos`）与凹性切线不等式 `entropy_tangent` 分属 κ 定理化（§6.3.1）与差距一闭合（§5.2.1）的前提，不进入主收敛链（§4）。**弱三分 `weak_trich` 的地位**：它是 `ConvergenceCauchy` 内的接口假设（`Variable`，形式 ¬(x<y) ∧ ¬(y<x) ⟹ x==y，非 LPO）；其具体 `Real` 层对应物 `real_weak_trich` 已是库内证明的引理（见附录 B 该行注），故该接口假设在具体实例上由已证定理满足。逐条详表（含类别、行号、归属）见附录 B。

**setoid 签名版本注**：上述分析前提在 setoid 签名版本（`UpReqCauchy.v`）中逐位保留；`log_lt_mono_cc` 消费位前提化（setoid log 带 `lt zero` 前提）；`abs_nonneg_plain`/`metric_pos_plain`/`metric_triangle_plain` 采用非严格余量形式——非严格序的逐 ε 余量形式无法由接口的 ε 形字段直接导出，因为非严格序不具备消去律；该边界条件的验证记录见补充材料 S1。

这些假设对应于经典分析中通常默认或由实数公理推出的性质；在纯构造性抽象 `R` 层显式声明、随 Section 泛化为定理前件，是接口纪律的体现（§6.3）。

### 6.1.1 `cauchy_complete` 的轨道归属

`iterate_lim_exists` 依赖 `cauchy_complete`——它是实数完备性的构造性版本吗？`cauchy_complete` 究竟是定理还是公理？**结论：二者皆有，分属不同轨道。**

| 轨道 | 名称 | 状态 |
|---|---|---|
| **抽象接口轨** | `cauchy_complete`（`RealInterface` Class 字段，经增强接口继承） | **接口假设**。`cauchy_complete` 的完整构造（对角线极限）是构造性分析的大工程，故在抽象层声明为显式 Variable（与 `proj_orthogonal_compat` 同先例，属结构性缺失记录） |
| **具体 Real 轨** | `real_cauchy_complete` | **已证定理，零 Variable 依赖**；`Print Assumptions real_cauchy_complete` 返回 `Closed under the global context`（批量审计口径见 §6.3） |

**含义**：`iterate_lim_exists` 工作在抽象轨，依赖接口字段 `cauchy_complete`。因此 `Print Assumptions dynamics_converges` 会把 `cauchy_complete` 列为前件（因它在抽象层作为字段出现）。但具体构造的柯西实数已具备零假设完备性定理 `real_cauchy_complete`，且完备性字段的实例装配已完成：库尾的 setoid 并行接口层把 metric 形式柯西条件桥接到 `real_cauchy_complete` 的双向 `real_lt` 形式——`real_cauchy_complete_metric` 及其 NatLe 索引版 `real_cauchy_complete_metric_natle`，底层为 `Id_eq`/`eq_Id` 单构造子桥与 `NatLe_to_le`/`le_to_NatLe` 索引桥；Instance `Real_RealInterfaceSetoidCore` 把 `cauchy_complete` 字段（:= `real_cauchy_complete_metric_natle`）实际装配到具体 `Real`。即：**完备性字段的实例化在 setoid Core 接口内已完成，抽象层前件在具体实例上由 `real_cauchy_complete` 满足**；exp/log 超越函数字段的实值填充见 §3.4（`Real_RealInterfaceSetoid` 与 `RealEnhancedReal`，字段全实值）。各条目的行号见附录 A。

### 6.2 不覆盖的内容

1. **高维状态空间**：`dynamics_converges` 限定于一维 `R`。
2. **随机噪声**：Section `GradientDescentAndAttractor` 定义了 `noise`/`sgd_step`，但未给出随机收敛定理。
3. **非凸景观**：严格凹性假设排除了多吸引子情形。
4. **吸引子 ⟹ 真值的完整证明**：抽象 `CoreClaim2` 保持为 Definition，未给出通用证明。
5. **位精度/内存/复杂度类资源**：本工作不讨论有限精度算术与误差传播，不涉及位精度、内存或计算复杂性类。「资源受限」按 §1.1 术语（显式迭代预算）理解：`iterate_cauchy` 给出存在性柯西点；`iterate_cauchy_explicit_N` 给出闭式预算（§4.8）。两级分工为「存在性」与「显式闭式条件」。

### 6.3 假设的封装状态与 Set 层可提取性

「零全局公理」的宣称依赖一个前提：大量未封装自由变量若未随 Section 泛化为定理前件，其逻辑地位确与公理无异。本库的封装机制保证该前提成立：

1. `RealInterfaceEnhanced` 是 Class，本节定理所在 Section 以 `Context {RI : RealInterfaceEnhanced}` 引入，不是顶层自由 `Variable`；
2. `End Section` 后 Coq 自动对 `RI` 及 §6.1 全部假设泛化，使其成为定理的显式（隐式）前件；
3. 实证：Rocq 9.0/9.1 `Print Assumptions dynamics_converges` 返回 `Closed under the global context`——批量核验的口径与局限（核验快照与未整体重跑的如实披露）见附录 A 边界声明。

**实例化方式**：抽象层定理以 `forall {RI : RealInterfaceEnhanced}` 陈述；具体柯西实数 `Real` 的实例化由该接口的 setoid 对应物承担（`Real_RealInterfaceSetoid`、`RealEnhancedReal`，全部字段实值化，§3.4/§6.1.1）。`real_cauchy_complete`（Real 层零依赖定理）已通过 setoid Core 实例回填接口完备性字段（`cauchy_complete := real_cauchy_complete_metric_natle`）；`strict_concavity`/`gradient_lipschitz`/`gradient_abs_decay` 等抽象层假设与实例层的逐 eps 对接记录于 §6.1.1。本实例化路径属两层解除（Two-level Discharging）口径之**字段级实例化**层（该口径分字段级实例化与定理级签名迁移两层；本处属前者，已完成），其边界限于字段级承载，不得读作定理级迁移已完成。

**Set 层细节与可提取性**：本库定义全部置于 Set 层——合取使用自定义 `And (A B : Set) : Set := A * B`（非 Coq 标准 Prop 层 `and`），析取 `Or`、存在 `ExistsT := sigT`；sigT/`And` 中的有理数序谓词一律使用 Set 值判定谓词（`QltT`/`QleT`，如 `Qlt_to_QltT`、`Qle_to_QleT'` 出现在提取依赖链中），`And` 不实例化到 Prop。**提取验证**：独立验证文件「提取验证探针」以 `Extraction Language OCaml` 把 `real_mult`、`cauchy_real_exp`、`cauchy_real_sin`、`cauchy_real_cos` 等核心构造及 cos/sin 恒等引理提取为 OCaml（产物 `提取验证探针.ml`/`提取验证探针.mli`）——该提取实证完成于早期基线，属历史事实，当前基线同型复验随 artifact 交付（包内路径见附录 A 许可与 artifact 打包声明）；即本段所述 Set 层编码在已覆盖的 Real 层核心构造上可提取为不含 Prop 残留的 OCaml 代码，本定理族的提取验证状态见补充材料 S1（全库审计口径见附录 A 边界声明）。

### 6.3.1 `gradient_abs_decay` 的定理化状态与贡献定位

核心观察：`gradient_abs_decay` 本身就是几何衰减的断言，作为 `Variable` 引入时，主链定理在逻辑上是该假设的直接展开——「几何衰减假设 ⟹ 几何衰减迭代收敛」。本工作不据此主张新的优化论收敛定理；准确的重述是：

```
收缩假设（κ-几何衰减 + Lipschitz + 几何击穿）⟹ 迭代序列柯西 ∧ 极限存在 ∧ 极限处梯度为零，
且该链附显式闭式预算 N(ε)（定理 4.10）。
```

其中「从 `strict_concavity` + `gradient_lipschitz` + 步长约束推出 `gradient_abs_decay`」——真正的优化论内容——的定理化状态（κ 定理化）如下：

**表 2**：核心定理族状态总览（§4；开放项见 §7.2）
| 目标 | 前提 | 状态 | 阻塞项 |
|---|---|---|---|
| 正分支衰减 | `g(x) > 0` 前提，μ-强凹（κ := 1−ημ） | **已证**（`gradient_step_contraction`、`gradient_step_abs_contraction`、`gradient_iterate_abs_decay`、`grad_decay_positive_iter`；Real 层平移 Section `RealKappa`） | 无 |
| 符号已知双分支 | 符号已知（Lipschitz + 步长 η < 1/L ⟹ 符号保持） | **已证**（Section `RealKappaSignReal`） | 无 |
| 条件化全符号 | 显式三分假设 `real_sign_dec`（Set 层 Or，可判定实例可用） | **已证**（`real_grad_decay_full_sign_iter`） | 需显式三分假设 |
| 无条件全符号 | 无符号前提 | **不可证** | 需整体三分律（LPO），构造性实数不可实例化 |

（各行对应定理的行号见附录 A。）关于最后一行：弱三分 `real_weak_trich`（Real 层已证）不足以支撑三分支重组的整体引理——整体引理不可逐点实例化、坏点传播无前提可矛盾、弱线性不可判定——故该行保持为构造性实数固有边界的如实记录，不列为可完成项；可判定梯度实例（有理值）方向可继续推进三分假设的实例化（§7.2 开放工作 6）。

本工作的实际贡献由此定位为：（a）把上述推理链的每一步前提显式化并机器检查（形式化纪律）；（b）给出构造性的显式迭代预算（可提取性语义限定见 §1.1 术语；§4.8，贡献 1）与 setoid/逐 eps 接口实例化工程（§3.4/§6.1.1）；（c）为 PCT 提供一维、严格凹、lim 语义层的必要条件侧参照与差距闭合（§5.2）。它**不是**一个新的优化论收敛定理。

### 6.4 与 O'Connor [1] 的关系

O'Connor [1] 给出构造性实数上可计算函数（含 exp）的收敛与计算框架。本工作的贡献不在分析学本身，而在把类似的构造性收敛纪律应用于梯度动力学，并给出显式预算与 PCT 差距闭合。两者的分工是互补的：O'Connor 的基线解决「可计算实数上的算术与超越函数」，本文处理「可计算实数上的迭代过程与显式复杂度界」，后者通常属于构造性泛函分析/可计算分析的迭代侧。

---

## 7 结论与开放工作

### 7.1 结论与贡献定位

本文给出 ConstructiveWorld 库中一维梯度动力学收敛链的完整机器检查，并把该链的定位收敛为两条并存的陈述：

1. **显式迭代预算线（主）**：「资源受限」按 §1.1 术语（显式迭代预算）理解，主定理为 `iterate_cauchy_explicit_N`（§4.8）；未涉及位精度/内存/复杂度类资源（§6.2 第 5 条）。
2. **PCT 必要条件侧参照线（次级，与主线不互斥）**：一维严格凹设定下，收敛链及其差距闭合（§5.2.1/§5.2.2）是 PCT「吸引子 ⟹ 真值」主张的必要条件侧参照——承担动力学侧构件的机器检查，不声称充分性；`clim`↔`lim` 形式化桥已在**定义层**闭合（`RealSelfSS` + `pct_attractor_is_lim`/`pct_truth_is_global_min`，机器检查），内容层 corollary（`CoreClaim2` 字面实例）仍开放（§5.2、§7.2 开放工作 1）。

本工作的主要价值不是给出新的优化论收敛定理，而是：（a）显式化并机器检查每一步前提（接口纪律，§6.1/§6.3）；（b）给出构造性可提取的显式预算与接口实例化工程（§3.4/§4.8）；（c）为 PCT 提供可核验的必要条件侧参照与差距一览（§5.2.2）。文中 §4 的定理编号与附录 A 的行号映射可作为库内其他形式化工作的交叉引用锚点。

### 7.2 开放工作

1. **`clim` ↔ `lim` 内容层 corollary（`CoreClaim2` 字面实例）**：`clim` 是 PCT 抽象所基于的状态空间接口（Class `StateSpace`）的收敛谓词字段，类型为 `(nat -> S) -> S -> Set`（「序列 u 收敛于点 l」的二值关系），该接口同时要求唯一性 `clim_unique` 与相应完备性 `cauchy_complete_S`，但不规定 `clim` 的具体语义。

   **定义层桥接已在库内完成**：`StateSpace` 实例 `RealSelfSS`（抽象接口层实例：S := @R RI、clim := @lim RI，非具体柯西实数 `Real`；Real 层 `lim` 实值 `real_lim` 经 setoid 实例承接，属开放工作 4 的签名对接）取 S := R、clim := lim（全部字段由 `RealInterface` 直供，clim_unique/cauchy_complete_S 一并实值化），把抽象 `clim` 实例化为 `RealInterface` 的 eps-N 收敛 `lim`。

   **setoid 签名版本对照（定性收窄注）**：上句「Real 层 `lim` 实值 `real_lim` 经 setoid 实例承接，属开放工作 4 的签名对接」中的 setoid 签名对接面已由定义层桥接的 setoid 版本交付（`UpReqPCT.v` 的 `reqRealSelfSS_inst`，clim:=lim 实例化的 setoid 镜像）——「开放工作 4」的剩余定性收窄为「Real 层 clim 实值承载与定理级签名迁移」（`real_lim` 实值经 setoid 实例的定理级对接仍开放，定性收窄部分维持）。

   定义层双向桥定理 `pct_attractor_is_lim`/`pct_truth_is_global_min` 机器检查了 PCT 的 `is_attractor`/`is_truth` 在该实例下分别 ↔ lim 序列收敛 / 全局最小（双向蕴含经定义展开直接闭合，零全局公理）。

   **剩余开放项 = 内容层 corollary**：把 §5.2.1/§5.2.2 的闭合结论（`ConvergenceCauchy.attractor_converges_unique_truth` 组装，lim 语义层）包装为 `CoreClaim2` 在 (S := R, clim := lim) 下的**字面实例**——定义层桥已提供谓词层面的双向等价，corollary 需在其上把收敛链的接口数据逐项装配进 `CoreClaim2` 签名并完成实例化证明。

   **setoid 签名版本对照**：定义层桥接定理的 setoid 版本（`UpReqPCT.v`：`reqRealSelfSS` 实例＋`req_pct_attractor_is_lim`/`req_pct_truth_is_global_min`）已交付且「桥即定义展开」（exact h 级，定义层）；**内容层 corollary（CoreClaim2 字面实例）仍为开放项**——本段开放定性不变。

   该装配并非纯机械，需先补足两处结构性缺口：其一，PCT `dynamics` 以损失 L 为参数而收敛链动力学为固定熵梯度上升，`CoreClaim2` 的 ∀L 字面形式在「动力学忽略 L」的包装下不成立，实例须取单损失 L0 := −entropy 的形态；其二，`is_attractor` 的 ∀s0 证书须覆盖零梯度驻点起点（常驻轨道 + 驻点唯一组装），需先补常序列收敛小引理族（§5.2.1 前提范围注）——故该 corollary 尚未完成。

   若未来把 `clim` 实例化为抽象序收敛（非度量）等其他语义，仍需额外的构造性完备性/单调收敛论证，复杂度显著更高——该分支同样未做。
2. **高维推广**：把一维 `R` 替换为 `StateSpace`/`HilbertSpace`，证明 `sgd_step` 的收敛性并给出多维预算（§5.2.2 开放项）；与此相关的层级聚合损失景观（§5.2.2「库内相关构件」）与热力学实例的 `CoreClaim2` 闭合亦属此推广方向。
3. **随机收敛**：在 `noise` 假设下建立随机梯度下降的构造性收敛界（§5.2.2 开放项）。该方向已有机器检查工作——随机逼近定理的形式化[11]（Coq，度量空间下的 Robbins–Monro 型收敛）；本文的开放式表述限于**未把该结果并入本文的构造性接口与预算框架**，而非该方向无形式化先例。
4. **抽象层签名对接**：把本文定理签名迁移到该接口的 setoid 对应物，使 `real_cauchy_complete` 这类 Real 层成果在单一签名下回填抽象层（§6.1.1 已记录完备性字段的 Core 级完成；exp/log 字段与全文对接为续作）——本项即两层解除（Two-level Discharging）口径之**定理级签名迁移**层（尚未完成，续作定性不变；库内首批机器检查试点为模块 `UpSigMigrate` 的 `req_free_energy_kl_decomp` 与 `req_attention_is_gibbs_temp` 两件（模块内行号见补充材料 S1），试点不等于全量迁移）。
5. **RLHF/DPO 对齐侧连接**：对齐目标侧的迭代收敛已有实现（`policy_iter_kl_geom_iter`、`policy_iter_kl_geom_step`、`dpo_loss_iter_mono`，Section `Alignment`；`policy_iter_kl_geom_iter` 即真几何率版本：KL(π*‖π_t) ≤ (1−η)^t · KL(π*‖π_0)，κ := 1−η，无附加常数项——行号见附录 A）；把对齐目标梯度纳入同一收敛框架的完整连接仍开放。
6. **κ 定理化的未完成分支（全符号无条件版）**：全符号无条件版依赖 LPO（构造性不可实例化）——如实记录，不列为可完成项（§6.3.1 状态表）；可判定梯度实例（有理值）方向可继续推进三分假设的实例化。
7. **资源预算的 Real 层载体与治理层扩展（边界注记）**：

   **(a) 已闭合（本文开放项清单不含该项）**：本文主定理（定理 4.10）在具体 Real 层的对应物已由独立模块 `UpBudgetReal` 机器检查——几何击穿显式定理 `r_arch_pow_real`（显式自然数见证 `N` 使 `a·κ^N < eps`，不依赖接口前提）、闭式对数判据 `budget_cond_sufficient`、尾界 `geo_tail_budget` 与组装件 `budget_min_tail`（min 尾界与显式预算的一次性消解）；四件均为纯构造性、零全局公理、零 `Admitted`，并经内核校验，且已通过代码提取产出可执行实现。其构造路线与逐件陈述见 §4.8「具体 Real 层对应物」段。**因此「Real 层预算载体」不是开放问题**；两层口径不变——正文（抽象接口层）定理的陈述与证明不消费该模块，本项为模块层对应物的登记。

   **(b) 开放（治理层方向，与本文定理互不消费）**：库内另有与「资源受限」主线呼应的治理构件——以承诺面执行资源宪法的 `UpConstitution`（`valid_claim_yields_breakthrough`；非空性 `constitution_nonvacuous`）与停时原语 `UpStopTime`（`minimal_stoptime`；阈值占优 `st_thresh_dominance`；「无守卫则无停时」边界 `unguarded_vs_guarded`）。这些属追加治理层的独立构造（随 artifact 交付，模块内行号见补充材料 S1），与本文 §4 的抽象接口层收敛定理互不消费——既不改变本文定理的陈述与前提，也不由本文定理推出；把本文的「显式迭代预算」与治理层的「资源宪法/停时」统一为单一资源语义框架属后续工作。

---

## 参考文献

1. O'Connor, R. (2008). Certified Exact Transcendental Real Number Computation in Coq. *TPHOLs 2008*, LNCS 5170. https://dblp.org/rec/conf/tphol/OConnor08.html （预印本：https://arxiv.org/abs/0805.2438）
2. C-CoRN: Constructive Coq Repository at Nijmegen（Geuvers, H., Cruz-Filipe, L., Niqui, M., Wiedijk, F., et al.）. http://c-corn.cs.ru.nl （社区维护仓库：https://github.com/rocq-community/corn ；ODE 目录含 `BanachFixpoint.v`，核验见 §2.5）
3. Boldo, S., Lelay, C., Melquiond, G. (2015). Coquelicot: A User-Friendly Library of Real Analysis for Coq. *Mathematics in Computer Science*. https://inria.hal.science/hal-00860648 （库：https://github.com/coq/coquelicot）
4. Affeldt, R., Cohen, C., Kerjean, M., Mahboubi, A., Rouhling, D., Sakaguchi, K. (2020). Competing Inheritance Paths in Dependent Type Theory: A Case Study in Functional Analysis. *ITP 2020*. https://github.com/math-comp/analysis （库；包结构含显式经典推理层 rocq-mathcomp-classical）
5. Bubeck, S. (2015). Convex Optimization: Algorithms and Complexity. *Foundations and Trends in Machine Learning* 8(3–4):231–357. https://mlanthology.org/ftml/2015/bubeck2015ftml-convex/ doi:10.1561/2200000050
6. Friston, K. (2010). The free-energy principle: a unified brain theory? *Nature Reviews Neuroscience* 11(2):127–138. https://pubmed.ncbi.nlm.nih.gov/20068583/ doi:10.1038/nrn2787
7. Kohlenbach, U. (2008). *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*. Springer Monographs in Mathematics. Springer. https://doi.org/10.1007/978-3-540-77533-1 （证明挖掘：从非构造性证明提取显式界与收敛率）
8. Kohlenbach, U. (1998). Proof Theory and Computational Analysis. *Electronic Notes in Theoretical Computer Science* 13:124–157. https://doi.org/10.1016/S1571-0661(05)80219-1
9. Kohlenbach, U., & Leuştean, L. (2011). Proof Mining in Metric Fixed Point Theory and Ergodic Theory. arXiv:0903.1529. https://arxiv.org/abs/0903.1529 （含凸优化中显式收敛率的提取）
10. Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437
11. Vajjha, K., Trager, B. M., Shinnar, A., & Pestun, V. (2022). Formalization of a Stochastic Approximation Theorem. *ITP 2022*, LIPIcs 237, 31:1–31:18. arXiv:2202.05959. https://arxiv.org/abs/2202.05959 （§5.2.2 随机收敛方向的已有形式化）
12. Li, C., Wang, Z., He, W., Wu, Y., Xu, S., & Wen, Z. (2025). Formalization of Convergence Rates of Four First-order Algorithms for Convex Optimization. *Journal of Automated Reasoning* 69(4):28. https://doi.org/10.1007/s10817-025-09741-w
13. Bentkamp, A., Mir, R. F., & Avigad, J. (2023). Verified Reductions for Optimization. *TACAS 2023*, LNCS 13994, 74–92. https://doi.org/10.1007/978-3-031-30820-8_8

---

## 附录 A：核心定理索引（内容摘要、状态与正文定位）

命名空间：主链定理位于 Section `ConvergenceCauchy`，记作 `ConvergenceCauchy.<名>`；PCT 抽象定义位于 Module `PropositionConvergenceCore`。本附录与附录 B 为索引表：行号按冻结基线主文件逐条实测，行号基准、版本哈希与逐条实测记录见补充材料 S1；全部锚点位于基底区（< L95604），该区在基线推进中为纯追加、未发生平移。行号与定理基准=冻结基线；验证与认证状态=当前真态快照（见「基线与验证状态（双轨）」）。

**表 3**：κ 定理化与全符号版状态表（§6.3.1；行号见补充材料 S1）
| 名称 | 命名空间 / 行号 | 状态 | 内容摘要 | 备注 |
|---|---|---|---|---|
| `grad_decay_iter` | `ConvergenceCauchy` L14117 | 已证（Lemma） | 梯度绝对值 κ^k 衰减 | 本文 §4.1 |
| `geom_sum_bound` | `ConvergenceCauchy` L14290 | 已证（Lemma） | 几何级数一致上界 1/(1−κ) | 本文 §4.2 |
| `iterate_metric_tail_bound` | `ConvergenceCauchy` L14376 | 已证（Lemma） | 迭代度量尾界（S := 1/(1−κ)） | 本文 §4.2 |
| `iterate_metric_min_bound` | `ConvergenceCauchy` L14499 | 已证（Lemma） | 迭代度量 κ^{min} 界 | 本文 §4.2 |
| `iterate_cauchy` | `ConvergenceCauchy` L14528 | 已证（Lemma） | 迭代序列柯西性（存在性 N） | 本文 §4.3 |
| `iterate_cauchy_explicit_N` | `ConvergenceCauchy` L14610 | 已证（Theorem） | **显式闭式预算**：log(a·κ^N) ≤ log ε 且 m,n ≥ N 时 metric < ε | 本文 §4.8（定理 4.10，主贡献）；setoid 签名版本 `req_iterate_cauchy_explicit_N` 已交付（`UpReqCauchy.v`） |
| `iterate_lim_exists` | `ConvergenceCauchy` L14653 | 已证（Lemma） | 极限存在性（经 `cauchy_complete`） | 本文 §4.4 |
| `iterate_grad_abs_mono` | `ConvergenceCauchy` L14674 | 已证（Theorem） | 梯度绝对值单调衰减 | 本文 §4.5（符号已知辅助） |
| `grad_squeeze_zero` | `ConvergenceCauchy` L14763 | 已证（Lemma） | 极限处梯度为零 | 本文 §4.6 |
| `dynamics_converges` | `ConvergenceCauchy` L14845 | 已证（Theorem） | 收敛 + 梯度为零组装 | 本文 §4.7 |
| `gradient_zero_entropy_max` | `ConvergenceCauchy` L15120 | 已证（Theorem） | 驻点 = 熵的全局最大点 | 差距一闭合 |
| `gradient_zero_neg_entropy_truth` | `ConvergenceCauchy` L15142 | 已证（Theorem） | −entropy 的全局最小点（is_truth 形式） | 差距一闭合（L := −entropy） |
| `gradient_zero_unique` | `ConvergenceCauchy` L15169 | 已证（Lemma） | 两驻点必相等（弱三分 + 严格凹；零经典） | 差距二闭合 |
| `unique_attractor` | `ConvergenceCauchy` L15197 | 已证（Theorem） | 非零初始梯度两轨道极限相同 | 差距二闭合（前提范围见 §5.2.1 注） |
| `attractor_converges_unique_truth` | `ConvergenceCauchy` L15215 | 已证（Theorem） | PCT 组装（lim 语义层） | 差距二闭合 |
| `is_truth` / `is_attractor` | `PropositionConvergenceCore` L1527 / L1530 | Definition | PCT 抽象定义（clim 表述） | §5.1 |
| `CoreClaim2` | `PropositionConvergenceCore` L1596 | Definition（保持纲领共享主张） | PCT 核心主张「吸引子 ⟹ 真值」 | lim 语义层的一维严格凹实例已闭合（初始梯度非零起点范围，§5.2.1 注/§5.2.2）；clim 定义层已桥接（`RealSelfSS` + `pct_attractor_is_lim`/`pct_truth_is_global_min`，机器检查）；内容层 corollary 仍开放（§5.2、§7.2 开放工作 1） |
| `RealSelfSS` / `pct_attractor_is_lim` / `pct_truth_is_global_min` | L1224（Definition，StateSpace 实例：S := R、clim := lim）/ L1742 / L1757（Section `PCTRealBridge` L1713 起） | Definition / Theorem | clim↔lim 定义层双向桥 | 机器检查，零全局公理；内容层 corollary（`CoreClaim2` 字面实例）仍开放（§5.2、§7.2 开放工作 1） |
| `real_cauchy_complete` | 顶层 L6134 | 已证（无 Variable 依赖） | 具体 Real 层完备性（`Print Assumptions` 闭合） | 构造性实数完备性基础 |
| `cauchy_complete` | `RealInterface` L202 | 接口字段（假设） | 抽象接口完备性字段 | 抽象层完备性假设；setoid Core 实例已回填（见下行） |
| `real_cauchy_complete_metric` / `real_cauchy_complete_metric_natle` | L33194 / L33401 | 已证（Lemma） | metric 形式完备性桥 → Real 层完备性 | NatLe 索引版装配为 `cauchy_complete` 字段 |
| `Id_eq` / `eq_Id` / `NatLe_to_le` / `le_to_NatLe` | L33375 / L33380 / L33385 / L33393 | 已证（Lemma） | 单构造子桥与索引桥 | §6.1.1 |
| `Real_RealInterfaceSetoidCore` | L33433 | Instance | setoid Core 实例 | `cauchy_complete := real_cauchy_complete_metric_natle` |
| `Real_RealInterfaceSetoid` | L39407 | Instance | setoid 完整实例 | exp/log 族实值化（§3.4） |
| `RealEnhancedReal` | L41115 | Instance | 增强接口实例 | §3.4 |
| `cw_log` | L38016 | Definition | 构造性对数（正参数） | `log_inv` 的实值 |
| `real_weak_trich` | L38268 | 已证（Lemma） | Real 层弱三分 | `weak_trich` 接口假设的实例（见下行） |
| `weak_trich` | `ConvergenceCauchy` L15166 | Variable（接口假设） | 弱三分：¬(x<y) ∧ ¬(y<x) ⟹ x==y（非 LPO） | 驻点唯一/差距二闭合（§5.2.1）；Real 层实例见上行 |
| `kappa` / `kappa_pos` / `kappa_lt_one` | `ConvergenceCauchy` L14055–L14057 | Variable | 收缩因子 κ ∈ (0,1) | 收缩因子假设（§4） |
| `strong_concavity` / `mu` / `mu_pos` | `ConvergenceCauchy` L14872 / L14870 / L14871 | Variable | μ-强凹（凹性模量化） | κ 定理化前提（§6.3.1，非主链前提） |
| `gradient_step_contraction` 等 κ 定理化族 | `ConvergenceCauchy` L14896–L15064（Section `RealKappa` 平移 L51490 起） | 已证 | 正分支衰减（κ := 1−ημ） | §6.3.1 状态表 |
| Section `RealKappaSignReal` | L51855 起 | Section | 符号已知双分支 κ 定理化 | §6.3.1 |
| `real_sign_dec` / `real_grad_decay_full_sign_iter` | Section `RealKappaSignReal` L52958 / L53032 | 已证 | 条件化全符号版（需显式三分假设） | §6.3.1 |
| `policy_iter_kl_geom_step` / `policy_iter_kl_geom_iter` / `dpo_loss_iter_mono` | Section `Alignment` L23146 / L23181 / L23256 | 已证 | 对齐侧迭代收敛 | §7.2 开放工作 5；`policy_iter_kl_geom_iter` 为真几何率 (1−η)^t（κ := 1−η，无附加常数项） |

**当前库真态（快照）**：ConstructiveWorld 为 Rocq/Coq 9.0/9.1 纯构造性库，零全局公理、零 Admitted；HEAD=39d81aa（成果接入与注册收尾波）；编译清单 246 模块，Live_X 356 个 .v；CI 连续 success；认证面 CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证；其后另有成果接入与注册收尾波推进中，以随论文 artifact 的变更记录为准。论文行号与定理基准为冻结基线；验证与认证状态以本快照为准。

**边界声明（审计口径，全文以本段为准）**：本文行号与审计数字的基准是一个冻结基线主文件；其行数与内容哈希、闭合标记计数（行首与缩进的 `Qed.`/`Defined.` 分列口径，不可相加为「声明总数」）以及禁词扫描结果（行首 `Admitted`、`Axiom`、`Abort.` 均 0，无经典逻辑公理引用，`Classical` 仅出现于纪律注释）的完整数字与逐项实测记录见补充材料 S1。

全库验证由三项独立验证构成：(1) **行首闭合统计与禁词扫描**（审计脚本随 artifact 提交）——行首口径对 `Qed.` 出现在注释或行中的形态天然免疫，非行首残留由后两项兜底；(2) **整根编译**——主文件单发全量编译、退出码 0，任何未闭合证明、`Admitted` 或语法残留都会使编译失败；(3) **提取验证**——核心构造提取为 OCaml，由独立验证文件断言零 Prop 残留。

批量 `Print Assumptions` 审计显示：81 条主定理与主定义均返回 `Closed under the global context`，未发现依赖未声明公理的条目。该审计的核验时点为早期基线的快照记录，其后至本表冻结基线未整体重跑；其间新增内容以行首禁词零命中与编译退出码 0 维持同一零公理纪律，冻结时点批量复验随 artifact 交付。§1.2/§6.1.1/§6.3 所引 `dynamics_converges`/`real_cauchy_complete` 的实证按本段口径披露。补充材料 S1 另注：81 条 PA 最终基线重跑仍为库侧挂账；本文维持 81 条 PA 的分层陈述口径，不作全量 PA 已完成声明。

**当前真态下的三种分发形态**（快照口径）：本节描述当前真态快照；论文行号、定理名与附录索引仍以冻结基线为基准。验证与认证状态以当前真态快照为准，二者按双轨声明处理，不相互覆盖。(a) **模块化树（权威分发形态）**——基座加模块化扩展层；截至当前真态快照（HEAD=39d81aa，编译清单 246 模块，Live_X 356 个 .v，CI 连续 success），认证面 CI #72（39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证；论文行号与定理基准仍为冻结基线，二者按双轨声明处理。(b) **扩展层拼装发布** `CW220_Extensions.v`——为冻结基线产物，已通过全量编译、禁词计数、提取与内核校验四项验证纪律；其与当前 HEAD=39d81aa、246 模块认证面的对应关系见补充材料 S1（行数、闭合标记计数与内容哈希见补充材料 S1）。



(c) **单文件全量合并** `CW_ConstructiveWorld_220.v`——截至当前真态快照（HEAD=39d81aa）仍为源码合并形态，全量编译阻塞在案（顶层同名声明碰撞等，见库内阻塞图谱文档）；该形态不表述为「编译通过」，亦不纳入当前模块化树 246/246 认证面。

**范围外披露（当前真态，不改本文定理）**：B 路 exp 加法交换性 UpReqBanachExpAddEq 已闭合并云认证；ExpOppOne/InstPre/InstEMult 与 BanachCauchyD 已认证；实例非空性 Real 载体实例 `UpReqBanachInstReal`（39/39 装配位消解，实例非空性 0%→100%）及同波 Banach 新件（分离定理 `UpReqBanachSepThm`、范数对偶 `UpReqBanachNormOpp`、B4 两段式 `UpReqB4TwoStage`、去假设 `BanachNoHyp`/`BanachNoHypNorm`）已随 b657aff 注册波并入认证面；S 系源侧 `Psatz` 移除（163 件闭包面）同波并入；第八波 Strong（qnorm Id 形强化轨）已注册。同两波另含 C 路 Padé 正尾线闭合至 n=2 旗舰 `cpf_exp_pos_final_n2` 等新认证（属论文3 披露面，本文不展开）。其后另有成果接入与注册收尾波推进中（246 注册面），以随论文 artifact 的变更记录为准。上述构件位于本文 §4 主链与 §5 PCT 参照的消费面之外，不改变本文定理陈述、前提与开放/闭合定性。

接口实例 3 处（`Real_RealInterfaceSetoidCore`、`Real_RealInterfaceSetoid`、`RealEnhancedReal`，均属 setoid 系接口、全部字段实值化；实测 L33433 / L39407 / L41115）。

本文收敛定理依赖附录 B 所列 `Variable` 假设；`cauchy_complete`（`RealInterface` Class 字段，实测 L202）在抽象层仍是假设，其 setoid 对应字段已由实例填为实值（`Real_RealInterfaceSetoidCore` 起，实测 L33433），接入须经签名对接（§6.1.1）。提取验证：核心构造（`real_mult`、`cauchy_real_exp`、`cauchy_real_sin`、`cauchy_real_cos` 等）与 cos/sin 恒等引理提取为 OCaml 的实证完成于早期基线（独立验证文件「提取验证探针」，产物 `提取验证探针.ml`/`提取验证探针.mli`）——属历史事实，当前基线同型复验随 artifact 交付。

**许可与 artifact 打包声明**：本文引用的库源码（冻结基线主文件与模块化扩展层）、审计与验证脚本（含行首闭合统计脚本与独立验证文件「提取验证探针」）及验证日志随投稿 artifact 一并归档，附 LICENSE 与 README；开发期路径为仓库内部基准，投稿版以包内相对路径与登记 DOI 为准。全部定理引用均可在 artifact 中逐名定位；本文不引入 artifact 之外的数学内容。

---

## 附录 B：分析前提详表（§6.1 类别概述的逐条展开）

本文收敛定理所在 Section `ConvergenceCauchy` 内的全部分析前提（类别按 §6.1 六类 + 辅助类；行号与定理基准=冻结基线，验证与认证状态=当前真态快照）：

| 假设 | 行号 | 数学含义 | 类别 | 归属 |
|---|---|---|---|---|
| `strict_concavity` | L14041 | 熵梯度严格递减 | 凹性 | 主收敛链（§4）；差距一/二闭合（§5.2.1） |
| `gradient_lipschitz` | L14044 | 梯度 Lipschitz 连续（常数 L，L_pos L14043） | Lipschitz | 主收敛链（§4） |
| `kappa` / `kappa_pos` / `kappa_lt_one` | L14055–L14057 | 收缩因子 κ ∈ (0,1) | 几何衰减 | 主收敛链（§4） |
| `gradient_abs_decay` | L14058 | 梯度绝对值几何衰减 | 几何衰减 | 主收敛链（§4）；定理化状态见 §6.3.1 |
| `r_arch_pow` | L14081 | 几何击穿（几何击穿） | 阿基米德 | 主收敛链（§4）；显式预算（§4.8） |
| `metric_abs` | L14053 | 度量由绝对值诱导 | 度量 | 主收敛链（§4） |
| `metric_refl_zero` | L14079 | 度量自反零（`metric a a == zero`） | 度量 | 主收敛链（§4） |
| `lt_plus_compat_lt_le` | L14063 | 严格 + 非严格序加法保序 | 度量/序 | 主收敛链（§4） |
| `lt_plus_compat_le_lt` | L14064 | 非严格 + 严格序加法保序 | 度量/序 | 主收敛链（§4） |
| `eta_abs_pos` | L14432 | 步长绝对值正（`lt zero (abs eta)`） | 度量/序 | 主收敛链（§4） |
| `lim_metric_approx` | L14722 | lim 的 eps-N 语义（`grad_squeeze_zero` 依赖）；setoid 签名版本 `req_grad_squeeze_zero` 已交付（`UpReqCauchy.v`） | 度量 | 主收敛链（§4） |
| `le_all_eps_zero` | L14728 | 任意小非负 ⟹ ≤ 0（夹逼收尾）；setoid 签名版本 `req_grad_squeeze_zero` 已交付（`UpReqCauchy.v`） | 度量/序 | 主收敛链（§4） |
| `cauchy_complete` | L202（`RealInterface` Class 字段，经 `RI_base` 继承） | 柯西序列完备性 | 完备性 | 极限存在（§4.4）；轨道归属见 §6.1.1 |
| `log_lt_mono_cc` | L14556 | 对数严格单调（正参数上） | 辅助（对数） | 显式预算（§4.8） |
| `weak_trich` | L15166 | 弱三分：¬(x<y) ∧ ¬(y<x) ⟹ x==y（非 LPO） | 辅助（序） | 驻点唯一/差距二闭合（§5.2.1）；Real 层实例 `real_weak_trich` 已证（附录 A） |
| `entropy_tangent` | L15114 | 凹函数切线不等式接口 | 辅助（凹性） | 差距一闭合（§5.2.1） |
| `strong_concavity` / `mu` / `mu_pos` | L14872 / L14870 / L14871 | μ-强凹（凹性模量化） | 辅助（凹性，κ 定理化） | κ 定理化（§6.3.1，非主链前提） |

行号按冻结基线主文件逐条实测，本表全部行号落在基底区（< L95604）；行号基准、版本哈希与逐条实测记录见补充材料 S1。各条目正文定位与实例见附录 A。

---

