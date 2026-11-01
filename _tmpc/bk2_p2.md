# 自由能原理、注意力-Gibbs 桥与截断采样（Top-k/Min-P）：一个构造性机器检查视角

**英文标题**：The Free Energy Principle, the Attention-Gibbs Bridge, and Truncated Sampling (Top-k/Min-P): A Constructive Machine-Checked Perspective


**作者**：王宝军、夏挽岚（通讯作者，xiawanlan33@163.com）、祖光照、周志农、高雪峰

**Authors**: Baojun Wang, Wanlan Xia, Guangzhao Zu, Zhinong Zhou, Xuefeng Gao. *Corresponding author: Wanlan Xia (xiawanlan33@163.com).*

---

## 摘要（Abstract）

本文的主要分析贡献是构造性柯西实数基座上的逐 eps 定量技术，以及 Top-k/Min-P 截断采样与 KV 驱逐的定量理论；FEP 数学核（含最大熵对偶的温度参数化闭合）与 attention-Gibbs 桥作为应用案例。本文所有定理在 Rocq/Coq 9.0/9.1 中机器检查，满足四项验证纪律：全量编译退出码 0、Print Assumptions 返回 Closed under the global context、提取无 Obj.magic、coqchk 内核校验通过。当前库状态为 HEAD=39d81aa，编译清单 246 模块，Live_X 356 个 .v，CI 连续 success，认证面 246/246，各波 coqchk 全绿（CI #72（head 39d81aa，246 注册面）COQCHK_ALL_PASS=最新云认证）；详细审计见补充材料 S3。首次主张严格限定为上述四族结果在纯构造性逻辑下的统一机器检查。适用限制：主要定理在抽象实数接口上陈述，其 setoid 对应物已在具体柯西实数上端到端实例化；抽象陈述与实例陈述之间的 statement-level 机器对齐仍为人工开放项。

---

**Abstract (English)**

The main analytical contributions of this paper are per-eps quantitative techniques over a constructive Cauchy-real base, together with a quantitative theory of Top-k/Min-P truncated sampling and KV-cache eviction. The mathematical core of the Free Energy Principle (including the temperature-parameterized closure of the maximum-entropy duality) and the attention-Gibbs bridge are presented as application cases. All theorems are machine-checked in Rocq/Coq 9.0/9.1 and satisfy four verification disciplines: full compilation with exit code 0, Print Assumptions returning Closed under the global context, extraction free of Obj.magic, and a passing coqchk kernel check. The current repository state is HEAD=39d81aa, with 246 modules in the compilation manifest, 356 Live_X .v files, continuous CI success, and a certified surface of 246/246 (latest cloud certification: CI #72, head 39d81aa, COQCHK_ALL_PASS); further results-integration and registration-closing waves are in progress, with the change log accompanying the paper artifact as the authoritative record. Detailed audit logs are provided in supplementary material S3. The "first" claim is strictly scoped to the unified machine-checked treatment of the above four families under pure constructive logic. Limitations: the main theorems are stated over an abstract real-number interface, and their setoid counterparts are instantiated end-to-end on concrete Cauchy reals; machine-checked statement-level alignment between abstract statements and their instantiations remains an open item requiring manual statement-level comparison.

---

## 1 引言

### 1.1 动机

自由能原理（Free Energy Principle, FEP）是统计力学、贝叶斯推断、认知科学与机器学习的统一纲领。其核心主张是：自组织系统通过最小化变分自由能来同时实现模型拟合与模型复杂度控制。然而，FEP 的数学基础长期存在争议，部分批评指向其推导中隐含的经典逻辑假设、未显式声明的分布正性条件，以及“自由能”与“证据下界”之间等价性的精确范围。

与此同时，Transformer 中的 softmax 注意力被广泛认为是 Boltzmann/Gibbs 分布的一个实例：attention 权重正比于 `exp(query·key / √d)`。这一对应为语言模型提供了一个物理/统计力学解释，纸笔文献通常将其当作类比；本工作在抽象 logits 层把它提升为**机器检查的精确等式定理**——softmax = Boltzmann（定理 5.1，premise-free 主定理；带前提形态为推论 5.1a/5.2），并进一步闭合缩放-温度对偶 `scale_temp_duality`（L28524）：任意 c>0 下「以 1/c 缩放 logits 的 softmax == 温度 c 的 softmax」。`1/√d` 缩放经见证式 `sqrt_witness`（L28552，d := r·r）在平方维数下实例化；对偶引理 `scale_sqrt_witness_dual`（L28565）对任意满足见证条件 `r·r == d` 的 (d, r) 成立。**√d 覆盖现状**：抽象层——任意平方维数 d = k² 的见证与对偶实例已机器检查（`sqrt_witness_nat_sq` L96596：`sqrt_witness (nat_to_R (k·k)) (nat_to_R k)`；`scale_dual_sq_k` L96603 / `scale_dual_nat_sq_k` L96622 给出 1/k 缩放 == 温度 k 的对偶实例，k ≥ 1——d=4 的 `sq_witness_4` L28555 成为其特例，此前的『注释级构造模式』现已成为库内任意 k 的通用引理）；Real 层——任意 d ≥ 0 的构造性平方根已证明（`real_sqrt_exists` L96475，`sigT` 见证 r ≥ 0 且 r·r == d，非平方 d 一并覆盖，见 §5.4(c)）。仍开放：query-key 点积到抽象 logits 的具体绑定中「范数界 → 显式收缩率」的末端一步（§5.4 适用限制、§9.2 边界 3、§10.2 第 2 项；「一致范数界 → 双界 logits」一段已机器检查，见 §5.5 定理 5.7/5.8）。

ConstructiveWorld 项目的目标是在同一逻辑立场（纯构造性、零全局公理）下，把自由能、Boltzmann 分布、注意力、信息论与对齐算法统一为单一机器检查库，从而：
1. 精确划定 FEP 数学核的成立范围；
2. 将 attention-Gibbs 桥从类比提升为定理；
3. 为 KV 缓存逐出、top-k/Min-P 截断等工程启发式提供可审计的**恒等式与单调性**刻画（注：不含可计算误差估计，见 §6.2）。

上述目标的列举顺序不反映分量顺序：按 §1.2 的分层判据，本文的分析分量最重处是目标 3 所依托的柯西实数基座逐 eps 定量技术、Real 层对应定理族与截断采样定量理论；目标 1、2（FEP 数学核与 attention-Gibbs 桥）在证明结构上多为该基座的实例化装配，定位为基座之上的应用案例（§9.2.2 分量自评）。

### 1.2 贡献
**术语约定**：构造性强度等级分三档——Or 精确形（结论为 x<y ∨ x=y 的精确形态）、Bishop 形（结论为 ∀ε>0, x<y+ε 的非严格序形态）、逐 eps 余量形（保留 Or 语法并显式携带余量参数；三档的代表定理目录见 §9.3）。CLEAN 指 `Print Assumptions` 返回 `Closed under the global context`。四项验证纪律为：全量编译退出码 0；Print Assumptions 返回 Closed under the global context；提取验证无 Obj.magic；coqchk 内核校验。文中 T-π2/T-π3 等为库内任务编号，非数学对象名。Axiom 为全局公理；接口 `Variable` 为定理前件；Class 字段为接口假设——本文定理均以显式前件陈述，三者的区别见 §3.5。符号约定：能量函数记 E、温度参数在库内语句中记 D（D>0，对应统计力学温度 T）、精度参数记 β := 1/D；`D_pos`/`T_pos` 为相应正性前提。

**FEP 读者导读**：FEP 读者可先读 §4.1–§4.4，其中给出变分自由能分解、Gibbs 不等式、Boltzmann 最小化与最大熵对偶的数学陈述、假设与证明思路；Coq 接口细节见 §3.5 与补充材料。§5 为注意力应用案例，可按需阅读。

**ML 读者导读**：ML 读者可先读 §5.2、§7.5、§8.4–§8.5，其中给出 softmax = Boltzmann、Top-k TV 恒等、Min-P 核归一化与截断质量界的算法定义、假设与结论；完整验证状态见表 A.1（附录 A）。使用有限状态空间与逐 eps 余量，不涉及浮点实现。

本文的贡献按**分量分层**组织。分层判据是证明的分析难度与机器检查所增加的贡献。本文叙述上最突出的主张——FEP 数学核与「attention 层 = 变分自由能唯一最小点」——在证明结构上多为三个基座定理（`free_energy_kl_decomp`/`min_free_energy_is_boltzmann`/`free_energy_min_unique`）的纯实例化装配（§9.2.2 分量自评），其价值在于构造性机器检查的前提显式化与跨域连通；分析分量主要落在柯西实数基座的逐 eps 定量技术与 Real 层对应定理族上。

**第一层：柯西实数基座上的逐 eps 定量技术与 Real 层对应定理族（分量最重）**
1. **Real 层对应定理族**：Min-P 截断质量的熵刻画（`dropped ≤ 1 − e^{−S}`，模块件；词表界 `dropped ≤ 1 − 1/|S|` 降为其推论，定理 8.9）；温度两极——T→0 硬注意力极限与 T→∞ 温度窗口 `temp_window_T_infty`（量词翻转闭合）；缩放-温度对偶与任意温度同构的 Real 层复刻（`real_scale_temp_duality`/`real_attention_is_gibbs_temp`）；双点 TV 收缩的 Real 层 δ 接口复刻（定理 5.10，已进入模块化树并通过四项验证；其 setoid/req 迁移未完成）；Q/K 范数界到双界 logits 的显式转化（`qk_logits_bounded`，根有界前提形态）；有限和 C-S 核（`real_cauchy_schwarz` 系，含反向不等式的形式化反驳）。
2. **柯西实数基座与构造性 LPO 规避机制**：exp/log 超越函数构造（`cauchy_real_exp`/`cw_log` 族）与逐 eps 序技术（§3.1/§9.2.3）；弱三分 `real_weak_trich` 替代排中律、逐 eps 余量替代“非严格且不趋近”、误差累积“恰为 eps 而非 |S|·eps”的归一化论证——这些是构造性分析中真正的技术点，也是全文定理可纯构造性陈述的基础。

**第二层：截断采样与迭代动力学的定量理论**
3. **Top-k 截断的总变差精确恒等（定理 7.6）**：`TV(boltzmann, topk_renorm) == tail_mass / Z_thermo`，条件化前提下的精确恒等（19 引理四段组装）；配合 Min-P 截断质量与词表大小的挂钩（定理 8.9，`≤ 1 − 1/|S|`），把截断采样从“规格机器检查”提升为截断误差的定量刻画。
4. **注意力核迭代的 TV 收缩与收敛（Doeblin minorization）**：把 softmax 注意力层的迭代视为 Markov 链，单步 TV 收缩 `attention_tv_contraction`（L29195，收缩因子 1−δ）、几何迭代收缩 `attention_tv_iter_contraction`（L29287，`TV(iterate n μ0, p_b) ≤ (1−δ)ⁿ·TV(μ0, p_b)`）与迭代收敛 `attention_iterate_converges`（L29330，∀ eps>0 存在 N，n ≥ N ⟹ TV_n < eps，sigT 见证）全部机器检查（Qed），前提为 Doeblin minorization（δ ∈ (0,1)，核 ≥ δ·稳态质量；收敛的几何击穿经显式前件 `r_arch_pow_attn` L29247），显式几何率 (1−δ)ⁿ（§5.5）。注意力的稳态解读因此在本文中分层为：稳态方程验证（定理 5.3）与 TV 意义下的迭代收敛均已机器检查；在此基础上，库内又把「由注意力权重构造 `transition`」与「Doeblin minorization 前提在注意力核上的实例化」两个开放端闭合——以行 softmax 核 `bs_kernel`（L96247，行归一化 `bs_kernel_row` L96263）构造 transition，经 `bs_minorization`（L96286）在双界 logits（−Δ ≤ z ≤ Δ、T > 0）上给出显式 Doeblin 下界 δ*·U ≤ K(s,·)（δ* := lo·lo = e^{−2Δ/T}，零余量损耗），收缩率显式化为 (1 − e^{−2Δ/T})ⁿ（`bounded_softmax_tv_contraction` L96331 / `bounded_softmax_tv_iter` L96344）；配套的双点收缩 `u_tv_contraction`（L95931）/`u_tv_iter`（L96019）在四个维度上推广基线 Doeblin 节（免平稳性、免详细平衡、免 `transition_nonneg`、免 μ 非负；参考分布只需任意归一化）（§5.5）。仍未形式化：状态空间（clim）收敛与 §5.5 双点族的 Real 层完整复刻（§5 章首、§9.2 边界 3、§10.2）；「Q/K 范数界 → 双界 logits → 显式 Δ」一段已在模块化树内闭合（§5.5 定理 5.7/5.8），「显式 Δ → 显式率 δ\* := e^{−2Δ/T}」的末端一步：其实例引理已在树内闭合（模块化树（补充材料 S2） Part 2，2026-09-11 核实），尚余模块级组合证明待完成（§10.2 第 2 项）。
5. **KV 逐出的结构刻画**：Set 层主体为偏差的三角不等式记账（定理 6.1）与分区单调性（定理 6.4/6.5）；另有破缺恒为零（定理 6.2）与有限 n 漂移界（定理 6.3，§6.2.2）；与温度、能量界、Lipschitz 常数的定量联系由 Real 层定理 6.1b/6.1c 承载（§6.2.1）。
6. **截断采样形式化套件（数学深度较低，价值在前提显式化）**：top-k 主化最优性（定理 7.1–7.3）、尾部质量记账（定理 7.4/7.5）；Min-P 截断的可判定性、非空性、核归一化（`minp_markov_kernel_normalized`）与相对完整 softmax 核的单调放大（`minp_markov_kernel_keep_ge_full`）。这些结果多为排序前缀/重归一化定义的直接后承（§9.2.2 自评），其价值在于把解码策略的全部前提显式化并机器检查。

**第三层：FEP 数学核与 attention-Gibbs 桥（基座之上的应用案例）**
7. **温度参数化最大熵对偶的闭合（定理 4.6a–4.6e）**：在温度参数化 Boltzmann 族上，约束熵最大化解的存在性、唯一性与温度-能量严格单调性全部闭合；核心为对称 KL 恒等 `(β1−β2)(E2−E1) == KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})`（log Z 项恰好抵消）。
8. **FEP 数学核与 Attention-Gibbs 桥**：变分自由能分解、Gibbs 不等式与等号条件、Boltzmann 最小化唯一性、ELBO 下界与紧性、softmax 注意力与 Boltzmann 分布的精确对应（premise-free 主定理 5.1 `fep_align`；单位温度与任意温度的带前提形态为推论 5.1a/5.2）；以及「attention 层 = 变分自由能唯一最小点」（§5.4(b)/§9.1）——本层定位为基座之上的应用案例：把 FEP、注意力与对齐目标连通到同一分解定理上（§9.1），并机器检查其全部前提。

**贯穿基础设施**
9. **统一基座**：`free_energy_kl_decomp`（L16259）与 `rlhf_free_energy_kl`（L20290）为同一自由能-KL 分解定理的两次实例化——FEP、attention 与 RLHF/DPO 的 KL 项由此形式同构（§9.1；关联对象见 Ouyang et al., 2022[26] 与 Rafailov et al., 2023[14]）。
10. **构造性纪律与接口实例化**：零全局公理、零 Admitted；分析层自建，依赖 Coq stdlib 的有理数层及本文公开 artifact 中列出的库内模块；抽象接口、setoid 实例与 Real 层复刻三路径的逐字段/逐定理对照见附录 B。

**分层的外部先例重叠度**：上述分层的「分量」判据是库内相对的（证明分析难度与机器检查所增加的贡献）；叠加外部先例维度后，各层重叠度如下：

| 分层 | 外部先例重叠度 | 说明 |
|---|---|---|
| 第一层：Cauchy 基座逐 eps 技术与 Real 层对应定理族 | **高**：Cauchy 实数、exp/log 构造与逐 eps 序技术与 CoRN/O'Connor 构造性分析先例[18][19]大量重合 | 本层的外部增量主要在 ML 侧量化陈述的构造强度与精确恒等（定理 7.6、Min-P 熵刻画、δ* 显式化；§9.2.2） |
| 第二层：截断采样与迭代动力学的定量理论 | **部分**：截断 = 去平滑的理论刻画（Hewitt et al., 2022[20]）、软截断的信息论框架（Meister et al., 2023[21]）；收缩系数经典（Doeblin[23]、Dobrushin[24]、Levin–Peres–Wilmer[25]） | 本文增量为机器检查的精确恒等（定理 7.6）与显式常数（δ* = e^{−2Δ/T}、零余量；§5.5） |
| 第三层：FEP 数学核与 attention-Gibbs 桥 | **低（主题层）**：可检索范围内无同范围形式化先例（§2.4 对照表与检索协议）；纸笔侧注意力-能量对应[6][7]与 RLHF/DPO[14][26]为关联对象 | 价值在前提显式化的机器检查与跨域连通（§9.2.2 自评） |

当前库状态（HEAD=39d81aa）：ConstructiveWorld 于 Rocq/Coq 9.0/9.1 纯构造性编译，零全局公理、零 Admitted；编译清单 246 模块，Live_X 356 个 .v；CI 连续 success，认证面 246/246，各波 coqchk 全绿（9.0 基线段以 run 94486425397 @24431dc 全树 COQCHK_ALL_PASS 收尾；当前 9.1 认证段 CI #72（head 39d81aa，run 35057242417，246 注册面）COQCHK_ALL_PASS，57,154 常量经内核复检）；81 条 PA 最终基线重跑尚未整体执行，本文分层口径不变。

### 1.3 论文结构

§2 介绍背景与相关工作；§3 描述构造性基座；§4 展开 FEP 数学核；§5 建立 attention-Gibbs 桥；§6 给出 KV 逐出界；§7 证明 top-k 主化最优性；§8 形式化 Min-P 截断采样；§9 讨论统一视角与边界；§10 总结。

---

## 2 相关工作

### 2.1 FEP 与变分推断

Friston 的自由能原理[1]将感知、行动与学习统一为变分自由能最小化。Buckley et al. (2017)[2] 对 FEP 的数学澄清指出其依赖若干未显式声明的假设。本工作通过机器检查把这些假设显式化。

变分推断中的 ELBO 分解是经典结果（Blei et al., 2017[3]）。在可检索文献范围内，本库未发现 ELBO 下界、紧性条件与证据间隙的其他机器检查形式化。

### 2.2 注意力机制理论

softmax 注意力与 Gibbs 分布的类比在物理学与 ML 文献中有两条可溯源的线索。第一条是能量模型/现代 Hopfield 网络[5]：Ramsauer et al. (2021)[7] 证明连续状态现代 Hopfield 网络的更新规则与 Transformer 的注意力机制**逐字等价**，并给出 softmax 注意力对应 Hopfield 能量函数（含全局平均、亚稳态平均与单模式存储三类极小点）的刻画；该文上承 Krotov & Hopfield (2016)[6] 的稠密联想记忆（指数型能量函数）。第二条是统计力学视角：softmax 权重正比于 `exp(query·key / √d)`，即配分函数归一化下的 Boltzmann 因子。本工作与前两者的区别在于：Ramsauer et al. (2021)[7] 与 Krotov & Hopfield (2016)[6] 在纸笔分析与实验层面建立能量-注意力对应，而本文在证明助手内把「softmax = Boltzmann 分布（温度参数化下）」提升为**机器检查的精确等式定理**（定理 5.1 及推论 5.1a/5.2），并把动力学解读分层：稳态方程定理 5.3 是「若视为 Markov 核」的稳态**验证**；把注意力核迭代视为 Markov 链的 TV 收缩与迭代收敛已在 Doeblin minorization 假设下机器检查（`attention_tv_contraction` L29195 / `attention_tv_iter_contraction` L29287 / `attention_iterate_converges` L29330，显式几何率 (1−δ)ⁿ，§5.5）；状态空间（clim）收敛仍开放（§5 章首）；由注意力权重构造 `transition` 与 Doeblin 前提的核上实例化已在库内闭合（§5.5，req 对应件见公开 artifact 迁移清单（补充材料 S2）），为上述物理类比给出构造性、可审计的精确边界。同时作范围界定：Ramsauer et al. (2021)[7] 的核心贡献——能量函数的刻画、极小点分类与收敛/容量等动力学分析——不在本工作的形式化范围内；本文动力学侧的机器检查主张以 §5.5 为限（稳态方程验证 + Doeblin 前提下的 TV 收敛），状态空间（clim）收敛维持开放登记（§9.2 边界 5）。

### 2.3 解码截断采样与 KV 缓存逐出

截断采样与 KV 缓存逐出是本文 §6–§8 形式化对象的工程来源：

- **Top-k 截断**：Fan, Lewis & Dauphin (2018)[8] 在分层故事生成中引入 top-k 截断采样（从概率最高的 k 个 token 中采样）。
- **Nucleus / top-p 采样**：Holtzman et al. (2020)[9] 提出 nucleus 采样（保留累积概率达到 p 的最小前缀集），针对文本退化的质量-多样性平衡。
- **Min-P 截断**：Nguyen et al. (2024)[10] 提出 Min-P 动态截断（以最大 token 概率为缩放基准的相对阈值），本文 §8 形式化的正是该策略的核定义与性质。
- **截断采样的理论刻画（先例）**：Hewitt, Manning & Liang (2022)[20] 把语言模型建模为「真实分布 + 平滑项」的混合，将截断采样刻画为**去平滑**（desmoothing），给出截断族的一般理论框架；Meister, Pimentel, Wiher & Cotterell (2023)[21] 从信息论角度提出局部典型性采样（每步逐 token 的信息量贴近模型条件熵的软截断规则）。本文与二者的定位互补：该文献给出截断采样的一般刻画（纸笔理论），本文给出其中截断对象的**机器检查精确恒等**（定理 7.6：`TV == tail_mass/Z_thermo`）与 Min-P 核性质的构造性形式化（§8）。
- **KV 缓存逐出**：H2O（Zhang et al. 2023[11]）以「重击者（Heavy Hitters）+ 近期 token」为逐出准则，把 KV 逐出建模为动态子模问题；本文 §6 把逐出导致的稳态方程偏离刻画为机器检查的恒等式上界、破缺恒为零的正结果与 Real 层定量界（§6.2、§6.2.2）。

这些工作均为工程启发式与经验评估；本文的对应物是它们的**构造性定量刻画**：可判定性、核归一化、单调性、TV 精确恒等与词表大小挂钩（定理 7.6、定理 8.9）。我们明确声明：本工作不提供这些启发式的端到端可计算误差估计（§6.2 边界），形式化的价值在于把被广泛默认的结构事实与前提条件机器化。

### 2.4 形式化工作

| 工作 | 逻辑立场 | 熵/KL/信息论 | Gibbs/变分/FEP | attention 能量对应 | 截断采样/KV |
|---|---|---|---|---|---|
| Isabelle AFP[12]（Source Coding Theorem，Hibon–Paulson 2016；Markov/遍历侧另有 Markov Models（Hölzl–Nipkow 2012）、Ergodic Theory（Gouëzel 2015）等） | 经典 | 熵、信源编码（Shannon 定理的熵下界半边；该条目无 KL/AEP）；Markov 链与遍历论有专条 | 无 | 无 | 无 |
| coq-proba / Infotheo（Affeldt et al.）[13] | 经典为主 | 离散概率、KL、互信息 | 无 | 无 | 无 |
| Coq 概率 monad 路线（Audebaud–Paulin-Mohring 2009） | Coq（分布 monad 框架） | 概率分布的 monadic 组合（随机算法证明） | 无 | 无 | 无 |
| C-CoRN / NuPRL[18][19] | 构造性分析 | 构造性分析基础 | 无 | 无 | 无 |
| Lean mathlib | 经典 | KL 簇（KullbackLeibler：Basic/ChainRule/DataProcessing/KLFun，含数据处理不等式）、Hamming、信源编码；无 Pinsker 不等式、无 softmax 定义（2026-09-10 master 快照，文件树与声明索引实查；形式化记述另见 Degenne 2025[42]） | 无（变分推断未覆盖） | 无 | 无 |
| **FEP_Lean（Friedman 2026，Lean 4 + Mathlib）[34]** | 经典（依赖 Mathlib 测度论层） | 有限集概率、KL（有限空间）、变分自由能界 | **FEP 数学核、主动推断、贝叶斯力学、信息几何、非平衡热力学**（155 主题 / 20 族，155/155 sorry-free；作者明言不证明 FEP 作为物理理论） | 无 | 无 |
| **本工作** | **纯构造性** | KL、Gibbs 不等式与等号条件 | FEP 数学核、ELBO、最大熵对偶 | softmax = Boltzmann（定理 5.1 及推论 5.1a/5.2） | top-k/Min-P 归一化与 TV 定量、KV 逐出界 |

（表中“无”指按可检索文献与库文档，该主题未进入其形式化范围；本表只对照主题覆盖，不断言他人的内部细节。）

**经典背景（本表之外的计量/不等式来源）**：KL 散度的原始文献见[40]，把最小判别信息问题表述为分布到凸集上的 I-投影见[41]（本文 §8.7 的投影主定理与 §9.1 的自由能–KL 分解共享该构造）；TV 与 KL 的两条标准传递为 Pinsker[39] 的 `δ ≤ √(½·KL)` 与 Bretagnolle–Huber[38] 的 `δ ≤ √(1 − e^{−KL})`——后者与本文 §5.5 的 `δ* = e^{−2Δ/T}` 及 `(1 − e^{−2Δ/T})ⁿ` 形态同构，是 §10.2 所述 KL→TV 缺口在经典侧的两条可选路线（前者含常数 2 限制，后者无）；形式化实数分析的库间综述见[43]。

据我们所知（检索协议见补充材料 S2，公开 artifact），截至 2026-09-14 未检索到将 FEP 数学核、attention-Gibbs 桥、KV 逐出界与 top-k/Min-P 截断定量刻画作为**统一体**在证明助手中形式化；本文的“首次”主张限于该 scoped claim（Coq、纯构造性、上述四族结果构成的统一体），不涉及经典逻辑下单个主题的零散形式化。**范围澄清（须与本表并读）**：FEP 主题本身已有独立的机器检查工作——FEP_Lean（Friedman 2026）[34] 在 Lean 4 + Mathlib 上给出 155 主题的 FEP / 主动推断 / 贝叶斯力学目录，属**经典测度论路线**，不覆盖 attention-Gibbs 桥、KV 逐出界与截断采样定量刻画，亦不带零公理与 Set 层可提取性口径；故本文的“统一体”主张与该项互补而不重叠，FEP 数学核一列的先行工作**不为空**。

**检索协议（scoped 主张与 §2.4 对照表的核实；检索日期 2026-09-14）**：
- **DBLP**：查询串 `free energy principle formalization`、`variational free energy Coq`、`attention Gibbs Coq`、`truncated sampling formalization`、`KV cache eviction formalization`；
- **Google Scholar**：上述词组与 `Coq` / `Isabelle` / `Lean` / `proof assistant` 的组合检索；
- **GitHub**：仓库与代码检索 `"free energy principle" Coq`、`softmax Boltzmann theorem verified`、`min-p sampling formalization`；
- **mathlib（Lean，master 快照 2026-09-10）**：文件树与声明索引检索 `Pinsker`、`softmax`、`KullbackLeibler`——实查结论：**无 Pinsker 不等式条目、无 softmax 定义**；信息论覆盖为 `Mathlib.InformationTheory` 下 KullbackLeibler 簇（Basic/ChainRule/DataProcessing/KLFun，含数据处理不等式）、Hamming 与 Coding（Kraft/KraftMcMillan/PrefixFree/UniquelyDecodable）；
- **Isabelle/AFP（isa-afp.org，2026-09-10）**：实查结论：概率主题下有 Markov Models（Hölzl–Nipkow，2012，离散时间 Markov 链/状态分类/pCTL 模型检验）、Hidden Markov Models（Wimmer，2018）、Ergodic Theory（Gouëzel，2015）、Markov Decision Processes with Rewards（Schäffeler–Abdulaziz，2021）、Source Coding Theorem（Hibon–Paulson，2016，Shannon 定理熵下界半边）等条目；未见 softmax 注意力核 TV 收缩/迭代收敛的形式化条目——§5.5 的「未见同类」主张 scoped 到该核查范围；
- **arXiv**：`truncation sampling`、`locally typical sampling`、`free energy principle machine checked`。

检索式与日期随修订公开，供独立复核；核对结论已回写 §2.4 对照表（Isabelle 与 mathlib 两行）。

我们也评估过以 coq-proba / Infotheo 作为依赖库的路线：因其经典逻辑（含排中律）假设与本库的纯构造性立场冲突，且其内容未覆盖 FEP 数学核与 attention-Gibbs 桥结构，最终未采用。

**Infotheo 对象的构造性可迁移面（对照讨论）**：对上表的 Infotheo/coq-proba 行，本文进一步讨论其与构造性立场的关系：该库的离散熵、KL 与互信息等对象在陈述形态上与本文 §3.3/§4.2 的对应物同族，可迁移面主要在**陈述层的对照**（术语、命题形态与恒等式清单）；由于该库以经典逻辑为背景（含排中律，见上段评估），其任一结论进入本库前需构造性重证而非直接引用——本文的 Gibbs 不等式（定理 4.2）、等号条件（定理 4.3）与对称 KL 恒等（定理 4.6e）可视为该构造性重证路线的已闭合样例。据此，本文与该库为互补定位：其覆盖面向经典信息论的系统整理，本文面向 FEP/注意力/截断对象的构造性定量核；凡本库已构造性闭合的对象无需回指该库，未闭合对象（连续推广等）在 §10.2 登记。

**测度论与有限和的方法论权衡（Isabelle 侧对照）**：Isabelle/HOL 的概率形式化传统以测度论为基——Hölzl (2016) 在 Isabelle/HOL 中的 Markov 链与 MDP 形式化[27]沿测度论概率组织（Markov Models、Ergodic Theory 等 AFP 条目同属该传统，见 [12] 注），以一般测度语义覆盖连续状态空间；本文取有限和路线：状态空间有限枚举、求和为可判定有限和、不等式以逐 eps 余量或精确恒等呈现。两路线对本文对象的权衡是清晰的：本文四族结果（本节 scoped claim）均可在有限和世界内完整陈述并闭合，不需要测度论机器；其代价是不覆盖连续状态空间（§9.2 边界 4、§10.2 第 1 项登记）。方法论上，逐 eps 显式余量使「前提是否显式、误差预算在哪一层」成为每个定理陈述的固有部分，这是本文选择有限和路线的动机，而非对测度论路线的否定。

**mathlib 的方法论定位（对表行的展开）**：在表行实查结论之外，方法论差异值得展开：mathlib[28] 的 KL 散度以测度论泛函形态组织（KullbackLeibler 簇的模块划分含数据处理不等式，见表行实查），底座为经典逻辑；本文的 KL 为有限状态空间上的显式求和（§3.3），一切操作落在可判定序与逐 eps 余量内。两个框架的陈述不在同一抽象层：本文定理的前提（归一化、正性、有限枚举）与结论（逐 eps/恒等形态）均绑定有限和语义，单向搬移到测度论泛函需重新给出适用面论证，反之亦然；这也是本文坚持单一构造性底座的原因——四族结果的全部前提在同一定理生态内显式可查（§9.2.1）。

**概率 monad 路线（Coq 侧对照）**：Coq 社区的另一条概率形式化路线以分布 monad 为载体——Audebaud 与 Paulin-Mohring (2009) 在 Coq 中以概率分布的 monadic 组合组织随机算法证明（Miller-Rabin 素性检测等经典例证）[29]。与该路线相比，本文不引入分布 monad 抽象：分布直接表为有限状态空间上的函数（§3.2），组合律以显式求和恒等呈现。权衡在于：monad 路线便于表达分布变换的一般组合与复用，有限和路线便于携带显式常数与可判定性——本文的 TV 精确恒等（定理 7.6）与显式 Doeblin 率（定理 5.5/5.6）依赖后一形态。两路线在离散对象上可对照，但抽象层不同使证明不可直接移植；该对照同时支持本节 scoped claim 的边界：「首次」主张不排除概率 monad 路线的既有工作，只主张四族对象统一体的构造性形式化。

**机器学习的形式化验证面（一般文献定位）**：在 CompCert 一系的程序验证之外，机器学习本身的形式化工作可按对象分三支：①学习/优化算法的定理级形式化——如 Coq 中带验证泛化界的学习器证书（Bagnall 与 Stewart, 2019[30]）与凸优化一阶算法收敛率的形式化（Li et al., 2025[31]）；②学习系统的运行时安全组合——如强化学习的 shielding 框架（Alshiekh et al., 2018[32]，以时序逻辑安全层监控与修正策略动作）；③神经网络性质的专用判定——以 Reluplex（Katz et al., 2017[33]）为代表的 SMT 路线（性质判定工具，非证明助手内定理证明）。本文在该对照面中的位置：对象是学习系统的概率内核（FEP 数学核、attention-Gibbs 桥、截断采样与 KV 逐出的分布层性质），方法上是证明助手内的构造性定理证明而非性质判定工具；与上述三支不构成重叠，亦不在其结论上叠加主张。可检索范围内的对照以该三支为限，未声称穷尽。

---

## 3 构造性基座

### 3.1 Cauchy 实数与可计算序

本库从有理数 Cauchy 序列构造实数：具体 `Real` 表示为携带柯西见证的有理数 Cauchy 序列（`sigT` 封装）——**取原始序列表示、不取商类型**；本文定理陈述所用等式 `Id` 即该原始序列表示上的相等（序列逐点相等语义的 setoid 对应物由平行 `req`/`real_eq` 系承载，并配 `real_eq_mult_compat` 等 Proper 兼容族，见下）；可计算序 `le`/`lt` 为 Or 编码的构造性序，其 Bishop 非严格序替代面 `real_le_b`（∀eps>0, x < y + eps）已完成谓词级封装（模块 `UpRealLeB`），且该序在 setoid 路线上的反对称已可证（`gibbe2_le_b_antisym`：`real_le_b a b -> real_le_b b a -> real_eq a b`，模块 `UpReqGibbsE2` L119）——所有存在性结论均为构造性见证。作为基座完备性注记：库内并已机器检查几何 π 与 Leibniz π 的跨定义相等（`b5dT_f1_pi_geom_eq_leibniz_univ`：`real_eq real_pi_geom cauchy_real_pi_leibniz`）。库尾的 Setoid 并行接口层（`Module RealSetoidCore`）把 `real_eq` 的全运算 Proper 兼容性（`real_eq_mult_compat` 等 10 条）、metric 逐 eps 度量族（`real_metric_triangle_eps` 等）与柯西完备性双桥（`real_cauchy_complete_metric`/`real_cauchy_complete_metric_natle`）逐一证明，并组装 Core 接口实例 `Real_RealInterfaceSetoidCore`；该 Core 实例不含 `exp_neg_pos`/`log` 字段；进一步在 `Section FullInstance` 装配完整版 `Real_RealInterfaceSetoid`，把 exp 族（`exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_zero := cauchy_real_exp_zero`、`exp_neg_plus := cauchy_real_exp_plus`）与 log 族（`log_inv := cw_log`、`log_inv_exp_neg := log_inv_exp_neg_thm`、`log_inv_one := log_inv_one_thm`、`log_inv_mult := log_inv_mult_thm`）共 57 字段无一遗留；增强版实例 `RealEnhancedReal` 见 §9.2.3(e)。与 `RealInterfaceEnhanced`（`Id` 版）缺口的关系详见 §9.2.3。

**与 Coq 标准库的对应关系（自定义原语首次出现处的对照）**：本文嵌入代码中的 `exp_neg`、`inv_pos` 等原语为库内自建定义，其数学内容与 Coq 标准库的对应为：`exp_neg x` 对应标准库 `Reals.Rtrigo.exp` 的负指数 `exp(−x)`（本库以柯西序列构造性给出，非公理化经典实数）、`inv_pos` 对应正实数求逆（经典侧角色对应 `R_inv`）。不直接采用标准库 `Reals` 作为基座的理由：标准库实数为公理化经典实数（其理论依赖排中律等经典公理），与本库零公理、纯构造性的立场不兼容——库的标准库依赖限于有理数层（`Q` 及 `QltT`/`QleT` 判定序，§9.2.1），分析层自建；这与 §2.4 未采用经典逻辑概率库（Infotheo/coq-proba）作依赖的理由同一。

**为何不基于 C-CoRN 自建基座（动机）**：本文不依赖 C-CoRN[18]，理由有三。其一（接口粒度与目标层不同）：C-CoRN 的 Setoid 代数以 `Module`/`Module Type` 组织，面向抽象代数层次的库内复用，未提供「把具体实数模型的超越函数性质回填为下游应用定理的假设字段」这一应用层接口；本文接口族（§3.5）以 `Class`/`Instance` 组织，字段（`exp_neg_pos`/`exp_neg_plus`/`log_inv` 等）正是为该回填设计（§3.5 三实例装配）。其二（依赖自足面）：本文基座以「仅依赖 Coq 标准库有理数层」为工程口径（见上段），不引入构造性分析库依赖；C-CoRN 现行公开仓库（rocq-community/corn，原 coq-community 名下）的一般形态仅作对照参照，本文不对其内容与维护状态作进一步断言。其三（构造路径并行）：C-CoRN 与本文同属 Bishop 构造性传统，两条构造路径为并行关系——§1.2 已标注第一层与其构造性分析先例的重合度（高），本文的贡献主张限定于 ML 侧量化陈述（§2.4 表与 scoped claim）。

### 3.2 概率分布与 Boltzmann 分布

有限状态空间 `S` 上的分布由函数 `S -> R` 表示。Boltzmann 分布定义为：

```coq
Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo : R := sum_over_S boltzmann_factor.

Definition boltzmann_dist (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).
```

其中 `energy : S -> R` 为能量函数，`D > 0` 为温度。`exp_neg` 表示构造性负指数函数。

### 3.3 KL 散度与相对熵

```coq
Definition relative_entropy (p q : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))).
```

### 3.4 自由能

```coq
Definition free_energy (energy : S -> R) (beta : R) (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (energy s))
  + mult beta (sum_over_S (fun s => mult (p s) (log (p s)))).
```

---

### 3.5 实数接口族与实例化

本库不以实数公理为起点，而把实数抽象为满足一组代数、序与完备性条件的接口。接口族按相等谓词分为两系：以命题相等 `Id` 表述的 `RealInterface` 及其增强版`RealInterfaceEnhanced`，以及以 setoid 等价 `req` 表述的 `RealInterfaceSetoid` 系。两系的字段构成一一对应，实质差别在于**超越函数字段是否携带正性前提**：柯西实数上的对数只能在正参数上构造（`cw_log`），因此 log 族带前提的 setoid 系可由具体 `Real` 满足。本文的实例化全部落在该系上。

| 接口 | 定义 | 字段构成 | `Real` 实例 |
|---|---|---|---|
| `RealSetoidCore.RealInterfaceSetoidCore` | Class | setoid 核心（req 自反/对称/传递）；常数与运算；Proper 原理；环律；序律；正元求逆；metric 逐 eps 族；lim / lim_unique / cauchy_complete | `Real_RealInterfaceSetoidCore` |
| `RealSetoid.RealInterfaceSetoid` | Class | Core 全部字段 + exp 族（exp_neg / exp_neg_pos / exp_neg_zero / exp_neg_plus）+ log 族（log_inv 及三条恒等，带正性前提）+ metric 逐 eps 与完备性 | `Real_RealInterfaceSetoid` |
| `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid` | Class | Setoid 全部字段 + 正性与保序（one_pos / lt_mult_compat / inv_pos_le_compat 等）+ min / r_max / pos_test / pos_part / r_if + abs 族 + exp_neg 族 + log 族（带正性前提）+ metric 与完备性 | `RealEnhancedReal` |

log 族的前提是两系的分水岭。setoid 系的相应字段为：

```coq
(* RealInterfaceSetoid *)
log_inv : forall x, lt zero x -> R;
(* RealInterfaceEnhancedSetoid *)
log : forall x, lt zero x -> R;
log_inv : forall x, lt zero x -> R;
exp_neg_log_inv : forall x Hx, req (exp_neg (log_inv x Hx)) x;
```

即 `exp_neg` 与 `log_inv` 的互逆性只在正参数上要求——这与构造性对数的定义域一致，
也是该系接口能够实例化的原因。

三个实例的字段逐一取自 `Real` 层已证引理，不含任何公理。例如`RealInterfaceEnhancedMod.RealEnhancedReal` 的回填包括`req := real_eq`、`plus := real_plus`、`req_plus_compat := RealSetoid.real_eq_plus_compat_adapt`；完整版实例 `Real_RealInterfaceSetoid`则把`exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log`等超越函数字段填为实值。度量与完备性方面，`metric_pos` 与 `metric_triangle` 采用**逐 eps 余量形式**：构造性 `le` 以 `Or (lt) (req)` 编码，无法表达「非严格且不趋近」，故以 `∀ eps > 0` 的余量陈述，这是该编码下可达的最强形式。该论断在 Or 编码下成立不变，且有同框对证：`min a b ≤ a` 的 Or 形精确版构造性不可证、同一语句的 Bishop 形（`real_min_le_l_B`）可证（`UpRealLeB.v` 尾注判定 2/7）——「逐 eps 余量」机制现已由序谓词 `real_le_b` 完成谓词级封装（Set 层 forall 型，零 Prop 泄露），并以装配引理族覆盖 28 件 plain/D·eps 余量件。

---

## 4 自由能原理的数学核

### 4.1 变分自由能分解

**定理 4.1**（`free_energy_kl_decomp`）：对任意归一化分布 `p`，
```
Id (free_energy energy D p)
   (plus (free_energy energy D boltzmann_dist)
         (mult D (relative_entropy p boltzmann_dist))).
```

即：
```
F[p] = F[p_b] + D·KL(p‖p_b).
```

〔构造强度：等式档——Id 层恒等式，强度由「Σp=1 逐点等式」承载、不涉序编码；setoid 同位直迁（`req_free_energy_kl_decomp`）；Real 层完整复刻已证（`rfep_real_kl_decomp_full`，模块 `UpReqRealFEP`；规范化引理 `real_kl_decomp_full_canon`，模块 `UpReqFEPCanon` L48 直接实例化；2026-09-12 核验）——档位定义见 §9.3〕

**证明概要**：
1. 将 `Σ p(s)·energy(s)` 用 Boltzmann 因子改写为 `−D·Σ p(s)·log p_b(s) − D·log Z`；
2. 熵项 `Σ p(s)·log p(s)` 与 KL 定义合并；
3. 利用 `p` 归一化消去 `Σ p(s)·log Z = log Z`。

### 4.2 Gibbs 不等式与等号条件

**定理 4.2**（`gibbs_inequality`）：对任意归一化正分布 `p, q`，
```
le zero (relative_entropy p q).
```

〔构造强度：Id 层结论为 Or 编码精确形（第一档语法），其强度实际消费于接口字段 `log_le_linear`；req 版为同位重述的条件形式（`req_gibbs_inequality`，消费 Section 前提槽、具体实例上未由实例满足）；Real 层最强承载为第三档逐 eps 形 `real_gibbs_inequality_eps`（第二档 Bishop 形 `real_gibbs_inequality_B`/`gibbsd_gibbs_inequality` 可引，严格正需显式分歧见证；第一档精确形在具体实数层不可达）——档位定义见 §9.3〕

**证明概要**：利用 log 严格凹性的切线不等式，得到逐点 `p(s) − q(s) ≤ p(s)·(log p(s) − log q(s))`；求和后左侧 `Σ(p−q)=0`，右侧即为 KL，故 KL ≥ 0。

**求和策略说明（误差累积机制）**：库内 Real 层逐 eps 版（`real_gibbs_inequality_eps`，L41704）的误差预算既不采用逐项分配 ε/|S|，也不依赖 telescoping，而是**归一化吸收**：逐点核心 `real_gibbs_core_eps` 给出 `p(s) − q(s) ≤ p(s)·(−log(q(s)/p(s))) + p(s)·eps`——每点余量按该点质量 `p(s)` 加权，求和后总余量为 `(Σ_s p(s))·eps == eps`（归一化 Σp == 1），故误差累积恰为 eps 而非 |S|·eps（验证状态见表 A.1）；同族结论的 Bishop 非严格序形（`real_gibbs_core_B` 走 D·eps 字面闭合、`real_gibbs_inequality_B` 等，模块 `UpRealLeB`）已全部交付，逐 eps 余量机制的谓词级封装见 §3.5。

**定理 4.3**（`gibbs_equality`）：若 `relative_entropy p q = 0`，则 `p` 与 `q` 逐点相等。

〔构造强度：等号条件档——无条件等号消去（`log_eq_linear`）需强三分/LPO、构造性不可证；req 同位（`req_gibbs_equality`，等号条件为 log 严格凹的唯一缺字段）；bool 载体＋显式前提为可达形态（`gibbe2_gibbs_equality_bool`）；Real 层无复刻——档位定义见 §9.3。〔2026-09-12 核验：注入前提已无条件由具体实例满足——`t1_log_eq_linear_inject`（模块 `UpReqKLSTangent` L81）＋ `t1_gibbe2_gibbs_equality_bool`（同模块 L121）零接口前提；「Real 层无复刻」登记不变。〕

**证明概要**：由逐点非负差分项之和为零推出每一点差分项为零；结合 log 严格凹的等号条件与乘法消去律，得到 `p(s)=q(s)`。

### 4.3 Boltzmann 分布的自由能最小化

**定理 4.4**（`min_free_energy_is_boltzmann`）：对任意归一化正分布 `p`，
```
le (free_energy energy D boltzmann_dist) (free_energy energy D p).
```

〔构造强度：等式/唯一性档——序强度经 `le` 字段（具体实例上 Or 编码），不涉第一档不可证面；req 无条件形态（`req_min_free_energy_is_boltzmann`）；Real 层第三档逐 eps 序档已组装（`min_free_energy_is_boltzmann_eps`，模块 `UpReqMinFreeEps` L122；2026-09-12 核验）——档位定义见 §9.3〕

**证明概要**：直接代入 `free_energy_kl_decomp`，并利用 `KL(p‖p_b) ≥ 0` 与 `D > 0`。

**定理 4.5**（`free_energy_min_unique`）：若 `free_energy p = free_energy boltzmann_dist`，则 `p` 与 `p_b` 逐点相等。

〔构造强度：等式/唯一性档（同定理 4.4）；req 同位；Real 层无复刻——档位定义见 §9.3〕

**证明概要**：由 `F[p]=F[p_b]` 与自由能分解得 `D·KL(p‖p_b)=0`；`D>0` 消去得 `KL=0`；再用 `gibbs_equality`。

### 4.4 最大熵对偶

最大熵原理的学科源头是 Jaynes (1957)[22]；本节在有限离散状态空间上以构造性形式化重现该原理的离散形态（约束期望能量下熵最大化的解为 Boltzmann 分布），不引入 Lagrange 乘子。

**定理 4.6**（`max_entropy_is_boltzmann`）：Boltzmann 分布也是**约束期望能量下最大化熵**的分布。在有限状态空间 S 上，优化变量为任意归一化正分布 p（归一化且逐点正）；约束为等式约束 E_p[energy] = E_{p_b}[energy]；结论为 S[p] ≤ S[p_b]，即 Boltzmann 分布的熵最大。完整 Coq 语句见补充材料 S1。

〔构造强度：序档——Id 层结论 `S[p] ≤ S[p_t]` 为 `le` 语法；req 同位（`req_max_entropy_is_boltzmann`）；Real 层经第三档逐 eps 形链承载，无独立复刻件——档位定义见 §9.3〕

**精确界定**：

| 项 | 内容 |
|---|---|
| 优化变量 | 任意 `p : S -> R`，满足 `normalized p`（归一化）与 `positive_dist p`（逐点正） |
| 约束 | **等式约束**：`energy_expectation p == energy_expectation boltzmann_dist`，即 `p` 的期望能量与 Boltzmann 分布**严格相等**（非 `≤`） |
| 结论 | `entropy_dist p ≤ entropy_dist boltzmann_dist`，即 Boltzmann 分布的熵最大 |
| 温度与 Lagrange 乘子 | 本库不引入 Lagrange 乘子；对偶性通过 `entropy_deficit_kl` 建立：在等能量约束下 `S[p_b] − S[p] == KL(p‖p_b)`，再用 `gibbs_inequality` 得 `KL ≥ 0`；温度参数化形态下的完整对偶见定理 4.6a–4.6e |

**定理 4.6 的精确形态（温度参数化闭合，定理 4.6a–4.6e）**：定理 4.6 是「固定约束值」形式——它把约束取为 `E(p) == E(p_b)` 这一个具体能量值，未刻画温度 `D` 与约束能量之间的对应。该缺口由温度参数化形态闭合：对每个温度 t，约束熵最大化解存在且唯一，且温度-能量严格单调，构成 Lagrange 对偶的构造性闭合（FreeEnergyMinimization Section，零新增公理）：

**定理 4.6a**（`entropy_deficit_kl_temp`）：熵亏 = KL 的温度版——同约束能量 `E(p) == E_temp(t)` 下 `S[p_t] − S[p] == KL(p‖p_t)`（组装 `entropy_temp_explicit` + `relative_entropy_temp_decomp` + 同能量替换）。

〔构造强度：等式档；req 同位（`req_entropy_deficit_temp`）；Real 层温度版熵亏序档已组装（`real_entropy_deficit_kl_temp`，模块 `UpReqEntropyDeficitTemp` L509；2026-09-12 核验）——档位定义见 §9.3〕

**定理 4.6b**（`max_entropy_is_boltzmann_temp`）：温度版最大熵——`E(p) == E_temp(t) ⟹ S[p] ≤ S[p_t]`（熵亏温度版 + `gibbs_inequality` + le 链）。

〔构造强度：序档（同定理 4.6）；req 同位；Real 层序档已组装（模块 `UpReqEntropyMaxTemp`，2026-09-12 核验）——档位定义见 §9.3〕

**定理 4.6c**（`entropy_max_unique_temp`）：温度版唯一性——同能量 + 同熵 ⟹ `p == p_t` 逐点（熵亏温度版 + `minus_self_zero` ⟹ KL == 0 + `gibbs_equality`）。

〔构造强度：等号条件档——唯一性步骤承定理 4.3 的等号分支构造性边界；req 同位；Real 层可达形已组装（模块 `UpReqEntropyUniqueTemp`）并伴逆否形（模块 `UpReqEntropyUniqueNeg`；2026-09-12 核验）——档位定义见 §9.3〕

**定理 4.6d**（`temp_energy_dual_closed`）：**对偶闭合**——`sigT` 见证 `p_t` 本身，嵌套 `And`（4 个 `And` 节点、5 个合取支：归一化、正性、约束 `E == E_temp(t)`、最优（同能量熵最大）、唯一（同能量同熵 ⟹ 逐点相等））：
```
sigT (fun pb : S -> Real =>
  And (And (normalized pb) (positive_dist pb))
      (And (Id (energy_expectation pb) (energy_exp_temp t Ht))
           (And (forall p, normalized p -> positive_dist p ->
                  Id (energy_expectation p) (energy_exp_temp t Ht) ->
                  le (entropy_dist p) (entropy_dist pb))
                (forall p, normalized p -> positive_dist p ->
                  Id (energy_expectation p) (energy_exp_temp t Ht) ->
                  Id (entropy_dist p) (entropy_dist pb) ->
                  forall s, Id (p s) (pb s)))))).
```
即**对每个温度 t（= 每个约束能量 E_temp(t)），熵最大化问题解存在且唯一**——与 `energy_exp_temp_mono`（温度↔能量单调）合拢为最大熵 Lagrange 对偶的构造性完整闭合；零新增公理、纯构造性、Set 层（`And := A*B`、`sigT` 信息性）。

〔构造强度：见证构造档（严格见证形亲缘）——内容为 sigT 显式见证组装（5 合取支）；req 同位 sigT 形；Real 层对应件已建成（`RealEnergyTempMono`；Bishop 形伴件 `etm_energy_temp_mono_b` 等，范围外披露见 §9.2）——档位定义见 §9.3〕

**定理 4.6e**（`energy_exp_temp_strict_mono`）：**温度-能量严格单调**——温度参数化对偶闭合中“温度 ↔ 约束能量”的**一一性严格化**：`t1 < t2` 且 `KL(p_{t2}‖p_{t1}) > 0`（诚实条件：能量非平凡 ⟹ 不同温度分布不同 ⟹ KL 严格正）⟹
```
lt zero (minus (energy_exp_temp t2 Ht2) (energy_exp_temp t1 Ht1))
```
即温度升高 ⟹ 期望能量严格增（差正形态）。证明核心是**对称 KL 恒等**：
```
(b1−b2)·(E2−E1) == KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})
```
（两温度 KL 分解 `relative_entropy_temp_decomp` + 熵显式 `entropy_temp_explicit` 相减）——KL 严格正 + `b1−b2 > 0`（inv 反序）经正乘严格消去（`lt_mult_pos_cancel`）⟹ 差正。零新增公理、纯构造性。

〔构造强度：严格见证形——严格单调以显式前提（能量非平凡）与严格序见证承载；req 同位（`req_energy_exp_temp_mono`，诚实签名含显式正性前提）；Real 层对应件已建成（`RealEnergyTempMono`；Bishop 形伴件 `etm_energy_temp_mono_b` 等，范围外披露见 §9.2）——档位定义见 §9.3〕

### 4.5 ELBO 下界与紧性

变分推断中，证据 `log p(x)` 可通过变分分布 `q(z)` 近似。ELBO 定义为：

```
ELBO(q) = E_q[log p(x,z)] − E_q[log q(z)]
        = log p(x) − KL(q(z)‖p(z|x)).
```

**定理 4.7**（`elbo_lower_bound`）：
```
le (elbo q) (evidence).
```

〔构造强度：序档；req 族已交付（`elbo_lower_bound`/`evidence_kl_decomp`/`elbo_explicit` 等）；Real 层逐 eps 序档已组装（`real_elbo ≤ real_evidence + eps`，模块 `UpReqELBOEps`；2026-09-12 核验）——档位定义见 §9.3〕

**定理 4.8**（`elbo_tight`）：当且仅当 `q(z)` 等于真实后验 `p(z|x)` 时，ELBO 等于证据（等号条件）。

〔构造强度：序档＋等号条件档——等号条件承定理 4.3 的构造性边界；req 同位；Real 层可达形（prod 双向＋切点⟹一弱形）已组装（`t12_elbo_tight_forward`/`t12_elbo_tight_backward`，模块 `UpReqELBOTight`；2026-09-12 核验）——档位定义见 §9.3〕

**证明概要**：由 `evidence_gap_kl` 将证据与 ELBO 的差写成 KL 散度，再用 `gibbs_inequality` 与 `gibbs_equality`。

### 4.6 稳态 Boltzmann 分布

**定理 4.9**（`steady_state_boltzmann`）：对满足详细平衡的转移核，Boltzmann 分布是稳态分布，即
```
Σ_{s'} p(s')·T(s',s) = p(s).
```

〔构造强度：等式档；req 同位（`req_steady_state_boltzmann`）；Real 层等式逐字复刻已完成（`real_steady_state_boltzmann`，模块 `UpReqSteadyThermo` L100，热力学侧载体 `real_boltzmann_prob` L81；2026-09-12 核验）；注意力侧稳态方程由定理 5.3a 承载——档位定义见 §9.3〕

**证明概要**：由详细平衡将求和项逐点替换为 `p(s)·T(s,s')`；提出常数因子 `p(s)`；利用转移核归一化 `Σ_{s'} T(s,s') = 1` 即得。

### 4.7 训练等价性

**定理 4.10**（`training_equivalence`）：最大化 ELBO 与最小化变分自由能等价。该定理为“变分推断 = 自由能最小化”提供了形式化基础。

〔构造强度：序档——交叉熵↔KL 单调输运（Real 层 real_le 版已组装：`real_training_equivalence`，模块 `UpReqTrainingEquiv`；2026-09-12 核验）——档位定义见 §9.3〕

---

## 5 注意力-Gibbs 桥：形式同构与「若视为 Markov 核」的稳态验证

本章标题中的「稳态」须分两层界定。**其一（稳态方程的验证）**：`steady_state_boltzmann_attn` 刻画的是，若把 softmax 输出视为一个满足详细平衡与行归一化（前提为 `transition` 族 Section 变量声明）的 Markov 转移核，则 Boltzmann 分布是它的稳态分布——这是对「Boltzmann 满足稳态方程」的**验证（verification）**，并不声称 Transformer 的注意力机制本身收敛到 Boltzmann 分布（注意力逐层应用，每层的 softmax 输出是该层输入的一个函数，不是某个 Markov 核的稳态分布）。**其二（迭代的 TV 收敛，已机器检查）**：把 `attention_step` 视为 Markov 单步，库内在 Doeblin minorization 前提（δ ∈ (0,1)，`transition s s' ≥ δ·boltzmann_dist_attn s'`，Section 变量 `delta`/`minorization`）下证明了单步 TV 收缩 `attention_tv_contraction`（收缩因子 1−δ）、几何迭代收缩 `attention_tv_iter_contraction`（`(1−δ)ⁿ` 界）与迭代收敛 `attention_iterate_converges`（TV→0，eps-N sigT 见证），全部 Qed、显式几何率 (1−δ)ⁿ（详见 §5.5）。因此本节内容为：稳态方程**验证**（定理 5.3）+ 注意力核迭代在 TV 意义下的**收敛（convergence）**（§5.5）。库内已把「由注意力权重构造 `transition` 的具体方式」与「Doeblin minorization 前提在（有界 logits）注意力核上的实例化」两项闭合为机器检查内容（`bs_kernel`/`bs_minorization`，δ* = e^{−2Δ/T}，§5.5 定理 5.4–5.6）；仍未形式化的边界：状态空间意义（`clim`）下的收敛，§5.5 双点收缩族的 setoid 迁移与 Real 层完整复刻（附录 B、§10.2），以及「双界 logits → 显式收缩率」的末端拼装（§9.2 边界 3——「Q/K 范数界 → 双界 logits」一段已闭合，§5.5 定理 5.7/5.8）。softmax 与 Boltzmann 分布的关系应表述为「**形式同构**」；动力学侧的收敛形态见 §5.5。

### 5.1 定义

库内 softmax 使用 `exp_pos_fn`，即标准正指数 softmax。以下为逐字抽取自基座 `AttentionGibbsBridge` 节的定义（与库内声明逐字核对）：softmax(z)(s) := e^{z(s)} / Σ_{s’} e^{z(s’)}。Coq 定义见补充材料 S1。

其中 `partition_function z = Σ_s e^{z(s)}`，`softmax(z)(s) = e^{z(s)} / Σ e^{z}`，即标准 softmax。

（**符号提示**：热力学侧温度自 §3.2 起记为 `D`（`D > 0`），注意力侧温度自本节起记为 `T`（`T_pos : lt zero T`）——二者是同一正参数，换算 `1/T = 1/D`；下文「符号一致性核验」与定理 5.2 的前提（`Id (inv_pos T T_pos) (inv_pos D D_pos)`）即逐字声明该对应，后文不再重复。）

带温度的版本（`T`/`T_pos` 声明与 `partition_function_temp`、`softmax_temp` 同在 `AttentionGibbsBridge` 节）：softmax_T(z)(s) := e^{z(s)/T} / Σ_{s’} e^{z(s’)/T}。Coq 定义见补充材料 S1。

**符号一致性核验**：在 `energy(s) = −z(s)` 且单位温度（`inv_pos D D_pos = one`）下，Boltzmann 因子为

```
boltzmann_factor s = exp_neg (1 · energy s) = exp_neg (−z(s)) = exp_pos_fn (z s)
```

与 softmax 分子逐点相同——定理 5.1（`fep_align`）以 premise-free 形态把这一对应机器检查为等式定理。任意温度版本（推论 5.2）在 `1/T = 1/D` 下同理（`attention_is_gibbs_temp` 证明体内显式构造 `exp_neg (opp (inv T · z s)) == exp_neg (inv D · energy s)`）。

### 5.2 单位温度对应

**定理 5.1（主定理，premise-free）**（`fep_align`，库面 Section `FEPAttention` L112164–L112252，引理声明 L112201，经检索实证）：在接口上下文与 Section 变量 `z : S -> R`、`T > 0`（`T_pos`）、`spp`（求和正性）下，取 `base := fun s => opp (z s)`（能量 = −logits）、`Zf := partition_function_temp T T_pos z`，则对任意状态 `s`：
```
Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
```
即 softmax 温度分布与（能量 = −z 的）Boltzmann 分布**逐点相等，不带任何配分函数相等前提**——两侧的归一化因子在该实例化下定义性为同一个数（`Zf` 本身），前提被构造吸收而非另行假设。这是本文「softmax = Boltzmann」主张在库内的最强形态；§5.4(b) 的 attention 侧变分自由能最小化定理（`attention_minimizes_free_energy_unique`）与 log-sum-exp 恒等（`UpExtras219.free_energy_softmax_eq_neg_T_logZ`）均以该引理为对接件装配。

〔构造强度：等式档（premise-free 主定理）——结论为逐点 `Id` 相等、全链无 Or/eps 分量，前提被构造吸收；req premise-free 对位件（`req_fep_align`）；Real 层承载见定理 5.2a/5.2b——档位定义见 §9.3〕

**证明概要**（纯恒等链，零新增公理）：unfold 定义后，`mult_comm` 提出归一化因子，`id_cong exp_neg (opp_mult_l invT (z s))` 统一两侧指数，`id_refl` 收尾。

**推论 5.1a**（`attention_is_gibbs`，定理 5.1 的带前提单位温度形态）：若单位温度 `inv_pos D D_pos = one`，且能量满足 `energy(s) = −z(s)`，并且热力学配分函数与 softmax 配分函数相等，则
```
forall s : S, Id (softmax z s) (boltzmann_dist_attn s).
```

〔构造强度：等式档——结论逐点 `Id` 相等，不涉序档位；配分相等前提在 FEPAttention 实例化下属定义性后承；setoid 直证（`attention_is_gibbs_setoid`）；Real 层复刻＝定理 5.2a——档位定义见 §9.3〕

**证明概要**：在单位温度下，`boltzmann_factor s = exp_neg(energy(s)) = exp_neg(−z(s))`；与 softmax 分子一致；配分函数相等保证归一化因子一致。在所述前提下，热力学侧（由抽象 `energy` 生成）逐点化归为定理 5.1 的 `base := −z` 形态，结论由 `fep_align` 承载。

**前提合理性注记**：推论 5.1a 的「配分函数相等」前提不是附加假设：在 §5.4(b) 的 FEPAttention 实例化（`base := fun s => opp (z s)`，即 energy = −z）下，热力学侧与 softmax 侧配分函数为同一个数，该前提属定义性成立的同构直接后承（premise-free 形态即定理 5.1 `fep_align`）；其 req 层机器检查承载为 `req_fep_partition_condition`（模块 `UpReqFEPAttn`，L128）与 `req_attention_minimizes_free_energy_unique`（同模块，L211）。

### 5.3 任意温度对应

**推论 5.2**（`attention_is_gibbs_temp`，定理 5.1 的带前提任意温度形态）：若温度满足 `1/T = 1/D`（即 `inv_pos T T_pos = inv_pos D D_pos`），能量满足 `energy(s) = −z(s)`，且配分函数相等，则
```
forall s : S, Id (softmax_temp z s) (boltzmann_dist_attn s).
```

〔构造强度：等式档（同推论 5.1a 的任意温度形态）；req 对位件已交付（模块 `UpReqFEPAttn`）；Real 层复刻＝定理 5.2b——档位定义见 §9.3〕

**证明概要**：利用 `opp_mult_l` 将 `−z(s)/T` 改写为 `energy(s)/D`，再化为与热力学 Boltzmann 因子一致的形式；在所述前提下热力学侧逐点化归为定理 5.1 的 `base := −z` 形态，结论由 `fep_align` 承载。

**前提合理性注记**：同推论 5.1a——任意温度（`1/T = 1/D`）下的「配分函数相等」前提在 FEPAttention 实例化（`base := −z`）下属定义性成立的同构直接后承（premise-free 形态即定理 5.1）：由 `req_fep_partition_condition`（模块 `UpReqFEPAttn`，L128）及其 log Z 侧对应 `req_fep_partition_condition_logz`（同模块，L372）机器检查承载，最小点处自由能取值恒等面由 `req_free_energy_softmax_eq_neg_T_logZ`（同模块，L424）给出，非附加假设。

**定理 5.2a**（`real_attention_is_gibbs`）：单位温度下 softmax = Boltzmann 的 **Real 层复刻**——柯西实数层（RealAttnMain Section）：
```
(real_eq (real_inv_pos D D_pos) real_one) ->
(forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
real_eq real_Z_thermo (real_partition_function z_logits) ->
forall s : S, real_eq (real_softmax z_logits s) (real_boltzmann_dist_attn s).
```
即 `inv D == 1` 且 `energy == −logits` 且配分相等 ⟹ `softmax(z,s) == boltzmann_dist_attn(s)`（逐点）。

〔构造强度：等式档——Real 层复刻，结论为逐点 `real_eq` 相等、不涉序档位——档位定义见 §9.3〕

**证明概要**：`mult (inv D)·energy` 归约（HD + `real_eq_mult_compat` + comm + `real_mult_one`）→ `energy == −logits` 替换 → `cauchy_real_exp_wd` 保 eq（指数归约 e^{−e/D} == e^{z}）→ `real_inv_pos_ext` 逆元统一（inv Z_thermo == inv partition_function）→ 以 `real_mult_comm` 完成证明。显式前件（零公理）：`real_sum_over_S`（抽象 S 求和——S 无枚举，Real 层形态）+ `real_sum_pos_preserved`。

**定理 5.2b**（`real_attention_is_gibbs_temp`，模块 `UpDebtGibbsT`）：任意温度对应的 **Real 层复刻**——柯西实数层、自含定义 `real_softmax_temp`（配正性件 `real_softmax_temp_pos` 与归一化件 `real_softmax_temp_normalized`）：
```
(real_eq (real_inv_pos T T_pos) (real_inv_pos D D_pos)) ->
(forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
real_eq real_Z_thermo real_partition_function_temp ->
forall s : S, real_eq (real_softmax_temp s) (real_boltzmann_dist_attn s).
```
即定理 5.2 的三前提逐字换 `real_eq` 后，`softmax_temp(z,s) == boltzmann_dist_attn(s)` 逐点成立——任意温度版长期缺 Real 承载的现状由该模块闭合（附录 B 同步）。

〔构造强度：等式档——Real 层复刻（任意温度），逐点 `real_eq` 相等——档位定义见 §9.3〕

### 5.4 缩放-温度对偶、温度 T 的语义与配分函数 Z（库内形式化 + interpretation/speculation 标注）

本节混有两类内容：**库内形式化定理**包括 (**c**) 的缩放-温度对偶族（另有 Real 层对偶 `real_scale_temp_duality` 与抽象层任意 d 见证 `sqrt_witness_exists_abstract`，见 (c)），库内已证明的 (a) T→0 硬注意力极限定理（`hard_attention_limit`）、库内闭合的 (a) T→∞ 温度窗口定理（`temp_window_T_infty`）与 (b) 的 attention 侧变分自由能最小化定理（`attention_minimizes_free_energy_unique`）、库内已证明的 (b) log-sum-exp == −T·log Z 恒等（`UpExtras219.free_energy_softmax_eq_neg_T_logZ`）——定理名逐条标注，经与库内声明逐字核对；(a)(b) 的其余内容与 (c) 的算法启示部分属 interpretation/speculation，不构成本库定理；库内定理以 §5.1–5.3 与本节所列精确陈述为准（措辞纪律见 §9.2）。

**(a) 温度 T 在注意力中的语义：软化/锐化插值与 Boltzmann 温度的对偶。** 库内形式化内容：温度以正参数进入——`Variable T : R` 与 `Variable T_pos : lt zero T` 声明于同一 Section `AttentionGibbsBridge`（紧邻温度化定义之前），温度化 softmax 用 `inv_pos T T_pos`（= 1/T）乘 logits：`softmax_temp(z)(s) = e^{z(s)/T} / Σ_{s'} e^{z(s')/T}`（`softmax_temp`；分母 `partition_function_temp`；`exp_pos_fn x := exp_neg (opp x)` 即 e^x）。推论 5.2（`attention_is_gibbs_temp`）的前提逐字声明 `Id (inv_pos T T_pos) (inv_pos D D_pos)`（即 1/T = 1/D），证明体把 `−z(s)/T` 经 `opp_mult_l` 改写为 `energy(s)/D`——**注意力的逆温度与热力学 Boltzmann 逆温度在库内被证明为同一参数**：这是「温度参数化 softmax = 温度参数化 Boltzmann」的精确同构（定理 5.1/推论 5.2 的形式化内容），而非把 `1/√d` 当作近似缩放（`energy`/`z` 未绑定 query-key 点积，§9.2 边界 3）。interpretation：T→∞ 时 1/T→0、softmax 权重趋于均匀（软化）；T→0 时质量向最大 logit 集中（锐化）——「锐化」的逐 T 定量由 `temperature_zero_limit` 与 `softmax_gap_concentration` 承载（非最优/最优态 ≤ e^{−γ/T}；库内代码注释读作「硬注意力坍缩」，逐 T 层面本身是定理），其上的「T→0 量词翻转极限」已机器检查（见下）。

> **硬注意力极限的闭合状态（库内现态）**：计数/求和机器与权重定义（`count_token`、`removeT`、`split_count_one`、`factor_T`、`ZT`、`w_T`，及正性/归一化 `w_T_pos`、`w_T_sum_one`）、Real 层逐点衰减界 `core_decay_bound`（x ≠ m ⟹ w_T(x) ≤ e^{−γ/T}）与 TV 总质量侧闭合 `tv_hard_le_decay_scale`（`TV(w_T, δ_m) ≤ |vocab|·e^{−γ/T}`；其 inv2 折叠代数件 `eq_inv2_double` 以根域自足形态补回，该模块曾在早期迭代暂缺）均已入主库——均为枚举词表世界（`Section AttnHardLimit`，一致间隙前提 `m_count_one`/`gap_le`，`w_T(x) := e^{z(x)/T}/Z(T)`、硬分布 `δ_m`（库内 `hard_dist`，one-hot）、`tv_hard T := (1/2)·Σ_x |w_T(x) − δ_m(x)|`）；∃T₀ 量词翻转极限 `hard_attention_limit` 已机器检查，逐字语句：`Theorem hard_attention_limit : forall eps : Real, real_lt real_zero eps -> sigT (fun T0 => And (real_lt real_zero T0) (forall (T : Real) (Ht : real_lt real_zero T), real_lt T T0 -> real_le (tv_hard T Ht) eps))`——即 ∀ eps > 0 存在 T₀ > 0（sigT 见证），对一切 0 < T < T₀：TV(w_T, δ_m) ≤ eps。〔构造强度：严格见证形——量词翻转极限定理，∃T₀ sigT 显式见证，构造性正例——档位定义见 §9.3〕 **粗界注记**：其上游 TV 界 `tv_hard_le_decay_scale` 的 `|S|·e^{−γ/T}` 为粗界——真值满足 `TV(w_T, δ_m) == 1 − w_T(m)`（逐对差绝对值直接求和：质量侧 `1 − w_T(m)` 与 `Σ_{x≠m} w_T(x)` 各占一半），且 `1 − w_T(m) = Σ_{x≠m} w_T(x) ≤ (|S|−1)·e^{−γ/T}`；库内界对 ∃T₀ 极限陈述足够，本文不主张其紧性。据此本文的「T→0 硬注意力极限」主张（T→0 时温度化权重依总变差收敛到硬注意力分布 δ_m）已证明为机器检查的极限定理。

> **温度窗口的 T→∞ 半边**：`temp_window_T_infty`（模块 `UpTempWindow`，世界 states/w_T/uniform/tv_unif 全装配）逐字语句：
```
Theorem temp_window_T_infty :
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun T2 => And (real_lt real_zero T2)
         (forall (T : Real) (Ht : real_lt real_zero T), real_lt T2 T ->
          real_le (tv_unif T Ht) eps)).
```
即 ∀ eps > 0 存在 T₂ > 0（sigT 见证），对一切 T > T₂：温度化权重 w_T 对均匀分布 U 的 TV ≤ eps（证明取 T₂ := 2Δ·inv(cw_log(1+eps)) + 1，经 e^{2Δ/T} < 1+eps 与 tw_sum_le_const 完成证明）。〔构造强度：严格见证形——量词翻转极限定理（∀eps ∃T₂ sigT 见证），构造性正例——档位定义见 §9.3〕 与 T→0 端的 `hard_attention_limit`（极限对象为点质量 δ_m）合成「**硬注意力–均匀混合**」的温度两极闭合：T→0 质量向最大 logit 集中、T→∞ 权重趋于均匀，两端均以量词翻转的极限定理呈现。适用限制：本定理是 softmax 分布对均匀分布的**采样层 TV 陈述**，与马尔科夫链遍历性/平稳分布无关，不作收敛主张以外的定位。

Transformer 的 `1/√d` 缩放（Vaswani et al., 2017[4]）的 logits 层对偶形态已在库内形式化（`scale_temp_duality`、`scaled_attention_is_gibbs_temp`，见 (c)）；未入库的仅是具体绑定：query-key 点积到抽象 `z` 的对应与非平方 d 的抽象层构造性 √d（§5.4(c) 诚实限定）。退火（annealing：高 T 探索 → 低 T 利用）与蒸馏温度（Hinton et al., 2015[15]）、校准温度缩放（Guo et al., 2017[16]）共享同一「T 为分布锐度旋钮」语义，为文献层面的 interpretation；库内同构为其提供机器检查的精确版。同模式亦见采样侧：Markov 温度的 `temperature`（另一 Section）以 `inv_pos temperature` 进入 `temp_factor`——温度总是以倒数出现。

**(b) 配分函数 Z ↔ softmax 归一化：log Z = log-sum-exp，平衡点为负自由能。** 库内形式化：Boltzmann 侧配分函数 `Z_thermo := Σ_s boltzmann_factor`（`boltzmann_factor s = exp_neg (inv D · energy s)`），`boltzmann_dist_attn = inv_pos Z_thermo · boltzmann_factor`；softmax 侧归一化因子 `partition_function_temp z = Σ_s e^{z(s)/T}`（单位温度版为 `partition_function`）。带前提形态（推论 5.1a/5.2）的第三个前提是配分函数相等 `Id Z_thermo (partition_function z)`/`Id Z_thermo (partition_function_temp z)`，证明经 `inv_pos_ext` 统一两个归一化逆元；定理 5.1（`fep_align`）在 `base := −z` 实例化下无需该前提（两侧归一化因子定义性为同一个数）——attention 的 softmax 分母与 Boltzmann 配分函数在 `energy = −z`、`1/T = 1/D` 下是**同一个数**（同构的直接后承）。**定理（数学陈述与机器检查状态）**：库尾 `Section FEPAttention` 使「attention 侧变分自由能最小化」成为机器检查定理——它取 `base := fun s => opp (z s)`（能量 = −logits）、`F_attn p := free_energy base T p`（`free_energy` 形态见 §3.4/§4.1），故 `F_attn[p] = −E_p[z] + T·Σ_s p(s)·log p(s)`；`attention_minimizes_free_energy_unique` 证明：

```
forall p : S -> R, normalized p -> positive_dist p ->
And (le (F_attn (softmax_temp spp T T_pos z)) (F_attn p))
    (Id (F_attn p) (F_attn (softmax_temp spp T T_pos z)) ->
      forall s : S, Id (p s) (softmax_temp spp T T_pos z s)).
```

即对任意归一化正分布 p：`softmax_temp z`（= 该能量-温度下的 Boltzmann 分布，`fep_align`）的自由能 ≤ p 的自由能（最小半边），且自由能相等 ⟹ p 与 `softmax_temp z` 逐点相等（唯一性半边）——**attention 的 softmax 权重是变分自由能 F_T[p] = −E_p[z] + T·Σ_s p(s)·log p(s) 的唯一最小点**。装配为纯实例化：`free_energy_kl_decomp`/`min_free_energy_is_boltzmann`/`free_energy_min_unique` 在 `base_loss := −z`、`D := T` 处直接实例化，经三条机械对接引理 `fep_partition_condition`/`fep_align`/`fep_F_ext` 完成证明（源件注记零全局公理/Admitted、5 处 Qed）。

**定理（数学陈述与机器检查状态）**：库尾 `Module UpExtras219` 内 `Section FEPLogZ` 使「log-sum-exp = 负自由能」的 attention 侧单列恒等成为机器检查恒等式——`UpExtras219.free_energy_softmax_eq_neg_T_logZ` 证明：

```
Id (F_attn (softmax_temp spp T T_pos z))
   (mult (opp T) (log Zf)).
```

其中 `F_attn p := free_energy base T p`、`base := fun s => opp (z s)`、`Zf := partition_function_temp T T_pos z` 与上文同一定义（`F_attn[p] = −E_p[z] + T·Σ_s p(s)·log p(s)`、`Zf = Z_T(z) := Σ_s e^{z(s)/T}`）——逐字语句即 **`F_attn[softmax_temp(z)] == −T · log Z_T(z)`：softmax 温度分布（变分自由能唯一最小点，见上）处的精确自由能值等于负温度对数配分函数**。装配与上文同通道：`fep_align`（softmax_temp 逐点 == boltzmann_dist）→ `fep_F_ext`（自由能外延）→ 根内 `free_energy_boltzmann`（配 `fep_partition_condition`）在 `base_loss := −z`、`D := T` 处由具体实例满足（`Section FEPLogZ` 自含 4 处 Qed，源件注记零全局公理/Admitted）。与 `attention_minimizes_free_energy_unique` 互补：后者机器检查 `softmax_temp z` 是 `F_T` 的唯一最小点（最小点身份），前者机器检查该点处的精确自由能值（最小点取值）——「attention 最小化自由能」与「log-sum-exp = 负自由能」两件互补的机器检查事实。

interpretation/speculation：(i) 该共同数的对数即 log-sum-exp（`log Z = log Σ_s e^{z(s)/T}`），也是 softmax 归一化因子的对数；在 §3.4/§4.1 的自由能约定（β=D）下平衡点自由能 `F[p_b] = −D·log Z`（由 `log p_b = −E/D − log Z` 与归一化直接导出；库内自由能分解 `free_energy_kl_decomp` 与熵显式 `entropy_temp_explicit` 给出该 log Z 项的代数地位，§4.4 对称 KL 恒等中 log Z 项恰好抵消）——「Z = e^{−F/D}」是本文框架的代数后承；其 attention 侧单列形态（log-sum-exp == 负自由能）已由上文「已定理化」条证明为机器检查恒等式；(ii) 数值上 log Z 通常以 log-sum-exp（减去最大值平移）稳定计算（Blanchard, Higham & Higham, 2021[17]），本库不涉及浮点；若把 attention 视为能量模型，`∂ log Z / ∂z(s)` 正比于 softmax/Boltzmann 期望（自由能对 logits 的敏感性、良定义平滑性来源），但该导数未在库内形式化（`energy`/`z` 抽象，§9.2 边界 3），属 speculation。

**(c) 缩放-温度对偶（库内形式化）与算法设计启示（interpretation/speculation）。**

> **√d 覆盖现状（两层均已闭合）**：抽象层——任意平方维数 d = k² 的见证式实例化已机器检查（`sqrt_witness_nat_sq` 给出 `sqrt_witness (nat_to_R (k·k)) (nat_to_R k)`；`scale_dual_sq_k`/`scale_dual_nat_sq_k` 给出对应 1/k 缩放 == 温度 k 的对偶实例，k ≥ 1——d=4 的 `sq_witness_4` 成为其特例）；Real 层——任意 d ≥ 0 的构造性平方根已证明（`real_sqrt_exists`，`sigT` 见证 r ≥ 0 且 r·r == d，非平方 d 一并覆盖）；抽象 Id 层——任意非负 d（含非平方）的平方根见证实例化已闭合（`sqrt_witness_exists_abstract`，模块 `UpDebtSqrtAbs`）。先前「抽象 Id 层非平方 d 开放」的保留意见已由上述闭合解除；仍开放的只剩 query-key 点积到抽象 logits 的具体绑定（§9.2 边界 3——其「一致范数界 → 双界 logits」一段亦已机器检查，§5.5 定理 5.7/5.8）——请勿把 `1/√d` 缩放在具体 Transformer 实现层面误读为已形式化。

**库内形式化内容**（本块为库内定理，非 interpretation）：库在 `AttentionGibbsBridge` Section 内建立了「缩放-温度」对偶族（库内代码注释明示其 1/√d 缩放视角）：
1. **缩放 softmax 族** `softmax_scaled c z s := e^{c·z_s}/Σ_{s'}e^{c·z_{s'}}`（`softmax_scaled`；c 为任意实缩放因子——exp 恒正 ⟹ 配分函数正性无需 c 正性前提，`partition_function_scaled`）；正性与归一化公理 `softmax_scaled_pos`、`softmax_scaled_normalized` 镜像温度版证明；
2. **核心对偶** `scale_temp_duality`（库内注释明示其 1/√d 缩放视角）：
```
forall (c : R) (Hc : lt zero c) (z : logits) (s : S),
  Id (softmax_scaled (inv_pos c Hc) z s) (softmax_temp_param c Hc z s).
```
即 **∀ c > 0：以 1/c 缩放 logits 的 softmax == 温度 c 的 softmax**——unfold 后两侧首因子逐字相同，配分函数定义性相等经 `inv_pos_ext`/`id_refl` 化归为自反性，纯恒等链、零新增公理；缩放因子 1/√d 与温度 √d 是同一正参数轴上的互逆参数化（库内代码注释），反向对称 `temp_is_scale_duality`；
3. **平方维数见证** `sqrt_witness (d r : R) : Set := Id (mult r r) d`（无 sqrt 函数符号的见证式）与 `scale_sqrt_witness_dual`：凡 `sqrt_witness d r`（r > 0）则以 1/r 缩放 == 温度 r 的 softmax（`scale_temp_duality` 的 r 实例；机器检查实例仅 d=4/r=2：`sq_witness_4` 与 `half_scale_is_temp_two`；一般 d = k² 的『取见证 r := k』为注释级构造模式（库内代码注释），非库内任意 k 的通用引理）；
4. **合成桥**：`scale_inv_T_eq_softmax_temp`：`softmax_scaled (inv_pos T T_pos) z s == softmax_temp z s`（1/T 缩放族 == 库内温度化 softmax，配分函数定义性相等）；`scaled_attention_is_gibbs_temp`：在推论 5.2 的同一前提（`1/T = 1/D`、`energy = −z`、配分匹配）下 `softmax_scaled (inv_pos T T_pos) z s == boltzmann_dist_attn s`——**以 1/T 缩放的 attention == 温度 D 的 Boltzmann**（`scale_inv_T_eq_softmax_temp` + `attention_is_gibbs_temp` 合成）。取 √d := T := D 即「1/√d 缩放 attention == 温度 √d 的 Boltzmann」；
5. **对偶族 Real 层**：`real_scale_temp_duality`（模块 `UpDebtDual`）——∀ c > 0：`real_softmax_scaled (real_inv_pos c Hc) z s == real_softmax_temp_param c Hc z s`（柯西实数层逐点 real_eq；自含定义族 `real_softmax_scaled`、正性件 `real_softmax_scaled_pos`、归一化件 `real_softmax_scaled_normalized`、`real_softmax_temp_param`）——缩放-温度对偶的 Real 层复刻由该模块闭合（定理 5.6c，陈述见 §5.5）。


**适用限制（不外推为 Transformer 具体实现的定理）**：(i) 上述定理全部陈述于抽象 logits 层——`z : logits` 为任意函数，`energy`/`z` 未绑定 query-key 点积（§9.2 边界 3）；(ii) 「√d」在库内以见证式 `sqrt_witness` 形式化——`scale_sqrt_witness_dual` 对任意满足见证条件 `r·r == d` 的 (d, r) 成立；任意平方维数 d = k² 的机器检查实例已补全（`sqrt_witness_nat_sq`、`scale_dual_sq_k`/`scale_dual_nat_sq_k`，经 nat 嵌入环同态 `nat_to_R_mult_hom`；d = 4 的 `sq_witness_4` 为其特例）；Real 层任意 d ≥ 0（含非平方）由 `real_sqrt_exists` 构造性闭合，抽象 Id 层任意非负 d 由 `sqrt_witness_exists_abstract`（定理 5.6d）闭合——√d 的构造在两层全部闭合；(iii) 缩放-温度对偶族的 Real 层复刻已由 `real_scale_temp_duality`（定理 5.6c）闭合；抽象层对偶族本身的 setoid 迁移已交付（`reqd_scale_temp_duality`，模块 `UpReqDist`；`ag_scaled_attention_is_gibbs_temp`，模块 `UpReqAttnGibbs`——迁移清单见公开 artifact 补充材料 S2，逐项已记录；附录 B）。

**interpretation/speculation**（其余部分）：把 `QK^T` 视作能量核，则温度 T（或等价的缩放）成为可调/可学习参数，校准与蒸馏的温度用法（Guo et al., 2017[16]；Hinton et al., 2015[15]）随之获得注意力侧的精确语义；现代 Hopfield 网络的容量-温度关系（Ramsauer et al., 2021[7]，§2.2 已引）以 β=1/T 出现，与本文 `1/T = 1/D` 同构呼应（文献主张）；温度退火/多温度混合可作为推断期工具——库内 `softmax_temp_mix_normalized` 已形式化「任意两温度 softmax 的凸组合仍归一化」（多温度蒸馏/专家混合的数学基础，库内代码注释），但调度自身的收敛性/最优性未形式化，属 speculation。

### 5.5 条件性稳态验证与注意力核迭代的 TV 收敛

本节把「稳态」的双层界定置于定理陈述之先（与 §5 章首一致）：**其一为条件性稳态验证**——定理 5.3 刻画的是「若转移核满足详细平衡与行归一化，则 Boltzmann 分布是其稳态」，属稳态方程的验证，不声称注意力机制本身收敛到 Boltzmann 分布（softmax 行核在非对称 logits 下一般不满足详细平衡）；**其二为迭代的 TV 收敛**——Doeblin minorization（Doeblin, 1938[23]；收缩系数经典见 Dobrushin, 1956[24]；系统现代处理见 Levin–Peres–Wilmer, 2009[25]）前提下的单步收缩、几何迭代收缩与收敛定理（定理 5.4–5.6），其前提由库内实例化验证（`bs_minorization`，显式 δ* = e^{−2Δ/T}），构成本节的主定理群。

**定理 5.3**（`steady_state_boltzmann_attn`）：注意力稳态等于 Boltzmann 分布。

转移核与条件在库内 `AttentionGibbsBridge` 节显式声明为 Section 变量。完整前提如下：

```coq
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.
Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_dist_attn s) (transition s s'))
       (mult (boltzmann_dist_attn s') (transition s' s)).
```

前提（正文陈述）：设转移核 `transition` 满足行归一化（`Σ_{s’} transition(s,s’) = 1`）与详细平衡（`p_B(s)·transition(s,s’) = p_B(s’)·transition(s’,s)`，其中 `p_B` 为 Boltzmann 分布）；结论为 `Σ_{s’} p_B(s’)·transition(s’,s) = p_B(s)`（逐字语句见下）。完整语句见补充材料 S1。

〔构造强度：等式档——稳态方程验证，结论为逐点 `Id` 相等；setoid 直证（`steady_state_boltzmann_attn_setoid`）；Real 层复刻＝定理 5.3a——档位定义见 §9.3〕

**边界声明**：定理 5.3 刻画的是「**若**转移核满足详细平衡与行归一化，**则** Boltzmann 分布是其稳态」——属稳态方程的**验证**（verification）。与之互补，把 `attention_step` 视为 Markov 单步的 TV 收敛已在库内机器检查（Doeblin minorization 路线；δ/minorization 为 Section 前提变量 `delta`/`minorization`）：单步收缩 `attention_tv_contraction`（`TV(attention_step μ, p_b) ≤ (1−δ)·TV(μ, p_b)`，μ 归一化非负）、几何迭代收缩 `attention_tv_iter_contraction`（`TV(iterate n μ0, p_b) ≤ (1−δ)ⁿ·TV(μ0, p_b)`）与迭代收敛 `attention_iterate_converges`（∀ eps>0 存在 N，n ≥ N ⟹ TV_n < eps，sigT 见证，前提初始 TV>0——TV=0 的初始分布与 p_b 逐点相等，经单步收缩不等式归纳后续每步 TV 恒为零、收敛平凡成立，该前提仅排除此平凡情形，不构成覆盖缺口；几何击穿经显式前件 `r_arch_pow_attn`），三者全部 Qed、显式几何率 (1−δ)ⁿ。库内把「transition 的构造」与「minorization 前提的实例化」两项在**抽象层**闭合为机器检查内容，且以比基线更强的双点形态呈现（nat 嵌入件以 `attn_nat_to_R` 系并入主库）：由注意力权重构造 `transition` 的具体方式 = 有界 logits 温度 softmax 核 `bs_kernel(s,s') := e^{z(s,s')/T}/Σ_{s''} e^{z(s,s'')/T}`（行归一化为 `bs_kernel_row`）；Doeblin minorization 前提的实例化 = `bs_minorization`：在双界 logits（−Δ ≤ z(s,s') ≤ Δ、T > 0、Δ > 0）下逐点成立 `δ*·U(s') ≤ bs_kernel(s,s')`，δ* := lo·lo = e^{−2Δ/T}（lo := e^{−Δ/T}，经 `bs_lo_hi_eq` 精确化、零余量损耗），U 为枚举上的均匀分布；于是 Part A 双点收缩 `u_tv_contraction`（`TV(step μ, step ν) ≤ (1−δ)·TV(μ,ν)`，μ、ν 只需归一化——免平稳性、免详细平衡、免 `transition_nonneg`、免 μ 非负，参考分布任意归一化）与 `u_tv_iter`（几何率 (1−δ)ⁿ）在 bs_kernel 上实例化，得到显式率 (1 − e^{−2Δ/T})ⁿ（`bounded_softmax_tv_contraction`/`bounded_softmax_tv_iter`）。前提形态：枚举求和规范化显式前件 `sum_eq_list` + expf 迷你接口（五字段：`expf_pos`/`expf_zero`/`expf_plus`/`expf_mono_lt`/`expf_mono_le`；其 Real 层非空性由 `real_expf_realizable` 在 `cauchy_real_exp` 上由具体实例满足）。「把 `bs_kernel` 行与 §5.2/5.3 的单查询 `softmax_temp` 钉成同一对象」的逐行等价恒等引理已闭合：`bs_kernel_row_is_softmax_temp`（`Section RowView` 内）逐行证明 `Id (bs_kernel … s s') (softmax_temp … (fun s0 => z2 s s0) s')`——经 expf 与 `exp_pos_fn` 的一致性前提 `expf_agree`（`real_expf_realizable` 由具体实例满足后取 `expf := exp_pos_fn` 即满足；附录 A）。仍**未**形式化：状态空间意义（`clim`）下迭代的收敛与该双点族的 setoid 迁移（附录 B）；Real 层侧，双点收缩的抽象层定理 5.4–5.6 的直接 Real 复刻已以 δ 接口形态并入模块化树（定理 5.10，模块化树（补充材料 S2） 树兼容重建件，2026-09-11 核实；该双点族的 setoid 迁移仍开放，附录 B），「Q/K 范数界 → 双界 logits」一段已在模块化树内闭合（定理 5.7/5.8）。

**定理 5.3a**（`real_steady_state_boltzmann_attn`）：稳态方程的 **Real 层复刻**——柯西实数层（RealAttnSteady Section）：
```
real_eq (real_sum_over_S (fun s' => real_mult (real_boltzmann_dist_attn_s s') (real_transition s' s)))
        (real_boltzmann_dist_attn_s s).
```
即 `Σ_s' p(s')·T(s',s) == p(s)`——抽象层定理 5.3 的 Real 值域版。

〔构造强度：等式档——Real 层复刻，逐点 `real_eq` 相等——档位定义见 §9.3〕

**证明概要**：逐点 detailed balance 替换（`real_detailed_balance s s'`）→ 求和外延（`real_sum_over_S_ext`）→ 线性提取 p(s)（`real_sum_over_S_linear`）→ 核归一化（`real_transition_normalization`）→ 以 `real_mult_one` 完成证明。显式前件（零公理）：`real_detailed_balance`（可逆核）+ `real_transition_normalization`（行归一化）+ 求和外延/线性——全部 Real 层可实例化。

库内已证明的定理块（定理名与模块路径经库内声明逐字核对）：

**定理 5.4**（`u_tv_contraction` / `u_tv_iter`）：设参考分布 `u` 满足 `Σu == 1`（任意归一化，无需平稳性/详细平衡），转移核有分解 `transition(s,s') == δ·u(s') + (1−δ)·R(s,s')`（δ ∈ (0,1)，R 行随机——分解式 minorization 的精确形态），则对任意归一化分布 μ、ν：
```
Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
le (tv (u_step mu) (u_step nu)) (mult (minus one delta) (tv mu nu))
```
迭代版 `u_tv_iter` 给出几何率 (1−δ)ⁿ。基线三件套（`attention_tv_contraction` 等）前提中的详细平衡、`transition_nonneg`、μ 非负被消去，参考分布从 Boltzmann 稳态推广为任意归一化 u——在四个前提维度上强于基线三件套。

〔构造强度：序档——TV 界为 `le` 语法，界含正系数乘余量结构（第三档逐 eps 形可达，非第一档不可证面）；req 层 Or 语法 `le` 全部模块交付（`rsq_u_tv_contraction`/`rsq_u_tv_iter`）；Real 层复刻已并入模块化树（模块化树（补充材料 S2） 1,986 行，定理 5.10）——档位定义见 §9.3〕

**定理 5.5**（`bs_minorization`）：有界 logits 温度 softmax 核 `bs_kernel`（z 双显式界 −Δ ≤ z(s,s') ≤ Δ、T > 0、Δ > 0）逐点满足显式 Doeblin 下界：
```
forall s s', le (mult delta_star (Unif s')) (bs_kernel s s')
```
其中 δ* := lo·lo = e^{−2Δ/T}（lo := e^{−Δ/T}），由 `bs_lo_hi_eq` 精确化、零 eps 损耗——此处「零 eps 损耗」指推导全程未引入 eps 余量（lo·lo 两因子界精确相乘），并非主张该界的紧致性：紧致需所有 logits 同时取到下界（z ≡ −Δ），一般 logits 下不成立，界的紧致性不在本定理主张范围。

〔构造强度：显式常数档——零 eps 损耗的非紧下界（δ\* := e^{−2Δ/T} 显式常数），构造性无障碍；req 对位（`rsq_bs_minorization`）；接口前件的 Real 层非空性由定理 5.6b 由具体实例满足——档位定义见 §9.3〕

**定理 5.6**（`bounded_softmax_tv_contraction` / `bounded_softmax_tv_iter`）：在定理 5.5 的同一前提下，bs_kernel 行的单步 TV 收缩率为显式 1 − e^{−2Δ/T}；迭代版给出 (1 − e^{−2Δ/T})ⁿ（`r_pow` 几何幂）。

〔构造强度：序档（同定理 5.4）；req 对位（`rsq_bounded_softmax_tv_contraction`/`rsq_bounded_softmax_tv_iter`）；Real 层复刻已并入模块化树（模块化树（补充材料 S2） 1,986 行，定理 5.10）——档位定义见 §9.3〕

**定理 5.6a**（`real_sqrt_exists`，Real 层）：任意非负实数的构造性平方根——
```
forall d : Real, real_le real_zero d -> sigT (fun r => And (real_le real_zero r) (real_eq (real_mult r r) d))
```
非平方 d 一并覆盖（正支 r := exp(½·log d)，零支 r := 0）——§5.4(c) 的 √d 构造组件。

〔构造强度：严格见证形——sigT 显式见证构造，构造性正例（非不可证面）——档位定义见 §9.3〕

**定理 5.6b**（`real_expf_realizable`，Real 层由具体实例满足）：expf 迷你接口全部字段在 `cauchy_real_exp` 上可满足（sigT + And）——定理 5.5/5.6 的接口前件在具体柯西实数上非空。

〔构造强度注记：定理 5.6b 为接口可实现性引理，不涉及序强度档位；其验证状态为已通过四项验证，见补充材料 S3。〕

**定理 5.6c**（`real_scale_temp_duality`，模块 `UpDebtDual`）：缩放-温度对偶的 Real 层复刻（§5.4(c) 第 5 条）——∀ c > 0：`real_softmax_scaled (real_inv_pos c Hc) z s == real_softmax_temp_param c Hc z s`（柯西实数层逐点 real_eq；自含定义族 `real_softmax_scaled`、正性件 `real_softmax_scaled_pos`、归一化件 `real_softmax_scaled_normalized`、`real_softmax_temp_param`）。

〔构造强度：等式档——Real 层复刻，逐点 `real_eq` 相等；req 伴件（`ag_temp_is_scale_duality`）——档位定义见 §9.3〕

**定理 5.6d**（`sqrt_witness_exists_abstract`，模块 `UpDebtSqrtAbs`）：抽象 Id 层任意非负 d 的平方根见证实例化——与 `real_sqrt_exists`（定理 5.6a，Real 层）合成 √d 构造的两层闭合（§5.4(c) 注记的依据）。

〔构造强度：严格见证形——抽象 Id 层 sigT 见证实例化，与定理 5.6a 合成两层闭合——档位定义见 §9.3〕

**定理 5.7**（`real_cauchy_schwarz` / `real_cauchy_schwarz_lt` / `real_cauchy_schwarz_reversed_false`，模块 `UpCS`）：有限和 Cauchy–Schwarz 的 Real 层逐 eps 形态——
```
forall (a b : list Real) (eps : Real), real_lt real_zero eps ->
  real_le (real_mult (dotp a b) (dotp a b))
          (real_plus (real_mult (sql a) (sql b)) eps).
```
严格版 `real_cauchy_schwarz_lt`（eps > 0 ⟹ Or 形严格不等式）为核心，平方形态为其直接后承；该严格形即 Bishop 序谓词 `real_le_b`（∀eps>0, x<y+eps）的展开本身——C-S 的 Bishop 形对照零换形成本可得（`UpRealLeB.v` 判定 1 谓词定义）；le 形（`real_cauchy_schwarz`）为其 Or 左支注入。同模块并以 `real_cauchy_schwarz_reversed_false` 把「反向不等式」形式化为**假命题**（构造性 Or 语义的反例陈述）——该方向勘误本身构成 C-S 陈述方向敏感性的机器检查注记。

〔构造强度：第三档逐 eps 形＋反例档——Real 层逐 eps 直证；反向不等式以构造性反例形式化为假命题（陈述方向敏感性）；第二档 Bishop 形对照零换形可得——档位定义见 §9.3〕

**定理 5.8**（`qk_logits_bounded`，模块 `UpQKBound`；前置 `inner_sq_norm`、`real_logit_bound_of_norm_bounds`）：Q/K 一致范数界到注意力双界 logits 的显式转化——
```
forall (k : nat) (Qb Kb : Q) (vq vk : nat -> list Real) …,
  (forall s : nat, real_le (root_of (sql (vq s)) (Hvsq s)) (real_const Qb)) ->
  (forall s : nat, real_le (root_of (sql (vk s)) (Hksq s)) (real_const Kb)) ->
  And (real_lt real_zero (Delta k Qb Kb))
      (forall s s' : nat, real_le (real_abs (attn_logit k (vq s) (vk s'))) (Delta k Qb Kb)).
```
即在每个查询的范数根 `‖q_s‖ := root_of(⟨q_s,q_s⟩)` 与 `‖k_s‖` 分别被常数 Qb/Kb 控制的前提下，构造出显式 Δ > 0 使 `|⟨q_s,k_{s'}⟩·w| ≤ Δ`（`w` 为 √d 缩放的根式系数）。

〔构造强度：前提显式化档——显式界与根有界前提（构造性理由见 §5.5 注记）；Real 层直证——档位定义见 §9.3〕

> **注记（根有界前提形态）**：前提取「根有界」形态——对每个查询直接陈述 `root_of(⟨q_s,q_s⟩) ≤ Qb`，而非平方形态 `⟨q_s,q_s⟩ ≤ Qb²`。这不是妥协而是构造性语义的忠实化：由 `A² ≤ Q²` 与 `A, Q ≥ 0` 构造性地推不出 `A ≤ Q`（Or 编码的 `real_le` 既造不出 `lt` 支的持续间隙见证，也造不出 `eq` 支；`real_weak_trich` 仅以双否定形式给出相等、不是三分）——Or 编码使范数界（而非平方范数界）成为正确原语。根总是可取的（`real_sqrt_exists`，定理 5.6a），故该前提非空。

**定理 5.9**（`attention_iterate_converges_real`，模块 `UpArchAttn`）：§4.6 稳态侧的 Real 镜像——几何衰减序列的迭代收敛（sigT N 见证，∀eps>0 存在 N，n ≥ N ⟹ 距离 < eps），消费 `r_arch_pow_attn_real`（几何幂预算件）。steady_state 一族的 Real 承载由此补齐一行（附录 B）。

〔构造强度：严格见证形——∃N ∀n≥N 量词翻转的 sigT 见证构造——档位定义见 §9.3〕

**定理 5.10**（`tv_doeblin_contraction` / `tv_doeblin_iter`，**模块化树（补充材料 S2），在树**）：定理 5.4 双点收缩的 Real 层复刻——list 离散世界（real_list_sum）下的 `TV(step μ, step ν) ≤ (1−δ)·TV(μ,ν)` 与几何率 (1−δ)ⁿ；δ 为 Section Variable（接口形态），显式前件仅 `abs_sum_le_list` 一条，δ=1 退化支构造性处理。**载体状态（2026-09-11 核验更新）**：本模块原为 attn 工作区独立存档件（`UpTVReal.v`，1,518 行，未入树、不构成复现入口），现以**树兼容重建件**形态并入模块化树——模块化树（补充材料 S2）（1,986 行；头注自证蓝本即该存档件、Require 仅基座与 Stdlib List/QArith.Qring；全文 0 Admitted；两定理现位于该模块 L884/L1564，经实测核对）。且其 Part 2 已把「显式 δ\* := e^{−2γ/T} 接入该 δ 接口」的实例闭合（γ 即正文的双界半宽 Δ：`tvd_dstar_instance` 打包「δ 接口字段面被显式常数满足」（0 < δ\* ≤ 1、δ\*·U ≤ K 逐点、行归一化），`tvd_dstar_iter_contraction` 给出显式率迭代收缩；经实测核对）；「范数界 → 双界 logits → 显式率」尚余 `UpQKBound`（现 G10）与 `UpTVDoeblin` 两件的模块级组合证明尚未完成、未并为单一定理形态（§10.2 第 2 项）；双点族的 setoid 迁移仍开放（库内无 req/setoid 对应件，经检索实证）。〔2026-09-12 核验：eps 余量伴随件已组装——模块 `UpReqTVAbsEps`（Or 形精确前提的构造性必要性已证）。〕

---

## 6 KV 缓存逐出：稳态偏差的三角不等式上界

本节 Set 层定理的数学内容是 `abs_sum_le`（`|Σ a_i| ≤ Σ|a_i|`）的一次实例化——`db_breaking` 的定义本身就是逐对差的绝对值，故本节标题为「三角不等式上界」。该结构界**不**声称关于「逐出 k 个 token 会导致多少偏差」的非平凡信息；`db_breaking` 与逐出集大小、温度、能量 Lipschitz 常数的**定量联系已由 Real 层定理 6.1b/6.1c 闭合**（§6.2.1）。库内进一步证明了一个更强的结构性事实：在库内逐出核的定义形态下 `db_breaking` **恒等于零**（定理 6.2，§6.2.2）——涨落-耗散型上界假设整体多余，截断核的稳态保持可从破缺恒为零直接读出；逐出核与完整核迭代偏差的有限 n 漂移界亦已闭合（定理 6.3）。分量归属上，本章的定量内核由 Real 层定理 6.1b/6.1c（§6.2.1）与定理 6.2/6.3（§6.2.2）承载，定理 6.1 的三角不等式记账为该内核的结构性前奏。

---

### 6.1 背景

大型语言模型推理时，KV 缓存容量有限。当缓存满时需逐出部分 token 的 key/value 对。逐出破坏了完整 Boltzmann 分布，导致注意力稳态方程偏离。**既有工作以经验启发式与系统优化为主**：以累积注意力得分为准则的逐出（H2O[11]）、依「重要性持久性」假设的一次性选择（Scissorhands[37]）、保留首段「注意力汇」token 加滑窗的流式方案（StreamingLLM[36]）等，系统的算法—系统分类见综述[35]；这些工作亦观察到 token 移除会扭曲底层 softmax 分布（Keyformer 一线，见[35]）。本节**不提出新的逐出策略**，而是在给定逐出核下刻画该偏离的**上界结构**：Set 层主体是偏差的三角不等式记账（定理 6.1），与温度、能量界、Lipschitz 常数的显式定量联系由 Real 层定理 6.1b/6.1c 承载（§6.2.1）；本文的增量在于把这些界做成机器检查在库定理（含免平稳约束的可行性与破缺恒为零的精确式），而非经验有效性评估。

### 6.2 逐出稳态偏差

定义逐出后的 Boltzmann 分布 `evicted_boltzmann` 与转移核 `evicted_transition`。逐出破缺项 `db_breaking` 度量逐出导致的局部详细平衡破坏逐出破缺项定义为逐对差的绝对值：`db_breaking(s,s’) := |p_ev(s’)·T_ev(s’,s) − p_ev(s)·T_ev(s,s’)|`，其中 `p_ev` 为逐出后 Boltzmann 分布、`T_ev` 为逐出后转移核。完整定义见附录 A（`db_breaking` 行），Coq 语句见补充材料 S1。

定理 6.1 的准确定位是**偏差恒等式/上界的形式化**，其数学内容等价于 `abs_sum_le`（绝对值求和引理）的一次应用；它不提供关于「逐出 k 个 token 会导致多少偏差」的可计算估计。库内另声明了 `fluctuation_dissipation_bound`（Variable）作为 `db_breaking` 的独立上界假设（界为 |energy s|·(|energy s'|+1) 的显式形态）；`eviction_db_breaking_bound` 是该假设下的条件化推论——该假设现被证明**整体多余**：`db_breaking` 在库内逐出核形态下恒为零（定理 6.2，§6.2.2），故 §6.2.1 的 Real 层定量界与该恒等式分别给出「上界化」与「精确归零」两个层次的刻画。

**定理 6.1**（`eviction_steady_deviation`）：对任意状态 `s`，
```
le (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
              (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
   (sum_over_S (fun s' => db_breaking s s')).
```

**证明概要**：
1. 将左侧差改写为 `Σ_s' [ev_b(s')·ev_t(s',s) − ev_b(s)·ev_t(s,s')]`；
2. 利用 `abs_sum_le` 将绝对值移入求和；
3. 证明每一项绝对值等于 `db_breaking s s'`。

该定理表明：逐出导致的稳态破坏程度被所有局部破缺项之和所控制。

### 6.2.1 db_breaking 的温度-Lipschitz 定量界

本节给出 `db_breaking` 与温度、能量 Lipschitz 常数、度量的显式定量联系（Real 层，24 个引理，零 `Admitted`、零全局公理，纯构造性；显式前件全部可实例化）：

- **能量 Lipschitz** `real_energy_lipschitz`：`|e(s) − e(s')| ≤ L·metric(s,s')`；
- **能量下界** `real_energy_lower`：`−E_max ≤ e(s)`（e^{−v} 有界的温度侧来源）；
- **无向核** `real_transition_sym`：`T(s,s') == T(s',s)`（转移非负 `real_transition_nonneg` 为马尔可夫核标准性质）。

**定理 6.1b**（Real 层，`real_boltzmann_diff_bound`）：Boltzmann 因子差受温度-能量界-Lipschitz 控制。该定理对两个相互独立的自由余量 `eps`、`eps'` 作全称量化（`forall (s s' : S) (eps eps' : Real), real_lt real_zero eps -> real_lt real_zero eps' -> …`，Coq 陈述）：
```
∀ eps > 0, ∀ eps' > 0 :
|b(s) − b(s')| ≤ e^{E_max/D}·(L/D)·metric(s,s')·e^{(L/D)·metric(s,s')} + e^{E_max/D}·eps + eps'
```

**定理 6.1c**（Real 层，`real_db_breaking_bound_eps`）：逐出破缺的完整定量界（保留对 (s,s')，前提 `keep s`、`keep s'`）——同一双量化形态：
```
∀ eps > 0, ∀ eps' > 0 :
db_breaking(s,s') ≤ inv Z_ev · T(s,s') · [e^{E_max/D}·(L/D)·metric(s,s')·e^{(L/D)·metric(s,s')} + e^{E_max/D}·eps + eps']
```

**显式假设（`Z_ev` 下界）**：定理 6.1c 的界含 `inv Z_ev`（逐出后配分函数的逆元），其定量非退化要求 `Z_ev` 有正下界——现显式声明：**保留集非空，且至少含一个具有正 Boltzmann 权重的状态**（§6.3 的单调性论证隐含该假设，现显式化；若 `Z_ev` 可任意小，此界在定量意义上退化）。

**为何需要两个独立 eps**：`eps` 与 `eps'` 属于**两条不同的收敛/误差通道**，不是同一度量的两个副本。证明链中第一个 eps 断言是 exp 差界 `real_exp_neg_diff_bound`（`|e^{−u} − e^{−v}| ≤ e^{−v}·(|u−v|·e^{|u−v|} + eps)`，其自身对 eps 全称量化）；第二个 eps 断言是乘积组装界 `real_abs_diff_prod_bound`（`|u−v|·e^{|u−v|} ≤ U·e^U + eps'`，对 eps' 全称量化）。两个引理各自携带一个余量，串联后 eps 经 Boltzmann 上界因子 e^{E_max/D} 缩放进入最终界，eps' 以加性形式进入，二者在证明链的不同环节出现、彼此无任何代数关系，故必须分别量化。这是构造性分析中「每个逐 eps 断言一个余量」的常规惯例在两步传递下的自然结果，并非可消除的非最优步骤——若把二者合并为单一 eps，需要在中间传递处重新引入等价的余量分裂，陈述不变得更简单。排版上，二式的完整量词前缀如上，正文中 `eps`、`eps'` 不再作为自由变量出现。

即 `db_breaking` 与**温度 D（倒数）、能量界 E_max、能量 Lipschitz 常数 L、度量 metric 显式挂钩**。证明链：exp 差界 `real_exp_neg_diff_bound` → 结构分解（逐出分支归零 `real_db_breaking_evicted_l`/`real_db_breaking_evicted_r`；保留分支提因子 `real_db_breaking_kept_final` 给出 `db == invZ_ev·T·|b−b'|`）→ 分析组装（Lipschitz 缩放 `real_energy_lipschitz_scaled`、温度上界 `real_boltzmann_upper`、乘积界 `real_abs_diff_prod_bound`）→ 最终界 `real_db_breaking_bound_eps`。

**构造性强度说明**（逐 eps 余量形，定义见 §1.2）：两件（定理 6.1b/6.1c）的逐 eps 结论属多 eps 前提组合／复合 D 形（eps/eps' 双通道、`inv Z_ev·T·(exp·(eps+eps'))` 复合系数）——Bishop 形可升格但证书链长（inv_pos 证书＋exp 正性＋逐 eps 面拆分），库内盘点判为**未建置（可升格的开放项，非阻塞）**（盘点记录 #32，见补充材料 S3；`UpRealLeB.v` 尾注结论 9(e)/(f) 同型口径）；其余 plain-eps 族已由 `real_le_closure_b_one` 统一闭合。

**前提满足性的工程论证**：定理 6.1b/6.1c 的三个显式前提（`real_energy_lipschitz`/`real_energy_lower`/`real_transition_sym`，Section `RealKVQuantMain` 变量声明，CW219 L53956/L53960/L53943）在 KV 逐出场景中的满足性可按如下工程层面论证。其一（能量 Lipschitz 与能量下界）：当能量由有界 logits 承载（e(s) := −z(s)）且 logits 处于 §5.5 定理 5.8 的双界 −Δ ≤ z ≤ Δ 内（Q/K 范数界经 `qk_logits_bounded` 显式转化），E_max 与 Lipschitz 常数均可取显式值（E_max := Δ；Lipschitz 常数在离散度量的归一化实例化下可取显式值，|e(s) − e(s')| ≤ 2Δ）——适用限制：energy/logits 的具体绑定（query-key 点积）本身仍是 §9.2 边界 3 的开放末端一步，故本论证给出的是「绑定闭合后前提显式满足」的形态，不是绑定本身的证明。其二（无向核）：对称核前提刻画的是无向注意力场景（双向编码、相似度核等对称打分场景；库内该变量声明处以 KV 缓存/相似度核为诚实假设语境）；解码器 KV 逐出的因果（有向）核不满足对称性，该场景不走定理 6.1b/6.1c，而由定理 6.3 的有限 n 漂移界承载——`kv_drift_bound`（模块 `UpKVDrift`，L2161）不要求核对称，其控制量行 TV 的显式式 `kev_row_tv_one_minus_Z`（同模块，L1035：tv_row == 2·(1 − Z_keep)）只用保留配分正性（`kv_Z_keep_pos`，同模块，L127）。其三（`Z_ev` 正下界）：上文显式声明的保留集条件在「保留头部」语义的逐出策略下成立——保留最大概率 token 的策略（如 Min-P 的 `pick_max_token_minp_keep`，CW219 L30954；Top-k 的前缀保留）使逐出后配分函数以被保留的最大 token 的 Boltzmann 因子为下界（Boltzmann 因子恒正，`boltzmann_factor_pos`，CW219 L1628），非退化性由策略的保留语义保证而非附加假设。

### 6.2.2 破缺恒为零与逐出漂移界

本小节汇总模块化树内闭合的两件 KV 逐出结果（模块 `UpEvictId` 与 `UpKVDrift`，均为独立编译单元）。

**定理 6.2**（`eviction_db_breaking_zero`，模块 `UpEvictId`）：在库内逐出核（保留集上按 `inv(Z_keep)` 重归一化、逐出处置零）的定义形态下，破缺项恒为零：
```
Theorem eviction_db_breaking_zero :
  forall s s' : S, Id (db_breaking s s') zero.
```
即逐对详细平衡在逐出后的核上**精确保持**——定理 6.1 的三角不等式上界右侧为 0，稳态偏差结构归零。同模块给出截断核稳态方程的精确式 `evicted_boltzmann_steady_exact`（截断 Boltzmann 分布满足逐出核的稳态方程）与配分增量恒等 `eviction_partition_increment`。据此，§6.2 中 `fluctuation_dissipation_bound` 的独立上界假设整体多余（其主定理 6.1 的右侧恒为零，任何非平凡上界假设均不再需要）；定理 6.1 的定位相应为「破缺恒为零 ⟹ 截断核稳态保持」的正结果，Real 层定理 6.1b/6.1c 的定量界则刻画保留分支的逐对代数（其结构性内容与恒零结果一致：逐出分支已归零，见 §6.2.1 证明链的 `real_db_breaking_evicted_l/_r`）。

**定理 6.3**（`kv_drift_bound` / `kv_drift_bound_tv`，模块 `UpKVDrift`）：逐出核与完整核迭代偏差的**有限 n 漂移界**——在一致行误差常数前提下（Section 前提 `Hrow : forall s, real_le (tv_row s) c`，c 为 Section Variable；μ 归一化、非负，eps > 0）：
```
Theorem kv_drift_bound : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_le (Ddist (kev_iter n mu) (k_iter n mu))
          (real_plus (real_mult (real_of_nat n) c) eps).
```
即 TV 距离（Ddist）≤ n·c + eps 对一切有限 n 成立；**构造性强度说明**（逐 eps 余量形，定义见 §1.2）：本模块右端为 plain-eps 字面且与 `UpRealLeB.v` 同基座（CW219），属闭包器单步直连同型——可升格未建，登记开放项。`kv_drift_bound_tv` 给出 inv2 折叠的同构形态（≤ (n·c + eps)/2）。控制量取**行 TV**（`tv_row`，由 `Z_keep_pos`（保留配分正性）与行 TV 精确式 `kev_row_tv_exact`、`kev_row_tv_bound`、`kev_row_tv_one_minus_Z`（tv_row == 2·(1 − Z_keep)）逐行控制——未使用 §6.2 中恒为零的 `db_breaking` 作为控制量），与逐出「控制行逐出质量」的工程语义一致。

> **遍历性口径（红线）**：定理 6.3 是 **∀n 有限 n** 的漂移界陈述，前提显式（一致行误差常数 c）；本文不主张任何遍历性、稳态分布存在性或 n→∞ 极限下的分布收敛——生成序列的渐近性质维持 §9.2 边界 7 的不主张立场，该有限 n 界是朝向它的第一个定量步。

### 6.3 分区函数单调性

**定理 6.4**（`eviction_partition_monotone`）：保留集扩张时，保留分区函数单调不减。

**定理 6.5**（`eviction_partition_le_full`）：保留分区函数不超过完整配分函数。

这些定理为“保留越多、损失越少”提供了定量基础。

---

## 7 Top-k 截断的主化最优性

本节的 Top-k 引理（`top_k_majorization`（L30047）、`top_k_swap_no_gain`（L30073）、`top_k_majorization_mem`（L30264）、`top_k_tail_bound`（L29719）、`tail_plus_kept_full`（L29732））同时是 §8 Min-P 截断的对照基准。

### 7.1 背景

Top-k 截断只保留注意力权重最大的 k 个状态。我们需要证明：在所有大小为 k 的保留集中，保留 Boltzmann 权重最大的 k 个状态使尾部质量（信息损失）最小。

### 7.2 支配性定理

定义 `keep_top_k s` 为“s 的 Boltzmann 权重属于前 k 大”。

**定理 7.1**（`top_k_majorization`, L30047）：若 `keep_top_k s1` 且 `¬keep_top_k s2`，则
```
le (boltzmann_factor s2) (boltzmann_factor s1).
```

**证明概要**：使用计数函数 `count_heavier` 对状态排序。若 `s2` 比 `s1` 重，则 `s2` 的“比它重的状态数”严格小于 `s1`；但 `s1` 在前 k 而 `s2` 不在，导致计数矛盾（`lia`）。

**定理 7.1a**（`real_top_k_majorization`, L43485）：Top-k 支配性的 **Real 层复刻**——柯西实数层（RealTopKMain Section）：
```
real_keep_top_k s1 -> Not (real_keep_top_k s2) ->
real_le (real_boltzmann_factor_ s2) (real_boltzmann_factor_ s1).
```
即 `keep_top_k s1 ∧ ¬keep_top_k s2 ⟹ f s2 ≤ f s1`——Top-k 保留者权重 ≥ 逐出者权重（最重 K 个的序刻画），抽象层定理 7.1 的 Real 值域版。

**证明概要**：`real_le_dec` 分叉 → 反证（`real_not_le_lt` 线序接口 ⟹ `lt (f s1) (f s2)`）→ 计数单调（`real_count_heavier_succ_le`）→ keep/drop 计数矛盾（`NatLt` 双向 + `Nat.ltb` 转换 + `lia`）。显式前件（零公理）：`real_le_dec`（线序判定）+ `real_not_le_lt`（`Not(le) ⟹ lt` 反向——`real_weak_trich` 仅弱三分，构造性边界）+ 计数接口（count/单调/keep 双向 `And`）。

### 7.3 交换不获益

**定理 7.2**（`top_k_swap_no_gain`, L30073）：对任意保留态 `s` 与逐出态 `s'`，
```
le tail_mass (plus (minus tail_mass (boltzmann_factor s')) (boltzmann_factor s)).
```

**证明概要**：由 `top_k_majorization` 得 `boltzmann_factor s' ≤ boltzmann_factor s`，即“重换出、轻换入”不会减少尾部质量，等价于 top-k 是最小信息损失选择。

### 7.4 排序级支配性

**定理 7.3**（`top_k_majorization_mem`, L30264）：若 `s1 ∈ select_top_k S_enum K` 且 `s2 ∉ select_top_k S_enum K`，则
```
le (boltzmann_factor s2) (boltzmann_factor s1).
```

**证明概要**：`select_top_k` 通过 `sort_weight` 将状态按 Boltzmann 权重降序排列后取前 k 个；`firstn_head_dominates_skipn` 证明排序列表中前缀元素支配后缀元素。

### 7.5 容量预算与尾部质量

**定理 7.4**（`top_k_tail_bound`, L29719）：尾部质量不超过完整配分函数，即
```
le tail_mass Z_thermo.
```

**定理 7.5**（`tail_plus_kept_full`, L29732）：尾部质量与保留质量之和等于完整质量，即
```
Id (plus tail_mass evicted_partition) Z_thermo.
```

这两个定理将 top-k 截断的信息损失与容量预算显式关联：保留集越大，尾部质量越小；全部质量守恒。

**定理 7.6**（`topk_tv_identity_strict`, L30638）：**Top-k 截断的总变差定量界**——在严格逐出前提（`lt (inv Z_thermo) (inv Z_keep)`，Real 层由尾部质量 T > 0 实例化）下，softmax/Boltzmann 分布与 Top-k 重归一化分布的总变差距离精确等于归一化尾部质量：
```
lt (inv_pos Z_thermo Z_thermo_pos) (inv_pos topk_kept_partition topk_kept_partition_pos) ->
Id (tv_dist boltzmann_dist_attn topk_renorm)
   (mult (inv_pos Z_thermo Z_thermo_pos) topk_tail_mass).
```
即 `TV(boltzmann, topk_renorm) == tail_mass / Z_thermo`。

〔构造强度：等式档——精确恒等式，不涉序档位；严格逐出前提为严格见证形亲缘；Id 层已是 list 具体世界；Real 层独立复刻已交付（`rtk_tv_identity_strict`，模块 `UpReqTopKTVChain` L967，19 引理链 Real 层全平移；2026-09-12 措辞更新核验）；req 对位（`ag_topk_tv_identity_strict`）——档位定义见 §9.3〕

**与截断采样理论先例的对照定位**：Hewitt et al. (2022)[20] 给出截断 = 去平滑的一般刻画，Meister et al. (2023)[21] 给出软截断的信息论框架；本定理的增量是对同一类对象给出**机器检查的精确恒等**（含条件化前提的显式化与 19 引理组装），与二者互补（§2.3）。

**证明概要**（19 引理四段组装，零新增公理）：① 逐点差分解：`|b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z)`（提公因子 `mult_minus_distr_r` 反向 + `abs_mult` + `|b| == b` + 符号经显式 `lt` 前提的 `abs_neg_cc`/`lt_minus_cc` 消去）；② 求和分解：`Σ (if keep then b·D else b/Z) == kept·D + invZ·T`（`topk_if_split` + `eviction_if_linear`/`_else` + `sum_over_S_linear`）；③ 守恒闭合：`kept + T == Z`（`topk_kept_plus_tail_full`）⟹ `1 − kept·invZ == invZ·T` ⟹ 总和 `== 2·invZ·T`；④ TV 归一化：`inv_two·(2·X) == X`。**构造性边界**：抽象层 `le`/`lt` 是 Class 字段（Set 非归纳）不可析取，符号消去只能走显式 `lt` 前提（条件定理模式）——这是“Real 层无 0 ≤ |a| 判定”（构造性边界）的抽象层形态，Real 层实例化后为无条件定理。

---

## 8 Min-P 截断采样的形式化

§7 的 Top-k 与本节的 Min-P 是对 §5 attention-Gibbs 桥所确定的 softmax/Boltzmann 分布的两种截断近似：Top-k 按绝对排名保留 k 个 token，Min-P 按相对阈值保留、其余置零后重归一化。

### 8.1 背景

Top-k 截断按**绝对排名**保留 k 个 token；Min-P 截断按**相对阈值**保留概率不低于 `min_p × max_prob` 的 token，其余置零后重归一化。两者都是对 Boltzmann/Gibbs 分布的截断近似，但 Min-P 的保留集随分布形状自适应变化。

### 8.2 定义

Min-P 保留判定为 `minp_keep(prefix,w) := kernel(prefix,w) ≥ min_p · max_{w’} kernel(prefix,w’)`（`min_p ∈ (0,1)` 为相对阈值超参）；Min-P 核对保留者按截断和重归一化、对逐出者置零：保留者 `minp_markov_kernel(prefix,w) = kernel(prefix,w) / Σ_{w’ 保留} kernel(prefix,w’)`，逐出者取 0。完整定义见附录 A（`minp_keep` 等行），Coq 语句见补充材料 S1。

### 8.3 可判定性与非空性

**引理 8.1**（`minp_keep_dec`, L30933，定义型判定函数）：`minp_keep prefix w` 是构造性可判定的。

**证明概要**：`minp_keep` 是 `le` 关系；`ord_le_dec` 提供可判定序判定。

**引理 8.2**（`pick_max_token_minp_keep`, L30954）：最大概率 token 总是满足 Min-P 条件。

**证明概要**：`min_p < 1` 且 `max_markov_prob > 0`，故 `min_p · max_markov_prob ≤ max_markov_prob`。

**引理 8.3**（`minp_temp_sum_pos`, L30981）：`minp_temp_sum prefix > 0`。

**证明概要**：`pick_max_token` 被保留且其 `temp_factor > 0`（`exp_neg_pos`），故子集和为正。

### 8.4 核性质

**定理 8.4**（`minp_markov_kernel_nonneg`, L31022）：对任意 `prefix, w`，`minp_markov_kernel prefix w` 要么等于 0，要么大于 0。

〔构造强度：等式/序档——枚举世界上的析取结论；Real 层归一化承载见定理 8.5a——档位定义见 §9.3〕

**定理 8.5**（`minp_markov_kernel_normalized`, L31050）：对任意 `prefix`，

```
Σ_{w ∈ vocab} minp_markov_kernel prefix w == 1.
```

〔构造强度：等式档（归一化恒等）；Real 层复刻＝定理 8.5a——档位定义见 §9.3〕

**证明概要**：将求和中的公共归一化因子 `inv(minp_temp_sum)` 提取到求和之外（`list_sum_linear`）；剩余部分按定义等于 `minp_temp_sum`；由 `inv_pos_correct` 得 `inv(Z)·Z == 1`。

**定理 8.5a**（`real_minp_markov_kernel_normalized`, L43392）：Min-P 核归一化的 **Real 层复刻**——柯西实数层（RealMinPMain Section）：
```
real_eq (real_list_sum Token (fun w => real_minp_markov_kernel prefix w) vocab) real_one.
```
即 `Σ_w minp_kernel(prefix,w) == 1`（概率守恒）——抽象层定理 8.5 的 Real 值域版。

〔构造强度：等式档——Real 层复刻（归一化恒等，逐点 `real_eq`）；Bishop 形投影件见 §8.7——档位定义见 §9.3〕

**证明概要**：逐点分支交换（keep 分支 `real_mult_comm` / drop 分支 `real_mult_zero` 反向）→ 标量线性提取 inv(temp_sum)（`real_list_sum_linear`）→ temp_sum 定义性换形 → `inv(temp_sum)·temp_sum == 1`（`real_mult_comm` + `real_inv_pos_correct`）完成证明。显式前件（零公理）：`real_minp_keep_dec`（Set 层 `Or` 判定）+ `real_minp_temp_sum_pos`（保留集非空 + 因子正）+ 环境。

### 8.5 与完整 softmax 核的单调性比较

本小节给出 Min-P 核与完整 softmax 核之间的**单调性比较**，以及截断质量的定量估计（截断质量与词表大小的量级关联见定理 8.9 `minp_dropped_mass_le_inv_vocab_size`；Top-k 截断的总变差定量见定理 7.6 `topk_tv_identity_strict`；与熵的量级关联已在模块化树内机器检查闭合（`dropped ≤ 1 − e^{−S}`，模块 `UpMinP`），见下文注与 §10.2 第 5 项）。

**引理 8.6**（`minp_temp_sum_le_partition`, L31112）：`minp_temp_sum prefix ≤ partition_temp prefix`。

**证明概要**：保留 token 的 `temp_factor` 之和不超过完整词表的 `temp_factor` 之和；对逐出 token，其 `temp_factor > 0` 但贡献为 0，因此 LHS ≤ RHS。

**定理 8.7**（`minp_markov_kernel_keep_ge_full`, L31127）：若 `minp_keep prefix w`，则

```
le (markov_kernel prefix w) (minp_markov_kernel prefix w).
```

**证明概要**：保留者 Min-P 核为 `temp_factor·inv(minp_sum)`，完整核为 `temp_factor·inv(partition)`。由 `minp_sum ≤ partition` 及 `inv_pos_le_compat`（`a ≤ b ⟹ inv b ≤ inv a`，字段归属 `RealInterfaceEnhanced`，L249）得 `inv(partition) ≤ inv(minp_sum)`，再乘以正的 `temp_factor` 即得。

**引理 8.8**（`minp_markov_kernel_dropped_zero`, L31147）：若 `¬minp_keep prefix w`，则 `minp_markov_kernel prefix w == 0`。

**定理 8.9**（`minp_dropped_mass_le_inv_vocab_size`, L31849）：**Min-P 截断质量与词表大小挂钩**——截断质量不超过词表大小倒数：
```
le (minp_dropped_mass prefix)
   (minus one (inv_pos (mp_of_nat (length vocab))
                       (mp_of_nat_pos vocab vocab_nonempty))).
```
即 `dropped mass ≤ 1 − 1/|S|`（|S| 为词表大小）。

〔构造强度：序档（Id 层 `le` 语法）——词表界为熵刻画的推论（熵刻画带严格见证形亲缘）；req 单调件面（`req_minp_keep_p_antitone` 等四件）；Real 层投影族已完成 Bishop 形升格（`real_minp_projection_eps_B`/`_tail_nonneg_B`/`_B_split`）——档位定义见 §9.3〕

**证明概要**（13 引理链，零新增假设）：① `p_max ≥ 1/|S|`：完整核归一化 `Σ kernel == 1`（`markov_kernel_normalized_mp`）→ 逐项 `kernel w ≤ p_max`（`argmin_aux_token_min_mp` 遍历最小性重述 + `temp_factor_antitone_mp` + `pick_best_optimal_mp` → `markov_kernel_le_max_mp`）→ 和 ≤ 势·最大（`list_sum_le_const_mp`）→ 除以正数（`le_one_mult_le_inv_mp`）⟹ `minp_max_ge_inv_vocab_size`；② `dropped ≤ 1 − p_max`（`minp_dropped_mass_le_one_minus_max`）→ 平移（`opp_le_compat` + `le_plus_compat`）。`mp_of_nat` 为 Section 内自包含计数（防全局重名）。

**熵刻画注记（模块化树内机器检查件）**：上述词表大小上界可视为下述更强熵界在 `S ≤ log|S|` 下的推论——模块 `UpMinP`（模块化树 + Extensions + 单文件三形态均已具备）已机器检查：(i) **熵刻画** `entropy_ge_neg_log_p_max`（L728：S ≥ −log p_max）与 `dropped_le_one_minus_exp_neg_S`（L830，逐字语句）：
```
Theorem dropped_le_one_minus_exp_neg_S :
  real_le um_dropped
          (real_plus real_one (real_opp (real_exp_neg um_entropy))).
```
即 `dropped ≤ 1 − e^{−S}`，S := Σ_w k_w·(−log k_w) 为截断前缀的 list 熵（k_w 为完整 markov 核）；(ii) **定理 8.9 降为推论**——`dropped_le_one_minus_inv_n`（L895）：由 `S ≤ log|S|`（Gibbs 不等式于均匀分布）得 `dropped ≤ 1 − 1/|S|`，定理 8.9 的同语句作为该熵界的推论重证。**锐度单调解读**：熵刻画同时给出 min-P 可用性随分布尖锐度的自动改善——分布越尖锐（熵 S 越小），界 `dropped ≤ 1 − e^{−S}` 越紧（S → 0 时 dropped → 0，低熵分布下有实质约束力）；在高熵端该界退化为词表界 `1 − 1/|S|`。该熵界的早期独立验证件形态已由模块 `UpMinP` 取代（旧件不再使用）；审计侧复合的现状见 §8.7（KL(minp‖full) == −log Z_aud 已闭合；KL ≤ S 的复合熵链已由模块 `UpReqMinPKLChain` 拼装闭合，2026-09-12 核验）。现状见 §10.2 第 5 项。

### 8.6 前提（Variable）清单与封装状态

Min-P 部分全部前提显式声明如下（`min_p`/`min_p_pos`/`min_p_lt_one` 三者连续声明于 `Section MinPSampling`）：

| 假设 | 文模块行号 | 数学含义 |
|---|---|---|
| `min_p` | L30870 | Min-P 阈值超参 |
| `min_p_pos` | L30871 | `min_p > 0` |
| `min_p_lt_one` | L30872 | `min_p < 1` |
| `temperature` / `temperature_pos` | L30696 / L30697 | 温度为正 |
| `vocab_nonempty` | L30693 | 词表非空 |
| `token_eq_dec` | L30694 | token 相等可判定 |
| `exp_neg_pos` | L182（字段归属 `RealInterface`，Class 声明于 L133） | `exp_neg x > 0` |
| `inv_pos_le_compat` | L249（字段归属 `RealInterfaceEnhanced`，Class 声明于 L217） | `a ≤ b ⟹ inv b ≤ inv a`（0 < a, 0 < b） |

这些假设以 Class + `Context` 机制封装为定理的显式前件：`End Section` 后 Coq 对 `RI` 与 `DO`（`DecidableOrder RI`）自动泛化，全部 Min-P 定理形如

```
forall {RI : RealInterfaceEnhanced} {DO : DecidableOrder RI}, <结论>
```

实证：Rocq 9.0 `Print Assumptions minp_markov_kernel_normalized` 返回 **`Closed under the global context`**。实例化全貌见 §9.2：代码库已为具体 `Real` 装配含全部超越函数字段的 Setoid 完整版实例（`Real_RealInterfaceSetoid`（L39407）与 `RealEnhancedReal`（L41115）），并另有 Real 层逐 eps 定理承载核心结论（见 §9.2 与附录 B）。

### 8.7 Min-P 的 KL 投影解释：Real 层实例族

§5.3 同源的「KL 投影解释」结构在 Min-P 截断对象上获得 Real 层实例族——模块 `UpAuditBridge`（1,122 行，模块化树 + Extensions + 单文件三形态均已具备）把「Min-P 截断核 == 到通过集的 KL 投影」从恒等式层面机器检查为七件：

1. **投影桥** `real_minp_kernel_is_projection`（L566）：`minp_markov_kernel` 的 Real 形态逐点等于到通过集的投影核（real_eq 逐点）；
2. **配分恒等** `real_Z_aud_is_kept_mass`（L588）：`Z_aud == kept mass == 1 − dropped`；`real_Z_aud_le_one`（L664）与 `real_log_Z_aud_le_zero`（L695）把根内 HlogZ 族（`real_log_le_mono`/`real_log_le_zero_of_le_one`）在 list 世界消解；
3. **精确分解** `real_kl_sum_split_list`（L967）：`kl_sum_split`/`kl_tail_eval` 的 list 世界重述；
4. **精确代价** `real_minp_kl_cost`（L1019）：`KL(minp ‖ full) == −log Z_aud`（逐字语句）——截断侧恒等；
5. **投影不等式** `real_minp_projection_eps`（L1070）：在 `Hq_fail`（通过集外质量为零）语义显式前提下 `KL(q ‖ minp) ≤ KL(q ‖ full) + eps`——投影侧不等式。**构造性强度说明**（逐 eps 余量形，定义见 §1.2）：本模块右端为 plain-eps 字面（y+eps），属 `real_le_closure_b_one` 单步直连同型（D:=one，证书 `real_lt_zero_one` 既有；前提位照抄）——可升格未建，登记为开放项（基座注：承载模块 `UpAuditBridge` 已回并 CW219 主基座——四项验证全过、双旗舰 `real_minp_kernel_is_projection`/`real_minp_projection_eps` Print Assumptions 均 Closed，本模块活态在库，B 形升格的基座前置已满足）。

> **KL 方向性纪律**：上列 4 与 5 是**两条不同方向的陈述**，不得混写——恒等式从截断侧度量 `KL(minp ‖ full)`（minp 核作为被度量的近似），不等式从投影侧度量 `KL(q ‖ minp)`（q 与截断兼容时的代价上界）；分别对应根内 `kl_sum_split` 与 `projected_distribution_minimizes_kl`（L95587）的方向。

**Bishop 形升格（已建成）**：上述投影侧不等式在模块 `UpReqMinPProjB` 中获得 Bishop 序谓词形态的构造性对应件 `real_minp_projection_eps_B`：在与第 5 件逐字相同的前提（`Hq_norm`/`Hq_pos`/`Hq_fail`，零新增逻辑前提）下成立 `KL(q ‖ minp) ≤_B KL(q ‖ full)`，其中 `real_le_b x y := ∀eps>0, x < y + eps` 为 Set 层谓词；原 plain-eps 余量经单步闭包引理 `real_le_closure_b_one`（模块 `UpRealLeB`，D:=one 特化，正性证书 `real_lt_zero_one` 为既有闭合件）在全称范围内消去。同模块以两条独立路线交叉验证同一结论：`real_minp_tail_nonneg_B`（`0 ≤_B Σ kl_tail`，经单向桥 `real_le_to_le_b`）与 `real_minp_projection_B_split`（不消费 eps 形原件，改走尾项非负、≤_B 加法兼容组合器 `real_le_b_plus_compat`（模块 `UpRealLeB2`）与精确分解 `uab_kl_sum_split` 的等式换形）；另有 ≤_B 自反、双端等式运输与非负右加四条辅助引理。七件结论全部位于 Set 层，经 `Print Assumptions` 审计为 Closed under the global context，全文件经 coqchk 认证（"Modules were successfully checked"），提取验收已在独立验证文件中完成（`Obj.magic` 零出现）。适用限制：`≤_B` 是逐 eps 近似的非严格序封装，本模块是第 5 件 plain-eps 形的谓词级升格而不改变其数学内容，也不触及截断侧恒等 `KL(minp ‖ full) == −log Z_aud` 的方向；原 §10.2 登记的合并开放项中的 C-S le 形（模块 `UpCS`）B 形显式对照件已建（`real_cauchy_schwarz_B`，模块 `UpReqCSB` L31；2026-09-12 核验）。

**复合链的现状（2026-09-12 核验更新）**：熵刻画（§8.5）与投影族（本节）的部件均已闭合；`KL(minp ‖ full) == −log(1 − dropped) ≤ S ≤ log|S|` 的复合熵链已拼装闭合——模块 `UpReqMinPKLChain`（1,038 行，R1–R4 全线 Qed；主件 `x1_kl_le_log_N` L1028：`real_le x1_KL LN`），原登记的该开放项就此闭合。

**同族登记（统一投影定理，本文仅登记不展开）**：模块 `UpProj`（经内核校验的独立模块）把 KV 逐出（实例 A）、安全过滤（实例 B）与 Min-P（实例 C）三个截断对象合并为同一投影定理的实例——`proj_normalized`（L296）、`proj_minor_uncond`（L332，minorization 无条件传送）与精确代价恒等 `proj_kl_cost`（L611：KL(q ‖ f) == KL(q ‖ Proj) − log Z_P）；模块 `UpProjBPC`（经内核校验的独立模块）给出两级级联的成本代数——`Z_compound_mul`（L216：Z₁₂ == Z₁·Z_c）与 `proj_kl_chain`（L289：KL 代价链可加）。两者与 §8.7 主线同构，本文不作为主线定理展开（其一实例即本节 Min-P 族）；另模块 `UpFirewall` 的熵-能量-KL 精确恒等 `recovery_entropy_gain`（L139：ΔH == β₂ΔE + KL(p_{t1} ‖ p_{t2})，任意两正温度）与 §9.1 的统一视角相关，同样仅登记不展开（该模块头注自设「不主张 TV-熵传递」边界声明，引用遵循该边界）。

---

## 9 与对齐理论的统一及当前边界

### 9.1 统一视角

FEP 与 RLHF/DPO（RLHF 见 Ouyang et al., 2022[26]；DPO 见 Rafailov et al., 2023[14]）之间是可核验的**结构关联**，而非「循环依赖」：

- **同一分解定理的两个实例化（可核验）**：FEP 的 `free_energy_kl_decomp`（L16259）与 RLHF 侧的 `rlhf_free_energy_kl`（L20290）是同一自由能-KL 分解定理的两次实例化，故本工作与 RLHF/DPO 对齐目标的关联表述为 **KL 项形式同构**：后者把 RLHF 对齐目标显式写成 `F[p] = F[p_b] + β·KL(p‖p_b)` 的形式（该 KL 正则形式与 Ouyang et al. (2022)[26] 的 KL 惩罚项、Rafailov et al. (2023)[14] 的隐式奖励分解同构），RLHF 最优策略 π\* 就是 `boltzmann_dist` 在能量 `−r`、温度 `β` 下的实例。本文不主张更强的「共享同一数学基座」整层等价——任何 KL 型正则化方法都与该分解形式同构，形式同构即这一层级的全部内容；实例化关系由定理 `rlhf_free_energy_kl` 机器检查。
- **单向依赖**：本工作不依赖 RLHF/DPO 的任何定理；本文亦不主张 RLHF/DPO 依赖本工作——二者的关联是同一分解定理的两个独立实例化。不构成「循环依赖」。
- **FEP-attention 连通（机器检查；分量定位见 §9.2.2：三个基座定理的纯实例化装配，应用案例层）**：同一 `free_energy_kl_decomp`（L16259）分解基座的第三次实例化落在 attention 侧——`attention_minimizes_free_energy_unique`（L112225，`base_loss := −z`、`D := T`，§5.4(b)）机器检查地证明 softmax 温度分布是变分自由能 `F_T[p] = −E_p[z] + T·Σp log p` 的唯一最小点。于是「attention 层 = FEP 变分自由能最小化的唯一解」不再是彼此脱节的两组叙述：FEP 数学核（§4）、attention-Gibbs 桥（§5.2/5.3）与对齐目标（RLHF/DPO）经由同一分解定理在库内连通。库内进一步把该唯一解处的精确自由能值并入同一基座：`UpExtras219.free_energy_softmax_eq_neg_T_logZ`（L114089，§5.4(b)）机器检查 `F_T[softmax_temp(z)] == −T·log Z_T(z)`——「attention 层 = FEP 变分自由能最小化的唯一解」连同解处的精确自由能值由此在库内完整连通。
- softmax 注意力的 Gibbs 解释为语言模型提供了统计力学语义；
- KV 逐出与 top-k 截断的恒等式与单调性刻画为推理效率启发式提供了可审计的**结构性**代价度量（不含可计算误差估计，见 §6.2；另含破缺恒为零与有限 n 漂移界，§6.2.2）。
- **签名迁移试点（登记）**：自由能-KL 分解与 attention-Gibbs 桥的 setoid 签名形态各有一定理级迁移试点——模块 `UpSigMigrate` 的 `req_free_energy_kl_decomp`（L310）与 `req_attention_is_gibbs_temp`（L544），为「抽象 Id 系陈述 → setoid 实例」的整体迁移（§10.2 已解决项（一））提供首批机器检查样例；该全量迁移已处置闭合（734 件全数落位：670 件交付四项验证，64 件保留为抽象层与实例层双套陈述并行；迁移清单见公开 artifact 补充材料 S2）。同视角下，温度族恒等式 `recovery_entropy_gain`（模块 `UpFirewall` L139：ΔH == β₂ΔE + KL(p_{t1} ‖ p_{t2})，任意两正温度精确成立，KL 项为温度分解恒等式的分量）与本文的对称 KL 恒等（定理 4.6e）同族——登记为统一自由能视角的延伸素材（该模块不主张 TV-熵传递，引用遵循该边界）。

### 9.2 边界与前提

**使用限制**：本工作全部定理（`attention_is_gibbs`、`free_energy_kl_decomp`、`steady_state_boltzmann_attn` 等）的形式为 `forall {RI : RealInterfaceEnhanced}, <结论>`，即对任意满足接口的实例成立。具体柯西实数 `Real` 的实例化由该接口的 setoid 对应物承担（§9.2.3(d)(e)）。

该实例化在平行的 **Setoid 版接口** `RealInterfaceSetoid`（L32672，以 setoid 相等 `req` 替代严格相等 `Id`，且 `log_inv : forall x, lt zero x -> R` 携带正性前提）上完成对具体 `Real` 的**端到端实例**（`Real_RealInterfaceSetoid`，L39407），57 字段全部为实值构造，其中 `exp_neg_pos := cauchy_real_exp_pos`（L39450）、`exp_neg_plus := cauchy_real_exp_plus`（L39452）、`log_inv := cw_log`（L39453）、`log_inv_exp_neg/one/mult := log_inv_*_thm`（L39454/L39455/L39456）、`cauchy_complete := RealSetoid.real_cauchy_complete_metric_natle`（L39464）。即：**「具体柯西实数满足 Boltzmann/Gibbs 推导所需的全部超越函数语义」已被机器检查**（详见 §9.2.3；抽象 Id 系陈述 ↔ setoid 实例 ↔ Real 层复刻的逐字段/逐定理对照见附录 B）。

因此本文定理的数学内容在构造性实数上有两条承载路径：setoid 实例的字段回填（exp 族、log 族、度量与完备性全部实值化），以及 `Real` 层的逐 eps 复刻（KL 不等式 `real_gibbs_inequality_eps`（L41704）、log 可微性 `real_log_differentiable`（L46386）、compose/entropy 可微性等已直接证明，主文件 Qed 计数见附录 C 审计口径、零全局公理）。抽象层与实例层之间的签名对接已完成全量处置闭合（迁移清单见公开 artifact 补充材料 S2：670 件交付四项验证，64 件保留为抽象层与实例层双套陈述并行，734/734=100%；验证记录见公开 artifact；逐定理对照见附录 B 与 §10.2 已解决项（一））。

> **边界声明——主要定理在具体 `Real` 上的承载现状**（逐条提炼自附录 B 对照表，不超出该表现状）：
> ① **经 setoid 实例承载、可在具体 `Real` 上成立（第一承载路径）**：字段级——`Real_RealInterfaceSetoid`（L39407，57 字段）与 `RealEnhancedReal`（L41115，增强版）的超越函数字段全部实值化，编译期机器检查（§9.2.3(d)(e)）；定理级——等号簇 3 头条已在 setoid（req）签名下直证并可被 `RealEnhancedReal` 直接消费：`attention_is_gibbs_setoid`（推论 5.1a，单位温度）、`steady_state_boltzmann_attn_setoid`（定理 5.3）、`boltzmann_normalized_attn_setoid`（Section `AttentionGibbsBridgeSetoid` L66137–66414）。
> ② **已在具体 `Real` 上逐 eps 直接证明（第二承载路径）**：`real_gibbs_inequality_eps`（Gibbs 不等式，定理 4.2 侧）、`real_attention_is_gibbs`（attention 同构，推论 5.1a 侧，单位温度）、`real_steady_state_boltzmann_attn`（稳态，定理 5.3 侧）、`real_top_k_majorization`（Top-k 支配，定理 7.1/7.3 侧）、`real_minp_markov_kernel_normalized`（Min-P 归一化，定理 8.5 侧）、`real_kl_sum_decomp`（自由能-KL 分解，定理 4.1 侧；完整分解的 Real 层对应件已建成——`rkd_kl_decomp_full`/`rkd_kl_decomp_full_partition` 已闭合，主文件 `real_kl_decomp_full` 的显式前件 Variable 旧形态已被取代，req 系完整分解已证载体 `rfep_real_kl_decomp_full` + 规范化引理 `real_kl_decomp_full_canon` 不变，见 §4.1 与附录 B 定理 4.1 行）、`real_boltzmann_diff_bound`/`real_db_breaking_bound_eps`（KV 定量界，定理 6.1b/6.1c——Real 层独立定量强化，非定理 6.1 的逐字复刻）。
> ③ **仅抽象 Id 层证明、承载现状分层**：温度对应（推论 5.2）已有 Real 层复刻——定理 5.2b（`real_attention_is_gibbs_temp`，模块 `UpDebtGibbsT`）；缩放-温度对偶族的 Real 复刻已闭合——定理 5.6c（`real_scale_temp_duality`，模块 `UpDebtDual`）；steady_state 迭代侧的 Real 镜像已闭合——定理 5.9（`attention_iterate_converges_real`，模块 `UpArchAttn`）；抽象层 √d 见证两层全闭（定理 5.6a/5.6d）。上列诸件的 setoid/req 迁移已全量交付（`req_attention_is_gibbs_temp`，模块 `UpSigMigrate`；`reqd_scale_temp_duality`，模块 `UpReqDist`；`agq_tv_contraction`/`agq_tv_iter`/`agq_iterate_converges`，模块 `UpReqAttnIter`；`ag_topk_tv_identity_strict`，模块 `UpReqAttnGibbs`；双点收缩族（定理 5.4–5.6：`u_tv_contraction` L95931 / `u_tv_iter` L96019 / `bs_minorization` L96286 / `bounded_softmax_tv_contraction` L96331 / `bounded_softmax_tv_iter` L96344——其 expf 迷你接口前件的 Real 层非空性由 `real_expf_realizable` L96364 由具体实例满足）的同名同形 req 件，模块 `UpReqSampling`——迁移清单见公开 artifact 补充材料 S2，逐项已记录，处置闭合 734/734）；真余项（论文自留，不在 734 迁移范围口径内）：`steady_state_boltzmann`（定理 4.9）的方程形态逐字复刻已闭合（`real_steady_state_boltzmann`，模块 `UpReqSteadyThermo` L100；2026-09-12 核验）；双点族的 Real 层完整复刻已以 δ 接口形态在树（定理 5.10，模块化树（补充材料 S2），2026-09-11 核实；其 Part 2 并已闭合显式 δ\* 实例，setoid 迁移仍开放）。
> **说明**：即使 ①② 均已覆盖的头条（如推论 5.1a/定理 5.3），其抽象 Id 陈述与 Real 层复刻之间的 statement-level 机器对齐仍为「开放：需逐条 diff」（现为人工比对，附录 B）；① 描述的是「setoid 签名下已直证 + 实例可消费」，抽象 Id 系定理签名向 setoid 实例的**整体迁移已处置闭合**（迁移清单见公开 artifact 补充材料 S2：734/734=100%，670 件交付四项验证，64 件保留为抽象层与实例层双套陈述并行——定理级试点两件（`req_free_energy_kl_decomp`/`req_attention_is_gibbs_temp`，模块 `UpSigMigrate`，§10.2 已解决项（一））已扩展为全量交付）；statement-level 机器对齐（人工逐条 diff，附录 B）为 734 迁移范围外的论文自留项，不因迁移闭合而自动完成。

**有效性先决问题（对以具体柯西实数为语义目标的读者，正文显式陈述）**：本文主要定理以抽象 `RealInterfaceEnhanced`（Id 系）接口陈述；「抽象定理是否已在具体柯西实数上成立」因此是使用本文结果的**有效性先决问题**，而非附录细节。对齐现状分三层陈述：①**字段层（已完成）**——setoid 实例 `Real_RealInterfaceSetoid`（57 字段）与 `RealEnhancedReal` 的全部超越函数字段已实值化（§9.2.3），接口语义在柯西实数上非空；②**定理层（已全量处置闭合）**——三条先行迁移带（`UpSigMigrate` 试点 12 件、基座内 `AttentionGibbsBridgeSetoid` 区段 7 件、全部 real_* 构造层）之上，主要定理的全量定理级迁移已按五批制完成（670 件交付四项验证，64 件保留为抽象层与实例层双套陈述并行；逐项清单见公开 artifact 补充材料 S2）——主要定理在柯西实数上的语义地位现可经三条头条 setoid 直证、req 对应件消费或 Real 层复刻读取（附录 B 逐条）；③**复刻层（部分）**——部分头条另有 Real 层逐 eps 直接复刻（附录 B）。**解法已立项、普查并执行完毕**：抽象层（Id 系）→实例层（req 系）的全量迁移覆盖 734 件，其中约 56 件保持双层并行不迁移（设计性双套保留，逐项理由公开）；迁移按五批拓扑执行，属工程迁移工作。处置结果：670 件交付四项验证，64 件保留为抽象层与实例层双套陈述并行；逐批记录与逐项清单见公开 artifact 补充材料 S2。其中 clip_lower/ppo_clipped_improvement 两件原列为暂缓（与实例层陈述并行保留），因 req 对位件建成现已交付。读者据附录 B 对照表逐定理读取任何主要定理的语义地位与承载路径（setoid 直证／req 对应件消费／Real 复刻／抽象层与实例层两套陈述并行保留）；statement-level 人工比对等论文自留项见 §10.2。

其余边界：

1. **exp 正性已在 Setoid 接口层实例化**：Real 层 `cauchy_real_exp_pos`（L13383）已证明；`esq_eq_corr` 为已证引理（L12837 → Qed L12868），其所需的两个 Vandermonde 恒等式 `vander_4m2`（L11361）、`vander_4m4`（L11567）均已闭合。此外 `exp_neg_recip`（L36044，`e^{-x} == (e^x)^{-1}`，以 `real_inv_pos` 表述）、`cauchy_real_exp_wd`（L35117）、`cauchy_real_exp_mono`（L35227）均已并入主库，并在完整版 Setoid 实例中把 exp 族填为实值（`exp_neg_pos := cauchy_real_exp_pos`，L39450；`exp_neg_plus := cauchy_real_exp_plus`，L39452）。另有 `exp_neg_positive`、`exp_pair_term_nonneg`、`e_o_split_even`/`e_o_split_pos` 等中间引理，作为该字段在具体实例上的补充证据。抽象层接入见上文使用限制与 §10.2 签名对接项。
2. **`log_inv` 族已闭合；`log_differentiable`（Set 层）仍为 `Variable`，Real 层对应已构造性闭合**：`entropy_differentiable`（L26368）已完整证明，Set 层依赖 `log_differentiable`（L26365）。主库已完成 `log_inv` 族的构造与闭合：`cw_log`（L38016）、右逆 `cw_log_exp_right`（L38059）、弱三分 `real_weak_trich`（L38268）、`cauchy_real_exp_mono`（L35227），以及三条恒等 `log_inv_exp_neg_thm`（L38421）、`log_inv_one_thm`（L38443）、`log_inv_mult_thm`（L38471），并全部填入完整版 Setoid 实例（见 §9.2.3）。`log_differentiable`（L26365）**不属于 `RealInterfaceSetoid` 的 57 字段**——该 Setoid 接口不含可微性——它是分析层独立的 `Variable` 假设。其 Real 层对应已构造性闭合：`real_log_differentiable`（Section LogDiffPhase4，主引理 L46386，`RealDifferentiable` 记录，Bishop 逐 eps，df := 1/x，零 `Admitted`/Axiom）与 `real_entropy_differentiable`（L51363，entropy 泛型组装，诚实前提 Omega_B_wd/E_B_pos 等 Section Variable，零公理）均已证明（主文件 Qed 计数见附录 C 审计口径）。Set 层接口字段因结构性边界保留 Variable，但其数学内容已在构造性实数上完整实现。
3. **能量函数抽象（边界收窄）**：`energy` 和 `z` 是任意函数；「一致范数界 → 双界 logits」一段已机器检查——模块 `UpCS` 的 C-S 核（定理 5.7）与模块 `UpQKBound` 的界转化（定理 5.8，`qk_logits_bounded`：根有界前提 `‖q_s‖ ≤ Qb`、`‖k_s‖ ≤ Kb` ⟹ sigT Δ>0 ∧ |attn_logit| ≤ Δ）把「Q/K 范数界到双界 logits」钉为机器检查内容（根有界前提形态的构造性理由见 §5.5 注记）。仍未闭合的是**末端一步**：把显式 Δ 值 δ\* := e^{−2Δ/T} 代入双点收缩的 Real 复刻（定理 5.10 的 δ 为接口形态），闭成「一致范数界 → 双界 −Δ ≤ z ≤ Δ → δ\* = e^{−2Δ/T} → (1 − e^{−2Δ/T})ⁿ」单条管线（§10.2 第 2 项）——〔2026-09-11 核验注记〕其中「δ\* 代入」一步已在树内闭合（模块化树（补充材料 S2） Part 2：`tvd_dstar_instance`/`tvd_dstar_iter_contraction`，经实测核对），尚余 `UpQKBound`→`UpTVDoeblin` 的模块级组合证明待完成，见 §5.5 定理 5.10 载体状态与 §10.2 第 2 项。**旁证供给（已机器检查，模块层）**：库内另有一支与「logits 幅度界」直接相关的已证族——模块 `AttnLogSumExpBound` 的逐 logit 配分控制 `attn_logit_le_log_partition`（`s ∈ ss ⟹ s ≤ log Σ_t e^{z_t}`，即 logit 被 log-配分函数支配）、log-配分型上界 `attn_log_partition_bound`（`log(Z·Agg) ≤ log Z + log B`）与倾斜配分恒等 `attn_tilted_eq`（`T == Z·Agg`）。该族为 logit 幅度提供了**除范数路线之外的第二个已证上界来源**，但其结论为单侧（`s ≤ log Z`），且与 `UpQKBound`→`UpTVDoeblin` 的组合**非同一命题**，故不构成上述末端一步的闭合；列此以说明该缺口的分量供给现状。**具体 Transformer 实现层面（浮点、多头、掩码）不在形式化范围。√d 覆盖现状：两层全闭（`sqrt_witness_nat_sq` L96596、`scale_dual_nat_sq_k` L96622；`real_sqrt_exists` L96475，定理 5.6a；`sqrt_witness_exists_abstract`，定理 5.6d）。
4. **有限状态空间**：当前形式化限定于有限离散 `S`。
5. **注意力「稳态」：方程验证 + TV 收敛（clim 侧开放）**：见 §5 章首说明——稳态方程定理 5.3 验证的是「若视为 Markov 核则 Boltzmann 为稳态」；注意力核迭代在 TV 意义下的收缩与迭代收敛已在 Doeblin minorization 假设下机器检查（§5.5，`attention_tv_contraction` L29195 / `attention_tv_iter_contraction` L29287 / `attention_iterate_converges` L29330），并进一步给出免平稳的双点形态、在有界 logits 核上给出显式 δ* = e^{−2Δ/T}（§5.5 定理 5.4–5.6）；温度两极（T→0 极限 + T→∞ 均匀混合，§5.4(a)）与稳态迭代的 Real 镜像（定理 5.9）亦已闭合。未覆盖的是 Transformer 逐层注意力的动力学与状态空间（clim）意义下的收敛（双点收缩族的 Real 层 δ 接口复刻已入模块化树——定理 5.10；setoid/req 迁移仍未完成，附录 B）。
6. **Min-P 定量估计的覆盖范围**：截断质量与词表大小的量级关联已闭合（定理 8.9 `minp_dropped_mass_le_inv_vocab_size`，L31849），放大因子、阈值单调与质量上界亦已证明（`minp_kernel_ratio`、`minp_dropped_mass_le_one_minus_max` 等）；与熵的量级关联已在模块化树内闭合（`dropped ≤ 1 − e^{−S}`，模块 `UpMinP`，§8.5 熵刻画注记——定理 8.9 降为推论）；KL 投影解释的 Real 层实例族已闭合（§8.7，模块 `UpAuditBridge`）。KL ≤ S 复合熵链已闭合（§8.7），仍开放项仅余完整的可计算误差估计（§10.2 第 5 项）。〔2026-09-12 核验：复合熵链一步已由模块 `UpReqMinPKLChain`（1,038 行，R1–R4 全线 Qed，主件 `x1_kl_le_log_N` L1028）闭合；仍开放项只剩完整的可计算误差估计。〕
7. **生成序列遍历性未覆盖**：top-p / nucleus、Top-p + Min-P、Top-k + Min-P 联合核均已形式化（§10.2 第 3 项），但生成序列的渐近性质（遍历性/稳态分布）仍未证明；§6.2.2 的有限 n 漂移界（定理 6.3）是该方向的第一个定量步，本文对其不作遍历性主张。
8. **历史 220 分发形态与当前 246 编译清单的范围注**：历史大库分发形态（历史名 220）的模块化扩展树包含与本文主题无消费关系的模块——治理演算簇（UpRecast 再铸账本、UpCLQuery 分型拒答、UpSLM 熔合不可逆演算、UpPLA p-adic 估值、UpRefuted 否定形定理库）、Löb 长线（UpLoeb/UpLoebD2）与对齐/宪法/停时/耗散系（UpAlignId/UpConstitution/UpStopTime/UpDissip 等）——**本文不消费**，其定理不入本文引用链；本文引用的该历史分发形态中的扩展件限于：UpCS、UpQKBound、UpDebtDual、UpDebtSqrtAbs、UpDebtGibbsT、UpTempWindow、UpMinP、UpAuditBridge、UpEvictId、UpKVEv、UpKVDrift、UpArchAttn（正文相应小节），以及仅登记不展开的 UpProj/UpProjBPC/UpFirewall（§8.7/§9.1）与迁移试点 UpSigMigrate（§9.1）。UpSigMigrate 的两件试点与 UpDebtSqrtAbs 的抽象层见证同时是「抽象层与 Real/setoid 层各自独立完成证明」这一双层验证口径的库内证例，本文不展开。当前编译清单为 246 模块，Live_X 356 个 .v；
9. **Real 层自由能间隙族（模块层；本文登记，不并入正文主张）**：本文 §4 FEP 数学核在 Real 层的对应物除 §4.3/§4.4 已登记者外，另有完整模块 `FreeEnergyKLGap`（578 行）给出 Real 层 FEP 核心形，四件均已机器检查、零全局公理：**间隙分解** `fekl_gap_decomp_general`（一般 `sumf` 载体，`F(p) − F(π_boltzmann) == D·Σ_s kl_term` 的等式形，接口参数全显式）；**B 形最小性** `fekl_fep_gap_le_b`（`F(π_boltzmann) ≤_B F(p)`，前提为两条归一化 premise）；**规范配分实例** `fekl_fep_gap_canonical_le_b`（取 `Z := Σ e^{−e/D}` 并以 partition 恒等放电 `Σπ_b == 1`，前提仅余 `p` 的归一化）；**逐 eps 形态** `fekl_fep_gap_eps`。前四件即定理 4.1/4.4 的 Real 层对应物，其存在意味着「Real 层 FEP 间隙」不属本文开放项。
   同模块另含 `fekl_sf_vfe_ge_complexity_B`（`|v| ≤_B VFE(v,v)`，即变分自由能不低于复杂度项）。**注记**：按库内定义 `VFE := distortion + complexity`，该结论的代数内容为 `complexity ≤ distortion + complexity`，由 `distortion ≥ 0` 得出，属**定义性后承**（与定理 5.3 同等口径），列此仅为 FEP 族完整性登记，**不计入本文并列贡献**，亦不改变 §2 scoped claim。
   两层口径不变：正文 §4 定理的陈述与证明不消费 `FreeEnergyKLGap`；本项为该模块族在 Real 层的登记。

**范围外披露（不进入本文 scoped claim）**：B 路（Banach 推广）认证推进至实例面——exp 加法交换性 `UpReqBanachExpAddEq` 已闭合并云认证；exp_neg/可逆性侧（`ExpOppOne`/`InstPre`/`InstEMult`）与 `BanachCauchyD` 全部认证；实例面 `UpReqBanachInstReal` 与无假设件 `BanachNoHyp`/`BanachNoHypNorm`、`UpReqBanachNormOpp`/`UpReqBanachSepThm`/`UpReqB4TwoStage` 已闭合（HEAD=b657aff）。同两波新增件中与本文相关者：温度-能量单调的 Real 层对应件 `RealEnergyTempMono` 与 Bishop 形伴件 `etm_energy_temp_mono_b`（§4.4 定理 4.6d/4.6e 的〔构造强度〕标签已同步登记）。上述结果仅用于对齐当前库认证面，不改变本文四族结果的构造性立场与结论；

### 9.2.1 接口字段的封装状态

`exp_neg_pos`、`log_differentiable` 等 `Variable` 在 Section 外以接口字段形式被抽象为定理的显式前件，其逻辑地位与 `Axiom` 不同：

1. `RealInterfaceEnhanced` 是 **Class**（L217），以 `Context {RI : RealInterfaceEnhanced}.` 引入（本模块 `Section AttentionGibbsBridge`（L27929）见 L27931），不是顶层自由 `Variable`；
2. `End Section` 后 Coq 自动对 `RI` 泛化，接口字段成为定理的显式（隐式）前件；
3. 实证：Rocq 9.0 `Print Assumptions` 对 `attention_is_gibbs`、`boltzmann_factor_pos`、`free_energy_kl_decomp` 均返回 **`Closed under the global context`**。
4. **`Print Assumptions` 完整输出（补充材料）**：在审计快照基线（76,830 行）对六条头条逐一执行 `Print Assumptions`——`attention_is_gibbs`、`topk_tv_identity_strict`、`attention_iterate_converges`、`scale_temp_duality`、`minp_markov_kernel_normalized`、`real_db_breaking_bound_eps` 全部返回 **`Closed under the global context`**（批量独立验证脚本与完整输出见补充材料 S3）。上述六条头条之后库内新增的定理（双点收缩族、硬注意力 TV 闭合链、FEP/逐行等价定理、log-sum-exp 恒等式与各模块件）未逐条重跑该批量验证；其零公理状态由编译期行首零命中审计（零全局公理/Admitted/Abort）与全量 coqc RC=0 维持。

因此本工作的定理应读作 `forall {RI : RealInterfaceEnhanced}, <结论>`，即对任意满足接口的实例成立；其 setoid 对应物的实例化与 Real 层逐 eps 复刻共同承载数学内容（见上文使用限制）。**可提取性**：全库定义均置于 Set 层：sigT/`And` 中的有理数序谓词一律使用 Set 值判定谓词 `QltT`/`QleT`，`And` 不实例化到 Prop；`real_mult`、`cauchy_real_exp` 等核心构造可提取为不含 Prop 残留的 OCaml 代码（提取验证在独立验证文件中完成）。本库使用自定义 Set 层合取 `And (A B : Set) : Set := A * B`（L68），非 Coq 标准的 Prop 层 `and`。

### 9.2.2 数学深度自评（截断采样与 FEP 桥）

截断采样部分（§7–§8）的数学内容深度有限：Top-k 支配性是排序前缀性质，Min-P 归一化是重归一化定义的直接后承，Min-P 核关系是一次倒数单调性调用。据此明确调整定位：

| 定理 | 数学深度 | 真实价值 |
|---|---|---|
| `minp_markov_kernel_normalized`（L31050） | 低（核心步为 `inv_pos_correct`） | 规格的机器检查：证明 Min-P 在工程实现中「重归一化后仍为概率分布」这一被广泛默认的事实 |
| `minp_markov_kernel_keep_ge_full`（L31127） | 低（核心步为 `inv_pos_le_compat` L249） | 确认截断只放大保留者概率、不产生方向性异常 |
| `top_k_majorization`（L30047）`top_k_majorization_mem`（L30264） | 低（排序前缀性质） | 作为后续 top-p / 核采样形式化的**对照基准** |
| `top_k_swap_no_gain`（L30073） | 低（加法保序） | 同上 |
| `top_k_tail_bound`（L29719）`tail_plus_kept_full`（L29732） | 低（逐项保序 + 求和线性） | 容量预算与质量守恒的形式化记账 |
| `minp_dropped_mass_le_inv_vocab_size`（L31849） | **中**（13 引理链：argmin 遍历最小性 + 完整核归一化 + 和≤势·最大 + 除以正数） | 截断质量与词表大小的定量挂钩（`≤ 1 − 1/|S|`） |
| `topk_tv_identity_strict`（L30638） | **中-高**（19 引理四段组装：逐点差分解 + 求和分解 + 守恒闭合 + TV 归一化，精确恒等） | Top-k 截断的总变差定量（`TV == tail_mass/Z_thermo`，条件化精确恒等） |

**FEP 桥与 attention 自由能定理的分量自评**：本文叙述上最突出的两项——FEP 数学核（§4）与「attention 层 = 变分自由能唯一最小点」（§5.4(b)/§9.1）——在证明结构上为初等组装：后者是 `free_energy_kl_decomp`/`min_free_energy_is_boltzmann`/`free_energy_min_unique` 三个基座定理在 `base_loss := −z`、`D := T` 处的纯实例化，辅以三条机械对接引理（§5.4(b)）；前者为同一分解定理的直接后承。其定位：**基座之上的应用案例**——价值在于（i）把 FEP、注意力与 RLHF/DPO 对齐目标连通到同一分解定理（§9.1），（ii）全部前提的构造性机器检查与显式化，（iii）为截断采样的定量理论提供被截断/被迭代的分布对象；不在分析难度。分析分量主要由 §1.2 第一层（柯西实数基座的逐 eps 技术与 Real 层对应定理族）与第二层（定理 7.6 的 19 引理组装、Doeblin 显式率链、KV 漂移界）承载。

**调整后的定位**：截断采样部分的贡献在于（a）把解码策略的**全部前提**显式化并机器检查（§8.6）；（b）为更复杂的截断策略（top-p、核采样、组合策略）提供可复用的形式化基座与对照基准；（c）展示这些工程启发式在纯构造性逻辑下不依赖排中律。定量层已把本部分的数学深度从“规格机器检查”提升到截断误差的定量刻画：Top-k 截断的总变差精确恒等（定理 7.6）与 Min-P 截断质量的词表大小挂钩（定理 8.9）构成定量主线；其中 TV 恒等的符号处理揭示了抽象层 `le` 不可析取的构造性边界，可作为独立技术贡献。

### 9.2.3 `log_inv` 族的闭合与完整版 Setoid 实例装配

（以下行号均为主库行号，经逐条核验。）

库尾新增 `Section LogStage3`（L34872–L39398，内含 `Section LogInvStage` L38201–L39397）与 `Section FullInstance`（L39399–L39467），Axiom / Admitted / Abort / `Classical_Prop.classic` 保持全零。

**(a) exp 层补全**（Setoid 装配的前提）：

| 引理 | 主库行号 | 陈述 |
|---|---|---|
| `cauchy_real_exp_gt_one` | L34910 | `t > 0 ⟹ e^t > 1` |
| `cauchy_real_exp_minus_one_pos` | L35043 | `e^t − 1 > 0`（`t > 0`） |
| `cauchy_real_exp_plus_pos` | L35073 | 加法式的正性配套 |
| `cauchy_real_exp_wd` | L35117 | `a == b ⟹ e^a == e^b`（setoid well-defined） |
| `cauchy_real_exp_mono` | L35227 | `x < y ⟹ e^x < e^y`（严格单调） |
| `exp_neg_recip` | L36044 | `e^{−x} == (e^x)^{−1}`（以 `real_inv_pos` 表述） |
| `exp_lower_lipschitz_real` | L37159 | exp 下界的 Lipschitz 控制 |

其中 `cauchy_real_exp_wd`（L35117）`cauchy_real_exp_mono`（L35227）是把 exp 纳入 setoid 接口、并支撑对数唯一性论证的两个关键组件。

**(b) log 构造机械**：`log_step`、`log_bisect`、`log_mid`、`log_scan`/`log_scan_spec`、`approx_root`、`log_interval_nested`、`log_scan_nested`、`log_seq_cauchy`（`Section LogStage3`，L37895 起）建立，最终以

```coq
Definition cw_log (y : Real) (Hy : real_lt real_zero y) : Real :=   (* cw_log，定义 L38016 *)
  existT _ (log_seq y Hy) (log_seq_cauchy y Hy).
```

把对数定义为柯西实数。右逆 `cw_log_exp_right`（L38059），`e^{cw_log y} == y`）为后续三条恒等的公共引理。

**(c) `log_inv` 族三条顶层恒等**（`Section LogInvStage`，全部 `Qed`）：

| 定理 | 行号 | 陈述 |
|---|---|---|
| `log_inv_exp_neg_thm` | L38421 | `cw_log (e^x) H == x`（左逆） |
| `log_inv_one_thm` | L38443 | `cw_log 1 H == 0` |
| `log_inv_mult_thm` | L38471 | `cw_log (a·b) == cw_log a + cw_log b` |

三者共用同一构造性论证骨架：由右逆得 `e^u == e^{target}`，再以弱三分 `real_weak_trich`（L38268）、`cauchy_real_exp_mono`（L35227）与 `real_lt_not_eq`（L38204）排除 `u < target` 与 `target < u`，避免使用排中律。

**(d) 完整版接口实例**：`Instance Real_RealInterfaceSetoid : RealSetoid.RealInterfaceSetoid Real`（L39407）把 `RealInterfaceSetoid`（L32672）的 57 字段全部填为实值：exp 族 `exp_neg := cauchy_real_exp`（L39449）、`exp_neg_pos := cauchy_real_exp_pos`（L39450）、`exp_neg_zero := cauchy_real_exp_zero`（L39451）、`exp_neg_plus := cauchy_real_exp_plus`（L39452）；log 族 `log_inv := cw_log`（L39453）、`log_inv_exp_neg := log_inv_exp_neg_thm`（L39454）、`log_inv_one := log_inv_one_thm`（L39455）、`log_inv_mult := log_inv_mult_thm`（L39456）；metric/lim 族直至 `cauchy_complete := RealSetoid.real_cauchy_complete_metric_natle`（L39464）。其余字段复用 `Real_RealInterfaceSetoidCore`（L33433）的投影。

**(e) 增强版接口实例**：`Instance RealEnhancedReal : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid Real`（L41115）把 req 版增强接口 `RealInterfaceEnhancedSetoid`（L40464）的 39 字段全显式填为 Real 层实值：setoid 核心 8 + Proper 6 + 环律 9 + 序 14 + inv 2 + min/r_max/pos_test/pos_part/r_if/abs 族 + exp_neg 族 `e^{-x}` + log/log_inv 带正性前提 + metric/lim/cauchy_complete——含 `real_min`/`real_max`（逐点 Qmin/Qmax + Lipschitz）、Bishop 逐 eps 序性质（`min_le_l`/`r_max_le_l` 等，绕 real_le 不可表达性）、`real_pos_test`（= `real_lt real_zero`）、`real_r_if`（Set 层 Or 驱动选择）、`real_exp_neg`（= `cauchy_real_exp ∘ real_opp`，Boltzmann 递减语义）与 `real_log`/`real_log_inv`（= ±`cw_log`）。接口以 `Module RealInterfaceEnhancedMod` 包裹（Coq 记录字段名全局唯一）。库内接口实例共三处：`Real_RealInterfaceSetoidCore`（L33433）、`Real_RealInterfaceSetoid`（L39407）、`RealEnhancedReal`（L41115），主文件 2,930 处 Qed（行首 2,917 处、缩进 13 处）/ BAD=0 / 全量 coqc RC=0。

**实例化边界**：以上装配落在 **Setoid 版接口**（`req` 相等）上，构成本文定理数学内容的第一条承载路径；第二条承载路径为 `Real` 层的逐 eps 复刻——Gibbs 不等式 Real 层完整版 `real_gibbs_inequality_eps`（L41704）已证明（含 DPO 前置 `real_log_lt_mono` 等）。另有 `log_differentiable`（L26365）不在 `RealInterfaceSetoid` 字段之列，仍为独立开放的分析层假设（其 Real 层可微性已构造性闭合，见 §9.2 边界第 2 点）。抽象 Id 系定理、setoid 实例与 Real 层复刻三路径的逐字段/逐定理对应见附录 B。

### 9.3 常见量化陈述的构造强度目录

#### 9.3.1 动机：同一句陈述可以在三种逻辑强度下成立

在经典数学中，「a ≤ b」是一个无歧义的命题。在构造性逻辑中，非负实数序的编码方式成为一个需要显式声明的选择，而不同的选择使**字面相同的定理陈述**承载不同的数学内容。本库在建立过程中对这一现象积累了系统的事实，本节将其整理为一份目录：对量化机器学习中常见的一批陈述（KL 非负性、格不等式、平方非负性、收缩率、熵界），逐一标注其在三种典型强度下的可证性。我们认为这份目录本身构成一项可独立迁移的形式化知识：它告诉形式化者，面对一个熟悉的经典陈述，构造性逻辑为其保留的**最强可达形态**是什么。正文 §4/§5/§7/§8 主要定理陈述旁的〔构造强度：…〕标签即按本节档位书写：涉序结论按第一/二/三档与严格见证形标注，不涉序编码的结论按其结论形态（等式档、序档、等号条件档、见证构造档等）标注，并逐项给出 setoid 迁移语义与 Real 层承载。

#### 9.3.2 三档强度分类

设 x, y 为本库柯西实数层的元素（有理 Cauchy 序列连同模量见证，取原始序列表示）。

**第一档：强序精确形（Or 编码）。** 库内序编码为

```
x ≤ y  :=  (x < y) ∨ (x = y),
```

其中 `<` 为 Set 层严格小于（携带显式 ε-见证）、`=` 为逐点序列相等。此编码下，证明 `x ≤ y` 必须**构造出**两个分支之一的见证；对一般的 x, y，等号分支的归属不可判定，故本档在具体实数层对一大类陈述不可达。库内该档仅以接口字段或接口槽位承载（见 9.3.4），不作为具体层定理出现。

**第二档：Bishop 形（≤_B）。** 库内定义（`real_le_b`，`UpRealLeB.v`）：

```
x ≤_B y  :⟺  ∀ε>0, x < y + ε.
```

这是 Bishop 意义下的非负序：序关系即「任意小正余量下的严格序」。它是 Set 层全称型谓词，不携带不可判定的分支选择，故可证面显著更宽。与第一档之间有一条**单向桥**：`x ≤ y ⟹ x ≤_B y` 可证（`real_le_to_le_b`）；逆向 `(x ≤_B y) ⟹ x ≤ y` 不可证——否则取 `(x, y) := (min(a, b), a)` 将立得第一档的 `min(a, b) ≤ a`，与下述不可证目录矛盾（库内判定逐字记录于 `UpRealLeB.v` 尾注；§3.5 已在基座层面给出该同框对照的谓词级封装视角，本节从目录角度将其系统化）。

**第三档：逐 eps 余量形。** 将结论改写为带显式正余量的形态

```
∀ε>0, x ≤ y + ε,
```

其中右侧的 `≤` 仍为第一档 Or 编码。此形态与第二档内容等价，但在语法上保留 Or 编码——由于余量 ε 以显式前提出现，严格分支变为可构造（取半即得），因此这是 Or 编码之下**可达的最强形态**（§3.5）。库内大量 Real 层定理取此形态（命名模式 `*_eps`）。

**补充形态（非独立档）**：其一为**严格见证形**——结论为 `0 < KL(p‖q)` 一类严格正陈述。严格序携带 Set 层见证，故当见证可被显式构造（例如「存在某状态 s₀ 使 p(s₀) ≠ q(s₀)」的显式证据）时严格形可证，且强于前两档；其二为**否定式**——`¬(x < y)` 型结论不需要分支选择，是平方非负性等陈述的构造性替身。

#### 9.3.3 目录：代表定理逐档标注

以下件名均可在随论文发布的编译工件中按名检索（`grep "^(Theorem|Lemma) 件名"` 复现坐标）；括注为库内坐标（文件）。

**(a) 第一档（强序精确形）在具体实数层不可证的代表性陈述**——每条附不可证机理：

| 陈述 | 机理（一句） | 可达替代 |
|---|---|---|
| `min(a, b) ≤ a` | 需在「b < a」（严格支）与「a ≤ b ⟹ min = a」（相等支）间作分支选择，而该分支对构造性实数不可判定 | `min(a, b) ≤_B a`（`real_min_le_l_B`，UpRealLeB.v；格论版 `latb_min_le_l`，UpReqLatticeB.v） |
| `KL(p‖q) ≥ 0`（单 Or 见证形） | 需对 KL 值的零点做可判定分辨（p 与 q 逐点相等与否不可判定） | 逐 eps 形（`real_gibbs_inequality_eps`）与 Bishop 形（`real_gibbs_inequality_B`，UpRealLeB.v；`gibbsd_gibbs_inequality`，UpReqGibbsD.v） |
| `0 ≤ t·t`（单 Or 见证形） | 同上，需三分律（库内源注记逐字在案：抽象接口层此形「不可证（需三分律）」） | 否定式 `¬(t·t < 0)`（`real_square_not_negative`）与 Bishop 形（`real_square_nonneg_B`） |
| 三分律 `a < b ∨ a = b ∨ b < a`（及 `a ≤ b ∨ b < a`） | 经典公理；构造性柯西实数模型不可满足（库内以删除该接口字段并留下源注记的方式记录此事实） | 弱三分（`real_weak_trich`：不可同时 ¬(x<y)、¬(x=y)、¬(y<x)，否定连言的构造性替身） |
| `e^t = 1 + t ⟹ t = 0`（等号消去） | 需强三分或受限连续性上的排中律（LPO） | bool 载体重述加显式前提（`gibbe2_gibbs_equality_bool`，UpReqGibbsE2.v）；注入前提已无条件由具体实例满足（`t1_log_eq_linear_inject` + `t1_gibbe2_gibbs_equality_bool` 零接口前提，UpReqKLSTangent.v L81/L121） |

**(b) 第二档（Bishop 形）成立的代表性陈述**——即「在 ≤_B 强度下成立」的量化 ML 常见结论：

| 陈述 | 件名（文件） | 备注 |
|---|---|---|
| `min(a, b) ≤_B a, b`；`max` 上界格 | `real_min_le_l_B`/`real_min_le_r_B`（UpRealLeB.v）；`latb_min_le_b`/`latb_max_le_b`（UpReqLatticeB.v） | 与第一档不可证性并置的典型示例：同一陈述、两种编码、可行性相反 |
| `0 ≤_B t·t`；三角不等式 \|a+b\| ≤_B \|a\| + \|b\| | `real_square_nonneg_B`、`real_abs_triangle_le_B`（UpRealLeB.v） | 由统一装配引理（`real_le_closure_b`）从逐 eps 形单步升格 |
| Gibbs 不等式 `0 ≤_B KL(p‖q)` | `real_gibbs_inequality_B`（UpRealLeB.v）；`gibbsd_gibbs_inequality`（UpReqGibbsD.v） | 逐点核心＋求和提升全链 Bishop 化 |
| KL 正则化策略优化目标的最优性 `J(π) ≤_B J(π\*)` | `real_rlhf_optimal_B`（UpRealLeB.v） | 无条件形：余量系数的正性证书为接口既有前提 |
| 插值配分函数界 `Σ_s π_t(s)^{1−η}·π\*(s)^η ≤_B 1` | `jens_partition`（UpReqJensen.v）；`real_interp_Z_le_one_B`（UpRealLeB.v） | 策略迭代几何收敛率定理的数学核；配套幂单调（`powb_sub_one`，UpReqPowB.v）与单步收缩（UpReqGeomD.v） |
| `le_b` 乘法保序正因子面：`a ≤_B b ∧ 0 ≤ c ⟹ a·c ≤_B b·c`（左因子形、严格因子对照形、有界非负因子形齐备） | `x3d_le_b_mult_r_nonneg_or`/`x3d_le_b_mult_l_nonneg_or`/`x3d_le_b_mult_r_pos`/`x3d_le_b_mult_r_nonneg_bnd`（UpReqPowMonoBridge.v，337 行/6 Qed） | Or 形乘法单调三件套＋非负系数闭包器装配的合成器族；纯 B 形因子无上界版登记开放 |
| `le_b` 乘法反变负因子面：`x ≤_B y ∧ c ≤ 0 ⟹ y·c ≤_B x·c`（负因子翻转不等方向） | `t27_le_b_mult_r_nonpos_or`/`t27_le_b_mult_l_nonpos_or`/`t27_le_b_mult_r_negstrict`（UpReqNegFactorB.v，183 行/5 decl） | 与正因子面经取负共轭成对（`le_b` 取负反序＋正面件于因子 −c 处直用），合为 Or 形因子证书强度下的完整乘法保序两面家族 |
| KL 严格族 `≤_B` 闭合：`0 ≤_B kl_term(p,q)+(q−p)`（零比较零归一化前提）、`≤_B` 逐项求和保序器、`klst_kl_sum_strict_B`/`klst_kl_energy_nonconst_B` 对照形 | 10 件（UpReqKLStrictB.v，296 行/10 Qed） | 库侧留待的 `real_le_b` 系严格化闭合面补齐：严格层 sigT 正陈述 → `≤_B` 显式单向桥、右平移兼容器、list 级求和保序器 |
| `0 < eˣ`（对全部实数 x 无条件；`real_lt` sigT 见证形） | `upreq_exp_pos`/`upreq_exp_pos_or_destruct`（UpReqExpPos.v，165 行/5 Qed） | LPO 裁决口径：平方非负 Or 形不可证（Or 左支需真实 ε 见证而平方表示不产出见证），左支由幂级数 ε-见证直供——级数 ε-见证为唯一路线；该不可证面与 LPO 的等价性已形式化（`UpReqLpoEquiv` 双向定理，姊妹论文披露） |
| Real 层半元底座：`upreq_half`（const ½ 常数因子形）与 `eˣ = (e^{x/2})²` 平方分解 | `upreq_half_plus`/`upreq_exp_half_sq`/`upreq_exp_neg_half_sq`（UpReqRealHalf.v，192 行/6 Qed） | 指数正性五步链步骤 3 的缺位底座；平方形态在 Or 编码下不推进闭合（承上行的不可证裁决） |
| ε 见证显式化双形：`ε := 1/(2C)` 字面现形（`real_lt` sigT 拆包，第一见证位浮出为有理数输出）；Q 层偶阶截断正下界 `q := 1/(1+B)`，`B := (2m+1)·(1+a)^{2m}` | `upreq_exp_pos_witness`（UpReqExpPosWitness.v，83 行/2 Qed）；`upqb_even_witness`（UpReqExpPosQBound.v，353 行/16 Qed） | 同一正性的两条不同源独立见证路线（1/C 形与 1/(1+B) 形互不依赖），均为可计算有理数输出 |
| 指数级数 Banach 代数层收敛：`Class BanachAlg`（Set 层语句面）上 exp 级数部分和尾界、柯西性与完备性 sigT | `exp_series_cauchy`/`bcauchy_complete_sig`（UpReqBanachExp.v） | 实数层正性链向 Banach 代数层的栈顶推广。范围外披露：B 路（Banach 推广）认证推进至实例面——exp 加法交换性 `UpReqBanachExpAddEq` 已闭合并云认证；exp_neg/可逆性侧（`ExpOppOne`/`InstPre`/`InstEMult`）与 `BanachCauchyD` 全部认证；实例面 `UpReqBanachInstReal` 与 `BanachNoHyp`/`BanachNoHypNorm` 等已闭合（HEAD=b657aff）。以上结果不改变本文四族 scoped claim； |
| Padé [n/n] 带符号逼近定义面：系数正性 `0 < pade_coeff n k`、分母对称 `pade_den n x == pade_num n (−x)`；非负递减序列有限交错和正性引擎 | `pade_coeff_pos`/`pade_den_sym`（UpReqPadeExp.v，200 行/9 Qed）；`altsum_pos_strict`（UpReqAltSumPos.v，677 行/34 Qed） | 定量带符号方向首砖不变（`pade_coeff_pos`/`altsum_pos_strict`）；C 路正尾线已闭合至 n=2 旗舰 `cpf_exp_pos_final_n2`（0<eˣ 的 n=2 定量面、零假设；配套 `UpReqPadeTailPos`/`BetaPos`/`DenPos12`/`Lower`/`Finale` 及 Q 层腿、符号迁移件），积分表示面仍登记为未完成项 |

**(c) 第三档（逐 eps 余量形）的代表性陈述**——保留 Or 语法但显式携带余量：

| 陈述 | 件名（文件） |
|---|---|
| `0 ≤ KL(p‖q) + ε`（∀ε>0） | `real_gibbs_inequality_eps`（CW 基座） |
| 步长 KL 控制 `Σ_i KL(p_i‖p_{i+1}) ≤ η·Σ_i KL(p_i‖r_i) + ε` | `real_step_kl_eta_bound_eps`（CW 基座）；接口前提消去形 `geod_step_kl_eta_bound_eps`（UpReqGeomD.v） |
| 逐出破缺复合界（inv·T·exp·(eps+eps′) 余量） | `real_db_breaking_bound_eps`（CW 基座）；Bishop 升格 `real_db_breaking_bound_B`（UpRealLeB2.v） |
| Min-P 投影质量界 | `real_minp_projection_eps_B`（UpReqMinPProjB.v） |
| exp 两点凸性、逐点 AM–GM | `real_exp_two_point_cvx_B`、`real_amgm_pointwise_B`（UpRealLeB.v） |

**(d) 补充形态（严格见证形）的代表性陈述**——严格正性**可以**构造性成立，但必须以显式见证为前提：

| 陈述 | 件名（文件） | 前提形态的启示 |
|---|---|---|
| 有限和 KL 严格正 | `klst_kl_sum_strict`（UpReqKLStrict.v） | 前提含某状态上 `p(s₀) < q(s₀)` 的显式严格见证 |
| 能量非常数 ⟹ KL 严格正 | `klst_kl_energy_nonconst`（UpReqKLEnergy，现并入 G07_KLWall.v：成员起点 G07:1984、主件 G07:2676，经实测核对） | 前提弱化为「存在 s₀：p(s₀) ≠ q(s₀)」的 Or 见证——「严格需见证」的标志性示例 |
| T→0 硬注意力极限、√d 构造 | `hard_attention_limit`、`real_sqrt_exists`（CW 基座） | ∃-量词翻转以 sigT 显式见证达成，构造性正例 |

#### 9.3.4 承载层与目录读法

上述三档的可证性差异不应与**陈述所在层**混淆。本库的主要定理群陈述于一个抽象接口；该接口的等式（setoid）对应物已由具体柯西实数端到端实例化（§9.2；逐定理承载路径对照见附录 B）。需要强调的一个结构性事实是：**抽象接口与其实例对个别序字段携带的强度并不相同**——抽象接口的 min–≤ 与 log 切线字段为第一档精确形，而实例化接口的对应字段已是第三档余量形；二者由同一命名字段连接，强度落差因此容易被「同形陈述」的表象遮蔽。本目录的读法即在此背景下才有意义：**对每一条头条陈述，读者应依次询问——它在抽象层以何种强度被假定（字段/前提），在实例层以何种强度被证明（第一/二/三档），以及是否存在严格见证形。** 凡实例层仅有第三档承载的陈述，正文在该定理陈述旁挂〔构造强度〕层标签（§4/§5/§7/§8 主要定理已逐个执行），不以无标记的序陈述面目出现。

**「复刻」用法的精确化（两类结论形态的保真度分界）。** 沿上述读法，本文在定理标签中对 Real 层对应物所用的两种措辞——「Real 层复刻」与「Real 层承载」——需要升格为一条显式规则，因为「逐 eps 复刻」是一个内在紧张的措辞：**复刻的保真度随结论形态分裂为两类**。其一，**恒等式层的复刻是真复刻**：等式档头条的 Real 层对应物以逐点 `real_eq` 相等承接同一恒等式（定理 5.2a/5.2b 的 softmax = Boltzmann、定理 5.3a 的稳态方程、定理 5.6c 的缩放-温度对偶），结论形态在抽象 `Id` 与 `real_eq` 之间同构对位，数学内容无损迁移——称其为「复刻」名实相符。其二，**不等式层的「复刻」实为弱化承载**：序档头条（如 Gibbs 非负 `KL ≥ 0`）的第一档精确形在具体实数层不可达（9.3.3(a)，零点可判定性缺失），其 Real 层对应物只能以第三档逐 eps 形或第二档 Bishop 形承接（`real_gibbs_inequality_eps`/`real_gibbs_inequality_B`）——此处「逐 eps」不是复刻的修辞，而是 Or 编码之下可达最强形态的登记（§3.5）。两类混称会使「复刻」一词同时掩盖「无损迁移」与「降档承载」这两种截然不同的关系。本文的执行规则即把 9.3.4 的读法逐定理落实：等式档头条一律标「Real 层复刻＝定理 5.2a 形」；序档头条一律标「Real 层最强承载为第 X 档形态」并附不可达机理（§4 定理 4.2 的〔构造强度〕标签即此格式的样例——「Real 层最强承载为第三档逐 eps 形……第一档精确形在具体实数层不可达」）。

#### 9.3.5 构造强度是形式化贡献的独立维度

通常的形式化贡献度量——定理数量、覆盖范围、公理依赖（`Print Assumptions` 输出）——都不分辨本节所刻画的维度：两条 `Print Assumptions` 均为「Closed under the global context」的定理，其构造性内容仍可以相差一个完整的序档位。以 Gibbs 不等式为例：第一档形态在具体实数层不可达、仅能以接口字段承载；第三档形态完全具体且携带定量余量；严格见证形态则以「存在分歧状态」的显式证据为前提——三者机器检查均为零公理，但可迁移给使用者的知识各不相同。我们因此主张：**对构造性形式化而言，「陈述强度档位」是与「是否机器检查」「公理依赖多少」并列的独立贡献维度**，应逐定理显式标注。本节目录即是这一标注在本库全部量化陈述上的执行结果；它同时解释了为什么本库的若干主要定理选择逐 eps 形态——那不是证明技术的妥协，而是 Or 编码之下该陈述的最强可达形态。该维度与 §9.2.2 的数学深度自评相互独立：深度自评分辨的是证明难度与分量定位，本节分辨的是陈述的逻辑强度，二者合成本文自评边界的完整刻画。

这一独立维度直接给出一个反直觉的系统性观察，本文将其显式登记为叙事层面的结论：**动力学侧陈述族的构造性地位系统性优于变分侧不等式族**。§4 的变分核承载着一族直觉上「基础」的不等式（Gibbs 非负、自由能最小化的序半边），但「非负性」在构造性逻辑下恰恰是被零点可判定性缺失锁死的形态——其具体实数层最强可达形态止步于第三档逐 eps 形/第二档 Bishop 形（9.3.3(a)）。与之相对，§5.5 的 Doeblin 收敛族——直觉上「更难」的收敛定理——天然携带自身的构造性见证：迭代收敛以 ∀ε>0 ∃N（sigT 见证）陈述（`attention_iterate_converges`）；收缩率以显式几何常数呈现（(1−δ)ⁿ；δ\* := e^{−2Δ/T} 且零 eps 损耗，定理 5.5/5.6）；温度两极以量词翻转极限闭合（∃T₀ sigT 见证，`hard_attention_limit`/`temp_window_T_infty`）——严格形与 ∃ 见证形正是构造性方法的强项（9.3.2 补充形态）。于是出现一个构造性逻辑特有的**地位反转**：直觉上「更难的」收敛型陈述反而处于更高的构造强度档位，「更基础的」非负不等式反而止步于弱化承载——这一分层在经典数学中不可见，在构造性档位维度上却是逐定理可机器检查的客观差异。本文登记该反转而不作方法论推断；其对形式化路线选择的具体含义（陈述形态的构造性代价应进入形式化对象的选取权衡）留作开放讨论（§10.2）。

#### 9.3.6 与既有构造性分析形式化的关系（重叠度注记）

适用限制如下。构造性柯西实数、setoid 代数层与逐 eps 序技术是成熟传统：CoRN/C-CoRN（Affeldt、Geuvers、Niqui、Spitters 等[18]）在统一库内建立了构造性实数的 setoid 主干与序的 Bishop 式处理；O'Connor 的认证逼近框架给出了 exp/log 等超越函数的构造性逐 eps 展开（§1.2/§3.1 所指先例线）。本库的第一档/第三档区分、≤_B 谓词及单向桥，在概念上均可在该传统中找到先例，我们不在此维度上主张原创性。本目录的增量定位有二：其一，**对象域**——被逐档标注的是量化机器学习的常见陈述族（KL 非负、格不等式、PPO/RLHF 最优性、策略迭代收缩率、截断采样界），此类陈述的强度目录在既有构造性形式化文献中未见系统整理；其二，**否定性结果的成目录化**——哪些陈述在 Or 编码下不可证、其不可证机理是什么、以何种替代形态可达，本库以机器检查工件（不可证性两侧的并置对照件、弱三分构造、否定式平方正定性）将它们固化为可检索条目。与 Infotheo/coq-proba[13]（经典逻辑下的信息论形式化，§2.4）的对照则属立场差异而非重叠：该线不面对本节的档位选择，恰构成本目录存在理由的外部印证。

---

## 10 结论与未来工作

### 10.1 结论

本文的主要贡献是构造性柯西实数基座上的逐 eps 定量技术，以及由此建立的截断采样与迭代动力学定量理论；FEP 数学核与 attention-Gibbs 桥是该基座上的应用案例，其价值在于前提显式化与跨域连通。全部结果在 Rocq/Coq 9.0/9.1 中机器检查，零全局公理、零 Admitted，并通过四项验证纪律；「首次」主张的 scoping 见 §2.4。

### 10.2 未来工作

各定理的验证状态与边界注记见表 A.1（附录 A）；以下仅列未完成项，已闭合项移入条目末的「已解决项」。

1. 多维/连续推广：将有限状态空间扩展到连续或高维离散空间。
2. **具体能量函数：query-key 点积到 logits 的绑定与显式收敛率管线（仅余末端一步）**：把 `z(s,s')` 具体化为查询-键点积 `(q_s · k_{s'})/√d`（d 为维数），闭成「一致范数界 → 双界 −Δ ≤ z ≤ Δ → δ* = e^{−2Δ/T} → (1 − e^{−2Δ/T})ⁿ」的单条机器检查管线（衔接 §5.5 定理 5.5/5.6）。**已闭合段（模块化树）**：前两段——有限和 C-S 的 Real 层逐 eps 形态（`real_cauchy_schwarz`/`_lt`，模块 `UpCS`，定理 5.7；反向不等式以 `real_cauchy_schwarz_reversed_false` 形式化为假命题）与「一致范数界 → 双界 logits」的界转化（`inner_sq_norm` → `real_logit_bound_of_norm_bounds` → `qk_logits_bounded`，模块 `UpQKBound`，定理 5.8）；任意维数（含非平方）的 √d 两层构造（`real_sqrt_exists` L96475 定理 5.6a / `sqrt_witness_exists_abstract` 定理 5.6d）；Doeblin 端的抽象层承接（`bs_minorization` L96286 与 `bounded_softmax_tv_iter` L96344，定理 5.5/5.6）与双点收缩的 Real δ 接口形态（`tv_doeblin_contraction`/`tv_doeblin_iter`，定理 5.10，模块化树（补充材料 S2）在树件）。**仍开放（末端一步，截至库状态快照 HEAD=39d81aa；库内未见把该组合并为单一定理的后续件）**：显式 Δ 的 δ\* := e^{−2Δ/T} 实例引理已在树内闭合——模块化树（补充材料 S2） Part 2 以双界 logits（|z| ≤ γ，γ 即正文 Δ）为前提证得 `tvd_dstar_instance`（δ 接口字段面被显式常数满足）与 `tvd_dstar_iter_contraction`（显式率 (1−e^{−2γ/T})ⁿ），经实测核对；尚余 `UpQKBound`（现 G10）界转化输出与 `UpTVDoeblin` 前提的模块级组合证明尚未完成、未并为单一定理形态（`UpQKBound` 文件头明示该下游件不在本文件范围）；当前认证面 246/246，CI 连续 success。构造性注意点（陈述）：一致范数界取「根有界」形态（对每个查询 s 直接陈述 `‖q_s‖ ≤ Q`，以 `real_sqrt_exists` 的根为前提，而非平方形态 `‖q_s‖² ≤ Q²`）——由 `A² ≤ Q²` 与 A ≥ 0 构造性推不出 `A ≤ Q`（`real_weak_trich` L38268 仅以双否定形式给出相等、不是三分），该 Or 编码现象作为注记随定理一并陈述（§5.5）。**该缺口的分量供给现状（已机器检查，模块层）**：库内另有一支与 logits 幅度界直接相关的已证族——模块 `AttnLogSumExpBound` 的逐 logit 配分控制 `attn_logit_le_log_partition`（`s ∈ ss ⟹ s ≤ log Σ_t e^{z_t}`）、log-配分型上界 `attn_log_partition_bound` 与倾斜配分恒等 `attn_tilted_eq`；其结论为单侧、与 `UpQKBound`→`UpTVDoeblin` 的组合**非同一命题**，故不构成末端一步的闭合（详见 §9.2 边界 3）。
**已解决项（一）｜动态收敛：KV 逐出 × Doeblin 双点收缩的逐出漂移定理（已闭合）**：KV 逐出与收敛框架的对接已在模块化树内机器检查——`u_tv_contraction`（L95931）的免平稳性是该形态成立的基础；逐出核 `K_ev` 与完整核的双核迭代漂移界已由模块 `UpKVDrift` 闭合为定理 6.3（`kv_drift_bound`：TV(K_evⁿ μ, Kⁿ μ) ≤ n·c + eps，∀n 有限 n、无平稳分布主张；一致行误差常数 c 为显式前提；控制量取行 TV，`kev_row_tv_one_minus_Z`：tv_row == 2·(1 − Z_keep)，§6.2.2）；配套的正结果为破缺恒为零（定理 6.2，`eviction_db_breaking_zero`，模块 `UpEvictId`）与截断核稳态保持（`evicted_boltzmann_steady_exact`）。`top_k_tail_bound` 的更紧 TV 界已由定理 7.6 的精确恒等承载。生成序列遍历性/稳态分布的极限主张维持不主张立场（§9.2 边界 7）。
3. top-p / nucleus 采样与组合策略（现状：核心已形式化）：`Section TopPSampling` 已建立概率降序的构造性插入排序（insert_kernel/sort_kernel）、前缀累积（prefix_sum）、top-p 保留判定（top_p_member/top_p_keep）及成员/支配性引理（sort_kernel_mem/insert_kernel_head_ge）；阈值形式 nucleus 核 topp_keep（保留 kernel ≥ p）带非空性 topp_temp_sum_pos（p ≤ max 前提）与核归一化 `topp_markov_kernel_normalized`（Σ=1），零 `Admitted`、纯构造性。Top-p + Min-P 联合核（阈值形式）：combined_keep（minp_keep ∧ topp_keep，可判定 combined_keep_dec）、非空性 combined_temp_sum_pos（p ≤ max 前提 ⟹ pick_max 双满足）、联合核归一化 `combined_markov_kernel_normalized`（Σ=1）——组合策略的构造性形式化（阈值形式绕开排序正确性障碍）。Top-k + Min-P 联合核（计数形式）：topk_keep（严格更重者计数 < K，count_kernel_heavier/NatLt_tk，沿用主文件 keep_top_k 计数模式）、可判定 topk_keep_dec（Nat.ltb 计算）、联合保留 combined_topk_keep（minp_keep ∧ topk_keep，可判定 combined_topk_keep_dec）、非空性 combined_topk_temp_sum_pos（K ≥ 1 且诚实前提 topk_pickmax_head：pick_max 在前 K 个中）、联合核归一化 `combined_topk_markov_kernel_normalized`（Σ=1）。仍开放：生成序列的遍历性与稳态分布（维持 §9.2 边界 7 的不主张立场；已解决项（一）的有限 n 漂移界（定理 6.3）为朝向它的第一个定量步）。
4. 提取与验证：将抽象 `R` 提取到 OCaml float，并给出浮点误差界。
5. Min-P 完整可计算误差估计：KL ≤ S 复合熵链已闭合（§8.7），完整的可计算误差估计仍开放（§8.5 注记、§9.2 边界 6）。

**已解决项（二）｜抽象 Id 系陈述 → setoid 实例的整体签名迁移（已闭合）**：734 件全数落位，670 件交付四项验证，64 件保留为抽象层与实例层两套陈述并行；statement-level 机器对齐（人工逐条 diff，附录 B）为迁移范围外的论文自留项。

---

## 参考文献

1. Friston, K. (2010). The free-energy principle: a unified brain theory? *Nature Reviews Neuroscience*.
2. Buckley, C. L., et al. (2017). The free energy principle for action and perception: A mathematical review. *Journal of Mathematical Psychology*.
3. Blei, D. M., Kucukelbir, A., & McAuliffe, J. D. (2017). Variational inference: A review for statisticians. *Journal of the American Statistical Association*.
4. Vaswani, A., et al. (2017). Attention is all you need. *NeurIPS*.
5. Hopfield, J. J. (1982). Neural networks and physical systems with emergent collective computational abilities. *PNAS*.
6. Krotov, D., & Hopfield, J. J. (2016). Dense Associative Memory for Pattern Recognition. *Advances in Neural Information Processing Systems 29 (NIPS 2016)*. arXiv:1606.01164. https://arxiv.org/abs/1606.01164
7. Ramsauer, H., et al. (2021). Hopfield Networks is All You Need. *ICLR 2021*. arXiv:2008.02217. https://arxiv.org/abs/2008.02217
8. Fan, A., Lewis, M., & Dauphin, Y. (2018). Hierarchical Neural Story Generation. *ACL 2018*. arXiv:1805.04833. https://arxiv.org/abs/1805.04833
9. Holtzman, A., Buys, J., Du, L., Forbes, M., & Choi, Y. (2020). The Curious Case of Neural Text Degeneration. *ICLR 2020*. arXiv:1904.09751. https://arxiv.org/abs/1904.09751
10. Nguyen, M. N., Baker, A., Neo, C., Roush, A., Kirsch, A., & Shwartz-Ziv, R. (2024). Turning Up the Heat: Min-p Sampling for Creative and Coherent LLM Outputs. *ICLR 2025*（oral）. arXiv:2407.01082. https://arxiv.org/abs/2407.01082
11. Zhang, Z., Sheng, Y., Zhou, T., Chen, T., Zheng, L., Cai, R., Song, Z., Tian, Y., Ré, C., Barrett, C., Wang, Z., & Chen, B. (2023). H2O: Heavy-Hitter Oracle for Efficient Generative Inference of Large Language Models. *NeurIPS 2023*. arXiv:2306.14048. https://arxiv.org/abs/2306.14048
12. Hibon, Q., & Paulson, L. C. (2016). Source Coding Theorem. *Archive of Formal Proofs*. https://www.isa-afp.org/entries/Source_Coding_Theorem.html（访问日期：2026-09-10；Isabelle/AFP 信息论条目：Shannon 信源编码定理的熵下界半边；Markov/遍历侧另有 Markov Models（Hölzl, J., & Nipkow, T., 2012）与 Ergodic Theory（Gouëzel, S., 2015）等同库条目）
13. Affeldt, R., & Hagiwara, M. (2014). Formalization of Shannon's Theorems. *Journal of Automated Reasoning* 53(1):63–103. https://doi.org/10.1007/s10817-013-9298-1；库：coq-proba / Infotheo（Rocq 库，含离散概率、相对熵、互信息、AEP 与线性纠错码），https://github.com/affeldt-aist/infotheo（访问日期：2026-09-16）。
14. Rafailov, R., Sharma, A., Mitchell, E., Manning, C. D., Ermon, S., & Finn, C. (2023). Direct Preference Optimization: Your Language Model is Secretly a Reward Model. *NeurIPS 2023*. arXiv:2305.18290. https://arxiv.org/abs/2305.18290
15. Hinton, G., Vinyals, O., & Dean, J. (2015). Distilling the Knowledge in a Neural Network. arXiv:1503.02531. https://arxiv.org/abs/1503.02531
16. Guo, C., Pleiss, G., Sun, Y., & Weinberger, K. Q. (2017). On Calibration of Modern Neural Networks. *ICML 2017*. arXiv:1706.04599. https://arxiv.org/abs/1706.04599
17. Blanchard, P., Higham, D. J., & Higham, N. J. (2021). Accurately Computing the Log-Sum-Exp and Softmax Functions. *IMA Journal of Numerical Analysis* 41(4):2311–2330. MIMS EPrints 2765. https://eprints.maths.manchester.ac.uk/2765/
18. C-CoRN: The Constructive Coq Repository at Nijmegen. Version [commit/tag], https://github.com/rocq-community/corn（访问日期：2026-09-13）.
19. Constable, R. L., et al. (1986). *Implementing Mathematics with the Nuprl Proof Development System*. Prentice Hall.
20. Hewitt, J., Manning, C. D., & Liang, P. (2022). Truncation Sampling as Language Model Desmoothing. *Findings of EMNLP 2022*. arXiv:2210.15191. https://arxiv.org/abs/2210.15191
21. Meister, C., Pimentel, T., Wiher, G., & Cotterell, R. (2023). Locally Typical Sampling. *Transactions of the Association for Computational Linguistics* 11. arXiv:2202.00666. https://arxiv.org/abs/2202.00666
22. Jaynes, E. T. (1957). Information theory and statistical mechanics. *Physical Review* 106(4):620–630.
23. Doeblin, W. (1938). Exposé de la théorie des chaînes simples constantes de Markov à un nombre fini d'états. *Revue Mathématique de l'Union Interbalkanique* 2:77–105.
24. Dobrushin, R. L. (1956). Central limit theorem for nonstationary Markov chains. I. *Theory of Probability and its Applications* 1(1):65–80.
25. Levin, D. A., Peres, Y., & Wilmer, E. L. (2009). *Markov Chains and Mixing Times*. American Mathematical Society.
26. Ouyang, L., Wu, J., Jiang, X., Almeida, D., Wainwright, C., Mishkin, P., Zhang, C., Agarwal, S., Slama, K., Ray, A., et al. (2022). Training language models to follow instructions with human feedback. *NeurIPS 2022*. arXiv:2203.02155. https://arxiv.org/abs/2203.02155
27. Hölzl, J. (2016). Markov Chains and Markov Decision Processes in Isabelle/HOL. *Journal of Automated Reasoning* 59(3):345–387. https://doi.org/10.1007/s10817-016-9401-5
28. The mathlib Community (2020). The Lean Mathematical Library. *CPP 2020*. arXiv:1910.09336. https://arxiv.org/abs/1910.09336
29. Audebaud, P., & Paulin-Mohring, C. (2009). Proofs of randomized algorithms in Coq. *Science of Computer Programming* 74(8):568–589. https://doi.org/10.1016/j.scico.2007.09.002
30. Bagnall, A., & Stewart, G. (2019). Certifying the True Error: Machine Learning in Coq with Verified Generalization Bounds. *AAAI 2019*. https://ojs.aaai.org/index.php/AAAI/article/view/4115
31. Li, C., Wang, Z., He, W., Wu, Y., Xu, S., & Wen, Z. (2025). Formalization of Convergence Rates of Four First-order Algorithms for Convex Optimization. *Journal of Automated Reasoning* 69(4), Art. 28. https://doi.org/10.1007/s10817-025-09741-w（arXiv:2403.11437）
32. Alshiekh, M., Bloem, R., Ehlers, R., Könighofer, B., Niekum, S., & Topcu, U. (2018). Safe Reinforcement Learning via Shielding. *AAAI 2018*. arXiv:1708.08611. https://arxiv.org/abs/1708.08611
33. Katz, G., Barrett, C., Dill, D. L., Julian, K., & Kochenderfer, M. J. (2017). Reluplex: An Efficient SMT Solver for Verifying Deep Neural Networks. *CAV 2017*. arXiv:1702.01135. https://arxiv.org/abs/1702.01135
34. Friedman, D. A. (2026). Towards Lean 4 Formalization of the Free Energy Principle: AI-Driven Theorem Sketching and Verification for Active Inference and Bayesian Mechanics. *Active Inference Journal*. https://doi.org/10.5281/zenodo.19699233 （FEP_Lean v1.1.0：Lean 4 + Mathlib，155 主题 / 20 族，155/155 sorry-free；作者明言不证明 FEP 作为物理理论）
35. Li, H., Li, Q., Li, Y., et al. (2024). A Survey on Large Language Model Acceleration based on KV Cache Management. arXiv:2412.19442. https://arxiv.org/abs/2412.19442
36. Xiao, G., Tian, Y., Chen, B., Han, S., & Lewis, M. (2024). Efficient Streaming Language Models with Attention Sinks. *ICLR 2024*. arXiv:2309.17453. https://arxiv.org/abs/2309.17453 （attention sink：首段 KV 不可驱逐的经验依据）
37. Liu, Z., Desai, A., Liao, F., et al. (2023). Scissorhands: Exploiting the Persistence of Importance Hypothesis for LLM KV Cache Compression at Test Time. *NeurIPS 2023*. arXiv:2305.17118. https://arxiv.org/abs/2305.17118
38. Bretagnolle, J., & Huber, C. (1979). Estimation des densités : risque minimax. *Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete* 47(2):119–137. https://doi.org/10.1007/BF00534262 （TV ≤ √(1 − e^{−KL})：KL→TV 传递的免常数替代路线，与本文 δ* = e^{−2Δ/T} 形态同构）
39. Pinsker, M. S. (1964). *Information and Information Stability of Random Variables and Processes*. Holden-Day.（俄文原版 1960；TV ≤ √(½·KL) 的来源）
40. Kullback, S., & Leibler, R. A. (1951). On Information and Sufficiency. *Annals of Mathematical Statistics* 22(1):79–86. https://doi.org/10.1214/aoms/1177729694
41. Csiszár, I. (1975). I-Divergence Geometry of Probability Distributions and Minimization Problems. *The Annals of Probability* 3(1):146–158. https://doi.org/10.1214/aop/1176996454
42. Degenne, R. (2025). Markov Kernels in Mathlib's Probability Library. arXiv:2510.04070. https://arxiv.org/abs/2510.04070
43. Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437

---

## 附录 A：核心定理清单

正文使用定理编号与稳定标签；完整行号索引、逐字语句与模块路径见补充材料 S1。

| 定理 | 行号 | 内容摘要 |
|---|---|---|
| `free_energy_kl_decomp` | L16259 | F[p] = F[p_b] + D·KL(p‖p_b) |
| `gibbs_inequality` | L16629 | KL(p‖q) ≥ 0 |
| `gibbs_equality` | L16678 | KL=0 ⟹ p=q |
| `min_free_energy_is_boltzmann` | L16838 | Boltzmann 最小化自由能 |
| `free_energy_min_unique` | L16888 | 自由能最小点唯一 |
| `max_entropy_is_boltzmann` | L17069 | 最大熵对偶 |
| `entropy_deficit_kl_temp` | L17691 | 定理 4.6a：熵亏 = KL 的温度版（同约束能量） |
| `max_entropy_is_boltzmann_temp` | L17726 | 定理 4.6b：温度版最大熵（同能量 ⟹ S[p] ≤ S[p_t]） |
| `entropy_max_unique_temp` | L17763 | 定理 4.6c：温度版唯一性（同能量 + 同熵 ⟹ 逐点相等） |
| `temp_energy_dual_closed` | L17788 | 定理 4.6d：温度参数化对偶闭合（sigT 见证，存在唯一 + 最优） |
| `energy_exp_temp_strict_mono` | L18019 | 定理 4.6e：温度-能量严格单调（对称 KL 恒等核心） |
| `elbo_lower_bound` | L18359 | ELBO ≤ 证据 |
| `elbo_tight` | L18520 | 等号条件 |
| `training_equivalence` | L18657 | 训练等价性 |
| `steady_state_boltzmann` | L15692 | Boltzmann 稳态分布 |
| `fep_align` | L112201 | 定理 5.1（premise-free 主定理）：Boltzmann 分布（base := −z、Zf）逐点 == softmax_temp z，无配分函数前提（Section `FEPAttention`；推论 5.1a/5.2 的前提消去承载） |
| `attention_is_gibbs` | L28606 | 推论 5.1a：单位温度 softmax = Boltzmann（带前提形态） |
| `attention_is_gibbs_temp` | L28634 | 推论 5.2：任意温度对应（带前提形态） |
| `steady_state_boltzmann_attn` | L28722 | 注意力稳态 = Boltzmann（稳态方程验证，详细平衡 + 行归一化前提） |
| `attention_tv_contraction` | L29195 | 单步 TV 收缩（Doeblin）：TV(attention_step μ, p_b) ≤ (1−δ)·TV(μ, p_b)（μ 归一化非负；δ/minorization 前提 L28756–L28759） |
| `attention_tv_iter_contraction` | L29287 | 几何迭代收缩：TV(iterate n μ0, p_b) ≤ (1−δ)ⁿ·TV(μ0, p_b) |
| `attention_iterate_converges` | L29330 | 迭代收敛：∀ eps>0，∃ N，n ≥ N ⟹ TV_n < eps（sigT 见证，初始 TV>0——TV=0 平凡情形恒收敛，见 §5.5；几何击穿经显式前件 r_arch_pow_attn L29247） |
| `eviction_steady_deviation` | L29626 | 逐出稳态偏差控制（三角不等式，非定量估计） |
| `db_breaking` | L29375 | 逐对详细平衡破缺项定义 |
| `eviction_partition_monotone` | L29485 | 保留分区单调性 |
| `top_k_majorization` | L30047 | Top-k 支配性（计数版） |
| `top_k_majorization_mem` | L30264 | Top-k 支配性（排序成员版） |
| `top_k_swap_no_gain` | L30073 | 交换不获益 |
| `top_k_tail_bound` | L29719 | 尾部质量 ≤ Z_thermo |
| `tail_plus_kept_full` | L29732 | 质量守恒 |
| `exp_pos_fn` | L27950 | 正指数函数 e^x := exp_neg(−x)（softmax 分子） |
| `softmax` | L27972 | 标准 softmax（e^{z}/Σe^{z}） |
| `softmax_temp` | L28104 | 带温度 softmax（e^{z/T}/Σe^{z/T}） |
| `scale_temp_duality` | L28524 | 缩放-温度对偶：∀ c>0，以 1/c 缩放 logits 的 softmax == 温度 c 的 softmax（纯恒等链，零新公理） |
| `sqrt_witness` | L28552 | 平方维数见证 sqrt_witness d r := r·r == d（无 sqrt 符号） |
| `scale_sqrt_witness_dual` | L28565 | d=k² 见证式下以 1/r 缩放 == 温度 r 的 softmax（scale_temp_duality 的 r 实例） |
| `scale_inv_T_eq_softmax_temp` | L28679 | 1/T 缩放族 == 库内温度化 softmax |
| `scaled_attention_is_gibbs_temp` | L28694 | 缩放 attention == Boltzmann（前提 1/T = 1/D、energy = −z、配分匹配） |
| `rlhf_free_energy_kl` | L20290 | RLHF 目标 ↔ 自由能-KL 分解（§9.1 共享结构锚点） |
| `minp_keep` | L30930 | Min-P 保留判定 |
| `minp_keep_dec` | L30933 | Min-P 保留判定可判定 |
| `pick_max_token_minp_keep` | L30954 | 最大概率 token 必被保留（截断集非空） |
| `minp_temp_sum_pos` | L30981 | Min-P 截断分母正性 |
| `minp_markov_kernel_nonneg` | L31022 | Min-P 核非负 |
| `minp_markov_kernel_keep_pos` | L31036 | Min-P 核正性（保留者） |
| `minp_markov_kernel_normalized` | L31050 | Min-P 核归一化 |
| `minp_temp_sum_le_partition` | L31112 | 截断和 ≤ 完整和 |
| `minp_markov_kernel_keep_ge_full` | L31127 | 保留者核 ≥ 完整核（单调性，非定量） |
| `minp_markov_kernel_dropped_zero` | L31147 | 逐出者核 = 0 |
| `minp_dropped_mass_le_inv_vocab_size` | L31849 | 截断质量 ≤ 1 − 1/\|S\|（词表大小挂钩，13 引理链） |
| `topk_tv_identity_strict` | L30638 | TV(boltzmann, topk_renorm) == tail_mass/Z_thermo（条件化精确恒等，19 引理） |
| `u_tv_contraction` | L95931 | 双点 TV 收缩：TV(u_step μ, u_step ν) ≤ (1−δ)·TV(μ,ν)——免平稳/免详细平衡/免 μ 非负，参考分布任意归一化（定理 5.4） |
| `u_tv_iter` | L96019 | 双点几何迭代收缩：(1−δ)ⁿ（定理 5.4） |
| `bs_kernel` | L96247 | 有界 logits 温度 softmax 核（行随机，transition 的显式构造） |
| `bs_minorization` | L96286 | 显式 Doeblin 下界：δ*·U ≤ bs_kernel（δ* := lo·lo = e^{−2Δ/T}，零余量损耗；定理 5.5） |
| `bounded_softmax_tv_contraction` | L96331 | 有界 softmax 核单步 TV 收缩，收缩率显式 1 − e^{−2Δ/T}（定理 5.6） |
| `bounded_softmax_tv_iter` | L96344 | 迭代几何收缩：(1 − e^{−2Δ/T})ⁿ（定理 5.6） |
| `real_expf_realizable` | L96364 | expf 迷你接口在 cauchy_real_exp 上的 Real 层由具体实例满足（sigT+And；定理 5.6b） |
| `real_sqrt_exists` | L96475 | Real 层任意 d ≥ 0 构造性平方根（sigT，r ≥ 0 ∧ r·r == d；非平方 d 覆盖；定理 5.6a） |
| `sqrt_witness_nat_sq` | L96596 | 抽象层任意 k 的 k² 维数见证：sqrt_witness (nat_to_R (k·k)) (nat_to_R k) |
| `scale_dual_nat_sq_k` | L96622 | k² 维数对偶实例：1/(S k) 缩放 == 温度 S k（任意 k ≥ 1） |
| `core_decay_bound` | L97265 | Real 层逐点衰减：x ≠ m ⟹ w_T(x) ≤ e^{−γ/T}（闭合状态见 §5.4(a)） |
| `eq_inv2_double` | L97558 | inv2·(X+X) == X（TV 的二分之一折叠代数件） |
| `tv_hard_le_decay_scale` | L97618 | TV 总质量侧闭合：TV(w_T, δ_m) ≤ \|vocab\|·e^{−γ/T}（§5.4(a)） |
| `hard_attention_limit` | L97679 | T→0 硬注意力极限（∃T₀ 量词翻转，机器检查）：∀ eps>0，∃ T₀>0，∀ 0<T<T₀：TV(w_T, δ_m) ≤ eps（§5.4(a)） |
| `attention_minimizes_free_energy_unique` | L112225 | attention = 变分自由能唯一最小点：F_T[p] = −E_p[z] + T·Σp log p 在 softmax_temp z 处唯一取最小（§5.4(b)/§9.1） |
| `bs_kernel_row_is_softmax_temp` | L112281 | 逐行等价：bs_kernel 的每一行 == 单查询 softmax_temp（经 expf_agree 前提；§5.5 边界声明） |
| `UpExtras219.free_energy_softmax_eq_neg_T_logZ` | L114089 | log-sum-exp == −T·log Z：F_T[softmax_temp(z)] == −T·log Z_T(z)（最小点处精确自由能值；§5.4(b)） |
| `temp_window_T_infty` | UpTempWindow L1563 | T→∞ 温度窗口：∀eps>0, ∃T₂>0, ∀T>T₂, TV(w_T,U) ≤ eps（sigT 量词翻转；§5.4(a)；模块化树 + Extensions + 单文件） |
| `real_attention_is_gibbs_temp` | UpDebtGibbsT L160（现并入 G02_Debt.v，组内 L601） | 任意温度同构的 Real 层复刻（定理 5.2b） |
| `real_scale_temp_duality` | UpDebtDual L219（现并入 G02_Debt.v，组内 L358） | 缩放-温度对偶 Real 层（定理 5.6c） |
| `sqrt_witness_exists_abstract` | UpDebtSqrtAbs L76（现并入 G02_Debt.v，组内 L79） | 抽象 Id 层任意非负 d 平方根见证（定理 5.6d；√d 两层全闭） |
| `real_cauchy_schwarz_lt` / `real_cauchy_schwarz` / `real_cauchy_schwarz_reversed_false` | UpCS L234 / L284 / L374 | 有限和 C-S Real 层：严格版 / 平方版 / 反向假命题的形式化反驳（定理 5.7） |
| `inner_sq_norm` / `real_logit_bound_of_norm_bounds` / `qk_logits_bounded` | UpQKBound L862 / L1142 / L1299（现并入 G10_LoebFam.v，组内 L2361 / L2641 / L2798） | QKᵀ 界转化链：根有界前提 ⟹ 显式 Δ（定理 5.8；仅模块化树，Extensions/单文件快照未含） |
| `attention_iterate_converges_real` / `r_arch_pow_attn_real` | UpArchAttn L171 / L90 | steady_state 迭代收敛的 Real 镜像（定理 5.9） |
| `tv_doeblin_contraction` / `tv_doeblin_iter` | UpTVDoeblin.v L884 / L1564（树兼容重建件；原 UpTVReal 存档件 L801 / L1481） | 双点 TV 收缩 Real 复刻，δ 接口形态（定理 5.10；已并入模块化树，0 Admitted；其 Part 2 并闭合显式 δ\* 实例） |
| `eviction_db_breaking_zero` / `evicted_boltzmann_steady_exact` | UpEvictId L185 / L202（现并入 G13_EvictFam.v，组内 L188 / L205） | 破缺恒为零（定理 6.2）/ 截断核稳态方程精确式（§6.2.2） |
| `Z_keep_pos` / `kev_row_tv_exact` / `kev_row_tv_one_minus_Z` | UpKVDrift L127 / L996 / L1035 | 行 TV 控制量族（tv_row == 2·(1 − Z_keep)；§6.2.2） |
| `kv_drift_bound` / `kv_drift_bound_tv` | UpKVDrift L2161 / L2217 | 有限 n 漂移界 TV(K_evⁿμ, Kⁿμ) ≤ n·c + eps（定理 6.3；仅模块化树，快照未含） |
| `entropy_ge_neg_log_p_max` / `dropped_le_one_minus_exp_neg_S` / `dropped_le_one_minus_inv_n` | UpMinP L728 / L830 / L895 | Min-P 熵刻画：S ≥ −log p_max / dropped ≤ 1−e^{−S} / 定理 8.9 降为推论（§8.5 注记） |
| `real_minp_kernel_is_projection` / `real_Z_aud_is_kept_mass` / `real_minp_kl_cost` / `real_minp_projection_eps` | UpAuditBridge L566 / L588 / L1019 / L1070 | KL 投影解释 Real 实例族：投影桥 / 配分恒等 / 精确代价 / 投影不等式（§8.7） |


### 表 A.1：全文结果族—定理—验证状态—PA 口径—所在节

正文散落的验证/边界状态句一律指向本表。

| 结果族 | 代表定理 | 四项验证 | PA 口径时点 | 所在节 |
|---|---|---|---|---|
| FEP 数学核 | free_energy_kl_decomp、gibbs_inequality、min_free_energy_is_boltzmann、elbo_lower_bound | 通过 | 2026-09-04 批量 PA 快照；其后新增件按编译期审计 | §4.1–§4.3、§4.5 |
| FEP 数学核（Real 层载体，模块层） | fekl_gap_decomp_general、fekl_fep_gap_le_b、fekl_fep_gap_canonical_le_b、fekl_fep_gap_eps（模块 FreeEnergyKLGap）；fekl_sf_vfe_ge_complexity_B 属定义性后承 | 通过 | 模块层，内核校验覆盖；不并入正文主张 | §9.2 第 9 项 |
| FEP 数学核（温度参数化） | entropy_deficit_kl_temp、max_entropy_is_boltzmann_temp、entropy_max_unique_temp、temp_energy_dual_closed、energy_exp_temp_strict_mono | 通过 | 同上 | §4.4 |
| FEP 数学核（稳态/训练） | steady_state_boltzmann、training_equivalence | 通过 | 同上 | §4.6–§4.7 |
| 注意力-Gibbs 桥 | fep_align、attention_is_gibbs、attention_is_gibbs_temp、steady_state_boltzmann_attn | 通过 | 2026-09-04 批量 PA 快照 | §5.2–§5.4 |
| 注意力-Gibbs 桥（迭代/TV） | attention_tv_contraction、attention_tv_iter_contraction、attention_iterate_converges、bs_minorization、bounded_softmax_tv_contraction | 通过 | 同上；迭代族未逐条重跑批量 PA，按编译期审计 | §5.5 |
| 截断采样（Top-k） | top_k_majorization、top_k_swap_no_gain、topk_tv_identity_strict | 通过 | 2026-09-04 批量 PA 快照（topk_tv_identity_strict 在列） | §7 |
| 截断采样（Min-P） | minp_markov_kernel_normalized、minp_markov_kernel_keep_ge_full、minp_dropped_mass_le_inv_vocab_size、dropped_le_one_minus_exp_neg_S | 通过 | 同上；熵刻画件按编译期审计 | §8 |
| KV 驱逐 | eviction_steady_deviation、eviction_db_breaking_zero、kv_drift_bound、real_db_breaking_bound_eps | 通过 | 2026-09-04 批量 PA 快照（real_db_breaking_bound_eps 在列） | §6 |
| 统一视角 | rlhf_free_energy_kl、attention_minimizes_free_energy_unique、free_energy_softmax_eq_neg_T_logZ | 通过 | 同上；后两件按编译期审计 | §9.1 |
| 库状态对齐 | HEAD=39d81aa；编译清单 246 模块；Live_X 356 个 .v；CI success；认证面 246/246；81 条 PA 待执行； | — | 2026-09-16 库状态快照 | 附录 C |
| 边界注 | 双点收缩 Real 层 δ 接口复刻（定理 5.10）已入模块化树；setoid/req 迁移未完成；query-key 点积到 logits 末端绑定未完成；真实 Transformer 浮点/多头/掩码未形式化 | — | — | §5.5、§9.2、§10.2 |

四项验证定义：全量编译退出码 0；Print Assumptions 返回 Closed under the global context；提取验证无 Obj.magic；coqchk 内核校验通过。审计日志见补充材料 S3。


## 附录 B：抽象 Id 系 ↔ setoid 实例 ↔ Real 层复刻 端到端实例化对照表

**用途**：把「三路径并行、无 statement-level 机器对齐」的现状显式化。下表行号均为基座内容锚（SHA `7BBE42EA…`，114,222 行）内经实测核对的坐标；该 SHA 为历史参考基线，当前库状态以 HEAD=39d81aa 为准（编译清单 246 模块，Live_X 356 个 .v，见表 A.1「库状态对齐」行与附录 C；），行号仅作参考坐标，稳定标签优先。「机器对齐现状」两档含义如下。

- **单文件同库编译对齐**：抽象接口字段与 setoid 实例字段位于同一 Coq 文件，实例的字段赋值（如 `exp_neg_pos := cauchy_real_exp_pos`）经 Coq 类型检查在编译期与字段签名一致——即该行的编译级一致性由同一编译单元保证。
- **开放：需逐条 diff**：抽象主要定理与 Real 层复刻是**两条独立陈述、各自完成证明**，库内没有任何工具（statement-level diff）机器检查二者「逐字对应」，目前只靠人工逐条比对；下表即当前的人工比对记录。同库编译只保证每条陈述自身成立，不保证两条陈述互为翻译。

| 抽象 Id 系（`RealInterfaceEnhanced` 族） | setoid 实例对应 | Real 层对应（若有） | 代码锚点（经实测核对） | 机器对齐现状 |
|---|---|---|---|---|
| 接口字段 `exp_neg_pos`（RealInterface，L133 Class；字段 L182） | `Real_RealInterfaceSetoid`（L39407）`exp_neg_pos := cauchy_real_exp_pos`（L39450）；`RealEnhancedReal`（L41115）`exp_neg_pos := real_exp_neg_pos`（L41196） | `cauchy_real_exp_pos`（L13383）；`real_exp_neg_pos`（L40323） | L182 / L39450 / L41196 / L13383 | 单文件同库编译对齐（Instance 字段赋值即机器检查） |
| 接口字段 `log_inv`（Id 系无正性前提 L186；setoid 系带正性前提 L32737） | `log_inv := cw_log`（L39453）；`log_inv_exp_neg/one/mult := log_inv_*_thm`（L39454–L39456）；增强版 `log_inv := real_log_inv`（L41205） | `cw_log`（L38016）；`log_inv_exp_neg_thm`（L38421）/`log_inv_one_thm`（L38443）/`log_inv_mult_thm`（L38471） | L186 / L32737 / L39453–L39456 / L41205 / L38016 | 单文件同库编译对齐；**注意**：Id 系 `log_inv` 无正性前提、setoid 系带前提，两系字段签名本身不同（§9.2 边界），非逐字同一字段 |
| 接口字段 `inv_pos_le_compat`（RealInterfaceEnhanced，L217 Class；字段 L249） | setoid 增强字段 L40526；`RealEnhancedReal` `inv_pos_le_compat := real_inv_pos_le_compat`（L41170） | `real_inv_pos_le_compat`（L39333） | L249 / L40526 / L41170 / L39333 | 单文件同库编译对齐 |
| metric / lim / cauchy_complete 字段 | `Real_RealInterfaceSetoidCore`（L33433，Core 实例）；`cauchy_complete := RealSetoid.real_cauchy_complete_metric_natle`（L39464 / L41215） | `real_cauchy_complete_metric_natle`（L33401） | L33433 / L39464 / L41215 / L33401 | 单文件同库编译对齐 |
| 定理 4.2 `gibbs_inequality`（抽象 Id 系） | —（未在 setoid 签名下重述） | `real_gibbs_inequality_eps`（L41704，Real 层逐 eps 完整版，list 状态空间） | L16629 / L41704 | 开放：需逐条 diff（Real 层为逐 eps 强化版，非逐字复刻） |
| 定理 4.1 `free_energy_kl_decomp`（抽象 Id 系） | —（未迁移） | Real 层自由能-KL 分解：`real_kl_sum_decomp`（L43740，已证）；完整分解对应件已建成——`rkd_kl_decomp_full`/`rkd_kl_decomp_full_partition` 已闭合（主文件 `real_kl_decomp_full` L43730 的显式前件 Variable 旧形态已被取代）；req 系完整分解已证载体 `rfep_real_kl_decomp_full`（模块 `UpReqRealFEP`；规范化引理 `real_kl_decomp_full_canon`，模块 `UpReqFEPCanon` L48 直接实例化） | L16259 / L43740 / L43730 / `UpReqRealFEP` | 已证在库（`rkd_kl_decomp_full`/`rkd_kl_decomp_full_partition`；req 载体 `rfep_real_kl_decomp_full` + 规范化引理 `real_kl_decomp_full_canon`）；余 statement-level 人工 diff |
| 推论 5.1a `attention_is_gibbs`（L28606；premise-free 主定理 5.1 `fep_align` 见 L112201） | `attention_is_gibbs_setoid`（L66294，req 签名，Section `AttentionGibbsBridgeSetoid` L66137–66414） | `real_attention_is_gibbs`（L43231，RealAttnMain） | L28606 / L112201 / L66294 / L43231 | setoid：已迁移（Id→req 直证）；Real 层：开放：需逐条 diff（人工比对一致；Real 层仅单位温度版） |
| 推论 5.2 `attention_is_gibbs_temp`（L28634） | —（未迁移；req 系迁移试点 `req_attention_is_gibbs_temp` 见模块 `UpSigMigrate` L544，独立模块行号零漂移） | `real_attention_is_gibbs_temp`（模块 `UpDebtGibbsT` L160，现 G02_Debt.v 组内 L601） | L28634 / L544 / L160（现 G02:601） | setoid：试点形态（req 系单件，非全量）；Real 层：已复刻（模块层；与抽象陈述的 statement-level 对齐仍为人工比对） |
| 定理 5.3 `steady_state_boltzmann_attn`（L28722） | `steady_state_boltzmann_attn_setoid`（L66371，req 签名） | `real_steady_state_boltzmann_attn`（L43322，RealAttnSteady） | L28722 / L66371 / L43322 | setoid：已迁移（Id→req 直证）；Real 层：开放：需逐条 diff（人工比对一致） |
| attention 侧 Boltzmann 归一化 `boltzmann_normalized_attn`（L28802） | `boltzmann_normalized_attn_setoid`（L66400，req 签名） | —（Real 层无独立佐证，平凡） | L28802 / L66400 | setoid：已迁移（Id→req 直证） |
| §5.4(c) 缩放-温度对偶族 `scale_temp_duality`（L28524）/`scale_sqrt_witness_dual`（L28565）/`scaled_attention_is_gibbs_temp`（L28694） | `reqd_scale_temp_duality`（模块 `UpReqDist`）、`ag_scaled_attention_is_gibbs_temp`（模块 `UpReqAttnGibbs`）——已交付（迁移清单见公开 artifact 补充材料 S2） | `real_scale_temp_duality`（模块 `UpDebtDual` L219）；抽象层任意 d 见证 `sqrt_witness_exists_abstract`（模块 `UpDebtSqrtAbs` L76） | L28524 / L28565 / L28694 / L219 / L76 | Real 层：对偶恒等已复刻（模块层）；setoid/req 迁移已交付（迁移清单见公开 artifact 补充材料 S2）；statement-level 人工比对为论文自留余项 |
| 定理 7.1/7.3 `top_k_majorization`（L30047）/`top_k_majorization_mem`（L30264） | —（未迁移） | `real_top_k_majorization`（L43485，RealTopKMain） | L30047 / L30264 / L43485 | 开放：需逐条 diff |
| 定理 8.5 `minp_markov_kernel_normalized`（L31050） | —（未迁移） | `real_minp_markov_kernel_normalized`（L43392，RealMinPMain） | L31050 / L43392 | 开放：需逐条 diff |
| 定理 7.6 `topk_tv_identity_strict`（L30638） | —（未迁移） | Real 层 TV 恒等独立复刻：`rtk_tv_identity_strict`（模块 `UpReqTopKTVChain` L967，19 引理链 Real 层全平移） | L30638 / L967（模块内行号） | Real 层：已复刻（模块层；与抽象陈述的 statement-level 对齐仍为人工比对） |
| 定理 6.1 `eviction_steady_deviation`（L29626，Set 层三角不等式记账） | —（未迁移） | Real 层定量定理 6.1b/6.1c：`real_boltzmann_diff_bound`（L54656）、`real_db_breaking_bound_eps`（L54882，RealKVQuantMain） | L29626 / L54656 / L54882 | 开放：Real 层为**独立定量强化**（非同一陈述复刻），§6.2.1 已声明 |
| 定理 4.9 `steady_state_boltzmann`（L15692） | —（未迁移） | 热力学侧方程形态逐字复刻：`real_steady_state_boltzmann`（模块 `UpReqSteadyThermo` L100，热力学侧载体 `real_boltzmann_prob` L81）；迭代收敛侧的 Real 镜像 `attention_iterate_converges_real`（模块 `UpArchAttn` L171）为同族增量；RLHF Real 层有 `real_boltzmann_dist_r` 族 L43686+，属 §9.1 共享基座 | L15692 / L100 / L171 | Real 层：已复刻（模块层；与抽象陈述的 statement-level 对齐仍为人工比对；同族增量已入模块层） |

**对照表自述**：字段级（前三行 + metric/lim/cauchy_complete）为「单文件同库编译对齐」——Instance 字段赋值在同文件内经 Coq 类型检查，编译级一致由同一编译单元保证。定理级（其余各行）的 Real 层复刻列覆盖单位温度 attention 同构、稳态、top-k 支配、Min-P 归一化、Gibbs 不等式逐 eps 版与 KV 定量界六类（行号经实测核对，见上）；`attention_is_gibbs_temp`、缩放-温度对偶族（`scale_temp_duality`/`scale_sqrt_witness_dual`/`scaled_attention_is_gibbs_temp`，§5.4(c)，Set 层新增）与注意力 TV 收敛簇（`attention_tv_contraction` L29195 / `attention_tv_iter_contraction` L29287 / `attention_iterate_converges` L29330，§5.5）的 Real 层 δ 接口复刻已由定理 5.10 闭合（已入模块化树；setoid/req 迁移未完成）——Real 层与抽象陈述之间为「开放：需逐条 diff」的人工比对（`topk_tv_identity_strict` 与 `steady_state_boltzmann` 的 Real 层复刻已入模块层，见上两行；其 statement-level 人工比对仍开放）。**setoid 迁移现状**：等号簇 3 头条已在 req 签名下直证——`attention_is_gibbs_setoid`（L66294）、`steady_state_boltzmann_attn_setoid`（L66371）、`boltzmann_normalized_attn_setoid`（L66400），Section `AttentionGibbsBridgeSetoid`（L66137–66414，单位温度），可被 `RealEnhancedReal`（L41115）直接消费；已列其余头条的 setoid/req 迁移已按公开 artifact 迁移清单（补充材料 S2）逐项交付（§9.2 边界③）：任意温度对应 `req_attention_is_gibbs_temp`（模块 `UpSigMigrate` L544）、缩放-温度对偶族 `reqd_scale_temp_duality`（模块 `UpReqDist`）与 `ag_scaled_attention_is_gibbs_temp`（模块 `UpReqAttnGibbs`）、注意力 TV 收敛簇 `agq_tv_contraction`/`agq_tv_iter`/`agq_iterate_converges`（模块 `UpReqAttnIter`）、Top-k TV 恒等 `ag_topk_tv_identity_strict`（模块 `UpReqAttnGibbs`）；本表其余「未迁移」行的承载归属按 734 件迁移范围逐项裁决口径读取——其中容器 Id 机器与 nat→R 嵌入域专属形等 64 件保留为抽象层与实例层双套陈述并行（Id 层陈述原样保留、Real 层复刻件并行承载、不经 req 签名消费；Top-k 支配引擎 `top_k_majorization`/`top_k_majorization_mem` 即公开清单 A1-3/A1-15），逐项清单已公开（公开 artifact，机器检索 64 行，与逐项迁移状态登记的对应行一致，差值为零）。抽象定理签名向 setoid 实例的**整体迁移已处置闭合**（迁移清单见公开 artifact 补充材料 S2，2026-09-10：734/734=100%——670 件交付四项验证，64 件保留为抽象层与实例层双套陈述并行；§9.2 使用限制段与 §10.2 已解决项（一）同口径），statement-level 机器对齐（人工逐条 diff，即本表「开放：需逐条 diff」档）为该迁移范围外的论文自留开放项。本表未单列库尾新增件（§5.5 定理 5.4–5.6 双点收缩族与 √d 件、硬注意力计数/权重与 TV 闭合件 `eq_inv2_double` L97558 / `tv_hard_le_decay_scale` L97618 / `hard_attention_limit` L97679、库尾 FEP 与逐行等价件 `attention_minimizes_free_energy_unique` L112225 / `bs_kernel_row_is_softmax_temp` L112281、库尾 `Module UpExtras219` 内 `UpExtras219.free_energy_softmax_eq_neg_T_logZ` L114089）：它们均为抽象 Id 层陈述（枚举 list 求和 + expf 迷你接口与 `sum_eq_list` 诚实前件）或 Real 层直证（`real_sqrt_exists` L96475、`core_decay_bound` L97265）与接口由具体实例满足（`real_expf_realizable` L96364），暂无 setoid 迁移与 Real 层完整复刻（后者列入未来工作，§10.2）。**模块件增补口径**：本表新增三行的 Real 层对应为**模块化树内的模块件**（`UpDebtGibbsT`/`UpDebtDual`/`UpDebtSqrtAbs`/`UpArchAttn`/`UpSigMigrate`，模块内行号），其与抽象陈述之间仍是「两条独立陈述、各自完成证明」的人工比对关系（本表「机器对齐现状」两档定义不变）；附录 A 中来自历史 220 分发形态的模块件（UpCS/UpQKBound/UpTempWindow/UpMinP/UpAuditBridge/UpEvictId/UpKVDrift/UpTVReal）同此口径；这些历史分发形态模块件暂不在本表单列。当前编译清单为 246 模块，Live_X 356 个 .v；其承接关系见正文相应小节与附录 A 注。

---

## 附录 C：Artifact、编译指标与补充材料

- **构建与审计日志**：见补充材料 S3。全文各结果族的验证状态与 PA 口径以表 A.1（附录 A）为唯一权威；Print Assumptions 批量审计以公开 artifact 版本为时点；其后新增定理未逐条重跑批量审计，其零公理状态由编译期审计与全量 coqc 维持。当前库状态为 HEAD=39d81aa，编译清单 246 模块，Live_X 356 个 .v，CI 连续 success，认证面 246/246；81 条 PA 最终基线重跑尚未整体执行；本文四族结果的分层陈述口径不变（表 A.1 体系不动）。版本差异与迁移清单见补充材料 S2/S3。

**补充材料索引**：S1 行号索引；S2 构建与维护记录；S3 审计日志；S4 提取验证。补充材料随论文公开，编号与正文定理稳定标签对应。

## 声明（Declarations）

**作者贡献**：〔作者决策项：按概念化、形式化、软件、验证、论文撰写等实际分工填写。〕

**利益冲突**：作者声明不存在利益冲突。

**数据与代码可用性**：本文全部机器检查结果依托公开 artifact（Coq 模块化树及配套构建/审计脚本）；复现入口为模块化树，单文件合并形态仅作源码归档，不作为复现入口。补充材料 S1–S4 随论文公开，可独立复核。

---
