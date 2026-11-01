# 构造性柯西实数的超越函数：从指数正性到几何 π

**英文标题**：Constructive Transcendental Functions on the Cauchy Reals: From Exponential Positivity to the Geometric π


**作者**：王宝军、夏挽岚（通讯作者，xiawanlan33@163.com）、祖光照、周志农、高雪峰

**Authors**: Baojun Wang, Wanlan Xia, Guangzhao Zu, Zhinong Zhou, Xuefeng Gao. *Corresponding author: Wanlan Xia (xiawanlan33@163.com).*

---

## 摘要（Abstract）

本文报告 ConstructiveWorld 库中构造性柯西实数上指数正性及相关超越函数的形式化结果。C1 主结果：在零全局公理、零 Admitted 下闭合 cauchy_real_exp_pos；Setoid 接口的字段级实例化已完成，exp_neg_pos/exp_neg_plus 已赋为已证引理；抽象 Id 系定理的签名迁移尚未完成。C2 方法资产：提出两层假设消除策略；有限截断代数路线与指数加法路线共享级数基座，并在最终包装定理层给出两个包装证明。C3 扩展结果：闭合 T-π3（π_geom == π_L）、两 π 严格数值界与 sin/cos 和角恒等。C4 推广结果：指数正性与指数律从柯西实数推广至 Bishop 式 Banach 代数（Set 层 Class BanachAlg，乘法不交换）——指数级数柯西性、加法交换律 exp(a)·exp(b) == exp(a+b)（交换面前提）、e⁰ == 1 与可逆性侧 exp(a)·exp(−a) == exp(0)，并以柯西实数为载体完成实例非空性装配；完整可逆性形态与完整构造性谱定理仍为开放问题，而 C* 代数的定义面（对合 + C* 恒等式 ‖a*a‖=‖a‖²）、严格正元 Newton 平方根的构造性显式率与正元锥已在模块层机器检查（§7.3）。在上述结果之外，本文给出定量构造性常数包络与第二定律的 eps 定量化组合成果（§10）：ln2/e/π 的显式有理包络与可计算柯西模量、以及「熵增 ≥ 熵亏(KL) − eps」的逐 eps 定量形，四件载体已入库并注册。在两个历史验证快照（迭代 198 与 206）上，81 条选定核心定理的批量假设检查返回 Closed under the global context；其后新增内容通过编译、提取与内核检查维持验证状态，详细日志见补充材料 S2。

---

**Abstract (English)**

This paper reports formalized results on exponential positivity and related transcendental functions over the constructive Cauchy reals in the ConstructiveWorld library. C1 main result: under zero global axioms and zero Admitted, we close cauchy_real_exp_pos; field-level instantiation on the Setoid interface is complete, with exp_neg_pos/exp_neg_plus assigned proved lemmas, while theorem-level signature migration at the abstract layer is not yet complete. C2 methodological asset: we introduce a two-level assumption-elimination strategy; the finite-truncation-algebra route and the exp-plus route share the same series foundation and provide two wrapper proofs at the final wrapper-theorem layer. C3 extended results: we close T-π3 (π_geom == π_L), strict numerical bounds for both π constructions, and the sine/cosine angle-addition laws. C4 extension: exponential positivity and the exponential law are extended from the Cauchy reals to Bishop-style Banach algebras (a Set-level Class BanachAlg with non-commutative multiplication) — the Cauchy property of the exponential series, the additive law exp(a)·exp(b) == exp(a+b) under the commutation premise, e⁰ == 1, and the invertibility-side identity exp(a)·exp(−a) == exp(0), with instance nonemptiness witnessed on the Cauchy-real carrier; the full invertibility statement and the complete constructive spectral theorem remain open, whereas the C*-algebra definition layer (involution plus the C*-identity ‖a*a‖=‖a‖²), the constructive explicit rate for Newton square roots of strictly positive elements, and the positive cone are machine-checked at the module layer (§7.3). Beyond these results, the paper presents a combined account of quantitative constructive constant envelopes and an eps-quantified Second Law (§10): explicit rational envelopes with computable Cauchy moduli for ln2, e, and π, together with the per-eps form "entropy increase ≥ KL deficit − eps"; all four carrier files are registered in the library. On two historical verification snapshots (iterations 198 and 206), a batch Print Assumptions check of 81 selected core theorems returned Closed under the global context; later additions are maintained by compilation, extraction, and kernel checking, with logs in Supplementary Material S2.

---

## 1 引言

**本文贡献（C1–C4）**。指数正性在数学上平凡而工程链条漫长（§1.1）。本文贡献分为四层：C1 主结果——`cauchy_real_exp_pos` 的闭合与接口字段回填（§5–§6、§8）；C2 方法与工程资产——两层假设解除口径与 esq/exp_plus 双路线交叉验证（§1.1、§6.6–§6.7）；C3 扩展结果——T-π3 两 π 合流、π 数值界与和角恒等（§1.1、§9.1）；C4 推广结果——指数律与级数柯西性向 Bishop 式 Banach 代数的推广（§7）。摘要、本节、§1.2 与 §9.1 使用同一编号；各层边界声明（CLEAN 判定的语义、「独立双证仅出现在最终包装定理层」等）见 §1.1、§8 与对应章节。

**附录与补充材料分工**：论文内设附录 A–C——附录 A 列主链核心引理/定理，附录 B 列接口字段回填与审计快照，附录 C 列 T-π3、和角恒等与可微性主件；完整行号索引与逐字证明脚本见补充材料 S1《行号索引与证明脚本》，历史构建与维护快照见补充材料 S2。正文叙述段只保留定理名与附录编号，行号仅在附录与补充材料中出现（正文内联锚的最小中间态保留，口径见 §1.3）。

**验证快照与版本基准**：本文定理陈述以 219 版主文件 `CW_ConstructiveWorld_219.v` 为版本基准；198/206 为历史验证快照，220 为 artifact 分发形态，不承载正文定理；完整行号索引、SHA 校验与编译审计记录见补充材料 S1/S2，编译、审计与提取验证命令见补充材料 S0，仓库后续维护形态、CI 记录与历史快照见补充材料 S2，正文不记录。S0–S2 随论文 artifact 提交。正文定理状态不随仓库维护形态变化。

### 1.1 动机

指数函数 `exp(x)` 的正性在数学上 trivial，但在构造性证明助手中却是一条漫长的链条：需要先有级数定义、柯西性、连续性、零点，再对负输入证明 `exp(x) > 0`（等价于 `exp(−x)` 可逆）。ConstructiveWorld 库选择从有理数 Cauchy 序列构造实数 `Real`，因此 `exp_neg : R -> R` 的构造性正性必须走完整条链，不能依赖经典逻辑中的「x>0 或 x=0 或 x<0」三分律。

当前库中大量下游定理——Boltzmann 因子正性（`boltzmann_factor_pos`）、softmax 输出正性（`softmax_pos`）、RLHF/DPO 最优策略正性——都依赖 `exp_neg_pos` 这一 `RealInterfaceEnhanced` 接口字段。本文展示其定理化的完整路径：`esq_eq_corr` 与 Real 层 `cauchy_real_exp_pos` 均已证明，指数正性并经三个 Setoid 系接口实例（`Real_RealInterfaceSetoidCore`、`Real_RealInterfaceSetoid`、`RealEnhancedReal`）回填为接口字段的实值（见 §8.2）。

**定义（Two-level Discharging，两层解除口径；全文统一，摘要与 §8.2 按此引用）**。为消除「假设解除」表述的歧义，本文把两层语义口径固化为如下定义；全文每一处「解除/回填/实例化」声明显式归属于其中一层。

> **（i）字段级实例化（field-level instantiation）——已完成。** Setoid 系接口实例把接口字段填为具体 `Real` 层已证引理的值：`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log` 等（§8.2）。经实例消费的下游正性结论在具体 Real 轨上由机器证明承载，不再依赖未证假设。这是本工作最重要的**已完成**工程决策——其边界同样必须钉死：字段级回填解决的是字段的实值承载，不得被读成（ii）已完成，更不得被读成「抽象层已零假设重证」。
>
> **（ii）定理级签名迁移（theorem-level signature migration）——尚未完成。** 把以 `forall {RI : RealInterfaceEnhanced}` 陈述的抽象 Id 系定理改以 setoid 相等谓词 `req` 重述并重证，使抽象层定理自身不携带接口假设。该迁移尚未完成，本文不声称抽象层已零假设重证。库内已出现首批机器检查试点（220 模块化扩展层中 `UpSigMigrate` 的 `req_free_energy_kl_decomp`/`req_attention_is_gibbs_temp` 两条 req 系定理，与 `UpDebtSqrtAbs` 的抽象 Id 层平方根见证件 `sqrt_witness_exists_abstract`）——试点交付不等于全量迁移。首批试点之后，抽象接口假设的 Real 层放电已升格为独立成族：`UpReqRealLtShiftBridge` 把「lt one two 抽象接口不可内证」的定谳（七条死路清单固证）消解为 Real 层放电件——弱槽 `real_le` 经 Or 分解升温为严格序、`lt one two` 纯平移、混合平移 `lt a b → le c d → lt (a+c) (b+d)` 三形均零装饰闭合；`UpReqStrictBridgeD` 进而把 `ReqStrictOrderBridge` 族仅有的三个 Hypothesis 槽位（严格步平移/log 兼容/log-exp 互逆）在 Real 实例 `RealEnhancedReal` 上逐槽放电闭合，伴件同步闭合 le_lt 出节形——该族桥位自此在 Real 载体上零真抽象位。两件均经全量编译、内核检查与 `Print Assumptions` 全 Closed，属接口假设 Real 层放电的首批成族试点（试点交付仍不等于（ii）全量迁移，口径不变）。文献对标定位（配对范式，诚实分级，非首创声明）：「弱序接口推不出 0<1」在形式化库设计中属已知现象——Coq stdlib 的 `Rlt_0_1` 虽为定理，其证明本质消费古典三分公理 `total_order_T`；mathlib 则把 `0 ≤ 1` 升格为 `ZeroLEOneClass` 类字段公理。本件的差集不在现象而在工件形态：抽象接口不可导性证书与 Real 载体层 Or-分解放电证书（`real_le = Or(lt, eq)` 两支独立组装）构成同库成对机证工件（`UpReqRealLtShiftBridge.v` md5 e491ac09、`UpReqStrictBridgeD.v` md5 11bf529b），且均为构造性 Set 层机证件、零古典公理消费——「构造性 Set 层成对工件」是本件相对三库设计选择的差异点，不是首创声明；主流库中未检索到以「节假设槽位＋载体实例放电」配对件形式处理该现象者（措辞按「未检索到」而非「不存在」），逐条出处见同目录《论文3-文献对标资料-20260916.md》。

判别注记：`Print Assumptions` 对抽象层定理返回 CLEAN，是因为 `RI` 经 `End Section` 泛化为定理类型的显式前件而非全局假设；CLEAN 不构成（ii）已完成的证据（§8.2）。本文正文凡未显式标注层属的「解除」声明，一律属口径（i）。

**状态一览**。下表汇总本文相关目标的状态与阻塞项，供读者在正文前部直接核对；各目标的展开见后文相应章节（exp 接口字段 §6 与 §8；π 族与和角恒等 §9.1 及附录 C；组装式主定理 §9.1 及附录 A；Banach 代数推广 §7；抽象层签名迁移 §8.2）。行号口径：本文正文行号引用（形如 Lnnnn）除另有注明外，均指 219 基线主文件 `CW_ConstructiveWorld_219.v`（114,222 行；SHA-1 与审计口径见 §8.3）；其中 T-π3 双路线定理与终末定理 C 位于该文件的基座追加段（§6.1 图）。

| 目标 | 状态 | 阻塞项 |
|---|---|---|
| `exp_neg_pos` 接口字段（setoid 实例回填） | 已实例化（`exp_neg_pos := cauchy_real_exp_pos`） | 无 |
| `exp_neg_plus` 接口字段 | 语义层已证（`cauchy_real_exp_plus`），setoid 实例已回填 | 抽象层 Id 系签名统一（库级接口族后续工程，§8.2） |
| sin 加法定理 `rs_add_sin`（Real 层） | 已闭合 | 无 |
| cos 加法定理 `rs_add_cos`（Real 层） | 已闭合 | 无 |
| 几何 π 数值界（T-π2，`real_pi_geom_between`） | 已闭合 | 无 |
| 几何 π == Leibniz π（T-π3，`b5dT_f1_pi_geom_eq_leibniz_single`/`_univ`） | **已闭合** | 无。两条独立证明路线：单点轨 `b5dQ_E_rational_zero`（L111289）→ `b5dF_E_one_zero_of_rational`（L104506）→ `b5b_hsc_main`（L72994）→ `a3_closure_f1`（L67997）；∀x 轨 `b5dS_E_zero_on_unit`（L111782）→ `b5b_f1_closure'`（L78187）。件行号 L111966/L111981（219 实测）；终末定理 C `b5dU_cos_piL_half_zero`（cos(π_L/2)==0，L112062）已闭 |
| exp 保序群同构的组装式主定理（`exp_strict_mono`/`exp_log`/`log_exp` 命名形态） | 部分闭合（结构定理层已闭；命名级组装待整理） | 结构定理 `exp_order_embedding` 及构成件（`cauchy_real_exp_mono` L35227、`exp_reflects_lt` L53092、左右逆 `log_inv_exp_neg_thm`/`cw_log_exp_right`、值域刻画 `exp_surj_pos`/`exp_image_pos`）均已闭合（§9.1、附录 A）；`exp_strict_mono`/`exp_log`/`log_exp` 命名级组装在库内尚未以该名闭合（219 根逐名 grep 零命中，实测），待整理 |
| 抽象层 Id 系定理的签名迁移 | 后续工程（§1.1 定义（ii）） | setoid 实例与 Real 层复刻已完成；req 系定理级迁移已有首批机器检查试点（`UpSigMigrate` 两件，§1.1 定义（ii）），全量语句级统一尚待完成 |
| Banach 代数推广（级数柯西性/加法交换律/e⁰==1/可逆性侧/实例非空性） | **主体闭合**（§7） | 完整可逆性形态（逆元素存在性包裹）与完整构造性谱定理开放；C* 代数定义面／严格正元 Newton 显式率／正元锥已闭合（§7.3） |

**π 的定位（已闭合主定理）**。标题中的几何 π 在本版本中已是闭合结果而非开放目标。先给出证明的数学骨架，再列机器链（各定理逐字语句见附录 C）。几何 π（π/2 零点的两倍，`real_pi_geom`）与 Leibniz π（交错级数 4·Σ(−1)ⁿ/(2n+1)，`cauchy_real_pi_leibniz`）是两条独立的构造路线，其一致性由一个**桥函数**中介：E(x) := sin(arctan x) − x·cos(arctan x)（库定义 `real_E`，根 L72948）——E(x) == 0 即 sin(arctan x) == x·cos(arctan x)，而端点形态 E(1) == 0（`real_E_one` 承载，L72953）蕴含 sin(arctan 1) == cos(arctan 1)，即「arctan 1 处正弦与余弦相等」的几何刻画；闭包件 `a3_closure_f1`（L67997）把它一步接入 π_geom == π_L。

这一归零命题的几何内涵近乎平凡：对 x ∈ (0,1) 取 θ := arctan x，直角三角形视角下 tan θ = x 与 sin θ = x·cos θ 是同一关系的两种写法（cos θ > 0），故 E(x) == 0 只是把「arctan 是 tan 之逆」这一几何上直接的恒等整理成 sin/cos 的代数形态。但机器证明的内容不在这条恒等本身：库内不把经典逆函数捷径或三分律当作可用前提，而是把同一目标作为纯构造性命题重建——有理点处以精确等式闭合、无理点处经有理近似逐 eps 传输（机器论证的细节即下文的归零层与最终装配层）。换言之，几何读法解释该恒等为何应当成立，机器证明则给出它在构造性框架内的完整重建；机器执行的是级数、连续性与逼近论证，不涉及任何三角形上的几何推理。

机器实现把「E 归零」拆为两层：**归零层**——对有理点 q ∈ Q∩(0,1) 闭 E(q) == 0（`b5dQ_E_rational_zero`，L111289；两条证明路线共享的唯一归零机器证明）；**最终装配层**——两条轨以不同方式把归零接到 π：单点轨经端点逼近得 E(1) == 0（`b5dF_E_one_zero_of_rational`，L104506），再经 `b5b_hsc_main`（L72994）与 `a3_closure_f1` 闭合；∀x 轨把有理归零经有理近似传输提升为任意 x ∈ (0,1) 的 E(x) == 0（`b5dS_E_zero_on_unit`，L111782），经 `b5b_f1_closure'`（L78187）直接闭合。

以下机器链即按此两层展开——单点轨（`b5dQ_E_rational_zero`：0<q<1 有理点 E(q)==0，→ `b5dF_E_one_zero_of_rational`：端点 E(1)==0，→ `b5b_hsc_main`：E(1)==0 ⟹ sin(arctan 1)==cos(arctan 1)，→ `a3_closure_f1`：⟹ π_geom==π_L）与 ∀x 轨（`b5dS_E_zero_on_unit`：(0,1) 上 E(x)==0，→ `b5b_f1_closure'`：⟹ π_geom==π_L），两条证明路线（共享有理点归零主引理 `b5dQ_E_rational_zero`——∀x 轨主定理 `b5dS_E_zero_on_unit` 的证明体位于基座根 L111835，于该处直接调用之——机器层面的独立双证仅出现在最终包装定理层，见 §9.1）给出同一闭式 `b5dT_f1_pi_geom_eq_leibniz_single`（单点轨，219 根 L111966）与 `b5dT_f1_pi_geom_eq_leibniz_univ`（∀x 轨，L111981）；终末定理 C `b5dU_cos_piL_half_zero`（cos(π_L/2) == 0，L112062）随之闭合（§9.1 与附录 C 给出链与行号）。π 工作在文中的定位：与指数正性主线共享同一级数基座的超越函数扩展（π/2 零点定理与 T-π2 数值界构成其独立价值），T-π3 的闭合使几何 π 与 Leibniz π 两条构造路线在机器检查层面合流。

### 1.2 贡献

**C1 主结果**：构造性柯西实数上 `cauchy_real_exp_pos` 的闭合与接口字段回填——有理数级数基座（`exp_partial` 的柯西性、Lipschitz 连续性、一致有界与零点恒性，§3–§4）、主恒等式 `esq_eq_corr`（系数层由两个交错二项式恒等 `vander_4m2`/`vander_4m4` 支撑，§5）、Q 层正性链（`exp_even_neg_nonneg`/`exp_even_neg_pos`/`exp_partial_tail_pos`，§5.1）到 Real 层 `cauchy_real_exp_pos`（§6.2），并经三个 Setoid 系接口实例把 `exp_neg_pos`/`exp_neg_plus` 回填为实值（§6.3–§6.5、§8.2；实例回填清单见附录 B）。

**C2 方法与工程资产**：两层假设解除口径（Two-level Discharging，§1.1 定义框）——字段级实例化（已完成）与定理级签名迁移（尚未完成）的显式分层，及「PA CLEAN ≠ 零假设」辨析；有限截断代数路线（esq）与指数加法路线（exp_plus）在共享级数基座与有理点归零引理之外，于最终包装定理层形成两个包装证明；本文不声称全链互不引用（§6.6–§6.7）。esq 供给可直接数值复核的 Q 层有限正性链，exp_plus 供给完整指数律与 eps/3 装配模板；支撑技术包括 Setoid 并行接口层的 Proper 兼容性证明（§6.4，含证明复杂度较高的 `real_eq_mult_compat`）与 metric 逐 eps 形式及完备性桥（§6.5）。

**C3 扩展结果**：T-π3 两 π 合流——几何 π 与 Leibniz π 经桥函数 E(x) := sin(arctan x) − x·cos(arctan x) 的归零论证（零点论证）两条独立证明路线闭合（§1.1、§9.1、附录 C）；几何 π/2 零点定理与两 π 严格数值界（§9.1）；sin/cos 和角恒等 `rs_add_sin`/`rs_add_cos`（§9.1）；exp-log 保序群同构与 exp/sin/cos 可微族（§9.1）。

**C4 推广结果（Banach 代数推广）**：指数正性与指数律从柯西实数推广至 Bishop 式 Banach 代数——Set 层 `Class BanachAlg`（载体、Set 层等词 `bae`、加法交换群与乘法幺半群-双分配律、Q 标量嵌入与 Q 值范数；乘法不交换）上的指数级数柯西主定理（`esp_diff_le_tail`/`exp_series_cauchy`）、exp 元素的 sigT 完备性定义（`bxdef_exp`，「定义即算法」）、加法交换律主定理 `bxae_exp_add`（柯西方块恒等 `esp_prod_square`、二项式展开与 Pascal 配对组装、截断误差分块上界的机器检查；交换面 `a·b == b·a` 为显式前提）、e⁰ == 1、可逆性侧 `bxoo_exp_opp_one`（exp(a)·exp(−a) == exp(0)）、ε-近邻收敛链 `bxcd_prod_near_one` 与以柯西实数为载体的实例非空性装配（39 字段逐一消解）。载体为独立模块层 UpReqBanach 系 26 件（11,568 行、345 处行首 `Qed.`、1 处 `Defined.`，行首 `Admitted`/`admit` 零出现），陈述、行号与验证面见 §7；完整可逆性形态与完整构造性谱定理如实列为开放问题（§7.3–§7.4），而 C* 代数一线已就定义面（`Class CStarAlg`：对合 ＋ C* 恒等式）、严格正元 Newton 平方根的构造性显式率与正元锥取得机器检查，其范围与逐件陈述见 §7.3。在 C1–C4 之外，本文另以 §10 组合节给出定量构造性常数包络与第二定律的 eps 定量化（ln2/e/π 的显式包络与可计算模量、熵增 ≥ 熵亏(KL) − eps 的逐 eps 定量形；四件载体已入库并注册）——该节为成果组合陈述，不改变 C1–C4 贡献边界。

**支撑技术条目**：语言模型实例中的 `exp_neg_positive` 及其求和形态 `sum_exp_positive`（通用 KeyProofs 引理）；审计纪律（零全局公理、零 Admitted，接口假设显式声明为 `Variable` 或字段前提，验证方法见 §8.3，接口字段清单见附录 B）。

**术语约定**：Print Assumptions 返回 Closed under the global context 简称 CLEAN；Two-level Discharging 指 §1.1 定义的两层假设解除口径；T-π2/T-π3 为库内任务编号，分别指 π 数值界与两 π 一致性任务，非数学对象名；本文区分全局公理与接口层 Variable/字段假设：零全局公理、零 Admitted，log_differentiable 仍为接口 Variable；Print Assumptions 批量假设检查在两个历史验证快照（迭代 198 与 206）上执行；其后新增面以编译、提取与内核检查维持验证状态，未整体重跑（§8.3）。正文叙述中的 `==` 表示相应相等谓词（Q 层 Qeq、Real 层 real_eq）意义下的相等，代码引文内保留 Coq 字形；行号锚以 219 基线主文件为基准（口径见 §1.3 与补充材料 S1）。

### 1.3 Artifact 版本说明

本文结果对应源码版本 `CW_ConstructiveWorld_219.v`（114,222 行，SHA-1 校验值见补充材料 S1/S2）。编译、审计与提取验证命令见补充材料 S0；正文不记录 CI 编号、分片布局与历史构建日志；相关记录见补充材料 S2。后续扩展结果（如 UpReqExpPos 系与 UpReqBanachExp 系）作为独立模块报告；其中 Banach 代数推广线已升格为正文 §7，其余（UpReqExpPos 系、Padé 系等）的状态、清单与验证日志见补充材料 S2 与 §6.7 末「后续认证披露」。

**当前库真态声明（截至 2026-09-16）**：ConstructiveWorld 库 HEAD=39d81aa（R82 成果四接入与注册收尾波），Rocq 9.1，纯构造性；编译清单 246 模块，开发树 Live_X 共 356 个 .v；认证面经 143/144→151→156→161→166→167→168→173→187→196→201→221→224→228→246 逐波扩展（注册 246 件 .vo 面 246/246 OK91 满面全绿、无缺面；本地全树 coqchk 246/246 通过）。云认证分两段如实：9.0 基线段以 run 94486425397 @24431dc 全树 `COQCHK_ALL_PASS` 及其后 #65 success 收尾；9.1 认证段中 #67 五红经绿谱系同步与源侧修复收口（#69 四红清偿，唯一余红 SqrtfCauchyArch 亦已由 R80（5a864a6）修复上云），#70（head 5a864a6 = R80）224 面 `COQCHK_ALL_PASS`（56,678 cst），R81（568a3fb：B 组四件注册、Index v3.4 落册与 vo 树漂移修复；终态 b379a75）上云后 #71（head b379a75）228 注册面 `COQCHK_ALL_PASS`（56,756 cst；轮次判读与 GitHub API 复核双证），9.1 重认证完全体达成；其后成果四接入与 R82 注册收尾波（HEAD=39d81aa）上云，当前云认证 **CI #72（head 39d81aa，run 35057242417，246 注册面）`COQCHK_ALL_PASS`**——246 注册面为成果四接入＋R82 注册收尾后的正式认证面。当前基态以随论文 artifact 的变更记录为准。如实限定（两项口径分列）：模块化拆分件 S11–S15 的闭包面公理依赖（`functional_extensionality_dep`、`ClassicalDedekindReals`×2，源于其中的 `Psatz` 引入）已作源侧移除修订（两件纯删除引入、三件改用库内已证线性算术件 `Lqa`，经五件合并内核检查、闭包面公理清零），并已随 b657aff 注册波并入认证面——S11–S15 源侧零 `Psatz` 直接引入，注册树内 163 件下游件闭包面源侧移除；另一方面，全树传递闭包仍经 stdlib 间接携带该三项公理（面内零直接 `Require`），全树 coqchk 认证通过——源侧清零与全树传递闭包清零系两个口径，分列如实。219 主文件定理基线的零全局公理/零 Admitted 审计口径不受影响（§8.3）。本文定理基准为 219 主文件；当前库真态不改变正文 A 路定理状态，新增认证见范围外披露（§6.7 末）。

---

## 2 相关工作

- **O'Connor (2008)**（文献 [1]）：在 Coq 中给出构造性超越实数计算（含 `exp`），其工作构筑于 C-CoRN 谱系的构造性实数之上（Bishop 传统、setoid 相等），本身即纯构造性路线。本文与其的对比不在「构造性 vs 经典」维度，而在编码与工程层：O'Connor 采用双侧逼近型 regular 编码承载实数与超越函数，本文则以有理数级数的显式范数界（柯西模量 + 逐 eps 界）直接承载截断级数，并以有限截断代数在截断层闭合正性；两种编码在提取质量上的系统对比留作后续工作。本库与其同样追求纯构造性、零 Axiom 的基座。
- **C-CoRN**（文献 [3]；正式文献锚 [3]）：构造性分析先驱，提供了级数、柯西序列等工具；其仓库的构造性超越函数谱系（exp/sin/cos 等）业已存在，故本文**不主张「首个构造性 exp 正性」**。本文的差异化定位在三点：应用层接口字段设计与实值回填（下游 Boltzmann/softmax/RLHF 假设的实例化链路，C-CoRN 侧无此物，见下文与 §8.2）、审计纪律（批量 `Print Assumptions` + `coqchk` 全树认证的五层验证组合，§8——「零 Axiom」本身不构成与 C-CoRN 的差异）、以及 T-π3 的 π 双构造机器合流（§1.1、§9.1）。
- **Geuvers–Niqui(-Wiedijk)**（文献 [2]）：Coq 中零公理构造性实数形式化的直接先例（构造性柯西序列与 categoricity 讨论）。本文「纯构造性、零 Axiom 统一基座」的定位须相对其划界：增量不在「是否零公理」，而在规模、接口族（Setoid 系接口字段 + 实值回填，§3.4/§6.3）与下游回填（ML 应用定理实例化，§8.2）。

**库间定位的对照口径（补充）**：形式化实数分析的库间综述见[30]；KL 与 I-投影的经典文献见[31][32]（本文 §10 第二定律定量化的 Gibbs/KL 腿以逐 eps 形消费该不等式族）；Mathlib 概率与熵/KL 形式化的权威记述见[33]；构造性代数中序域、离散域与局部环的处理口径见[29]。

**与 C-CoRN 的 Setoid 代数设计对比**：C-CoRN 建立了丰富的 Bishop 式 Setoid 代数结构（`CSetoid`、`CSemiGroup`、`CGroup`、`CRing`、`CField` 等），其组织方式以 Coq **`Module`/`Module Type`** 为主：每个代数层是一个模块类型，实例经模块函子（functor）参数化组装。本文的 Setoid 并行接口层采用 **`Class`/`Instance`** 组织（§3.4）：接口族 `RealInterfaceSetoid` 系以 Class 声明字段（运算 + Proper 原理 + 环/序/度量/完备性律），具体 `Real` 经三个 Instance（`Real_RealInterfaceSetoidCore`/`Real_RealInterfaceSetoid`/`RealEnhancedReal`）一次性装配。两种组织的工程差异与粒度对比：

- **组织方式**：Module/functor 的参数化在「库级复用」上更显式（结构共享与约束都写在模块签名里），Class/Instance 则在「按需推断」上更顺手——下游定理以 `forall {RI : …}` 消费接口字段时，实例自动参与类型类解析，这正对应本文「下游抽象定理直接消费实例字段」的用法；C-CoRN 侧同等用法需显式例化 functor。
- **Proper 兼容性**：本文 §6.4 的 `real_eq_*_compat` 族（`real_eq_plus_compat`/`real_eq_mult_compat` 等）对应 C-CoRN 代数层中按 `_wd` 后缀惯例命名的 well-definedness 引理族——两边都须为 Setoid 替换原理提供逐运算的替换证明，工程形态一致；差异在粒度：C-CoRN 把 wd 证明组织进代数结构的 Module 签名（每层结构自带其 Proper 场），本文把 Proper 族作为独立引理层先行证明、再在实例组装时逐一填入 Proper 字段。
- **接口粒度与目标层**：至于 C-CoRN 的既有基础设施为何未直接支撑本文的下游应用，主要不是构造性路线差异（两者同属 Bishop 传统），而是**接口粒度与目标层不同**：C-CoRN 的 Setoid 代数面向抽象代数层次的库内复用，未提供「把某具体实数模型的指数正性回填为下游应用定理（Boltzmann/softmax/RLHF）的假设字段」这一应用层接口；本文的 `RealInterfaceEnhanced`/`RealInterfaceSetoid` 系字段（`exp_neg_pos`/`exp_neg_plus` 等）正是为此设计——下游库内形式化（`boltzmann_factor_pos`/`softmax_pos` 等，附录 B）以接口字段声明假设，本文以具体层的已证引理实例化之。

该对比亦说明：Setoid 代数本身（C-CoRN 早已有之）不是本文的贡献点，贡献在于把指数正性这类分析事实组织为可实例化的接口字段并完成实值回填（§8.2）。本文对 C-CoRN 的结构性描述以其公开文档与一般形态为据，未逐一核验具体标识符；相关对比仅作组织方式层面的定性参照。
- **mathlib / Lean**：分析库内容丰富，但基于经典逻辑，与本工作的构造性立场不同。

**与 mathlib `real.exp_pos` 的方法论对比**：mathlib（文献 [5]）基于经典逻辑，其 `real.exp_pos` 可走「平方捷径」：由函数方程 `exp(x) = exp(x/2)²` 先得非负，再结合 `exp(x)·exp(−x) = exp(0) = 1` 排除 `exp(x) = 0`，从而得正——其中「非负且非零 ⟹ 正」的判定与情形拆分由经典逻辑（排中/三分律）直接供给。该捷径在纯构造性设定下整体不可行：第一步需要「所有平方非负」的全称 Or 形陈述——本库 `real_le = Or (real_lt) (real_eq)` 序编码下，该全称形态与 LPO 等价、构造性不可证（库内 `real_square_not_negative` 的自注即同框证据）；该等价现已定理化为注册件 `UpReqLpoEquiv`：全称平方非负墙 SqWall（`∀x, real_le real_zero (x·x)`）与受限 LPO（柯西实数零问题决策形：|x| 一致正下界 ∨ 逐点归零）的双向归约（`lpn_forward`/`lpn_backward`/`lpn_equivalence`）。**文献定位（诚实分级）**：该现象在构造性反数学（constructive reverse mathematics）中有系统的先例——LPO / LLPO 的定义与层级见 Bishop & Richman[25]，Ishihara[26][27] 分类了构造性分析中大量定理相对这些原理的强度（实数上 `x # y ∨ x = y` ⟺ LPO、`x ≤ y ∨ y ≤ x` ⟺ LLPO、`¬x = y → x # y` ⟺ MP），系统综述见 Diener[28]。**本件的增量不在发现该等价**，而在两点：其一，把双向归约在本文的**具体序编码**（`real_le = Or (lt) (eq)`，Set 层，非 Bishop 的否定式序）下做成机器检查工件；其二，与载体层放电件（同库成对工件）配套，把「抽象接口推不出」与「载体层可达」这两个方向在同一库内机证并置。本文不主张该等价关系本身的数学新颖性（与 §2 对 C-CoRN 的定位同理）；该归约以机器检查取代原先的自注证据，钉定墙（PinWall）的等价器亦已定理化（`UpReqPinWallEquiv`：`pwe_pin_wall_lpo`，与 C* 正典范可判定对接；该件已建成、9.1 vo 面重铸完成，已注册入库）；且 `exp(x) = exp(x/2)²` 还依赖完整的函数方程 `cauchy_real_exp_plus`（本文经 58 条引理闭合，§6.6–6.7）。构造性可行的正性路线不限于单一形态：本文 esq 有限截断代数路线、后续认证的级数 ε-见证路线，以及后续注册的 Padé 免积分正尾路线（见 §6.7 末段「后续认证披露」）。因此本文主链采用 esq 路线：`S_{2m}(−a)·S_{2m}(a) == 1 + corr m a ≥ 1`（`exp_even_mul_eq` + `corr_nonneg`）在 Q 层直接闭合截断正性，零完备性机械、可 `vm_compute` 复核（§5.3）；函数方程路线保留为独立交叉验证与和角恒等 `rs_add_sin`/`rs_add_cos` 的 eps/3 方法模板（§6.7、§9.1）。这一对比说明：与经典库的「一行捷径」不同，构造性正性证明的主要成本在代数组织（交错二项式系数层，见 §5.4 命名注记）而非分析工具——这也是本文 §1.2 立场（零三分律、有限截断代数优先）的方法论动机。

**构造性分析的数学源头与序编码理论**：构造性分析的标准文献是 Bishop–Bridges《Constructive Analysis》（文献 [6]；Bishop 1967 初版）与 Bridges–Vîță《Techniques of Constructive Analysis》（文献 [7]）；序的构造性编码（apartness、Bishop 逐 eps 非严格序）的理论背景见 Troelstra–van Dalen《Constructivism in Mathematics》（文献 [8]）。其中与本文直接同型的一处：Bishop 谱系的 exp 正性论证以「下界逼近 + 有界逆控制」在极限层完成，与本文 Real 层提升结构（乘积形态 + 有界逆，§6.1）同型。本文相对该论证的增量在于把正性论证**前移到有限截断层**：Q 层截断乘积恒等式 `S_{2m}(−a)·S_{2m}(a) == 1 + corr m a ≥ 1`（§4.2、§5）在截断层直接闭合正性，零极限机械、可 `vm_compute` 复核——这是 esq 路线相对 Bishop 极限层论证的实质差异点，也是本文正性主链的真实新颖性所在（exp 正性本身在构造性分析中是已知内容）。

**Class/Instance 组织与 C-CoRN 的正式文献锚**：以 Coq 类型类组织构造性精确实数算术的直接先例是 Krebbers–Spitters（文献 [9]）——其以 type classes 承载「相等不满足替换性」的实数序结构，与本文 §3.4 的 Class/Instance 接口组织同属一路；上文 Module/functor vs Class/Instance 的组织对比应参照该文（以及 Isabelle/HOL 侧 class-based 分析库的同型组织，文献 [11]）。C-CoRN 库本身的正式文献锚为 Cruz-Filipe–Geuvers–Wiedijk（即文献 [3]）。

**经典路线对照与无经典公理的平行形式化**：经典实分析库方面，Coquelicot（文献 [10]）是 Coq 生态中含 `atan` 与完整三角函数组织的经典分析库，其接口工程与本文 rs_add 系（§9.1）构成经典/构造性跨路线对照；MathComp-Analysis（文献 [12]）是经典逻辑 + Bishop 风格组织的现代代表，其序结构与本文 `real_le = Or (real_lt) (real_eq)` 编码（§6.5）的取舍构成直接对照。无经典公理的实数平行形式化方面，UniMath（文献 [13]）与 HoTT Book（文献 [14]；其 §11.2–11.3 对 modulus Cauchy 与 choice 依赖有标准讨论）分别给出单价类型论与同伦类型论口径的构造性实数——本文的柯西证据为 Set 层数据形态（给定 ε 产出具体 N 的模量，Set 层口径与可提取性见 §8.4），choice 以构造性方式被证据形态吸收、零 AX 声明，与上述口径的差异属证据形态层。

---

## 3 构造性基座

### 3.1 有理数幂与阶乘

```coq
Fixpoint q_pow (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S n' => x * q_pow x n'
  end.

Fixpoint q_fact (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S n' => Z.of_nat (Datatypes.S n') # 1 * q_fact n'
  end.
```

`q_pow_add` 给出指数加法：`q_pow x (a+b) == q_pow x a * q_pow x b`。

### 3.2 截断指数级数

```coq
Fixpoint exp_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => exp_partial m x + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)
  end.
```

该框与机器定义逐字一致（根锚 `exp_partial` 定义组，行号对照见 artifact 行号索引）：递归项累加 `x^{m+1}/(m+1)!`，故 `exp_partial n x = Σ_{k=0}^{n} x^k/k!`——`exp_partial 1 x == 1 + x`，与 §4.2 的偶/奇部分和实例（基于同一语义）一致。

### 3.3 柯西实数 exp

**底座披露（`Real` 的完整定义与完备性）**。本文全部构造所依附的柯西实数定义如下（库内拆分件 `S02_CauchyComplete.v` L380–L391 逐字）：

```coq
Definition cauchy (u : Qseq) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
        QltT (Qabs (u m - u n)) eps).

Definition Real : Set := sigT (fun u : Qseq => cauchy u).

Definition real_eq (x y : Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
        QltT (Qabs (projT1 x n - projT1 y n)) eps).
```

即柯西证据为 Set 层函数型模量（给定 ε 产出具体 N），`Real := sigT (fun u : Qseq => cauchy u)`——构造性选择内建于 sigT 证据形态，零公理。完备性定理语句（同件 L3073 起逐字；陈述中的减法按 `real_plus (u m) (real_opp (u n))` 展开）：

```coq
Theorem real_cauchy_complete :
  forall (u : nat -> Real),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        And (real_lt (real_plus (u m) (real_opp (u n))) (real_const eps))
            (real_lt (real_plus (u n) (real_opp (u m))) (real_const eps)))) ->
    sigT (fun l : Real => real_lim u l).
```

证明体为 Bishop 正则化对角线构造（同件 L3073 起）；与 HoTT Book §11.2–11.3 的 modulus-Cauchy/choice 讨论（文献 [14])的对应见 §2 末段。

```coq
Definition cauchy_real_exp (x : Real) : Real.
```

其构造性定义以 `Defined.` 闭合：对 `x = [u_n]`，取对角序列 `exp_partial n (u n)`，并证明其为柯西序列。该证明拆分 `exp_partial m (u m) - exp_partial n (u n)` 为输入差分项与截断差分项，分别用 Lipschitz 控制与级数尾部控制。

**arctan 的构造性定义（披露）**。T-π3 的桥函数 E(x) := sin(arctan x) − x·cos(arctan x)（§1.1、§9.1）依赖 arctan 的构造性定义。库内 arctan 经 Leibniz 级数构造（库内拆分件 `S11_TP3B5.v`，行号为该拆分件坐标；L37–L45 逐字）：

```coq
Definition arctan_term (k : nat) (x : Q) : Q :=
  q_pow (-1) k * (q_pow x (2 * k + 1) / (Z.of_nat (2 * k + 1) # 1)).

(* 部分和 arctan_partial n x = Σ_{k=0}^{n} arctan_term k x *)
Fixpoint arctan_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => arctan_term 0 x
  | Datatypes.S m => arctan_partial m x + arctan_term (Datatypes.S m) x
  end.
```

即 `arctan_term k x := (−1)^k · x^{2k+1}/(2k+1)`（Leibniz 级数项），`arctan_partial n x := Σ_{k=0}^{n} arctan_term k x`；项模长闭式 `atan_mag k x := |x|^{2k+1}/(2k+1)`（同件 L47–L50 逐字）供收敛控制。Real 层构造 `cauchy_real_arctan`（同件 L786）在逐点界前提 `Hx : forall n, QleT' (Qabs (projT1 x n)) 1` 下，以 Q 级数部分和加余项界见证构造柯西实值（`Definition cauchy_real_arctan (x : Real) (Hx : …) : Real`，`Defined.` 闭合）；`arctan_one_real` 即其于 x = 1 的实例，T-π3 链中 arctan 1 的承载件由此而来。

---

### 3.4 实数接口族与实例化

**动机（Setoid 系的数学必要性）**：在 Bishop 式构造性分析中，柯西实数的相等是**近似相等**：`real_eq a b` 定义为逐 eps 的收敛意义（`∀ eps > 0, |a − b| < eps`），而非命题相等。因此，把具体 `Real` 装配为抽象接口（其代数律以相等谓词表述）时，相等必须是 Setoid 意义上的 `req := real_eq`，全部代数结构（运算、序、度量、极限）都须在 `req` 上重述——这是 Setoid 并行接口层存在的深层理由，也是 Bishop 构造性分析的标准做法。直接触发该并行接口层重构的工程原因是命名空间冲突（类字段 `zero`/`one`/`plus` 等与既有 `RealInterface` 投影同名，需以 Module 隔离），但深层理由如上，命名冲突只是工程上的导火索。与之同构地，序的「非严格且不趋近」语义亦有同一选择：库内新交付的 `real_le_b`（∀eps>0, x<y+eps）即序上的逐 eps 编码谓词（`UpRealLeB.v` 判定 1）——本文的 Setoid 动机段与该谓词共享「逐 eps 全称化承载构造性语义」的方法论。

本库不以实数公理为起点，而把实数抽象为满足一组代数、序与完备性条件的接口（不以经典实数公理系统为前提的构造性路线，对照见文献 [2]）。接口族按相等谓词分为两系：以命题相等 `Id` 表述的 `RealInterface` 及其增强版 `RealInterfaceEnhanced`，以及以 setoid 等价 `req` 表述的 `RealInterfaceSetoid` 系。两系的字段构成一一对应，实质差别在于**超越函数字段是否携带正性前提**：柯西实数上的对数只能在正参数上构造（`cw_log`），因此 log 族带前提的 setoid 系可由具体 `Real` 满足。本文的实例化全部落在该系上：

| 接口 | 字段构成要点 | `Real` 实例 |
|---|---|---|
| `RealSetoidCore.RealInterfaceSetoidCore` | setoid 核心（req 自反/对称/传递）、常数与运算、Proper 原理、环律、序律、正元求逆、metric 逐 eps 族、lim/lim_unique/cauchy_complete | `Real_RealInterfaceSetoidCore` |
| `RealSetoid.RealInterfaceSetoid` | Core 全部字段 + exp 族（exp_neg/exp_neg_pos/exp_neg_zero/exp_neg_plus）+ log 族（log_inv 及三条恒等，带正性前提） | `Real_RealInterfaceSetoid` |
| `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid` | Setoid 全部字段 + 正性与保序（one_pos/lt_mult_compat/inv_pos_le_compat 等）+ min/r_max/pos_test/pos_part/r_if + abs 族 + exp 族 + log 族（带正性前提）+ metric 与完备性 | `RealEnhancedReal` |

log 族的前提是两系的分水岭。setoid 系的相应字段为：

```coq
log_inv : forall x, lt zero x -> R;              (* RealInterfaceSetoid *)
log     : forall x, lt zero x -> R;              (* RealInterfaceEnhancedSetoid *)
exp_neg_log_inv : forall x Hx, req (exp_neg (log_inv x Hx)) x;
```

即 `exp_neg` 与 `log_inv` 的互逆性只在正参数上要求——这与构造性对数的定义域一致，也是该系接口能够实例化的原因。

三个实例的字段逐一取自 `Real` 层已证引理，不含任何公理。例如增强版实例 `RealEnhancedReal` 的回填包括 `req := real_eq`、`plus := real_plus`、`req_plus_compat := real_eq_plus_compat_adapt`；完整版实例 `Real_RealInterfaceSetoid` 则把 `exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log` 等超越函数字段填为实值（逐条清单与见附录 B）。度量与完备性方面，`metric_pos` 与 `metric_triangle` 采用**逐 eps 余量形式**：构造性 `le` 以 `Or (lt) (req)` 编码，无法表达「非严格且不趋近」，故以 `∀ eps > 0` 的余量陈述——这是该编码下可达的最强形式（§6.5）。该论断在 Or 编码下成立不变，且有同框对照实证：`min a b ≤ a` 的 Or 形精确版构造性不可证、同一语句的 Bishop 形（`real_min_le_l_B`）可证（`UpRealLeB.v` 尾注判定 2/7）——「逐 eps 余量」机制现已由序谓词 `real_le_b` 完成谓词级封装（Set 层 forall 型，零 Prop 泄露），并以装配引理族覆盖 28 条 plain/D·eps 余量引理。两系接口的字段级对照与实例回填值汇总见 §6.3 表。

## 4 已闭合的关键引理

### 4.1 零点与连续性

**引理 4.1**（`exp_partial_zero`）：`forall n, exp_partial n 0 == 1`。

**引理 4.2**（`exp_partial_lipschitz`）：对 `|x|,|y| ≤ B`，有
```
Qabs (exp_partial m x - exp_partial m y) ≤ Qabs (x - y) * exp_series m B.
```

**引理 4.3**（`cauchy_real_exp_zero`）：`cauchy_real_exp real_zero == real_one`。

### 4.2 corr 非负性与归零

**定义**（`corr`）：`corr m a` 是主恒等式 `E_m(a)² − O_m(a)² == 1 + corr m a` 的**校正项**，Coq 定义与闭式如下：

```coq
Definition corr (m : nat) (a : Q) : Q := kloop m (2 * m - 1) a.
(* corr m a = Σ_{k=m}^{2m−1} Σ_{j=1}^{2m−k} brk2 k j a *)
```

其中括号项 `brk2 k j a := 2·a^{2k+2j}·(1/((2k+1)!·(2j−1)!) − 1/((2k+2)!·(2j−2)!))`，`kloop` 为内层 `inner2` 的求和器。

为便于逐字对照与独立复算，此处一并给出三件辅助定义的 Coq 逐字定义（与机器定义组逐字一致；上框 `corr` 的双和注释即依此组逐层展开）：

```coq
(* 括号项（j ≥ 1）：brk2 k j a := 2·a^{2k+2j}·[1/((2k+1)!(2j−1)!) − 1/((2k+2)!(2j−2)!)] *)
Definition brk2 (k j : nat) (a : Q) : Q :=
  2 * q_pow a (2 * k + 2 * j) /
    (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
  2 * q_pow a (2 * k + 2 * j) /
    (q_fact (2 * k + 2) * q_fact (2 * j - 2)).

(* 内和：inner2 k J a := Σ_{j=1}^{J} brk2 k j a *)
Fixpoint inner2 (k J : nat) (a : Q) : Q :=
  match J with
  | 0%nat => 0
  | Datatypes.S J' => inner2 k J' a + brk2 k (Datatypes.S J') a
  end.

(* kloop m k a := Σ_{k'=k}^{2m−1} inner2 k' (2m−k') a —— k 递减递归（J 依赖不变的外层 m） *)
Fixpoint kloop (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => if Nat.leb m k then inner2 k (2 * m - k) a + kloop m k' a else 0
  end.
```

**防御性注记**：`2 * m - 1` 中的 nat 减法在 `m = 0` 时按 Coq 语义下溢为 `0`——这是本定义的**刻意行为**而非隐藏陷阱：`corr 0 a = kloop 0 (2·0 − 1) a = kloop 0 0 a == 0`（`kloop` 首分支直接返回 0，见下段），归纳基例随之 trivial。本文**不**改用 `N` 类型或分段写法（`m=0` 时 0、否则 …），因为 `corr` 的 nat 索引形态贯穿 `Section QExpEOSplit` 全套引理（行差分 `corr_diff_*`、`esq_sum`/`osq_sum` 双和的 nat 索引等，§5.4 与附录 A），改动索引形态会牵动 16+ 条已闭合引理而零数学收益；下段与 §5.1/§5.2 对该基例行为作了显式说明，`vm_compute` 亦可数值复核（§5.3），读者无需依赖 Coq nat 减法语义的专门知识。

关于基例 `m = 0` 的计算行为需作显式说明：`corr 0 a = kloop 0 (2·0 − 1) a`，而 Coq 的 nat 减法把 `2·0 − 1` 计算为 `0`（`0 − 1 = 0`），于是 `corr 0 a = kloop 0 0 a`；`kloop` 的第一分支（`k = 0`）直接返回 0，故 `corr 0 a == 0`——不存在减法下溢问题，归纳基例随之 trivial。直观上，因 `E−O = S_{2m}(−a)`、`E+O = S_{2m}(a)`（`e_o_split_even/pos`），主恒等式即有限截断乘积恒等 `S_{2m}(−a)·S_{2m}(a) == 1 + corr m a`（`exp_even_mul_eq`）；对照无穷级数事实 `exp(−a)·exp(a) == 1`（经典指数级数理论，如文献 [4]），截断到 2m 项后低次（≤ 2m 次）偶次项系数经交错二项式系数和恒等（§5.4 `altf_zero` 层）两两抵消，恰好只留下高次过剩项（次数 2m+2 至 4m）——`corr m a` 正是这批项的三角双和，即「有限截断相对极限值 1 的过剩量」；`corr_nonneg` 证 `a ≥ 0 ⟹ corr m a ≥ 0`，故 `S_{2m}(−a)·S_{2m}(a) ≥ 1`，负输入处截断正性由此而来。

**低阶实例（`m = 2, a = 1`）**：按定义手算核验 `corr 2 1 == 1/64`。偶部分和 `E_2(1)` 含偶次项至 4 次：`E_2(1) = 1 + 1/2! + 1/4! = 1 + 1/2 + 1/24 = 37/24`；奇部分和 `O_2(1)` 含奇次项至 3 次：`O_2(1) = 1/1! + 1/3! = 1 + 1/6 = 7/6`。于是

```
E_2(1)² − O_2(1)² = (37/24)² − (7/6)² = 1369/576 − 784/576 = 585/576 = 65/64 = 1 + 1/64,
```

由主恒等式 `E_m(a)² − O_m(a)² == 1 + corr m a` 得 `corr 2 1 = 1/64`——即截断到 4 阶时相对极限值 1 的过剩量恰为 1/64（低次项两两抵消后仅剩的高次过剩项之和，见上段）；该值亦与 §5.3 的 `vm_compute` 复核（`E=37/24, O=7/6, E²−O²=65/64, corr=1/64`）一致。

**逐项分解**：按上框逐字定义直接代入，`corr 2 1 = kloop 2 3 1` 展开为三项（`k=3` 支 `j=1` 一项、`k=2` 支 `j=1,2` 两项；`k=1` 支因 `Nat.leb 2 1 = false` 归零）：

```
corr 2 1 = brk2 2 1 1 + brk2 2 2 1 + brk2 3 1 1 = 1/72 + 1/720 + 1/2880 = 45/2880 = 1/64,
```

与上段经偶/奇部分和平方的手算路径在 `1/64` 汇合——同一定义的两条独立代入互为复核。

**引理 4.4**（`corr_nonneg`）：`forall (a : Q) (m : nat), Qle 0 a -> Qle 0 (corr m a)`。

**引理 4.5**（`altf_zero`）：`forall N, (1 <= N)%nat -> altf N == 0`。

### 4.3 偶/奇双和展开

定义偶部分和 `e_sum`、奇部分和 `o_sum`，以及对应的行/双和 `esq_row` / `esq_sum` / `osq_row` / `osq_sum`。

**引理 4.6**（`e_mul_term`）：`E_m(a) · a^{2N}/(2N)! == esq_row N m a`。

**定理 4.7**（`e_sq_expand`）：`E_m(a)^2 == esq_sum m a`。

**引理 4.8**（`o_mul_term`）：`O_{S m}(a) · a^{2N+1}/(2N+1)! == osq_row N m a`。

**定理 4.9**（`o_sq_expand`）：`O_m(a)^2 == osq_sum m a`。

`o_sq_expand` 的证明是正性证明的关键进展：它处理了奇侧双和的对角去重（`osq_sum` 中 `2 * osq_row m' m' a - 对角`）与 Fixpoint 索引形态不一致问题。

---

## 5 `esq_eq_corr` 的证明与剩余目标

### 5.1 目标陈述

```coq
Lemma esq_eq_corr : forall (a : Q) (m : nat),
  e_sum m a * e_sum m a - o_sum m a * o_sum m a == 1 + corr m a.
Proof.
  intros a m. induction m as [| m' IH].
  - simpl. reflexivity.                       (* m=0：E_0=1, O_0=0, corr 0=0 *)
  - destruct m' as [| m''].
    + unfold ...; simpl; field; apply q_fact_pos.   (* m=1：直接计算 *)
    + assert (Hstep : ... == (E_{m''}² - O_{m''}²) + (corr (S(S m'')) a - corr (S m'') a)).
      { apply (corr_diff_eq_sq_diff a (S m'')). lia. }
      setoid_rewrite Hstep. setoid_rewrite IH. unfold Qminus. ring.
Qed.
```

经 `e_sq_expand`/`o_sq_expand`，该式等价于 `esq_sum m a - osq_sum m a == 1 + corr m a`。归纳证明的关键是 `corr_diff_eq_sq_diff`：它把 `corr` 的差分化为偶/奇平方和的差分，从而把目标归约到归纳假设后由 `ring` 闭合。

该恒等式是负输入处截断部分和正性的核心代数关卡，现已证明，并直接推出下列 Q 层正性引理：

- `exp_even_neg_nonneg`：`forall a m, Qle 0 a -> Qle 0 (exp_partial (2*m) (- a))`——`a ≥ 0` 时偶阶截断 `exp_partial (2m) (−a)` 非负；
- `exp_even_neg_pos`：`forall a m, Qle 0 a -> Qlt 0 (exp_partial (2*m) (- a))`——同上但严格为正；
- `exp_partial_tail_pos`：`forall a m, Qle 0 a -> Qlt 0 (exp_partial (2*m + 2) (- a))`——偶阶尾截断（`2m+2` 阶）亦严格为正，是 `exp_even_neg_pos` 的下一阶形态，为 Real 层提升时的柯西尾论证提供逐阶正性；
- `cauchy_real_exp_pos`：Real 层指数正性 `forall x : Real, cauchy_real_exp x > 0`。

### 5.2 证明结构

实际证明采用对 `m` 的归纳，关键一步是 `corr_diff_eq_sq_diff`（前提 `1 ≤ m`）：它把 `corr` 的**单步**差分化为偶/奇平方和的**单步**差分，

```
corr (S m) a - corr m a == (E_{S m}² - O_{S m}²) - (E_m² - O_m²)   （1 ≤ m），
```

真归纳步（`m = S(S m'')`）即以 `m := S m''` 实例化此式，得 `E_{S(S m'')}² − O_{S(S m'')}² == (E_{m''}² − O_{m''}²) + (corr (S(S m'')) a − corr (S m'') a)`，从而把目标归约到归纳假设后由 `ring` 闭合。基例 `m=0`（`E_0=1, O_0=0, corr 0=0`）由 `simpl; reflexivity` 直接得（`corr 0 a == kloop 0 0 a == 0`，见 §4.2）；`m=1` 展开后由 `field` 配合 `q_fact_pos` 闭合——归纳结构为 `induction m` 后步内 `destruct m'` 特判 `m=1`，故真归纳步只需上述单步差，无须跨两阶的差分式。

**注记（`corr` 零基例）**：基例 `m=0` 所依赖的 `corr 0 a == 0` 是定义性事实而非库内命名引理：`corr 0 a = kloop 0 (2·0 − 1) a = kloop 0 0 a`——Coq 的 nat 减法把 `2·0 − 1` 下溢为 `0`，而 `kloop` 的首分支（`k = 0`）直接返回 0，故 §5.1 上框 `m=0` 支由 `simpl; reflexivity` 一步闭合（框内注释 `E_0=1, O_0=0, corr 0=0` 即此化简）。其角色：该事实正是 `esq_eq_corr` 归纳基例 `m=0` 的实质内容——`E_0² − O_0² == 1 − 0 == 1 == 1 + corr 0 a`。该减法下溢的刻意性已在 §4.2 防御性注记说明（非隐藏陷阱），此处不重复其动机讨论；化简内嵌于 `esq_eq_corr` 证明体的基例支，未单列为独立引理。

一个等价的因式分解形态有助于直观理解：因 `E−O = S(−a)`、`E+O = S(a)`，有

```
S_{2m}(−a)·S_{2m}(a) == 1 + corr m a,   即   E² − O² = (E−O)(E+O).
```

该形态与系数层 交错二项式恒等（见 §5.4 命名注记）在结构上一致，可视为同一恒等式的两种视图。

**`corr_diff_eq_sq_diff` 为何成立（直觉）**。把 `corr m a` 读作截断乘积 `S_{2m}(−a)·S_{2m}(a)` 相对极限值 1 的过剩量（§4.2），相邻阶过剩之差就是截断从 2m 加深到 2m+2 时新出现的系数项之和。该引理不能借主恒等循环证明（它正是 `esq_eq_corr` 归纳步的前件），机器从定义两侧独立展开：左侧经 `corr_succ_decomp` 把 `corr (S m) a − corr m a` 按 `brk2` 双和拆成行差形态 `ksum_diff m m a + inner2 … a`；右侧把 `(E_{S m}² − O_{S m}²) − (E_m² − O_m²)` 经 `e_sq_expand`/`o_sq_expand` 反用为双和相邻差——`esq_sum (S m) − esq_sum m` 的定义性单步只含新增行 `2·esq_row (S m) m a` 与其对角项（机器注释自证）。`ksum_diff_row` 与 `ksum_diff_row_rhs` 证明两侧落到同一行差表达式（本段所涉机件均以唯一名指称，其行号对照见 artifact 行号索引）：同一批新项在 corr 侧按 `brk2` 行计数、在平方侧按 esq/osq 行计数，逐项重合，仅余 `q_pow` 指数书写形态差（`2m+2m+2` 对 `4m+2`），经 `lia` 统一两侧后 `reflexivity` 闭合。直观上：`E_m² − O_m²` 相对 1 的超出量与 `corr m a` 是同一个量（主恒等），其差分自然相等——`corr_diff_eq_sq_diff` 是把这一事实落实为两套行和重组恒等的独立代数证明（`esq_eq_corr` 归纳步的完整机器脚本见 A.8）。

### 5.3 当前状态

`esq_eq_corr` 已完成证明，闭合了主恒等式。数值一致性另经 `vm_compute` 复核（`a=1, m=2`：`E=37/24, O=7/6, E²−O²=65/64, corr=1/64`；`m=3`：`103721/103680`），与构造性代数证明吻合。

由 `esq_eq_corr` 出发的下游链条现已全部闭合：`exp_even_neg_nonneg`、`exp_even_neg_pos`、`exp_partial_tail_pos` 均在 Q 层证明，并进一步在 Real 层证明 `cauchy_real_exp_pos`；`exp_neg_pos` 字段的 setoid 系对应已由实例回填为实值（`Real_RealInterfaceSetoid` 中 `exp_neg_pos := cauchy_real_exp_pos`，见 §8.2）。本条恒等式与 Real 层 exp 加法公式 `cauchy_real_exp_plus`（§6.6–6.7）的路线关系（依赖图、经济性、独立价值）见 §6.7 末段。

### 5.4 两个 交错二项式恒等与系数层支撑

`esq_eq_corr` 的系数层恒等依赖于 `Section QExpEOSplit` 尾部一组支撑引理，其中两个 交错二项式恒等已证明为 `Lemma`，并配有 16 条配套代数引理（完整清单与行号索引见附录 A）。

**命名注记**：本文正文称这两条恒等为**交错二项式恒等**——其结构是阶乘分母对的交错和，组合学亲属为交错二项式求和族（经 `altf_zero` 出发、`altf_as_sum_upto` 转和式、偶奇拆分与镜像配对得到），而非标准 Vandermonde 卷积（Σ_k C(r,k)·C(s,n−k) == C(r+s,n)）。库内名 `vander_4m2`/`vander_4m4` 沿用历史称谓「Vandermonde 型」，与经典 Vandermonde 卷积并不相同；库内改名将牵动 16+ 处索引引用而零数学收益，故保留库内名，读者可将其读作「交错二项式恒等（库内旧称 Vandermonde 型）」。

#### 5.4.1 支撑引理族（18 条，全部 `Qed`）

这些引理按作用分为三族：

- **Qeq 移项族**：`q_div_scale2`、`qeq_moved`、`qeq_moved_neg`、`qeq_moved_neg2`——完成 `Qeq` 等式移项与常数缩放（E₀/O₀ 抵消用）；
- **求和代数族**：`sum_upto_shift`/`sum_upto_scale`/`sum_upto_scale_neg2`（下标平移与因子提取）、`sum_upto_even_split(_odd)`（偶奇拆分）、`sum_upto_split_gen`（区间拆分）、`sum_upto_mirror_even/odd`（镜像对称配对）、`q_pow_one`/`q_pow_neg1_even/odd`（幂值归约）、`altf_as_sum_upto`（`altf N == Σ_{u=0}^{N} (−1)^u/(u!(N−u)!)` 的和式形态）；
- **两个 交错二项式恒等**：`vander_4m2`（a^{4m+2} 层）与 `vander_4m4`（a^{4m+4} 层），完整语句见 §5.4.2。

全部 18 条均以 `Qed.` 闭合；名称→行号对照见附录 A。

#### 5.4.2 两个 交错二项式恒等的完整语句

```coq
Lemma vander_4m2 : forall (m : nat),
  (1 <= m)%nat ->
  sum_upto m
    (fun j =>
       - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))
       + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ==
  2 / (q_fact (2 * m + 2) * q_fact (2 * m)) -
  1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1)).

Lemma vander_4m4 : forall (m : nat),
  (1 <= m)%nat ->
  sum_upto m
    (fun j =>
       - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))
       + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))
  - 2 / (q_fact (4 * m + 4) * q_fact 0)
  + 2 / (q_fact (4 * m + 3) * q_fact 1) ==
  1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2)).
```

**证明路线**（与代码证明一致）：

1. 取 `altf_zero (4m+2)`（或 `4m+4`），得 `altf N == 0`；
2. 经 `altf_as_sum_upto` 把 `altf_aux` 递归形态转为 `sum_upto` 形态；
3. 用 `sum_upto_even_split`/`_odd` 做偶奇拆分；
4. 用 `q_pow_neg1_even/odd` 把 `(−1)^u` 归约为 ±1；
5. 用 `sum_upto_mirror_even/odd` 做镜像配对（偶部×2、奇部×2，奇长时留中项）；
6. `qeq_moved*` 系列完成 Qeq 移项；`q_div_scale2` 收尾。

**核心洞察**：`0 == 2·Σ_{j=0}^{m} E_j − (2·Σ_{j=0}^{m−1} O_j + O_m) ⟹ 2·Σ_{j=0}^{m−1}(O_j−E_j) == 2·E_m − O_m == RHS`。`esq_eq_corr` 本质是一个多项式/组合恒等式，闭合它不需要新的数学工具，只需系统的代数重组。

#### 5.4.3 状态小结

除 §5.1–5.2 已述的归纳步核心 `corr_diff_eq_sq_diff` 外，系数层尚包括行差分部件 `row_diff_closed`、`ksum_diff_row_rhs`、`corr_diff_expand` 与两个 交错二项式恒等（语句见 §5.4.2），全部已闭合（名称→行号对照见附录 A/A.3）。

实际证明以对 `m` 的归纳组织上述部件：基例 `m=0` 与 `m=1` 直接闭合，归纳步借 `corr_diff_eq_sq_diff` 与归纳假设由 `ring` 收尾。系数层与 `esq_eq_corr` 已全部闭合，下游 Q 层正性与 Real 层 `cauchy_real_exp_pos` 亦已证明；剩余工作为抽象接口层面的签名对接（§8.2），与本条恒等式的证明相互独立。

---

## 6 从 esq_eq_corr 到 exp_neg_pos 实例化

### 6.1 链条概述

```
esq_eq_corr（已证）
  → exp_even_neg_nonneg / exp_even_neg_pos（已证）
  → exp_partial_tail_pos（已证）
  → cauchy_real_exp_pos（已证）
  → Setoid 版接口实例装配（Real_RealInterfaceSetoidCore / Real_RealInterfaceSetoid / RealEnhancedReal）
  → exp_neg_pos / exp_neg_plus 字段被具体 Real 的已证正性（与加法公式）填充
  → 下游抽象层定理（FEP / RLHF / Attention / Min-P）的假设集实际缩减
```

代码库已为具体 `Real` 组装三个 Setoid 系接口实例（`Real_RealInterfaceSetoidCore`、`Real_RealInterfaceSetoid`、`RealEnhancedReal`），超越函数字段按实例实值回填：完整版实例 `Real_RealInterfaceSetoid` 取 `exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`（L39450/L39452），增强版实例 `RealEnhancedReal` 以 Real 层派生引理回填（`exp_neg_pos := real_exp_neg_pos`、`exp_neg_plus := real_exp_neg_plus`，L41196/L41198——数学内容同源，见 §8.2）——`cauchy_real_exp_pos` 已通过实例字段进入接口层；以 `forall {RI : RealInterfaceEnhanced}` 陈述的下游抽象定理据此直接消费该实例（详见 §8.2）。

**证明依赖静态表**：为便于不熟悉 Coq 脚本的读者，把 §5–§6 的证明依赖（**纯示意**——叙述层概览而非 `coqdep` 机器依赖图，语义同 §5.3/§6.7/§8.2 一致；行号以 219 基线主文件为基准逐名实测命中；T-π3 双路线定理与终末定理 C 位于基座追加段）列示如下：

| 下游件 | 上游/来源 | 关系 |
|---|---|---|
| `exp_even_mul_eq`（代数枢纽） | `esq_eq_corr`（归纳驱动，经 `corr_diff_eq_sq_diff`） | 证明依赖 |
| `exp_even_neg_nonneg` / `exp_even_neg_pos` | `exp_even_mul_eq` | 证明依赖 |
| `exp_partial_tail_pos` | `exp_even_neg_pos` | 证明依赖 |
| `exp_partial_even_lower`/`odd_lower`/`tail_small`（Real 层提升件） | `exp_even_mul_eq` ＋ `real_norm_bounded` ＋ `exp_series_arch` | 证明依赖 |
| `cauchy_real_exp_pos` | 提升件族 | 证明依赖 |
| `exp_neg_pos` 字段回填（完整版实例；增强版经 `real_exp_neg_pos`） | `cauchy_real_exp_pos` | 接口字段回填 |
| `boltzmann_factor_pos` / `softmax_pos` / `minp_markov_kernel_normalized` | `exp_neg_pos` 字段 | 假设解除 |
| `cauchy_real_exp_plus`（exp_plus 路线） | 同源级数基座（`exp_partial`/`q_pow`/`q_fact`） | 独立支线 |
| `rs_add_sin` / `rs_add_cos` | `cauchy_real_exp_plus` | eps/3 方法模板沿用（非逻辑依赖） |
| `real_cos_pi_half_zero` → `real_pi_geom` → `real_pi_geom_between` | 同源级数基座 | sin/cos 独立支线 |
| T-π3 两条独立证明路线（单点轨/∀x 轨） | `real_pi_geom_between` ＋ 归零层（`b5dQ_E_rational_zero`） | 两条独立证明路线 |
| 终末定理 C（`b5dU_cos_piL_half_zero`） | 单点轨（routeA）/ `a3_closure_n5`（alt） | 双路径 |

注（如实）：`exp_partial_tail_pos` 与 lower/tail_small 族出自同一代数源 `exp_even_mul_eq` 的两条用途支线——前者提供「偶阶尾截断正性」的逐阶形态（§5.3 叙述），后者是 `cauchy_real_exp_pos` 机器证明体实际使用的提升件（经 `exp_partial_even_lower`/`exp_partial_odd_lower`/`exp_partial_tail_small`，以 `exp_even_mul_eq` 为代数底，根 L13143–L13436）；本图为叙述层依赖（同 §5.3/§6.1 既有链条），不作逐行调用边的承诺。实例字段口径：图中 `exp_neg_pos := cauchy_real_exp_pos`（L39450）为完整版实例 `Real_RealInterfaceSetoid` 的字段值；增强版实例 `RealEnhancedReal` 的该字段取 Real 层派生引理 `real_exp_neg_pos`（L41196，证明体即 apply `cauchy_real_exp_pos`）——图中以完整版实例为代表，两实例数学内容同源（§8.2）。

### 6.2 已证定理与剩余推论

**定理 6.1**（`cauchy_real_exp_pos`，已证明）：`forall x : Real, lt zero (cauchy_real_exp x)`。

**推论 6.2**（`exp_neg_pos` 实例化，已完成）：`forall x : R, lt zero (exp_neg x)` 由 `cauchy_real_exp_pos` 与 `exp_neg` 的接口字段等价性得到——Setoid 系增强版实例 `RealEnhancedReal` 已装配完成，其中 `exp_neg_pos := real_exp_neg_pos`（L41196：Real 层派生引理，其证明体即 unfold 后 apply `cauchy_real_exp_pos`，L40323–40327，数学内容同源）；完整版实例 `Real_RealInterfaceSetoid` 中该字段直接取 `cauchy_real_exp_pos`（L39450）（见 §8.2 与附录 B）。

### 6.3 Setoid 并行接口层与实例组装

就本层完成的内容，一句话概括：**本文证明了 `real_eq` 对全部算术运算与度量均满足 Proper 替换原理，建立了 metric 逐 eps 形式与柯西完备性的桥接（§6.4–6.5），并据此组装三个接口实例**——Core 实例 `Real_RealInterfaceSetoidCore`（`req := real_eq`，全库首个接口实例）、完整版实例 `Real_RealInterfaceSetoid`（在 Core 之上增加 exp 族 `exp_neg`/`exp_neg_pos`/`exp_neg_zero`/`exp_neg_plus` 与 log 族 `log_inv`/`log_inv_exp_neg`/`log_inv_one`/`log_inv_mult`）与增强版实例 `RealEnhancedReal`。三者全部字段逐一取自已证 Real 层引理（代表性回填如 `plus_assoc := real_plus_assoc`、`cauchy_complete := real_cauchy_complete_metric_natle`；超越函数字段按实例分列：完整版 `Real_RealInterfaceSetoid` 填 `exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log`（L39449–39453），增强版实例 `RealEnhancedReal` 填 Real 层派生形态 `exp_neg := real_exp_neg`、`exp_neg_pos := real_exp_neg_pos`、`exp_neg_plus := real_exp_neg_plus`、`log_inv := real_log_inv`（L41195–41205，数学内容同源，如 `real_exp_neg x := cauchy_real_exp (real_opp x)`、`real_log_inv x := −(cw_log x)`，见 §8.2））；实例字段的逐条清单与见附录 B，`exp_neg_plus` 的支撑代数（`ExpPlusStage2` 36 条 + `ExpPlusStage2b` 22 条 = 58 条引理）见 §6.6，超越函数字段实值化与签名对接见 §8.2。Setoid 系并行接口的深层数学动机（柯西实数的相等是近似相等，代数结构须在 `req` 上重述）见 §3.4。

**表（Setoid 接口字段实例化对照）**：下表按字段组对照 Id 系与 Setoid 系接口的字段形态及三个实例的回填值；表内字段名与行号均为 219 基线主文件逐名 grep 实测（2026-09-08 复核零平移），字段数按 Class 声明体内 `:` 声明条目计。

| 字段组 | Id 系（`RealInterface` L133 / `RealInterfaceEnhanced` L217，相等谓词 `Id`） | Setoid 系（`RealInterfaceSetoidCore` L32576 / `RealInterfaceSetoid` L32672 / `RealInterfaceEnhancedSetoid` L40464，相等谓词 `req`） | 实例回填（完整版 `Real_RealInterfaceSetoid` L39407 / 增强版 `RealEnhancedReal` L41115） |
|---|---|---|---|
| setoid 核心 | 无对应字段（`Id` 的替换由内核 J 规则自带） | `req`/`req_refl`/`req_sym`/`req_trans` | `req := real_eq` 及 `real_eq_refl`/`real_eq_sym`/`real_eq_trans` |
| Proper 替换原理 | 无对应字段 | 新增 6 字段：`req_plus_compat`/`req_mult_compat`/`req_opp_compat`/`req_abs_compat`/`req_lt_compat`/`req_le_compat` | `real_eq_plus_compat_adapt`（L33417）/`real_eq_mult_compat_adapt`（L33424）/`real_eq_opp_compat`/`real_eq_abs_compat`/`real_lt_compat`/`real_le_compat`（供给见 §6.4） |
| 常数/运算/环律/序律 | 8 运算字段 + 9 环律 + 12 序律（其中 6 条陈述含 `Id`，见右列） | 同名重述，相等谓词 `Id` → `req`（`le_antisym`/`lt_le_iff`/`le_id_l`/`le_id_r`/`lt_id_l`/`lt_id_r` 随之 req 化） | `real_zero`…`real_le` 与 `real_plus_assoc` 等 Real 层已证引理 |
| 正元求逆 | `inv_pos`/`inv_pos_correct`；增强版另有 `inv_pos_pos`/`inv_pos_ext`/`inv_pos_le_compat` | 同名重述并 req 化（`inv_pos_ext` 的外延性谓词 `Id` → `req`） | `real_inv_pos`/`real_inv_pos_correct`/`real_inv_pos_pos` 等 |
| exp 族 | `exp_neg`/`exp_neg_pos`/`exp_neg_zero`/`exp_neg_plus`（L181–184）；增强版另有 `exp_neg_decr`/`exp_neg_le_decr` | 同名 6 字段并 req 化（`exp_neg_pos` 结论不含相等谓词，两系语句一致） | 完整版：`cauchy_real_exp`/`cauchy_real_exp_pos`/`cauchy_real_exp_zero`/`cauchy_real_exp_plus`（L39449–39452）；增强版：`real_exp_neg`/`real_exp_neg_pos`/`real_exp_neg_zero`/`real_exp_neg_plus`（L41195–41198，数学内容同源，§8.2） |
| log 族（两系分水岭） | `log_inv : R -> R`（全定义域，L186）及 `log_inv_exp_neg`/`log_inv_one`/`log_inv_mult`（无前提）；增强版另有 `log`（全定义域）/`log_mult`/`log_one`/`log_inv_log`/`exp_neg_log_inv`/`log_le_linear`/`log_eq_linear` | **log 族带正性前提**：`log_inv`/`log : forall x, lt zero x -> R`，相应恒等随之前提化；`log_le_linear` 改逐 eps 形态 `log_le_linear_eps`；`log_eq_linear`（等号点形态）不设字段（构造性 `le` 的 Or 编码无法表达等号点，§6.5） | 完整版：`cw_log`/`log_inv_exp_neg_thm`/`log_inv_one_thm`/`log_inv_mult_thm`（L39453–39456）；增强版：`real_log`/`real_log_mult`/`real_log_one`/`real_log_le_linear_eps`/`real_log_inv`/`real_log_inv_log`/`real_exp_neg_log_inv`（L41201–41207） |
| metric 族 | `metric_pos`/`metric_triangle`（非严格形态） | 逐 eps 余量形式（§6.5）；`metric_zero` 的分离性谓词 req 化 | `real_metric`/`real_metric_sym`/`real_metric_pos_eps`/`real_metric_zero`/`real_metric_triangle_eps` |
| 极限与完备性 | `lim`/`lim_unique`/`cauchy_complete` | 同名重述并 req 化 | `real_lim`/`real_lim_unique`/`real_cauchy_complete_metric_natle` |
| 增强版序/选择字段 | `one_pos`、`lt_plus_compat`/`le_plus_compat`、`plus_positive`/`mult_positive`、`lt_mult_compat`/`le_mult_compat(_weak)`、`opp_lt_compat`/`lt_zero_opp`/`opp_le_compat`、`min` 族、`r_max` 族、`pos_test` 族、`pos_part` 族、`r_if` 族、`abs` 族（L217–L321） | 同名重述；其中 `min_le_l`/`min_le_r`、`r_max_le_l`/`r_max_le_r`、`pos_part_nonneg`、`abs_nonneg`、`abs_triangle` 逐 eps 化，`r_max_l_iff`/`r_max_r_iff`/`pos_part_def`/`abs_zero`/`abs_mult`/`abs_opp`/`abs_pos` req 化 | `real_lt_zero_one`（L41157）、`real_min_le_l_eps` 等 Real 层已证引理逐条回填（逐条清单见附录 B） |

表注（Bishop 形对照，两形态并存）：上列「逐 eps 化」字段与其 Real 层回填件（`real_min_le_l_eps` 等七件、`real_log_le_linear_eps`、`real_metric_pos_eps`/`real_metric_triangle_eps`、`real_exp_abs_minus_one_eps`、`real_exp_ge_linear_eps`、`real_gibbs_inequality_eps`）的 **Bishop 形对应物已全部建成**（`UpRealLeB.v`：`real_min_le_l_B`/`real_min_le_r_B`/`real_r_max_le_l_B`/`real_r_max_le_r_B`/`real_pos_part_nonneg_B`/`real_abs_nonneg_le_B`/`real_abs_triangle_le_B`/`real_log_le_linear_B`/`real_metric_pos_B`/`real_metric_triangle_B`/`real_exp_abs_minus_one_B`/`real_exp_ge_linear_B`/`real_gibbs_inequality_B` 等；逐件经全量编译、提取检查与内核检查）。注意模块前缀：`real_metric_*` 在 `RealSetoid`、`real_exp_ge_linear_eps`/`real_log_le_linear_eps` 在 `RealInterfaceEnhancedMod`（模块前缀经 grep 实测）。

规模口径（grep 实测）：`RealInterface` 48 字段（含载体 `R : Set`）、`RealInterfaceEnhanced` 经 `RI_base :>` 继承并另含 47 字段；`RealInterfaceSetoidCore` 49 字段、`RealInterfaceSetoid` 57 字段（= Core + exp 族 4 + log 族 4）、`RealInterfaceEnhancedSetoid` 100 字段（全显式不继承）。两系字段一一对应，实质差别集中于上表 setoid 核心、Proper 原理、log 族与 metric 族各行——相等谓词、Proper 原理、log 正性前提与 metric 逐 eps 形态，后者正是该系可由具体 `Real` 实例化的原因。

### 6.4 Proper 兼容性引理族

`real_eq` 的 Proper（集合等式替换）原理是实例组装的关键前置。本文证明了 `real_eq` 对全部算术运算与度量满足 Proper 兼容性，并建立了序的等式替换传递：`real_eq_plus_compat`、`real_eq_opp_compat`、`real_eq_mult_compat`、`real_eq_abs_compat`、`real_lt_compat`、`real_le_compat` 及 `real_lt_id_l/r`、`real_le_id_l/r`（逐条引理与见附录 B）。另有 `real_eq_le`、`real_lt_le_iff_req` 两条序桥与 `real_eq_plus_compat_adapt`、`real_eq_mult_compat_adapt` 两条参数序适配引理，供接口 Proper 字段直接引用。

其中证明复杂度较高的是 `real_eq_mult_compat`：乘积的等式保持需要因子的一致界（柯西序列范数有界性）与乘积差三角界，采用与 `real_mult` 同构的 eps/(2M) 阈值分割结构（`1+|a|`、`1+|d|` 的正界提升）——这正是完整版实例 Proper 字段的主要 Real 层供给。

### 6.5 metric 逐 eps 形式与完备性桥

度量族与完备性桥解决两个具体问题：

1. **逐 eps 余量形式**：本库 `real_le = Or (real_lt) (real_eq)` 的构造性编码无法直接表达「非严格且不趋近」的度量正性与三角不等式，故采用逐 eps 余量形式——`real_metric_pos_eps`（`0 < eps ⟹ 0 ≤ metric a b + eps`）与 `real_metric_triangle_eps`（`0 < eps ⟹ metric a c ≤ metric a b + metric b c + eps`），即「对任意正 eps 余量成立」；配套的对称性 `real_metric_sym` 与分离性 `real_metric_zero`（`metric a b ≈ 0 ⟹ a ≈ b`）给出度量论基本性质。该论断在 Or 编码下成立不变；同一事实族现已另有**谓词级封装**：序谓词 `real_le_b x y := ∀eps>0, x < y+eps`（Set 层 forall 型，`UpRealLeB.v`，判定 1）把「逐 eps 余量」打包为非严格序形——`real_metric_pos_B`/`real_metric_triangle_B` 等装配件（装配引理 `real_le_closure_b_one` 单步＋源件直连，零新增前提）与 Or 形不可证的同框对照（`min a b ≤ a` 精确版不可证、Bishop 形 `real_min_le_l_B` 可证，判定 2/7）一并交付，Print Assumptions 全 Closed。「最强形式」与「Bishop 封装」并行不悖：前者是 Or 编码内的最强陈述，后者是该编码外的等强度序形表述。
2. **柯西完备性桥**：接口 `cauchy_complete` 字段以 metric 形式陈述，具体层 `real_cauchy_complete`（零 Variable）以双向 `real_lt` 形式陈述，二者经 `real_cauchy_complete_metric` 桥接；再经索引桥（`NatLe_to_le`/`le_to_NatLe`、`Id_eq`/`eq_Id`）适配接口的 NatLe 索引形态，得到 `real_cauchy_complete_metric_natle`——这正是实例 `cauchy_complete` 字段的直接来源（见附录 B）。

**对下游形式化的意义**：抽象接口轨上依赖 `cauchy_complete` 字段的定理（如收敛动力学中的极限存在性），在具体 Real 轨已有零 Variable 的对应物；本节所述桥接已落实为实例字段的实际装配（完备性与 exp/log 全部字段实值，见 §8.2 与附录 B）。

### 6.6 `exp_neg_plus` 第二阶段：二项式/部分和代数与截断误差（58 条引理）

`exp_neg_plus`（`exp (x+y) == exp x · exp y` 的柯西实数版本）的构造性闭合分两个 Section 实现：`Section ExpPlusStage2`（36 条引理）提供组合数展开与部分和重组的代数拼图——二项式系数与二项式定理（`q_choose`、`q_binom`）、配对索引重组（`q_binom_pair_mid/_head/_tail/_S`）、部分和标量/移位/除法/乘积代数（`sum_upto_*`）、单项分解（`exp_term_binom`/`exp_term_split`）与双重 Cauchy 和重组（`exp_cauchy_swap`/`exp_cauchy_double`/`exp_prod_double`）；`Section ExpPlusStage2b`（22 条引理）在其上叠加截断误差上界——把双和残差夹在 `exp_series · exp_tail_abs` 之间（头条 `exp_trunc_band_up`），并新增 `exp_trunc_bound`/`exp_trunc_arch`/`exp_trunc_arch_seq` 把误差证明为随阶数可构造地趋于 0，为 §6.7 的 `cauchy_real_exp_plus` 提供 Q 层「代数 + 分析」底层。两节合计 58 条引理，全部零 `Variable`；逐条清单与行号索引见附录 A。

**定位**：上述两节把「组合数展开 + 部分和重组 + 截断误差控制」路线在 Q 层全部实现为零 `Variable` 引理，并沿对角序列提升到构造性柯西实数层，在语义层证明顶层定理 `cauchy_real_exp_plus`（`cauchy_real_exp (x+y) == cauchy_real_exp x · cauchy_real_exp y`，§6.7）。该最终闭合已回填进 Setoid 系接口实例（`Real_RealInterfaceSetoid` 中 `exp_neg_plus := cauchy_real_exp_plus`）；本文定理所涉抽象层签名的接入待签名统一（§8.2）。`exp_neg` 的同态性（`exp_neg_plus`）与正性（由 `cauchy_real_exp_pos` 供给）由此均在其语义层闭合。


**`Section ExpPlusStage2b`：截断误差上界**。`ExpPlusStage2b` 把阶段 2 从「代数重组」推进到「截断误差分析」：先经求和绝对值三角不等式（`sum_upto_abs_le`）与逐项幂-阶乘上界（`q_abs_pow_fact_le`）建立双和残差的构造性上界——头条 `exp_trunc_band_up` 把残差夹在 `exp_series n B · exp_tail_abs n (2n) B` 之间，再经 `exp_trunc_bound`/`exp_trunc_arch`/`exp_trunc_arch_seq` 把该误差证明为随 n 可构造地趋于 0。配合 ExpPlusStage2 的代数重组（`exp_cauchy_double`/`exp_prod_double`），`exp (x+y)` 的有限部分和便能以构造性可证方式收敛到 `exp x · exp y`——这一收敛正是 `cauchy_real_exp_plus`（§6.7）的证明内核。该最终闭合已回填进 Setoid 版接口实例（`Real_RealInterfaceSetoid` 中 `exp_neg_plus := cauchy_real_exp_plus`，见 §8.2）；引理级清单与行号索引见附录 A。

---

### 6.7 顶层定理 `cauchy_real_exp_plus`

`cauchy_real_exp`（构造性柯西实数直接指数）语义层已证明阶段 2 的**顶层定理**：

```
Lemma cauchy_real_exp_plus : forall x y : Real,
  real_eq (cauchy_real_exp (real_plus x y))
          (real_mult (cauchy_real_exp x) (cauchy_real_exp y)).
```

即 `exp(x+y) = exp(x)·exp(y)` 在柯西实数模型上以构造性方式成立。其证明内核为：对任意 eps > 0，借 `real_norm_bounded` 取 x、y 的范数界 Mx、My，将 `exp (x+y)` 的有限部分和经 ExpPlusStage2 的对角重组（`exp_cauchy_double`/`exp_prod_double`）化为双和，再借 ExpPlusStage2b 的截断误差界（`exp_trunc_band_up` + 后续新增 `exp_trunc_bound`/`exp_trunc_arch`/`exp_trunc_arch_seq`）证明该双和残差 < eps，从而由实数完备性得等式。

**层次界定**：`cauchy_real_exp_plus` 闭合的是 `cauchy_real_exp` **语义层**的 exp 加法公式，并已由 setoid 系接口实例回填为接口字段（`Real_RealInterfaceSetoid` 中 `exp_neg_plus := cauchy_real_exp_plus`）；下游抽象定理（如依赖 `exp_neg_plus` 的 Gibbs 推导）假设集的缩减随抽象层签名统一完成（§8.2）。本工作的边界是：**语义层 exp 加法公式已机器检查证明，并已通过实例回填进入接口层**。

**与 `esq_eq_corr` 路线的相互关系（技术路线讨论）**：两条路线**在证明策略与上层引理上互不依赖**。二者共享 `exp_partial`、`q_pow`、`q_fact` 等基础定义，因此并非「完全独立」；严格地说，它们是同一级数基座之上、面向不同目标的两套独立证明，构成机器检查层面的交叉验证。esq 路线由 `esq_eq_corr`（Q 层有限恒等）经 `exp_even_neg_nonneg/pos`、`exp_partial_tail_pos` 到 `cauchy_real_exp_pos`，全程纯 Q 层代数（归纳 + ring + 交错二项式系数层，见 §5.4 命名注记），**零截断误差分析**；`cauchy_real_exp_plus` 则由 `ExpPlusStage2`/`ExpPlusStage2b`（58 条引理：Cauchy 积展开 + 截断误差收敛）支撑，其证明不引用 `esq_eq_corr`/`cauchy_real_exp_pos`/`exp_even_neg*`，且 esq 定义在先（Coq 无前向引用），故二者在依赖图中互不引用。就「负输入正性」（`exp(−x) > 0`、接口字段 `exp_neg_pos`）这一目标，esq 路线更直接：`S_{2m}(−a)·S_{2m}(a) == 1 + corr m a ≥ 1`（`exp_even_mul_eq` + `corr_nonneg`）在 Q 层即闭合，`cauchy_real_exp_pos` 直接充当实例字段值，无需完备性/eps 余量机械。后续认证的级数 ε-见证路线（`UpReqExpPos`，见下段披露）与有限截断代数路线、指数加法路线均正交：其正性见证由级数尾项直接构造，不依赖主恒等式，亦无须任何三分律形态。`cauchy_real_exp_plus` 的独立价值在其**函数方程**地位：`exp(a)·exp(−a) == exp(0) == 1` 与 esq 侧的 `exp_even_mul_eq` 恰是同一「±对称乘积 == 1」事实的极限/有限两种形态——两条独立闭合的机器证明互相印证；`cauchy_real_exp_plus` 还是 exp–log 保序群同构、exp 可微（§9.1）与和角恒等 `rs_add_sin`/`rs_add_cos`（沿用其 eps/3 装配模板）的共同基座。故本库保留两条路线：esq 提供最短、可 `vm_compute` 数值复核、直接供给下游字段值的 Q 层有限正性链；exp_plus 提供完整指数律与可迁移的 eps/3 方法模板。

**后续认证披露（本文基线之后的库内新增，与 esq/exp_plus 双路线并行；载体为独立模块层 `UpReq*` 系，行数与行首 `Qed.` 数为实测（2026-09-13/14），逐件均经全量编译、提取检查与内核检查，并经 `Print Assumptions` 确认 `Closed under the global context`（验证细节见补充材料 S0））**：

- **`UpReqExpPos`**（165 行/4 处行首 `Qed.`）：`0 < eˣ` 对全部实数无条件成立的级数 ε-见证构造（`upreq_exp_pos` 及 Or 分拆形态 `upreq_exp_pos_or_destruct`）——如 §2 所析，这是平方捷径不可行背景下可行的正性路线族之一。
- **`UpReqExpPosWitness`**（83 行/2 处行首 `Qed.`）：见证显式化——提取后 ε := 1/(2C) 以有理数字面现形（提取验证 `Obj.magic=0`），正性见证成为可计算输出。
- **`UpReqExpPosQBound`**（353 行/12 处行首 `Qed.`）：Q 层偶阶截断的显式正下界 `upqb_even_witness`（`q := 1/(1+B)` 形），与 1/(2C) 形互不依赖，构成同一正性的两条独立见证路线。
- **`UpReqPadeExp`/`UpReqPadeSign`**（200 行/7 与 133 行/4）：Padé [n/n] 逼近的系数正性、分母对称与分母正性（n=0/1）；数值哨兵 `pade_num_1_half`/`pade_den_1_half`（P₁(1/2) == 5/4、Q₁(1/2) == 3/4）实测在件（其后续通用 n 化见 §9.2 方向 C 披露）。
- **`UpReqPadeBetaPos`/`UpReqPadeTailPos`/`UpReqPadeLower`/`UpReqPadeDenPos12`/`UpReqPadeFinale`**（284 行/9、179 行/6、385 行/15、275 行/8 与 421 行/22 处行首 `Qed.`）：Padé 余项正尾性的免积分构造性直证——余项尾分解为正系数级数（尾系数 β 逐项为正：`ptp_beta_pos`，n=1/2 两侧逐 m 数值件与 β₀=1/720 见证 `cpl_sent_witness_half` 在件；偶阶下界 `cpl_lower_even`），终件 `cpf_exp_pos_pade2` 经 Padé [2/2] 链闭合 0 < eˣ，同件以直组装给出 Real 层 n=2 定量旗舰 `cpf_exp_pos_final_n2`（对 0<x 的有理点闭合 `real_lt real_zero (cauchy_real_exp (real_const x))`，`Print Assumptions` 零假设；详见 §9.2 方向 C）。学术定位如实申明：正尾性的数学实质属经典 Hermite–Padé 余项理论；本库贡献限于免积分的构造性直证（不依赖积分表示，适配无经典基建的形式化环境）与相应的机器可检验工件。五件已注册入当前认证面（注册波 35f2495，现认证面 HEAD=97cbc4a）。
- **`UpReqAltSumPos`**（677 行/25 处行首 `Qed.`）：非负递减序列有限交错和正性引擎（`altsum_pos_strict`），为 Padé 符号面的通用代数底座。
- **`UpReqBanachExp` 系及后续扩展（Banach 代数推广）**：实数层正性链向 Banach 代数层的推广已升格为正文一章——Set 层 `Class BanachAlg` 类底座、指数级数柯西主定理（`esp_diff_le_tail`/`exp_series_cauchy`）、加法交换律 `bxae_exp_add`（`UpReqBanachExpAddEq` 闭合并云认证）、e⁰ == 1、可逆性侧 `bxoo_exp_opp_one` 与 ε-近邻链 `bxcd_prod_near_one`、实例非空性装配（`UpReqBanachInstReal`），陈述、行号、证明结构概述与体量详见 §7。完整构造性谱定理仍为开放问题（§7.3–§7.4），而 C* 代数的定义面（对合 ＋ C* 恒等式 ‖a*a‖=‖a‖²）与严格正元 Newton 平方根的构造性显式率已于模块层机器检查（§7.3；该件头注自陈为「谱定理阶梯第 1 级开工件」）。

上述认证面的完整披露与逐件状态，与 §9.2 未来工作的三路径现状（见该节）互为呼应。三路载体为互不引用的独立模块，各自经同一套验证关卡（全量编译、提取检查、内核检查、假设审计）；任一路内的未决项不传染其余两路的已认证结果。

**范围外披露（Strong 及其他）**：本文基线之后，库内 Banach 推广线已升格为正文 §7——其定理面（加法交换律、可逆性侧、ε-近邻链、实例装配）与支撑件（分离定理 `UpReqBanachSepThm`（`spt_bxce_sep_real`）、范数对偶件 `UpReqBanachNormOpp`、无假设件 `BanachNoHyp`/`BanachNoHypNorm`（接口显式形参假设负债消解））的状态与验证面见 §7，Banach 类签名层两行手术（范数字段余域 Id→QeqT，公理面零新增）已注册（§7.4 一句备查）；本段保留非 Banach 件：B4 两段式 `UpReqB4TwoStage`（Padé 余项两段式模型）与 S11–S15 源侧 `Psatz` 移除（163 件闭包面）已随 b657aff 注册波并入认证面；第八波 Strong（qnorm Id 形强化轨）已注册；其后另有模块整合与注册波推进中，以随论文 artifact 的变更记录为准。上述结果与本文 A 路（esq/exp_pos 主线）定理族平行，不改变本文 C1–C4 贡献边界与 81 条@198/206 分层口径（认证记录与验证命令见补充材料 S2/S0，与正文披露互指）。

---

## 7 Banach 代数推广

**定位与动机**。§3–§6 的指数正性链工作于柯西实数这一具体载体上，但其证明所消费的代数结构——加法交换群、乘法幺半群（含双分配）、Q 标量嵌入、Q 值范数与完备性——并不依赖实数的序结构或三分律。本章把该链条中最核心的三件事实——指数级数的柯西性、加法交换律 `exp(a)·exp(b) == exp(a+b)` 与基础律 e⁰ == 1（及可逆性侧）——推广至 Bishop 式 Banach 代数：一个 Set 层 `Class BanachAlg` 抽象载体上的全称定理族，柯西实数仅作为其具体实例之一。载体为独立模块层 UpReqBanach 系（26 件、11,568 行、345 处行首 `Qed.`、1 处 `Defined.`，行首 `Admitted`/`admit` 零出现）；逐件均经全量编译、提取检查与内核检查，并经 `Print Assumptions` 确认 `Closed under the global context`（验证细节见补充材料 S0）；实例装配波随 b657aff 注册波并入认证面（§1.3「当前库真态声明」）。本章行号均为开发树 Live_X 各件实测坐标（2026-09-16 复核实测），区别于正文其余部分以 219 基线主文件为基准的行号口径（§1.1）。

### 7.1 类底座与级数收敛

**Banach 代数类（`Class BanachAlg`，`UpReqBanachExp.v` L39）**。类字段全部置于 Set 层：载体 `BA : Set`；Set 层等词 `bae`（自反/对称/传递）；常数与运算 `bzero`/`bone`/`bplus`/`bmult`/`bopp`；Q 标量嵌入 `bcoef : Q -> BA`（级数系数 1/k! 的载体）与 Q 值范数 `bnorm : BA -> Q`。公理面为加法交换群律（`bplus_assoc`/`bplus_comm`/`bplus_zero`/`bplus_opp`）、乘法幺半群与双分配（`bmult_assoc`/`bmult_one_l`/`bmult_one_r`/`bdistrib_l`/`bdistrib_r`/`bmult_zero`）及等词-运算相容（`bplus_wd` 族）。两点设计如实声明：其一，乘法**不交换**——交换律不在类字段内，非交换性是本类的关键面；其二，等词取 Set 层 `bae` 而非 Prop 层 `eq`，与全库 Set 层可提取口径一致（§8.4）。

**级数柯西主定理（`UpReqBanachExp.v`，482 行/14 处行首 `Qed.`）**。指数级数 `exp_series_partial B a n := Σ_{k≤n} bpow a k · bcoef (1/k!)` 的收敛不依赖交换性，其证明是 §3.2 实数侧截断估计的范数化重述：

```coq
Lemma esp_diff_le_tail : forall (B : BanachAlg) (a : (@BA B)) (m n : nat),
  (m <= n)%nat ->
  QleT' (@bnorm B (@bplus B (exp_series_partial B a n)
                            (@bopp B (exp_series_partial B a m))))
        (exp_tail_abs m n (@bnorm B a)).            (* UpReqBanachExp.v L351 *)

Lemma exp_series_cauchy : forall (B : BanachAlg) (a : (@BA B)),
  bcauchy B (fun n => exp_series_partial B a n).    (* UpReqBanachExp.v L410 *)
```

**exp 元素的 sigT 定义（`UpReqBanachExpDef.v`，183 行/7 处行首 `Qed.`）**。类内完备性见证 `bcauchy_complete_sig`（`UpReqBanachExp.v` L173）把柯西性提升为「极限元素 + 收敛见证」的 sigT 对：

```coq
Definition bxdef_exp (B : BanachAlg) (a : (@BA B)) : (@BA B) :=
  projT1 (bxdef_exp_pair B a).                      (* UpReqBanachExpDef.v L55 *)
```

其中 `bxdef_exp_pair` 由 `bcauchy_complete_sig B _ (exp_series_cauchy B a)` 一步构成。该定义「定义即算法」：右端携带级数部分和的结构递归实参，提取产物含 Fixpoint（提取验证零 Prop 残留，§8.4 口径）；收敛规格 `bxdef_exp_spec`/`bxdef_exp_spec_eps`（同件 L59/L66）保证 `bxdef_exp` 是部分和序列的 `blim` 极限。双和的范数控制由范数卷积件承担（`UpReqNormConv.v`，888 行/24 处行首 `Qed.`：`ncv_norm_conv_le` 等）。

### 7.2 加法交换律

**代数前置（三件）**。加法交换律 `exp(a)·exp(b) == exp(a+b)` 的机器证明由三层代数组装：① 二项式展开——`(a+b)^n` 的 Pascal 配对重组（`UpReqBanachAdd.v`，756 行/15 处行首 `Qed.`：头条 `bpa_bpow_add` L355，配对件 `bpa_pair_head/mid/tail` L269/L290/L323，与 `bpa_esp_binom` L715 的部分和二项式形态）；② 配对桥——自建二项式系数 `bpa_binom` 与库内 `q_choose` 的逐项恒等（`UpReqBanachBinomBridge.v`，166 行/4 处行首 `Qed.`：`bxcb_binom_eq_bpr2` L153；数值哨兵 `bxcb_sentinel_bridge_4_2` L112：bpa_binom 4 2 == q_choose 4 2 == 6）；③ 柯西方块恒等——乘积部分和的三角-矩形双重和重组（`UpReqBanachDouble.v`，318 行/5 处行首 `Qed.`：`bd2_tri_eq_diag`/`bd2_tri_eq_rect` L180/L272），落点为乘积展开恒等：

```coq
Lemma esp_prod_square : forall (B : BanachAlg) (a b : (@BA B)) (n : nat),
  @bae B (@bmult B (exp_series_partial B a n)
                   (exp_series_partial B b n))
         (bsum B (Datatypes.S n)
            (fun j : nat => bsum B (Datatypes.S n)
               (fun i : nat =>
                  @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                           (@bmult B (bpow B b i) (@bcoef B (/ q_fact i)))))).
   (* UpReqBanachProd.v L296 *)
```

（`UpReqBanachProd.v` 413 行/12 处行首 `Qed.`，配套 `UpReqBanachProd2.v` 222 行/7 处行首 `Qed.`。）

**主定理（`UpReqBanachExpAddEq.v`，1,152 行/26 处行首 `Qed.`）**。逐字陈述：

```coq
Theorem bxae_exp_add : forall (E : BanachAlgExt) (a b : (@BA (@bxce_base E))),
  @bae (@bxce_base E) (@bmult (@bxce_base E) a b) (@bmult (@bxce_base E) b a) ->
  @bae (@bxce_base E)
       (@bxdef_emul (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                    (bxdef_exp (@bxce_base E) b))
       (bxdef_exp (@bxce_base E) (@bplus (@bxce_base E) a b)).
   (* UpReqBanachExpAddEq.v L1125 *)
```

即 `exp(a)·exp(b) == exp(a+b)`，前提仅为交换面 `a·b == b·a`（陈述首行 `hab`）。**证明结构概述**：柯西方块恒等把 `exp(a)` 与 `exp(b)` 的部分和乘积展开为双重和（`esp_prod_square`）；二项式行组装把该双重和识别为 `exp(a+b)` 部分和的行和（`bxae_binom_row`/`bxae_prod_row`/`bxae_tri_row`，L663/L693/L713）；误差侧经 Q 层分块上界 `bxae_block_norm_le`（L972）与尾界收得「部分和乘积 − exp(a+b) 部分和逐 eps 趋于零」（`bxae_diff_small` L1053，其块界使用交换面 `hab`）；最后由乘积极限 `bxadd_esp_prod_blim`（`UpReqBanachExpAdd.v`，456 行/12 处行首 `Qed.`）、极限移位 `bxae_lim_shift`（L1080）与极限唯一性 `bxuq_lim_uniq`（`UpReqBanachLimUniq.v` L188）总装闭合。**前提位如实**：非交换 Banach 代数上指数函数一般不满足加法公式，交换面前提是数学内容的组成部分而非技术缺陷；交换情形覆盖交换 Banach 代数与非交换代数中的可交换元对。扩展类 `BanachAlgExt`（`UpReqBanachClassExt.v`，206 行/5 处行首 `Qed.`）为冻结类 `BanachAlg` 的扩展（底类 + 标量嵌入加法等新字段，禁改原类），主定理以该类陈述以取得非交换乘积定义 `bxdef_emul` 的良好定义性。

### 7.3 基础律与可逆性侧（部分闭合，如实标注）

**e⁰ == 1（`UpReqBanachExpBasic.v`，265 行/7 处行首 `Qed.`）**。零元处级数恒为单位：`bxb_series_zero`（L101：零元级数逐项为零）、`bxb_norm_series_zero`（L122）与 `bxb_expdef_exp_zero_close`（L218：`bxdef_exp B bzero` 任意 eps 逼近 `bone`）。

**exp(−a) 的级数识别（`UpReqBanachExpNeg.v`，295 行/12 处行首 `Qed.`）**。(−1)^k 的奇偶归约（`bxn_mone_sq`/`bxn_series_mone_even`/`bxn_series_mone_odd` L74/L117/L151）给出 `exp(−a)` 的级数与柯西实数侧负项级数同型的交错形态；收敛规格 `bxn_exp_neg_spec`（L49）与 `bxdef_exp_spec` 对称。

**可逆性侧主腿（`UpReqBanachExpOppOne.v`，219 行/7 处行首 `Qed.`）**。逐字陈述：

```coq
Theorem bxoo_exp_opp_one : forall (E : BanachAlgExt)
  (a : (@BA (@bxce_base E))),
  @bae (@bxce_base E)
    (@bmult (@bxce_base E) (bxdef_exp (@bxce_base E) a)
                   (bxdef_exp (@bxce_base E) (@bopp (@bxce_base E) a)))
    (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E))).
   (* UpReqBanachExpOppOne.v L207 *)
```

即 `exp(a)·exp(−a) == exp(0) == 1`。**证明结构概述**：ε-近邻链 `bxcd_prod_near_one`（`UpReqBanachCauchyD.v` L1154，该件 1,423 行/34 处行首 `Qed.`）构造性地证明部分和乘积逐 eps 逼近 1——对任意 q > 0 产出 N，使 n ≥ N 时 ‖esp a n · esp(−a) n − 1‖ < q；再经近一极限 `bxoo_nearone_blim`（L100）与装配定理 `bxoo_exp_opp_one_assembly`（L156）提升到极限层。

**部分闭合边界（如实）**：已闭合的是可逆性侧主腿——`exp(−a)` 与 `exp(a)` 的乘积等于单位（`bxoo_exp_opp_one`）；完整可逆性形态（`exp_invertible`：以 sigT 见证给出逆元素的存在性包裹及一般元素的逆理论）在库内尚未建成（逐名 grep 零命中），列为后续工作（§9.2）。完整构造性谱定理仍为开放问题（§9.2 方向 B）；而 C* 代数的定义面与正元面已在本节下文登记——该件的机器检查范围见紧接本段的分层清单。

**C\* 代数扩展的分层登记（模块层，`UpReqCStarDef`，758 行）**：在 `BanachAlg` 之上，库内已装配 Set/sigT 编码的 C\* 代数定义面并给出正元平方根的构造性显式率；该件头注自陈为「谱定理阶梯第 1 级开工件」。逐层如下（零承认件、零经典公理，语句面全 Set/sigT）：

- **S1 定义面**：`Class CStarAlg` = `BanachAlg` 包装 ＋ 对合 `cst_star`（反线性：`cst_star_add` / `cst_star_mult`（反转序）/ `cst_star_star` 对合 ＋ `cst_star_one` ＋ `cst_star_coef`）＋ **C\* 恒等式字段** `cst_norm_sq`：`‖star a · a‖ == ‖a‖·‖a‖`（以 `QeqT` 陈述，零 Prop 落语句面）。派生件：`cst_star_zero`（star 零）、`cst_star_opp`（star 负）、`cst_norm_star`（`‖star a‖ == ‖a‖` 等距，经 Q 双侧消去）。
- **S2／S3 显式率**：Q 层 Newton 引擎对 `x₀ := a+1`、`x_{n+1} := (x_n + a/x_n)/2` 给出**精确二次收敛系数恒等式** `d_{n+1} = d_n²/(4·x_n²)`、几何率 `d_m ≤ d₀·(1/4)^m`（`cst_d_geo12`）与显式模量（`cst_newton_rate`：对任意 `0<a`、`0<eps` 构造性地产出显式 `N`，使 `m ≥ N ⟹ |x_m² − a| < eps`）；范数迁移 `cst_newton_alg` 把同一显式 `N` **逐字继承**到任意 `BanachAlg` 的标量嵌入面（经 `bcoef`，即 S3 为 `bcoef` 嵌入的标量子代数面）。
- **S4 正元锥**：`cst_pos (C : CStarAlg) (a) : Set` 取 C\* 锥标准形——`sigT (fun b => star b · b == a)`，即**正性走见证形、不走序判定**（规避受限 LPO）；配套三件 `cst_pos_selfadj`（正元恒自伴）、`cst_star_preserves_pos`（star 保锥）与 `cst_star_residual`（Newton 残差在对合下的交换面，即 star 与平方根的交换引理级形）。

**该方向收窄后的开放面**：仍开放的是**完整构造性谱定理**（谱测度／谱分解）与正性在序意义下的完整刻画（正元锥定义的逆命题）；「C\* 代数方向整体开放」的表述不成立——定义面、正元平方根的构造性显式率与正元锥均已机器检查，其阶梯第 2 级及以上未见开工件。

### 7.4 实例非空性与验证面

**实例非空性装配**。类公理面的非空性由具体实例承载：进库类 `bxin_BanachAlgPre`（`UpReqBanachInst.v`，349 行/6 处行首 `Qed.`/1 处 `Defined.`）以 39 字段弱化形态收拢类义务并给出装配器 `bxin_BanachAlg_of_pre`；柯西实数载体实例 `bxra_real_pre`（`UpReqBanachInstReal.v`，774 行/33 处行首 `Qed.`）为全库首个库类具体实例——39 个字段装配位逐一消解，实例非空性由 0% 到 100%，已随 b657aff 注册波并入认证面（§1.3）。配套面：标量模型 `UpReqBanachInstB.v`（599 行/25 处行首 `Qed.`）、Real 载体预装配 `UpReqBanachInstPre.v`（737 行/31 处行首 `Qed.`：`bxip_real_pre`）、乘法面 `UpReqBanachInstEMult.v`（288 行/12 处行首 `Qed.`：分配律与交换面 `bxem_mult_comm` L217）。

**支撑件面**：分离定理 `UpReqBanachSepThm.v`（193 行/6 处行首 `Qed.`：实数载体分离性 `spt_bxce_sep_real` L130）；极限唯一性 `UpReqBanachLimUniq.v`（227 行/10 处行首 `Qed.`，§7.2 总装消费）；范数对偶与倒数和逃逸 `UpReqBanachNormOpp.v`（459 行/19 处行首 `Qed.`）；非交换代数逆理论预备 `UpReqBanachInvPre.v`（545 行/20 处行首 `Qed.`）；无假设件 `BanachNoHyp.v`/`BanachNoHypNorm.v`（581 行/7 处与 123 行/2 处行首 `Qed.`：把携带显式形参假设的陈述重述为零假设形态，`bnh_esp_binom` 与 §7.2 二项式件同位供给——与 §1.1 两层解除口径（ii）同向的零假设收窄）。类签名层两行手术（范数字段余域 Id→QeqT，公理面零新增）已注册，此处一句备查。

**验证状态（四项验证 + 云认证，按 §1.3 口径）**：本章所列各件逐件经全量编译（退出码 0）、提取检查、内核检查（coqchk）与 `Print Assumptions` 假设审计（`Closed under the global context`）；实例装配波随 b657aff 注册波并入认证面，云认证 run 94486425397 @24431dc 全树 `COQCHK_ALL_PASS`（与 §1.3「当前库真态声明」同一口径，不另设验证通道）；行首 `Admitted`/`admit` 零出现（2026-09-15 grep 实测）。

---

## 8 形式化边界与假设声明

1. **Real 层 `exp_neg_pos` 已闭合，接口字段经 setoid 实例回填**：语言模型实例中已证明 `exp_neg_positive`；Real 层 `cauchy_real_exp_pos` 及其前置主恒等式 `esq_eq_corr` 均已闭合——exp 正性链完整。本文定理所涉接口的 setoid 对应物 `RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid`（Class，索引见附录 B）在 log 族上携带正性前提（`log_inv` 的定义域限于正参数），与构造性对数的定义域一致，故可由具体 `Real` 满足；其数学内容经三个 Setoid 系接口实例与 Real 层逐 eps 复刻实现（审计见本节目末）。

2. **`log_differentiable`（Set 层）仍为接口 Variable，Real 层已构造性闭合**：Set 层抽象接口的 `log_differentiable` 仍为 `Variable`——结构性边界：接口的 `df_correct` 全称量化于所有点，而接口 log 性质仅在正点上陈述，抽象层不可证。Real 层对应物 `real_log_differentiable` 已用 `RealDifferentiable` 记录（Bishop 逐 eps：`df := 1/x`、`δ := min(x/2, eps·x²/4)`、误差 ≤ eps·|h| + eps'）在构造性实数上完整证明（零 admit、零 Axiom）；在此基础上完成 Real 层 entropy 泛型组装 `real_entropy_differentiable`（`entropy_ent E_A := k_B·log(Ω_A E_A · Ω_B (E_total − E_A))`，经 const/minus/id/mult/compose 组装，前提仅为 `Omega_B_wd`、`E_B_pos` 等 Section Variable）。
3. **有限有理数截断**：`exp_partial` 定义在 `Q` 上；`cauchy_real_exp` 通过对角序列提升到 `Real`。
4. **无经典逻辑**：未使用 `Classical_Prop.classic` 或排中律；所有存在性结论均为可计算构造。
5. **库级边界**：全库审计的口径与数字集中见 §8.3「验证方法与可复现性」（219 基线 + 220 分发形态）；三个 Setoid 系接口实例（`Real_RealInterfaceSetoidCore`、`Real_RealInterfaceSetoid`、`RealEnhancedReal`）全部字段实值化，索引见附录 B。

### 8.1 正性链与接口假设的独立性

**正性链的引理不依赖 `exp_neg_pos`（可结构性判定）。** `esq_eq_corr` 及下游正性链的证明工作集中于 `Section QExpEOSplit`，全部工作在 **`Q`（有理数）层**：

| 引理 | 层级 | 是否依赖 `RealInterfaceEnhanced` |
|---|---|---|
| `q_pow_add`、`q_pow_one`、`q_pow_neg1_even/odd` | `Q` | 否 |
| `exp_partial_cauchy`、`exp_partial_lipschitz`、`exp_partial_cauchy_bounded` | `Q` | 否 |
| `exp_partial_zero`、`exp_pair_term_nonneg` | `Q` | 否 |
| `corr_nonneg`、`altf_zero`、`altf_as_sum_upto` | `Q` | 否 |
| `e_sq_expand`、`o_sq_expand`、`e_mul_term`、`o_mul_term` | `Q` | 否 |
| `vander_4m2`、`vander_4m4` 及镜像/拆分/移项族 | `Q` | 否 |
| `cauchy_real_exp_zero` | `Real`（具体层） | 否（工作于具体 `Real`，不经抽象接口） |

（各条行号索引见附录 A。）因此该正性链是一条独立于抽象接口假设的构造性链条：它以 `Qed.` 闭合后，即是不含 `exp_neg_pos` 前提的真结果。

### 8.2 接口字段的实例化

需要澄清接口字段的假设地位：`exp_neg_pos` 等超越函数字段（声明于 Id 系基类 `RealInterface`，L182；`RealInterfaceEnhanced` 经 `RI_base :>` 继承可见，L217–218）并非顶层公理。`RealInterfaceEnhanced` 是 **Class**，库内以 `Context {RI : RealInterfaceEnhanced}.` 引入（而非顶层自由 `Variable`）；`End Section` 后 Coq 自动对 `RI` 泛化，接口字段成为定理类型的显式（隐式）前件，不构成全局假设。实证：Rocq 9.1（219 artifact 历史验证环境；当前库 CI/coqchk 现亦运行于 Rocq 9.1，见 §1.3「当前库真态声明」）下 `Print Assumptions` 对下游核心定理（`boltzmann_factor_pos`、`minp_markov_kernel_normalized`、`rlhf_optimal` 等）均返回 `Closed under the global context`；批量 artifact 覆盖论文点名的 81 条主定理，全部无全局假设（CLEAN）（验证快照与未整体重跑的如实披露见 §8.3）。

**实例化方式**：抽象层定理（FEP / RLHF / Attention / Min-P）以 `forall {RI : RealInterfaceEnhanced}` 陈述，具体柯西实数 `Real` 的实例化由该接口的 setoid 对应物承担（`Real_RealInterfaceSetoid` 与增强版实例 `RealEnhancedReal`，见附录 B）。由此：

- 抽象层定理对 `RI` 全称量化，其签名与 setoid 实例层的对接为后续工程；
- **Setoid 版接口实例已完成装配**：三个实例的超越函数字段全部填为实值——完整版 `Real_RealInterfaceSetoid` 取 `exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log`（L39449–39453）；增强版实例 `RealEnhancedReal` 取 Real 层派生引理 `exp_neg := real_exp_neg`、`exp_neg_pos := real_exp_neg_pos`（其证明体即 apply `cauchy_real_exp_pos`，L40323–40327）、`exp_neg_plus := real_exp_neg_plus`、`log_inv := real_log_inv`（L41195–41205，数学内容同源）；核心定理亦经 **Real 层逐 eps 复刻**直接证明（KL 不等式 `real_gibbs_inequality_eps`、log/entropy 可微性等，审计见 §8）。

因此 §6 的链条实现方式为：

```
esq_eq_corr → exp_even_neg_nonneg → exp_partial_tail_pos → cauchy_real_exp_pos
⟶ Setoid 版接口实例（Real_RealInterfaceSetoid / RealEnhancedReal）装配
⟶ Real 层逐 eps 复刻核心定理
→ exp 正性在具体构造性实数上成立
```

**下游定理的接口假设与 Setoid 实例回填（以 `boltzmann_factor_pos` 为例）**：`boltzmann_factor_pos`（根 L1628 → Qed L1634）的证明体仅三步——`unfold boltzmann_factor; intros L s; apply exp_neg_pos`——它消费的接口假设只有正性字段 `exp_neg_pos`（经 `boltzmann_factor` 定义展开触及指数函数字段 `exp_neg`）。该假设在两系接口下的地位对比如下：

| `boltzmann_factor_pos` 消费的接口假设 | 实例化前：抽象 Id 系（`RealInterfaceEnhanced`） | 实例化后：Setoid 系实例（`Real_RealInterfaceSetoid` L39407 / `RealEnhancedReal` L41115） |
|---|---|---|
| `exp_neg_pos`（正性字段，证明直接 `apply`） | Class 字段假设：`End Section` 后成为定理类型的显式前件（故 `Print Assumptions` 仍 CLEAN，见本节目首段）；但在具体柯西 Real 上尚无 Id 系实例做字段级机器证明回填——若在 Id 层消费，正性内容由接口假设承载 | 已回填实值：完整版实例 `Real_RealInterfaceSetoid` 中 `exp_neg_pos := cauchy_real_exp_pos`（L39450）；增强版实例 `RealEnhancedReal` 中 `exp_neg_pos := real_exp_neg_pos`（L41196——Real 层派生引理，证明体即 unfold 后 apply `cauchy_real_exp_pos`，L40323–40327）——两值数学内容同源，该正性假设在具体 Real 轨上由机器证明承载 |
| `exp_neg`（指数函数字段，经 `boltzmann_factor` 定义展开） | 同上（Id 系抽象字段） | 已回填：完整版实例 `exp_neg := cauchy_real_exp`（L39449）；增强版实例 `exp_neg := real_exp_neg`（L41195，`real_exp_neg x := cauchy_real_exp (real_opp x)`，L40320）——语义同源 |
| `lt` 及序/正元字段（结论 `lt zero …` 的形态） | 同上 | Real 层已证引理实值（逐条清单与见附录 B） |

小结（如实）：该定理自身的 Id 系语句在签名迁移完成前保持原样（§1.1 状态一览表末行）；上表「解除」发生在具体 Real 轨——下游正性结论经 Setoid 系实例（或相应 setoid 对应定理）消费时，`exp_neg_pos` 的值来自已 Qed 的 `cauchy_real_exp_pos`，不再依赖未证假设（§8 第 1 条、§9.1.1 口径）。`softmax_pos`（L2856）、`minp_markov_kernel_normalized`（L31050）等下游定理的假设集同构于此。

**Id 系与 Setoid 系的语义关系**：`RealInterfaceEnhanced`（Id 系）与 `RealInterfaceEnhancedSetoid`（Setoid 系）承载同一组字段与代数律，实质差别在相等谓词：Id 系以命题相等表述，Setoid 系以 `req := real_eq` 表述。语义上，`real_eq` 是柯西实数上的构造性相等——逐 eps 的「渐近相等」：两个柯西表示只要逐 eps 逼近同一极限即视为相等，不必是同一表示；命题相等 Id 是更细的关系——命题相等的两项必 `real_eq`（后者为等价关系、含自反性），反向在表示层一般不成立。因此对具体 `Real` 而言，正确的相等语义是 `req`，代数律、Proper 兼容性（§6.4）与完备性（§6.5）都须在 `req` 上重述——这正是 Setoid 并行层的数学内容，也是字段实值化落在 Setoid 系实例的原因。抽象 Id 系定理的签名迁移（Id→req）是「把相等谓词由 Id 替换为 req 并核对 Proper 兼容性（附录 B 的 `real_eq_*_compat` 族即其前提）」的机械工程步骤，不引入新的数学内容——故 §1.1 状态一览表将其列为「后续工程」而非开放数学目标。

### 8.3 验证方法与可复现性

**审计方法与可复现性**：本文的全部「闭合/审计」数字采用 audited 口径。本文行号与引用锚的基准是 **219 基线主文件**：114,222 行，SHA-1 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`，全量编译产物 .vo 在案（SHA-1 `B8838C418A2CD2719FC295FEA1A1B8224E020C21`；220 模块化树复用该基座的已验证编译产物，不再重编）。闭合标记计数（2026-09-08 grep 实测）：**2,930 处 `Qed.`（行首 2,917 处、缩进 13 处）/ 51 处 `Defined.`**，行首 `Admitted`/`admit`/`Axiom`/`Abort\.` 均 **0**，无经典逻辑公理引用（`Classical` 仅出现于纪律注释）。**计数口径**：`Qed.` 与 `Defined.` 为两类闭合标记的分别计数，不可相加为「声明/定理总数」，也不与接口实例数、Section 数、Variable 数等其他口径的数字混用；本文不主张任何「声明总数」汇总。在该基线上，本文引用的全部行号锚——基底区（< L95604，含 §3–§6、§8 与全部引用件）与 T-π3 双路线定理/终末定理 C 所在的基座追加段（L104506–L112067）——经逐名 grep 复核零平移；§7 Banach 推广各件的行号为开发树 Live_X 各件坐标（§7 章首口径），不在 219 基线行号体系内。

**三项独立验证**：(1) **audit_full.ps1 正则统计与禁词扫描**（库内审计脚本，随论文 artifact 打包提交）——按行首正则统计闭合标记并扫描禁词；行首口径对「`Qed.` 出现在注释或字符串中」天然免疫，但它是行首级统计，不声称覆盖非行首形态，非行首残留由 (2)(3) 与批量 `Print Assumptions` 审计兜底；(2) **coqc 编译**：219 基线主文件（artifact 历史重编环境）经 Rocq 9.1（Rocq-Platform~9.1~2026.01，`coqc -version` 报 The Rocq Prover, version 9.1.0）单发全量编译、退出码 0；当前库 CI 与 coqchk 运行于 Rocq 9.1（见 §1.3「当前库真态声明」）——任何未闭合证明、`Admitted` 或语法残留都会使编译失败；(3) **提取验证**：核心构造（`real_mult`、`cauchy_real_exp` 等）提取为 OCaml，由独立验证文件断言零类型级 `__`（无 Prop/证明残留）。

**批量 `Print Assumptions` 审计（两个口径，承载对象不同，不可混读）**：

- **口径一（选定核心定理清单批量：81/81）**：库内 81 条核心主定理/主定义（覆盖论文 1–4 的主要结果面，独立验证文件逐名执行 `Print Assumptions`，清单与判定规则随 artifact 提交）全部返回 `Closed under the global context`——**81 条全部无全局假设（CLEAN）、零全局依赖（DEP 0）**（批量审计报告与断言脚本随论文 artifact 打包提交，包内路径与复现命令见 artifact README）。该清单最近一次全量执行的实测验证快照为 198（2026-09-03，主文件 64,248 行）。
- **口径二（验证快照编号标记：198/206）**：历史注记中的「198/206」是**验证快照编号（198 与 206 两个时点）的双时点标记**，不是「206 条中 198 条通过」的分数式——81 条选定核心定理清单在该两时点作为核验依据登记，自快照 207 起未再随基线整体重跑（版本注记「按验证快照 206 注明（207 起未整体重跑）」即此义）。
- **此后新增面的验证维持与现态**：自迭代 210 起，81 条选定核心定理的批量假设检查未随每一版本整体重跑；新增内容经「行首禁词零命中 + 全量编译退出码 0 + `coqchk` 内核校验」维持验证状态，特此如实披露。当前状态以 §1「验证快照与版本基准」段与 §1.3 为准。**当前验证边界**：81 条选定核心定理的最近一次全量批量假设检查在迭代 198/206；其后新增面以编译、提取与内核检查维持，未整体重跑。公理面批量假设检查其后另以四波批量 `Print Assumptions` 累计覆盖 546 枚收尾件（48＋279＋199＋20），均 `Closed under the global context`、0 `Axioms:`（明细随补充材料 S2）。

**可复现性**（220 分发形态、两套源码树演进与历史构建记录见补充材料 S2，正文不再保留）：(a) **模块化树（权威分发形态）**：基座 `CW_ConstructiveWorld_219.v` 为本文定理基准；当前库真态（HEAD=39d81aa，R82 成果四接入与注册收尾波）编译清单 246 模块、Live_X 356 个 .v，认证面经 143/144→151→156→161→166→167→168→173→187→196→201→221→224→228→246 逐波扩展（246 件 .vo 面 246/246 OK91 满面全绿，本地全树 coqchk 246/246 通过；云认证轮次与认证现状见 §1.3）；219/220 artifact 的历史认证记录见补充材料 S2，当前认证面以 246 模块为准（见 §1.3「当前库真态声明」）。(b) **扩展层拼装发布件** `CW220_Extensions.v`：15,254 行，553 处 `Qed.`（行首 512 处、缩进/行内 41 处）、11 处 `Defined.`，分发件校验值与验证明细见补充材料 S2；该拼装形态已退役瘦身（现维护形态为 S/G 双系拆分树），此处数字为历史分发口径。(c) **单文件全量** `CW_ConstructiveWorld_220.v`：129,396 行，3,443 处 `Qed.`（行首 3,429 处、缩进 14 处）、62 处 `Defined.`——目前为**源码合并形态**，全量编译存在待解决事项（顶层同名声明碰撞等四项，见库内问题跟踪文档；其中大文件编译冻结的机制画像为 coqc 异步证明工作线程在大文件累积阈值处的死锁，解决方式为 `-async-proofs off` 内联证明旗标）；该形态在本文语境一律不表述为「编译通过」。本文正文行号均以 219 基线为准，与模块层无涉；历史构建批次的审计明细与过程记录移入 artifact CHANGELOG，正文不再保留。本工作随论文提交完整 artifact（主文件与模块源码、编译与审计脚本、批量 `Print Assumptions` 断言清单与锚表，附 LICENSE 声明与 DOI 存证），包内相对路径与一键复现命令见 artifact README。

### 8.4 可提取性

全库定义均置于 Set 层——sigT/`And` 内的有理数序谓词一律使用 Set 值判定谓词 `QltT`/`QleT`，`And` 不实例化到 Prop（无 Prop 层泄漏）；`real_mult`/`cauchy_real_exp` 等核心构造可提取为不含 Prop 残留的 OCaml 代码（提取验证在独立验证文件中完成）。本库使用自定义 Set 层合取 `And (A B : Set) : Set := A * B`，而非 Coq 标准的 Prop 层 `and`。

---

## 9 结论与未来工作

### 9.1 结论

**贡献总结（C1–C4）**。C1 主结果：`cauchy_real_exp_pos` 在 Real 层闭合，主恒等式 `esq_eq_corr` 为其 Q 层代数核（§5–§6.2），并经三个 Setoid 系接口实例回填为 `exp_neg_pos`/`exp_neg_plus` 实值（§8.2，清单见附录 B）。C2 方法与工程资产：两层假设解除口径（§1.1 定义框经摘要、§1.2 与 §8.2 统一引用，CLEAN 判定语义由 §8.2 钉死）；有限截断代数路线与指数加法路线形成交叉验证（「±对称乘积 == 1」的极限/有限两形态互证，§6.7 末段，代数底层 §6.6）。C3 扩展结果：本节下文 T-π3 条目给出桥函数直觉、双路线机器链、共享主引理调用关系与两条核心论证的思路；几何 π/2 零点定理、两 π 数值界、和角恒等与可微族见本节相应条目。C4 推广结果：指数律与级数柯西性向 Bishop 式 Banach 代数的推广主体闭合（§7）——级数柯西主定理、加法交换律 `bxae_exp_add`（交换面前提）、e⁰ == 1 与可逆性侧 `bxoo_exp_opp_one`，实例非空性以柯西实数载体装配完成；完整可逆性形态与完整构造性谱定理留作开放问题（§7.3–§7.4；C* 代数的定义面、正元平方根构造性显式率与正元锥已闭合，见 §7.3）。以下按 C1 支撑结果主线陈述正性链条及其扩展。

本文给出了 ConstructiveWorld 库中构造性柯西实数指数函数正性证明的完整结果：从有理数级数到偶/奇双和展开的关键引理全部闭合，语言模型实例中证明 `exp_neg_positive`，其求和形态 `sum_exp_positive` 提升为通用 KeyProofs 引理。主恒等式 `esq_eq_corr` 的证明是本文主链的关键步骤（作者解读：其系数层恒等由两个交错二项式恒等（`vander_4m2`/`vander_4m4`，见 §5.4 命名注记）及 16 条配套代数引理支撑，归纳由 `corr_diff_eq_sq_diff` 驱动，依次完成 `exp_even_neg_nonneg`、`exp_even_neg_pos`、`exp_partial_tail_pos` 与 Real 层 `cauchy_real_exp_pos`，得到 `forall x : Real, cauchy_real_exp x > 0`。`exp_neg_pos` 字段已在完整版实例 `Real_RealInterfaceSetoid` 中填为实值（`exp_neg_pos := cauchy_real_exp_pos`，见 §8.2）。

**扩展：构造性超越函数微积分**：在上述正性链条之上，本库进一步闭合了两个非平凡定理族：

- **exp-log 有序群同构组装**（`Section ExpLogGroupIso`）：值域刻画 `exp_surj_pos`（0 < y ⟹ ∃x, e^x == y，sigT 见证 `cw_log y Hy`）/ `exp_image_pos`；序逆保持 `exp_reflects_lt`（e^x < e^y ⟹ x < y）；像侧完备性 `cw_log_reflects_lt`（log a < log b ⟹ a < b）；结构定理 `exp_order_embedding`（exp 双向保序，And 层）。同态（`cauchy_real_exp_plus`）/ 单射（左逆）/ 满射（右逆 `cw_log_exp_right`）/ 值域（正性）四个组成部分齐备，构成「保序群同构」的机器检查叙述。
- **exp 不等式族**（`Section ExpInequalities`）：非 eps 严格版 `real_exp_ge_linear`（0 < t ⟹ 1+t < e^t）；`real_exp_le_inv_one_minus`（0 < x < 1 ⟹ e^x ≤ 1/(1−x)）；eps 余量 Lipschitz 型 `real_exp_abs_minus_one_eps`（|e^x−1| ≤ |x|·e^{|x|} + eps；非 eps 版需三分律判定，故保留 eps 余量——构造性边界）。

两族合计 21 个 Qed（ExpLogGroupIso 5 + ExpInequalities 16），全部 `Closed under the global context`（零公理、零经典、Set 层、可提取）。详细清单见附录 A。

**扩展：三角函数与几何 π 定理族**：在超越函数微积分工作之上，本库新增构造性正弦/余弦与几何 π 定理族（sin/cos 级数、π 定理与和角恒等区位于根 L55100–L66105，逐 eps 可微件位于 L68354–L69642——均在基底区，文件尾部（L95604 之后）为追加区段；级数至和角区约 1.1 万行）：

- **sin/cos 的 Q 层与 Real 层构造**：`sin_term`/`cos_term` 级数项与 `sin_partial`/`cos_partial` 部分和（柯西性/Lipschitz/零点/奇性全套）、`real_sin_proj`/`real_cos_proj` 的柯西序列提升，与基础恒等 `real_sin_zero`（sin 0 == 0）。
- **Leibniz π**：`cauchy_real_pi_leibniz`（π := 4·Σ(−1)^n/(2n+1)）与数值界 `real_pi_leibniz_between`（3 < π < 4）。
- **cos/sin 的分析性质**：`real_cos_three_halves_pos`（cos(3/2) > 0）、`real_sin_pos_lt_two`（0 < x < 2 ⟹ sin x > 0）、`real_cos_strict_decr`（(0, 2) 上余弦严格递减）。
- **几何 π/2 零点定理（重点定理）**：二分机械（`cos_scan_nested`、`approx_root_cos`、`cos_zero_seq` 及其柯西性、端点符号证书 `cos_zero_lower/upper`、`cos_root_pt_bound`、投影 `cos_pi_half_proj`、有界性 `cos_zero_abs_le_two`）⟹ **`real_cos_pi_half_zero`：cos(π/2) == 0**；配套**最小正零点唯一性** `cos_pi_half_unique`（(3/2, 5/3) 内唯一零点）与**几何 π 封装** `real_pi_geom`（π_geom := 2·(π/2 零点)）。
  **二分符号判定机制**：零点的构造不依赖三分律。`cos_scan` 对证书区间（0 < cos a、cos b < 0）逐轮在有理中点 m := (a+b)/2 做**带余量的可判定符号测试**：先按截断级数余项界取逼近步数 K（`cos_partial_cauchy` 的模量，d4 := eps/16），算有理近似 q := `cos_partial K m`（误差 < d4），再以 Set 层 `Qlt_bool` 判定 A：q + 2·d4 < 0 ⟹ cos m < −d4 < 0（取左半 (a, m)），或 B：2·d4 < q ⟹ cos m > d4 > 0（取右半 (m, b)）（`cos_testA_eps_true_lt`/`cos_testB_eps_true_gt`）；双假则 |q| ≤ 2·d4，中点已满足 |cos m − 0| ≤ 3·d4 < eps（`cos_test_mid_bound`：两端判定均不成立时中点已直接达到所需精度）。区间每步减半且端点符号证书保持（`cos_scan_spec`：宽度 (b−a)·2^{−n}），配合 cos 在 (0, 2) 严格递减（`real_cos_strict_decr`）与跨段 Lipschitz（`cos_span_lipschitz`），`approx_root_cos` 对任意 eps > 0 输出 x ∈ (3/2, 5/3) 满足 |cos x − 0| < eps（证书：`real_cos_three_halves_pos`、`real_cos_five_thirds_neg`）——符号信息全程由带余量的有理测试携带，无需事先计算 cos 的精确符号。
- **几何 π 数值界（T-π2）已闭合**：`real_pi_geom_gt_three`（3 < π_geom）与 `real_pi_geom_lt_ten_thirds`（π_geom < 10/3）合取 **`real_pi_geom_between`：3 < π_geom < 10/3**——与 Leibniz π 侧（`real_pi_leibniz_between_tenthirds`：3 < π_L < 10/3）构成两 π 各自的严格数值界（T-π3 本体的闭合走 §9.1 的 E(x) 归零论证双路线，不依赖区间论证）。同期闭合：**`real_sin_pi_half_one`：sin(π/2) == 1**（经 `real_sin_pi_half_pos`/`real_sq_eq_one_pos`/`real_lt_zero_cos_pi_half`/`real_lt_cos_pi_half_two`）；零点唯一性拓宽 **`cos_pi_half_unique_widened`**（(3/2, 2) 内任一零点 == cos_pi_half，辅 `cos_inv_dist_le2`）；**exp 显式导数等式 `real_exp_deriv_eq_self`**（x > 0 可微且导数即自身，Bishop 显式：误差 ≤ eps·|h| + eps'；配套 `real_exp_diff_with_deriv_self`：exp ∈ `RealDifferentiable` 且导函数显式取为 exp）；**T-π3 外围辅助引理**：`w_leibniz`（= π_L·(1/2)）、`real_pi_leibniz_half_lower`（3/2 < π_L·(1/2)）与 `real_pi_leibniz_half_upper`（π_L·(1/2) < 5/3）。
- **几何 π == Leibniz π（T-π3）已闭合为主定理**。两 π 各自独立闭合（几何侧经 π/2 零点，解析侧经 Leibniz 级数），其相等无先验理由；合流的中介是**桥函数** E(x) := sin(arctan x) − x·cos(arctan x)（`real_E`，根 L72948）——它度量「arctan x 处 sin/cos 的几何关系与 x 的偏差」，E(x) == 0 即 sin(arctan x) == x·cos(arctan x)。若 E 在端点 1 归零，则 sin(arctan 1) == cos(arctan 1)（`b5b_hsc_main` 的输入），几何角 π/4 的刻画由此钉在解析的 arctan(1) 上，闭包件 `a3_closure_f1` 借此把几何 π 合流到 Leibniz π。机器把「E 归零」实现为两层：先闭**有理点归零** `b5dQ_E_rational_zero`（∀q ∈ Q∩(0,1)：E(q) == 0——两条证明路线共享的唯一归零机器证明），再由两条轨闭合——单点轨把有理归零经端点逼近推到 E(1) == 0（`b5dF_E_one_zero_of_rational`），∀x 轨把有理归零经有理近似传输提升为 (0,1) 上逐点归零（`b5dS_E_zero_on_unit`）；两条核心论证 `b5dS`/`b5dF` 的证明思路见本段末，各定理逐字语句见附录 C。
  两条主定理 `b5dT_f1_pi_geom_eq_leibniz_single`（单点轨，L111966 → Qed L111973）与 `b5dT_f1_pi_geom_eq_leibniz_univ`（∀x 轨，L111981 → Qed L111986）的语句均为 `real_eq real_pi_geom cauchy_real_pi_leibniz`（π_geom == π_L）。**单点轨证明链**：`b5dQ_E_rational_zero`（L111289：∀q ∈ Q∩(0,1)，E(q) == 0，其中 E(x) := sin(arctan x) − x·cos(arctan x)）→ `b5dF_E_one_zero_of_rational`（L104506：E(1) == 0）→ `b5b_hsc_main`（L72994：E(1)==0 ⟹ sin(arctan 1) == cos(arctan 1)）→ `a3_closure_f1`（L67997：sin(arctan 1)==cos(arctan 1) ⟹ π_geom==π_L）——四步纯应用链闭合（该定理证明体 4 条战术 + Qed）。
  **∀x 轨证明链**：`b5dS_E_zero_on_unit`（L111782：∀x ∈ (0,1)，E(x) == 0）→ `b5b_f1_closure'`（L78187：E 在 (0,1) 归零 ⟹ π_geom==π_L）——两战术链闭合（该定理证明体 2 条战术 + Qed）。
  两条证明路线共享有理点归零主引理 `b5dQ_E_rational_zero`——单点轨以 b5dQ 语句为 `b5dF_E_one_zero_of_rational` 的前提（其证明体即 `exact b5dQ_E_rational_zero`）；∀x 轨主定理 `b5dS_E_zero_on_unit` 的证明体亦在有理近似传输后直接调用 b5dQ（基座根 L111835，`b5dS_E_zero_on_unit` 证明体内，代码注释自证「本段唯一 CW2 消费点」）——E 归零层只有一条机器证明，两条路径共享有理点归零引理；独立双证仅出现在最终包装定理层：单点轨经 `b5dQ`/`b5dF`/`b5b_hsc_main` 到闭包 `a3_closure_f1`，∀x 轨经 `b5b_f1_closure'`，两链闭合出同一 `b5dT_*` 语句；终末定理 C 亦有 `b5dU_routeA_from_f1`（routeA）与 `b5dU_cos_piL_half_zero_alt`（alt，经 `a3_closure_n5`）两条不同路径——即两条证明路线共享核心归零引理、在最终包装定理层以两个包装证明闭合同一结论。
  **终末定理 C**：`b5dU_cos_piL_half_zero`（L112062 → Qed L112067）：`cos(π_L/2) == 0`——Leibniz π 半角处的余弦零点，经 `b5dU_routeA_from_f1`（L112033：F1 ⟹ cos(π_L·(1/2))==0）实例化单点轨件闭合；另有零新证路径 `b5dU_cos_piL_half_zero_alt`（L112018）。`real_E_one`（L72953）为 E(1) 的承载定义。以上行号均为 219 根实测（2026-09-08 逐名 grep 复核零平移；双路线定理与终末定理 C 位于基座追加区段）。
  **两条核心论证的思路**（两条独立证明路线闭合的论证内容）：`b5dS_E_zero_on_unit`（150 行）把「任意 x ∈ (0,1) 的 E(x) == 0」化约为有理点归零——给定 eps，先由 E 的等度连续件（pair-close）取一个**与 x 无关**的 Q 层窗口 [Nc, d0]（预算 eps/2），再由 0 < x < 1 的分离证书与 x 的柯西性取坐标 Nτ，令 q := x_{Nq}（Nq := max(max N0s N1s) Nτ）为 x 的 Cauchy 坐标逼近，q 是有理数；随后把 |E(x)_n − 0_n| 拆为两项：|E(x)_n − E(q)_n|（在窗口 |x_n − q| ≤ d0 内由 E 的坐标级连续界控制）与 |E(q)_n − 0_n|（有理点归零件 `b5dQ_E_rational_zero` 直给），各 < eps/2，三角闭合——任意实数的归零由此落到一个有理点的归零上。
  `b5dF_E_one_zero_of_rational`（124 行）把同一有理归零前提推到端点 1：取有理点 xg := real_const (1−g)（g := Qmin (1/2) a，a := 1/(K+2) 由 arch 性质选得使 0 < g < g0，故 xg ∈ (0,1) 且距 1 足够近），E 的端点连续界 `b5b_E_close_q`（L77321）控住 |E(1) − E(xg)| < eps/2，前提实例化给 E(xg) == 0，再与 |E(xg) − 0| < eps/2 三角闭合。故两条证明路线的机器实质分别是「有理点归零 + 端点逼近」（单点轨）与「有理点归零 + 有理近似传输」（∀x 轨），共享前者——与上文「独立双证仅出现在最终包装定理层」的表述一致。这一「有理稠密 + 等度连续窗口 ⟹ 逐点归零」的论证模式是构造性分析中的通用稠密性传输原语：把该模式从 E 的具体归零证明中提炼为可复用的抽象传输引理、使双路线进一步共享同一条归零机器证明（单证多用途），已列入库级后续工程计划（§9.2）；在该抽象引理交付前，本文维持「双路线双证、归零层单证」的如实表述。
- **和角恒等（sin 与 cos 均已闭合）**：Q 层地基为 sin/cos 项级数的加法恒等——对角项恒等 `sc_add_sin_diag_term`（sin_term j (x+y) == Σ(cos·sin) + Σ(sin·cos)）与 `sc_add_cos_diag_term`（cos_term j (x+y) == Σ(cos·cos) − Σ(sin·sin)），部分和的度向分解 `sc_add_sin_prod_decomp`（精确 Qeq）与 Q 层模量链 `sc_add_sin_err_bound`；Real 层据此闭合 sin 加法定理 **`rs_add_sin`**（sin(x+y) == sin x·cos y + cos x·sin y，real_eq）与 cos 加法定理 **`rs_add_cos`**（cos(x+y) == cos x·cos y − sin x·sin y，real_eq），两则证明均沿用 `cauchy_real_exp_plus` 的 eps/3 装配模板（见附录 C）。
- **sin/cos 的 Real 层逐 eps 可微（全域）**：零点线性界 `real_sin_zero_linear_bound`（L68354：\|sin h − h\| ≤ eps·\|h\| + eps′，sin′(0) == 1）与 `real_cos_zero_linear_bound`（L68521：\|cos h − 1\| ≤ eps·\|h\| + eps′）；全域导数定理 **`real_sin_deriv_linear`**（L69023：∀x，\|sin(x+h) − (sin x + cos x·h)\| ≤ eps·\|h\| + eps′，即 sin′ == cos）与 **`real_cos_deriv_linear`**（L69331：∀x，\|cos(x+h) − (cos x − sin x·h)\| ≤ eps·\|h\| + eps′，即 cos′ == −sin）。**sin/cos 可微是全域结果（无 x>0 前提，比 exp 的 x>0 版更强）**，与 exp（Real 层可微，x>0 限定，见上）及 log（Real 层 `real_log_differentiable`，正域，见 §8 第 2 条）共同构成 exp/log/sin/cos 的 Real 层可微四函数微积分层；清单见附录 C。

**目标状态一览**：各目标的状态与阻塞项已在 §1.1 状态一览表集中汇总（相应展开见 §6–§8 与本节上文），此处不再重复列表。

**可提取性**：全库定义均置于 Set 层——sigT/`And` 中的有理数序谓词一律使用 Set 值判定谓词 `QltT`/`QleT`，`And` 不实例化到 Prop；`real_mult`、`cauchy_real_exp` 等核心构造可提取为不含 Prop 残留的 OCaml 代码（提取验证在独立验证文件中完成）。本库使用自定义 Set 层合取 `And (A B : Set) : Set := A * B`，而非 Coq 标准的 Prop 层 `and`。

**构造性特征（可计算性与可提取性）**：本文成果的意义不止于「零全局公理、零 Admitted」的否定性口径，更在构造性证明的正向内容。其一，**可计算性**：全部存在性结论均为可计算构造（§8 第 4 条）——π/2 零点由带余量的可判定符号测试逐轮二分构造（`cos_scan`，§9.1），任意实数处的 E 归零经有理近似逐 eps 传输化约为有理点归零（§9.1），Q 层截断正性链可 `vm_compute` 数值复核（§5.3）。其二，**逐 eps 见证可计算**：度量族的逐 eps 余量形式（§6.5）、Bishop 逐 eps 可微的显式 δ 构造（§8 第 2 条、§9.1）与截断误差的 eps 见证（`exp_trunc_bound`/`exp_trunc_arch_seq`，§6.6）均以可构造的见证给出，结论的使用者可按同一 eps 复算。其三，**可提取性（附提取实证）**：全库定义置于 Set 层、序谓词取 Set 值判定谓词 `QltT`/`QleT`，`real_mult`/`cauchy_real_exp` 等核心构造提取为不含 Prop 残留的 OCaml 代码，由独立验证文件断言零类型级残留（§8.4 与三项独立验证之 (3)）——被机器检查的证明对象同时是可执行的计算。其四，**Setoid 替换原理机器检查**：`real_eq` 对全部算术运算与度量的 Proper 兼容性（含证明复杂度较高的 `real_eq_mult_compat`，§6.4）逐条机器检查，替换原理在具体 `Real` 上成立由三个接口实例的字段装配承载（§6.3、§8.2）。这些性质使本文的定理链在机器检查之外，同时构成可复用、可执行、可提取的构造性分析基础设施。

**与库内上层形式化的边界**：本文聚焦于构造性指数正性链条在 `Q` 层与 `Real` 层的完整闭合，为库内上层形式化（对齐理论、自由能原理、采样控制）提供下层基础。需明确两点边界：（一）`cauchy_real_exp_pos` 已在一般 `Real` 上证明，并经 Setoid 版接口实例回填到接口层（`exp_neg_pos := cauchy_real_exp_pos`，见 §8.2），下游假设集的缩减经该实例与 Real 层逐 eps 复刻完成；（二）`log_differentiable` 在 Set 层仍是 `Variable`，但其 Real 层对应物 `real_log_differentiable` 与 entropy 泛型组装 `real_entropy_differentiable`（前提为 `Omega_B_wd`/`E_B_pos` 等 Section Variable）已在构造性实数上成立（审计见 §8）。把这些接口假设转为构造性证明，列为库内接口族工程的后续工作（§9.2）。

### 9.2 未来工作

1. **抽象层 Id 系签名迁移**：`exp_neg_plus` 与 `exp_neg_pos` 的 Setoid 字段级实例化已完成；未完成的是抽象层 `forall {RI : ...}` 语句的 Id→req 迁移（见 §8.2）。
2. **接口假设收束**：持续排查抽象层残留 `Variable`（`log_inv` 族已在 Setoid 版实例填为实值），逐步将以 `Variable` 表述的结论转为构造性证明。
3. **`log_differentiable` 接口字段实例化**：Real 层 `real_log_differentiable` 与 `real_entropy_differentiable` 已闭合；Set 层接口字段因结构性边界保留 `Variable`。
4. **中层策略自动化（证明工程方向）**：库内自定义 `Ltac` 目前仅 4 条（`id_simpl_step`/`id_simpl`/`id_ring` 与 `b4_qring`，见补充材料 S1），近期新增的模块区块（§8）均未引入新 Ltac；Bishop 逐 eps 可微证明（`real_sin_deriv_linear` 305 行、`real_cos_deriv_linear` 311 行、`b3rr_real_arctan_deriv_linear` 321 行等）与 eps/3 装配（`cauchy_real_exp_plus`、`rs_add_sin`/`rs_add_cos`）中的重复模式目前以注释约定与模板复制管理。该方向已有一个经机器检查的实例：严格步生成器族 `UpReqStrictStepGen`——库内五件 S 系模块中「eps 拆分（half·ε＋quarter·ε<ε）」惯用法的内联重证经 grep 计数达 734 处（S10=375/S07=317/S08=25/S09=16/S04=1），该件把此惯用法接口级收敛为参数化母定理（`ssg_half_quarter_eps_lt`/`ssg_quarter_eps_lt` 等 2 Def＋13 Lemma，全 Closed），后续工作可直接按名消费、免再内联；文献对标注记（诚实分级）：eps 拆分的命名原子件先例在主流库已在案——mathlib 的 `half_pos`（0 < a/2，2018 年入库名件）、`add_halves`（a/2＋a/2＝a）与 `zero_lt_two`（0 < 2）即为原子命名件，mathlib3 实数完备性（柯西收敛）证明即以 `half_pos` 配 `add_halves` 内联消费 eps 拆分论证，故本文不主张「首创 eps 拆分命名引理」——上述 734 处内联计数应读作收敛审计的杠杆数据，新颖性仅落在「内联惯用法 → 参数化母定理族」的库内收敛工程与母定理对终局消费形的逐字对齐（部分新，形式化工程件；逐条出处见同目录《论文3-文献对标资料-20260916.md》）；每件母定理对应数十消费点的杠杆比，是「把证明工程方法成为可陈述贡献」的已实现样本（消费侧兑现：Sqrtf 三件全绿的放电链即其同族）。同族 `ReqStrictOrderBridge` 三槽全放电判词（§1.1 定义（ii））的验收方法学为**零真抽象位检查审计**——节闭 `Check` 语句普查（节闭后非常量即诚实槽位）、逐槽放电、复验留痕，属工程工件的系统化验收，非新数学主张。将「eps 余量分割 + QltT/Qlt 桥」模式系统化为可复用策略族（如 `eps_three_split`/`real_eq_by_eps` 形态）是降低长期维护成本、并使证明工程方法成为可陈述贡献的候选方向——列为后续工作，不改变本文定理的闭合状态。
5. **稠密性传输引理的抽象化（已立项方向，待实施）**：§9.1 的 ∀x 轨主定理 `b5dS_E_zero_on_unit` 与单点轨共享「有理点归零 + 等度连续窗口传输 + 有理逼近闭合」的论证模式（三组件正交：前提 A 有理点归零、前提 B 逐 eps 等度连续窗口、前提 C 分离证书 + 柯西坐标逼近）。将该模式提炼为 Real 层抽象引理（有理稠密 + 等度连续 ⟹ 逐点归零），并回接 T-π3 双路线作回归验证（原双路线定理保持陈述不变、编译通过，新引理并行共存），可把现有「独立双证仅出现在最终包装定理层」的形态升级为「共享稠密传输引理的单证多用途架构」；同一原语可复用于 sin/cos 恒等式传输、log 恒等传输与连续界传输等场景。在该引理交付前，本文维持「双路线双证」表述（§9.1）。
6. **三条延伸方向的现状（本文基线之后已在独立模块层部分实现，见 §6.7 末「后续认证披露」）**：方向 A（正性的算法见证显式化）——已认证（`UpReqExpPosWitness` 的 ε=1/(2C) 字面见证与 `UpReqExpPosQBound` 的 1/(1+B) 显式下界）；方向 B（Banach 代数推广）——主体已闭合，正文升格为 §7：级数柯西主定理（`exp_series_cauchy`）、加法交换律 `bxae_exp_add`（交换面前提，`UpReqBanachExpAddEq` 云认证）、e⁰ == 1（`bxb_expdef_exp_zero_close` 族）、可逆性侧 `bxoo_exp_opp_one`（exp(a)·exp(−a) == exp(0)，ε-近邻链 `bxcd_prod_near_one` 供给）与实例非空性装配（Real 载体实例 `bxra_real_pre`，39/39 字段装配位逐一消解，实例非空性 0%→100%，已随 b657aff 注册波并入认证面）均已闭合，陈述与行号见 §7；余量如实两项——完整可逆性形态（逆元素存在性包裹）与完整构造性谱定理仍为开放问题（§7.3–§7.4；C* 代数一线已就定义面、正元平方根构造性显式率与正元锥闭合，见 §7.3 分层登记），不再改变本文 C1–C4 贡献边界；方向 C（Padé 带符号逼近）——符号面首砖已认证（`UpReqPadeExp`/`UpReqPadeSign`/`UpReqAltSumPos`：系数正性、分母正性 n=0/1、交错和正性引擎）；余项正尾性的免积分构造性直证五件已注册并经全树内核认证（`UpReqPadeBetaPos`/`UpReqPadeTailPos`/`UpReqPadeLower`/`UpReqPadeDenPos12`/`UpReqPadeFinale`：尾系数逐项为正 `ptp_beta_pos`、偶阶下界 `cpl_lower_even`、[2/2] 链正性 `cpf_exp_pos_pade2`；正尾性的数学实质属经典 Hermite–Padé 余项理论，本库贡献限于免积分的构造性直证与相应工件）；其后两波再获三面推进并已注册：其一，分母正性由 n=0/1 特例升为通用 n 定理——0≤x≤1 域全 n 版（`PadeDenPosA`）与 x≤2 域全 n 版（`PadeDenPosB12`，`pdpb_den_pos_le2`）；其二，Real 层 n=2 定量旗舰——`cpf_exp_pos_final_n2`（`UpReqPadeFinale`）对 0<x 的有理点闭合 `real_lt real_zero (cauchy_real_exp (real_const x))`，`Print Assumptions` 零假设；其三，余项 (−1)ⁿ 符号面定理化——`UpReqPadeSignXfer` 的 `psx_sign_instantiated`（余项系数 = (−1)ⁿ×正因子的符号实例化，`psx_beta_bridge` 与 β 闭式桥接；引擎件 `UpReqPadeQLeg`）。余项 (−1)ⁿ 完整误差界与经典积分表示的逐字对照仍待建。
7. **路线图余项的分级披露（排队/未立项/开放三档，如实）**：**排队档（已立项有领地/原型件在库）**——①宪法执行器、耗散币制与停时原语：原型件 `UpConstitution`/`UpDissip`/`UpStopTime` 已落库注册并经编译与内核检查（9.1 认证面），语义整合、与熵-温度族的接口对接及论文级陈述待排期（纠正旧档「未实现」的过期记载）；②圆桌问题 Q1–Q4：跨论文共同开放项，排队档，本文不逐条展开；③完整可逆性形态与稠密性传输引理抽象化（§7.3 与本节第 5 条既有项，维持）。**未立项档（有方向、无路线图承诺）**——完整构造性谱定理（§7.3–§7.4 既有开放项，维持；其阶梯第 1 级——C* 代数定义面与正元平方根构造性显式率——已开工并闭合，见 §7.3 分层登记）与 Лёвner 单调性族 L1–L4（未立项，属算子不等式扩展方向；其中 L4 为开放问题）。**开放档（问题存在、无路线图承诺）**——机器化不可能性证明（模型构造级）：受限选择原理等价族的首两层已定理化（`UpReqLpoEquiv` 三重奏＋`UpReqPinWallEquiv` 钉定墙等价器，后者已注册入库）——该方向的**数学侧**在构造性反数学中已有系统分类（LPO/LLPO 层级与实数序/邻离原理的对应见[25][26][28]），本文的增量在**机器化与具体编码层**（§1.1 文献定位）；把受限构造性数学中的不可证命题推进到模型构造级的机器化证明为开放方向；提取质量与 regular 编码的系统对比（§2 既有，维持）。分档判据：排队=已有命名模块或既定领地；未立项=有方向无路线图；开放=仅登记问题。本条为状态披露，不改变 C1–C4 贡献边界。

---

## 10 定量构造性常数包络与第二定律的 eps 定量化

**本节定位与诚实状态段（按 §1.3「当前库真态声明」口径，如实分列）**。本节为成果四批次（2026-09-16 外部同步）四件新成果的组合入文节：`LogTwoEnvelope.v`（ln2 包络）、`ExpOneEnvelope.v`（e 包络）、`PiEnvelope.v`（π 包络）、`SecondLawQuantified.v`（第二定律定量化），按零结构重写纪律置于 §9 之后、既有节零改动（本节陈述为四件在盘稿语义的忠实转述，以名引）。机器认证面口径（沿 §7.4「四项验证 + 云认证」框架）：**四件载体已入库并注册（R82 注册收尾，编译清单 246 模块），云认证 CI #72（head 39d81aa，run 35057242417，246 注册面）`COQCHK_ALL_PASS`**——本地 9.1 标准甄别（19 件外部稿逐件本地重编，2026-09-16）15/19 绿：`LogTwoEnvelope`（PA×4 Closed）、`ExpOneEnvelope`（PA×4 Closed）、`SecondLawQuantified`（PA×5 Closed）三件甄别绿，`PiEnvelope` 其后经 T4G 修复过编（Live_X `.vo` 在盘）；四件已随成果四接入与 R82 注册收尾波（HEAD=39d81aa）并入注册面，认证面 228→246。定理编号 10.1–10.15 连续；评注 10.1–10.4 为语义注记，非机器陈述。

**导语（家族框架）**。本节给出一个统一的对数—指数—圆周率—熵四件认证成果的组合陈述。四件在语句面上分属逼近论（常数包络，envelope）与热力学（熵账，entropy accounting）两个语境，但共享同一证据范式：每条主定理都是**逐 eps（per-eps）形不等式**，配备**可计算模量（computable modulus）** N(eps) 作为 sigT 见证，并给出**显式有理/规范见证**（explicit rational witness）。下文先逐一给出四件的主定理（§10.1–§10.4），再提炼家族框架（§10.5），最后给出组合声明与伞形展望（§10.6）。全部出口位于 Set 层（`QltT'`/`QleT'` 为 `Qlt_bool`/`Qle_bool` 的 Id-反映形；Real 层 `real_lt`/`real_le`），零经典逻辑（零 Axiom/`excluded_middle`），逐件文末 `Print Assumptions` 审计留痕（PA 计数见状态段）。该家族名为**定量构造性分析**（Quantitative Constructive Analysis）：从常数包络到热力学定律，可计算模量贯穿。与本文前九节的关系：级数基座即 §3.2 的 `exp_partial`/`q_pow`/`q_fact`（e 件为该引擎在 x := 1 处的实例），实层桥消费 §9.1 库件 `cauchy_real_pi_leibniz`，严格步底座即 §9.2 第 4 条的 `UpReqStrictStepGen` 族。

### 10.1 ln2 的交错级数双边包络

记 `S_n = Σ_{k<n} (−1)^k/(k+1)`（有理数层 Q）。级数源为交错调和级数，`l2e_term`/`l2e_alt_partial` 为自足定义（不挂库 exp/log 引擎）。

> **定理 10.1（尾界，Leibniz 余项；`l2e_alt_two_sided`）.** 对任意 `m ≤ n`：`|S_n − S_m| ≤ 1/(m+1)`。
> **定理 10.2（奇偶夹逼；`l2e_even_le_odd`/`l2e_parity_gap`）.** 任一偶部分和不超过任一奇部分和：`S_{2j} ≤ S_{2k+1}`；且夹口隙宽显式：`S_{2m+1} − S_{2m} = 1/(2m+1)`。
> **定理 10.3（柯西模量；`l2e_cauchy_modulus`）.** 对任意 eps > 0，存在（可构造）`N = ⌈1/eps⌉ + 1`，使 `N ≤ m`、`N ≤ n` 蕴含 `|S_n − S_m| < eps`。

*证明模式*：四段式——模量列 `m_k = 1/(k+1)` 的反序性；成对项恒等 `|t_k + t_{k+1}| = m_k − m_{k+1}`；对距离 `n − m` 的良基归纳（`lt_wf_ind`，三角拆分 + 归纳假设）；取整引理 `m_{⌈1/eps⌉+1} < eps`（`Qceiling` 整数步进供严格性）。∎

**评注 10.1**. 模量 N 由 `Qceiling` 显式给出，是可抽取程序（extractable witness），非存在性断言；本件配有独立提取验证件 `l2e_g3.v`（`Recursive Extraction` + `Print Assumptions`），验收记录 `Obj.magic = 0`、Axioms Closed。尾界 `1/(m+1)` 为闭式公式（调和速率）。

### 10.2 e 的显式有理双区间

记 `S_n = Σ_{k<n} 1/k!`（正项级数）。本件不自建级数：为 §3.2 引擎 `exp_partial` 在 `x := 1` 处的实例，尾界消费库件 `exp_partial_diff_bound`。

> **定理 10.4（双区间；`eoe_two_sided`）.** 对任意 `n ≥ 1`，取 `lo = S_n`、`hi = S_n + 2/n!`，则 `hi − lo = 2/n! > 0` 显式，且对任意 `m ≥ n`：`lo ≤ S_m ≤ hi`。
> **定理 10.5（柯西模量；`eoe_cauchy_modulus`）.** 对任意 eps > 0，取 `N = ⌈2/eps⌉ + 1`，则 `N ≤ m`、`N ≤ n` 蕴含 `|S_m − S_n| < eps`。

*证明模式*：正项递增性（`eoe_mono`）替代奇偶两翼；尾界由库引擎 `exp_partial_diff_bound`（A := 1）给出 `(Qabs 1)^m/m!·2 = 2/m!`；模量界用 `n ≤ n!` 将 `2/eps` 压入阶乘，再以 `(k+1)·k! ≥ 2·k!` 的阶乘严格增把非严格界压成严格（与定理 10.3 的 ceiling 步进不同源）。∎

**评注 10.2**. 隙宽 `2/n!` 是阶乘速率（factorial rate）——家族中最快的尾界；与 §10.1 的调和速率 `1/(m+1)` 对照可知：模量族 `N_c(eps) = ⌈c/eps⌉ + 1` 的取整分子 c 只承担级数归一因子，真实收敛速率藏在见证公式的分母里。可抽取性注记（如实）：本件语句面与 §10.1 同款 Set 纪律（PA×4 Closed），但独立提取验证件在盘缺位，可抽取性为结构级预期、验证件待补（`l2e_g3.v` 为已验收的验证件样本）。

### 10.3 π 的 Leibniz 有理包络与实层桥

记 `S_n = Σ_{k<n} (−1)^k/(2k+1)`、`L_n = 4·S_n`；π_L 为 §9.1 实层库件 `cauchy_real_pi_leibniz`。

> **定理 10.6（×4 奇偶夹逼与尾界；`pie_leibniz_two_sided`/`pie_leibniz_tail`/`pie_parity_gap4`）.** 任一偶 `L_{2j} ≤` 任一奇 `L_{2k+1}`；`m ≤ n` 蕴含 `|L_n − L_m| ≤ 4/(2m+1)`；夹口隙宽 `L_{2m+1} − L_{2m} = 4/(4m+1)`。
> **定理 10.7（柯西模量；`pie_modulus_cauchy`）.** 对任意 eps > 0，取 `N = ⌈4/eps⌉ + 1`，则 `N ≤ m`、`N ≤ n` 蕴含 `|L_n − L_m| < eps`。
> **定理 10.8（实层有理包络；`pi_rational_envelope`）.** 对任意 eps > 0，存在有理 `lo, hi` 使 `lo < π_L < hi` 且 `hi − lo < eps`（`And` 取积型，零 Prop 泄露）。

*证明模式*：§10.1 四段式的同构替换 `1/(k+1) ↦ 1/(2k+1)` 加因子 4（`QltT'` 出口与 `Qceiling` 模量同构）；新增一层为实层桥 `lp_odd m = S_{2m+2}`（偶子列接引 Q 层部分和），由此构造下/上翼生成器（见证 `c/2 = c/4 + c/4` 拆分），将 Q 层夹逼提升为 `real_lt` 夹逼。∎

**评注 10.3**. 定理 10.8 的端点取 `4·S_{2N′+2} − eps/4` 与 `4·S_{2N′+1} + eps/4`（N′ = 模量在 eps/2 档的取值），即包络端点本身是模量的函数——「包络随精度可控收缩」在语句面直接可见。特例推论 `3 < π_L < 10/3`（`pie_real_three`/`pie_real_ten_thirds`，合取件 `pie_const_bounds_merge`）由 m = 3/4 档包络加 `vm_compute` 数值核验闭合，与 §9.1 Leibniz 侧数值界 `real_pi_leibniz_between_tenthirds` 同档。状态注记（如实）：本件已编译入库（Live_X `.vo` 在盘），定理 10.6–10.8 的语句以在盘稿文面为据，认证随成果四接入与 R82 注册收尾波并入 CI #72（246 注册面 `COQCHK_ALL_PASS`，见状态段与 §1.3）。

### 10.4 Second Law 定量化

设正温度 T、能量 energy、Boltzmann 分布 p_T、分布熵 S[p]、KL 亏账 `KL(p‖p_T)`，一步 Gibbs 热浴核 `(step p)(s′) = Σ_s p(s)·p_T(s′)`（Real 层，CW219 具体 Real 载体；求和机器为 `sumf` 及四假设槽 `sumpos`/`sumext`/`sumlinear`/`sumadd` 的诚实节）。

> **定理 10.9（热浴核不动点；`slq_gibbs_step_fixed`/`slq_step_entropy_eq_boltz`）.** 若 `Σp = 1`，则 `step p = p_T`（逐点）。从而一步演化的实现熵 `S[step p] = S[p_T]`。
> **定理 10.10（主定量式，双向；`slq_entropy_gain_kl_lower`/`_upper`）.** 在归一与能量匹配前提下，对任意 eps > 0：`KL(p‖p_T) − (S[p_T] − S[p]) ≤ eps`（故**熵增 ≥ 熵亏 − eps，熵亏 = KL(当前‖Boltzmann)**），且互补向 `熵亏 − KL ≤ eps`。
> **定理 10.11（实现形；`slq_step_gain_kl_lower`）.** 实现熵增 `S[step p] − S[p] ≥ KL(p‖p_T) − eps`。
> **定理 10.12（定量读法，全闭；`slq_second_law_eps_list`）.** 在 list 载体上全闭：`S[p] ≤ S[p_T] + eps`——其中 Gibbs 腿（KL ≥ 0）以逐 eps 形闭式组装（`real_gibbs_inequality_eps` 引擎 + `real_KL_temp_kl_term_bridge` 桥；LPO 墙下禁 plain KL ≥ 0，与 §2 受限 LPO 等价器 `UpReqLpoEquiv` 同一约束面）。
> **定理 10.13（受体升级；`slq_receiver_second_law_quant`）.** 受体库原 `second_law_irreversible` 件（严格熵增假设的零内容转述）升级为实例化定量结论：严格增 lt 结论 ⟹ 逐 eps le：`entropy x ≤ entropy(dynamics x) + eps`（经温度 softmax 接口桥 `TempSoftmaxInstantiation` 的 `tsi_le_plus_eps_r`/`tsi_rie_setoid` 收口）。

*证明模式*：供体精确式 `S[p_T] − S[p] = KL(p‖p_T)`（`real_entropy_deficit_kl_temp`，real_eq）沿 req 单调平移升格为逐 eps `real_le` 双向界（`plus_opp` 归零 + `real_lt_le_iff`）；不动点定理把实现熵增兑换为熵亏；list 载体四槽求和机器实例化后以 Gibbs 不等式 eps 形引擎闭式收口。∎

**评注 10.4**. 本件「模量」为退化极限：兑换在一步内精确完成（定理 10.9 的 real_eq），eps 完全来自精确式的逐 eps 伸张。这使 Second Law 成为 §10.5 家族的 N = 1 端点——热力学第二定律在此框架下不是范式之外的「应用」，而是范式的极限点。

### 10.5 家族框架

> **范式（三要素）**. 定量构造性分析的一条认证 = (i) eps 形不等式（Set 层出口）；(ii) 可计算模量 N(eps)（sigT 见证）；(iii) 显式见证（闭式公式/规范形）。

四件主陈述的逐件分解：

| 件 | eps 形不等式 | 可计算模量 N | 显式有理见证 |
|---|---|---|---|
| ln2 | `|S_n − S_m| ≤ 1/(m+1)`（QleT'） | `⌈1/eps⌉ + 1` | 尾界 `1/(m+1)`、夹口 `1/(2m+1)` |
| e | `|S_m − S_n| ≤ 2/n!`；区间宽 `2/n!` | `⌈2/eps⌉ + 1` | 双区间 `[S_n, S_n + 2/n!]` |
| π | `|4S_n − 4S_m| ≤ 4/(2m+1)`；Real 层 `lo < π_L < hi`，`hi−lo < eps` | `⌈4/eps⌉ + 1` | 尾界 `4/(2m+1)`、夹口 `4/(4m+1)`、`3 < π_L < 10/3` |
| Second Law | `熵增 ≥ 熵亏 − eps`；`S[p] ≤ S[p_T] + eps`（real_le） | N = 1（一步核精确兑换）+ eps 伸张 | KL 规范形 `Σ p·(log p − log p_T)`、精确式 `S[p_T]−S[p] == KL` |

三要素各自的纪律面统一：eps 形不等式一律 Set 层出口（零 Prop 语句面）；模量一律 sigT witness（可抽取）；见证一律闭式公式（非恒真壳）。

> **命题 10.14（模量线性族）**. 三件常数包络的模量呈同一线性族 `N_c(eps) = ⌈c/eps⌉ + 1`（c = 1, 2, 4 = 级数归一因子），证明骨架逐字同构（定义 → 模量序 → 项恒等 → 奇偶夹逼/尾界四段式）；Second Law 件为其 N = 1 退化端点。

**差异轴**（家族内部两个正交轴）：（轴一）常数逼近 vs 物理不等式——前三件产出区间套 + 柯西模量（逼近论语义），末件产出逐 eps 双向界 + 单向定量读法（热力学语义）；前者模量回答「多少步够」，后者模量回答「一步兑换多少亏账」。（轴二）交错级数 vs KL 亏账——前者靠符号结构（偶/奇两翼单调 + 成对项消去 `|t_k + t_{k+1}| = m_k − m_{k+1}`；ln2/π 交错需奇偶夹逼，e 正项退化为单调上逼 + 阶乘尾），后者靠正性引擎（Gibbs eps 形 + req 平移 + eps 伸张），符号结构的位置由不动点精确式替代。

### 10.6 组合声明、文献定位与伞形展望

**组合增量**。四件并列时是四个收敛/不等式结果；组合后是同一三要素范式下的四个实例：其一，同一证据范式可公理化，第五件（如 √2、Euler 常数）入库成本降为填槽；其二，模量可抽取性贯穿全谱（`⌈c/eps⌉+1`、`2/n!`、一步不动点全部是 sigT + `Qceiling` 可计算程序，非存在性口号）；其三，四件排成一条有内在次序的谱线——ln2（单比特熵的常数值）→ e（指数族之基，其部分和引擎与 Boltzmann 权同属一个指数家族）→ π（实层桥的有理包络）→ Second Law（同一 eps-模量-见证范式在热力学定律上的实例化）。

> **定理 10.15（谱系；综合陈述）**. ln2、e、π、Second Law 四件在「eps 形不等式 + 可计算模量 + 显式见证」三要素下构成同一认证家族的四个实例，且其全部精度预算为可抽取程序；家族的严格步公共底座为命名引理族 `UpReqStrictStepGen`（全库 734 处内联 eps 拆分惯用法的收敛命名，§9.2 第 4 条：`ssg_half_quarter_eps_lt` 及取整步/伸张腿）。（本条为对既有四件的组织性综合，非新数学内容；伞形机证陈述见本节展望。）

**组合声明与文献定位（诚实分级，组合空白写法为主）**。三组件各有分立先例，逐一引证。π 侧（先例延伸 + 形态统一，非「无先例」）：mathlib `Mathlib.Analysis.Real.Pi.Bounds`（文献 [15]）给出挂于固定序列的定理级参数化包络（`Real.pi_gt_sqrtTwoAddSeries`/`Real.pi_lt_sqrtTwoAddSeries`，区间宽 `1/4^n`，模量可读出但无 `N(eps)` 形模量函数封装）；Coq stdlib `Rtrigo_def`/`Machin`（文献 [16]）给出级数定义 + 部分和夹逼（误差隐含于部分和内，无闭式误差项）；coq-interval（文献 [17]）与 Isabelle/HOL `Approximation`（文献 [18]）给出战术级精度参数包络（精度参数在战术层，不在定理陈述层）。本件的差异点是把「显式有理上下界 + 显式 N(eps)」统一为**可抽取的定理级模量函数**。Second Law 侧：KL 亏账的数学底座已在 mathlib 就位（`Mathlib.InformationTheory.KullbackLeibler`，2025：Gibbs 型非负、链式法则、数据处理不等式；文献 [19]），但与任何热力学陈述零连接；第二定律的 ITP 形式化在已检索范围内唯一是 Lieb–Yngvason 式**定性**框架（ThermodynamicsLean（文献 [20]），Lean 4，进行中/部分，覆盖至原文 §II.E，不作「已完成」声明）；「熵增 ≥ 熵亏(KL) − eps」的逐 eps 定量形，在已检索的形式化库与文献范围内**未检索到先例**（措辞按「未检索到」而非「不存在」，与 §1.1 同一口径）——此为可辩护的组合空白。该定量形态在非形式文献中自然存在（表述合法性）：Seifert 的轨迹熵产生 = 正/反轨迹测度 KL 散度（文献 [21]）、Baez–Fong 的相对熵单调衰减 = 第二定律信息论形态（文献 [22]）、Cover–Thomas 第 2 章的 Markov 链相对熵衰减读法（文献 [23]）。「单一可计算模量贯穿」的组合论述近旁先例为数值内核单线贯穿数学对象（Isabelle `Approximation` → 数值 ODE/Lorenz 链；CoRN 的 ε-计算底座贯穿，文献 [3]；旁证 arXiv:2608.21502 的 `ricci_flow_uniform_existence`——模量先于对象类选定的定量升级，2026 新文、尚未经同行评审，仅作旁证不作主引（文献 [24]））——本节是把该范式接到物理定律侧的组合陈述（组合空白写法，见上）。

**伞形展望（实装候注册）**。组合价值的机械兑现是伞形注册件 `UpReqQuantConstThermo`（零编译设计稿、非实编；前缀 `uqct_` 实装前按纪律全库防撞）：① 家族抽象槽——Section 三槽（尾界 `hb_tail`、模量界 `hb_mod`、见证反序 `hb_anti`），三包络共槽；② 家族母定理 `uqct_family_cauchy`——模量柯西件（witness := M eps，分案骨架照 `l2e_cauchy_modulus` 的 leb 对折，四件注册后 exact 级接线）；③ 精确式 → 逐 eps 升格母件 `uqct_exact_to_le_eps`——Second Law 腿的族级去实例化（req 平移 + eps 伸张），将来任何「精确式 → 逐 eps 界」装配可直接消费；④ 模量线性族索引定义 `uqct_l2e_N`/`uqct_eoe_N`/`uqct_pie_N`（c = 1/2/4）；⑤ 伞形组合定理 `uqct_const_thermo_spectrum`——五腿合取（ln2/e/π 三腿 Q 层模量件 + π Real 桥腿 + Second Law list 载体全闭腿），采用合取而非打包 Record，避免给异质件强加同型接口（诚实分腿）；⑥ 严格步底座接线位——证明体内严格步一律走 `ssg_`/`tsi_` 命名件、禁内联，使 734 处审计的收敛成果在本家族内继续累积。全部证明体以「依赖四件注册后接线」占位、不使用任何实编占位命令；实装令随四件注册完成（R82 及其后波次）核发。

---

## 参考文献

1. O'Connor, R. (2008). Certified Exact Transcendental Real Number Computation in Coq. *TPHOLs*.
2. Geuvers, H., Niqui, M., & Wiedijk, F. (2000). Constructive Reals in Coq: Axioms and Categoricity. *TYPES*.
3. Cruz-Filipe, L., Geuvers, H., & Wiedijk, F. (2004). C-CoRN, the Constructive Coq Repository at Nijmegen. *IJCAR 2004*, LNCS 3097, Springer.（现行维护仓库：rocq-community/corn，https://github.com/rocq-community/corn，访问日期 2026-09-06；无单一版本号——本文 §2 对比以访问时点的仓库内容为准。）
4. Rudin, W. (1976). *Principles of Mathematical Analysis*. McGraw-Hill.
5. The mathlib Community. *mathlib: The Lean Mathematical Library*. https://github.com/leanprover-community/mathlib（访问日期 2026-09-08；本文 §2 的 `real.exp_pos` 方法论对比以其经典证明路线为据，无单一版本号）。
6. Bishop, E., & Bridges, D. (1985). *Constructive Analysis*. Grundlehren der mathematischen Wissenschaften 279. Springer-Verlag.（Bishop 1967 *Foundations of Constructive Analysis* 为初版前身。）
7. Bridges, D., & Vîță, L. (2006). *Techniques of Constructive Analysis*. Universitext. Springer.
8. Troelstra, A. S., & van Dalen, D. (1988). *Constructivism in Mathematics: An Introduction*（两卷）. North-Holland.
9. Krebbers, R., & Spitters, B. (2013). Type classes for (easily) efficient exact real arithmetic in Coq. *Logical Methods in Computer Science* 9(1:28). DOI: 10.2168/LMCS-9(1:28)2013.
10. Boldo, S., Lelay, C., & Melquiond, G. (2015). Coquelicot: A User-Friendly Library for Real Analysis for Coq. *Mathematics in Computer Science* 9(1): 41–62.（官方仓库：https://gitlab.inria.fr/coquelicot/coquelicot 。）
11. Hölzl, J., Immler, A., & Huffman, B. (2013). Type Classes and Filters for Mathematical Analysis in Isabelle/HOL. *ITP 2013*, LNCS 7998, Springer.
12. MathComp-Analysis（math-comp 团队）. *Analysis Library for MathComp*. https://github.com/math-comp/analysis（访问日期 2026-09-12；无单一版本号）。
13. UniMath（Voevodsky 等发起）. *UniMath: Univalent Mathematics*. https://github.com/UniMath/UniMath（访问日期 2026-09-12；无单一版本号）。
14. The Univalent Foundations Program (2013). *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study. https://homotopytypetheory.org/book/（第 11 章为构造性实数）。
15. The mathlib Community. *Mathlib.Analysis.Real.Pi.Bounds*. https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Bounds.html（访问日期 2026-09-16；无单一版本号）。
16. The Rocq/Coq standard library. *Coq.Reals.Rtrigo_def* / *Coq.Reals.Machin*. https://rocq-prover.org/doc/V8.19.1/stdlib/Coq.Reals.Machin.html（访问日期 2026-09-16）。
17. coq-interval. https://coqinterval.gitlabpages.inria.fr/（访问日期 2026-09-16）。
18. Hölzl, J., Immler, F., et al. Isabelle/HOL `HOL/Decision_Procs/Approximation`（"Proving Inequalities over Reals with Computation in Isabelle/HOL"）。
19. The mathlib Community. *Mathlib.InformationTheory.KullbackLeibler*（Basic/ChainRule/DataProcessing/KLFun，2025）. https://github.com/leanprover-community/mathlib4（访问日期 2026-09-16）。
20. ThermodynamicsLean（Lean 4，进行中）. https://github.com/or4nge19/ThermodynamicsLean（访问日期 2026-09-16）。
21. Seifert, U. (2005). *Phys. Rev. Lett.* 95, 040602；Seifert, U. (2012). *Rep. Prog. Phys.* 75, 126001.
22. Baez, J. C., & Fong, B. (2016). Relative Entropy in Biological Systems. *Entropy* 18(2):46.
23. Cover, T. M., & Thomas, J. A. *Elements of Information Theory*（第 2 章）.
24. arXiv:2608.21502（2026 预印本，尚未经同行评审；本文仅作旁证）。
25. Bishop, E., & Richman, F. (1987). *Varieties of Constructive Mathematics*. London Mathematical Society Lecture Note Series 97. Cambridge University Press.（LPO / LLPO 的权威定义源，见 p. 3）
26. Ishihara, H. (2006). Reverse Mathematics in Bishop's Constructive Mathematics. *Philosophia Scientiæ*, CS 6, 43–59. https://doi.org/10.4000/philosophiascientiae.406 （构造性分析中定理对 LPO / LLPO 的分类）
27. Ishihara, H. (2005). Constructive Reverse Mathematics: Compactness Properties. In L. Crosilla & P. Schuster (Eds.), *From Sets and Types to Analysis and Topology: Towards Practicable Foundations for Constructive Mathematics*. Oxford University Press.
28. Diener, H. (2020). Constructive Reverse Mathematics. arXiv:1804.05495. https://arxiv.org/abs/1804.05495
29. Mines, R., Richman, F., & Ruitenburg, W. (1988). *A Course in Constructive Algebra*. Universitext. Springer-Verlag.
30. Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437
31. Kullback, S., & Leibler, R. A. (1951). On Information and Sufficiency. *Annals of Mathematical Statistics* 22(1):79–86. https://doi.org/10.1214/aoms/1177729694
32. Csiszár, I. (1975). I-Divergence Geometry of Probability Distributions and Minimization Problems. *The Annals of Probability* 3(1):146–158. https://doi.org/10.1214/aop/1176996454
33. Degenne, R. (2025). Markov Kernels in Mathlib's Probability Library. arXiv:2510.04070. https://arxiv.org/abs/2510.04070

---
## 附录 A：主链核心引理/定理清单

> 完整行号索引与逐字证明脚本见补充材料 S1（随论文 artifact 提交）。

| 名称 | 语句摘要 | 所属章节 | 验证状态 |
|---|---|---|---|
| `q_pow_add` | `x^(a+b) == x^a · x^b` | §3.1 | 已证 |
| `exp_partial_cauchy` / `exp_partial_lipschitz` / `exp_partial_cauchy_bounded` | 截断级数柯西性 / Lipschitz 控制 / 一致有界 | §3.2 | 已证 |
| `exp_partial_zero` / `cauchy_real_exp_zero` | `exp_partial n 0 == 1`；`exp 0 == 1` | §4.1 | 已证 |
| `corr` / `corr_nonneg` | 校正项定义；`corr m a ≥ 0` | §4.2 | 已定义 / 已证 |
| `altf_zero` | 交错二项式系数和归零 | §4.2 | 已证 |
| `e_sq_expand` / `o_sq_expand` | `E_m² == esq_sum`；`O_m² == osq_sum` | §4.3 | 已证 |
| `vander_4m2` / `vander_4m4`（交错二项式恒等） | `a^{4m+2}` / `a^{4m+4}` 层系数恒等 | §5.4 | 已证 |
| `corr_diff_eq_sq_diff` | `corr` 相邻差 == 偶/奇平方和差（归纳步核心） | §5.2 | 已证 |
| `esq_eq_corr` | `E_m² − O_m² == 1 + corr m a`（主恒等式） | §5 | 已证 |
| `exp_even_neg_nonneg` / `exp_even_neg_pos` / `exp_partial_tail_pos` | Q 层正性链（`0 ≤ a ⟹` 偶阶截断非负/严格正） | §5.1 | 已证 |
| `cauchy_real_exp_pos` | `∀ x : Real, cauchy_real_exp x > 0` | §6.2 | 已证（C1 主结果） |
| `cauchy_real_exp_plus` | `exp(x+y) == exp x · exp y`（real_eq 意义） | §6.7 | 已证 |
| `q_binom` / `exp_cauchy_double` / `exp_trunc_band_up` / `exp_trunc_bound` 族 | ExpPlusStage2/2b 代表件（二项式定理、双重和重组、截断误差带与构造趋零；两节合计 58 条） | §6.6 | 已证 |
| `exp_order_embedding` / `exp_surj_pos` / `exp_reflects_lt` / `real_exp_ge_linear` 等 | exp-log 保序群同构五件与不等式族（合计 21 条） | §9.1 | 已证 |
| `real_eq_mult_compat` 等 Proper 兼容性族 | `real_eq` 的替换原理（含参数序适配桥） | §6.4 | 已证 |

## 附录 B：接口字段回填与审计快照

**接口字段回填（三个实例）**：

| 实例 | 相等谓词 | 代表性回填 | 状态 |
|---|---|---|---|
| `Real_RealInterfaceSetoidCore` | `req := real_eq` | 环律/序律/metric 逐 eps 族/完备性桥 `real_cauchy_complete_metric_natle` | 全部字段实值 |
| `Real_RealInterfaceSetoid`（完整版） | `req := real_eq` | `exp_neg := cauchy_real_exp`、`exp_neg_pos := cauchy_real_exp_pos`、`exp_neg_plus := cauchy_real_exp_plus`、`log_inv := cw_log` | 57 字段全部实值 |
| `RealEnhancedReal`（增强版） | `req := real_eq` | exp/log 族取 Real 层派生引理（如 `real_exp_neg_pos`，与完整版数学内容同源）；正性/保序/min/abs 等扩展字段 | 全部字段实值 |

**审计快照**：在两个历史验证快照（迭代 198 与 206）时点，81 条选定核心定理/定义的批量 `Print Assumptions` 全部返回 `Closed under the global context`；此后新增面经禁用词扫描、全量编译退出码 0 与 `coqchk` 内核校验维持验证状态。批量假设检查的最近一次全量执行在迭代 198/206 快照，未整体重跑（§8.3）。

**边界声明**：闭合审计的口径与数字见 §8.3「验证方法与可复现性」；接口实例见附录 B；`exp_neg_pos` 等字段的回填属字段级实例化（§1.1 定义（i）），抽象层 Id 系定理的签名迁移尚未完成（§1.1 定义（ii）），列为 §9.2 后续工程，与本文 `esq_eq_corr` / `cauchy_real_exp_pos` 的证明相互独立；T-π3（π_geom == π_L）经两条独立证明路线闭合（`b5dT_f1_pi_geom_eq_leibniz_single`/`_univ`），终末定理 C `b5dU_cos_piL_half_zero`（cos(π_L/2)==0）已闭（§9.1、附录 C）。Banach 代数推广线的定理面见正文 §7，模块化认证面与当前库 HEAD 的对应关系见 §1.3「当前库真态声明」与 §6.7 末「范围外披露（Strong 及其他）」；本附录清单口径截至 219 基线。

## 附录 C：T-π3、和角恒等与可微性主件清单

| 定理/路线 | 语句摘要 | 归属与共享件 |
|---|---|---|
| `real_cos_pi_half_zero` | cos(π/2) == 0（二分机械 `cos_scan`，带余量可判定符号测试） | 几何 π 重点定理；配套 `cos_pi_half_unique`（(3/2,5/3) 内唯一）与 `cos_pi_half_unique_widened`（(3/2,2) 内唯一） |
| `real_pi_geom_between`（T-π2） | 3 < π_geom < 10/3 | 与 `real_pi_leibniz_between_tenthirds`（3 < π_L < 10/3）构成两 π 各自数值界 |
| `b5dQ_E_rational_zero` | ∀q ∈ Q∩(0,1)：E(q) == 0（E := sin∘arctan − id·cos∘arctan） | 归零层；两条独立证明路线的唯一共享机器证明 |
| 单点轨：`b5dF_E_one_zero_of_rational` → `b5b_hsc_main` → `a3_closure_f1` | 端点逼近：E(1)==0 ⟹ sin(arctan 1)==cos(arctan 1) ⟹ π_geom==π_L | `b5dF` 前提即 `b5dQ` 语句 |
| ∀x 轨：`b5dS_E_zero_on_unit` → `b5b_f1_closure'` | 有理近似传输：(0,1) 逐点归零 ⟹ π_geom==π_L | `b5dS` 证明体内调用 `b5dQ` |
| `b5dT_f1_pi_geom_eq_leibniz_single` / `_univ` | π_geom == π_L（real_eq） | T-π3 两条独立证明路线主定理（独立双证仅出现在最终包装定理层） |
| `b5dU_cos_piL_half_zero`（终末定理 C） | cos(π_L/2) == 0 | routeA/alt 双路径 |
| `rs_add_sin` / `rs_add_cos` | sin/cos 和角恒等（real_eq） | Q 层地基 `sc_add_*` 四件；沿用 `cauchy_real_exp_plus` 的 eps/3 装配模板 |
| `real_sin_deriv_linear` / `real_cos_deriv_linear` | 全域可微：sin′ == cos、cos′ == −sin（Bishop 逐 eps） | 配套零点线性界两件；与 `real_exp_deriv_eq_self`、`real_log_differentiable` 构成可微四函数层 |

> 完整行号索引与逐字语句见补充材料 S1；历史构建与维护快照见补充材料 S2。

