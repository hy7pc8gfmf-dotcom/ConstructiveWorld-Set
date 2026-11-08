# 评审意见材料(定稿)——论文 A 投稿 JAR 版

- **评审对象**:《Constructive Strong Irrationality of π: A Zero-Axiom Criterion with an Explicit but Factorially Growing Search Bound》(投稿包 `paper_zip/投稿版-JAR-KB87/`:main.tex + partA/partB/partC/refs.tex + cover-letter.md;配套中文稿 `论文A-中文终版-draft - 05.md`;复现手册、审计日志)
- **起草说明**:本材料供形式化验证方向评审人使用。所有论断分两类标注:**【论文已声明】**(出处=论文 §节/行号或配套材料)与**【评审人推断】**(出处=本会话实测或其他勘察材料,逐条给出来源)。凡本会话实际执行的检查,附命令与输出(见文末"附:本次会话实测记录");凡未能在本会话执行的检查,如实注明"未复跑"。
- **核验基线**:引用面第一手核验记录 `claim_verification_firsthand.md`(21 条坐标:19 精确命中、2 条 +6 行漂移且漂移被论文《审计日志》A1.7(a) 自行披露;主件 5,723 行/SHA-1 双验证;主件裸计数 66);主库勘察 `main_survey.md`;旗舰链逐件 `flagship_chain.md`;五常数与 ZZ 线 `five_constants.md`。本会话在其基础上对冻结重建树 `D:/ComplexAnalysis/ConstructiveWorld-Main` 复跑了 5 项检查(见附录)。
- **定稿说明**:本稿在起草稿基础上落实终审意见 8 条:引文坐标更正 3 处(§一.1、§二.4、§三.3)、§二.4 增补 μ₀_cos 对数反转承重件并新增 Q15、§四.7 Glossary 计数更正(14→19)、§3.1 测度谱系记号改按 partC.tex:212、Q2 增补全量编译差异清单问项、附录补时间戳核对记录 1 行。终审复核确认项(评审人三项实测关键事实在稿无遗漏、无"评审人推断"误标为"论文已声明"、定性总体公允)不改动正文。

---

## 一、论文主张清单(JAR 投稿版)

### 1.1 三件定位(primary / organizational / engineering)

**【论文已声明】** 投稿版将贡献重组为"三件定位,另附一件记录与一张推广面"(§1.3,partA.tex:111;cover-letter.md:19-23):

| # | 定位 | 内容 | 论文自设边界 |
|---|---|---|---|
| 1 | **首要贡献**(primary,§5) | π 强无理的构造性闭合:无条件形分离定理 `leibsep_pi_rational_unconditional`——对每有理数 a/b(b≠0)构造显式有理 c>0 严格小于点态距离 \|π_geom − a/b\|,无前提、零公理、Set 层 `sigT` 见证 | 逐点型(pointwise),非一致型;主张面**仅由无条件形承载**,守卫形(§5.1)与组合定理(§5.5)"同为支持证据,不属独立贡献"(partA.tex:111) |
| 2 | **组织性贡献**(organizational,§3–§4) | 五段判据框架(窗口界→整除见证→无界 margin→逃逸引理→可判定检验)+ 逃逸引理的标准库化(PR #313,未合并) | "**事后描述,非事前框架**";不能对任意级数自动生成证明;逃逸引理是唯一具跨实例复用潜力的组件;"标准化"意义"潜在而非既成"(partA.tex:111;partB.tex:84) |
| 3 | **工程交付**(engineering,§5.6–§5.7) | 跨库 CReal 形态转移(`ucreal_of_real`/`ucreal_lt_compat`/`ucreal_pi_sep_unconditional` 及等式层双向桥),外加 √2/√3/e 实例化 | "实质技术内容是例行适配工作,难度不构成独立数学贡献";价值在使分离陈述经标准库接口可用(partA.tex:111) |

**【评审人推断】** 这一定位相对 figshare 预印本 v4(`paper_v4.md`)是**实质性降格重述**:v4 摘要将三支柱标为"并列首要贡献(第一、二项)+ 独立贡献(第三项)",并称"第一、二项贡献为新数学"(paper_v4.md:17 摘要、:41 贡献定位段,两处均 grep 逐字命中);投稿版把第二件改为"事后组织描述"、第三件改为"工程交付"。这是向审稿人诚实化的重要修订,但也说明 v4 的公开措辞曾经过强——建议作者在 cover letter 中主动说明这一措辞变迁(预印本披露段现只说明版本关系,cover-letter.md:29)。另,术语"分离指数"已改名"分离窗口级"(partA.tex:43、审计日志 A8(e)),v4 题录仍用旧名——作者已在审计日志 A8(e) 登记此题录不一致,属**已声明的遗留项**。

### 1.2 强度阶梯

**【论文已声明】** 摘要与 §1.1 明示三级阶梯:**一致型(Bishop 对 √2,1/(3b²)) > 全称逐点型(本文 π) > 单点实例级(Nuprl 22/7)**;本文结果"在逻辑强度上弱于 Bishop 对 √2 的一致型下界"(main.tex:28;partA.tex:68)。√2 一致型下界的库内形式化(`Sqrt2UniformStrongIrrational`,显式 margin 与 Bishop 同值)已由延伸库交付并经 run #35 云端认证(2026-11-01;partA.tex:68;审计日志 A5(g-1))。

**【评审人推断】** 该阶梯本身在构造性数学语义下成立(一致型蕴涵逐点型,反之不然;逐点 Skolem 函数不受一致界支配,论文在 §1.1 给出结构性理由,partA.tex:68)。把自身置于阶梯中位并点名上界(Bishop)与下界(Nuprl)两侧先例,是少见的老实定位方式,值得肯定;但注意阶梯两端证据等级不对称:Bishop 端在论文内从"转述级 T5"(ref04 注记"registered from public secondary accounts, not verified to page level",refs.tex:35)升至"库内同值形式化"(2026-11-01 波),Nuprl 端始终是"据语句面转录"(审计日志 A7 末段)。引用两端时应注明证据级差。

### 1.3 "明确不主张"清单

**【论文已声明】**(散布于全文,集中于 §1.3(b)-(d)、§7、§8 对照表 partC.tex:262-282):
1. 不主张一致型下界(§1.3(d),partA.tex:113;§8 表行 10 "未交付面");
2. 不主张对经典渐近测度 μ(π) 的任何界关系,除非严格可推导;不参与测度竞争(§1.3(a)、§7"两种读法"段,partC.tex:227;§8 表行 9);
3. 不主张与"经典 π"相等(§1.3(c));
4. `Bexp` 增长律只作 O 上界,不主张 Θ(§4.3,partB.tex:145;附录 B 口径段 partC.tex:415);
5. 判据框架非事前框架、不自动生成证明(§3.3,partB.tex:84);
6. "显式正距"不得读作"可用正距"(§4.2 量级对照段,partB.tex:137);
7. 对提取产物的时间性能/终止性/完全可初始化性不作主张(§1.5(ii),partA.tex:154);
8. PR #313/#316 未合并,"标准化"是潜在意义(partA.tex:111;§8,partC.tex:286);opam 索引收录不等于进入标准库(§8,partC.tex:286);
9. 上游 PR 的 CI/审计结论是上游面自述,本文未独立复核(§8 项 (x),partC.tex:284);
10. 环境可复现性不主张(复现手册 M6(o));三计数、run 号、行号等均为作者侧工程记录,"独立可核验面/不可核验面"已分列(partA.tex:117 末段)。

**【评审人推断】** 这份不主张清单在同类投稿中罕见地完整,且 §8 的"主张—边界对照表"(10 行,partC.tex:262-282)提供了集中索引。评审人核对后未发现"正文主张越出对照表边界"的明确反例——**唯一疑似例外**是 §7.1 第 2 项/§7 的"一致型无条件闭合"新段落(见 §四.1 与 §二.4,这是本材料最重要的一致性问题)。

### 1.4 数值锚:22/7 与 355/113;Bexp~10²⁴¹ vs N*=1582 的鸿沟

**【论文已声明】**(§4.2,partB.tex:133、137):
- 22/7:`lw0_pi_d0_of(22/7)=5`;n_sel = `lw0_n_select(10·5) 0 + 1` = **123**;分离检验实测命中级 **N\* = 1582**(该级窗口距 **5/3165**;精确有理增量扫描,机外镜像仪器口径);`Bexp(22/7)` 量级 **10²⁴¹ ≤ Bexp < 10²⁴²**(BF 项 22¹²³·(246)!/(123!)² 定位于 10²³⁷ ≤ BF < 10²³⁸,K ∈ [10²³⁹,10²⁴⁰),Bexp = 64K);交付见证 c ≈ 1/(32K) ≈ **10⁻²⁴²**,比真实距离 |π−22/7| ≈ 1.26×10⁻³ 低 **10²³⁹ 倍以上**;阶乘率上界超出实际命中级约 **10²³⁸ 倍**。
- 355/113:d0 = 5、n_sel = 123(与 22/7 同值,选取级只经 d0 进入);N\* = **7,497,258**(窗口距 5/14994517 ≈ 3.33×10⁻⁷;整数定标增量扫描,定标 10⁶⁰ 逐级下截);两实例 d0/n_sel 锚同值而命中级相差约 4.7×10³。
- 证据级:**全部为机外精确(整数/有理)算术记录,T5,非库内定理**(partB.tex:133 明示"not in-library theorems";§4.3 开头"Stage-3 magnitude conclusion declared up front",partB.tex:145);10⁻²⁴² 的推导路径与"窗口距 5/3165 是另一对象"的口径区分在复现手册 M6(m)。
- 配套声明:库内对 22/7 在 1582 位级的直接求值**未产出**(成本受限而非可求值性受限,复现手册 M4(b));库内可求值的只有小实例(`lw5n_nsep (3/1) = 2`、`lw5n_sep_dec (22/7) 20 = false`,M4(a))。

**【评审人推断】** 这组数值锚是投稿版相对 v4 的**新增内容**,其作用是把"存在性可计算 vs 实践可行"的鸿沟从一个抽象声明变成可复核的具体账目;Bexp~10²⁴¹ 与 N*=1582 的 10²³⁸ 倍差距是全文最有说服力的一个自反性数字(证明自己交付的界远离可用)。两点保留:(i) 全部锚为 T5 机外账,论文虽反复声明,但锚值本身无法从归档制品复算——见问题清单 Q13;(ii) 355/113 的 N\*=7,497,258 扫描"定标 10⁶⁰ 逐级下截、累计截断亏远小于判定间隙"的精确性论证(partB.tex:133)是作者侧描述,未见独立复核记录。

---

## 二、代码库对主张的支撑度(逐条:贡献 → 库内证据 → 核验结果)

### 2.1 逐条支撑表

| 贡献/主张 | 库内证据(冻结树实测) | 核验结果 |
|---|---|---|
| 主定理语句面(§5.2) | `Local/LW0LeibSeparation.v:5697` `Theorem leibsep_pi_rational_unconditional : forall a b : Q, QltT 0 (Qabs b) -> sigT(...real_lt (real_const c) (real_metric real_pi_geom ...))` | **✓ 本会话逐字复核一致**(sed :5697-5702;与第一手核验记录、flagship_chain §2.1 三方一致)。签名与论文 §5.2 转录逐字同 |
| 装配动作(§5.2/附录 B) | :5705-5719:`destruct (leibsep_q_kernel (a / b)%Q)`、`lw0m_vanish_pi (c * (1 # 8))`、`set (N1 := Nat.max N (Nat.max N0 1))`、`apply (leibsep_pi_sep_alpha_guarded a b N1 (c * (1 # 4)))` | ✓ 第一手核验记录 §三 :5705-5712 实测与论文附录 B 的 c₀=c/4 装配推导一致 |
| 审计语句计数(§1.5) | 主件行首锚定 `^Print Assumptions` = 61 条;子串计数 = 66(5 条在块注释);去注释口径 61 为判据(复现手册 M2(a) 给出可执行片段) | ✓ 本会话复跑两种计数,与论文口径完全一致;`^(Axiom|Parameter|Hypothesis|Conjecture|Admitted)` 全件零命中(文本级;flagship_chain §〇.2 对 16 件引用面同样零命中) |
| 守卫形(§5.1) | :298-306 四元前件 + sigT 结论 | ✓(第一手核验;flagship_chain §2.1 逐字摘录) |
| Q 内核(§5.2 关键链) | `leibsep_q_kernel` :5452,门真支复用守卫内核、门假支走 Niven 带/WING/载体黑箱(:5457-5694) | ✓(第一手核验命中 :5452;flagship_chain §2.1 给出双出闸骨架;论文"两半支独立闭合、包络序列上汇合"的叙述与源件一致) |
| S973 常数(附录 B) | :4033 `Notation S973 := (1 + (121 # 18) + (73205 # 5364))%Q` | ✓ 逐字命中(第一手核验;与附录 B 的 38209/1788 化简叙述一致;源内 :5478/:5481 有 `vm_compute; reflexivity` 收尾) |
| 组织性贡献五段(§3.1) | `LW0LeibWindow.v`:`leiblw_dist_set` :747、`leiblw_integrality` :546、`leiblw_margin_unbounded` :910、`leiblw_escape_obstacle` :865、`leiblw_Id` :63;`LW5SepComplexity.v`:`lw5n_sep_dec` :301、`lw5n_find` :416、`lw5n_nsep` :429(现 :435) | ✓ 坐标系 19/21 精确命中、2 条 +6 行漂移且被《审计日志》A1.7(a) 披露(第一手核验记录 §二);件头"预算足用性不主张"的诚实注记在源件在卷(flagship_chain §2.4) |
| 率层闭合定理(§4.3) | `tlw1448_rebase/transfer/l2escape` + `tlw1459_fold.v` 四件;`tlw1459_fold_closed` :42(见证即 `Bexp q` 自身)、双向带 :74-80 | ✓(flagship_chain §2.5-2.8 全件读毕,签名与论文逐字一致;论文"紧界不自动给出紧上界"段与"见证取 Bexp q 自身"的源件事实吻合) |
| 工程交付(§5.6-5.7) | `ucreal_bridge.v` 515 行(`ucreal_of_real` :226、`ucreal_pi_sep_guarded` :486);`u4a_budget_flip.v` 408 行;`u6a_dammroze_quant.v` 228 行;u5c 桥+三实例 | ✓ 行数与语句坐标全中(flagship_chain §〇.1、§2.10-2.12;第一手核验 21 条中的 ucreal/u4a/u6a/u5c 条目) |
| 延伸面五支逃逸点(附录 B) | `UpReqSqrt3Irrational.v:915` `Definition ir2_escape : lic_escape_window ir2_x ir2_e.`,五支逐行核实(den+8 / 矛盾 / num+den+1 / den+8 / 1) | ✓(第一手核验命中 :915;five_constants §2 逐支坐标与论文附录 B 五支表逐点吻合) |

### 2.2 主张面覆盖与证据分级

**【论文已声明】** 引用面 T1 覆盖 23/23 符号(A 侧);含延伸面全口径 13/15(partA.tex:139);T1 = 在册+编译凭证+公理审计,提取审计不入档(A1.4);审计语句按"证明段落入口"集中布点,内核件与守卫形无独立 PA 语句,由无条件形传递闭包+coqchk 合取间接覆盖(partA.tex:152;复现手册 M1"审计语句分布"段,11 簇坐标)。

**【评审人推断】** 两个支撑度弱点,均为论文自己登记的:
1. **两个承重件无专属审计行**:`leibsep_q_kernel`(:5452)与守卫形(:298)的最近独立 PA 在 ±200 行邻域外(最近簇 :4025-4026 与 :5721-5722);论文以 2026-10-12 单发 REPL 取证补强(复现手册 M1 逐字转录,"Closed under the global context"×3),但该取证"性质为取证而非新的认证来源"(同段原文),产物是否公开可取未登记——见 Q6。
2. **S10(12,497 行)仅 1 条 PA 且不覆盖旗舰链所引 π 常数**;`u4a_budget_flip.v` 全件零出口审计行(flagship_chain §三 汇总表、§四.4)。论文对后者的登记是"该文件不在 23 符号主张面、不单独主张档位"(partC.tex:80 LW3ExclusionCalc 段同款逻辑),但对 u4a 所在的 §5.6(ii) 三条语句,正文标注为 T1(run #205)。评审人认为此处档位承重实际落在 coqchk 全树判定而非件内 PA——应向作者索取该面的逐条 PA/coqchk 归属说明(见 Q6)。

### 2.3 代际错位:冻结面 9.1-only 与 Statements 9.3.0(重点)

**事实链(全部标注来源):**

1. **【论文已声明·Statements】** partC.tex:307-309:"All mathematical content of the paper is carried by machine verification **under Rocq 9.3.0 (built from source via opam, OCaml 5.5.2)**";"All formal content in this paper was **developed and kernel-certified under Rocq 9.3.0** … with full-closure coqchk certification (4 parallel lanes); CI status, layered: Set and π verify continuously on 9.3 CI (Set #145 / π #40, all green), **while the Main repository's consistency-tier closure certification was completed in the 9.1 CI furnace, with the 9.3 rebase in transit (the active Main CI pins 9.1)**. The known Rocq 9.1 kernel vulnerability face … does not exist in 9.3, so the results of this paper are unaffected by that family."
2. **【论文已声明·同一投稿包内矛盾】** cover-letter.md:17:"with machine verification in **Coq (Rocq 9.1)**";§1.5 一句版结论:"**on Rocq 9.1.0**, via the coqchk three-criterion conjunction …"(partA.tex:187);判定实验在"Rocq 9.1.0"执行(partA.tex:165);复现手册定位"任意具备 **Rocq 9.1** 的机器"、`.vo` 版式 **90100**(手册第 3 行、M2 ⑤)。
3. **【本会话实测】** 冻结 tag 重建树在 **Rocq 9.3.0**(opam93,`coqc --version` = "The Rocq Prover, version 9.3.0 / compiled with OCaml 5.5.2"——恰为 Statements 点名的版本串)下按 order.txt 序编译:S01–S10 十件通过,**S11_TP3B5.v:2665 编译失败**:`Error: Multiple "Proof" commands not supported.`(compile_log.txt 2026-11-07 00:37:31 起;last_fail_11.out 同文;源件 :2665-2666 连续两个 `Proof.`,本会话 sed 确认)。按 order.txt 拓扑,S11 在主定理闭包之内——复现手册 M6(l) 明确列主定理编译闭包 45 件"含 S11_TP3B5"(该件另携 5 条 Section Hypothesis)。
4. **【评审人推断】** 三点结论:
   - **归档制品(Zenodo 23717748 = tag v1.0-pi-separation = 冻结面)只在 9.1 可编译**;论文主定理的认证面(CI run #195 等)全部在 9.1 生成。Statements 的"all formal content … kernel-certified under Rocq 9.3.0"对**投稿所依赖的制品面不成立**,且与同段自述"Main CI 钉 9.1、9.3 换基在途"自相矛盾——同一句话里既有"kernel-certified under 9.3.0"又有"rebase in transit",这是投稿版新增内容中**最需要修正的表述**。
   - "9.1 漏洞面不存在于 9.3,故本文结果不受该族影响"的推理对 9.1 认证的制品无效:按论文自己的失效模式矩阵(partA.tex:176-183),guard 族(72703/72704/72705)在 9.1 上"无机械排除闸";要援引 9.3 的免疫性,必须先交付 9.3 上的重认证,而这正是"in transit"未完成的部分。
   - 该错位同时伤及复现叙事:复现手册 M3(f) 已登记"三项判据绑定 9.1 的 coqchk 输出语义,升级后行为未实测·open"——Statements 的 9.3 断言与该登记直接冲突。

### 2.4 冻结面之外的承重注册与归档缺口

**【论文已声明】** 投稿版正文多处引用**冻结面之后**的注册批与树状态:#R195(`piu1930_domface_negative`,400 行)、#R196/#R197(`piu_zz_ec_mu_cond`/`piu_zz_mu_assembly`)、#R199/#R200(`NsepBudgetExhaustion.v`/`NsepBudgetVerify.v`,run #318)、W1–W6 批、μ₀_cos 对数反转封闭式(`rocq-pi-leibniz` 仓库 cos 引擎件 `PiMu0Cos.v`,commit 1706a1d5;云认证 run #33)、`order.txt` 973 行(#R221 基)/1,019 件 Live `.v`(partB.tex:111、143、145、175;partC.tex:229、241、247);并自述这些是"post-freeze extension-surface update,不计入登记账"(partA.tex:117 "changes none of the main text's count registrations";partB.tex:175 "post-freeze extension-surface update after the frozen baseline `16c2a12`, not counted in this paper's registration tally under the \S 1.4 extension accounting",两句均本会话 grep 逐字命中)。

**【评审人推断·库勘察交叉】** 上述件在**冻结树内均不存在**:
- `five_constants.md` §14 实测:`piu1930_domface_negative.v`、`piu_zz_ec_mu_cond.v`、`piu_zz_mu_assembly.v`、`piu_zz_e_carrier.v`、`piu_zz_cage_constants.v` 五件在冻结树**缺席**(其内容位为头注申报/其他件承载);
- `main_survey.md` R4 实测:`NsepBudgetExhaustion.v` 不在冻结树,唯一出现处是 `tlw1703_uacm_combo_unconditional.v:5` 的**注释**("断链引用");`NsepBudgetVerify` 全树零命中;冻结 `order.txt` 819 行(本会话 `wc -l` 复核一致);
- **μ₀_cos 对数反转封闭式**(partB.tex:143,本会话逐字核读):主库增长律 b^{O(b)} 的"窗口级方向"改进——`rocq-pi-leibniz` 的 `PiMu0Cos.v`(commit 1706a1d5;per-q 无条件;零公理)把窗口级搜索预算从线性反演 S(⌈5/eps⌉) 降至**对数反演 S(4+⌈log₂(8/eps)⌉)**;数值锚(精确有理算术,vm_compute 转录+独立镜像复算双证):22/7 命中级 **13**(Leibniz 路线同级预算 1977)、355/113 命中级 **25**(旧路线 9,371,572);认证史:早期受挫——#30 两连取消属并发组级联、#31(head 3d00d8dc)**两度被作者取消**,现由 **run #33(head 839ae588,2026-10-28,whole-tree coqchk 通过)** 承载该件云认证;论文自注"post-freeze extension-surface update;不计入 §1.4 登记账"。本会话实测:`grep PiMu0Cos order.txt` 与 `find -iname "*Mu0Cos*"` 对冻结树**零命中**——与上述各件同属"冻结面外承重件",且其命中级账(13/25)恰与 §一.4 的 N\*=1582/7,497,258 形成跨代对照,承重位与 §二.4 清单内各件及 Q4/Q12 完全同类;
- 冻结树内的 ZZ 线实况(five_constants §10-11、§16):`piu1932_uncond_zz.v` 定理**仍以率面 μ 证书为显式前提**(件头自述"唯一前提=率面 μ 证书";"uncond"名实=消灭 cwin 死槽);`piu_zz_tau_enclosure.v` 携 **PNT 两条 Hypothesis**(:1214/:1216);`piu_zz_poincare_engine.v` 主定理 `piu_zz_poincare_rootlimit` 语句面**注释冻结**;`piu_zz_padic_clearing.v` 留接续面(A_j 本体、Lemma 2 结论本体、式(10)、π 系数入口)。

**结论:投稿版 §7.1 第 2 项/§7 的"一致型无条件闭合、μ(π) ≤ 8"叙事,其全部承重件都落在归档制品(止于冻结面)之外**,第三方无法从 Zenodo 归档、GitHub tag 或本地重建树核验这些注册与运行;μ₀_cos 段(partB.tex:143)是同一模式的另一实例——`PiMu0Cos.v` 与 run #33 同样落在冻结面与 Zenodo 23717748 之外(见 Q15);且"Rocq 9.3 内核下 coqchk 认证"的说法与冻结面 9.1-only 的实测相冲突。评审人要求作者提交该批注册的树锚、run id 与 coqchk 日志,或将其从投稿文本中降格为"在研登记"(见 Q4、Q12、Q15)。这不是指控:论文对冻结/延伸面的会计纪律(§1.4"不计入登记账")是自觉的;问题在于**正文叙述强度**("hence the unconditional uniform-type strong irrationality of π",partC.tex:229)超出了它自己的会计纪律。

### 2.5 .vo 归档缺口与复现不对称

**【论文已声明】** 复现分层:A 侧 23 符号面可按"最小审计脚本包"本地复现;**延伸面 22 件凭证由 CI 认证面承载、`.vo` 未在本地取得,完整本地重建须自源码重编**,"第三方独立复现对主张面主定理面完整、对延伸面不完整,此不对称在此明示"(partA.tex:117;复现手册 M2 步骤 0;§8 项 (ix))。

**【已实测工程事实·按任务直接引用】** ①git 树内零 `.vo` 二进制(`.gitignore` 忽略 `*.vo`;main_survey R3;本地无 .git 无法重验上游跟踪状态,勘察已声明);②Zenodo 23717748 仅含 **9 件 `.vo`**(对应 v4 证据表 17 行中标注"本地"的 9 行,paper_v4.md 附录 A"凭证源列说明";其余 11 件只有临时 CI 工件);③`order.txt` 实测 **819 行 = 论文冻结面口径**(本会话 `wc -l` 复核一致)。

**【本会话补充实测】** 本地重建树现有 10 件 `.vo`(S01–S10),时间戳与本会话 9.3 编译波一致——即它们是**评审侧试编译的残渣,不是归档面内容**(main_survey R3 同判读;逐件时间戳核对见附录 #9)。②项因本环境无网络(Zenodo API 解析失败)未复跑,按给定事实引用。

**【评审人推断】** 对 JAR 的 artifact evaluation 期望而言,这一缺口是实质性的:17 行证据表中 8 行(11 件)的编译凭证只存在于 GitHub Actions 工件(平台策略过期,论文自己登记 run #195/#205/#208 的 coqchk-logs "有效期至 2027-01-04",复现手册 M2 ⑤),**永久归档里没有对应的可内核复核对象**;论文的补救路径("自源码重编")又受 2.3 的代际错位拖累(9.3 编不过冻结面,9.1 工具链长期可得性无保障——M3(f) 自登记)。建议:大修时要求作者补交(i) 22 件的 `.vo` 或逐 run coqchk 日志入 Zenodo,(ii) 9.1 工具链的容器化镜像或至少版本坐标+校验和(M3(f) 自己建议的方案)。

---

## 三、价值与意义评估

### 3.1 构造性数学维度

**【评审人推断·基于论文定位与文献坐标】**
- **断言层**:π 的强无理(逐点正距)在 Bishop 传统中对 √2、e 可构造证明;π 因超越性无代数整隙可依,需专门分析技术(论文 §1.1 的难度分层论证,partA.tex:68)。本文把 Niven 型路线在零公理 Set 层基底上逐项显式化,并以 `sigT` 交付逐有理数显式见证——这是把"经典论证的构造性内容"完整机器化的工作,数学新意主要在**交付形态**(全称形 + 逐点显式 Q 常数 + 零公理 Set 层基底的组合),而非数学引擎;论文对此的自觉(§1.1 加权段"实质是既有传统的构造化移植")应予肯定。
- **缺口定位**:与经典测度谱系的换算链"两端未闭"(上界端 Bexp 阶乘率;桥端 `lw5n_bnd_caliber` 只有标度关系无一致性,§7,partC.tex:216-225)——论文不主张换算,正确。论文谱系段记载的测度竞争链 Mahler(1953,42)→Mignotte(1974)→Chudnovsky(1982)→Rhin–Viola(1993)→Hata(1993,8.016)→Salikhov(2008,7.6063)→Zeilberger–Zudilin(2020,7.1032)→Bai(2026-09,7.10186)(partC.tex:212,记法从该行)与本文断言不交(审计日志 A8(b));"显式常数非构造"的对照(refs 13/30 的有效性由共同体评估)处理得当。
- **一致型问题**:见 §二.4 与 §四.1——若 20261103 收官批为真,本库将同时持有 α=8 档的一致型形式化(弱于 Bai 的 7.10186 但为构造性/机器验证);若不真或未归档,则该叙事必须撤回。这一悬而未决的内部张力是目前评估本文"构造性数学意义"的最大变量。

### 3.2 形式化验证维度

**【评审人推断】**
- **审计方法论是本文第二项实质贡献**:`Print Assumptions` 盲区(CVE-2020-37268)× coqchk 三判据承重结构 × 两道闸(结构检索 + 内核复核)× 失效模式三分矩阵(宇宙开关类 / 72714 工件级 / guard 逻辑缺陷类),并配判定实验(公开 PoC `ZeroEqOne.v`,sha256 在卷,rc=129 拒绝;partA.tex:158-187;审计日志 A6 判定实验段)。对"proof assistant 上的零公理声称应如何承重"这一问题,本文给出了当前文献中少见的细粒度答案,guard 族"无机械排除闸"的坦白尤佳。**代价**是暴露了承重面绑定 9.1 的脆弱性(2.3)。
- **两层口径(搜索层可求值/见证层可定义可提取但不可机算)及其三层成因实验**(§4.2,partB.tex:135;复现手册 M4)是关于"构造性见证的可提取性 ≠ 计算可求值性"的一组有教学价值的实证:Qed/Defined 提取字节级同一(549,297 字节 diff=0)、透明化实验(#301 快照面;π 见证层 3.5 秒归约到 1#60、内核见证层 >960 秒不可中断、第四道不透明门 `real_lt_eq_lt` @S02_CauchyComplete.v:2421/2461)、Q 层成本 n=3→39s、n=4→>280s 而真实 n_sel=24 远超 10¹⁵ 秒。这一节值得发表;建议作者把它整理为独立可引用的实验记录并归档实验脚本(见 Q13)。
- **工程生态位**:主张面 Apache-2.0 冻结 tag(远端推送+Zenodo 23717747/48 双归档);延伸面 `rocq-pi-leibniz` LGPL-2.1(Zenodo 23527295/23656983,opam 官方索引收录 opam#3884 合并,2026-10-20);上游 stdlib PR #313(逃逸窗引擎)/#316(π_L 顶点)均 open 未合并,stdlib 维护者转介 CoRN,CoRN 维护者 Lysxia 判定"自成一体、无需入库",最终格局=独立库+opam 索引(审计日志 A6 终局段)。**生态贡献真实但上游标准化未成**——论文把"标准化=潜在"写进了贡献声明(partA.tex:111),措辞与事实相称;opam 收录改善的是可及性而非标准库地位,论文对此的精确界定(partC.tex:286"两件必须区分")应予肯定。

### 3.3 谱系位置

**【论文已声明+评审人核对】**
- vs **openai/math PiExponent**(refs 30;审计日志 A5(e)、A8(a)):最近邻。三项形态差异(最终式 ∃Q vs 本文全称无阈值;Prop 存在阈值 vs Set 层 sigT 逐点见证;mathlib 经典 Real.pi vs 零公理 Set 层)逐条可核;工作谱系时间线(本文工件仓首提 2026-09-28 早于该仓建仓 8 天;预印本公开 2026-10-10 晚于建仓 4 天)双侧登记且明示"不构成同断言优先权主张"。可靠性限定(未发布 AI 模型产物)与 Bai 同档,如实。
- vs **C-CoRN**:有构造性 π 定义(`CRpi_fast/slow`),无逐有理数分离定理;论文自登记"未直接检查该库,T5 二手注册"(partA.tex:74)——诚实,但作为 Coq 生态最近缘库,建议作者在修稿期做一次直接核对(见 Q10)。
- vs **AFP 级数判据**(Koutsoukou-Argyraki–Li–Paulson 2022,refs 33):方法层同族(级数判据的形式化)、基座与交付面两层分岔;系终稿补检发现的覆盖缺口(审计日志 A7 补批段,作者自我登记"此前检索零覆盖"),补录处理规范。
- vs **Bai 2026**(7.10186)/**Niedbala Giraudin 2026**(闭式律+最优性计算证据):经典强度上 Bai 蕴含本文逐点正距但常数存在性非构造;Giraudin 的筛选下界是"猜想级陈述非定理级"(partB.tex:173,本会话 grep 逐字命中;原稿误标 partC.tex:173,该行为空);论文两条都只作对照不占其成果,且对两文的 AI 使用披露(refs 13/30)处理了引用伦理。
- vs **Nuprl 22/7** 与 **Bishop √2**:强度阶梯的上下邻;证据级差见 §一.2。
- **结论**:本文在"π_geom 顶点 × Q 级显式正距 × Set 层 sigT 全称形 × 零公理 Set 层基底"四合取上的首例声称,就其登记的检索面(七渠道、130+ 轮、未覆盖面逐条登记)而言**可辩护**;这是"组合首例而非强度首例"的声称,论文自己已作此限定(审计日志 A8(d))。

---

## 四、评审关注点

1. **【一致型"未交付"与"已闭合"的文本冲突——最高优先级】** 摘要限制段:"the uniform bound for π is **not delivered**"(main.tex:30);强度段:"Once a constructive measure-route formalization lands, existing bridge lemmas upgrade our pointwise result to the uniform form (§7)"(main.tex:28)。而 §7(partC.tex:229)与 §7.1 第 2 项(partC.tex:241)却登记:"率面 μ 证书槽已获无条件闭合:六前提全部无条件闭合,装配顶件 `piu1932_uncond_zz` 在 Rocq 9.3 内核下通过无歧义 coqchk 认证(Axioms: <none>),给出机器验证的有效 μ(π) ≤ 8 上界链——**hence the unconditional uniform-type strong irrationality of π**"。中文稿摘要更直接写"π 的一致型下界**已交付**(20261103 收官登记)"。三处互相矛盾;且该批承重件全部在冻结面之外(§二.4)、9.3 认证与冻结面 9.1-only 冲突(§二.3)。**评审人判断:投稿版在"v4 之后"混入了两个不同代际的文本层,摘要/limitation 层与 §7.1 收官层未同步。** 必须二选一并全文对齐(问题清单 Q1/Q4/Q12)。
2. **【点态非一致的申明本身合格】** 强度阶梯、Skolem 函数不受一致界支配的结构性理由、√2 序列 2⁻ᵇ 衰减 vs Bishop 1/(3b²) 的量化对照(附录 B,partC.tex:474)——这部分是清晰的;若 Q1 按"未交付"口径对齐,建议把该量化对照升入正文更显眼处。
3. **【见证层不可机算的三层实验】** 内容扎实(§3.2),但全部为作者侧实验:透明化实验挂在"#301 快照实验面"(post-freeze),成本测量无第三方复算记录;"Timeout 机制未触发、卡在不可中断深归约"的判定只有作者描述。建议归档实验脚本与环境快照(Q13)。
4. **【复现不对称性】** 论文自登记完整(partA.tex:117),但组合后果严峻:延伸面 22 件无永久 `.vo`(§二.5)+ 冻结面 9.3 编译失败(§二.3)+ 9.1 工具链长期可得性缺口(M3(f))= 年际尺度上,归档制品可能既不能快速复核也不能原样重建。这不是诚信问题而是**归档完备性问题**,JAR 应按大修要求补救。
5. **【自证 CI】** 认证链单一来源:自托管 Windows runner、播种步引用维护者本地路径(复现手册 M2 ③自登记)、并发取消制、多 run 作者手停(#30/#31/#34,partB.tex:143 与手册 M1)、**一次转录讹误的实证**(run #291 先被转录为"全绿 848 模块",后 API 勘正为 cancelled 并撤销——审计日志 A1 20261026 增补段)、gate2 banner 硬钉 "Welcome to Chicken 9.1.0"(main_survey §1.3)。论文对"作者侧工程记录 vs 独立可核验面"的分列(partA.tex:117)降低了风险,但评审人仍应把 CI 结论视为**作者自述级证据**,与源件级证据(可独立核验)区别对待。
6. **【冻结面 9.1-only vs Statements 9.3.0】** 见 §二.3。重复要点:同一 Statements 段落内"kernel-certified under 9.3.0"与"rebase in transit / Main CI pins 9.1"并存,且与本会话 9.3 编译失败实测冲突。这是必须在修稿中解决的问题,不属于"可容忍的措辞含糊"。
7. **【术语密度与可读性】** Glossary 19 条(partA.tex 长表数据行 :37–55,共 19 条;本会话 awk 计数含 2 表头行共 21 行,原稿"14 条"有误)+ 正文自创术语(窗口界/窗口级/窗口距、逃逸引理、判据框架、顶点标签、守卫/无条件形、组合定理、分离窗口级 μ₀……);§1.1–§1.3、§4.2–§4.3、§5.7 多个段落单段上千词、内嵌多层括注与自指修订记录("20261030 增补""更正之更正"等)。论文自辩为"各节局部自足性的设计选择"(审计日志 A1.4),并做了 AI 味词面审查(A7 第 4 批 49 发)。**评审人推断**:JAR 读者群体可承受术语,但当前密度已影响论证主线可追踪性;建议大修要求作者(a)把代际修订史移入附录,(b)将 §1.4/§1.5 的工程登记压缩为表+指针,(c)对每个自创术语在 Glossary 给一行"文献对应物/无"。
8. **【cover-letter TODO 与投稿包完整性】** cover-letter.md:3 "[TODO: date of submission]"、:42 "[TODO: suggested-reviewer list]" 均空;main.tex:33 留有 "%% TODO sn-jnl 换装点" 注释;refs.tex 条目 15 含中文标题(需 CJK 排版,refs.tex:57-66 自登记未决);附录 A/M-坐标表整体外移至《材料索引》,而该文件**不在投稿包内**——正文大量"line numbers in the Materials Index M-coordinate table"引用落空。投稿前必须:补 TODO、定 refs15 形态、随稿提交补充材料或把关键坐标收回正文。
9. **【P9 姊妹篇骨架】** `投稿版-JAR-P9/` 仅有骨架:partA/B/C.tex 各 355 字节空占位、refs.tex 379 字节零条目、摘要/关键词零填装(main.tex:56-64);投稿清单自登记"全稿英文化未做"(投稿清单.md 第 1 项)。两处**跨篇不一致**须在两稿同时处理前修复:(i) P9 cover-letter 骨架把论文 A 主张面描述为"π_L 顶点·rocq-pi-leibniz 延伸面·L5 无条件形"(cover-letter-骨架.md:45),与论文 A 自己的顶点分层(主张面=π_geom 顶点在册树;π_L 延伸面**不计入**,partC.tex:188 表、partA.tex:74)相抵触;(ii) P9 摘要沿用"662 在册模块"旧口径(终版摘要),而冻结面实际 819 行(本会话 wc -l)、主仓现势 846/964 行(手册 M1)——README 同病(main_survey R1)。另:论文 A 把 P9 以预印本证据级引用(refs 15"self-citation;preprint form"),并将 Nuprl 22/7 登记自包含化以免脱钩——处理得当。
10. **【AI 披露】** 已声明(Statements,partC.tex:307):生成式 AI 用于"文献调研整理、代码与文本润色",已文档化,作者负责,不列为作者;并以同口径披露 Bai/PiExponent 的 AI 使用。**评审人推断**:措辞合规但过泛;考虑到本稿的注册批次/审计日志/检索日志体量高度依赖自动化流程,建议按 Springer 政策细化为阶段清单(哪些代码、哪些审计脚本、哪些正文段落),并明确"Coq 证明体未经 AI 生成"或如实披露(见 Q11)。论文自己的 A7 第 4 批("AI 味词面判别"49 发)表明作者对此有意识,这是一个加分点。
11. **【CVE 意识与 coqchk 承重】** §1.5 的两道闸+三分矩阵+判定实验是模范级的威胁建模(§3.2);保留意见:(i) 结构闸的 grep 面以"1,009 文件 @HEAD 17e6ad7"(partA.tex:167)执行——那是冻结后 head,非归档冻结面;(ii) 三判据语义绑定 9.1(M3(f) 自登记 open),与 Statements 9.3 断言冲突;(iii) coqchk 承重的最终背书(run #195/#205/#225/#228 日志)只能以 CI 工件形式获得,存在过期风险。总体:这一节应**保留并在修稿中与 Q1/Q6 的口径统一**。
12. **【投稿版新增内容的其他核查记录】**(均正面):22/7/355/113 数值锚(§一.4)、两层口径与 Qed 反驳实验(partB.tex:135)、`ucreal_eq_*` 双桥的"逆模量对齐"技术分解(partC.tex:161)、上游终局登记(A6)、首例检索的未覆盖面披露(A7)、Nuprl/C-CoRN 二手证据降级登记(partA.tex:74)——这些内容使本稿在"证据纪律"维度显著高于平均水平。

---

## 五、向作者的问题清单(可核查;优先针对投稿版新增内容)

**Q1(最高优先)** 摘要"the uniform bound for π is not delivered"(main.tex:30)与 §7/§7.1"六前提无条件闭合、piu1932_uncond_zz 给出 μ(π)≤8、hence the unconditional uniform-type strong irrationality of π"(partC.tex:229、241)及中文稿"一致型下界已交付"互相矛盾。请明确:投稿版以哪一口径为准?若主张已闭合,请给出承载文件名、注册行、CI run id 与 coqchk 日志,并说明其所在的树/head 与归档 DOI 的关系;若不主张,请修订 §7/§7.1/中文稿相应段落。

**Q2** Statements 声称"all formal content … kernel-certified under Rocq 9.3.0"。评审实测:冻结 tag 树在 Rocq 9.3.0 下编译于 `S11_TP3B5.v:2665` 失败("Multiple Proof commands not supported";S01–S10 通过;该件在主定理 Require 闭包内,见《复现手册》M6(l))。请逐项回答:(a) 9.3.0 认证针对哪个树/head?(b) 是否存在 9.3 版式的 `.vo`(魔数非 90100)与对应 coqchk 日志?(c) 若无,是否同意将 Statements 改为 9.1.0 并删除"results … unaffected by that family"句,或补齐 9.3 重认证后再作此言?(d) 请提供 **9.1→9.3 全量编译差异清单**:评审侧试编按 order.txt 拓扑进行,于第 11 件 S11_TP3B5 失败即停(compile_closure.sh 首错即 break),复现手册 M6(l) 闭包内 S12 起的后续件均未测——请逐件说明 9.1→9.3 的全部不兼容面及对应修法,以防仅修 S11:2665-2666 双 `Proof.` 一处即声称"9.3 可编译"。

**Q3** Zenodo 23717748(冻结面永久归档)仅含 17 行证据表中 9 行的 `.vo`;其余 11 件与延伸面 22 件的凭证只在临时 CI 工件中。作者是否愿意(i)将逐 run coqchk 日志或全部 `.vo` 作为永久工件补入 Zenodo,(ii)同时按《复现手册》M3(f) 自己的建议归档 9.1 工具链镜像或版本坐标+校验和?

**Q4** "piu1932_uncond_zz 在 Rocq 9.3 内核下通过无歧义 coqchk 认证"对应的仓库、commit、run id 与日志?冻结树内该件(:818 #R194)定理仍以率面 μ 证书为显式函数前提(件头自述;库勘察 five_constants §10.2),六前提的无条件闭合文件(W1–W6 批)是否已入任何永久归档?若没有,请说明第三方如何核验此句。

**Q5** 冻结树内 `tlw1703_uacm_combo_unconditional.v:5` 的注释引用 `NsepBudgetExhaustion.v`,而该文件在冻结树缺席(主库勘察 R4"断链引用");正文(partB.tex:111)以 run #318 为其认证锚。请说明归档制品内的断链引用如何处置(补文件入冻结面?改注释?加 erratum?),并给出 #R199/#R200 的树锚。

**Q6** 内核件 `leibsep_q_kernel`(:5452)与守卫形(:298)无专属 `Print Assumptions` 语句;S10(12,497 行)仅 1 条 PA 且不覆盖旗舰链 π 常数;`u4a_budget_flip.v` 全件零出口审计行(库勘察 flagship_chain §三)。请提供:(a) 2026-10-12 单发 REPL 取证的归档产物公开坐标;(b) 上述三面在 coqchk 共享闭包中的逐条归属说明(哪个 run、哪个闭包规模覆盖哪些名字)。

**Q7** `order.txt` 计数口径在投稿包内多处漂移:冻结面 819(评审实测一致)→ 公开 main 841/844/846 → 964(KB70)→ §7.1 又引"973 行(#R221 基)/1,019 件"。投稿日应锁定哪一个作为基线?请在修稿中统一 §1.4、§8 基线段、§7.1 第 2 项的树面计数,并注明各计数的日期与 head。

**Q8** 搜索层"machine-evaluable"的范围:库内正面转录仅 q=3/1(μ₀=2)与小样例;22/7 在 1582 位级 `vm_compute` 未产出(《复现手册》M4(b))。是否同意在摘要(main.tex:12 "The search layer is machine-evaluable")加限定(如"for instances of practical scale the hit-level search has only been demonstrated off-machine")?

**Q9** Bexp~10²⁴¹、K∈[10²³⁹,10²⁴⁰)、N\*=1582/7,497,258 全为机外 T5 账。请提交产生这些数值的精确算术脚本(或其镜像仪器说明)入永久归档,使第三方可复算;并说明 355/113 扫描"定标 10⁶⁰ 逐级下截"的截断亏上界是如何证得的。

**Q10** Nuprl 22/7 与 C-CoRN 两条对照均为二手转录级(T5;审计日志 A7;partA.tex:74)。修稿期内作者是否愿意(i)直接联系 Nuprl 侧取得 `pi-irrational-instance` 可核坐标,(ii)对 C-CoRN 做一次直接源码核对并把 T5 升级或维持登记?如均不做,请在正文再缩一层措辞。

**Q11** AI 披露(partC.tex:307)目前覆盖"literature survey and organization; polishing of code and text"。请按阶段细化:注册批次的生成、审计脚本(gate1–gate7)、`Print Assumptions`/coqchk 日志的整理、正文写作各用了哪些工具;并明确声明 Coq 证明体与语句面是否全程无 AI 生成(或如实披露)。

**Q12** 冻结树内 ZZ 线的实况:`piu_zz_tau_enclosure.v` 携 PNT 两条 Hypothesis(:1214/:1216),`piu_zz_poincare_engine.v` 主判据语句面注释冻结,`piu_zz_padic_clearing.v` 留 A_j/Lemma 2/式(10)/π 系数入口四个接续面(库勘察 five_constants §16)。这与 §7.1 第 2 项"the whole chain is machine-verified (kernel coqchk, zero axioms)"如何相容?请给出在冻结面之后补齐这些缺口的逐件清单(文件名、W 批次、认证 run),或修正该句强度。

**Q13** cover-letter 两处 TODO(日期、建议审稿人)与 main.tex:33 的 sn-jnl TODO 注释、refs 条目 15 的 CJK 排版问题(refs.tex:57-66)请在修稿时解决;同时请说明《材料索引》与《审计日志》《复现手册》是否作为补充材料随稿提交(JAR 是否可获取)——正文大量坐标引用指向这些文件。

**Q14** 姊妹篇(P9)现处骨架态(partA/B/C 空占位;英文化未做),其 cover-letter 骨架把论文 A 主张面写为"π_L 顶点·延伸面"(cover-letter-骨架.md:45),与本文顶点分层相反;其"662 在册模块"口径已过时。两稿若先后投同一期刊,请说明:(a) 作者拟如何修复两稿互相矛盾的登记;(b) 是否按一稿一信披露兄弟篇关系(JAR 对 self-citation 与 salami 的政策)。

**Q15** μ₀_cos 对数反转封闭式(partB.tex:143,冻结面外承重件):`rocq-pi-leibniz` 的 `PiMu0Cos.v`(commit 1706a1d5;per-q 无条件;零公理)把窗口级搜索预算从线性反演 S(⌈5/eps⌉) 降至对数反演 S(4+⌈log₂(8/eps)⌉),数值锚 22/7 命中级 13(Leibniz 路线同级预算 1977)、355/113 命中级 25(旧路线 9,371,572);早期认证 #30/#31 两度被作者取消,现由 run #33(head 839ae588,2026-10-28)承载 whole-tree coqchk 云认证;论文自注为 post-freeze 扩展面、不计入 §1.4 登记账。该件在冻结树内零命中(本会话 grep/find 实测)。请给出:(a) `PiMu0Cos.v` 的精确树锚(commit 1706a1d5 所在分支/tag 及其注册行)与载有该 commit 的永久归档 DOI——延伸面 Zenodo 23527295 覆盖的 head 是否包含 1706a1d5;(b) run #33 的 coqchk 日志公开可取坐标;(c) 该件与 §7.1"973 行(#R221 基)/1,019 件 Live `.v`"口径的关系——`PiMu0Cos.v` 是否计入 1,019 件,μ₀_cos 的命中级账(13/25)与主库 `lw5n` 路线的登记账(N\*=1582/7,497,258)如何分列或合并?

---

## 附:本次会话实测记录(评审起草员执行)

| # | 命令 | 结果 |
|---|---|---|
| 1 | `/d/ComplexAnalysis/attn/opam93/default/bin/coqc.exe --version` | `The Rocq Prover, version 9.3.0 / compiled with OCaml 5.5.2` |
| 2 | 冻结树按 order.txt 序编译(`compile_closure.sh`,Rocq 9.3.0,2026-11-07 00:37 起) | `OK(1..10) S01_BaseRing.v … S10_KVQuantTrig.v`;`FAIL(11) S11_TP3B5.v`:`Error: Multiple "Proof" commands not supported.`(compile_log.txt;last_fail_11.out) |
| 3 | `sed -n '2660,2670p' S11_TP3B5.v` | :2665-2666 连续两个 `Proof.`(9.1 容忍、9.3 拒绝的语法面) |
| 4 | `wc -l ConstructiveWorld_Live/order.txt` | **819** 行(=论文冻结面口径) |
| 5 | `find ConstructiveWorld-Main -name "*.vo" \| wc -l` | **10**(全部为 S01–S10,与本次 9.3 编译波时间戳一致,系评审侧残渣;非归档面) |
| 6 | `wc -l Local/LW0LeibSeparation.v`;`grep -c "^Print Assumptions"`;`grep -c "Print Assumptions"` | **5723** 行;行首锚定 **61**;子串 **66**(与论文口径一致) |
| 7 | `grep -cE "^(Axiom|Parameter|Hypothesis|Conjecture|Admitted)" Local/LW0LeibSeparation.v` | 0(退出码 1;文本级事实,未编译) |
| 8 | `sed -n '5697,5702p' Local/LW0LeibSeparation.v` | 主定理语句面与论文 §5.2 转录逐字一致 |
| 9 | `find ConstructiveWorld-Main -name "*.vo" -exec ls -la {} \;`(定稿时复核) | 10 件时间戳:S01–S04 为 Nov 7 00:37、S05–S10 为 Nov 7 00:38,**全部落在 compile_log.txt 编译波窗口 00:37:31–00:38:52 内** → 与本次 9.3 试编译同源,系评审侧残渣、非归档面内容(时间戳判读复核成立) |
| 10 | `grep -n "conjecture-grade as stated by Niedbala Giraudin" part*.tex`(定稿时复核) | 唯一命中 partB.tex:173;partC.tex:173 为空行 → §三.3 坐标更正为 partB.tex:173 |
| 11 | `grep -n "post-freeze extension-surface update after the frozen baseline" part*.tex`(定稿时复核) | 唯一命中 partB.tex:175(#R195/400 行段);partC.tex:175 为空行 → §二.4 坐标更正为 partB.tex:175(partA.tex:117 "changes none of the main text's count registrations" 并列保留) |
| 12 | `grep -n "并列首要贡献" paper_v4.md`(定稿时复核) | 命中 :17(摘要)与 :41(定位段);:25 为 §1.1 标题段 → §一.1 坐标更正为 paper_v4.md:17、:41 |
| 13 | `awk` 计数 partA.tex Glossary 长表(partC 定稿时复核) | 数据行 partA.tex:37–55 共 **19** 条;含 2 表头行共 21 行以 `\\` 结尾 → §四.7 计数更正为 19 条 |
| 14 | `grep -rn "PiMu0Cos" order.txt`、`find ConstructiveWorld-Main -iname "*Mu0Cos*"`(定稿时复核) | 均零命中 → μ₀_cos 承重件不在冻结树(§二.4 增补、Q15 依据) |

**未能执行(如实声明)**:①Zenodo 23717748 内容清点(环境无网络,`curl zenodo.org` 域名解析失败)——"仅含 9 件 .vo"按任务给定工程事实引用,**待核验**;②CI run #195/#205/#225/#228/#318 日志回放(同因无网络)——**待核验**;③9.1 工具链复核(本环境仅装 9.3.0;冻结面 9.1 上的 coqchk 三判据未在本会话重放,其结论仍为作者侧 CI 记录)——**待核验**;④`Print Assumptions` 实际输出与 `Obj.magic` 计数(依赖编译产物,同上未重放;源件级 PA 布局已核对);⑤Q15 所涉 run #33 日志与延伸面归档对 commit 1706a1d5 的覆盖情况(本会话仅能确认冻结树内零命中,归档面内容无网络不可查)——**待核验**。

---

*定稿:修订定稿员(动态工作流子代理);2026-11-07;基于评审起草员起草稿逐条落实终审意见 8 条(坐标 3 处、覆盖增补+新增问题 1 处、数字更正 1 处、记号更正 1 处、问题清单边界补强 1 处、附录记录补全 1 处),复核确认项未改动正文。本稿为评审意见材料,供评审人参考与取舍;所有"评审人推断"以标注为准,不建议未经评审人本人复核即对外引用。*
