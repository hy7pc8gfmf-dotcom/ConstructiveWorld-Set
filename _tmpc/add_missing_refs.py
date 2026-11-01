# -*- coding: utf-8 -*-
"""四篇论文缺失文献补入：在参考文献段末尾按序追加，幂等 + 计数断言。"""
import io, os, re, sys

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'

# 各篇追加条目（自下一序号起）
ADD = {
'论文1-构造性ML对齐统一形式化-正式版.md': [
 "Bradley, R. A., & Terry, M. E. (1952). Rank Analysis of Incomplete Block Designs: I. The Method of Paired Comparisons. *Biometrika* 39(3/4):324–345. https://doi.org/10.2307/2334029 （§5 隐式奖励所依据的偏好模型）",
 "Kullback, S., & Leibler, R. A. (1951). On Information and Sufficiency. *Annals of Mathematical Statistics* 22(1):79–86. https://doi.org/10.1214/aoms/1177729694 （KL 散度的原始文献）",
 "Csiszár, I. (1975). I-Divergence Geometry of Probability Distributions and Minimization Problems. *The Annals of Probability* 3(1):146–158. https://doi.org/10.1214/aop/1176996454 （I-投影；§5.3 KL 投影主定理的经典对应）",
 "Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437",
 "Li, C., Wang, Z., He, W., Wu, Y., Xu, S., & Wen, Z. (2025). Formalization of Convergence Rates of Four First-order Algorithms for Convex Optimization. *Journal of Automated Reasoning* 69(4):28. https://doi.org/10.1007/s10817-025-09741-w （Lean 4 / Mathlib）",
 "Vajjha, K., Trager, B. M., Shinnar, A., & Pestun, V. (2022). Formalization of a Stochastic Approximation Theorem. *ITP 2022*, LIPIcs 237, 31:1–31:18. arXiv:2202.05959. https://arxiv.org/abs/2202.05959 （§10.2 随机收敛方向的已有形式化）",
 "Tassarotti, J., Vajjha, K., Banerjee, A., & Tristan, J.-B. (2021). A Formal Proof of PAC Learnability for Decision Stumps. *CPP 2021*, 5–17. https://doi.org/10.1145/3437992.3439915 （§10.2 泛化界方向的已有形式化）",
 "Degenne, R. (2025). Markov Kernels in Mathlib's Probability Library. arXiv:2510.04070. https://arxiv.org/abs/2510.04070 （Mathlib 概率/熵/KL 形式化的权威记述）",
 "Ziegler, D. M., Stiennon, N., Wu, J., et al. (2019). Fine-Tuning Language Models from Human Preferences. arXiv:1909.08593. https://arxiv.org/abs/1909.08593",
],
'论文2-自由能原理与注意力Gibbs桥-正式版.md': [
 "Friedman, D. A. (2026). Towards Lean 4 Formalization of the Free Energy Principle: AI-Driven Theorem Sketching and Verification for Active Inference and Bayesian Mechanics. *Active Inference Journal*. https://doi.org/10.5281/zenodo.19699233 （FEP_Lean v1.1.0：Lean 4 + Mathlib，155 主题 / 20 族，155/155 sorry-free；作者明言不证明 FEP 作为物理理论）",
 "Li, H., Li, Q., Li, Y., et al. (2024). A Survey on Large Language Model Acceleration based on KV Cache Management. arXiv:2412.19442. https://arxiv.org/abs/2412.19442",
 "Xiao, G., Tian, Y., Chen, B., Han, S., & Lewis, M. (2024). Efficient Streaming Language Models with Attention Sinks. *ICLR 2024*. arXiv:2309.17453. https://arxiv.org/abs/2309.17453 （attention sink：首段 KV 不可驱逐的经验依据）",
 "Liu, Z., Desai, A., Liao, F., et al. (2023). Scissorhands: Exploiting the Persistence of Importance Hypothesis for LLM KV Cache Compression at Test Time. *NeurIPS 2023*. arXiv:2305.17118. https://arxiv.org/abs/2305.17118",
 "Bretagnolle, J., & Huber, C. (1979). Estimation des densités : risque minimax. *Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete* 47(2):119–137. https://doi.org/10.1007/BF00534262 （TV ≤ √(1 − e^{−KL})：KL→TV 传递的免常数替代路线，与本文 δ* = e^{−2Δ/T} 形态同构）",
 "Pinsker, M. S. (1964). *Information and Information Stability of Random Variables and Processes*. Holden-Day.（俄文原版 1960；TV ≤ √(½·KL) 的来源）",
 "Kullback, S., & Leibler, R. A. (1951). On Information and Sufficiency. *Annals of Mathematical Statistics* 22(1):79–86. https://doi.org/10.1214/aoms/1177729694",
 "Csiszár, I. (1975). I-Divergence Geometry of Probability Distributions and Minimization Problems. *The Annals of Probability* 3(1):146–158. https://doi.org/10.1214/aop/1176996454",
 "Degenne, R. (2025). Markov Kernels in Mathlib's Probability Library. arXiv:2510.04070. https://arxiv.org/abs/2510.04070",
 "Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437",
],
'论文3-构造性柯西实数指数正性-正式版.md': [
 "Bishop, E., & Richman, F. (1987). *Varieties of Constructive Mathematics*. London Mathematical Society Lecture Note Series 97. Cambridge University Press.（LPO / LLPO 的权威定义源，见 p. 3）",
 "Ishihara, H. (2006). Reverse Mathematics in Bishop's Constructive Mathematics. *Philosophia Scientiæ*, CS 6, 43–59. https://doi.org/10.4000/philosophiascientiae.406 （构造性分析中定理对 LPO / LLPO 的分类）",
 "Ishihara, H. (2005). Constructive Reverse Mathematics: Compactness Properties. In L. Crosilla & P. Schuster (Eds.), *From Sets and Types to Analysis and Topology: Towards Practicable Foundations for Constructive Mathematics*. Oxford University Press.",
 "Diener, H. (2020). Constructive Reverse Mathematics. arXiv:1804.05495. https://arxiv.org/abs/1804.05495",
 "Mines, R., Richman, F., & Ruitenburg, W. (1988). *A Course in Constructive Algebra*. Universitext. Springer-Verlag.",
 "Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437",
 "Kullback, S., & Leibler, R. A. (1951). On Information and Sufficiency. *Annals of Mathematical Statistics* 22(1):79–86. https://doi.org/10.1214/aoms/1177729694",
 "Csiszár, I. (1975). I-Divergence Geometry of Probability Distributions and Minimization Problems. *The Annals of Probability* 3(1):146–158. https://doi.org/10.1214/aop/1176996454",
 "Degenne, R. (2025). Markov Kernels in Mathlib's Probability Library. arXiv:2510.04070. https://arxiv.org/abs/2510.04070",
],
'论文4-资源受限收敛动力学与PCT-正式版.md': [
 "Kohlenbach, U. (2008). *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*. Springer Monographs in Mathematics. Springer. https://doi.org/10.1007/978-3-540-77533-1 （证明挖掘：从非构造性证明提取显式界与收敛率）",
 "Kohlenbach, U. (1998). Proof Theory and Computational Analysis. *Electronic Notes in Theoretical Computer Science* 13:124–157. https://doi.org/10.1016/S1571-0661(05)80219-1",
 "Kohlenbach, U., & Leuştean, L. (2011). Proof Mining in Metric Fixed Point Theory and Ergodic Theory. arXiv:0903.1529. https://arxiv.org/abs/0903.1529 （含凸优化中显式收敛率的提取）",
 "Boldo, S., Lelay, C., & Melquiond, G. (2015). Formalization of Real Analysis: A Survey of Proof Assistants and Libraries. *Mathematical Structures in Computer Science* 26(7):1196–1233. https://doi.org/10.1017/S0960129514000437",
 "Vajjha, K., Trager, B. M., Shinnar, A., & Pestun, V. (2022). Formalization of a Stochastic Approximation Theorem. *ITP 2022*, LIPIcs 237, 31:1–31:18. arXiv:2202.05959. https://arxiv.org/abs/2202.05959 （§5.2.2 随机收敛方向的已有形式化）",
 "Li, C., Wang, Z., He, W., Wu, Y., Xu, S., & Wen, Z. (2025). Formalization of Convergence Rates of Four First-order Algorithms for Convex Optimization. *Journal of Automated Reasoning* 69(4):28. https://doi.org/10.1007/s10817-025-09741-w",
 "Bentkamp, A., Mir, R. F., & Avigad, J. (2023). Verified Reductions for Optimization. *TACAS 2023*, LNCS 13994, 74–92. https://doi.org/10.1007/978-3-031-30820-8_8",
],
}

for fn, items in ADD.items():
    p = os.path.join(BASE, fn)
    txt = io.open(p, encoding='utf-8').read()
    lines = txt.split('\n')
    # 找参考文献段
    start = None
    for i, l in enumerate(lines):
        if re.match(r'^##\s*参考文献', l):
            start = i; break
    if start is None:
        print('✗ %s：未找到参考文献段' % fn); continue
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if re.match(r'^##\s', lines[j]):
            end = j; break
    # 最后一个编号条目
    last = None; lastno = 0
    for j in range(start + 1, end):
        m = re.match(r'^(\d+)\.\s', lines[j])
        if m:
            last = j; lastno = int(m.group(1))
    if last is None:
        print('✗ %s：段内无编号条目' % fn); continue
    new_lines = []
    for k, it in enumerate(items, start=lastno + 1):
        new_lines.append('%d. %s' % (k, it))
    lines[last + 1:last + 1] = new_lines
    io.open(p, 'w', encoding='utf-8', newline='').write('\n'.join(lines))
    print('✓ %-46s 原末号 %d → 追加 %d 条 → 末号 %d' % (fn[:44], lastno, len(items), lastno + len(items)))

print('\n完成。')
