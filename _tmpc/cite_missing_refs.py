# -*- coding: utf-8 -*-
"""为新增文献补正文引用点（幂等 + 计数断言）。"""
import io, os, sys

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
P1 = '论文1-构造性ML对齐统一形式化-正式版.md'
P2 = '论文2-自由能原理与注意力Gibbs桥-正式版.md'
P3 = '论文3-构造性柯西实数指数正性-正式版.md'
P4 = '论文4-资源受限收敛动力学与PCT-正式版.md'

REPS = [
# ---- 论文1 ----
(P1, "即标准 DPO 的 Bradley-Terry 形式",
     "即标准 DPO 的 Bradley-Terry 形式[31]（RLHF 侧以偏好微调语言模型的早期工作见[39]）", 1),
(P1, "（Rocq 9.1 以 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 存留，标准库文档核对（2026-09-03））",
     "（Rocq 9.1 以 `Stdlib.Reals.Cauchy.ConstructiveCauchyReals` 存留，标准库文档核对（2026-09-03）；形式化实数分析的库间综述见[34]）", 1),
(P1, "`Mathlib.InformationTheory.KullbackLeibler` [14]：在一般测度上定义 KL 散度",
     "`Mathlib.InformationTheory.KullbackLeibler` [14]（Mathlib 概率/熵/KL 形式化的权威记述见[38]）：在一般测度上定义 KL 散度", 1),

# ---- 论文2 ----
(P2, "（表中“无”指按可检索文献与库文档，该主题未进入其形式化范围；本表只对照主题覆盖，不断言他人的内部细节。）",
     "（表中“无”指按可检索文献与库文档，该主题未进入其形式化范围；本表只对照主题覆盖，不断言他人的内部细节。）\n\n**经典背景（本表之外的计量/不等式来源）**：KL 散度的原始文献见[40]，把最小判别信息问题表述为分布到凸集上的 I-投影见[41]（本文 §8.7 的投影主定理与 §9.1 的自由能–KL 分解共享该构造）；TV 与 KL 的两条标准传递为 Pinsker[39] 的 `δ ≤ √(½·KL)` 与 Bretagnolle–Huber[38] 的 `δ ≤ √(1 − e^{−KL})`——后者与本文 §5.5 的 `δ* = e^{−2Δ/T}` 及 `(1 − e^{−2Δ/T})ⁿ` 形态同构，是 §10.2 所述 KL→TV 缺口在经典侧的两条可选路线（前者含常数 2 限制，后者无）；形式化实数分析的库间综述见[43]。", 1),

# ---- 论文3 ----
(P3, "**与 C-CoRN 的 Setoid 代数设计对比**：",
     "**库间定位的对照口径（补充）**：形式化实数分析的库间综述见[30]；KL 与 I-投影的经典文献见[31][32]（本文 §10 第二定律定量化的 Gibbs/KL 腿以逐 eps 形消费该不等式族）；Mathlib 概率与熵/KL 形式化的权威记述见[33]；构造性代数中序域、离散域与局部环的处理口径见[29]。\n\n**与 C-CoRN 的 Setoid 代数设计对比**：", 1),

# ---- 论文4 ----
(P4, "- **Coquelicot [3] / MathComp-Analysis [4] / C-CoRN [2]**：经典或半构造性分析库，提供完备性、度量空间与不动点机制；与本文的关系正面比较于 §2.5。",
     "- **Coquelicot [3] / MathComp-Analysis [4] / C-CoRN [2]**：经典或半构造性分析库，提供完备性、度量空间与不动点机制；与本文的关系正面比较于 §2.5。形式化实数分析的库间综述见[10]。", 1),
(P4, "；本文 §4.8 的闭式预算与该类复杂度界在构造性接口下对应。",
     "；本文 §4.8 的闭式预算与该类复杂度界在构造性接口下对应。形式化侧的相邻工作另见：一阶优化算法收敛率的 Lean 4 形式化[12]与优化的经验证归约[13]（均属经典逻辑路线，与本文的构造性接口不同层）。", 1),
]

ok = True
for fn, old, new, exp in REPS:
    p = os.path.join(BASE, fn)
    txt = io.open(p, encoding='utf-8').read()
    n = txt.count(old)
    if n != exp:
        print('✗ [%s] 计数不符（期望 %d 实测 %d）: %s' % (fn[:14], exp, n, old[:70]))
        ok = False
        continue
    io.open(p, 'w', encoding='utf-8', newline='').write(txt.replace(old, new))
    print('✓ [%s] %s' % (fn[:14], old[:70]))

print('\n判定：', 'PASS' if ok else 'FAIL（未全写盘）')
