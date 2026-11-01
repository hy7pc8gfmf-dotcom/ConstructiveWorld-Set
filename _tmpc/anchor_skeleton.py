# -*- coding: utf-8 -*-
"""规范化聚类：把每处 L 令牌的 ±22 字符窗口中的「标识符名」「数字」「反引号内容」掩码化后聚类，
得到真正的语法骨架；同时排除「模块相对行号」（形如 Xxx.v:L### 或 Xxx.v L###）。"""
import io, os, re
from collections import Counter

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = [('P1','论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2','论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3','论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4','论文4-资源受限收敛动力学与PCT-正式版.md')]
LNUM = re.compile(r'(?<![A-Za-z0-9_.])L(\d{3,7})(?!\d)')
MODREL = re.compile(r'[A-Za-z_][A-Za-z0-9_]*\.v\s*:\s*$|[A-Za-z_][A-Za-z0-9_]*\.v\s+$')

sk = Counter(); modrel = 0; total = 0
for tag, fn in PAPERS:
    ls = io.open(os.path.join(BASE, fn), encoding='utf-8').read().split('\n')
    for i, l in enumerate(ls, 1):
        for m in LNUM.finditer(l):
            n = int(m.group(1))
            if n > 114222: continue
            total += 1
            pre20 = l[max(0, m.start()-24):m.start()]
            if MODREL.search(pre20) or re.search(r'\.v\s*:?\s*$', pre20):
                modrel += 1
                continue
            s = max(0, m.start()-38); e = min(len(l), m.end()+30)
            frag = l[s:e]
            # 掩码：中文保留，标识符/数字/反引号内容 → ∅
            frag2 = re.sub(r'`[^`]*`', '`∅`', frag)
            frag2 = re.sub(r'[A-Za-z_][A-Za-z0-9_\.\']*', '∅', frag2)
            frag2 = re.sub(r'\d+', '#', frag2)
            frag2 = re.sub(r'∅(?:\s*∅)+', '∅', frag2)
            sk[frag2] += 1

print('=' * 106)
print('L 令牌语法骨架聚类（∅=标识符，#=数字）')
print('=' * 106)
print('  L 令牌总数 %d ；其中模块相对行号（.v:L###）%d ；219 锚点 %d' % (total, modrel, total - modrel))
print()
cum = 0
for k, v in sk.most_common(45):
    cum += v
    print('  ×%-4d │ %s' % (v, k))
print('  —— 以上覆盖 %d / %d 个 219 锚点' % (cum, total - modrel))
