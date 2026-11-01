# -*- coding: utf-8 -*-
"""量化行号锚点迁移工作量：区分「已有邻近标识符（可删行号）」与「仅行号（需解析名称）」。"""
import io, os, re
from collections import defaultdict

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = [('P1', '论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2', '论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3', '论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4', '论文4-资源受限收敛动力学与PCT-正式版.md')]

IDENT = re.compile(r'`([A-Za-z_][A-Za-z0-9_\.]*)`')
LNUM = re.compile(r'(?<![A-Za-z0-9_.])L(\d{3,7})(?!\d)')

tot = defaultdict(int)
uniq = set()
NULLNAME = []
TABLE = 0
for tag, fn in PAPERS:
    lines = io.open(os.path.join(BASE, fn), encoding='utf-8').read().split('\n')
    for i, l in enumerate(lines, 1):
        nums = list(LNUM.finditer(l))
        if not nums: continue
        ids = [m for m in IDENT.finditer(l)]
        for m in nums:
            n = int(m.group(1))
            if n > 114222: continue
            tot[tag + '_all'] += 1
            uniq.add(n)
            # 同行 L 之前 40 字符内是否有标识符
            pre = l[max(0, m.start() - 40):m.start()]
            has = bool(IDENT.search(pre)) or bool(re.search(r'`[^`]*$', pre))
            if has:
                tot[tag + '_named'] += 1
            else:
                tot[tag + '_bare'] += 1
                NULLNAME.append((tag, i, n, l.strip()[:120]))
            if l.lstrip().startswith('|'): TABLE += 1

print('=' * 98)
print('行号锚点迁移工作量')
print('=' * 98)
print('%-5s %-9s %-9s %-9s' % ('论文', '锚点总数', '已有邻近名', '仅行号'))
T = N = B = 0
for tag, _ in PAPERS:
    a, nm, b = tot[tag + '_all'], tot[tag + '_named'], tot[tag + '_bare']
    T += a; N += nm; B += b
    print('%-5s %-9d %-9d %-9d  (%.0f%% 可直接删除行号)' % (tag, a, nm, b, 100 * nm / max(a, 1)))
print('%-5s %-9d %-9d %-9d  (%.0f%%)' % ('合计', T, N, B, 100 * N / max(T, 1)))
print()
print('唯一锚点（去重后，即附录定位表行数）: %d' % len(uniq))
print('位于表格中的锚点: %d' % TABLE)
print()
print('=' * 98)
print('「仅行号、无邻近名」清单（需先解析名称，共 %d 条）' % len(NULLNAME))
print('=' * 98)
for tag, i, n, s in NULLNAME[:40]:
    print('  %-4s L%-5d L%-8d %s' % (tag, i, n, s))
