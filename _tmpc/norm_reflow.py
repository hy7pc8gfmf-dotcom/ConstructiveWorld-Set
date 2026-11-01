# -*- coding: utf-8 -*-
"""段落重排：合并被人工硬折行的散文行（仅限连续散文行且上一行不以「：」结尾）。"""
import io, os, re, sys

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
DRY = ('--apply' not in sys.argv)
P = [('P1', '论文1-构造性ML对齐统一形式化-正式版.md'),
     ('P2', '论文2-自由能原理与注意力Gibbs桥-正式版.md'),
     ('P3', '论文3-构造性柯西实数指数正性-正式版.md'),
     ('P4', '论文4-资源受限收敛动力学与PCT-正式版.md')]

def is_prose(s):
    if not s or len(s) < 20: return False
    if s[0] in '#|>': return False
    if re.match(r'^\s*[-*+] ', s) or re.match(r'^\d+[.)] ', s): return False
    if re.match(r'^\s{2,}', s): return False
    return True

for tag, fn in P:
    path = os.path.join(BASE, fn)
    with io.open(path, encoding='utf-8') as f:
        ls = f.read().split('\n')
    # 标记 fenced 区
    fence = [False] * len(ls)
    inf = False
    for i, l in enumerate(ls):
        if l.startswith('```'):
            inf = not inf; fence[i] = True; continue
        fence[i] = inf
    out = []
    i = 0; merged = 0
    while i < len(ls):
        cur = ls[i]
        if not fence[i] and is_prose(cur) and not cur.rstrip().endswith('：'):
            j = i + 1
            while (j < len(ls) and not fence[j] and is_prose(ls[j])
                   and not ls[j].lstrip().startswith('```')):
                cur = cur.rstrip() + ls[j].strip()
                merged += 1; j += 1
            out.append(cur); i = j
        else:
            out.append(cur); i += 1
    print('%-4s 合并 %d 行 → 段落 %d 行（%s）' % (tag, merged, len(out) - len(ls), 'DRY-RUN' if DRY else 'APPLIED'))
    if not DRY:
        with io.open(path, 'w', encoding='utf-8', newline='') as f:
            f.write('\n'.join(out))
