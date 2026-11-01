# -*- coding: utf-8 -*-
"""① 严格判定硬折行（连续两行皆为散文）；② 修复已确认缺陷。"""
import io, os, re

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
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

print('=' * 100)
print('① 硬折行严格判定（连续散文行对数）')
print('=' * 100)
for tag, fn in P:
    ls = io.open(os.path.join(BASE, fn), encoding='utf-8').read().split('\n')
    infence = False; pairs = []
    for i in range(len(ls) - 1):
        if ls[i].startswith('```'): infence = not infence; continue
        if infence: continue
        if is_prose(ls[i]) and is_prose(ls[i + 1]):
            pairs.append(i + 1)
    print('  %-4s %d 处｜样例 %s' % (tag, len(pairs), pairs[:10]))
    for n in pairs[:3]:
        print('        L%-5d %r' % (n, ls[n - 1][:88]))
        print('        L%-5d %r' % (n + 1, ls[n][:88]))

# ---------- ② 缺陷修复 ----------
FIX = [
 ("（）：", "："),
 ("（）", ""),
 ("**锚尾追加层块清单", "**末尾追加层块清单"),
 ("锚尾追加层（L112,463–114,222）", "末尾追加层（L112,463–114,222）"),
 ("本稿建议维持", "本文建议维持"),
 ("入该模块尾注台账。", "入该模块尾注备注。"),
 ("（在盘稿文面为据", "（以在盘稿文面为据"),
]
print()
print('=' * 100)
print('② 缺陷修复')
print('=' * 100)
for tag, fn in P:
    path = os.path.join(BASE, fn)
    with io.open(path, encoding='utf-8') as f:
        t = f.read()
    n = 0
    for old, new in FIX:
        c = t.count(old)
        if c:
            t = t.replace(old, new); n += c
    with io.open(path, 'w', encoding='utf-8', newline='') as f:
        f.write(t)
    with io.open(path, encoding='utf-8') as f:
        t2 = f.read()
    print('  %-4s 修复 %d 处 ｜ 回读 （） 残留 %d ｜ 锚尾 %d ｜ 台账 %d ｜ 本稿 %d'
          % (tag, n, t2.count('（）'), t2.count('锚尾'), t2.count('台账'), t2.count('本稿')))
