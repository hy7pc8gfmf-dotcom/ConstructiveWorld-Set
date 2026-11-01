# -*- coding: utf-8 -*-
"""提取每个 L<n> 令牌的精确前后文（±24 字符），聚类出替换规则所需的语法变体。
同时把 Variable/Context/Hypothesis 纳入声明索引，并对表格行取首格标识符。"""
import io, os, re, json
from collections import Counter, defaultdict

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
OUT = r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc'

lines = io.open(ORIG, encoding='utf-8', errors='replace').read().split('\n')
DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant|'
                  r'Variable|Context|Hypothesis)\s+([A-Za-z_][A-Za-z0-9_\']*)')
FIELD = re.compile(r'^\s{2,}([a-z_][A-Za-z0-9_\']*)\s*:')
decl_at = {}
for i, l in enumerate(lines, 1):
    d = DECL.match(l)
    if d: decl_at[i] = (d.group(1), d.group(2))
    else:
        f = FIELD.match(l)
        if f: decl_at[i] = ('field', f.group(1))

def near_decl(n, w=2):
    for d in (0,1,-1,2,-2):
        k = n + d
        if k in decl_at: return decl_at[k]
    return (None, None)

PAPERS = [('P1','论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2','论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3','论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4','论文4-资源受限收敛动力学与PCT-正式版.md')]
LNUM = re.compile(r'(?<![A-Za-z0-9_.])L(\d{3,7})(?!\d)')
IDENTALL = re.compile(r'`([A-Za-z_][A-Za-z0-9_\.]*)`')

samples = Counter()
detail = []
missing = []
for tag, fn in PAPERS:
    ls = io.open(os.path.join(BASE, fn), encoding='utf-8').read().split('\n')
    for i, l in enumerate(ls, 1):
        for m in LNUM.finditer(l):
            n = int(m.group(1))
            if n > 114222: continue
            s = max(0, m.start() - 26); e = min(len(l), m.end() + 22)
            frag = l[s:e]
            # 归一化：把数字替换为 #，便于聚类
            norm = re.sub(r'\d+', '#', frag)
            samples[norm] += 1
            kd, nm = near_decl(n)
            ids = IDENTALL.findall(l)
            detail.append({'paper': tag, 'pline': i, 'anchor': n, 'declkind': kd, 'decl': nm,
                           'row_ident': (ids[0] if (l.lstrip().startswith('|') and ids) else None),
                           'line_ident': (ids[0] if ids else None), 'frag': frag})
            if not kd and not (l.lstrip().startswith('|') and ids):
                missing.append((tag, i, n, l.strip()[:110]))

json.dump(detail, io.open(os.path.join(OUT, 'anchor_detail.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=1)

print('=' * 108)
print('L 令牌语法变体聚类（数字归一为 #；仅列出现 ≥3 次的形态）')
print('=' * 108)
tot = 0
for k, v in samples.most_common():
    if v < 3: break
    tot += v
    print('  ×%-4d %s' % (v, k))
print('  —— 前若干形态覆盖 %d / %d' % (tot, sum(samples.values())))
print()
print('=' * 108)
print('映射缺口（既无邻近声明名、也非表格带名行）：%d 条' % len(missing))
print('=' * 108)
for tag, i, n, s in missing[:28]:
    print('  %-4s P%-5d L%-8d %s' % (tag, i, n, s))
print()
print('表格行锚点（首格标识符可作名称）：%d' % sum(1 for d in detail if d['row_ident']))
