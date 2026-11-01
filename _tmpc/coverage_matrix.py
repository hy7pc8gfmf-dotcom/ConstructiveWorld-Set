# -*- coding: utf-8 -*-
"""模块 × 论文覆盖度矩阵：找出「代码已证、论文不提或淡淡而过」的资产。

口径：
 - 对每个模块，抽取其顶层声明标识符（Lemma/Theorem/Definition/Fixpoint/Instance/Class/Record/Inductive）
 - 对每篇论文，抽取全部反引号标识符 + .v 文件名提及
 - 覆盖判定：模块名被提及（任一篇）→ MENTIONED_MODULE
             模块内任一特性标识符被提及 → MENTIONED_IDENT
             两者皆无 → UNCLAIMED（论文零覆盖）
 - 对 UNCLAIMED 与低覆盖模块，报告其规模与「高价值信号」（定理名关键词）
"""
import os, re, sys, json, glob
from pathlib import Path
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')
from audit_cw import strip_comments, strip_strings

LIVE = r'D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live'
BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = {'P1': '论文1-构造性ML对齐统一形式化-正式版.md',
          'P2': '论文2-自由能原理与注意力Gibbs桥-正式版.md',
          'P3': '论文3-构造性柯西实数指数正性-正式版.md',
          'P4': '论文4-资源受限收敛动力学与PCT-正式版.md'}

# ---- 1. 每篇论文的提及集合 ----
paper_text = {}
paper_ids = {}
paper_mods = {}
ALL_IDS = set()
for tag, fn in PAPERS.items():
    txt = open(os.path.join(BASE, fn), encoding='utf-8', errors='replace').read()
    paper_text[tag] = txt
    ids = set(re.findall(r'`([A-Za-z_][A-Za-z0-9_.]*)`', txt))
    mods = set(re.findall(r'([A-Za-z_][A-Za-z0-9_]*\.v)\b', txt))
    paper_ids[tag] = ids
    paper_mods[tag] = mods
    ALL_IDS |= ids
UNION_IDS = ALL_IDS
UNION_MODS = set().union(*paper_mods.values())

# ---- 2. 每个模块的声明标识符 ----
DECL = re.compile(r'(?m)^[ \t]*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(?:Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|CoFixpoint|'
                  r'Instance|Inductive|CoInductive|Record|Class|Structure|Variant)\s+([A-Za-z_][A-Za-z0-9_\']*)')
mods = {}
for f in sorted(glob.glob(LIVE + '/*.v')):
    name = os.path.basename(f)[:-2]
    raw = open(f, encoding='utf-8', errors='replace').read()
    code = strip_strings(strip_comments(raw))
    ids = set(DECL.findall(code))
    mods[name] = {'lines': raw.count('\n') + 1, 'ids': ids, 'raw_len': len(raw)}

# ---- 3. 覆盖判定 ----
rows = []
for name, d in mods.items():
    hit_mod = name in UNION_MODS or (name + '.v') in UNION_MODS
    hit_ids = d['ids'] & UNION_IDS
    per = {}
    for tag in PAPERS:
        m = name in paper_mods[tag] or (name + '.v') in paper_mods[tag]
        i = len(d['ids'] & paper_ids[tag])
        per[tag] = ('M' if m else '-') + ('I%d' % i if i else '')
    if hit_mod and hit_ids:
        cls = 'A_MOD+IDS'
    elif hit_mod:
        cls = 'B_MOD_ONLY'
    elif hit_ids:
        cls = 'C_IDS_ONLY'
    else:
        cls = 'D_UNCLAIMED'
    rows.append({'name': name, 'lines': d['lines'], 'cls': cls,
                 'hit': len(hit_ids), 'per': per})

order = {'D_UNCLAIMED': 0, 'C_IDS_ONLY': 1, 'B_MOD_ONLY': 2, 'A_MOD+IDS': 3}
rows.sort(key=lambda r: (order[r['cls']], -r['lines']))

print('=' * 118)
print('论文覆盖度矩阵（246 模块）')
print('=' * 118)
from collections import Counter
c = Counter(r['cls'] for r in rows)
for k in ('A_MOD+IDS', 'B_MOD_ONLY', 'C_IDS_ONLY', 'D_UNCLAIMED'):
    sub = [r for r in rows if r['cls'] == k]
    print('%-13s 件=%-4d 行=%-8d' % (k, len(sub), sum(r['lines'] for r in sub)))
print()
print('D_UNCLAIMED 明细（论文零覆盖）：')
print('%-34s %-7s %s' % ('模块', '行数', 'P1/P2/P3/P4'))
for r in rows:
    if r['cls'] == 'D_UNCLAIMED':
        print('  %-32s %-7d %s' % (r['name'], r['lines'], [r['per'][t] for t in ('P1','P2','P3','P4')]))
print()
print('C_IDS_ONLY 明细（模块名未提，仅个别标识符被引）：')
print('%-34s %-7s %-6s %s' % ('模块', '行数', '命中', 'P1/P2/P3/P4'))
for r in rows:
    if r['cls'] == 'C_IDS_ONLY':
        print('  %-32s %-7d %-6d %s' % (r['name'], r['lines'], r['hit'], [r['per'][t] for t in ('P1','P2','P3','P4')]))
print()
print('B_MOD_ONLY 明细（模块名被提，无标识符被引）：')
for r in rows:
    if r['cls'] == 'B_MOD_ONLY':
        print('  %-32s %-7d %s' % (r['name'], r['lines'], [r['per'][t] for t in ('P1','P2','P3','P4')]))
Path(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc\coverage.json').write_text(json.dumps(rows, ensure_ascii=False, indent=1), encoding='utf-8')
