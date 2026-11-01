# -*- coding: utf-8 -*-
"""从 4 篇论文中抽取所有代码引用（标识符 + L行号），并按 219 锚原件核验位置。"""
import os, re, json, sys
from pathlib import Path
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')
from audit_cw import strip_comments

PAPERS = {
 'P1': r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\论文1-构造性ML对齐统一形式化-正式版.md',
 'P2': r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\论文2-自由能原理与注意力Gibbs桥-正式版.md',
 'P3': r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\论文3-构造性柯西实数指数正性-正式版.md',
 'P4': r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\论文4-资源受限收敛动力学与PCT-正式版.md',
}
ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'

orig_lines = open(ORIG, encoding='utf-8', errors='replace').read().split('\n')
# 去注释后的原文件（用于判定某行是否为声明行）
orig_code = strip_comments('\n'.join(orig_lines)).split('\n')

DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant|Variable|'
                  r'Context|Hypothesis|Section|Module|End)\b')

# 引用形态
TABLE = re.compile(r'\|\s*`([A-Za-z_][\w\'\.]*)`\s*\|[^|\n]*?\bL(\d+)\b')
INLINE = re.compile(r'`([A-Za-z_][\w\'\.]*)`\s*[（(]?\s*(?:L|行)\s*(\d+)')
ANY_L  = re.compile(r'\bL(\d{3,7})\b')

def extract(path):
    txt = open(path, encoding='utf-8', errors='replace').read()
    refs = []
    for i, line in enumerate(txt.split('\n'), 1):
        for m in TABLE.finditer(line):
            refs.append(('TABLE', m.group(1), int(m.group(2)), i, line.strip()[:150]))
        for m in INLINE.finditer(line):
            refs.append(('INLINE', m.group(1), int(m.group(2)), i, line.strip()[:150]))
    return refs

def judge(ident, ln, window=2):
    """返回 (verdict, 该行原文, 实际命中行)"""
    if not (1 <= ln <= len(orig_lines)):
        return 'OUT_OF_RANGE', '', None
    base = ident.split('.')[-1]
    # 在 ±window 内找标识符
    for d in range(0, window + 1):
        for s in ({0} if d == 0 else {d, -d}):
            j = ln - 1 + s
            if 0 <= j < len(orig_code) and re.search(r'\b' + re.escape(base) + r'\b', orig_code[j]):
                return ('EXACT' if d == 0 else 'NEAR±%d' % d), orig_lines[j].strip()[:130], j + 1
    # 全文找该标识符的真实位置
    hits = [k + 1 for k, l in enumerate(orig_code) if re.search(r'\b' + re.escape(base) + r'\b', l)]
    if not hits:
        return 'DELETED(未见)', '', None
    decl = [h for h in hits if DECL.match(orig_lines[h - 1] if h - 1 < len(orig_lines) else '')]
    return ('MISS (真值@L%d)' % (decl[0] if decl else hits[0])), '', (decl[0] if decl else hits[0])

allrefs = {}
summary = {}
for tag, p in PAPERS.items():
    refs = extract(p)
    allrefs[tag] = refs
    cnt = {}
    rows = []
    for kind, ident, ln, pline, ctx in refs:
        v, s, real = judge(ident, ln)
        cnt[v.split(' ')[0]] = cnt.get(v.split(' ')[0], 0) + 1
        rows.append((kind, ident, ln, v, real, pline, ctx))
    summary[tag] = cnt
    print('=' * 110)
    print('%s  %s' % (tag, os.path.basename(p)))
    print('  引用总数: %d' % len(refs))
    for k, v in sorted(cnt.items(), key=lambda x: -x[1]):
        print('    %-22s %d' % (k, v))
    print('-' * 110)
    bad = [r for r in rows if r[3].startswith('MISS') or r[3].startswith('OUT')]
    if bad:
        print('  ⚠ 未命中/越界清单（%d 条）：' % len(bad))
        for kind, ident, ln, v, real, pline, ctx in bad:
            print('    P%-5d L%-7d %-42s %s' % (pline, ln, ident[:42], v))
    else:
        print('  ✅ 全部命中')
    print()
Path(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc\refs.json').write_text(json.dumps({'summary': summary,
           'detail': {k: [list(x) for x in v] for k, v in allrefs.items()}}, ensure_ascii=False, indent=1), encoding='utf-8')
