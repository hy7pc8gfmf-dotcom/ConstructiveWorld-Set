# -*- coding: utf-8 -*-
"""论文 ↔ 219 锚 引用核验（v2：最近前置标识符配对，消除跨列/张冠李戴伪影）。

配对规则（互斥，按优先级）：
 R1 行内紧邻：   `ident` 之后 0~12 字符内出现 L<num>     → (ident, num)
 R2 表格单元格： | ... `ident` ... | ... L<num> ... |    → 取同一表格行内、L<num> 之前最近的 `ident`
 R3 裸行号 L<num>：无标识符可配 → 单独核验该行是否为声明行
"""
import os, re, sys, json
from pathlib import Path
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')
from audit_cw import strip_comments

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = {
 'P1': os.path.join(BASE, '论文1-构造性ML对齐统一形式化-正式版.md'),
 'P2': os.path.join(BASE, '论文2-自由能原理与注意力Gibbs桥-正式版.md'),
 'P3': os.path.join(BASE, '论文3-构造性柯西实数指数正性-正式版.md'),
 'P4': os.path.join(BASE, '论文4-资源受限收敛动力学与PCT-正式版.md'),
}
ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'

orig = open(ORIG, encoding='utf-8', errors='replace').read().split('\n')
code = strip_comments('\n'.join(orig)).split('\n')
DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant|Variable|'
                  r'Context|Hypothesis|Section|Module|End)\b')
IDENT = re.compile(r'`([A-Za-z_][A-Za-z0-9_]*)((?:\.[A-Za-z_][A-Za-z0-9_]*)*)`')
LNUM = re.compile(r'(?<![A-Za-z0-9_])L(\d{2,7})(?!\d)')

def pairs_in_line(line):
    """返回该行所有 (ident, num) 配对 + 未配对的裸行号。"""
    out = []
    used = set()
    # 收集标识符位置
    ids = [(m.start(), m.end(), m.group(1), m.group(1) + m.group(2)) for m in IDENT.finditer(line)]
    for m in LNUM.finditer(line):
        num = int(m.group(1))
        pos = m.start()
        cand = None
        # R1/R2：L 之前最近的标识符，且中间无其他标识符阻隔过远
        for s, e, base, full in ids:
            if e <= pos:
                gap = line[e:pos]
                # 允许其间只有标点/空格/中文/分隔符，且不含第二个 `…`
                if len(gap) <= 30 and '`' not in gap:
                    cand = (base, full, s)
        if cand:
            out.append((cand[0], cand[1], num, pos))
        else:
            out.append((None, None, num, pos))
    return out

def verdict(base, num, window=2):
    if not (1 <= num <= len(orig)):
        return 'OUT_OF_RANGE', ''
    for d in range(0, window + 1):
        for s in ({0} if d == 0 else {d, -d}):
            j = num - 1 + s
            if 0 <= j < len(code) and re.search(r'(?<![\w.])' + re.escape(base) + r'(?![\w.])', code[j]):
                return ('EXACT' if d == 0 else 'NEAR±%d' % d), orig[j].strip()[:120]
    hits = [k + 1 for k, l in enumerate(code)
            if re.search(r'(?<![\w.])' + re.escape(base) + r'(?![\w.])', l)]
    if not hits:
        return 'NOT_IN_219', ''
    decl = [h for h in hits if DECL.match(orig[h - 1])]
    return ('MISS(真值@L%d)' % (decl[0] if decl else hits[0])), ''

def bare(num, window=1):
    """裸行号：判定该行是否为声明行，或附近是否有声明。"""
    if not (1 <= num <= len(orig)):
        return 'OUT_OF_RANGE'
    if DECL.match(orig[num - 1]):
        return 'DECL_LINE'
    for d in range(1, window + 1):
        for s in {d, -d}:
            j = num - 1 + s
            if 0 <= j < len(orig) and DECL.match(orig[j]):
                return 'NEAR_DECL±%d' % d
    if orig[num - 1].strip() == '':
        return 'BLANK'
    return 'NON_DECL'

grand = {}
for tag, p in PAPERS.items():
    lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
    rows = []
    for i, line in enumerate(lines, 1):
        for base, full, num, pos in pairs_in_line(line):
            if base is None:
                rows.append((i, None, None, num, bare(num), 'BARE', line.strip()[:120]))
            else:
                v, src = verdict(base, num)
                rows.append((i, base, full, num, v, 'PAIR', line.strip()[:120]))
    cnt = {}
    for r in rows:
        cnt[r[4].split('(')[0].split('±')[0]] = cnt.get(r[4].split('(')[0].split('±')[0], 0) + 1
    grand[tag] = (len(rows), cnt, rows)
    print('=' * 108)
    print('%s  %s   (引用令牌 %d 条)' % (tag, os.path.basename(p), len(rows)))
    for k, v in sorted(cnt.items(), key=lambda x: -x[1]):
        print('    %-18s %d' % (k, v))
    bad = [r for r in rows if r[4] in ('OUT_OF_RANGE', 'NON_DECL') or r[4].startswith('MISS')]
    print('    需人工复核: %d' % len(bad))
    for r in bad:
        print('      P%-5d %-38s L%-8d %-24s' % (r[0], (r[1] or '(裸)')[:38], r[3], r[4]))
    print()

Path(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc\refs2.json').write_text(json.dumps({t: [[r[0], r[1], r[2], r[3], r[4], r[5], r[6]] for r in g[2]] for t, g in grand.items()}, ensure_ascii=False, indent=1), encoding='utf-8')
