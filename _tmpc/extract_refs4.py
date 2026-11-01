# -*- coding: utf-8 -*-
"""论文引用最终核验 v4：区分「219 锚引用」与「模块相对行号引用」，分别核验。

判定：
 - 若 L<n> 前方 16 字符内出现 `<Name>.v` → 归为 MODULE 引用（在该模块文件中核验）
 - 否则归为 ANCHOR 引用（在 219 冻结主文件中核验）
核验档：
 VERIFIED   第 n 行是声明行，或行内标识符出现在 n±2
 STRUCT     第 n 行是「结构行」（Class/Record/Section 字段、Proof/Qed/缩进证明体），合法引用
 SUSPECT    其余（需人工看）
"""
import os, re, sys, json, glob
from pathlib import Path
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')
from audit_cw import strip_comments

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = [('P1','论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2','论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3','论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4','论文4-资源受限收敛动力学与PCT-正式版.md')]
ANCHOR = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
LIVE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\ConstructiveWorld_Live'

anch = open(ANCHOR, encoding='utf-8', errors='replace').read().split('\n')
anch_c = strip_comments('\n'.join(anch)).split('\n')
MODCACHE = {}
def modlines(name):
    if name in MODCACHE: return MODCACHE[name]
    for root in (LIVE, r'D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live'):
        p = os.path.join(root, name + '.v')
        if os.path.exists(p):
            ls = open(p, encoding='utf-8', errors='replace').read().split('\n')
            MODCACHE[name] = ls; return ls
    MODCACHE[name] = None; return None

DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant|Variable|'
                  r'Context|Hypothesis|Section|Module|End|Notation|Class|Record)\b')
STRUCT = re.compile(r'^\s*(?:\}|\{|Proof\.|Qed\.|Defined\.|intros?\b|apply\b|exact\b|rewrite\b|unfold\b|'
                    r'assert\b|split\b|induction\b|destruct\b|simpl\b|reflexivity\b|auto\b|-\s|\+\s|'
                    r'[\w\'\s]*:\s|\(|\)|\[|\]|\*|\(\*.*\*\)\s*$|-\s|=>|\||Local|#[^\n]*$)')
IDENT = re.compile(r'`([A-Za-z_][A-Za-z0-9_]*)`')
LNUM = re.compile(r'(?<![A-Za-z0-9_])L(\d{3,7})(?!\d)')
MODQ = re.compile(r'([A-Za-z_][A-Za-z0-9_]*\.v)\s*:\s*$')

def classify(line, pos, n):
    """返回 (kind, verdict, srcline)"""
    pre = line[max(0, pos - 20):pos]
    m = MODQ.search(pre)
    if m:
        name = m.group(1)[:-2]
        ls = modlines(name)
        if ls is None: return 'MODULE', 'NOFILE', ''
        if not (1 <= n <= len(ls)): return 'MODULE', 'OOR', ''
        src = ls[n - 1].strip()
        if DECL.match(ls[n - 1]): return 'MODULE', 'VERIFIED', src
        if STRUCT.match(ls[n - 1]): return 'MODULE', 'STRUCT', src
        return 'MODULE', 'SUSPECT', src
    # ANCHOR
    if not (1 <= n <= len(anch)): return 'ANCHOR', 'OOR', ''
    src = anch[n - 1].strip()
    if DECL.match(anch[n - 1]): return 'ANCHOR', 'VERIFIED', src
    # 行内标识符就近命中
    for base in [x for x in IDENT.findall(line) if not x.startswith('L')]:
        for d in (0, 1, -1, 2, -2):
            j = n - 1 + d
            if 0 <= j < len(anch_c) and re.search(r'(?<![\w.])' + re.escape(base) + r'(?![\w.])', anch_c[j]):
                return 'ANCHOR', 'VERIFIED', src
    if STRUCT.match(anch[n - 1]): return 'ANCHOR', 'STRUCT', src
    return 'ANCHOR', 'SUSPECT', src

tot = {}
for tag, fn in PAPERS:
    lines = open(os.path.join(BASE, fn), encoding='utf-8', errors='replace').read().split('\n')
    stats = {}; suspects = []
    for i, line in enumerate(lines, 1):
        for m in LNUM.finditer(line):
            n = int(m.group(1))
            kind, v, src = classify(line, m.start(), n)
            key = kind + '_' + v
            stats[key] = stats.get(key, 0) + 1
            if v == 'SUSPECT':
                suspects.append((i, n, kind, line.strip()[:100], src[:100]))
    tot[tag] = stats
    print('=' * 112)
    print('%s  %s' % (tag, fn))
    n_anc = sum(v for k, v in stats.items() if k.startswith('ANCHOR'))
    n_mod = sum(v for k, v in stats.items() if k.startswith('MODULE'))
    print('  引用令牌: %d （ANCHOR %d / MODULE %d）' % (n_anc + n_mod, n_anc, n_mod))
    for k in sorted(stats): print('    %-18s %d' % (k, stats[k]))
    if suspects:
        print('  ⚠ 残留 SUSPECT %d 条：' % len(suspects))
        for i, n, kind, s, src in suspects[:25]:
            print('     [%s] P%-5d L%-8d %s' % (kind, i, n, s[:92]))
    print()
Path(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc\refs4.json').write_text(json.dumps(tot, ensure_ascii=False, indent=1), encoding='utf-8')
