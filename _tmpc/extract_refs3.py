# -*- coding: utf-8 -*-
"""论文 ↔ 219 冻结锚 引用核验 v3（消除配对伪影）。

对每个 `L<n>` 令牌：
  1) 取出 219 锚第 n 行原文，判定是否「声明/定义类行」；
  2) 收集同一论文行内全部反引号标识符，逐一在 n±2 内检索；
  3) 分档：
     VERIFIED   —— 至少一个行内标识符出现在 n±2，且第 n 行为声明行
     NEAR_DECL  —— 行内标识符出现在 n±2，但第 n 行不是声明行（多为 Qed/续行，合法）
     DECL_ONLY  —— 第 n 行是声明行，但行内标识符未在 n±2 命中（表格第二格/命名空间格，需人工确认语义）
     SUSPECT    —— 既无标识符命中、第 n 行也非声明行（真实疑似失效引用）
     OOR        —— 超出 219 行域（引用他文件，如 220 合并稿）
"""
import os, re, sys, json
from pathlib import Path
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')
from audit_cw import strip_comments

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = {
 'P1': '论文1-构造性ML对齐统一形式化-正式版.md',
 'P2': '论文2-自由能原理与注意力Gibbs桥-正式版.md',
 'P3': '论文3-构造性柯西实数指数正性-正式版.md',
 'P4': '论文4-资源受限收敛动力学与PCT-正式版.md',
}
ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
orig = open(ORIG, encoding='utf-8', errors='replace').read().split('\n')
code = strip_comments('\n'.join(orig)).split('\n')
DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant|Variable|'
                  r'Context|Hypothesis|Section|Module|End|Notation)\b')
IDENT = re.compile(r'`([A-Za-z_][A-Za-z0-9_]*)`')
LNUM = re.compile(r'(?<![A-Za-z0-9_])L(\d{3,7})(?!\d)')

big = {}
for tag, fn in PAPERS.items():
    lines = open(os.path.join(BASE, fn), encoding='utf-8', errors='replace').read().split('\n')
    rows = []
    for i, line in enumerate(lines, 1):
        nums = [(int(m.group(1)), m.start()) for m in LNUM.finditer(line)]
        if not nums: continue
        # 该行全部标识符
        ids = [m.group(1) for m in IDENT.finditer(line)]
        ids = [x for x in ids if not x.startswith('L')]
        for n, pos in nums:
            if not (1 <= n <= len(orig)):
                rows.append((i, n, 'OOR', '', '', ids)); continue
            src = orig[n - 1].strip()
            isdecl = bool(DECL.match(orig[n - 1]))
            hit = None
            for base in ids:
                for d in (0, 1, -1, 2, -2):
                    j = n - 1 + d
                    if 0 <= j < len(code) and re.search(r'(?<![\w.])' + re.escape(base) + r'(?![\w.])', code[j]):
                        hit = (base, d); break
                if hit: break
            if hit and isdecl:      v = 'VERIFIED'
            elif hit:               v = 'NEAR_DECL'
            elif isdecl:            v = 'DECL_ONLY'
            else:                   v = 'SUSPECT'
            rows.append((i, n, v, src[:95], hit, ids))
    big[tag] = rows
    cnt = {}
    for r in rows: cnt[r[2]] = cnt.get(r[2], 0) + 1
    print('=' * 112)
    print('%s  %s' % (tag, fn))
    print('  L<n> 令牌总数: %d' % len(rows))
    for k in ('VERIFIED', 'NEAR_DECL', 'DECL_ONLY', 'SUSPECT', 'OOR'):
        if k in cnt: print('    %-10s %d' % (k, cnt[k]))
    sus = [r for r in rows if r[2] == 'SUSPECT']
    do  = [r for r in rows if r[2] == 'DECL_ONLY']
    if sus:
        print('  ⚠ SUSPECT（既非声明行、行内标识符也不在附近）%d 条：' % len(sus))
        for i, n, v, src, hit, ids in sus:
            print('     P%-5d L%-8d | %s' % (i, n, src[:88]))
            print('            %s' % ('L%d处: %s' % (n, orig[n-1].strip()[:88])))
    if do:
        print('  ○ DECL_ONLY（第 n 行是声明行，行内标识符未就近命中）%d 条 —— 多为命名空间格，需人工确认' % len(do))
        for i, n, v, src, hit, ids in do[:30]:
            print('     P%-5d L%-8d %s' % (i, n, src[:88]))
    print()
Path(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc\refs3.json').write_text(json.dumps({t: [list(r) for r in v] for t, v in big.items()}, ensure_ascii=False, indent=1), encoding='utf-8')
