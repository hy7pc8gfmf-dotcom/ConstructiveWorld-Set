# -*- coding: utf-8 -*-
"""代码级差异判定：剥除注释与空白后，维护树 S01–S15 与 219 冻结分片是否一致。
若代码面完全一致 → 差异纯属注释措辞（E201 提交级清洗），定理语句与标识符未变动。
"""
import os, re, sys, difflib
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')
from audit_cw import strip_comments, strip_strings

SPLIT = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\CW219_split'
LIVE  = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\ConstructiveWorld_Live'
SHARDS = ['S01_BaseRing','S02_CauchyComplete','S03_QExp','S04_RealExpLogConv',
          'S05_AlignmentGRPO','S06_DiffSamplingGibbs','S07_RealSetoidExpLog',
          'S08_RealMainlineDPO','S09_EntropyReal','S10_KVQuantTrig','S11_TP3B5',
          'S12_B5RecycleSF','S13_NLiveAudit','S14_B5BatchBlock','S15_TailFEPUp']

def code_only(path):
    raw = open(path, encoding='utf-8', errors='replace').read()
    c = strip_strings(strip_comments(raw))
    out = []
    for l in c.split('\n'):
        s = l.strip()
        if s: out.append(re.sub(r'\s+', ' ', s))
    return out

print('%-24s %-9s %-9s %-12s %-12s %s' % ('分片','Split代码行','Live代码行','净增','差异块','判定'))
print('-' * 100)
tot_ins = tot_del = 0
identical = 0
diffblocks = []
for sh in SHARDS:
    a = code_only(os.path.join(SPLIT, sh + '.v'))
    b = code_only(os.path.join(LIVE, sh + '.v'))
    if a == b:
        identical += 1
        print('%-24s %-9d %-9d %-12s %-12s %s' % (sh, len(a), len(b), '0', '0', 'CODE_IDENTICAL'))
        continue
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    ins = dele = 0; blocks = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal': continue
        blocks += 1
        if tag in ('insert', 'replace'): ins += j2 - j1
        if tag in ('delete', 'replace'): dele += i2 - i1
        if len(diffblocks) < 25:
            diffblocks.append((sh, tag, a[i1:i1+2], b[j1:j1+2]))
    tot_ins += ins; tot_del += dele
    print('%-24s %-9d %-9d %-12s %-12d %s' % (sh, len(a), len(b), '%+d' % (len(b)-len(a)),
          blocks, 'CODE_DIFF (+%d/-%d)' % (ins, dele)))
print('-' * 100)
print('代码面完全一致分片: %d / %d' % (identical, len(SHARDS)))
print('代码面总插入 %d 行 / 总删除 %d 行' % (tot_ins, tot_del))
print()
if diffblocks:
    print('=== 代码级差异明细（前 %d 处）===' % len(diffblocks))
    for sh, tag, aa, bb in diffblocks:
        print('[%s] %s' % (sh, tag.upper()))
        for x in aa: print('   - %s' % x[:130])
        for x in bb: print('   + %s' % x[:130])
