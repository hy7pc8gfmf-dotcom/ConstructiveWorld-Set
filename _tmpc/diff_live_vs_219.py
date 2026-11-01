# -*- coding: utf-8 -*-
"""量化 ConstructiveWorld_Live（维护树 HEAD）S01–S15 相对 219 冻结分片（CW219_split）的差异。
先剥掉两边的头部（注释 + Require/Import 区），只比对"正文"，
以判定：219 正文是否在维护树中逐字节未动。
"""
import os, re, difflib

SPLIT = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\CW219_split'
LIVE  = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\ConstructiveWorld_Live'

SHARDS = ['S01_BaseRing','S02_CauchyComplete','S03_QExp','S04_RealExpLogConv',
          'S05_AlignmentGRPO','S06_DiffSamplingGibbs','S07_RealSetoidExpLog',
          'S08_RealMainlineDPO','S09_EntropyReal','S10_KVQuantTrig','S11_TP3B5',
          'S12_B5RecycleSF','S13_NLiveAudit','S14_B5BatchBlock','S15_TailFEPUp']

HDRLINE = re.compile(r'^\s*(Require|Import|Export|From|Set |Unset |Open |Close |Declare )')

def body(ls):
    """返回 (起始下标, 前导备注行数)：跳过前导块注释与 Require/Import/Set/Open 段落及空行。"""
    i = 0; depth = 0
    while i < len(ls):
        s = ls[i].strip()
        if depth > 0:
            if '*)' in s: depth = 0
            i += 1; continue
        if s.startswith('(*'):
            if '*)' not in s[2:]: depth = 1
            i += 1; continue
        if s == '' or HDRLINE.match(s):
            i += 1; continue
        return i
    return len(ls)

def norm(ls):
    """归一：去行尾 CR，去首尾空行。"""
    out = [l.rstrip('\r') for l in ls]
    while out and out[0].strip() == '': out.pop(0)
    while out and out[-1].strip() == '': out.pop()
    return out

print('%-24s %-9s %-9s %-9s %-8s %-8s %s' % ('分片','Split总','Live总','Split正文','Live正文','净增','判定'))
print('-' * 105)
grand = {'ins': 0, 'del': 0, 'same': 0, 'diff_files': 0}
detail = []
for sh in SHARDS:
    ps = os.path.join(SPLIT, sh + '.v'); pl = os.path.join(LIVE, sh + '.v')
    ss = norm(body(open(ps, encoding='utf-8', errors='replace').read().split('\n'))
              and open(ps, encoding='utf-8', errors='replace').read().split('\n')
              [body(open(ps, encoding='utf-8', errors='replace').read().split('\n')):])
    ls_ = open(pl, encoding='utf-8', errors='replace').read().split('\n')
    ll = norm(ls_[body(ls_):])
    a = norm(ss); b = ll
    if a == b:
        print('%-24s %-9d %-9d %-9d %-8d %-8s %s' % (sh, len(open(ps,encoding='utf-8',errors='replace').read().split('\n'))-1,
              len(ls_)-1, len(a), len(b), '0', 'IDENTICAL'))
        grand['same'] += 1
    else:
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        ins = dele = 0
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'insert': ins += (j2 - j1)
            elif tag == 'delete': dele += (i2 - i1)
            elif tag == 'replace': ins += (j2 - j1); dele += (i2 - i1)
        grand['ins'] += ins; grand['del'] += dele; grand['diff_files'] += 1
        print('%-24s %-9d %-9d %-9d %-8d %-8s %s' % (sh, len(open(ps,encoding='utf-8',errors='replace').read().split('\n'))-1,
              len(ls_)-1, len(a), len(b), '%+d' % (len(b)-len(a)), 'DIFF (+%d/-%d)' % (ins, dele)))
        # 记录前 3 处差异
        n = 0
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag != 'equal' and n < 3:
                detail.append((sh, tag, i1+1, i2, j1+1, j2, a[i1:i1+2], b[j1:j1+2]))
                n += 1
print('-' * 105)
print('完全一致分片 %d / %d ；相异 %d ；总插入 %d 行 / 总删除 %d 行'
      % (grand['same'], len(SHARDS), grand['diff_files'], grand['ins'], grand['del']))
print()
print('=== 差异样本（每片最多 3 处，正文行号）===')
for sh, tag, i1, i2, j1, j2, aa, bb in detail[:40]:
    print('[%s] %s  Split L%d-%d -> Live L%d-%d' % (sh, tag.upper(), i1, i2, j1, j2))
    for x in aa[:2]: print('   - %s' % x[:120])
    for x in bb[:2]: print('   + %s' % x[:120])
