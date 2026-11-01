# -*- coding: utf-8 -*-
"""核验 CW219_split 的 S01–S15 分片是否为 219 单文件（ConstructiveWorld.v）的保序保真切分。

判定：
1. 各分片去掉头部 Require/注释头后，正文是否在原文件中按序出现（单调不减）；
2. 拼接去头正文 + 原文件残留段，是否行数守恒；
3. 输出每个分片的起始行号（累积偏移），供论文行号映射核验。
"""
import os, sys, re

ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
SPLIT = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\CW219_split'
LIVE  = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\ConstructiveWorld_Live'

SHARDS = ['S01_BaseRing','S02_CauchyComplete','S03_QExp','S04_RealExpLogConv',
          'S05_AlignmentGRPO','S06_DiffSamplingGibbs','S07_RealSetoidExpLog',
          'S08_RealMainlineDPO','S09_EntropyReal','S10_KVQuantTrig','S11_TP3B5',
          'S12_B5RecycleSF','S13_NLiveAudit','S14_B5BatchBlock','S15_TailFEPUp']

def read(p):
    return open(p, encoding='utf-8', errors='replace').read().split('\n')

orig = read(ORIG)
# 建索引：原文件中每个非空、非注释行的首次出现位置
idx = {}
for i, l in enumerate(orig):
    s = l.strip()
    if len(s) >= 25:
        idx.setdefault(s, []).append(i + 1)

print('原文件: %d 行' % len(orig))
print('=' * 100)
cum = 0
prev_end = 1
report = []
for sh in SHARDS:
    p = os.path.join(SPLIT, sh + '.v')
    if not os.path.exists(p):
        print('%-28s MISSING' % sh); continue
    ls = read(p)
    # 找正文起点：跳过文件头注释块与 Require/Import/Set/Open 行
    body_start = 0
    depth = 0
    for i, l in enumerate(ls):
        s = l.strip()
        if s.startswith('(*'): depth = 1
        if depth:
            if s.endswith('*):') or s.endswith('*)'): depth = 0
            continue
        if re.match(r'^(Require|Import|Export|From|Set |Open |Unset |Local |Global |Declare )', s):
            continue
        if s == '':
            continue
        body_start = i
        break
    # 取正文中若干"锚行"原文件定位
    anchors = []
    for j in range(body_start, len(ls)):
        s = ls[j].strip()
        if len(s) >= 30 and s in idx:
            anchors.append((j + 1, idx[s][0], s[:60]))
            if len(anchors) >= 5: break
    # 用第一个锚行确定起始
    if anchors:
        first_local, first_orig, sample = anchors[0]
        off = first_orig - first_local
    else:
        first_orig, off, sample = None, None, ''
    # 校验单调性：全部锚行 orig - local 应一致
    consistent = all(o - lo == off for lo, o, _ in anchors) if anchors else False
    report.append((sh, len(ls), off, consistent, sample, len(anchors)))
    print('%-28s 分片行=%-7d 推定Δ=%-8s 锚一致=%-5s 锚数=%d' % (sh, len(ls), off, consistent, len(anchors)))

print('=' * 100)
print('Δ 单调性检查（应为严格递增）：')
prev = -1
ok = True
for sh, n, off, c, s, na in report:
    flag = 'OK' if (off is not None and off >= prev) else '<<< 逆序/缺失'
    if off is None or off < prev: ok = False
    print('  %-28s Δ=%-8s %s' % (sh, off, flag))
    if off is not None: prev = off
print()
print('分片总行数 =', sum(r[1] for r in report), ' | 原文件 =', len(orig),
      ' | 差 =', sum(r[1] for r in report) - len(orig))
print('保序判定:', 'PASS' if ok else 'FAIL')

# 附带：Live 树同名分片与 Split 分片是否逐字节一致
print()
print('=' * 100)
print('Live 树 vs Split 树 分片逐字节比对（判定 219 锚在维护树中是否被改动）：')
same = diff = missing = 0
for sh in SHARDS:
    a = os.path.join(LIVE, sh + '.v'); b = os.path.join(SPLIT, sh + '.v')
    if not (os.path.exists(a) and os.path.exists(b)):
        missing += 1; print('  %-28s MISSING' % sh); continue
    ca = open(a, 'rb').read(); cb = open(b, 'rb').read()
    if ca == cb: same += 1; print('  %-28s SAME' % sh)
    else:
        diff += 1
        la = len(ca.split(b'\n')); lb = len(cb.split(b'\n'))
        print('  %-28s DIFF  Live=%d 行 / Split=%d 行  (+%d)' % (sh, la, lb, la - lb))
print('一致 %d / 相异 %d / 缺失 %d' % (same, diff, missing))
