# -*- coding: utf-8 -*-
"""CW219_split / ConstructiveWorld_Live 的 S01–S15 分片 vs 219 单文件：
严格顺序匹配（greedy pointer），判定是否「保序 + 正文逐行保真」。
"""
import os, re

ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
SPLIT = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\CW219_split'
LIVE  = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\ConstructiveWorld_Live'

SHARDS = ['S01_BaseRing','S02_CauchyComplete','S03_QExp','S04_RealExpLogConv',
          'S05_AlignmentGRPO','S06_DiffSamplingGibbs','S07_RealSetoidExpLog',
          'S08_RealMainlineDPO','S09_EntropyReal','S10_KVQuantTrig','S11_TP3B5',
          'S12_B5RecycleSF','S13_NLiveAudit','S14_B5BatchBlock','S15_TailFEPUp']

HDR = re.compile(r'^(Require|Import|Export|From|Set |Unset |Open |Close |Declare |Local |Global |'
                 r'#[A-Za-z]|Add |Remove |Test |Print |Check |About |Comments |Extraction |Cd |'
                 r'Redirect |Back |Reset |Undo |Load |LoadPath |AddLoadPath|Arguments |Tactic |'
                 r'Infix |Notation |Reserved |Ltac |Hint |Existing |Instance |Fail |Succeed |Time |Timeout)')

def read(p):
    return open(p, encoding='utf-8', errors='replace').read().split('\n')

def body(ls):
    """返回 (正文起始下标, 头部行数)。头部 = 前导块注释 + Require/Import/Export/Set/Open 区。"""
    i = 0; depth = 0; seen_code = False; hdr_end = 0
    while i < len(ls):
        s = ls[i].strip()
        if depth > 0:
            if '*)' in s: depth = 0
            i += 1; continue
        if s.startswith('(*'):
            if '*)' not in s[2:]: depth = 1
            i += 1; continue
        if s == '' or HDR.match(s):
            i += 1; continue
        return i, i
    return 0, 0

def greedy(orig, ls, start_ptr, n_check=200):
    """从 orig 的 start_ptr 起，寻找 ls 正文起点，再校验随后连续行一致。"""
    bstart, _ = body(ls)
    if bstart >= len(ls): return None, 0, 0
    probe = ls[bstart].rstrip('\r')
    # 在 orig 中向后找 probe
    pos = None
    for j in range(start_ptr, len(orig)):
        if orig[j].rstrip('\r') == probe:
            pos = j; break
    if pos is None: return None, 0, 0
    # 连续校验
    n_ok = 0; n_bad = 0
    k = 0
    j = pos; i = bstart
    while j < len(orig) and i < len(ls) and k < n_check:
        a = orig[j].rstrip('\r'); b = ls[i].rstrip('\r')
        if a == b:
            n_ok += 1; j += 1; i += 1
        else:
            n_bad += 1
            # 允许分片比原文多出追加行：跳过 ls 中不匹配行继续对齐
            i += 1
            if n_bad > 30: break
        k += 1
    return pos, n_ok, n_bad

orig = read(ORIG)
print('原文件 (ConstructiveWorld.v, 219 锚): %d 行' % (len(orig) - 1))
for label, root in (('CW219_split', SPLIT), ('ConstructiveWorld_Live', LIVE)):
    print('=' * 92)
    print('【%s】分片对 219 锚的保序保真校验' % label)
    print('-' * 92)
    ptr = 0
    rows = []
    for sh in SHARDS:
        p = os.path.join(root, sh + '.v')
        ls = read(p)
        pos, ok, bad = greedy(orig, ls, ptr)
        bstart, hlen = body(ls)
        if pos is None:
            rows.append((sh, len(ls) - 1, hlen, None, None, ok, bad))
            print('  %-26s 行=%-7d 头=%-5d  <定位失败>' % (sh, len(ls) - 1, hlen))
            continue
        rows.append((sh, len(ls) - 1, hlen, pos + 1, pos + 1 - bstart, ok, bad))
        print('  %-26s 行=%-7d 头=%-4d 原文件起始=%-8d 偏移Δ=%-7d 连续命中=%-4d 失配=%d'
              % (sh, len(ls) - 1, hlen, pos + 1, pos + 1 - bstart, ok, bad))
        ptr = pos + 1
    print('-' * 92)
    print('  分片总行 = %d   | 219 锚 = %d  | 差 = %+d'
          % (sum(r[1] for r in rows), len(orig) - 1, sum(r[1] for r in rows) - (len(orig) - 1)))
    print('  头部行合计（分片新增)= %d' % sum(r[2] for r in rows))
    tot_ok = sum(r[5] or 0 for r in rows); tot_bad = sum(r[6] or 0 for r in rows)
    print('  正文连续命中 %d 行 / 失配 %d 行' % (tot_ok, tot_bad))
