# -*- coding: utf-8 -*-
"""评估：219 绝对行号 → 模块分片 + 模块内偏移 的映射可行性；
并统计论文中 L<n> 锚点的规模与分布。"""
import io, os, re, json

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
SPLIT = os.path.join(BASE, 'CW219_split')
LIVE = os.path.join(BASE, 'ConstructiveWorld_Live')
PAPERS = [('P1', '论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2', '论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3', '论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4', '论文4-资源受限收敛动力学与PCT-正式版.md')]
SHARDS = ['S01_BaseRing','S02_CauchyComplete','S03_QExp','S04_RealExpLogConv','S05_AlignmentGRPO',
          'S06_DiffSamplingGibbs','S07_RealSetoidExpLog','S08_RealMainlineDPO','S09_EntropyReal',
          'S10_KVQuantTrig','S11_TP3B5','S12_B5RecycleSF','S13_NLiveAudit','S14_B5BatchBlock','S15_TailFEPUp']

# ---------- 1. 从分片头部抽「原文区间」 ----------
ranges = {}
for sh in SHARDS:
    p = os.path.join(SPLIT, sh + '.v')
    raw = io.open(p, encoding='utf-8', errors='replace').read()
    m = re.search(r'原文区间：\S*\s*L(\d+)\s*-\s*L(\d+)', raw)
    mh = re.search(r'头部\s*(\d+)\s*行', raw)
    if m:
        ranges[sh] = (int(m.group(1)), int(m.group(2)), int(mh.group(1)) if mh else None)
    else:
        ranges[sh] = (1, 3071, None)   # S01：覆盖 L1–L3071，无区间声明

print('=' * 104)
print('① 219 → 分片 区间表（据分片头部声明）')
print('=' * 104)
prev = 0; tile_ok = True
for sh in SHARDS:
    a, b, hdr = ranges[sh]
    gap = a - prev - 1
    if gap != 0: tile_ok = False
    print('  %-22s L%-7d– L%-7d  长度 %-6d 头部 %-4s %s' % (sh, a, b, b - a + 1, hdr, '' if gap == 0 else '⚠ 与前片间隔 %d' % gap))
    prev = b
print('  —— 区间铺满判定：%s（末片止于 L%d，219 锚 114,222）' % ('完全相接无空洞' if tile_ok and prev == 114222 else '有空洞/重叠', prev))

def locate(n):
    for sh in SHARDS:
        a, b, hdr = ranges[sh]
        if a <= n <= b:
            return sh, n - a + 1 + (hdr or 0)
    return None, None

# ---------- 2. 论文 L<n> 锚点统计 ----------
print()
print('=' * 104)
print('② 论文中 L<n> 锚点规模与分布')
print('=' * 104)
all_anchors = {}
for tag, fn in PAPERS:
    t = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    # 排除模块相对行号（形如 Xxx.v:L### 或 Xxx L###）
    nums = [int(x) for x in re.findall(r'(?<![A-Za-z0-9_.])L(\d{3,7})(?!\d)', t)]
    anchor = [n for n in nums if n <= 114222]
    all_anchors[tag] = anchor
    from collections import Counter
    shardcnt = Counter()
    oob = 0
    for n in anchor:
        sh, off = locate(n)
        if sh: shardcnt[sh] += 1
        else: oob += 1
    print('  %-4s L 令牌 %-5d （≤114222 的锚点 %-5d，越界 %d）' % (tag, len(nums), len(anchor), oob))
    print('       分片分布：%s' % ' '.join('%s:%d' % (k.replace('_', ''), v) for k, v in sorted(shardcnt.items())))
    print()

# ---------- 3. 映射可验证性抽样 ----------
print('=' * 104)
print('③ 映射可验证性抽样（取 P4 全部锚点，核对该行是否为声明行）')
print('=' * 104)
orig = io.open(r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v', encoding='utf-8', errors='replace').read().split('\n')
DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|Record|Class|Section|Module|Variable|Context|End)\b')
ok = bad = 0; badlist = []
for n in sorted(set(all_anchors['P4'])):
    sh, off = locate(n)
    src = orig[n-1] if 1 <= n <= len(orig) else ''
    verdict = 'DECL' if DECL.match(src) else ('STRUCT' if src.strip() else 'BLANK')
    if verdict == 'DECL': ok += 1
    else:
        bad += 1; badlist.append((n, sh, off, src.strip()[:60]))
print('  P4 唯一锚点 %d：声明行 %d ｜ 非声明行 %d' % (len(set(all_anchors['P4'])), ok, bad))
for n, sh, off, s in badlist[:8]:
    print('     L%-7d → %-22s 模块内偏移 %-6s ｜ 该行：%s' % (n, sh, off, s))
