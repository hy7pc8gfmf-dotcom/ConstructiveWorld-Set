# -*- coding: utf-8 -*-
"""逐片验证 S01–S15 分片头部声明的「原文区间」与「去头正文 ≡ 原文区间逐字节」。

分片头部格式（CW219_split）：
  (* ===== CW219 拆分分片 S0X_XXX（机械生成头部，非原文） ===== *)
  (* 原文区间：CW_ConstructiveWorld_219.v L3072-L6982；头部 10 行（含尾空行）；
     依赖：S01；去头正文 ≡ 原文区间逐字节（tools/verify_split.py） *)
"""
import os, re

ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
ROOTS = {
    'CW219_split': r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\CW219_split',
    'ConstructiveWorld_Live': r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\ConstructiveWorld_Live',
}
SHARDS = ['S01_BaseRing','S02_CauchyComplete','S03_QExp','S04_RealExpLogConv',
          'S05_AlignmentGRPO','S06_DiffSamplingGibbs','S07_RealSetoidExpLog',
          'S08_RealMainlineDPO','S09_EntropyReal','S10_KVQuantTrig','S11_TP3B5',
          'S12_B5RecycleSF','S13_NLiveAudit','S14_B5BatchBlock','S15_TailFEPUp']

orig = open(ORIG, encoding='utf-8', errors='replace').read().split('\n')
print('219 锚原件 ConstructiveWorld.v: %d 行' % (len(orig) - 1))
print()

for label, root in ROOTS.items():
    print('=' * 100)
    print('【%s】' % label)
    print('=' * 100)
    total_body = 0
    prev_end = 0
    rows = []
    for sh in SHARDS:
        p = os.path.join(root, sh + '.v')
        raw = open(p, encoding='utf-8', errors='replace').read()
        ls = raw.split('\n')
        m = re.search(r'原文区间：\S*\s*L(\d+)\s*-\s*L(\d+)', raw)
        mh = re.search(r'头部\s*(\d+)\s*行', raw)
        if not m:
            rows.append((sh, len(ls) - 1, None, None, None, None, 'NO_RANGE_DECL'))
            print('  %-24s 行=%-7d  <未声明原文区间>' % (sh, len(ls) - 1))
            continue
        a, b = int(m.group(1)), int(m.group(2))
        hdrcnt = int(mh.group(1)) if mh else None
        # 去头正文
        body = '\n'.join(ls[hdrcnt:]) if hdrcnt is not None else None
        seg = '\n'.join(orig[a - 1:b])
        if body is not None:
            # 允许尾部空行差异
            same = body.rstrip('\n') == seg.rstrip('\n')
            lenb = body.count('\n') + 1
            lenseg = b - a + 1
        else:
            same, lenb, lenseg = None, None, b - a + 1
        rows.append((sh, len(ls) - 1, a, b, hdrcnt, same, '%s' % ('BYTE_EQ' if same else 'DIFF')))
        print('  %-24s 分片行=%-6d 声明区间 L%d-L%d  头=%-4s 区间长度=%-6d 去头正文长度=%-6s 判定=%s'
              % (sh, len(ls) - 1, a, b, hdrcnt, lenseg, lenb, 'BYTE_EQ' if same else ('DIFF' if same is False else '?')))
        total_body += (lenb or 0)
        if a < prev_end:
            print('      ⚠ 区间与前片重叠/逆序（前片止于 L%d）' % prev_end)
        prev_end = max(prev_end, b)
    print('-' * 100)
    ok = sum(1 for r in rows if r[6] == 'BYTE_EQ')
    print('  BYTE_EQ 分片数: %d / %d ；声明区间总长(去重可见) = %d ；219 锚 = %d'
          % (ok, len(rows), prev_end, len(orig) - 1))
    print()
