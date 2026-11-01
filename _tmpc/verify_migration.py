# -*- coding: utf-8 -*-
"""行号迁移最终验证：正文残留 / 文献连续性 / 结构完整性。"""
import io, os, re

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
BK = r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc'
PAPERS = [('P1','论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2','论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3','论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4','论文4-资源受限收敛动力学与PCT-正式版.md')]
GUARD = re.compile(r'([A-Za-z_][A-Za-z0-9_]*\.v\s*:\s*)L(\d{1,7})')
LANCHOR = re.compile(r'(?<![A-Za-z0-9_.])L\d{2,7}(?!\d)')

print('%-5s %8s %6s %8s %6s %s' % ('论文','残留','文献','越界','表头行','字节差(vs bk3)'))
for tag, fn in PAPERS:
    t = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    ls = t.split('\n')
    # 残留（排除代码围栏 + .v:guard）
    resid = 0; inf = False
    for l in ls:
        if l.startswith('```'): inf = not inf; continue
        if inf: continue
        ll = GUARD.sub('', l)
        resid += len(LANCHOR.findall(ll))
    # 文献连续性
    start = None
    for i,l in enumerate(ls):
        if re.match(r'^##\s*参考文献', l): start = i; break
    body = '\n'.join(ls[:start])
    nums = [int(x) for x in re.findall(r'\[(\d{1,2})\]', body)]
    refs = sum(1 for j in range(start+1, len(ls)) if re.match(r'^\d+\.\s', ls[j]))
    oob = sum(1 for x in nums if x > refs)
    # 表头含"行号"误导检查（值列已是模块名，但表头仍写"行号"的已重命名；此处只统计仍含"行号"的表头）
    bad_hdr = 0
    for l in ls:
        if l.lstrip().startswith('|') and re.search(r'\|\s*行号\s*\|', l) and not re.search(r'219\s*基线行号', l):
            bad_hdr += 1
    bk = io.open(os.path.join(BK, 'bk3_'+tag.lower()+'.md'), encoding='utf-8').read()
    diff = len(t.encode('utf-8')) - len(bk.encode('utf-8'))
    print('%-5s %8d %6d %8d %6d %+d' % (tag, resid, refs, oob, bad_hdr, diff))
    if resid or oob or bad_hdr:
        print('   ⚠ 需复核')

# 审计表存在性
ap = os.path.join(BASE, '代码引用定位表-20260916.md')
print()
print('审计定位表:', '存在' if os.path.exists(ap) else '缺失',
      '%d 字节' % os.path.getsize(ap) if os.path.exists(ap) else '')
print('DONE')
