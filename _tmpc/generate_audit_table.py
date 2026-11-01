# -*- coding: utf-8 -*-
"""从迁移前备份(bk3)抽取 (标识符, 219锚行) 对，映射模块+分片区间，
生成独立审计定位表 代码引用定位表-20260916.md。"""
import io, os, re

BK = r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc'
PAPERS = [('论文1-构造性ML对齐统一形式化-正式版.md','P1'),
          ('论文2-自由能原理与注意力Gibbs桥-正式版.md','P2'),
          ('论文3-构造性柯西实数指数正性-正式版.md','P3'),
          ('论文4-资源受限收敛动力学与PCT-正式版.md','P4')]

SH = [(1,3071,'S01_BaseRing'),(3072,6982,'S02_CauchyComplete'),(6983,13800,'S03_QExp'),
      (13801,18733,'S04_RealExpLogConv'),(18734,24767,'S05_AlignmentGRPO'),
      (24768,32574,'S06_DiffSamplingGibbs'),(32575,41232,'S07_RealSetoidExpLog'),
      (41233,46820,'S08_RealMainlineDPO'),(46821,53931,'S09_EntropyReal'),
      (53932,66414,'S10_KVQuantTrig'),(66415,79152,'S11_TP3B5'),
      (79153,93447,'S12_B5RecycleSF'),(93448,97866,'S13_NLiveAudit'),
      (97867,112163,'S14_B5BatchBlock'),(112164,114222,'S15_TailFEPUp')]
def shard(n):
    for a,b,k in SH:
        if a<=n<=b: return k+'.v', 'L%d–L%d'%(a,b)
    return None, None

# 抽取：(标识符, 219行) —— 仅捕获 Coq 风格标识符
pat_backtick = re.compile(r'`([A-Za-z_][A-Za-z0-9_]*)`\s*[（(]\s*L(\d{2,7})')
pat_table    = re.compile(r'^\|\s*`([A-Za-z_][A-Za-z0-9_]*)`\s*\|\s*L(\d{2,7})\s*\|', re.M)
pat_paren    = re.compile(r'（\s*`?([A-Za-z_][A-Za-z0-9_]*)`?\s*，?\s*定义\s*L(\d{2,7})')

seen = {}   # name -> (line, set(papers))
total = 0
for fn, tag in PAPERS:
    t = io.open(os.path.join(BK, 'bk3_'+tag.lower()+'.md'), encoding='utf-8').read()
    for m in pat_backtick.finditer(t):
        name, ln = m.group(1), int(m.group(2))
        seen.setdefault(name, [ln, set()])[1].add(tag); total += 1
    for m in pat_table.finditer(t):
        name, ln = m.group(1), int(m.group(2))
        seen.setdefault(name, [ln, set()])[1].add(tag); total += 1
    for m in pat_paren.finditer(t):
        name, ln = m.group(1), int(m.group(2))
        seen.setdefault(name, [ln, set()])[1].add(tag); total += 1

# 去重后唯一标识符 -> (219行, 模块, 分片)
rows = []
unmapped = 0
for name, (ln, tags) in seen.items():
    mod, iv = shard(ln)
    if mod is None:
        unmapped += 1
        continue
    rows.append((ln, name, mod, iv, ','.join(sorted(tags))))

rows.sort()
print('抽取命中 %d 处；唯一标识符 %d；映射到模块 %d；未映射 %d' % (total, len(seen), len(rows), unmapped))

out = []
out.append('# 代码引用定位表（219 冻结基线 → 模块文件）')
out.append('')
out.append('> 本表为论文 1–4 代码引用的审计坐标。正文以**全限定标识符**为引用坐标；')
out.append('> 本表将该标识符映射回 **219 冻结基线**（`CW_ConstructiveWorld_219.v`，114,222 行，SHA-1 `7BBE42EA83D178901C94FA13FB18E0A3B975D09A`）的锚行与模块化分片，供读者在冻结快照中逐名核验。')
out.append('> 模块文件以 `ConstructiveWorld_Live/` 下 246 模块树为当前权威分发形态；行号随快照漂移，故正文不承载绝对行号（见各篇「标识符引用坐标」说明）。')
out.append('')
out.append('| 219 锚行 | 标识符 | 模块文件 | 分片区间（219 基线） | 来源 |')
out.append('|---|---|---|---|---|')
for ln, name, mod, iv, tags in rows:
    out.append('| L%-d | `%s` | `%s` | %s | %s |' % (ln, name, mod, iv, tags))
out.append('')
out.append('---')
out.append('')
out.append('**生成说明**：本表由迁移前论文快照（`_tmpc/bk3_*.md`）机械抽取 `(标识符, 锚行)` 对并映射模块生成；')
out.append('抽取覆盖正文中 `` `ident`（L####）``、审计表 `` | `ident` | L#### | `` 与 `` （`ident`，定义 L####）`` 三类形态，')
out.append('去重后按 219 锚行升序排列。未映射项（锚行超出 219 范围）已剔除。')

path = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\代码引用定位表-20260916.md'
with io.open(path, 'w', encoding='utf-8', newline='') as f:
    f.write('\n'.join(out))
with io.open(path, encoding='utf-8') as f:
    rb = f.read()
assert rb == '\n'.join(out), '审计表回读不一致'
print('✓ 已写出 %s （%d 行数据）' % (path, len(rows)))
