# -*- coding: utf-8 -*-
"""步骤 3：正文行号锚点迁移 —— 219 绝对行号 → 具名引用 / 模块定位。
规则组（按序）：
  R1  反引号标识符紧邻的（L####）括号 → 删除括号
  R2  反引号标识符紧邻的（L####，…）   → 保留其余内容，删除行号部分
  R3  裸标识符紧邻的（L####）          → 转为 `标识符`
  R4  区间（L####–L####）              → 删除
  R5  表格中的行号格 |L####| / |ident| L#### |  → 替换为所属模块文件
  R6  代码块注释 (* L#### *)           → 删除括号注释
  R7  列表/枚举中的“L####、L####”      → 删除
排除：模块相对行号（Xxx.v:L###）
写入后强制回读校验。
"""
import io, os, re, sys

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = [('P1','P1.md'),
          ('P2','P2.md'),
          ('P3','P3.md'),
          ('P4','P4.md')]

SH = [(1,3071,'S01_BaseRing'),(3072,6982,'S02_CauchyComplete'),(6983,13800,'S03_QExp'),
      (13801,18733,'S04_RealExpLogConv'),(18734,24767,'S05_AlignmentGRPO'),
      (24768,32574,'S06_DiffSamplingGibbs'),(32575,41232,'S07_RealSetoidExpLog'),
      (41233,46820,'S08_RealMainlineDPO'),(46821,53931,'S09_EntropyReal'),
      (53932,66414,'S10_KVQuantTrig'),(66415,79152,'S11_TP3B5'),
      (79153,93447,'S12_B5RecycleSF'),(93448,97866,'S13_NLiveAudit'),
      (97867,112163,'S14_B5BatchBlock'),(112164,114222,'S15_TailFEPUp')]
def shard(n):
    for a, b, k in SH:
        if a <= n <= b: return k + '.v'
    return None

L = r'L\d{2,7}'
# 模块相对行号的保护：先把 Xxx.v:L### 暂存
GUARD = re.compile(r'([A-Za-z_][A-Za-z0-9_]*\.v?\s*:\s*)L(\d{1,7})')

RULES = [
 # R2 先做（更特殊）：`ident`（L####，其余）
 (re.compile(r'(`[^`\n]+`)\s*[（(]\s*' + L + r'\s*[，,]\s*'), r'\1（', 'R2a'),
 (re.compile(r'(`[^`\n]+`)\s*[（(]\s*' + L + r'\s*[–—\-]\s*' + L + r'\s*[，,]\s*'), r'\1（', 'R2b'),
 # R1：`ident`（L####）或 `ident`（L####–L####）
 (re.compile(r'(`[^`\n]+`)\s*[（(]\s*' + L + r'(?:\s*[–—]\s*' + L + r')?\s*[)）]'), r'\1', 'R1'),
 # R4：任意位置的行号区间（独立括号内）
 (re.compile(r'[（(]\s*' + L + r'\s*[–—]\s*' + L + r'\s*[)）]'), '', 'R4'),
 # R3：裸标识符（L####）
 (re.compile(r'(?<![`\w])(' + r'[A-Za-z_][A-Za-z0-9_]{2,}' + r')\s*[（(]\s*' + L + r'\s*[)）]'), r'`\1`', 'R3'),
 # R7：列表“L####、L####、L####” 或 “，L####、L####”
 (re.compile(r'(?<![A-Za-z0-9_.])' + L + r'(?:\s*[、,，]\s*' + L + r')+'), '', 'R7'),
 # R6：代码注释 (* L#### *) 或 (* L#### 起 *)
 (re.compile(r'[（(]\*\s*' + L + r'(?:\s*起)?\s*\*\s*[)）]'), '', 'R6'),
]

def migrate(txt):
    # 保护模块相对行号
    stash = []
    def keep(m):
        stash.append(m.group(0)); return '\x00%d\x00' % (len(stash) - 1)
    txt = GUARD.sub(keep, txt)

    cnt = {}
    for pat, rep, tag in RULES:
        txt, k = pat.subn(rep, txt)
        if k: cnt[tag] = cnt.get(tag, 0) + k

    # R5：表格行中的行号 → 所属模块
    out = []
    for line in txt.split('\n'):
        if line.lstrip().startswith('|') and re.search(L, line) and '`' in line:
            def cell(mm):
                sh = shard(int(mm.group(1)))
                return '`%s`' % sh if sh else mm.group(0)
            line2 = re.sub(r'(?<![A-Za-z0-9_.])L(\d{2,7})(?!\d)', lambda m: cell(m), line)
            if line2 != line:
                cnt['R5'] = cnt.get('R5', 0) + 1
                line = line2
        out.append(line)
    txt = '\n'.join(out)
    # 还原
    for i, s in enumerate(stash):
        txt = txt.replace('\x00%d\x00' % i, s)
    return txt, cnt

tot = {}
for tag, fn in PAPERS:
    path = os.path.join(BASE, fn)
    with io.open(path, encoding='utf-8') as f: t = f.read()
    t2, cnt = migrate(t)
    with io.open(path, 'w', encoding='utf-8', newline='') as f: f.write(t2)
    # 回读
    with io.open(path, encoding='utf-8') as f: r = f.read()
    rem = len(re.findall(r'(?<![A-Za-z0-9_.])L\d{2,7}(?!\d)', GUARD.sub('', r)))
    tot[tag] = (cnt, rem)
    print('✓ %-4s %s ｜ 残留独立行号 %d' % (tag, ' '.join('%s=%d' % kv for kv in sorted(cnt.items())), rem))
print()
print('合计规则命中：')
agg = {}
for tag, (cnt, rem) in tot.items():
    for k, v in cnt.items(): agg[k] = agg.get(k, 0) + v
print(' ', agg)
print(' 残留独立行号合计：', sum(v[1] for v in tot.values()))
