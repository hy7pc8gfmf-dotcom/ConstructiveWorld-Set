# -*- coding: utf-8 -*-
"""行号锚点迁移 v2：在 v1 规则基础上补 R8–R17，覆盖残留形态（列表/斜杠/代码注释/区间/区域界）。"""
import io, os, re, sys

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = [('P1', '论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2', '论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3', '论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4', '论文4-资源受限收敛动力学与PCT-正式版.md')]
if os.environ.get('MIG_BASE'):
    BASE = os.environ['MIG_BASE']
    PAPERS = [(t, n) for (t, _), n in zip(PAPERS, os.environ.get('MIG_NAMES', '').split(','))]
    print('[DRY-RUN] BASE=%s' % BASE)

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
GUARD = re.compile(r'([A-Za-z_][A-Za-z0-9_]*\.v\s*:\s*)L(\d{1,7})')

RULES = [
 # ---- v1：括号族 ----
 (re.compile(r'(`[^`\n]+`)\s*[（(]\s*' + L + r'\s*[，,]\s*'), r'\1（', 'R2a'),
 (re.compile(r'(`[^`\n]+`)\s*[（(]\s*' + L + r'\s*[–—\-]\s*' + L + r'\s*[，,]\s*'), r'\1（', 'R2b'),
 (re.compile(r'(`[^`\n]+`)\s*[（(]\s*' + L + r'(?:\s*[–—]\s*' + L + r')?\s*[)）]'), r'\1', 'R1'),
 (re.compile(r'[（(]\s*' + L + r'\s*[–—]\s*' + L + r'\s*[)）]'), '', 'R4'),
 (re.compile(r'(?<![`\w])(' + r'[A-Za-z_][A-Za-z0-9_]{2,}' + r')\s*[（(]\s*' + L + r'\s*[)）]'), r'`\1`', 'R3'),
 (re.compile(r'[（(]\*\s*' + L + r'(?:\s*起)?\s*\*\s*[)）]'), '', 'R6'),
 # ---- v2：列表 / 斜杠 / 区间 / 区域界 ----
 (re.compile(r'(?<![A-Za-z0-9_.])' + L + r'(?:\s*[、/]\s*' + L + r')+'), '', 'R9'),          # L###、L### / L###/L###
 (re.compile(r'[，,]\s*' + L + r'(?=\s*[，,)）;；])'), '', 'R8'),                              # ，L### 于括号内
 (re.compile(r'[（(]\s*(?:<|≤)\s*' + L + r'\s*[)）]'), '', 'R13'),                            # （< L#####）
 (re.compile(r'[（(]\s*' + L + r'\s*区\s*[)）]'), '', 'R16'),                                  # （L##### 区）
 (re.compile(r'(?<![A-Za-z0-9_.])' + L + r'\s*[–—]\s*' + L + r'(?!\d)'), '', 'R15'),           # 裸区间
 (re.compile(r'实测\s*' + L + r'(?:\s*[/、]\s*' + L + r')*'), '实测结果见模块表', 'R12'),
 (re.compile(r'，\s*' + L + r'(?=\s*\*)'), '', 'R10'),                                        # 代码注释内 ，L###
 (re.compile(r'(?<=[A-Za-z0-9_]) ' + L + r'(?=\s|$|\*/)'), '', 'R11'),                        # code: ident L###
]

def migrate(txt):
    stash = []
    txt = GUARD.sub(lambda m: (stash.append(m.group(0)), '\x00%d\x00' % (len(stash) - 1))[1], txt)
    cnt = {}
    for pat, rep, tag in RULES:
        txt, k = pat.subn(rep, txt)
        if k: cnt[tag] = cnt.get(tag, 0) + k
    out = []
    for line in txt.split('\n'):
        if line.lstrip().startswith('|') and re.search(L, line) and '`' in line:
            before = line
            line = re.sub(r'(?<![A-Za-z0-9_.])L(\d{2,7})(?!\d)',
                          lambda m: ('`%s`' % shard(int(m.group(1)))) if shard(int(m.group(1))) else m.group(0), line)
            if line != before: cnt['R5'] = cnt.get('R5', 0) + 1
        out.append(line)
    txt = '\n'.join(out)
    for i, s in enumerate(stash): txt = txt.replace('\x00%d\x00' % i, s)
    return txt, cnt

for tag, fn in PAPERS:
    path = os.path.join(BASE, fn)
    with io.open(path, encoding='utf-8') as f: t = f.read()
    t2, cnt = migrate(t)
    with io.open(path, 'w', encoding='utf-8', newline='') as f: f.write(t2)
    with io.open(path, encoding='utf-8') as f: r = f.read()
    resid = [(i, l) for i, l in enumerate(r.split('\n'), 1)
             if re.search(r'(?<![A-Za-z0-9_.])L\d{2,7}(?!\d)', GUARD.sub('', l))]
    print('✓ %-4s %s ｜ 残留 %d 行' % (tag, ' '.join('%s=%d' % kv for kv in sorted(cnt.items())), len(resid)))
    if os.environ.get('MIG_SHOW'):
        for i, l in resid[:14]:
            m = re.search(r'(?<![A-Za-z0-9_.])L\d{2,7}(?!\d)', l)
            s = max(0, m.start() - 60)
            print('     L%-5d …%s…' % (i, l[s:m.end() + 45]))
