# -*- coding: utf-8 -*-
"""步骤 1–2：建立权威映射 —— 219 行号 → (所属模块路径, 该行声明名, 分片, 片内偏移)
并对论文中每个 L<n> 令牌的**语法上下文**分类，为批量替换定规则。
"""
import io, os, re, json
from collections import Counter, defaultdict

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
ORIG = r'D:\ComplexAnalysis\ConstructiveWorld\ConstructiveWorld.v'
OUT = r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc'

SHARD_RANGE = {
 'S01_BaseRing':(1,3071,0), 'S02_CauchyComplete':(3072,6982,10), 'S03_QExp':(6983,13800,11),
 'S04_RealExpLogConv':(13801,18733,12), 'S05_AlignmentGRPO':(18734,24767,14),
 'S06_DiffSamplingGibbs':(24768,32574,15), 'S07_RealSetoidExpLog':(32575,41232,16),
 'S08_RealMainlineDPO':(41233,46820,18), 'S09_EntropyReal':(46821,53931,19),
 'S10_KVQuantTrig':(53932,66414,20), 'S11_TP3B5':(66415,79152,21),
 'S12_B5RecycleSF':(79153,93447,23), 'S13_NLiveAudit':(93448,97866,24),
 'S14_B5BatchBlock':(97867,112163,25), 'S15_TailFEPUp':(112164,114222,27),
}

def shard_of(n):
    for k,(a,b,h) in SHARD_RANGE.items():
        if a <= n <= b: return k, n - a + 1 + h
    return None, None

# ---------- 构建 219 的 Module/Section 栈 + 声明索引 ----------
lines = io.open(ORIG, encoding='utf-8', errors='replace').read().split('\n')
DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant)\s+'
                  r'([A-Za-z_][A-Za-z0-9_\']*)')
FIELD = re.compile(r'^\s{2,}([a-z_][A-Za-z0-9_\']*)\s*:')
OPEN = re.compile(r'^\s*(Module|Section)\s+(?:Type\s+)?([A-Za-z_][A-Za-z0-9_\']*)')
CLOSE = re.compile(r'^\s*End\s+([A-Za-z_][A-Za-z0-9_\']*)')

stack = []
decl_at = {}      # line -> (kind, name)
mod_at = {}       # line -> module path (sections excluded from qualification)
for i, l in enumerate(lines, 1):
    # End 需先处理（End 行本身属于外层）
    m = CLOSE.match(l)
    if m:
        if stack: stack.pop()
        mod_at[i] = '.'.join(n for k, n in stack if k == 'Module')
        continue
    o = OPEN.match(l)
    if o:
        stack.append((o.group(1), o.group(2)))
        mod_at[i] = '.'.join(n for k, n in stack if k == 'Module')
        continue
    d = DECL.match(l)
    if d:
        decl_at[i] = (d.group(1), d.group(2))
    else:
        f = FIELD.match(l)
        if f: decl_at[i] = ('field', f.group(1))
    mod_at[i] = '.'.join(n for k, n in stack if k == 'Module')

def fullname(n):
    """返回 (模块路径, 名字, 类型)"""
    for k in (n, n-1, n+1, n+2, n-2):
        if k in decl_at:
            kind, name = decl_at[k]
            return mod_at.get(k, ''), name, kind
    return '', None, None

json.dump({'ok': True}, io.open(os.path.join(OUT, '_mapmark.json'), 'w'))

# ---------- 论文锚点 + 语法上下文分类 ----------
PAPERS = [('P1','论文1-构造性ML对齐统一形式化-正式版.md'),
          ('P2','论文2-自由能原理与注意力Gibbs桥-正式版.md'),
          ('P3','论文3-构造性柯西实数指数正性-正式版.md'),
          ('P4','论文4-资源受限收敛动力学与PCT-正式版.md')]
LNUM = re.compile(r'(?<![A-Za-z0-9_.])L(\d{3,7})(?!\d)')

def ctx_kind(l, m):
    """判定该 L 令牌的语法上下文"""
    s = l.strip()
    pre = l[:m.start()]; post = l[m.end():]
    if re.search(r'`[^`]*$', pre) or re.search(r'^\s*`', post[:2]):
        return 'C_BACKTICK'
    if re.match(r'^\s*\|\s*L\d', l) or re.search(r'\|\s*$', pre[len(pre.rstrip())-1:len(pre.rstrip())+1] or ' '):
        return 'E_TABLE_CELL'
    if re.search(r'\(\*\s*$', pre) or re.search(r'\(\*\s*L?\d', l) and s.endswith('*)'):
        return 'D_CODE_COMMENT'
    if re.search(r'[（(]\s*$', pre):
        return 'A_PAREN'
    if re.search(r'[，,]\s*$', pre):
        return 'B_COMMA'
    if re.search(r'[–—-]\s*$', pre) or re.match(r'^\s*[–—-]', post):
        return 'F_RANGE'
    if s.startswith('|'):
        return 'E_TABLE_ROW'
    return 'Z_OTHER'

rows = []
kinds = Counter()
for tag, fn in PAPERS:
    ls = io.open(os.path.join(BASE, fn), encoding='utf-8').read().split('\n')
    for i, l in enumerate(ls, 1):
        for m in LNUM.finditer(l):
            n = int(m.group(1))
            if n > 114222: continue
            k = ctx_kind(l, m)
            kinds[k] += 1
            sh, off = shard_of(n)
            mp, nm, kd = fullname(n)
            pre = l[:m.start()]
            ids = re.findall(r'`([A-Za-z_][A-Za-z0-9_\.]*)`', pre)
            rows.append({'paper': tag, 'pline': i, 'anchor': n, 'kind': k,
                         'shard': sh, 'off': off, 'mod': mp, 'decl': nm, 'declkind': kd,
                         'near_ident': ids[-1] if ids else None,
                         'text': l.strip()[:160]})

json.dump(rows, io.open(os.path.join(OUT, 'anchor_map.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=1)

print('=' * 104)
print('① 语法上下文分类（决定替换规则）')
print('=' * 104)
for k, v in kinds.most_common():
    print('  %-16s %5d  (%.1f%%)' % (k, v, 100*v/sum(kinds.values())))
print('  合计 %d' % sum(kinds.values()))

print()
print('=' * 104)
print('② 映射命中率（该行/邻近是否为声明）')
print('=' * 104)
hit = sum(1 for r in rows if r['decl'])
print('  有声明名 %d / %d (%.1f%%)' % (hit, len(rows), 100*hit/len(rows)))
print()
print('  未命中样例：')
for r in rows:
    if not r['decl']:
        print('     %-4s L%-5d L%-8d %-22s %s' % (r['paper'], r['pline'], r['anchor'], r['shard'], r['text'][:80]))
print()
print('=' * 104)
print('③ 邻近标识符 与 该行声明名 是否一致（抽查 25 条）')
print('=' * 104)
same = diff = 0; n = 0
for r in rows:
    if r['near_ident'] and r['decl']:
        n += 1
        if r['near_ident'].split('.')[-1] == r['decl']: same += 1
        elif n <= 25:
            diff += 1
            print('  ✗ 邻近名 %-34s 该行声明 %s' % (r['near_ident'], r['decl']))
print('  一致 %d / 有邻近名且有声明 %d' % (same, n))
