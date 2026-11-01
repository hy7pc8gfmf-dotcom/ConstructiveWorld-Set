# -*- coding: utf-8 -*-
"""抽取模块头部注释块（ConstructiveWorld 各件头注含内容自述），用于快速判定实质。"""
import os, sys, glob, re, json
sys.path.insert(0, r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc')

LIVE = r'D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live'
cov = json.load(open(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc\coverage.json', encoding='utf-8'))
targets = [r['name'] for r in cov if r['cls'] == 'D_UNCLAIMED' and r['lines'] >= 300]
want = set(sys.argv[1:]) if len(sys.argv) > 1 else None

def header(path, maxlines=26):
    ls = open(path, encoding='utf-8', errors='replace').read().split('\n')
    out = []
    i = 0
    # 找第一个块注释起点
    while i < len(ls) and not ls[i].lstrip().startswith('(*'):
        i += 1
    depth = 0
    while i < len(ls) and len(out) < maxlines:
        l = ls[i]
        out.append(l)
        depth += l.count('(*') - l.count('*)')
        i += 1
        if depth <= 0 and len(out) > 2:
            break
    return out

for name in targets:
    if want and name not in want: continue
    p = os.path.join(LIVE, name + '.v')
    if not os.path.exists(p): continue
    n = len(open(p, encoding='utf-8', errors='replace').read().split('\n')) - 1
    print('#' * 112)
    print('### %s   (%d 行)' % (name, n))
    print('#' * 112)
    for l in header(p):
        print(l.rstrip()[:150])
    print()
