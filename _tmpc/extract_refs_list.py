# -*- coding: utf-8 -*-
"""抽取四篇论文的参考文献条目，并按 URL/DOI 归一，供联网核验。"""
import io, os, re

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = {
 'P1': '论文1-构造性ML对齐统一形式化-正式版.md',
 'P2': '论文2-自由能原理与注意力Gibbs桥-正式版.md',
 'P3': '论文3-构造性柯西实数指数正性-正式版.md',
 'P4': '论文4-资源受限收敛动力学与PCT-正式版.md',
}

for tag, fn in PAPERS.items():
    txt = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    lines = txt.split('\n')
    # 定位「## 参考文献」段并抓到下一个 ## 或文件尾
    start = None
    for i, l in enumerate(lines):
        if re.match(r'^##\s*参考文献', l) or re.match(r'^###\s*参考文献', l):
            start = i + 1
            break
    if start is None:
        print('%s: 未找到参考文献段' % tag); continue
    end = len(lines)
    for j in range(start, len(lines)):
        if re.match(r'^##\s', lines[j]) and j > start:
            end = j; break
    seg = lines[start:end]
    print('=' * 110)
    print('【%s】%s   （条目段 L%d–L%d）' % (tag, fn, start + 1, end))
    print('=' * 110)
    n = 0
    for k, l in enumerate(seg):
        s = l.strip()
        if re.match(r'^\d+\.\s', s):
            n += 1
            print('  [%s] %s' % (tag, s))
    print('  —— 共 %d 条\n' % n)

# 统计全文出现的 URL / DOI / arXiv
print('=' * 110)
print('全文 URL / DOI / arXiv 汇总')
print('=' * 110)
for tag, fn in PAPERS.items():
    txt = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    urls = set(re.findall(r'https?://[^\s\)\]，。；、]+', txt))
    arx = set(re.findall(r'arXiv:\s*([\d.]+)', txt))
    dois = set(re.findall(r'doi:\s*(10\.[^\s\)\]，。；、]+)', txt))
    print('\n【%s】URL %d 条 / arXiv %d 条 / DOI %d 条' % (tag, len(urls), len(arx), len(dois)))
    for u in sorted(urls): print('   ', u)
    for a in sorted(arx): print('    arXiv:', a)
    for d in sorted(dois): print('    doi:', d)
