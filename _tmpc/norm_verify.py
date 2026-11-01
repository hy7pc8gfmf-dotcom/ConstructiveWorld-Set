# -*- coding: utf-8 -*-
"""规范性修订 · 综合验证"""
import io, os, re

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
P = [('P1', '论文1-构造性ML对齐统一形式化-正式版.md'),
     ('P2', '论文2-自由能原理与注意力Gibbs桥-正式版.md'),
     ('P3', '论文3-构造性柯西实数指数正性-正式版.md'),
     ('P4', '论文4-资源受限收敛动力学与PCT-正式版.md')]

E201_BAN = ['版本：', '2026-08/', 'v9', 'v10', 'E1xx', 'Aug', '深夜', '战役', '收官',
            '对齐版', '探针', '经验卡', '落地', '沉淀']
STYLE_BAN = ['如实', '照实', '诚实标注', '真态', '该件', '本件', '同件', '逐件',
             '挂账', '收口', '收束', '判词', '定谳', '裁定', '钉死', '钉定', '归并', '退役',
             '新增面', '其后另有', '母版', '投稿面', '送审面', '规范版', '正式版',
             '体量', '杠杆', '压缩前', '旧第', '版本快照', '版本日期依据', '历史快照',
             '历史基线', '钉墙', '台账', '本稿', '两版差异', '锚尾', '归并', '座位']
PUNCT = {'连续逗号 ，，': r'，，', '连续句号 。。': r'。。', '；，': r'；，', '。，': r'。，',
         '，；': r'，；', '，。': r'，。', '：，': r'：，', '：。': r'：。', '空括号 （）': r'（）',
         '空括号 「」': r'「」', '空 号': r'、\s*。', '句首逗号': r'(?m)^[，。；、]',
         '未闭合 〔': r'〔(?![^〕]*〕)', '未闭合 （': r'（(?![^）\n]*）)', '未闭合 「': r'「(?![^」]*」)'}

print('=' * 100)
print('① E201 禁词终检（须零命中）')
print('=' * 100)
for tag, fn in P:
    t = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    hits = ['%s×%d' % (k, t.count(k)) for k in E201_BAN if t.count(k)]
    print('  %-4s %s' % (tag, '○ 零命中' if not hits else '⚠ ' + '｜'.join(hits)))

print()
print('=' * 100)
print('② 规范性黑名单终检')
print('=' * 100)
for tag, fn in P:
    t = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    hits = ['%s×%d' % (k, t.count(k)) for k in STYLE_BAN if t.count(k)]
    print('  %-4s %s' % (tag, '○ 干净' if not hits else '⚠ ' + '｜'.join(hits)))

print()
print('=' * 100)
print('③ 标点 / 括号完整性（须零命中）')
print('=' * 100)
for tag, fn in P:
    t = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    hits = ['%s×%d' % (k, len(re.findall(p, t))) for k, p in PUNCT.items() if re.findall(p, t)]
    print('  %-4s %s' % (tag, '○ 干净' if not hits else '⚠ ' + '｜'.join(hits)))

print()
print('=' * 100)
print('④ 参考文献完整性（编号连续 / 越界引用 / 未引用条目）')
print('=' * 100)
for tag, fn in P:
    t = io.open(os.path.join(BASE, fn), encoding='utf-8').read()
    lines = t.split('\n')
    start = None
    for i, l in enumerate(lines):
        if re.match(r'^##\s*参考文献', l):
            start = i; break
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if re.match(r'^##\s', lines[j]):
            end = j; break
    nums = [int(re.match(r'^(\d+)\.\s', lines[j]).group(1)) for j in range(start + 1, end) if re.match(r'^(\d+)\.\s', lines[j])]
    body = '\n'.join(lines[:start])
    cited = set(int(x) for x in re.findall(r'\[(\d{1,2})\]', body))
    n = len(nums)
    cont = 'OK' if nums == list(range(1, n + 1)) else '✗'
    oob = sorted(x for x in cited if x > n)
    unc = sorted(set(range(1, n + 1)) - cited)
    print('  %-4s 条目 %-3d 连续 %-3s 越界 %-3s 未引用 %-3s' % (tag, n, cont, len(oob) or '0', len(unc) or '0'))

print()
print('=' * 100)
print('⑤ 规模对照（相对备份）')
print('=' * 100)
bk = {'P1': 'bk_p1.md', 'P2': 'bk_p2.md', 'P3': 'bk_p3.md', 'P4': 'bk_p4.md'}
for tag, fn in P:
    a = os.path.join(r'D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc', bk[tag])
    b = os.path.join(BASE, fn)
    sa, sb = os.path.getsize(a), os.path.getsize(b)
    la = io.open(a, encoding='utf-8').read().count('\n') + 1
    lb = io.open(b, encoding='utf-8').read().count('\n') + 1
    print('  %-4s 字节 %7d → %7d (Δ%+d) ｜ 行 %5d → %5d (Δ%+d)' % (tag, sa, sb, sb - sa, la, lb, lb - la))
