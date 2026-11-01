# -*- coding: utf-8 -*-
"""参考文献一致性校验：编号连续、正文 [n] 均在范围内、占位符/错误期刊名残留、新增条目到位。"""
import io, os, re

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = ['论文1-构造性ML对齐统一形式化-正式版.md',
          '论文2-自由能原理与注意力Gibbs桥-正式版.md',
          '论文3-构造性柯西实数指数正性-正式版.md',
          '论文4-资源受限收敛动力学与PCT-正式版.md']

# 旧错误措辞黑名单
BAD = {
 '论文1-构造性ML对齐统一形式化-正式版.md': ['Infotheo / coq-proba: A Coq Library for Information Theory. *MathComp*'],
 '论文2-自由能原理与注意力Gibbs桥-正式版.md': ['Version [X.Y]', 'Archive of Formal Proofs, https://clip4.ait',
                                             'Garrigue, J., Nowak, D.'],
}

for fn in PAPERS:
    p = os.path.join(BASE, fn)
    txt = io.open(p, encoding='utf-8').read()
    lines = txt.split('\n')
    # 参考文献段
    start = None
    for i, l in enumerate(lines):
        if re.match(r'^##\s*参考文献', l):
            start = i; break
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if re.match(r'^##\s', lines[j]):
            end = j; break
    nums = []
    for j in range(start + 1, end):
        m = re.match(r'^(\d+)\.\s', lines[j])
        if m: nums.append(int(m.group(1)))
    # 编号连续性
    expect = list(range(1, len(nums) + 1))
    cont = 'OK' if nums == expect else '✗ 断号/重号: %s' % [x for x in nums if nums.count(x) > 1]
    # 正文引用范围（只看参考文献段之前的正文，排除年份/页码干扰：限定形式 [数字] 且 ≤ 上限）
    body = '\n'.join(lines[:start])
    cited = set(int(x) for x in re.findall(r'\[(\d{1,2})\]', body))
    n = len(nums)
    oob = sorted(x for x in cited if x < 1 or x > n)
    uncited = sorted(set(expect) - cited)
    print('=' * 104)
    print('【%s】' % fn)
    print('  条目数 %d   编号连续性 %s   段位置 L%d–L%d' % (n, cont, start + 1, end))
    print('  正文引用上限 %d ；越界引用 %s' % (n, oob if oob else '无'))
    print('  正文未引用条目 %d 条：%s' % (len(uncited), uncited[:24] if uncited else '无'))
    # 黑名单
    hits = [b for b in BAD.get(fn, []) if b in txt]
    print('  旧错误措辞残留：%s' % ('✗ %s' % hits if hits else '○ 无'))
    # 新增条目到位检查（末 N 条）
    print('  末 3 条：')
    for j in range(max(start + 1, end - 3), end):
        if re.match(r'^\d+\.\s', lines[j]):
            print('    ', lines[j][:150])
    print()
