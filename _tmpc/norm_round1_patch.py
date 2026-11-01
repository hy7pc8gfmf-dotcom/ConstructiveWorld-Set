# -*- coding: utf-8 -*-
"""第 1 轮补丁：处理计数不符的波次变体。"""
import io, os, re

BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
P = ['论文1-构造性ML对齐统一形式化-正式版.md',
     '论文2-自由能原理与注意力Gibbs桥-正式版.md',
     '论文3-构造性柯西实数指数正性-正式版.md',
     '论文4-资源受限收敛动力学与PCT-正式版.md']

# 用正则统一清除所有残留的"其后另有…为准"族
PAT = re.compile(r'[；，。]?\s*其后另有成果接入与注册收尾波（波次 →228→246）(?:推进中)?，以随论文 artifact 的变更记录为准[。；]?')
for fn in P:
    path = os.path.join(BASE, fn)
    txt = io.open(path, encoding='utf-8').read()
    n = len(PAT.findall(txt))
    if n == 0:
        print('○ %-5s 无残留' % fn[:4]); continue
    def fix(m):
        s = m.group(0)
        head = s[0] if s[0] in '；，。' else ''
        tail = s[-1] if s[-1] in '。；' else '。'
        # 句末保留一个句号；句中保留分号
        if head == '；':
            return '；'
        if head == '，':
            return '，'
        return '。'
    txt = PAT.sub(fix, txt)
    io.open(path, 'w', encoding='utf-8', newline='').write(txt)
    print('✓ %-5s 清除 %d 处' % (fn[:4], n))
print('完成。')
