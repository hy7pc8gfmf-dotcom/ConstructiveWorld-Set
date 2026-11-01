# -*- coding: utf-8 -*-
"""论文2 库真态刷新：84e2de2/221/333/221-221/CI#65 → 39d81aa/246/356/246-246/CI#72。
幂等 + 计数断言：每处替换声明期望次数，不匹配即报错退出（不静默）。
"""
import sys, io

P = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文\论文2-自由能原理与注意力Gibbs桥-正式版.md'
txt = io.open(P, encoding='utf-8').read()
orig = txt

# (旧串, 新串, 期望次数)  —— 顺序：短语统一先行，再做定位替换
REPS = [
    # ---- A. 波次措辞统一（先行）----
    ("其后另有模块整合与注册波推进中",
     "其后另有成果接入与注册收尾波（波次 →228→246）推进中", 9),
    ("further module-integration and registration waves are in progress",
     "further results-integration and registration-closing waves are in progress", 1),

    # ---- B. 中文摘要 ----
    ("当前库真态为 HEAD=84e2de2，编译清单 221 模块，Live_X 333 个 .v，CI 连续 success，认证面 221/221，各波 coqchk 全绿",
     "当前库真态为 HEAD=39d81aa，编译清单 246 模块，Live_X 356 个 .v，CI 连续 success，认证面 246/246，各波 coqchk 全绿", 1),

    # ---- C. 英文摘要 ----
    ("The current repository state is HEAD=84e2de2, with 221 modules in the compilation manifest, 333 Live_X .v files, continuous CI success, and a certified surface of 221/221",
     "The current repository state is HEAD=39d81aa, with 246 modules in the compilation manifest, 356 Live_X .v files, continuous CI success, and a certified surface of 246/246", 1),

    # ---- D. §1.3 头部（含版本标签对齐：9.0 → 9.0/9.1）----
    ("当前库真态（HEAD=84e2de2）：ConstructiveWorld 于 Rocq/Coq 9.0 纯构造性编译",
     "当前库真态（HEAD=39d81aa）：ConstructiveWorld 于 Rocq/Coq 9.0/9.1 纯构造性编译", 1),

    # ---- E. §1.3 认证段（9.0 基线段保留为史实 + 补 9.1 段至 CI #72）----
    ("编译清单 221 模块，Live_X 333 个 .v；CI 连续 success，认证面 221/221，各波 coqchk 全绿（最近云认证 run 94486425397 @24431dc，COQCHK_ALL_PASS）",
     "编译清单 246 模块，Live_X 356 个 .v；CI 连续 success，认证面 246/246，各波 coqchk 全绿（9.0 基线段以 run 94486425397 @24431dc 全树 COQCHK_ALL_PASS 收尾；当前 9.1 认证段 CI #72（head 39d81aa，run 35057242417，246 注册面）COQCHK_ALL_PASS，57,154 常量经内核复检）", 1),

    # ---- F. §9.2 第 8 项标题 ----
    ("**历史 220 分发形态与当前 221 编译清单的范围注**",
     "**历史 220 分发形态与当前 246 编译清单的范围注**", 1),

    # ---- G. §9.2 第 8 项尾（该处措辞已被 A 替换，故此处用替换后文本）----
    ("当前编译清单为 221 模块，Live_X 333 个 .v；",
     "当前编译清单为 246 模块，Live_X 356 个 .v；", 2),

    # ---- H. 表 A.1 库真态对齐行（A 已替换，故直接改数值）----
    ("| 库真态对齐 | HEAD=84e2de2；编译清单 221 模块；Live_X 333 个 .v；CI success；认证面 221/221；81 条 PA 挂账；",
     "| 库真态对齐 | HEAD=39d81aa；编译清单 246 模块；Live_X 356 个 .v；CI success；认证面 246/246；81 条 PA 挂账；", 1),
    ("| 2026-09-15 库真态快照 | 附录 C |", "| 2026-09-16 库真态快照 | 附录 C |", 1),

    # ---- I. 附录 B 用途段 ----
    ("当前库真态以 HEAD=84e2de2 为准（编译清单 221 模块，Live_X 333 个 .v，",
     "当前库真态以 HEAD=39d81aa 为准（编译清单 246 模块，Live_X 356 个 .v，", 1),

    # ---- J. §10.2 第 2 项：开放项时点锚 + 认证面 ----
    ("**仍开放（末端一步，截至 HEAD=b657aff）**",
     "**仍开放（末端一步，截至库真态快照 HEAD=39d81aa；库内未见把该组合并为单一定理的后续件）**", 1),
    ("当前认证面 221/221，CI 连续 success。",
     "当前认证面 246/246，CI 连续 success。", 1),

    # ---- K. 附录尾段 ----
    ("当前库真态为 HEAD=84e2de2，编译清单 221 模块，Live_X 333 个 .v，CI 连续 success，认证面 221/221；",
     "当前库真态为 HEAD=39d81aa，编译清单 246 模块，Live_X 356 个 .v，CI 连续 success，认证面 246/246；", 1),
]

ok = True
for old, new, exp in REPS:
    n = txt.count(old)
    if n != exp:
        print('✗ 计数不符（期望 %d 实测 %d）：%s' % (exp, n, old[:72]))
        ok = False
        continue
    txt = txt.replace(old, new)
    print('✓ %-2d 处  %s' % (n, old[:72]))

if not ok:
    print('\n存在计数不符项 —— 未写盘。')
    sys.exit(1)

io.open(P, 'w', encoding='utf-8', newline='').write(txt)
print('\n已写盘。行数 %d → %d' % (orig.count('\n') + 1, txt.count('\n') + 1))

# ---- 唯一性 / 残留审计 ----
print('\n残留审计（期望值见注释）：')
CHK = [('84e2de2', 0), ('模块整合与注册波', 0), ('认证面 221', 0), ('编译清单 221', 0),
       ('Live_X 333', 0), ('94486425397 @24431dc，COQCHK_ALL_PASS）', 0), ('333 Live_X', 0),
       ('HEAD=b657aff', 2)]   # 2 处＝范围外披露的历史时点锚（与论文1 同款保留）
ok2 = True
for pt, exp in CHK:
    n = txt.count(pt)
    flag = '✓' if n == exp else '✗'
    if n != exp: ok2 = False
    print('  %s %-42s 实测 %d（期望 %d）' % (flag, pt, n, exp))
print('\n新值出现次数（信息）：')
for pt in ['39d81aa', '246 模块', '356 个 .v', '246/246', 'CI #72', '228→246', 'Rocq/Coq 9.0/9.1']:
    print('  %-42s %d' % (pt, txt.count(pt)))
print('\n审计判定：', 'PASS' if ok2 else 'FAIL')
