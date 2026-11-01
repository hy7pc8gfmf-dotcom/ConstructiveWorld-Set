# -*- coding: utf-8 -*-
"""回归校验：论文新引入的模块层标识符是否真实存在，并回填精确行号。"""
import os, re, glob, sys

LIVE = r'D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live'
BASE = r'D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文\分析论文'
PAPERS = ['论文1-构造性ML对齐统一形式化-正式版.md',
          '论文2-自由能原理与注意力Gibbs桥-正式版.md',
          '论文3-构造性柯西实数指数正性-正式版.md',
          '论文4-资源受限收敛动力学与PCT-正式版.md']

# 建立 模块 -> 源码文本 与 全局名 -> (模块,行号)
mods = {}
decl = {}
DECL = re.compile(r'(?m)^[ \t]*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Program|Export)\s+)*'
                  r'(?:Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Definition|Fixpoint|'
                  r'CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Variant)\s+'
                  r'([A-Za-z_][A-Za-z0-9_\']*)')
# Class 字段名也算
FIELD = re.compile(r'(?m)^[ \t]*([a-z_][A-Za-z0-9_\']*)\s*:\s')
for f in sorted(glob.glob(LIVE + '/*.v')):
    name = os.path.basename(f)[:-2]
    txt = open(f, encoding='utf-8', errors='replace').read()
    mods[name] = txt
    for m in DECL.finditer(txt):
        ln = txt[:m.start()].count('\n') + 1
        decl.setdefault(m.group(1), []).append((name, ln))
    for m in FIELD.finditer(txt):
        ln = txt[:m.start()].count('\n') + 1
        decl.setdefault(m.group(1), []).append((name, ln))

# 本轮修订新引入的标识符
NEW = {
 'P1(论文1)': ['UpStepKLM3','real_iter_kl_geom','real_iter_step_geom_eps','KLWallClosed',
               'klc_closed_powb_mono','klc_le_mult_r_weak','klc_strict_branch',
               'PinskerTwoPoint','p2_pinsker_witness_b','p2_kl2_nonneg_b',
               'SupKLBound','skb_sup_kl_log_inv_min'],
 'P2(论文2)': ['AttnLogSumExpBound','attn_logit_le_log_partition','attn_log_partition_bound',
               'attn_tilted_eq','FreeEnergyKLGap','fekl_gap_decomp_general','fekl_fep_gap_le_b',
               'fekl_fep_gap_canonical_le_b','fekl_fep_gap_eps','fekl_sf_vfe_ge_complexity_B'],
 'P3(论文3)': ['UpReqCStarDef','CStarAlg','cst_star','cst_star_add','cst_star_mult','cst_star_star',
               'cst_star_one','cst_star_coef','cst_norm_sq','cst_star_zero','cst_star_opp',
               'cst_norm_star','cst_d_geo12','cst_newton_rate','cst_newton_alg','cst_pos',
               'cst_pos_selfadj','cst_star_preserves_pos','cst_star_residual'],
 'P4(论文4)': ['UpBudgetReal','r_arch_pow_real','budget_cond_sufficient','geo_tail_budget','budget_min_tail'],
}

print('=' * 96)
print('模块层标识符存在性校验')
print('=' * 96)
allok = True
for tag, names in NEW.items():
    print('\n【%s】' % tag)
    for n in names:
        if n in mods:                       # 模块名
            print('  ✓ %-34s 模块（%d 行）' % (n, mods[n].count('\n') + 1)); continue
        if n in decl:
            ms = decl[n]
            s = ', '.join('%s:%d' % (m, l) for m, l in ms[:3])
            print('  ✓ %-34s %s%s' % (n, s, ' …(%d处)' % len(ms) if len(ms) > 3 else ''))
        else:
            allok = False
            print('  ✗ %-34s 未找到' % n)
print()
print('=' * 96)
print('总判定：', 'ALL PRESENT' if allok else '存在未找到项')
print('=' * 96)

# 论文中是否残留被排除的旧措辞
print('\n旧措辞残留检查（应为 0）：')
BAD = ['Real 层闭式载体待建', 'Real 层闭式 N 为续作', '迭代率的 Real 层镜像为开放项',
       'C*-代数正性', '库内无此材料', '不构成 §9.2 未复刻清单的闭合']
for fn in PAPERS:
    txt = open(os.path.join(BASE, fn), encoding='utf-8').read()
    hits = [b for b in BAD if b in txt]
    print('  %-46s %s' % (fn[:44], '○ 干净' if not hits else '⚠ 残留: %s' % hits))
