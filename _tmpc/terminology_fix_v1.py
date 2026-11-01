# -*- coding: utf-8 -*-
"""术语规范修订 v1（轻参考 评审报告-002）。
- 在每篇 §1.2 术语约定后插入统一术语表（Glossary）
- 在摘要/核心声明处把「零全局公理」「零 Admitted」改为精确口径
- P3: 实值回填→字段级实例化；证明依赖静态表→证明结构示意；C-CoRN 应用层接口措辞对齐
- P2: premise-free→无附加前提（premise-free）
遵循工程铁律：先备份 bk4_*.md，with 写回，回读断言。
"""
import io, os, hashlib

BASE = r"D:\ComplexAnalysis\ConstructiveWorld\演变\相关论文"
OUT  = r"D:\ComplexAnalysis\ConstructiveWorld-Main\_tmpc"
PAPERS = {
 "P1": "论文1-构造性ML对齐统一形式化-正式版.md",
 "P2": "论文2-自由能原理与注意力Gibbs桥-正式版.md",
 "P3": "论文3-构造性柯西实数指数正性-正式版.md",
 "P4": "论文4-资源受限收敛动力学与PCT-正式版.md",
}

CORE_GLOSSARY = """**术语表（Glossary）**。下表集中定义正文高频重载术语的精确口径，全文统一按此使用：

| 术语 | 精确口径 |
|---|---|
| 零全局公理 | 库内无顶层 `Axiom`/`Parameter`/`Conjecture`；接口层 `Variable` 与字段假设已显式声明为定理前件，不作为全局公理。 |
| 零 `Admitted` 命令 | 全文行首 `Admitted`/`admit` 零出现（无未证结论）；并列的 `Abort` 同样零出现。 |
| CLEAN | `Print Assumptions` 返回 *Closed under the global context*：因 `End Section` 将接口假设 `RI` 泛化为定理显式前件，故零公理依赖；CLEAN 不等于抽象层已零假设重证。 |
| 字段级实例化（field-level instantiation） | Setoid 系接口实例把接口字段填为具体 `Real` 层已证引理的值（如 `exp_neg_pos := cauchy_real_exp_pos`）。 |
| 定理级签名迁移（theorem-level signature migration） | 把以 `forall {RI : RealInterfaceEnhanced}` 陈述的抽象 Id 系定理改以 setoid 相等谓词 `req` 重述并重证。 |
| 两层解除口径（Two-level Discharging） | 上述（i）字段级实例化与（ii）定理级签名迁移两层语义口径的统称。 |
"""

GLOSSARY = {
 "P1": CORE_GLOSSARY,
 "P2": CORE_GLOSSARY + "| 无附加前提主定理（premise-free） | 在抽象接口假设下陈述、不附加库内未证前提的主定理；其前提为接口层已声明假设，非额外未证命题。 |\n",
 "P3": CORE_GLOSSARY + "| 应用层接口字段 | 把具体实数模型的超越函数正性（如 `exp_neg_pos`）组织为可实例化的接口字段，供下游应用定理（Boltzmann/softmax/RLHF）以接口字段声明假设并实例化（§1.1、§8.2）。 |\n",
 "P4": CORE_GLOSSARY + "| 资源受限（explicit iteration budget） | 严格含义为「显式迭代预算」：对给定容差 ε>0 构造性给出满足闭式条件 `log(a·κ^N) ≤ log ε` 的 N；不覆盖位精度、内存或复杂度类资源（§1.1 术语）。 |\n",
}

# 在 §1.3 节标题之前插入术语表（避免割裂多行术语约定段落）
HEADING_ANCHOR = {
 "P1": "### 1.3 论文结构",
 "P2": "### 1.3 论文结构",
 "P3": "### 1.3 Artifact 版本说明",
 "P4": "### 2.5 与 Banach 不动点形式化的关系",
}

# 定向替换：(old, new, replace_all?)
REPL = {
 "P1": [
   ("全部结果满足零全局公理、零 Admitted、零 Abort。",
    "全部结果满足零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）、零 `Abort`。", False),
   ("纯构造性 Coq、零全局公理、Set 层信息性证明与可提取 OCaml",
    "纯构造性 Coq、零全局公理（接口层 Variable 假设已显式声明）、Set 层信息性证明与可提取 OCaml", False),
   ("对 RLHF/DPO/PPO/GRPO 四族单步对齐目标理论给出零全局公理的机器检查统一",
    "对 RLHF/DPO/PPO/GRPO 四族单步对齐目标理论给出零全局公理（接口层 Variable 假设已显式声明）的机器检查统一", False),
 ],
 "P2": [
   ("零全局公理、零 Admitted",
    "零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）", True),
   ("（纯构造性、零全局公理）",
    "（纯构造性、零全局公理（接口层 Variable 假设已显式声明））", False),
   ("premise-free", "无附加前提（premise-free）", True),
 ],
 "P3": [
   ("在零全局公理、零 Admitted 下闭合",
    "在零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）下闭合", False),
   ("实值回填", "字段级实例化", True),
   ("**证明依赖静态表**", "**证明结构示意**", False),
   ("未提供「把某具体实数模型的指数正性回填为下游应用定理（Boltzmann/softmax/RLHF）的假设字段」这一应用层接口",
    "未把指数正性组织为可实例化的接口字段（即 §1.1 定义的字段级实例化）", False),
 ],
 "P4": [
   ("全部结论在零全局公理、零 Admitted、零 Abort 的构造性纪律下给出",
    "全部结论在零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）、零 `Abort` 的构造性纪律下给出", False),
   ("零全局公理、零 Admitted、零 Abort——该纪律指",
    "零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）、零 `Abort`——该纪律指", False),
   ("四件均为纯构造性、零全局公理、零 `Admitted`",
    "四件均为纯构造性、零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）", True),
   ("零全局公理、零 Admitted；",
    "零全局公理（接口层 Variable 假设已显式声明）、零 `Admitted` 命令（行首 `Admitted`/`admit` 零出现）；", False),
 ],
}

def sha256(path):
    return hashlib.sha256(open(path,'rb').read()).hexdigest()

report = []
for pid, fname in PAPERS.items():
    src = os.path.join(BASE, fname)
    txt0 = open(src, encoding='utf-8').read()
    # 1) 备份 bk4
    bk = os.path.join(OUT, f"bk4_{pid.lower()}.md")
    with io.open(bk, 'w', encoding='utf-8', newline='') as f:
        f.write(txt0)
    # 2) 插入术语表（在 §1.3 节标题之前）——幂等：已存在则跳过
    heading = HEADING_ANCHOR[pid]
    if heading not in txt0:
        raise SystemExit(f"[{pid}] 节标题锚未命中：{heading!r}")
    if "术语表（Glossary）" not in txt0:
        t = txt0.replace(heading, "\n" + GLOSSARY[pid] + "\n" + heading, 1)
        report.append(f"[{pid}] glossary inserted before {heading!r}")
    else:
        t = txt0
        report.append(f"[{pid}] glossary already present, skip")
    # 3) 定向替换——幂等：old 已不存在且 new 已存在则跳过
    for old, new, ra in REPL[pid]:
        cnt = t.count(old)
        if cnt == 0:
            if new in t:
                report.append(f"[{pid}] already applied, skip: {old[:24]!r}")
                continue
            raise SystemExit(f"[{pid}] 替换目标未命中：{old!r}")
        if ra:
            t = t.replace(old, new)
        else:
            t = t.replace(old, new, 1)
        report.append(f"[{pid}] replace x{cnt}: {old[:30]!r}")
    # 4) 回读校验：被彻底删除的词应归零（premise-free 保留于中文 gloss 括号内，不要求归零）
    for old, new, ra in REPL[pid]:
        if old in ("实值回填", "**证明依赖静态表**"):
            assert t.count(old) == 0, f"[{pid}] 残留下: {old!r}"
    # premise-free 应全部转为「无附加前提（premise-free）」形态
    if pid == "P2":
        assert t.count("无附加前提（premise-free）") >= 1, f"[P2] premise-free 未转换"
    # 5) with 写回 + 回读断言
    with io.open(src, 'w', encoding='utf-8', newline='') as f:
        f.write(t)
    with io.open(src, encoding='utf-8') as f:
        rb = f.read()
    assert rb == t, f"[{pid}] 写回不一致"
    assert "术语表（Glossary）" in rb, f"[{pid}] 术语表缺失"
    nl = rb.count('\n') + 1
    report.append(f"[{pid}] OK  sha={sha256(src)[:16]}  lines={nl}  bk={os.path.basename(bk)}")

print("\n".join(report))
print("\nALL DONE")
