#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
闸④ 头注五字段机检守卫 · 扩展版 v2.1（GATE4-EXT 20260925｜词面族谱＋三域＋判定原则
＋v2.1 vo 树盲区升级 GATE4-AUDIT 20260925）
====================================================================================
承 v1.0（_tgate4_ws\\gate4_comment_guard.py，五检项）扩展，主会话清洗规则扩展令＋
包装协议 v2 条款 I（注释卫生 v1.1 清洗规则扩展）的机械化。零编译零网络零树写。
判定原则（兜底，凌驾词面）：注释唯一受众＝无项目内部上下文的国际数学/形式化读者——
凡需了解项目内部组织/战役/席位/会话历史才能理解的注释＝违规。

v2.0 扩展 diff（对 v1.0）：
  [E1] 词面族谱五族全量内嵌——战役组织族/工程隐喻族/过程叙述族/口语非正式族/
       英文俚语族（62/65 禁词之外净新增，源＝条款 I v1.1＋E-STAGING-CMT-JARGON）。
       长词优先/零消费豁免/组装守卫照旧；全扫描器统一 claimed-interval 去重
       （v1.0 中 落刀 类同词被禁词层＋战役层双计——v2.0 单词面单计）。
  [E2] 三域覆盖——文件头注（A 区）/证明体内注释（Proof..Qed 区间）/子结构头注
       （Module/Section/Record/Instance/Class 头部直接附着注释块）逐域分类报告；
       其余注释块归「体内散块」域照扫（覆盖不缩水）。命中带域标签。
  [E3] 判定原则模式（--principle 默认开；--no-principle 关）——词面未中但命中
       「内部上下文依赖」启发式（批次序号叙述/md5 账面/年份＋过程语同现/
       文件名进度账/内部组织语残面）→ review 级人工复核清单（不硬红，exit 2）。
  [E4] 正面自审豁免扩展——axiom-free／零公理／无公理 类不误报（v1.0 的
       「零 Axiom／Axioms: none」豁免保留；E962 口径：英文 zero-admit 字面仍违，
       改写义务＝中文表述，不放豁免）。
  [E5] v1.0 缺陷修复（响亮登记）：_iter_comment_lines 行首表重复扫描——每条注释行
       被二次产出且第二遍行号错位（幻影行号/命中数近似翻倍：UpReqIndex 禁词
       338(普查)→678(v1.0) 直证）。v2.0 单遍修复，行号守恒。

v1.0 五检项照旧全保留：[1]头注五字段 [2]禁词(65 词面) [3]承认式英文词面
[4]三类禁写(席次/战役/更新日志) [5]头注超标＋.(* 词法陷阱附检。

v2.1 盲区升级（GATE4-AUDIT 20260925）：
  [U1] --tree-recursive DIR（可多次）——递归深扫该树全部子目录内 .v（顶层
       件与 --tree 同口径并入）。堵 vo 树子目录探针件盲区（实测 18 子目录
       22 件 .v 逃出非递归扫描域，CI 同盲区）。默认行为零变：只用 --tree
       时非递归平扫照旧、警示照旧、退出码语义不变（0/1/2）。跨来源路径
       去重（同件只扫一次），逐树件数台账入 --json meta.trees_ledger。
       与 gate1 双树先例对齐：多 --tree/--tree-recursive 显式传树，不做隐式递归。

v2.2 台账机读化（GATE4-LEDGER 20260926｜承 YELLOW-CALIBER 黄面口径对表报告 §三
机读化建议）：
  [L1] --emit-ledger PATH——扫描时同步出机读豁免台账 JSON（gate4_exempt_ledger
       schema v1：语境双义复核桶逐项 file/line/domain/rule/word/reason/
       exemption_status/first_registry/verdict_impact/suggested_action/
       file_verdict/detail，附 attested_by〔scan_time/tool_md5/ledger_tsv_md5〕）。
       豁免状态=命中权威台账 TSV（--ledger-tsv 显式传；默认找本脚本同目录
       carrier_exemption_ledger_final.tsv——缺席即 FATAL exit 2，禁静默降级）。
       纯附加：不带参时输出与 v2.1 逐字节一致（运行时版本串冻结「v2.1 EXT」
       承字节兼容铁律；v2.2 标识由台账 JSON schema 字段自证），不改
       verdict/退出码语义。

退出码：0=PASS；1=违规（硬命中）；2=无法判定（仅复核项〔含原则启发式〕/路径无效/IO 错误）。

用法（v1.0 CLI 全兼容）：
  python gate4_comment_guard.py --file A.v [--file B.v ...]
  python gate4_comment_guard.py --tree DIR [--tree DIR2 ...] [--json OUT]
  python gate4_comment_guard.py --tree DIR --baseline _tcmtsurvey_phase1_result.json
  v2.0 新增：--no-principle（关判定原则启发式）
  v2.1 新增：--tree-recursive DIR（递归深扫，堵子目录盲区）
"""
import os, re, sys, json, argparse, datetime

# ------------------------------------------------------------- 词面族谱 ----
# 基座：白皮书 §4 全禁词成文总表 65 词面（词表权威，逐字承 v1.0）
FAMILY_BASE = "白皮书§4·65禁词"
BANNED_WORDS = [
    "承重墙", "拍平", "接线", "垫片", "总装", "打包", "定谳", "挂账",
    "消费", "探针", "清盘", "旗舰", "搬运", "封口", "记账", "派发",
    "喂参", "收口", "直配", "直喂", "增薄", "机判", "墙位", "墙账",
    "合龙", "摘牌", "计功", "缝合", "双杀", "回收", "换装", "账目",
    "机械化", "舞步", "环账", "簿记", "卸出", "收编", "判词", "宣言",
    "实勘", "装机", "击坠", "收割", "翻牌", "上车", "同车", "底座",
    "地基件", "母件", "母本", "墙槽", "喂入", "投喂", "登记件",
    "正侧支", "负侧支", "脱余量", "工作马", "死亡证书", "哨兵",
    "槽位", "放电", "镜像", "组装机", "两腿", "塌缩腿",
]

# 扩展五族（条款 I v1.1＋E-STAGING-CMT-JARGON 开放清单；只收 mandate 词面，
# 与基座去重后的净新增；E992 账族/别名族等候选入报告卡建议，不入硬表——
# E-STAGING-TCMTJUDGE3 纪律：词表扩口走白皮书 §4 回填候选，机检不越权硬判）
FAMILY_BATTLE = "战役组织族"
FAMILY_METAPHOR = "工程隐喻族"
FAMILY_NARRATE = "过程叙述族"
FAMILY_COLLOQ = "口语非正式族"
FAMILY_SLANG = "英文俚语族"

EXT_WORD_FAMILIES = {
    FAMILY_BATTLE: {
        # 席/本席/前席/姊妹席 已由 SEAT_RE 泛匹配；战役 v1.0 BATTLE_RE 已收
        "words": ["波次", "批次"],
        "regex": [(re.compile(r"\bR\d{2,4}\b(?![\d.])"), "R编号")],
    },
    FAMILY_METAPHOR: {
        "words": [
            "落位", "回潮", "撕裂", "哑弹", "冰川", "幽灵", "金丝雀", "让道",
            "独占窗", "硬闸", "断根", "枢纽", "叶件", "桥件", "壳线",
            "供给件", "伴生件", "旗件", "伞件", "锚定", "回写", "身换壳留",
            "休眠水库", "外道", "红温", "硬凑", "咬合", "假绿", "假红", "秒红",
            "卡死", "撞墙", "塌缩", "沉淀", "提炼", "融合", "承接", "接力",
            "接管", "尾插", "换体", "腰斩", "亮红", "红屏", "全绿", "咬死",
        ],
        "regex": [],
    },
    FAMILY_NARRATE: {
        "words": ["前述", "复验", "复测", "复扫"],
        "regex": [(re.compile(r"\b(?:[01]\d|2[0-3]):[0-5]\d(?::[0-5]\d)?\b"), "时间戳")],
    },
    FAMILY_COLLOQ: {
        "words": ["炸了", "打错", "漏网", "翻车", "踩坑"],
        "regex": [],
    },
    FAMILY_SLANG: {
        "words": [],
        "regex": [(re.compile(r"\bFIXME\b"), "FIXME"),
                  (re.compile(r"\bXXX\b"), "XXX"),
                  (re.compile(r"\bHACK\b"), "HACK"),
                  (re.compile(r"\bworkaround\b", re.I), "workaround")],
    },
}

# 长词优先合并（组装机>装机；塌缩腿>塌缩；身换壳留/休眠水库 最长——v2.0 新解）
_ALL_WORDS = [(w, FAMILY_BASE) for w in BANNED_WORDS]
for fam, spec in EXT_WORD_FAMILIES.items():
    _ALL_WORDS.extend((w, fam) for w in spec["words"])
_ALL_WORDS_SORTED = sorted(set(_ALL_WORDS), key=lambda p: len(p[0]), reverse=True)
UNIFIED_RE = re.compile("|".join(re.escape(w) for w, _ in _ALL_WORDS_SORTED))
WORD_FAMILY = {w: fam for w, fam in _ALL_WORDS_SORTED}

# 正则族合并（命名组定位归属）
_EXT_REGEX_SPECS = []
for _fam, _spec in EXT_WORD_FAMILIES.items():
    for _p, _lbl in _spec["regex"]:
        _EXT_REGEX_SPECS.append((_fam, _lbl, _p))
_EXT_REGEX_RES = [p for (_f, _l, p) in _EXT_REGEX_SPECS]
EXT_BANNED_RE = re.compile("|".join(f"(?P<g{i}>{p.pattern})"
                                    for i, p in enumerate(_EXT_REGEX_RES)))

REVIEW_ONLY_WORDS = {"腿"}  # 单字残余按语境——复核级（承 v1.0）
# 语境双义词（v2.0）：词表在册（mandate 工程隐喻族），但实测存在数学合法用法——
# 复核级不硬红（E992「预算」双义同款纪律；直证：载体供给节/典范 Real 载体 carrier 用法
# 105 处，见 GATE4-EXT 报告 §三。候选回填白皮书 §4 裁决前按复核级扫出）。
CONTEXT_REVIEW_WORDS = {"载体": "语境双义（数学 carrier／工程隐喻）——人工复核"}

# 席次语汇（承 v1.0）：任意 ≤12 连续词字符后接「席」
SEAT_RE = re.compile(r"[0-9A-Za-z\u4e00-\u9fff]{0,12}席")

# 战役/波次过程词表（承 v1.0，含横幅族/批波包号/Tnnn/任务书引用）
BATTLE_RE = re.compile(
    r"战役|台账|立项|在飞|落刀|落树|回填|回刷|核销|收官|终版|补植|补登|"
    r"清偿|建席|任务书|GO 文书|GO文书|横幅|本波|本轮|勘误|更正|"
    r"批\d+|波\d+|包[A-Z](?![A-Za-z])|T\d{2,3}(?!\d)"
)

# 更新日志模式（承 v1.0）
DATE_PATTERNS = [
    (r"20\d{2}[-/.]\d{1,2}[-/.]\d{1,2}", "日期戳"),
    (r"20\d{2}年\d{1,2}月\d{1,2}日", "日期戳"),
    (r"\b20\d{6}\b", "日期戳"),
    (r"v\d+\.\d+(?![\d.])", "版记版本戳"),
    (r"更新日志|本轮改动|修正记录|修订历史|改动清单", "更新日志段"),
]
DATE_RES = [(re.compile(p), t) for p, t in DATE_PATTERNS]

# 判定原则启发式（v2.0 [E3]）——review 级，只对词面未中行生效
PRINCIPLE_VERBS = ("清洗", "改写", "复扫", "返工", "落树", "开工", "收官", "收口",
                   "落刀", "补刀", "候清", "已清", "在飞", "回写", "整改")
PRINCIPLE_RES = [
    (re.compile(r"[上下前次该后本]\s*批|[上下前次该后本]\s*波|第\s*[0-9一二三四五六七八九十百]+\s*[批波轮](?![日号])"),
     "批次序号叙述(原则)"),
    (re.compile(r"\b[0-9a-fA-F]{32}\b"), "md5账面(原则)"),
    (re.compile(r"\bE\d{3,4}\b(?![\d.])"), "卡号引述(原则)"),
    (re.compile(r"工单|派单|挂单|断点|交棒|回执|白名单|四关|四件套|born-in-place|收账|盯守|停写令|对表"),
     "内部组织语(原则)"),
]
# 双条件原则（同现才判）：文件名＋进度语／年份＋过程语——防编译配方行误伤
PRINCIPLE_FILE_RE = re.compile(r"[A-Za-z0-9_]+\.(?:v|vo)\b")
PRINCIPLE_YEAR_RE = re.compile(r"20\d{2}(?![\d/-])")
PRINCIPLE_VERB_RE = re.compile("|".join(PRINCIPLE_VERBS))

# 承认式英文词面（承 v1.0）＋ v2.0 [E4] 豁免扩展
ADMIT_RE = re.compile(r"\b(Axioms?|Admitted|admit|parameter|conjecture|abort|hypothesis)\b")
ADMIT_EXEMPT_RE = re.compile(r"零|无|none|None|NONE|Axioms?\s*[:：]")
ADMIT_EXEMPT_EXT_RE = re.compile(          # v2.0：axiom-free／零公理 类正面自审
    r"axiom\s*[-–—]?\s*free|零\s*公理|无\s*公理|公理自由|Axioms?\s*[:：]\s*none", re.I)

# 五字段标签（承 v1.0）
FIELD_SPECS = [
    ("使命", re.compile(r"使命(?:行)?(?:\s*(?:（|\()[^）)]*(?:）|\)))?\s*[:：]|Mission\s*\.")),
    ("依赖", re.compile(r"依赖(?:清单)?(?:\s*(?:（|\()[^）)]*(?:）|\)))?\s*[:：]|Dependencies\s*\.")),
    ("对标", re.compile(r"对标(?:行)?(?:\s*(?:（|\()[^）)]*(?:）|\)))?\s*[:：]|References\s*\.")),
    ("构造性", re.compile(r"构造性(?:注记)?(?:\s*(?:（|\()[^）)]*(?:）|\)))?\s*[:：]|Constructivity\s*\.")),
    ("编译", re.compile(r"编译配方(?:\s*(?:（|\()[^）)]*(?:）|\)))?\s*[:：]|Build\s*\.")),
]
OPTIONAL_FIELDS = {"对标"}
MISSION_HEURISTIC_RE = re.compile(r"本件形式化|形式化.{0,30}性质")

# ---- 三域识别（v2.0 [E2]） ----
STRUCT_DECL_RE = re.compile(r"^\s*(Module|Section|Record|Instance|Class)\b")
PROOF_START_RE = re.compile(r"^\s*Proof\b")
PROOF_END_RE = re.compile(r"^\s*(Qed|Defined|Abort|Admitted|Save)\b")
DOM_HEADER = "头注"
DOM_PROOF = "证明体内"
DOM_SUBSTRUCT = "子结构头注"
DOM_BODY = "体内散块"


def extract_comments(text):
    """(* *) 嵌套感知抽取注释块（承 v1.0，行号守恒）。"""
    blocks = []
    comment_pos = set()
    i, n = 0, len(text)
    line = 1
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if text.startswith("(*", i):
            start_line = line
            depth = 0
            seg_start = i
            while i < n:
                if text.startswith("(*", i):
                    depth += 1
                    comment_pos.add(i)
                    comment_pos.add(i + 1)
                    i += 2
                    continue
                if text.startswith("*)", i):
                    depth -= 1
                    comment_pos.add(i)
                    comment_pos.add(i + 1)
                    i += 2
                    if depth == 0:
                        break
                    continue
                if text[i] == "\n":
                    line += 1
                    comment_pos.add(i)
                else:
                    comment_pos.add(i)
                i += 1
            blocks.append((start_line, line, text[seg_start:i]))
            continue
        i += 1
    return blocks, comment_pos


def header_region(text):
    """头注区=自文件首个非空白字符起的连续注释块（承 v1.0）。"""
    blocks, _ = extract_comments(text)
    if not blocks:
        return [], False, 0, 0
    hdr = []
    prev_end = 0
    for (s, e, t) in blocks:
        if not hdr:
            hdr.append((s, e, t))
            prev_end = e
            continue
        if _lines_between(text, prev_end, s):
            break
        hdr.append((s, e, t))
        prev_end = e
    first_at_1 = hdr[0][0] == 1
    end_line = hdr[-1][1]
    return hdr, first_at_1, end_line, end_line


def _lines_between(text, start_line, end_line):
    lines = text.splitlines()
    for ln in range(start_line + 1, end_line):
        if 0 <= ln - 1 < len(lines) and lines[ln - 1].strip():
            return True
    return False


def _iter_comment_lines(text, comment_pos):
    """产出 (line_no, 行文本)。v2.0 修复 v1.0 行首表重复扫描缺陷（原实现把
    line_starts 构建循环跑了两遍→注释行二次产出且第二遍行号错位/幻影行号）。"""
    line_starts = [0]
    for idx, ch in enumerate(text):
        if ch == "\n":
            line_starts.append(idx + 1)
    out = []
    total = len(line_starts)
    for ln, ls in enumerate(line_starts, 1):
        le = line_starts[ln] if ln < total else len(text)
        has_comment = any((ls + k) in comment_pos for k in range(le - ls))
        if has_comment:
            out.append((ln, text[ls:le]))
    return out


def _code_line_map(text, comment_pos):
    """逐行代码面文本（剥注释字符）。返回 {line: code_only_text}。"""
    line_starts = [0]
    for idx, ch in enumerate(text):
        if ch == "\n":
            line_starts.append(idx + 1)
    total = len(line_starts)
    out = {}
    for ln, ls in enumerate(line_starts, 1):
        le = line_starts[ln] if ln < total else len(text)
        buf = []
        for k in range(ls, le):
            if text[k] != "\n" and k not in comment_pos:
                buf.append(text[k])
        out[ln] = "".join(buf)
    return out


def domain_map(text, blocks, comment_pos, hdr_line_span):
    """v2.0 [E2] 三域识别。返回 (line_domain, proof_regions, struct_decls)。
    域优先序：头注 > 证明体内 > 子结构头注 > 体内散块。块按首行域整块归类。"""
    lines = text.splitlines()
    n_lines = len(lines)
    code = _code_line_map(text, comment_pos)
    # 证明区间：Proof. 起，Qed/Defined/Abort/Admitted/Save 止（Coq 证明不嵌套）
    proof_regions = []
    in_proof = False
    proof_start = 0
    for ln in range(1, n_lines + 1):
        cl = code.get(ln, "")
        if not in_proof and PROOF_START_RE.match(cl):
            in_proof = True
            proof_start = ln
        elif in_proof and PROOF_END_RE.match(cl):
            proof_regions.append((proof_start, ln))
            in_proof = False
    if in_proof:
        proof_regions.append((proof_start, n_lines))
    # 子结构声明行（Module/Section/Record/Instance/Class）
    struct_decls = []
    for ln in range(1, n_lines + 1):
        m = STRUCT_DECL_RE.match(code.get(ln, ""))
        if m:
            struct_decls.append((ln, m.group(1)))

    def in_proof_region(ln):
        return any(s <= ln <= e for (s, e) in proof_regions)

    def blank_between(a, b):
        # 原文行号区间 (a, b) 开区间全空白
        return all(not lines[k].strip() for k in range(a, b - 1) if 0 <= k < n_lines)

    def attached_to_struct(s, e):
        for (d, _k) in struct_decls:
            if (e < d and blank_between(e, d)) or (s > d and blank_between(d, s)):
                return True
        return False

    line_domain = {}
    for (s, e, _t) in blocks:
        if any(l in hdr_line_span for l in range(s, e + 1)):
            dom = DOM_HEADER
        elif in_proof_region(s):
            dom = DOM_PROOF
        elif attached_to_struct(s, e):
            dom = DOM_SUBSTRUCT
        else:
            dom = DOM_BODY
        for l in range(s, e + 1):
            line_domain[l] = dom
    return line_domain, proof_regions, struct_decls


def _claim(start, end, claimed):
    """claimed-interval 去重：与已消费面重叠则 False（单词面单计）。"""
    for (a, b) in claimed:
        if start < b and a < end:
            return False
    claimed.append((start, end))
    return True


def check_file(path, length_cap=30, length_fail=False, principle=True):
    """扫描单件（v2.0）。verdict: PASS/FAIL/REVIEW/UNREADABLE；
    hard/review 条目=(line, domain, type, detail)。"""
    rep = {"file": path, "verdict": "PASS", "hard": [], "review": [],
           "header_fields": [], "header_lines": 0, "header_first_at_1": True,
           "domains": {}, "families": {}, "proof_regions": 0, "struct_decls": 0,
           "principle": principle}
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            raw = f.read()
    except OSError as e:
        rep["verdict"] = "UNREADABLE"
        rep["hard"] = [(0, "-", "IO-ERROR", str(e))]
        return rep

    blocks, comment_pos = extract_comments(raw)
    hdr, first_at_1, hdr_end, hdr_lines = header_region(raw)
    rep["header_first_at_1"] = first_at_1
    rep["header_lines"] = hdr_lines
    hdr_text = "\n".join(t for (_, _, t) in hdr)
    hdr_line_span = set()
    for (s, e, _t) in hdr:
        hdr_line_span.update(range(s, e + 1))

    line_domain, proof_regions, struct_decls = domain_map(
        raw, blocks, comment_pos, hdr_line_span)
    rep["proof_regions"] = len(proof_regions)
    rep["struct_decls"] = len(struct_decls)
    for dom in (DOM_HEADER, DOM_PROOF, DOM_SUBSTRUCT, DOM_BODY):
        rep["domains"][dom] = sum(1 for v in line_domain.values() if v == dom)

    comment_lines = _iter_comment_lines(raw, comment_pos)
    hard_lines = set()
    claims = {}  # line -> [(start,end)] 已消费词面区间（跨扫描器去重）

    def add_hard(ln, typ, detail, family=None):
        rep["hard"].append((ln, line_domain.get(ln, "-"), typ, detail))
        hard_lines.add(ln)
        if family:
            rep["families"][family] = rep["families"].get(family, 0) + 1

    def add_review(ln, typ, detail):
        rep["review"].append((ln, line_domain.get(ln, "-"), typ, detail))

    # ---- [1] 头注五字段（承 v1.0） ----
    if not blocks:
        rep["hard"].append((0, "-", "无头注", "文件无任何注释块"))
        hard_lines.add(0)
    else:
        if not first_at_1:
            add_hard(hdr[0][0], "头注非首块", f"头注起于 L{hdr[0][0]} 非 L1")
        found = []
        for name, rx in FIELD_SPECS:
            m = rx.search(hdr_text)
            if m:
                found.append(name)
            elif name == "使命" and MISSION_HEURISTIC_RE.search(hdr_text):
                found.append(name)
                add_review(hdr[0][0], "使命启发式",
                           "无「使命」标签，以「本件形式化」启发式判定存在——人工复核")
        rep["header_fields"] = found
        missing = [n for n, _ in FIELD_SPECS
                   if n not in found and n not in OPTIONAL_FIELDS]
        if missing:
            add_hard(hdr[0][0] if hdr else 1, "缺字段", ",".join(missing))
        order = [found.index(n) for n in found]
        if order != sorted(order):
            add_review(hdr[0][0], "字段顺序", f"实测序 {'<'.join(found)} ≠ 规范序")

    # ---- [2] 统一词面扫描（基座 65＋扩展五族；长词优先＋claimed 去重） ----
    for ln, line in comment_lines:
        cl = claims.setdefault(ln, [])
        for m in UNIFIED_RE.finditer(line):
            w = m.group(0)
            if not _claim(m.start(), m.end(), cl):
                continue  # 长词优先已消费（塌缩腿>塌缩 等）
            fam = WORD_FAMILY.get(w, FAMILY_BASE)
            # 「零消费」保留裁决豁免（承 v1.0）
            if w == "消费" and "零" in line[max(0, m.start() - 2):m.start()]:
                continue
            # 「组装机」守卫（承 v1.0）
            if w == "装机" and line[max(0, m.start() - 1):m.start()] == "组":
                continue
            add_hard(ln, "禁词", w, fam)
        for m in EXT_BANNED_RE.finditer(line):
            if not _claim(m.start(), m.end(), cl):
                continue
            gi = next(i for i in range(len(_EXT_REGEX_RES))
                      if m.group(f"g{i}") is not None)
            fam, label = _EXT_REGEX_SPECS[gi][0], _EXT_REGEX_SPECS[gi][1]
            add_hard(ln, "禁词(模式)", f"{label}:{m.group(0)}", fam)
        if not re.search(r"两腿|塌缩腿", line):
            if re.search(r"腿", line):
                add_review(ln, "禁词复核(语境)", "腿")
        for cw, note in CONTEXT_REVIEW_WORDS.items():
            if re.search(re.escape(cw), line):
                add_review(ln, "语境双义复核", f"{cw}（{note}）")

    # ---- [3] 承认式英文词面（豁免扩展 v2.0 [E4]） ----
    for ln, line in comment_lines:
        for m in ADMIT_RE.finditer(line):
            pre = line[max(0, m.start() - 12):m.start()]
            post = line[m.end():m.end() + 12]
            if ADMIT_EXEMPT_RE.search(pre):
                continue
            if ADMIT_EXEMPT_EXT_RE.search(pre) or ADMIT_EXEMPT_EXT_RE.search(
                    pre + m.group(0) + post):
                continue  # axiom-free／零公理 类正面自审——豁免（v2.0）
            add_hard(ln, "承认式词面", m.group(1), "承认式")

    # ---- [4] 三类禁写（承 v1.0：席次/战役/更新日志；claimed 跨层去重） ----
    for ln, line in comment_lines:
        cl = claims.setdefault(ln, [])
        m = SEAT_RE.search(line)
        if m and _claim(m.start(), m.end(), cl):
            add_hard(ln, "席次语汇", m.group(0), FAMILY_BATTLE)
        m = BATTLE_RE.search(line)
        if m and _claim(m.start(), m.end(), cl):
            add_hard(ln, "战役叙述", m.group(0), FAMILY_BATTLE)
        for rx, typ in DATE_RES:
            dm = rx.search(line)
            if dm:
                add_hard(ln, typ, dm.group(0), FAMILY_NARRATE)
                break

    # ---- [4e] 判定原则启发式（v2.0 [E3]，review 级，词面未中行限定） ----
    if principle:
        for ln, line in comment_lines:
            if ln in hard_lines:
                continue
            if not re.search(r"[\u4e00-\u9fff]", line):
                continue  # 纯代码/纯英文引述行不入原则（候裁人工）
            hit = None
            for rx, typ in PRINCIPLE_RES:
                mm = rx.search(line)
                if mm:
                    hit = (typ, mm.group(0))
                    break
            if hit is None:
                ym, vm = PRINCIPLE_YEAR_RE.search(line), PRINCIPLE_VERB_RE.search(line)
                fm = PRINCIPLE_FILE_RE.search(line)
                if ym and vm:
                    hit = ("年份+过程语(原则)", f"{ym.group(0)}+{vm.group(0)}")
                elif fm and vm:
                    hit = ("文件进度账(原则)", f"{fm.group(0)}+{vm.group(0)}")
            if hit:
                add_review(ln, hit[0], hit[1])

    # ---- [5] 头注超标（承 v1.0） ----
    if hdr_lines > length_cap:
        item = (1, DOM_HEADER, "头注超标", f"头注 {hdr_lines} 行 > 上限 {length_cap}")
        if length_fail:
            rep["hard"].append(item)
            hard_lines.add(1)
        else:
            rep["review"].append(item)

    # ---- 附：词法陷阱 .(* （承 v1.0） ----
    for m in re.finditer(r"\.\(\*", raw):
        ln = raw.count("\n", 0, m.start()) + 1
        rep["review"].append((ln, line_domain.get(ln, "-"), "词法陷阱",
                              ".(* 紧随句点（T3 席实证）"))

    if rep["hard"]:
        rep["verdict"] = "FAIL"
    elif rep["review"]:
        rep["verdict"] = "REVIEW"
    else:
        rep["verdict"] = "PASS"
    return rep


def scan_tree(tree):
    """非递归平扫（gate1 同款）——子目录存在即响亮警示。
    v2.2 [U2] `_*` 下划线守卫：下划线前缀件（沙箱/探针/临时件，素不在
    build/coqchk 认证面——cw_build/cw_chk 依 order 拓扑消费注册名）同样
    素不在注释卫生认证面；扫描域与认证面口径对齐（20260926，R134RB 判例：
    vo 树 15 件 `_*` 探针把闸拖入与认证面无关的红）。"""
    if not os.path.isdir(tree):
        return None, 0
    names = sorted(os.listdir(tree))
    subdirs = [n for n in names if os.path.isdir(os.path.join(tree, n))]
    if subdirs:
        print(f"[gate4ext] 警示(非递归)：树 {tree} 下有 {len(subdirs)} 个子目录未扫"
              f"（gate1 三树教训——如需子目录请逐个 --tree 传入，"
              f"v2.1 起可 --tree-recursive 深扫）: "
              f"{', '.join(subdirs[:8])}{'…' if len(subdirs) > 8 else ''}",
              file=sys.stderr)
    return [os.path.join(tree, n) for n in names
            if n.endswith(".v") and not n.startswith("_")], len(subdirs)


def scan_tree_deep(tree):
    """v2.1 [U1] 递归深扫：树顶层＋全部子目录内 .v（含嵌套层）。
    返回 (相对层标记路径列表, 子目录内件数, 触及子目录数)。"""
    if not os.path.isdir(tree):
        return None, 0, 0
    top = [os.path.join(tree, n) for n in sorted(os.listdir(tree))
           if n.endswith(".v") and not n.startswith("_")
           and os.path.isfile(os.path.join(tree, n))]
    deep, dirs_seen = [], set()
    for root, dirs, files in os.walk(tree):
        rel = os.path.relpath(root, tree)
        if rel == ".":
            continue
        dirs_seen.add(rel.split(os.sep)[0])
        for n in sorted(files):
            if n.endswith(".v") and not n.startswith("_"):
                deep.append(os.path.join(root, n))
    deep.sort()
    return top + deep, len(deep), len(dirs_seen)


def baseline_compare(results, baseline_path):
    """与普查 JSON 逐件对表（承 v1.0）。"""
    with open(baseline_path, encoding="utf-8") as f:
        census = json.load(f)
    by_name = {os.path.basename(rec["file"]): rec for rec in census}
    summary = {"matched": 0, "both_bad": 0, "both_ok": 0,
               "census_bad_guard_ok": 0, "guard_bad_census_ok": 0,
               "no_census_record": 0}
    per = []
    for r in results:
        name = os.path.basename(r["file"])
        rec = by_name.get(name)
        if rec is None:
            summary["no_census_record"] += 1
            per.append({"file": name, "note": "无普查记录"})
            continue
        summary["matched"] += 1
        census_bad = bool(rec.get("header_viol") or rec.get("body_viol")
                          or rec.get("banned") or rec.get("admit_lit"))
        guard_bad = r["verdict"] == "FAIL"
        guard_ok = r["verdict"] in ("PASS", "REVIEW")
        if census_bad and guard_bad:
            summary["both_bad"] += 1
            tag = "一致-双违规"
        elif (not census_bad) and guard_ok:
            summary["both_ok"] += 1
            tag = "一致-双洁净"
        elif census_bad and guard_ok:
            summary["census_bad_guard_ok"] += 1
            tag = "普查违规-守卫过（候查：已清洗新代件/口径差）"
        else:
            summary["guard_bad_census_ok"] += 1
            tag = "守卫违规-普查洁（响亮——机检/人工口径分歧，须逐条核对）"
        per.append({"file": name, "guard": r["verdict"], "tag": tag})
    return summary, per


def _md5_of_file(path):
    import hashlib
    with open(path, "rb") as f:
        return hashlib.md5(f.read()).hexdigest()


def load_exempt_tsv(tsv_path):
    """v2.2 [L1] 权威豁免台账 TSV 加载（黄面口径终稿，只读）。返回
    (in_force{(file, line): row}, hist{file: row})。行解析失锐（line 列非整数，
    含历史清偿账的「-」与列错位态）一律归 hist 文件级账——容错不静默：
    计数入台账 JSON meta，供人工对表。"""
    in_force, hist = {}, {}
    with open(tsv_path, encoding="utf-8") as f:
        header = f.readline().rstrip("\r\n").split("\t")
        for row in f:
            if not row.strip():
                continue
            cols = row.rstrip("\r\n").split("\t")
            if len(cols) < len(header):
                cols += [""] * (len(header) - len(cols))
            rec = dict(zip(header, cols))
            fname = rec.get("file", "")
            try:
                ln = int(rec.get("line", ""))
            except ValueError:
                reg = rec.get("first_registry", "") or rec.get("word", "")
                if not reg:
                    reg = "?"
                rec["_registry_fallback"] = reg
                hist.setdefault(fname, rec)
                continue
            in_force[(fname, ln)] = rec
    return in_force, hist


def emit_exempt_ledger(results, out_path, tsv_path, scan_time):
    """v2.2 [L1] --emit-ledger：扫描时同步出机读豁免台账 JSON。只消费
    review 桶「语境双义复核」项（CONTEXT_REVIEW_WORDS 桶，现盘=载体一词），
    纯附加零干预：不改 verdict/硬命中/退出码/stdout 既有行。"""
    in_force, hist = load_exempt_tsv(tsv_path)
    entries = []
    n_force = n_hist = n_new = 0
    for r in results:
        base = os.path.basename(r["file"].replace("\\", "/"))
        for item in r["review"]:
            ln, dom, typ, det = item[0], item[1], item[2], item[3]
            if typ != "语境双义复核":
                continue
            word = det.split("（", 1)[0]
            if (base, ln) in in_force:
                rec = in_force[(base, ln)]
                status, reg = "在册", rec.get("first_registry", "")
                action = "豁免有效——维持 REVIEW 不降档（豁免≠降档，黄面口径§三）"
                n_force += 1
            elif base in hist:
                rec = hist[base]
                status = "已清偿/词面重排"
                reg = rec.get("_registry_fallback", "")
                action = "历史在册已清偿——人工确认词面重排后豁免归档"
                n_hist += 1
            else:
                status, reg = "未登", ""
                action = "候选新登——人工复核后回填豁免台账 TSV"
                n_new += 1
            entries.append({
                "file": base, "line": ln, "domain": dom, "rule": typ,
                "word": word,
                "reason": "数学carrier；" + CONTEXT_REVIEW_WORDS.get(word, "语境双义"),
                "exemption_status": status, "first_registry": reg,
                "verdict_impact": "REVIEW(豁免≠降档)",
                "suggested_action": action,
                "file_verdict": r["verdict"], "detail": det,
                "source_path": r["file"],
            })
    out = {
        "schema": "gate4_exempt_ledger v1",
        "generated_by": "gate4_comment_guard.py --emit-ledger (运行时串 v2.1 EXT)",
        "scan_time": scan_time,
        "attested_by": {
            "scan_time": scan_time,
            "tool_md5": _md5_of_file(os.path.abspath(__file__)),
            "ledger_tsv": tsv_path,
            "ledger_tsv_md5": _md5_of_file(tsv_path),
        },
        "counts": {"entries": len(entries), "在册": n_force,
                   "已清偿/词面重排": n_hist, "未登": n_new,
                   "tsv_in_force_rows": len(in_force), "tsv_hist_files": len(hist)},
        "entries": entries,
    }
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    print(f"[gate4ext] LEDGER 已写 {out_path}: 共 {len(entries)} 项"
          f"（在册 {n_force}／已清偿 {n_hist}／未登 {n_new}）；"
          f"台账 TSV={tsv_path}")


def main():
    ap = argparse.ArgumentParser(description="gate4 头注五字段机检守卫 扩展版 v2.1")
    ap.add_argument("--file", action="append", default=[], help="单件扫描（可多次）")
    ap.add_argument("--tree", action="append", default=[], help="树平扫（非递归，可多次）")
    ap.add_argument("--tree-recursive", dest="tree_recursive", action="append", default=[],
                    help="树深扫（递归含子目录 .v，v2.1 盲区升级，可多次）")
    ap.add_argument("--baseline", default=None, help="普查结果 JSON（对表模式）")
    ap.add_argument("--length-cap", type=int, default=30, help="头注行数上限（默认 30）")
    ap.add_argument("--length-fail", action="store_true", help="超标升格硬违规（默认复核级）")
    ap.add_argument("--no-principle", action="store_true",
                    help="关闭判定原则启发式（默认开——review 级不硬红）")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--emit-ledger", dest="emit_ledger", metavar="PATH", default=None,
                    help="v2.2：同步出机读豁免台账 JSON（语境双义复核桶；默认关，零变）")
    ap.add_argument("--ledger-tsv", dest="ledger_tsv", metavar="PATH", default=None,
                    help="v2.2：权威豁免台账 TSV（默认=本脚本同目录 "
                         "carrier_exemption_ledger_final.tsv）")
    args = ap.parse_args()

    paths = list(args.file)
    ledger = []          # v2.1 逐树件数台账（入 --json meta.trees_ledger）
    for t in args.tree:
        plist, _nsub = scan_tree(t)
        if plist is None:
            print(f"[gate4ext] FATAL: 树不存在: {t}", file=sys.stderr)
            return 2
        paths.extend(plist)
        ledger.append({"tree": t, "mode": "flat", "files": len(plist),
                       "subdir_files": 0, "subdirs": _nsub})
    deep_count = 0
    for t in args.tree_recursive:
        plist, ndeep, ndir = scan_tree_deep(t)
        if plist is None:
            print(f"[gate4ext] FATAL: 树不存在: {t}", file=sys.stderr)
            return 2
        paths.extend(plist)
        deep_count += ndeep
        ledger.append({"tree": t, "mode": "recursive", "files": len(plist) - ndeep,
                       "subdir_files": ndeep, "subdirs": ndir})
        print(f"[gate4ext] v2.1 深扫 {t}: 顶层 {len(plist) - ndeep} ＋ 子目录 {ndeep} 件"
              f"（{ndir} 个子目录）", file=sys.stderr)
    # v2.1 跨来源去重：--tree 与 --tree-recursive 顶层重叠面同件只扫一次
    seen, uniq = set(), []
    for p in paths:
        k = os.path.normcase(os.path.normpath(os.path.abspath(p)))
        if k not in seen:
            seen.add(k)
            uniq.append(p)
    if len(uniq) != len(paths):
        print(f"[gate4ext] v2.1 去重 {len(paths) - len(uniq)} 件"
              f"（双口径顶层重叠，避免同件双计）", file=sys.stderr)
    paths = uniq
    if not paths:
        print("[gate4ext] FATAL: 未指定 --file/--tree", file=sys.stderr)
        return 2

    now = datetime.datetime.now().isoformat(timespec="seconds")
    principle = not args.no_principle
    results = [check_file(p, args.length_cap, args.length_fail, principle)
               for p in paths]

    n_fail = sum(1 for r in results if r["verdict"] == "FAIL")
    n_rev = sum(1 for r in results if r["verdict"] == "REVIEW")
    n_pass = sum(1 for r in results if r["verdict"] == "PASS")
    n_unread = sum(1 for r in results if r["verdict"] == "UNREADABLE")

    print(f"[gate4ext] v2.1 扫描时点={now}  件数={len(results)}  "
          f"PASS={n_pass}  FAIL={n_fail}  REVIEW(人工复核)={n_rev}  "
          f"UNREADABLE={n_unread}  length_cap={args.length_cap}"
          f"{'(fail)' if args.length_fail else '(review)'}  "
          f"principle={'on' if principle else 'off'}"
          f"  deep_files={deep_count}")
    for r in results:
        if r["verdict"] == "PASS" and not r["review"]:
            print(f"  PASS {r['file']}  头注{r['header_lines']}行 "
                  f"字段={','.join(r['header_fields']) or '—'} 三域={r['domains']}")
    for r in results:
        if r["verdict"] != "PASS" or r["review"]:
            print(f"  {r['verdict']} {r['file']}  头注{r['header_lines']}行 "
                  f"字段={','.join(r['header_fields']) or '—'} 三域={r['domains']}")
            for (ln, dom, typ, d) in r["hard"][:40]:
                print(f"    HIT {r['file']}:{ln}  [{dom}] {typ}  {d}")
            if len(r["hard"]) > 40:
                print(f"    …（另 {len(r['hard']) - 40} 条硬命中略）")
            for (ln, dom, typ, d) in r["review"][:20]:
                print(f"    REVIEW {r['file']}:{ln}  [{dom}] {typ}  {d}")
            if len(r["review"]) > 20:
                print(f"    …（另 {len(r['review']) - 20} 条复核项略）")

    cmp_summary = None
    if args.baseline:
        cmp_summary, cmp_per = baseline_compare(results, args.baseline)
        print(f"[gate4ext] 对表基线={args.baseline}: "
              f"{json.dumps(cmp_summary, ensure_ascii=False)}")

    if args.jsonout:
        out = {"scan_time": now, "tool": "gate4_comment_guard.py v2.1 EXT",
               "length_cap": args.length_cap, "principle": principle,
               "trees_ledger": ledger, "deep_files": deep_count,
               "results": results, "baseline": cmp_summary}
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(out, f, ensure_ascii=False, indent=1)
        print(f"[gate4ext] JSON 已写 {args.jsonout}")

    if args.emit_ledger:
        tsv = args.ledger_tsv or os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "carrier_exemption_ledger_final.tsv")
        if not os.path.isfile(tsv):
            print(f"[gate4ext] FATAL: 豁免台账 TSV 不存在: {tsv} —— --emit-ledger "
                  f"需权威台账对表（--ledger-tsv 显式传入，或将 TSV 置于 "
                  f"scripts/gates/ 同目录）；禁静默降级", file=sys.stderr)
            return 2
        try:
            emit_exempt_ledger(results, args.emit_ledger, tsv, now)
        except OSError as e:
            print(f"[gate4ext] FATAL: 豁免台账 JSON 写出失败: {e}", file=sys.stderr)
            return 2

    if n_fail:
        return 1
    if n_rev or n_unread:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
