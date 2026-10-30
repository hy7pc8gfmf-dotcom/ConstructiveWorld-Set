#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""coqchk_delta_check.py — coqchk check 的薄包装·输出人读差分摘要。

对账逻辑零重复：直接 import 同目录 coqchk_attest 的 load_archive /
reconcile_tree（与 CI 接线步同一实现·工单 20261030 步骤 3 的成对件）。
本件只补一层人读渲染：三态逐件点名（changed 双哈希逐字对照·removed/
added 点名）＋ms 计时＋verdict，供终端审阅；--json 给出时原样落差分报告。

用法：
    coqchk_delta_check.py --tree <dir> --archive <archive.json> [--json <report.json>]

退出码：0=CLEAN（changed=0 且 removed=0），1=DIRTY，2=操作错误。
（added 为信息列·不影响 verdict——判义见 coqchk_attest.py docstring。）
"""

import argparse
import os
import sys
from typing import List, Optional

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from coqchk_attest import AttestError, load_archive, reconcile_tree, write_json  # noqa: E402


def _short(hexstr: Optional[str]) -> str:
    """人读摘要里哈希截前 16 位（同事报告行文同款·全量以 json 为准）。"""
    if not hexstr:
        return "(无)"
    return hexstr[:16] + "…"


def render_summary(tree: str, archive_path: str, report: dict, elapsed_ms: float) -> str:
    s = report["summary"]
    lines: List[str] = []
    lines.append("== W3 coqchk 差分对账摘要 ==")
    lines.append("树      : %s" % tree)
    lines.append("档案    : %s（archive_tree_sha256=%s）" % (archive_path, _short(report["archive_tree_sha256"])))
    lines.append("现树    : tree_sha256=%s" % _short(report["tree_sha256"]))
    lines.append("对账耗时: %.1f ms" % elapsed_ms)
    lines.append(
        "计数    : unchanged=%d  changed=%d  removed=%d  added=%d（信息列）"
        % (s["unchanged"], s["changed"], s["removed"], s["added"])
    )
    if s["changed"]:
        lines.append("--- changed（%d 件·双哈希逐字对照）---" % s["changed"])
        for item in report["changed"]:
            lines.append("  %s" % item["path"])
            lines.append("      档案 sha256=%s" % _short(item["archive_sha256"]))
            lines.append("      现树 sha256=%s" % _short(item["current_sha256"]))
    if s["removed"]:
        lines.append("--- removed（%d 件）---" % s["removed"])
        for item in report["removed"]:
            lines.append("  %s（档案 sha256=%s）" % (item["path"], _short(item["archive_sha256"])))
    if s["added"]:
        lines.append("--- added（%d 件·档案未登记·信息列）---" % s["added"])
        for item in report["added"]:
            lines.append("  %s（sha256=%s）" % (item["path"], _short(item["sha256"])))
    if report["verdict"] == "CLEAN":
        lines.append("判决: CLEAN（全树逐件哈希与认证档案一致）")
    else:
        lines.append("判决: DIRTY（changed/removed 逐件点名如上·与认证档案不符）")
    return "\n".join(lines)


def main(argv: List[str] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="coqchk_delta_check.py",
        description="coqchk check 的薄包装：三态对账＋人读差分摘要（逻辑同 coqchk_attest.py check）",
    )
    parser.add_argument("--tree", required=True, help="待对账的 .vo 树目录")
    parser.add_argument("--archive", required=True, help="认证档案 json")
    parser.add_argument("--json", dest="report_json", default=None, help="差分报告输出路径（省略则只出终端摘要）")
    args = parser.parse_args(argv)

    try:
        archive = load_archive(args.archive)
        report, elapsed_ms = reconcile_tree(args.tree, archive)
    except AttestError as exc:
        print("ERROR: %s" % exc, file=sys.stderr)
        return 2

    print(render_summary(args.tree, args.archive, report, elapsed_ms))
    if args.report_json:
        write_json(args.report_json, report)
        print("（差分报告已落盘 -> %s）" % args.report_json)
    return 0 if report["verdict"] == "CLEAN" else 1


if __name__ == "__main__":
    sys.exit(main())
