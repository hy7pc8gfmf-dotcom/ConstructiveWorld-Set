#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""coqchk_attest.py — W3 内容寻址认证对账器（Set 版重产·纯 python 零编译）。

按同事测试报告语义重产（测试报告-三捷径Set库落地效果-20261030.md）：
  · build: 逐 .vo sha256 建档＋tree_sha256 聚合 → 认证档案 json
    （报告 T1:「对 Set Live 树 90 件 .vo 建档（tree_sha256 顶层字段）」）
  · check: 三态对账 unchanged / changed / removed·逐文件哈希对档·ms 计时
    （报告 T1:「无变=全 unchanged；翻转 1 字节→changed 精确点名；
      删件→removed 精确点名」「0.2 秒全树逐件哈希对账」）

json 拓扑（仿同事报告）：tree_sha256 顶层字段＋逐件条目（path/sha256）。
档案内 path 一律为相对树根的 POSIX 路径——档案可在任意绝对位置重放对账
（CI fresh-checkout 同理，工单 20261030 步骤 3 的在库用法）。

补充申明（超出三态命名的一处）：树上存在而档案未登记的文件记入顶层
`added` 列表（纯信息性·不参与 verdict）——对账判决三态
unchanged/changed/removed 驱动；同事工单「活树对账 unchanged=848
changed=0 added=29」证明原器同样上报 added 计数，此处不为丢信息而省。

tree_sha256 聚合算法定义（确定性·跨机可重放）：
    h = sha256()
    对 sorted(rel_paths) 中每个 path:
        h.update(path.encode('utf-8') + b'\\x00'
                 + file_sha256.encode('ascii') + b'\\n')
    tree_sha256 = h.hexdigest()
即「相对路径 \\0 逐件 sha256 \\n」的排序字节流再哈希；空树 = 空流 sha256。

用法：
    coqchk_attest.py build  --tree <dir> [--out archive.json]
    coqchk_attest.py check  --tree <dir> --archive <archive.json> --json <report.json>

退出码：build 0=成功；check 0=CLEAN（changed=0 且 removed=0），1=DIRTY，
2=操作错误（树/档案不可读等）。
"""

import argparse
import hashlib
import json
import os
import sys
import time
from typing import Dict, List, Tuple

SCHEMA = "coqchk_attestation/1.0"
VO_SUFFIX = ".vo"


class AttestError(Exception):
    """操作级错误（树/档案不可读·档案拓扑不合法）。"""


def sha256_file(path: str) -> str:
    """逐块 sha256 一个文件，返回 64 位 hex。"""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def scan_tree(tree_dir: str) -> Dict[str, str]:
    """扫描树内全部 .vo：{相对 POSIX 路径: sha256}。路径排序由调用方保证。"""
    tree_dir = os.path.abspath(tree_dir)
    out: Dict[str, str] = {}
    for root, _dirs, names in os.walk(tree_dir):
        for name in names:
            if not name.endswith(VO_SUFFIX):
                continue
            full = os.path.join(root, name)
            rel = os.path.relpath(full, tree_dir).replace(os.sep, "/")
            out[rel] = sha256_file(full)
    return out


def compute_tree_sha256(per_file: Dict[str, str]) -> str:
    """按上文 docstring 的算法定义聚合 tree_sha256。"""
    h = hashlib.sha256()
    for rel in sorted(per_file):
        h.update(rel.encode("utf-8") + b"\x00" + per_file[rel].encode("ascii") + b"\n")
    return h.hexdigest()


def build_archive(tree_dir: str) -> Tuple[dict, float]:
    """逐 .vo 建档 → (档案 dict, elapsed_ms)。"""
    t0 = time.perf_counter()
    if not os.path.isdir(tree_dir):
        raise AttestError("tree 目录不存在或不是目录: %s" % tree_dir)
    per_file = scan_tree(tree_dir)
    files = [
        {
            "path": rel,
            "sha256": per_file[rel],
            "size_bytes": os.path.getsize(os.path.join(os.path.abspath(tree_dir), *rel.split("/"))),
        }
        for rel in sorted(per_file)
    ]
    archive = {
        "schema": SCHEMA,
        "kind": "attestation_archive",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tree": tree_dir,
        "file_count": len(files),
        "tree_sha256": compute_tree_sha256(per_file),
        "files": files,
    }
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    return archive, elapsed_ms


def load_archive(path: str) -> dict:
    if not os.path.isfile(path):
        raise AttestError("认证档案不存在: %s" % path)
    try:
        with open(path, "r", encoding="utf-8") as f:
            archive = json.load(f)
    except (OSError, ValueError) as exc:
        raise AttestError("认证档案不可读或非 JSON: %s (%s)" % (path, exc))
    if not isinstance(archive, dict) or not isinstance(archive.get("files"), list):
        raise AttestError("档案拓扑不合法（缺顶层 files 列表）: %s" % path)
    return archive


def reconcile_tree(tree_dir: str, archive: dict) -> Tuple[dict, float]:
    """三态对账（unchanged/changed/removed）＋added 信息列 → (报告 dict, elapsed_ms)。

    逐文件哈希对档为准；verdict=CLEAN 当且仅当 changed=0 且 removed=0。
    """
    t0 = time.perf_counter()
    if not os.path.isdir(tree_dir):
        raise AttestError("tree 目录不存在或不是目录: %s" % tree_dir)
    per_file = scan_tree(tree_dir)

    archived: Dict[str, str] = {}
    for entry in archive.get("files", []):
        if isinstance(entry, dict) and isinstance(entry.get("path"), str) and isinstance(entry.get("sha256"), str):
            archived[entry["path"]] = entry["sha256"]

    unchanged: List[dict] = []
    changed: List[dict] = []
    removed: List[dict] = []
    added: List[dict] = []
    for rel in sorted(set(per_file) | set(archived)):
        cur = per_file.get(rel)
        old = archived.get(rel)
        if cur is not None and old is None:
            added.append({"path": rel, "sha256": cur})
        elif cur is None and old is not None:
            removed.append({"path": rel, "archive_sha256": old})
        elif cur == old:
            unchanged.append({"path": rel, "sha256": cur})
        else:
            changed.append({"path": rel, "archive_sha256": old, "current_sha256": cur})

    clean = (len(changed) == 0 and len(removed) == 0)
    report = {
        "schema": SCHEMA,
        "kind": "delta_report",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tree": tree_dir,
        "archive_tree_sha256": archive.get("tree_sha256"),
        "tree_sha256": compute_tree_sha256(per_file),
        "elapsed_ms": None,  # 占位·计时完成后回填（保持字段序）
        "verdict": "CLEAN" if clean else "DIRTY",
        "summary": {
            "unchanged": len(unchanged),
            "changed": len(changed),
            "removed": len(removed),
            "added": len(added),
        },
        "unchanged": unchanged,
        "changed": changed,
        "removed": removed,
        "added": added,
    }
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    report["elapsed_ms"] = round(elapsed_ms, 3)
    return report, elapsed_ms


def write_json(path: str, obj: dict) -> None:
    """原子写 json（tmp+replace）·UTF-8·缩进 2。"""
    parent = os.path.dirname(os.path.abspath(path))
    if parent and not os.path.isdir(parent):
        os.makedirs(parent, exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write("\n")
    os.replace(tmp, path)


def cmd_build(args: argparse.Namespace) -> int:
    archive, elapsed_ms = build_archive(args.tree)
    write_json(args.out, archive)
    print("[build] tree=%s" % args.tree)
    print("[build] files=%d tree_sha256=%s" % (archive["file_count"], archive["tree_sha256"]))
    print("[build] elapsed=%.1f ms" % elapsed_ms)
    print("[build] archive written -> %s" % args.out)
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    archive = load_archive(args.archive)
    report, elapsed_ms = reconcile_tree(args.tree, archive)
    write_json(args.report_json, report)
    s = report["summary"]
    print("[check] tree=%s archive=%s" % (args.tree, args.archive))
    print("[check] archive_tree_sha256=%s" % report["archive_tree_sha256"])
    print("[check] tree_sha256(recomputed)=%s" % report["tree_sha256"])
    print(
        "[check] unchanged=%d changed=%d removed=%d added=%d (info)"
        % (s["unchanged"], s["changed"], s["removed"], s["added"])
    )
    print("[check] elapsed=%.1f ms" % elapsed_ms)
    print("[check] verdict=%s" % report["verdict"])
    print("[check] report written -> %s" % args.report_json)
    return 0 if report["verdict"] == "CLEAN" else 1


def main(argv: List[str] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="coqchk_attest.py",
        description="W3 内容寻址认证对账器（build 建档 / check 三态对账·纯 python）",
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_build = sub.add_parser("build", help="逐 .vo sha256＋tree_sha256 聚合 → 认证档案 json")
    p_build.add_argument("--tree", required=True, help="待建档的 .vo 树目录")
    p_build.add_argument(
        "--out", "--archive", dest="out", default="coqchk_attestation.json",
        help="档案输出路径（默认 ./coqchk_attestation.json）",
    )
    p_build.set_defaults(func=cmd_build)

    p_check = sub.add_parser("check", help="三态对账 unchanged/changed/removed·逐文件哈希对档·ms 计时")
    p_check.add_argument("--tree", required=True, help="待对账的 .vo 树目录")
    p_check.add_argument("--archive", required=True, help="认证档案 json")
    p_check.add_argument("--json", dest="report_json", required=True, help="差分报告输出路径")
    p_check.set_defaults(func=cmd_check)

    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except AttestError as exc:
        print("[%s] ERROR: %s" % (args.cmd, exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
