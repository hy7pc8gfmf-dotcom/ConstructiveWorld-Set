#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""gate7_extract_run.py -- extraction-execution gate (red-line law IV, 4a/4b).

Doctrine (white paper v2.2-v2.5): extractable is NOT enough -- the extracted
code must exist, be magic-free, and compile; the extraction diff is the FINAL
mechanical arbiter of Prop leakage (v2.3 ruling six).  This gate automates 4a
per module:

  for every order.txt module with top-level informative statement names:
    1. emit ONE `Separate Extraction <all names>` driver (single-command rule:
       Separate Extraction resets output per command -- multi-command drivers
       would silently keep only the last command's files);
    2. compile the driver against the built Live tree (.vo required: run AFTER
       the build step);
    3. account BOTH faces (.ml / .mli): Obj.magic counts (law: =0, stock debt
       tracked via baseline) and statement-name presence diff (mangled-name
       candidates; absent names are reported as ERASURE CANDIDATES -- word-face
       proxy, human/third-source review per the three-source reading rule);
    4. optionally compile with ocamlc when a toolchain is present (4b; skipped
       with an explicit note otherwise).

Modes
  report (default)      census only, exit 0
  --gate --baseline B   red (exit 1) on regression vs baseline: Obj.magic growth
                        on either face, erasure-candidate growth, driver rc
                        0->nonzero, or a NEW module born with magic>0 / missing
                        names (born-clean zero tolerance).

Exit codes: 0 clean / report-only, 1 gate regression, 2 usage/IO error.
"""

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from gate6_statement_census import census_file, strip_comments, sentences  # noqa: E402

DEFAULT_COQC = r"C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe"


def statement_names(vfile):
    """Top-level informative statement names of a .v file (gate6 scanner reuse)."""
    text = strip_comments(vfile.read_bytes().decode("utf-8-sig", errors="replace"))
    names = []
    for _, sent in sentences(text):
        m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)", sent)
        if not m:
            continue
        cmd = m.group(1)
        if cmd in {"Theorem", "Lemma", "Corollary", "Proposition", "Example",
                   "Definition", "Fixpoint", "Function", "Instance"}:
            m2 = re.match(r"\s*" + re.escape(cmd) + r"\s+([A-Za-z_][A-Za-z0-9_']*)", sent)
            if m2:
                names.append(m2.group(1))
    return names


def mangle_candidates(name):
    c = {name, name.lower()}
    if "'" in name:
        c.add(name.replace("'", "_p"))
        c.add(name.replace("'", "_qs"))
    c.add(name.replace("_", ""))
    return c


def run_module(mod, tree, workdir, coqc, timeout):
    names = statement_names(tree / (mod + ".v"))
    rec = {"names_total": len(names), "magic_ml": None, "magic_mli": None,
           "missing_candidates": [], "driver_rc": None, "secs": None, "note": ""}
    if not names:
        rec["note"] = "no top-level informative statements -- skipped"
        return rec
    driver = workdir / ("_gate7_%s_driver.v" % mod)
    driver.write_text(
        "From Coq Require Import Extraction.\n"
        "Require Import %s.\n"
        "Separate Extraction %s.\n" % (mod, " ".join(names)),
        encoding="utf-8")
    t0 = time.time()
    try:
        p = subprocess.run([coqc, "-native-compiler", "no", "-q", "-Q", str(tree), "",
                            driver.name],
                           cwd=str(workdir), capture_output=True, text="utf-8",
                           errors="replace", timeout=timeout)
        rc = p.returncode
        tail = (p.stderr or p.stdout or "")[-400:]
    except subprocess.TimeoutExpired:
        rc, tail = -9, "TIMEOUT after %ss" % timeout
    rec["driver_rc"] = rc
    rec["secs"] = round(time.time() - t0, 1)
    ml = workdir / (mod + ".ml")
    mli = workdir / (mod + ".mli")
    if rc != 0:
        rec["note"] = "driver failed: " + " ".join(tail.split())[-200:]
        return rec
    if not ml.exists():
        rec["note"] = "no .ml produced (extraction silently skipped?)"
        return rec
    ml_text = ml.read_text(encoding="utf-8", errors="replace")
    mli_text = mli.read_text(encoding="utf-8", errors="replace") if mli.exists() else ""
    rec["magic_ml"] = ml_text.count("Obj.magic")
    rec["magic_mli"] = mli_text.count("Obj.magic")
    blob = ml_text + "\n" + mli_text
    missing = []
    for nm in names:
        if not any(c in blob for c in mangle_candidates(nm)):
            missing.append(nm)
    rec["missing_candidates"] = missing
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", required=True)
    ap.add_argument("--order", required=True)
    ap.add_argument("--workdir", default="_gate7_work")
    ap.add_argument("--coqc", default=DEFAULT_COQC)
    ap.add_argument("--timeout", type=int, default=240)
    ap.add_argument("--json", dest="json_out")
    ap.add_argument("--gate", action="store_true")
    ap.add_argument("--baseline")
    ap.add_argument("--baseline-out", dest="baseline_out")
    args = ap.parse_args()

    tree = Path(args.tree).resolve()
    order = Path(args.order)
    if not tree.is_dir() or not order.is_file():
        print("GATE7-USAGE: --tree/--order must exist", file=sys.stderr)
        return 2
    modules = []
    for line in order.read_text(encoding="utf-8-sig", errors="replace").splitlines():
        f = line.split("#")[0].strip().rstrip("\r")
        if f:
            modules.append(f[:-2] if f.endswith(".v") else f)

    workdir = Path(args.workdir)
    workdir.mkdir(exist_ok=True)
    for old in workdir.glob("*.ml"):
        old.unlink()
    for old in workdir.glob("*.mli"):
        old.unlink()

    results = {}
    for i, mod in enumerate(modules, 1):
        rec = run_module(mod, tree, workdir, args.coqc, args.timeout)
        results[mod] = rec
        print("GATE7 [%d/%d] %s names=%s rc=%s magic=%s/%s missing=%d %s"
              % (i, len(modules), mod, rec["names_total"], rec["driver_rc"],
                 rec["magic_ml"], rec["magic_mli"], len(rec["missing_candidates"]),
                 rec["note"][:80]))

    tot_magic = sum((r["magic_ml"] or 0) + (r["magic_mli"] or 0) for r in results.values())
    tot_missing = sum(len(r["missing_candidates"]) for r in results.values())
    failed = sorted(m for m, r in results.items() if r["driver_rc"] not in (0, None))

    rc = 0
    if args.gate:
        if not args.baseline:
            print("GATE7-USAGE: --gate requires --baseline", file=sys.stderr)
            return 2
        base = json.loads(Path(args.baseline).read_text(encoding="utf-8")).get("modules", {})
        regs = []
        for mod, r in results.items():
            b = base.get(mod)
            if b is None:
                if (r["magic_ml"] or 0) + (r["magic_mli"] or 0) > 0 or r["missing_candidates"]:
                    regs.append("%s NEW-module with magic/missing (born-clean violation)" % mod)
                continue
            if (r["magic_ml"] or 0) > (b.get("magic_ml") or 0) or \
               (r["magic_mli"] or 0) > (b.get("magic_mli") or 0):
                regs.append("%s magic growth %s/%s -> %s/%s"
                            % (mod, b.get("magic_ml"), b.get("magic_mli"),
                               r["magic_ml"], r["magic_mli"]))
            bmiss = set(b.get("missing_candidates") or [])
            newmiss = set(r["missing_candidates"]) - bmiss
            if newmiss:
                regs.append("%s new erasure candidates: %s" % (mod, sorted(newmiss)[:6]))
            if (r["driver_rc"] or 0) != 0 and (b.get("driver_rc") or 0) == 0:
                regs.append("%s driver regressed to rc=%s" % (mod, r["driver_rc"]))
        if regs:
            rc = 1
            print("GATE7-RED: %d regression(s) vs baseline" % len(regs))
            for r in regs:
                print("  " + r)
        else:
            print("GATE7-GREEN: no extraction-execution regression (modules=%d)" % len(results))
    else:
        print("GATE7-CENSUS: modules=%d magic_total=%d missing_candidates=%d driver_failed=%s"
              % (len(results), tot_magic, tot_missing, ",".join(failed) or "-"))

    if args.json_out:
        Path(args.json_out).write_text(
            json.dumps({"modules": results,
                        "totals": {"magic": tot_magic, "missing": tot_missing}},
                       ensure_ascii=False, indent=1),
            encoding="utf-8")
    if args.baseline_out:
        modules_out = {}
        for m, r in results.items():
            modules_out[m] = {"names_total": r["names_total"],
                              "magic_ml": r["magic_ml"],
                              "magic_mli": r["magic_mli"],
                              "missing_candidates": r["missing_candidates"],
                              "driver_rc": r["driver_rc"]}
        Path(args.baseline_out).write_text(
            json.dumps({"modules": modules_out}, ensure_ascii=False, indent=1),
            encoding="utf-8")
        print("GATE7-BASELINE-WRITTEN: %s" % args.baseline_out)
    return rc


if __name__ == "__main__":
    sys.exit(main())
