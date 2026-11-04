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

v2 sandbox patch (kb52_work_20261029, repo original untouched):
  - face 1: name-candidate blacklist -- a captured statement name that is a
    Coq vernacular/reserved keyword (Proposition, Context, Section, End,
    Require, Import, Export, Print, Check, Evaluation, ...) can never be a
    legal bare reference target for `Separate Extraction` (it is either a
    keyword that makes the driver sentence a syntax error, or resolves to a
    sort alias, never to the user definition).  Such candidates are dropped
    and recorded in the module's `exclusions`.
  - face 2: scope-depth tracking -- the sentence walk now maintains the
    Module/Section ... End nesting stack.  A name born while a MODULE block
    is open is qualified by that module (bare name NOT visible at top level
    after `End`) and is dropped from the driver list and recorded in
    `exclusions`.  DEVIATION NOTE vs the literal fix order: names born in a
    pure top-level SECTION stay in the driver list -- the committed baseline
    proves they are bare-referable and extract cleanly (17+ green modules
    carry section-born names in passing drivers, e.g. S04_RealExpLogConv:
    all 153 names section-born, driver_rc=0), so excluding them would break
    the hard no-new-exclusions mandate on unaffected modules.
  - both faces are occurrence-level and order-preserving; for every module
    whose captured names contain no keyword and no module-born name, the
    v2 driver list is IDENTICAL to v1 (zero behavior drift, verified over
    all 87 Live .v files by the sandbox dry run).

v3 tool-fault patch (20261105, worktree chore/gate7-tool-and-constraints):
  - WF-B: Coq identifiers are Unicode-aware -- S11_TP3B5.v:12038 defines
    top-level `Lemma b5n_2S_kδ_le`.  The v1/v2 ASCII class
    [A-Za-z_][A-Za-z0-9_']* truncates the name at the first non-ASCII
    letter and emits the phantom prefix `b5n_2S_k` into the driver, which
    coqc rejects with "The reference b5n_2S_k was not found in the current
    environment" (driver line 3, chars 6600-6608).  The captured-name class
    is therefore widened to the Unicode-aware `[^\W\d][\w']*`
    (letter/underscore start, letter/digit/underscore/prime tail).  On pure
    ASCII input the new class is EXACTLY the old class (character-by-
    character equivalence), so driver lists are unchanged for every module
    whose names are all-ASCII -- verified over all 375 Live .v files: the
    ascii-vs-unicode scan differs on exactly one file (S11_TP3B5) and
    exactly one name (phantom `b5n_2S_k` <-> real `b5n_2S_kδ_le`).
  - WF-B companion (identifier escaping): the name-presence proxy now also
    accepts extraction's UU-escaped identifier form (`_UU<hex>_` per
    non-ASCII char, verified against S11_TP3B5.ml), so a Unicode name that
    IS extracted is no longer reported as a false erasure candidate.
  - WF-C: --timeout is now tiered by names_total when not given explicitly:
    <=50 names keep the historical 240s budget, >50 names get 600s
    (LW3FamScale's driver exceeded 240s and the timeout kill took down the
    whole CI tree run).  An explicit --timeout value is honored verbatim
    (backward compatible).  Batching the driver into several `Separate
    Extraction` commands is NOT implemented on purpose: per-command output
    reset (single-command rule, top of this docstring) makes multi-command
    drivers silently keep only the last command's files.
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

# v2 face 1 -- keywords excluded from the captured statement NAME set.
# Rationale (corrected per independent review 20261029): this tree proves a
# reserved word CAN be a legal user definition name -- S01_BaseRing.v:1330
# `Definition Proposition` (inside Module PropositionConvergenceCore) and
# S13_NLiveAudit.v:1148 `Definition Context` (inside LCAudit) both compile
# (.vo FRESH, glob def records on file).  The exclusion is therefore a
# CONSERVATIVE DRIVER-REFERENCE AVOIDANCE: a top-level `Separate Extraction`
# driver cannot reference these module-internal names, and naming them in the
# driver makes coqc fail at the reference site.  Extraction coverage of the
# retained statements is unaffected (Separate Extraction pulls transitive
# dependencies).  The first ten are the words named by the fix order; the
# rest are the same-class vernacular/Gallina words.  Known limitation
# (review issue 2): the keyword branch runs before the scope walk, so a
# future TOP-LEVEL legal definition with one of these names would be dropped
# unconditionally -- revisit if that case ever appears.
VERNAC_NAME_BLACKLIST = {
    "Proposition", "Context", "Section", "End", "Require", "Import", "Export",
    "Print", "Check", "Evaluation",
    # same-class reserved words (safe: can never be legal user names)
    "Compute", "Eval", "Theorem", "Lemma", "Definition", "Proof", "Qed",
    "Fixpoint", "CoFixpoint", "Function", "Example", "Remark", "Fact",
    "Corollary", "Instance", "Goal", "Abort", "Admitted", "Variable",
    "Variables", "Hypothesis", "Hypotheses", "Axiom", "Axioms", "Parameter",
    "Parameters", "Conjecture", "Record", "Inductive", "CoInductive",
    "Class", "Scheme", "Notation", "Infix", "Reserved", "Arguments", "Ltac",
    "Load", "Declare", "Module", "Set", "Type", "Prop", "SProp", "Time",
    "Separate", "Extraction", "Existing", "Canonical", "Coercion", "Let",
}


def _scope_open(sent_tokens):
    """Return the scope label pushed by a Module/Section sentence, else None."""
    first = sent_tokens[0] if sent_tokens else ""
    if first in ("Module", "Section"):
        # `Module Type X` blocks namespace-hide their contents just the same;
        # record the full head for the human-readable scope chain.
        return first + ":" + (sent_tokens[1].rstrip(".") if len(sent_tokens) > 1 else "?")
    return None


def statement_scan(vfile):
    """v2 core walk: classify captured statement name occurrences.

    Returns (driver_names, exclusions):
      driver_names  order-preserving list (duplicates kept, exactly like v1)
                    of names that are safe to reference bare at top level;
      exclusions    list of {"name", "reason", "scope"} for dropped
                    occurrences: reason "vernacular-keyword" (face 1) or
                    "module-scope" (face 2 -- born inside an open Module
                    block, bare name not visible at top level).  Pure
                    top-level Section-born names are KEPT (see module
                    docstring deviation note).
    """
    text = strip_comments(vfile.read_bytes().decode("utf-8-sig", errors="replace"))
    stack = []  # open scope chain, e.g. ["Module:LCAudit", "Section:LiveCore"]
    names, exclusions = [], []
    for _, sent in sentences(text):
        toks = sent.split()
        # --- maintain the scope stack BEFORE capturing (a scope opener or a
        # --- closer sentence never carries a statement name itself) --------
        pushed = _scope_open(toks)
        if pushed is not None:
            stack.append(pushed)
        elif toks and toks[0] == "End" and stack:
            stack.pop()
        # --- v1 capture logic, unchanged ------------------------------------
        # v3 WF-B: identifier class is Unicode-aware ([^\W\d] = Unicode letter
        # or underscore; [\w'] = letters/digits/underscore/prime).  Identical
        # to the old ASCII class on pure ASCII input (see module docstring).
        m = re.match(r"\s*([^\W\d][\w']*)", sent)
        if not m:
            continue
        cmd = m.group(1)
        if cmd in {"Theorem", "Lemma", "Corollary", "Proposition", "Example",
                   "Definition", "Fixpoint", "Function", "Instance"}:
            m2 = re.match(r"\s*" + re.escape(cmd) + r"\s+([^\W\d][\w']*)", sent)
            if m2:
                nm = m2.group(1)
                chain = "/".join(stack)
                if nm in VERNAC_NAME_BLACKLIST:
                    # face 1: keyword names can never be bare reference targets
                    exclusions.append({"name": nm, "reason": "vernacular-keyword",
                                       "scope": chain})
                elif any(s.startswith("Module:") for s in stack):
                    # face 2: module-born names are module-qualified, hence not
                    # visible bare at top level after the module is closed
                    exclusions.append({"name": nm, "reason": "module-scope",
                                       "scope": chain})
                else:
                    names.append(nm)
    return names, exclusions


def statement_names(vfile):
    """Top-level informative statement names of a .v file (gate6 scanner reuse).

    v2: drops vernacular-keyword names and module-scoped names (see
    statement_scan); the returned list feeds the Separate Extraction driver.
    """
    return statement_scan(vfile)[0]


def mangle_candidates(name):
    c = {name, name.lower()}
    if "'" in name:
        c.add(name.replace("'", "_p"))
        c.add(name.replace("'", "_qs"))
    c.add(name.replace("_", ""))
    # v3 WF-B: extraction escapes non-ASCII identifier characters as
    # _UU<hex>_ (lowercase zero-padded hex, e.g. U+03B4 -> _UU03b4_), so the
    # escaped form is a presence candidate too.  Real tree case: source
    # `b5n_2S_kδ_le` appears in S11_TP3B5.ml as `b5n_2S_k_UU03b4__le`;
    # without the escaped candidate the presence proxy reported a FALSE
    # erasure candidate for a name that is in fact extracted.  Adding a
    # candidate can only turn missing -> present, never the reverse; for
    # all-ASCII names esc == name (zero drift).
    esc = re.sub(r"[^\x00-\x7F]", lambda m: "_UU%04x_" % ord(m.group(0)), name)
    if esc != name:
        c.add(esc)
    return c


def run_module(mod, tree, workdir, coqc, timeout):
    # v2: statement_scan returns (driver names, exclusions); exclusions are
    # recorded additively in the JSON record (gate decisions untouched).
    names, exclusions = statement_scan(tree / (mod + ".v"))
    rec = {"names_total": len(names), "magic_ml": None, "magic_mli": None,
           "missing_candidates": [], "driver_rc": None, "secs": None, "note": "",
           "exclusions": exclusions}
    if not names:
        rec["note"] = "no top-level informative statements -- skipped"
        return rec
    if timeout is None:
        # v3 WF-C: tiered budget by names_total (None = caller gave no
        # explicit --timeout).  <=50 names keep the historical 240s; larger
        # drivers get 600s (240s tree-killed LW3FamScale).  An explicit
        # --timeout is honored verbatim (backward compatible).
        timeout = 240 if len(names) <= 50 else 600
    rec["timeout_eff"] = timeout  # v3: additive audit field
    driver = workdir / ("_gate7_%s_driver.v" % mod)
    driver.write_text(
        "From Stdlib Require Import Extraction.\n"
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
    ap.add_argument("--timeout", type=int, default=None,
                    help="per-driver coqc budget in seconds; default: tiered "
                         "by names_total (<=50 names -> 240s, >50 -> 600s); "
                         "an explicit value is honored verbatim")
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
                              "driver_rc": r["driver_rc"],
                              "exclusions": r["exclusions"]}  # v2: additive
        Path(args.baseline_out).write_text(
            json.dumps({"modules": modules_out}, ensure_ascii=False, indent=1),
            encoding="utf-8")
        print("GATE7-BASELINE-WRITTEN: %s" % args.baseline_out)
    return rc


if __name__ == "__main__":
    sys.exit(main())
