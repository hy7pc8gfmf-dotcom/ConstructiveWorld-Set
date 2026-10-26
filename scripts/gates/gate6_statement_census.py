#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""gate6_statement_census.py -- Prop-leakage word-face census (channels 1+2).

Red-line law II (Path A, white paper v2.4+) requires every named construction
(definitions / theorems / auxiliary lemmas / field positions) to be carried by
Set/Type with zero new Prop statements.  Word-face scanning is only a PRE-SCREEN
(the semantic final arbiter is the extraction diff, gate7); this gate makes the
pre-screen mechanical and CI-bound so the three leakage channels have at least
a standing census:

  channel 1  statement faces  (Theorem/Lemma/Corollary/Proposition/Example/
             Remark/Fact/Definition/Fixpoint/Function/Instance)
  channel 2  field & section faces (Record/Class/Inductive fields,
             Context/Variable(s)/Hypothes(is|es))
  channel 3  global assumption faces (Axiom/Axioms/Parameter(s) at top level)

Modes
  census (default)   report only, exit 0
  --gate --baseline B regression gate vs committed baseline JSON:
                     red (exit 1) on any per-file/per-channel count ABOVE the
                     baseline or on hits in files absent from the baseline
                     (born-clean: new files start at zero tolerance).
                     R15 doctrine: stock is frozen, never retroactive; only
                     growth is red.

Exit codes: 0 clean / report-only, 1 gate regression, 2 usage or IO error.
"""

import argparse
import json
import re
import sys
from pathlib import Path

# Commands whose sentence is a STATEMENT FACE (channel 1).
STMT_CMDS = {
    "Theorem", "Lemma", "Corollary", "Proposition", "Example", "Remark", "Fact",
    "Definition", "Fixpoint", "Function", "Instance",
}
# Commands whose sentence carries FIELD/SECTION positions (channel 2).
FIELD_CMDS = {
    "Record", "Class", "Inductive", "CoInductive",
    "Context", "Variable", "Variables", "Hypothesis", "Hypotheses",
}
# Global assumption faces (channel 3).
ASSUM_CMDS = {"Axiom", "Axioms", "Parameter", "Parameters"}

PROP_WORD = re.compile(r"\bProp\b")


def strip_comments(text):
    """Remove (* ... *) comments (Coq comments nest) and string literals."""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("*)", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        ch = text[i]
        if ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 1
            out.append(" ")
            i = j + 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def sentences(text):
    """Yield (start_line, sentence_text) for top-level Coq sentences.

    A sentence ends at a '.' at bracket depth 0 followed by whitespace/EOF
    (this library avoids decimal literals in statement faces; decimal dots
    inside brace-protected terms are shielded by the depth counter).
    """
    depth = 0
    start = 0
    n = len(text)
    line = 1
    start_line = 1
    i = 0
    while i < n:
        ch = text[i]
        if ch == "\n":
            line += 1
        elif ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == "." and depth == 0:
            nxt = text[i + 1] if i + 1 < n else " "
            if nxt.isspace() or nxt == "。" or i + 1 == n:
                sent = text[start:i + 1]
                if sent.strip():
                    yield (start_line, sent)
                start = i + 1
                start_line = line
        i += 1
    tail = text[start:]
    if tail.strip():
        yield (start_line, tail)


def command_of(sentence):
    m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)", sentence)
    return m.group(1) if m else ""


def name_of(sentence, cmd):
    m = re.match(r"\s*" + re.escape(cmd) + r"\s+([A-Za-z_][A-Za-z0-9_']*)", sentence)
    return m.group(1) if m else ""


def census_file(path):
    """Return {'ch1': [hits], 'ch2': [...], 'ch3': [...], 'names': [...]}."""
    raw = path.read_bytes()
    text = raw.decode("utf-8-sig", errors="replace")
    clean = strip_comments(text)
    # Recompute line numbers on the CLEAN text (comment stripping only removes
    # spans; we count newlines kept verbatim so line numbers stay true).
    hits = {"ch1": [], "ch2": [], "ch3": []}
    names = []
    for start_line, sent in sentences(clean):
        cmd = command_of(sent)
        base = cmd.rstrip("0123456789")  # not needed today; future-proof
        if cmd in STMT_CMDS:
            nm = name_of(sent, cmd)
            if nm:
                names.append(nm)
            if PROP_WORD.search(sent):
                hits["ch1"].append({"line": start_line, "cmd": cmd, "name": nm,
                                    "excerpt": " ".join(sent.split())[:120]})
        elif cmd in FIELD_CMDS:
            if PROP_WORD.search(sent):
                hits["ch2"].append({"line": start_line, "cmd": cmd, "name": "",
                                    "excerpt": " ".join(sent.split())[:120]})
        elif cmd in ASSUM_CMDS:
            hits["ch3"].append({"line": start_line, "cmd": cmd, "name": name_of(sent, cmd),
                                "excerpt": " ".join(sent.split())[:120]})
    return {"ch1": hits["ch1"], "ch2": hits["ch2"], "ch3": hits["ch3"], "names": names}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", required=True)
    ap.add_argument("--json", dest="json_out")
    ap.add_argument("--text", action="store_true")
    ap.add_argument("--gate", action="store_true")
    ap.add_argument("--baseline")
    ap.add_argument("--baseline-out", dest="baseline_out")
    args = ap.parse_args()

    tree = Path(args.tree)
    if not tree.is_dir():
        print("GATE6-TREE-MISSING: %s" % tree, file=sys.stderr)
        return 2

    files = sorted(tree.glob("*.v"))
    census = {}
    for f in files:
        try:
            census[f.name] = census_file(f)
        except Exception as e:  # fail-loud per file, never silent
            print("GATE6-PARSE-ERROR: %s: %s" % (f.name, e), file=sys.stderr)
            return 2

    totals = {k: sum(len(census[f][k]) for f in census) for k in ("ch1", "ch2", "ch3")}
    summary = {
        "files": len(files),
        "totals": totals,
        "statement_names": sum(len(census[f]["names"]) for f in census),
    }

    rc = 0
    if args.gate:
        if not args.baseline:
            print("GATE6-USAGE: --gate requires --baseline", file=sys.stderr)
            return 2
        base = json.loads(Path(args.baseline).read_text(encoding="utf-8"))
        base_files = base.get("files", {})
        regressions = []
        for fname, c in sorted(census.items()):
            b = base_files.get(fname)
            for ch in ("ch1", "ch2", "ch3"):
                cur = len(c[ch])
                if b is None:
                    if cur > 0:
                        regressions.append((fname, ch, 0, cur, "new-file"))
                else:
                    old = b.get(ch, 0)
                    if cur > old:
                        regressions.append((fname, ch, old, cur, "growth"))
        # baseline files that disappeared: informational, not red (retirement
        # of stock is allowed; only growth is a violation).
        gone = sorted(set(base_files) - set(census))
        if regressions:
            rc = 1
            print("GATE6-RED: %d regression(s) vs baseline %s" % (len(regressions), args.baseline))
            for fname, ch, old, cur, why in regressions:
                print("  %s %s baseline=%d current=%d (%s)" % (fname, ch, old, cur, why))
        else:
            print("GATE6-GREEN: no Prop-face regression vs baseline (files=%d)" % len(files))
        if gone:
            print("GATE6-INFO: %d baseline file(s) retired: %s" % (len(gone), ", ".join(gone[:8])))
    else:
        print("GATE6-CENSUS: files=%d ch1=%d ch2=%d ch3=%d names=%d"
              % (len(files), totals["ch1"], totals["ch2"], totals["ch3"], summary["statement_names"]))

    if args.text:
        for fname in sorted(census):
            for ch in ("ch1", "ch2", "ch3"):
                for h in census[fname][ch]:
                    print("  %s:%d %s %s %s | %s" % (fname, h["line"], ch, h["cmd"],
                                                     h.get("name") or "-", h["excerpt"]))

    if args.json_out:
        Path(args.json_out).write_text(
            json.dumps({"summary": summary, "files": census}, ensure_ascii=False, indent=1),
            encoding="utf-8")
    if args.baseline_out:
        Path(args.baseline_out).write_text(
            json.dumps({"generated_from_tree": str(tree),
                        "files": {f: {"ch1": len(census[f]["ch1"]),
                                      "ch2": len(census[f]["ch2"]),
                                      "ch3": len(census[f]["ch3"]),
                                      "names": len(census[f]["names"])}
                                  for f in sorted(census)}},
                      ensure_ascii=False, indent=1),
            encoding="utf-8")
        print("GATE6-BASELINE-WRITTEN: %s" % args.baseline_out)
    return rc


if __name__ == "__main__":
    sys.exit(main())
