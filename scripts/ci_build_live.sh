#!/usr/bin/env bash
# CI build loop for the single ConstructiveWorld_Live tree (order.txt topology, cold build).
# Self-contained: no dependency on local vo trees or D:\actions-runner wrappers.
# Caller wraps this in cpu_guard.ps1 (thermal guard), same as the previous cmd wrappers.
set -u
export COQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
export ROCQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
COQC="C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe"
cd "$(dirname "$0")/.." || exit 1
# Mirror-clean products so a rerun never sees a stale .vo (P9 lesson: stale survivors
# across runs caused coqchk digest tears under the old seeding scheme).
rm -f ConstructiveWorld_Live/*.vo ConstructiveWorld_Live/_chk_all.log
fail=0
while IFS= read -r line || [ -n "$line" ]; do
  f="${line%%\#*}"          # strip trailing #R-anchor
  f="${f%$'\r'}"            # CRLF-safe
  [ -z "$f" ] && continue
  if [ ! -f "ConstructiveWorld_Live/$f" ]; then
    echo "BUILD-FAIL: order entry $f missing from ConstructiveWorld_Live"
    fail=1
    continue
  fi
  log="ConstructiveWorld_Live/_${f%.v}.build.log"
  "$COQC" -native-compiler no -q -Q "ConstructiveWorld_Live" "" "ConstructiveWorld_Live/$f" > "$log" 2>&1
  rc=$?
  echo "$f EXIT=$rc"
  if [ "$rc" -ne 0 ]; then
    fail=1
    echo "----- last 30 lines of $log -----"
    tail -30 "$log"
  fi
done < ConstructiveWorld_Live/order.txt
if [ "$fail" -ne 0 ]; then
  echo "BUILD-FAIL: one or more files failed (true RC accounted above)"
fi
exit $fail
