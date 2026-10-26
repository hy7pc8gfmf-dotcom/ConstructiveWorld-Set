#!/usr/bin/env bash
# CI/local build loop for the single ConstructiveWorld_Live tree (order.txt topology)
# with fingerprint SKIP (trust-cache semantics). Difference from ci_build_live.sh:
# NO mirror-clean here -- cache seeding/cleanliness is the caller's duty (CI seed
# step mirrors rm+cp; local runs keep the incremental .vo cache). ".vo newer than
# .v" skips, everything else truly compiles. Caller wraps in cpu_guard (thermal).
set -u
export COQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
export ROCQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
COQC="C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe"
cd "$(dirname "$0")/.." || exit 1
fail=0; n=0; s=0
while IFS= read -r line || [ -n "$line" ]; do
  f="${line%%\#*}"          # strip trailing #R-anchor
  f="${f%$'\r'}"            # CRLF-safe
  [ -z "$f" ] && continue
  if [ ! -f "ConstructiveWorld_Live/$f" ]; then
    echo "BUILD-FAIL: order entry $f missing from ConstructiveWorld_Live"
    fail=1
    continue
  fi
  v="ConstructiveWorld_Live/${f%.v}.vo"
  log="ConstructiveWorld_Live/_${f%.v}.build.log"
  if [ -f "$v" ] && [ "$v" -nt "ConstructiveWorld_Live/$f" ]; then
    echo "$f SKIP(vo-newer-than-src)"
    s=$((s+1))
    continue
  fi
  "$COQC" -native-compiler no -q -Q "ConstructiveWorld_Live" "" "ConstructiveWorld_Live/$f" > "$log" 2>&1
  rc=$?
  echo "$f EXIT=$rc"
  if [ "$rc" -ne 0 ]; then
    fail=1
    echo "----- last 30 lines of $log -----"
    tail -30 "$log"
  else
    n=$((n+1))
  fi
done < ConstructiveWorld_Live/order.txt
if [ "$fail" -ne 0 ]; then
  echo "BUILD-FAIL: one or more files failed (true RC accounted above)"
fi
echo "CACHE-BUILD-SUMMARY compiled=$n skipped=$s fail=$fail"
exit $fail
