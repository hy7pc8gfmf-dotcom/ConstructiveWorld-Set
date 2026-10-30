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
  sc="ConstructiveWorld_Live/_${f%.v}.vobuild.md5"
  # 20261030 digest sidecar guard (run 67 lesson): a seeded .vo from an older
  # generation of the same-named .v shadows the checkout -- seed cp refreshes
  # mtimes, so "vo newer than v" alone is unsound for relanded pieces. Skip
  # only when .vo is newer AND the compile-time sidecar digest matches the
  # current .v; missing/mismatched sidecar forces a true recompile.
  cur="$(md5sum "ConstructiveWorld_Live/$f" 2>/dev/null | cut -d' ' -f1)"
  skip=0
  if [ -f "$v" ] && [ "$v" -nt "ConstructiveWorld_Live/$f" ] \
     && [ -n "$cur" ] && [ -f "$sc" ] \
     && [ "$(tr -d '[:space:]' < "$sc" 2>/dev/null)" = "$cur" ]; then
    skip=1
  fi
  if [ "$skip" -eq 1 ]; then
    echo "$f SKIP(vo-newer+digest)"
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
    printf '%s\n' "$cur" > "$sc"
  fi
done < ConstructiveWorld_Live/order.txt
if [ "$fail" -ne 0 ]; then
  echo "BUILD-FAIL: one or more files failed (true RC accounted above)"
fi
# 20261029 green-gated write-back: on a fully green build, mirror the freshly
# compiled .vo back into the local dev-tree trust cache (CACHE_WRITEBACK_DIR).
# Era guard: skip when the dev tree has uncommitted tracked modifications --
# a dirty dev tree is a different era and must not inherit head-era .vo.
# Same-platform by construction (Windows CI -> Windows dev tree).
if [ "$fail" -eq 0 ] && [ -n "${CACHE_WRITEBACK_DIR:-}" ]; then
  if git -C "$CACHE_WRITEBACK_DIR/.." status --porcelain -- ConstructiveWorld_Live 2>/dev/null | grep -qE "^( M|M )"; then
    echo "CACHE-WRITEBACK: dev tree dirty -- skip (era guard)"
  else
    wb=0
    for v in ConstructiveWorld_Live/*.vo; do
      [ -e "$v" ] || continue
      cp -f "$v" "$CACHE_WRITEBACK_DIR/" && wb=$((wb+1))
    done
    for m in ConstructiveWorld_Live/*.vobuild.md5; do
      [ -e "$m" ] || continue
      cp -f "$m" "$CACHE_WRITEBACK_DIR/"
    done
    echo "CACHE-WRITEBACK: $wb .vo (+digest sidecars) -> $CACHE_WRITEBACK_DIR"
  fi
fi
echo "CACHE-BUILD-SUMMARY compiled=$n skipped=$s fail=$fail"
exit $fail
