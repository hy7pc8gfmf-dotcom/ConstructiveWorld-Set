#!/usr/bin/env bash
# CI/local build loop for the single ConstructiveWorld_Live tree (order.txt topology)
# with fingerprint SKIP (trust-cache semantics). Difference from ci_build_live.sh:
# NO mirror-clean here -- cache seeding/cleanliness is the caller's duty (CI seed
# step mirrors rm+cp; local runs keep the incremental .vo cache). ".vo newer than
# .v" skips, everything else truly compiles. Caller wraps in cpu_guard (thermal).
set -u
# Toolchain: env-overridable (form A injection, Rocq 9.3 migration wave); defaults keep
# today's 9.1 platform byte-for-byte. COQLIB/ROCQLIB derive from COQC via the SW2 same-root
# rule (<root>/bin/coqc.exe -> <root>/lib/coq), so one COQC export moves the whole toolchain.
COQC="${COQC:-C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe}"
COQDEP="${COQDEP:-${COQC%/coqc.exe}/coqdep.exe}"
case "$COQC" in
  */bin/coqc.exe) _root="${COQC%/bin/coqc.exe}"; export COQLIB="${COQLIB:-$_root/lib/coq}"; export ROCQLIB="${ROCQLIB:-$COQLIB}" ;;
  *) export COQLIB="${COQLIB:-C:/Rocq-Platform~9.1~2026.01/lib/coq}"; export ROCQLIB="${ROCQLIB:-$COQLIB}" ;;
esac
cd "$(dirname "$0")/.." || exit 1
fail=0; n=0; s=0; vld=0; stale=0
LIVE="ConstructiveWorld_Live"

# ---- 20261102 dependency-closure fingerprint (run-113 lesson) ------------------
# The digest sidecar used to prove only that a module's OWN .v is unchanged. When an
# upstream module is recompiled (re-landed / cured piece), every seeded downstream
# .vo is stale yet still passed "vo-newer + own digest", so it was SKIPped and the
# next genuinely compiled consumer died with "Compiled library X makes inconsistent
# assumptions over library Y" (run 113: AlignIdUnclosed.v:40 over a stale
# UpAlignIdReq.vo). Now:
#   * the sidecar _X.vobuild.md5 carries TWO tokens: "<md5 of X.v> <closure digest>",
#     where the closure digest is the md5 over "<dep> <md5 of dep.vo>" lines for the
#     tree-internal dependencies coqdep reports for X. Any upstream .vo change --
#     whenever it happened -- flips the closure digest and forces a recompile;
#   * a legacy one-token sidecar is migrated without a blind cold rebuild: the .vo is
#     load-validated by Coq itself (`Require X.` probe -- Coq checks the recorded
#     dependency digests on load); a clean load writes the two-token sidecar and
#     SKIPs, a failed load means the .vo is stale and X is truly recompiled;
#   * before the loop, fail fast (seconds, not an hour) on libraries coqdep cannot
#     locate (run 113: GibbsFamilyExt.v requires UpRealLeB3) and on required .v files
#     present in the tree but absent from order.txt.
# Degradation: if coqdep cannot run, the legacy one-token semantics apply for this
# run and the fact is printed loudly -- never worse than before this patch.
# Sidecar consumers: only this script reads the content; the CI seed/purge steps and
# the write-back below handle *.vobuild.md5 by file name, so no yml change is needed.
order_files=()
declare -A ORDERSET=() DEPS_OF=() VOMD5=()
dep_graph=0
while IFS= read -r line || [ -n "$line" ]; do
  f="${line%%\#*}"; f="${f%$'\r'}"
  [ -z "$f" ] && continue
  order_files+=("$f"); ORDERSET["${f%.v}"]=1
done < "$LIVE/order.txt"

dep_out="$("$COQDEP" -Q "$LIVE" "" "$LIVE"/*.v 2>&1)"; dep_rc=$?
if [ "$dep_rc" -ne 0 ]; then
  echo "DEP-PRECHECK-DEGRADED: coqdep rc=$dep_rc -- legacy own-digest skip semantics (no closure fingerprint) for this run"
  printf '%s\n' "$dep_out" | tail -10
else
  if printf '%s\n' "$dep_out" | grep -q "has not been found in the loadpath"; then
    echo "BUILD-FAIL: MISSING-DEP -- coqdep cannot locate required libraries (batch incomplete; fix the landing set):"
    printf '%s\n' "$dep_out" | grep -B1 -A1 "has not been found in the loadpath" | sed 's/^/  /'
    echo "CACHE-BUILD-SUMMARY compiled=0 skipped=0 fail=1"
    exit 1
  fi
  while IFS= read -r l; do
    case "$l" in "$LIVE"/*.vo*:*) ;; *) continue ;; esac
    lhs="${l%%:*}"; rhs="${l#*:}"
    tgt="${lhs%% *}"; tgt="${tgt##*/}"; tgt="${tgt%.vo}"
    DEPS_OF["$tgt"]="${DEPS_OF[$tgt]:-}"
    for d in $rhs; do
      case "$d" in
        "$LIVE"/*.vo)
          dm="${d##*/}"; dm="${dm%.vo}"
          [ "$dm" = "$tgt" ] && continue
          DEPS_OF["$tgt"]="${DEPS_OF[$tgt]} $dm"
          ;;
      esac
    done
  done <<< "$dep_out"
  for m in "${!ORDERSET[@]}"; do
    for d in ${DEPS_OF[$m]:-}; do
      if [ -z "${ORDERSET[$d]:-}" ] && [ -f "$LIVE/$d.v" ]; then
        echo "BUILD-FAIL: ORDER-MISSING -- $d.v is in the tree and required by $m but absent from order.txt"
        fail=1
      fi
    done
  done
  if [ "$fail" -ne 0 ]; then
    echo "CACHE-BUILD-SUMMARY compiled=0 skipped=0 fail=1"
    exit 1
  fi
  dep_graph=1
  echo "DEP-PRECHECK: graph_nodes=${#DEPS_OF[@]} order_entries=${#order_files[@]}"
fi

vo_md5() {  # memoised md5 of $LIVE/$1.vo (deps are final when their dependents are processed)
  local m="$1"
  if [ -z "${VOMD5[$m]:-}" ]; then
    VOMD5["$m"]="$(md5sum "$LIVE/$m.vo" 2>/dev/null | cut -d' ' -f1)"
  fi
  printf '%s' "${VOMD5[$m]}"
}
closure_digest() {  # $1 = module; "-" when the module has no tree-internal deps
  local m="$1" d acc=""
  [ "$dep_graph" -eq 1 ] || { printf '%s' ""; return; }
  for d in $(printf '%s\n' ${DEPS_OF[$m]:-} | sort -u); do
    acc+="$d $(vo_md5 "$d")"$'\n'
  done
  if [ -z "$acc" ]; then printf '%s' "-"; else printf '%s' "$acc" | md5sum | cut -d' ' -f1; fi
}
PROBE_DIR="_build_probe"
probe_load_ok() {  # $1 = module; rc 0 when Coq loads $1.vo with a consistent dependency closure
  mkdir -p "$PROBE_DIR"
  printf 'Require %s.\n' "$1" > "$PROBE_DIR/_probe.v"
  "$COQC" -native-compiler no -q -Q "$LIVE" "" "$PROBE_DIR/_probe.v" > "$PROBE_DIR/_probe.log" 2>&1
  local rc=$?
  rm -f "$PROBE_DIR/_probe.vo" "$PROBE_DIR/_probe.vos" "$PROBE_DIR/_probe.vok" "$PROBE_DIR/_probe.glob" "$PROBE_DIR/.probe.aux" "$PROBE_DIR/._probe.aux" 2>/dev/null
  return $rc
}

while IFS= read -r line || [ -n "$line" ]; do
  f="${line%%\#*}"          # strip trailing #R-anchor
  f="${f%$'\r'}"            # CRLF-safe
  [ -z "$f" ] && continue
  if [ ! -f "$LIVE/$f" ]; then
    echo "BUILD-FAIL: order entry $f missing from $LIVE"
    fail=1
    continue
  fi
  m="${f%.v}"
  v="$LIVE/$m.vo"
  log="$LIVE/_$m.build.log"
  sc="$LIVE/_$m.vobuild.md5"
  # 20261030 digest sidecar guard (run 67 lesson): a seeded .vo from an older
  # generation of the same-named .v shadows the checkout -- seed cp refreshes
  # mtimes, so "vo newer than v" alone is unsound for relanded pieces. Skip
  # only when .vo is newer AND the compile-time sidecar digest matches the
  # current .v; missing/mismatched sidecar forces a true recompile.
  # 20261102: plus the dependency-closure digest (second sidecar token), see top.
  cur="$(md5sum "$LIVE/$f" 2>/dev/null | cut -d' ' -f1)"
  cdig="$(closure_digest "$m")"
  sc_own=""; sc_dep=""
  [ -f "$sc" ] && read -r sc_own sc_dep _ < "$sc"
  skip=0
  if [ -f "$v" ] && [ "$v" -nt "$LIVE/$f" ] && [ -n "$cur" ] && [ "$sc_own" = "$cur" ]; then
    if [ "$dep_graph" -ne 1 ]; then
      skip=1; why="vo-newer+digest"
    elif [ "$sc_dep" = "$cdig" ]; then
      skip=1; why="vo-newer+digest+closure"
    elif [ -z "$sc_dep" ]; then
      if probe_load_ok "$m"; then
        printf '%s %s\n' "$cur" "$cdig" > "$sc"
        skip=1; why="legacy-sidecar load-validated"; vld=$((vld+1))
      else
        echo "$m STALE(legacy sidecar, load probe failed: dependency closure changed) -> recompile"
        stale=$((stale+1))
      fi
    else
      echo "$m STALE(closure digest changed: an upstream .vo was rebuilt) -> recompile"
      stale=$((stale+1))
    fi
  fi
  if [ "$skip" -eq 1 ]; then
    echo "$f SKIP($why)"
    s=$((s+1))
    continue
  fi
  "$COQC" -native-compiler no -q -Q "$LIVE" "" "$LIVE/$f" > "$log" 2>&1
  rc=$?
  echo "$f EXIT=$rc"
  if [ "$rc" -ne 0 ]; then
    fail=1
    echo "----- last 30 lines of $log -----"
    tail -30 "$log"
  else
    n=$((n+1))
    unset "VOMD5[$m]"
    if [ "$dep_graph" -eq 1 ]; then printf '%s %s\n' "$cur" "$cdig" > "$sc"; else printf '%s\n' "$cur" > "$sc"; fi
  fi
done < "$LIVE/order.txt"
rm -rf "$PROBE_DIR" 2>/dev/null
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
    for v in "$LIVE"/*.vo; do
      [ -e "$v" ] || continue
      cp -f "$v" "$CACHE_WRITEBACK_DIR/" && wb=$((wb+1))
    done
    for m in "$LIVE"/*.vobuild.md5; do
      [ -e "$m" ] || continue
      cp -f "$m" "$CACHE_WRITEBACK_DIR/"
    done
    echo "CACHE-WRITEBACK: $wb .vo (+digest sidecars) -> $CACHE_WRITEBACK_DIR"
  fi
fi
echo "CACHE-BUILD-DEPCHECK legacy_validated=$vld stale_recompiled=$stale"
echo "CACHE-BUILD-SUMMARY compiled=$n skipped=$s fail=$fail"
exit $fail
