#!/usr/bin/env bash
# CI coqchk certification for the single ConstructiveWorld_Live tree — PARALLEL (K lanes).
# Canon: whitepaper v1.3 section 8 (bytecode flag mandatory) + Main parallel_chk pattern
# (root-grouped lanes; each lane checks a disjoint target set and ADMITS every other
# module, so the whole tree is kernel-checked exactly once across lanes).
#
# Selection:
#   SET_CHK_JOBS unset or <=1  -> exact legacy serial behavior (ci_coqchk_live.sh path)
#   SET_CHK_JOBS=K (>=2)       -> K parallel lanes (round-robin partition of the module
#                                 roster; per-lane logs merged into ConstructiveWorld_Live/
#                                 _chk_all.log preserving per-lane Chicken banner + Axioms
#                                 sections, so gate2's banner grep and the block-state-machine
#                                 parser consume the merged log unchanged).
# Fallback contract identical to the serial script: _chk_all.log + COQCHK_EXIT + banner
# grep + gate2 parser all keep their meaning; any lane failure = step failure (fail-loud).
set -u
# Form A (Rocq 9.3 migration wave, 20261102): COQCHK env-overridable, COQLIB/ROCQLIB
# derive via the SW2 same-root rule. Defaults keep the 9.1 platform byte-for-byte.
COQCHK="${COQCHK:-C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe}"
case "$COQCHK" in
  */bin/coqchk.exe) _root="${COQCHK%/bin/coqchk.exe}"; export COQLIB="${COQLIB:-$_root/lib/coq}"; export ROCQLIB="${ROCQLIB:-$COQLIB}" ;;
  *) export COQLIB="${COQLIB:-C:/Rocq-Platform~9.1~2026.01/lib/coq}"; export ROCQLIB="${ROCQLIB:-$COQLIB}" ;;
esac
cd "$(dirname "$0")/.." || exit 1
log="ConstructiveWorld_Live/_chk_all.log"
mods=()
for vo in ConstructiveWorld_Live/*.vo; do
  [ -e "$vo" ] || { echo "COQCHK-FAIL: no .vo products in ConstructiveWorld_Live (build step missing?)"; exit 1; }
  b="$(basename "$vo" .vo)"
  case "$b" in _*) continue ;; esac
  mods+=("$b")
done
if [ "${#mods[@]}" -eq 0 ]; then
  echo "COQCHK-FAIL: zero certifiable modules"
  exit 1
fi
K="${SET_CHK_JOBS:-1}"
case "$K" in ''|*[!0-9]*) K=1 ;; esac
[ "$K" -ge 1 ] || K=1
n="${#mods[@]}"
if [ "$K" -le 1 ] || [ "$K" -ge "$n" ]; then
  echo "coqchk modules (${n}) serial (SET_CHK_JOBS=${K})"
  "$COQCHK" -o -bytecode-compiler yes -Q "ConstructiveWorld_Live" "" "${mods[@]}" > "$log" 2>&1
  rc=$?
  echo "COQCHK_EXIT=$rc"
  if [ "$rc" -eq 0 ] && grep -q "Modules were successfully checked" "$log"; then
    echo "COQCHK_ALL_PASS"
    exit 0
  fi
  echo "COQCHK_ALL_FAIL: see $log"
  tail -30 "$log"
  exit 1
fi
# ---- parallel path (K lanes, round-robin partition, -admit the rest) ----
echo "coqchk parallel: modules=${n} lanes=${K} (SET_CHK_JOBS)"
lane_dir="ConstructiveWorld_Live/_chk_lanes"
rm -rf "$lane_dir"; mkdir -p "$lane_dir"
pids=()
lane_rc=()
g=0
while [ "$g" -lt "$K" ]; do
  targets=(); admits=()
  i=0
  for m in "${mods[@]}"; do
    if [ $(( i % K )) -eq "$g" ]; then targets+=("$m"); else admits+=("$m"); fi
    i=$(( i + 1 ))
  done
  [ "${#targets[@]}" -eq 0 ] && { g=$(( g + 1 )); continue; }
  ll="$lane_dir/lane_$g.log"
  (
    adm=""
    for a in "${admits[@]}"; do adm="$adm -admit $a"; done
    "$COQCHK" -o -bytecode-compiler yes -Q "ConstructiveWorld_Live" "" $adm "${targets[@]}" > "$ll" 2>&1
    echo "$?" > "$ll.rc"
  ) &
  pids+=("$!")
  lane_rc+=("$ll")
  g=$(( g + 1 ))
done
fail=0
for j in "${!pids[@]}"; do
  wait "${pids[$j]}"; r="$(cat "${lane_rc[$j]}.rc" 2>/dev/null || echo 1)"
  [ "$r" -ne 0 ] && fail=1
done
# merged log for gate2 (banner grep + multi-section parser both consume this)
: > "$log"
for j in "${!lane_rc[@]}"; do cat "${lane_rc[$j]}" >> "$log" 2>/dev/null; done
echo "COQCHK_PARALLEL_SUMMARY lanes=$K modules=$n fail=$fail"
echo "COQCHK_EXIT=$fail"
if [ "$fail" -eq 0 ] && grep -q "Modules were successfully checked" "$log"; then
  echo "COQCHK_ALL_PASS"
  exit 0
fi
echo "COQCHK_ALL_FAIL: see $log"
tail -40 "$log"
exit 1
