#!/usr/bin/env bash
# CI coqchk certification for the single ConstructiveWorld_Live tree.
# Shared-closure single pass with -o (no -o, no Axioms section = unverifiable, gate2 fails red).
# Self-contained: replaces the retired D:\actions-runner cw_chk.cmd wrapper.
set -u
# Form A (Rocq 9.3 migration wave, 20261102): COQCHK is env-overridable and
# COQLIB/ROCQLIB derive from it via the SW2 same-root rule
# (<root>/bin/coqchk.exe -> <root>/lib/coq), mirroring ci_build_live_cached.sh.
# Defaults keep today's 9.1 platform byte-for-byte (zero change when env unset).
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
echo "coqchk modules (${#mods[@]}): ${mods[*]}"
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
