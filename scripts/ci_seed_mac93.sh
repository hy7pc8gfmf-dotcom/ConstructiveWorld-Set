#!/usr/bin/env bash
# ci_seed_mac93.sh -- macOS-lane W3-mode seeder (Rocq 9.3 trust cache) and, via
# --build, a bash-3.2-compatible port of the fingerprint-SKIP build loop.
#
# Two macOS constraints make this file necessary (measured 20261103, this host
# doubles as the self-hosted runner):
#   * macOS ships bash 3.2 (no associative arrays) and no md5sum binary. The
#     canonical scripts/ci_build_live_cached.sh (form A, Windows production)
#     uses both, so it cannot run here until a bash>=4 exists on PATH.
#   * The W3 seed sources are host-local directories of this self-hosted runner.
#
# Modes:
#   (no arg) | seed     Seed the checkout tree with mac-native 9.3 .vo + write
#                       two-token sidecars "<md5 of X.v> <closure digest>" in the
#                       exact format and algorithm of ci_build_live_cached.sh
#                       (its vo_md5/closure_digest, lines 94-108), so the
#                       canonical script accepts the seeded face verbatim once a
#                       bash>=4 is available.
#   --build             Seed, then run the bash-3.2-compatible port of the
#                       canonical build loop (order topology, DEP-PRECHECK,
#                       own-digest + closure-digest SKIP, load-validated legacy
#                       sidecar migration, identical CACHE-BUILD-SUMMARY anchors).
#   --build-only        Skip seeding; run the build port only (idempotence check).
#
# Seed sources, in priority order; every piece is seeded only against explicit
# .v-md5 provenance from its own source (cross-generation protection, run#51
# precedent):
#   S1  $SEED_CACHE_DIR (default /Users/apple/vo_ci_cache_set): this host's CI
#       green-door export. Provenance = _manifest.tsv rows "file<TAB>v_md5<TAB>vo_md5",
#       written by the Export trust cache step on every green run.
#   S2  $SEED_ATTEST_DIR (default /Users/apple/Desktop/vo93_mac_cache): W34-era
#       certified 320-piece native-9.3 cache. Provenance = attest tsv
#       $SEED_ATTEST_TSV (default /Users/apple/Desktop/vo93_work/attest/
#       mac93_attest_320.tsv; col1=file col3=src_md5). Measured 20261103 at the
#       rolling wash-wave heads: only pieces whose .v bytes never changed since
#       W34 can match, and seeding any of them INTO a closure seeded from S1
#       tears the burned digest chain -- S01_BaseRing.vo from S2/W34
#       (md5 720b4077...) inside an S1/run-cache closure whose S02_CauchyComplete.vo
#       burned the S1 digest (ec7f6258...) produced "Compiled library S02_
#       CauchyComplete makes inconsistent assumptions over library S01_BaseRing"
#       (dry-run round 1, LW3JointFill red). The closure digest sidecar only
#       proves tree-internal byte consistency; it cannot see which generation
#       burned a dependency's digest. Hence the SINGLE-SOURCE RULE: when the S1
#       manifest exists and has rows, S1 is the only source consulted (pieces
#       failing md5 reconciliation are left for honest recompilation, and their
#       consumers cascade via the closure digest); S2 is a whole-source fallback
#       used only when S1 yields nothing, never mixed per-piece with S1.
#
# Per-piece guards, in order: (1) era guard -- od first 8 bytes must equal
# 436f7121000160bc ("Coq!" + version 0x000160BC = 90300 = Rocq 9.3.0; 9.1 is
# ...5f f4 = 90100), else the piece is rejected, never seeded; (2) source .v
# md5 must equal the checkout .v md5, else rejected; (3) S1 additionally
# verifies the cached .vo against the manifest's own vo_md5 (source corruption
# guard). The closure-digest sidecars are written only after ALL .vo are in
# place, so every token2 is computed over the final seeded face.
#
# Fail-open by construction: any seeder fault purges everything it seeded and
# exits 0 -- the lane then takes an honest cold build (run#51 precedent: a
# seeding failure must degrade to cold compilation, never to a red or to a
# stale-seeded green).
set -u
cd "$(dirname "$0")/.." || exit 1
LIVE="ConstructiveWorld_Live"
ERA_MAGIC="436f7121000160bc"

# ---- md5sum shim ----------------------------------------------------------
# macOS has /sbin/md5 but no md5sum; ci_build_live_cached.sh and this script
# call md5sum. `md5 -r` prints "digest path" (file arg) or "digest" (stdin),
# identical to md5sum for `cut -d' ' -f1` consumers. The shim lives in /tmp
# (never in the tree) and is exported on PATH for the build step to reuse.
SHIM_DIR="${CW_MD5SHIM_DIR:-/tmp/cw_md5shim}"
if ! command -v md5sum >/dev/null 2>&1; then
  mkdir -p "$SHIM_DIR"
  printf '#!/bin/sh\nexec /sbin/md5 -r "$@"\n' > "$SHIM_DIR/md5sum"
  chmod +x "$SHIM_DIR/md5sum"
  PATH="$SHIM_DIR:$PATH"; export PATH
  echo "MAC-SEED: md5sum shim installed at $SHIM_DIR (backend /sbin/md5 -r) -- build step must keep it first on PATH"
fi
md5f() { md5sum "$1" 2>/dev/null | cut -d' ' -f1; }

# ---- toolchain ------------------------------------------------------------
COQDEP="${COQDEP:-${MAC_ROCQ93_ROOT:-}/bin/coqdep}"
COQC="${COQC:-${MAC_ROCQ93_ROOT:-}/bin/coqc}"
if [ ! -x "$COQDEP" ]; then
  echo "MAC-SEED-FAIL: coqdep not executable at $COQDEP (export MAC_ROCQ93_ROOT or COQDEP) -- fail-open: nothing seeded, honest cold build"
  exit 0
fi

mode_seed=1; mode_build=0
case "${1:-seed}" in
  seed|"") ;;
  --build)      mode_build=1 ;;
  --build-only) mode_build=2; mode_seed=0 ;;
  *) echo "usage: $0 [seed|--build|--build-only]"; exit 2 ;;
esac

# purge_seeded_face: remove everything this script could have put into the tree
# (mirror-clean semantics; build then recompiles every module from source).
purge_face() {
  rm -f "$LIVE"/*.vo "$LIVE"/*.vos "$LIVE"/*.vok "$LIVE"/*.vobuild.md5 2>/dev/null || true
}

# ---- pass 1: pick + copy .vo (era guard + md5 reconciliation) --------------
SEED_CACHE_DIR="${SEED_CACHE_DIR:-/Users/apple/vo_ci_cache_set}"
SEED_ATTEST_DIR="${SEED_ATTEST_DIR:-/Users/apple/Desktop/vo93_mac_cache}"
SEED_ATTEST_TSV="${SEED_ATTEST_TSV:-/Users/apple/Desktop/vo93_work/attest/mac93_attest_320.tsv}"
MANIFEST="$SEED_CACHE_DIR/_manifest.tsv"

have_cache=0; have_attest=0
[ -f "$MANIFEST" ] && have_cache=1
[ -f "$SEED_ATTEST_TSV" ] && [ -d "$SEED_ATTEST_DIR" ] && have_attest=1

# single-source rule (see header): S1 wins when its manifest has rows; S2 is a
# whole-source fallback only. Never mix sources within one seeding pass.
seed_from=""
if [ "$have_cache" -eq 1 ] && [ "$(wc -l < "$MANIFEST" | tr -d ' ')" -gt 0 ]; then
  seed_from="cache"
elif [ "$have_attest" -eq 1 ]; then
  seed_from="attest"
  echo "MAC-SEED: S1 manifest absent/empty -- whole-source fallback to S2 attest (single-source rule)"
else
  echo "MAC-SEED: no provenance-carrying source available -- nothing seeded, honest cold build (fail-open)"
  echo "MAC-SEED-SUMMARY seeded=0 (cache=0 attest=0) md5_reject=0 era_reject=0 nocache=0 sidecars=0"
  # --build-only / --build must still run the compile loop: the tree needs
  # .vo files on disk or every gate7 driver dies "Unable to locate library".
  # The bare `exit 0` here short-circuited those modes (20261112 run
  # 43142078293: empty cache dir -> 0.1s build step -> 510/510 driver rc=1).
  if [ "$mode_build" -ge 1 ]; then
    echo "MAC-SEED: build mode requested -- continuing into the cold build loop"
  else
    exit 0
  fi
fi

if [ "$mode_seed" -eq 1 ]; then
  purge_face
  seeded=0; md5_rej=0; era_rej=0; nocache=0; n_cache=0; n_attest=0
  SEEDED_LIST="$PWD/_seeded_list.txt"; : > "$SEEDED_LIST"
  while IFS= read -r line || [ -n "$line" ]; do
    f="${line%%\#*}"; f="${f%$'\r'}"; [ -z "$f" ] && continue
    [ -f "$LIVE/$f" ] || continue          # missing order entries fail loudly in the build loop
    m="${f%.v}"
    cur="$(md5f "$LIVE/$f")"
    [ -n "$cur" ] || { nocache=$((nocache+1)); continue; }
    pick=""; src=""
    if [ "$seed_from" = "cache" ]; then
      # S1: CI green-door export, manifest provenance
      row="$(awk -F'\t' -v mm="$m" '$1==mm{print;exit}' "$MANIFEST" 2>/dev/null)"
      if [ -n "$row" ]; then
        vmd5="$(printf '%s' "$row" | cut -f2)"; vomd5="$(printf '%s' "$row" | cut -f3)"
        cand="$SEED_CACHE_DIR/$m.vo"
        if [ "$vmd5" = "$cur" ]; then
          if [ -f "$cand" ] && [ "$(md5f "$cand")" = "$vomd5" ]; then
            pick="$cand"; src="cache"
          else
            echo "MAC-SEED: S1 $m vo/manifest digest mismatch (source corruption guard) -- not seeded"
          fi
        else
          md5_rej=$((md5_rej+1))
        fi
      fi
    else
      # S2 whole-source fallback: W34 attest archive, src_md5 provenance
      row="$(awk -F'\t' -v mm="$m" '$1==mm{print;exit}' "$SEED_ATTEST_TSV" 2>/dev/null)"
      if [ -n "$row" ]; then
        smd5="$(printf '%s' "$row" | cut -f3)"
        cand="$SEED_ATTEST_DIR/$m.vo"
        if [ "$smd5" = "$cur" ] && [ -f "$cand" ]; then pick="$cand"; src="attest"; else md5_rej=$((md5_rej+1)); fi
      fi
    fi
    if [ -z "$pick" ]; then nocache=$((nocache+1)); continue; fi
    magic="$(od -An -tx1 -N8 "$pick" 2>/dev/null | tr -d ' \n')"
    if [ "$magic" != "$ERA_MAGIC" ]; then
      era_rej=$((era_rej+1))
      echo "MAC-SEED: era-reject $m (magic=${magic:-none}, expected $ERA_MAGIC) -- not seeded"
      continue
    fi
    if ! cp -f "$pick" "$LIVE/$m.vo"; then
      echo "MAC-SEED-FAIL: cp failed for $m -- purging seeded face, honest cold build (fail-open)"
      purge_face; rm -f "$SEEDED_LIST"; exit 0
    fi
    echo "$m" >> "$SEEDED_LIST"
    echo "MAC-SEED: seeded $m (src=$src)"
    seeded=$((seeded+1))
    case "$src" in cache) n_cache=$((n_cache+1)) ;; attest) n_attest=$((n_attest+1)) ;; esac
  done < "$LIVE/order.txt"

  # ---- pass 2: closure-digest sidecars over the final seeded face --------
  # Dependency graph parse is byte-identical to ci_build_live_cached.sh L52-77:
  # lhs first token of "<targets>: <deps>" lines, tree-internal "$LIVE/*.vo" deps,
  # self excluded. coqdep failure = fail-open purge (sidecars without a sound
  # closure digest would lie about freshness).
  dep_out="$("$COQDEP" -Q "$LIVE" "" "$LIVE"/*.v 2>&1)"; dep_rc=$?
  if [ "$dep_rc" -ne 0 ]; then
    echo "MAC-SEED-FAIL: coqdep rc=$dep_rc -- purging seeded face, honest cold build (fail-open)"
    printf '%s\n' "$dep_out" | tail -5
    purge_face; rm -f "$SEEDED_LIST"; exit 0
  fi
  DEPSDIR="_seeddeps_$$"; rm -rf "$DEPSDIR"; mkdir -p "$DEPSDIR"
  printf '%s\n' "$dep_out" | while IFS= read -r l; do
    case "$l" in "$LIVE"/*.vo*:*) ;; *) continue ;; esac
    lhs="${l%%:*}"; rhs="${l#*:}"
    tgt="${lhs%% *}"; tgt="${tgt##*/}"; tgt="${tgt%.vo}"
    : > "$DEPSDIR/$tgt"
    for d in $rhs; do
      case "$d" in
        "$LIVE"/*.vo)
          dm="${d##*/}"; dm="${dm%.vo}"
          [ "$dm" = "$tgt" ] || echo "$dm" >> "$DEPSDIR/$tgt"
          ;;
      esac
    done
  done
  sd=0
  while IFS= read -r m; do
    acc=""
    for d in $(sort -u "$DEPSDIR/$m" 2>/dev/null); do
      acc="$acc$d $(md5f "$LIVE/$d.vo")"$'\n'
    done
    if [ -z "$acc" ]; then cdig="-"; else cdig="$(printf '%s' "$acc" | md5sum | cut -d' ' -f1)"; fi
    cur="$(md5f "$LIVE/$m.v")"
    printf '%s %s\n' "$cur" "$cdig" > "$LIVE/_$m.vobuild.md5"
    sd=$((sd+1))
  done < "$SEEDED_LIST"
  rm -rf "$DEPSDIR" 2>/dev/null; rm -f "$SEEDED_LIST"
  echo "MAC-SEED-SUMMARY seeded=$seeded (cache=$n_cache attest=$n_attest) md5_reject=$md5_rej era_reject=$era_rej nocache=$nocache sidecars=$sd"
  echo "MAC-SEED: provenance -- S1 manifest rows=$( [ "$have_cache" -eq 1 ] && wc -l < "$MANIFEST" | tr -d ' ' || echo 0), S2 attest rows=$( [ "$have_attest" -eq 1 ] && grep -c -v '^file' "$SEED_ATTEST_TSV" || echo 0)"
fi

# ---- build loop: bash-3.2-compatible port of ci_build_live_cached.sh ------
if [ "$mode_build" -ge 1 ]; then
  if [ "$mode_build" -eq 2 ]; then
    echo "MAC-SEED: --build-only, seeding skipped"
  fi
  fail=0; n=0; s=0; vld=0; stale=0

  # order list (plain array, bash3-safe)
  order_files=()
  while IFS= read -r line || [ -n "$line" ]; do
    f="${line%%\#*}"; f="${f%$'\r'}"; [ -z "$f" ] && continue
    order_files+=("$f")
  done < "$LIVE/order.txt"

  # ORDERSET as one flat string: membership via substring match (fast, no -A)
  ordidx=" "
  for f in ${order_files+"${order_files[@]}"}; do ordidx="$ordidx${f%.v} "; done

  # dependency graph via coqdep; on failure, legacy own-digest semantics for
  # this run (never worse than the canonical script's degradation)
  dep_graph=0
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
    DEPSDIR="_builddeps_$$"; rm -rf "$DEPSDIR"; mkdir -p "$DEPSDIR"
    printf '%s\n' "$dep_out" | while IFS= read -r l; do
      case "$l" in "$LIVE"/*.vo*:*) ;; *) continue ;; esac
      lhs="${l%%:*}"; rhs="${l#*:}"
      tgt="${lhs%% *}"; tgt="${tgt##*/}"; tgt="${tgt%.vo}"
      : > "$DEPSDIR/$tgt"
      for d in $rhs; do
        case "$d" in
          "$LIVE"/*.vo)
            dm="${d##*/}"; dm="${dm%.vo}"
            [ "$dm" = "$tgt" ] || echo "$dm" >> "$DEPSDIR/$tgt"
            ;;
        esac
      done
    done
    # ORDER-MISSING fail-fast: tree .v required but absent from order.txt
    ordfail=0
    for df in "$DEPSDIR"/*; do
      [ -f "$df" ] || continue
      tgt="${df##*/}"
      for d in $(cat "$df"); do
        case "$ordidx" in *" $d "*) ;; *)
          if [ -f "$LIVE/$d.v" ]; then
            echo "BUILD-FAIL: ORDER-MISSING -- $d.v is in the tree and required by $tgt but absent from order.txt"
            ordfail=1
          fi ;;
        esac
      done
    done
    if [ "$ordfail" -ne 0 ]; then
      rm -rf "$DEPSDIR" 2>/dev/null
      echo "CACHE-BUILD-SUMMARY compiled=0 skipped=0 fail=1"
      exit 1
    fi
    dep_graph=1
    echo "DEP-PRECHECK: graph_nodes=$(ls "$DEPSDIR" | wc -l | tr -d ' ') order_entries=${#order_files[@]}"
  fi

  vo_md5_of() {  # memoised per-module md5 in /tmp files (bash3-safe memo)
    mm="$1"
    cache_f="/tmp/cw_vomd5_$$/$mm"
    if [ ! -f "$cache_f" ]; then
      mkdir -p "/tmp/cw_vomd5_$$" 2>/dev/null
      md5f "$LIVE/$mm.vo" > "$cache_f"
    fi
    cat "$cache_f" 2>/dev/null
  }
  forget_vo_md5() { rm -f "/tmp/cw_vomd5_$$/$1" 2>/dev/null; }
  closure_digest_of() {  # "-" when no tree-internal deps; md5 over "d <vo_md5>" lines
    mm="$1"; acc=""
    if [ "$dep_graph" -eq 1 ]; then
      for d in $(sort -u "$DEPSDIR/$mm" 2>/dev/null); do
        acc="$acc$d $(vo_md5_of "$d")"$'\n'
      done
    fi
    if [ -z "$acc" ]; then printf '%s' "-"; else printf '%s' "$acc" | md5sum | cut -d' ' -f1; fi
  }
  PROBE_DIR="_build_probe"
  probe_load_ok() {  # rc 0 when Coq loads $1.vo with a consistent dependency closure
    mkdir -p "$PROBE_DIR"
    printf 'Require %s.\n' "$1" > "$PROBE_DIR/_probe.v"
    "$COQC" -native-compiler no -q -Q "$LIVE" "" "$PROBE_DIR/_probe.v" > "$PROBE_DIR/_probe.log" 2>&1
    prc=$?
    rm -f "$PROBE_DIR/_probe.vo" "$PROBE_DIR/_probe.vos" "$PROBE_DIR/_probe.vok" "$PROBE_DIR/_probe.glob" "$PROBE_DIR/.probe.aux" "$PROBE_DIR/._probe.aux" 2>/dev/null
    return $prc
  }

  for f in ${order_files+"${order_files[@]}"}; do
    if [ ! -f "$LIVE/$f" ]; then
      echo "BUILD-FAIL: order entry $f missing from $LIVE"
      fail=1
      continue
    fi
    m="${f%.v}"
    v="$LIVE/$m.vo"
    log="$LIVE/_$m.build.log"
    sc="$LIVE/_$m.vobuild.md5"
    cur="$(md5f "$LIVE/$f")"
    cdig="$(closure_digest_of "$m")"
    sc_own=""; sc_dep=""
    [ -f "$sc" ] && { read -r sc_own sc_dep _ < "$sc"; } 2>/dev/null
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
      forget_vo_md5 "$m"
      if [ "$dep_graph" -eq 1 ]; then printf '%s %s\n' "$cur" "$cdig" > "$sc"; else printf '%s\n' "$cur" > "$sc"; fi
    fi
  done
  rm -rf "$PROBE_DIR" "$DEPSDIR" "/tmp/cw_vomd5_$$" 2>/dev/null
  if [ "$fail" -ne 0 ]; then
    echo "BUILD-FAIL: one or more files failed (true RC accounted above)"
  fi
  echo "CACHE-BUILD-DEPCHECK legacy_validated=$vld stale_recompiled=$stale"
  echo "CACHE-BUILD-SUMMARY compiled=$n skipped=$s fail=$fail"
  exit $fail
fi
exit 0
