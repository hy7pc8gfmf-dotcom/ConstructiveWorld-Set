# ConstructiveWorld-Set — Pure-Constructivity Constraint Canon (CONSTRAINTS.md)

> **Version**: v1.0 (2026-10-26). **Authority chain**: the workspace white paper
> 《纯构造性纲领与红线律白皮书》v2.4+ is the legislature; THIS file is its
> in-repo execution canon for the ConstructiveWorld-Set repository — the single
> authority every collaborator (Windows / macOS / future machines) reads and
> obeys on this repo. Conflicts resolve upward to the white paper; propose
> changes here as PRs, they get ported to the white paper at the next revision.
>
> **Why this file exists** (20261026 user decree): the law was hardened in
> workspace documents, but a law without in-repo teeth lets collaborators
> drift — the macOS side was clearing extraction debt (M10, 58 Obj.magic → 0)
> without a mechanical gate to hold the line. This file plus gates 6/7 give
> Path A standing mechanical enforcement on this repo.

## 1. The six laws (condensed; white paper is normative)

1. **Constructivity** — zero global assumptions, zero proof surrender
   (`Admitted`/`admit`/`Abort`), zero check-weakening, zero classics/choice
   (`Classical`, `FunctionalExtensionality`, `ProofIrrelevance`, classical
   reals). Kernel verdict via `coqchk`/`Print Assumptions` = `Closed` is the
   only standard. lia/lra stock is frozen, never retroactive, touch = re-certify.
2. **Set-carrier (Path A, the unique constraint)** — every named construction
   (definitions, theorems, auxiliary lemmas, field positions) carried by
   Set/Type; predicate positions in decidable Set forms (`QltT`/`QeqT`);
   zero Prop components embedded in Set carriers; **zero new Prop statements**;
   the exception registry is frozen (stock sunsets are scheduled, no new rows).
   Proof-body constructive Prop consumption is tolerated but must shrink wave
   over wave (each wave receipt carries its body-Prop consumption list).
3. **Substance** — mission statements carry real derivation chains; bare
   `exact`/`reflexivity` endings on mission statements are violations;
   definitions are `Defined` (transparent).
4. **Extraction execution** — see §3 (the 4a–4d ladder). Extractable is not
   enough: extracted code must exist, run, be usable, and be fast enough.
5. **Honest interface** — every non-decidable premise is either discharged by a
   supplied theorem or explicitly disclosed at the interface (Set-carried,
   documented).
6. **Signature stability** — exported-signature changes ship with a migration
   ledger (old → new, bridges, downstream consumers file:line).

## 2. Prop-leakage: three channels and their gates

| Channel | What it is | Standing gate on this repo |
|---|---|---|
| ① statement faces | bare Prop statements | **gate6** `ch1` census — baseline is ZERO (audit 20261026: 57 files, 5,373 statement names, zero hits); any new hit is red |
| ② field positions | Prop-typed Record/Class/Inductive/section fields | **gate6** `ch2` census — baseline zero; any new hit is red |
| ③ embedded in Set carriers | Prop components inside Set-carried types (Qlt-in-sigT family) | invisible to word-face — **gate7 extraction diff is the final mechanical arbiter** (Obj.magic accounting both faces, erasure-candidate diff) |

Word-face scanning is a pre-screen only (carrier innovation escapes any word
list — R1). The gates make the pre-screen standing; the extraction diff makes
the semantics arbitrated.

## 3. Extraction-execution ladder (law IV)

| Cert | Meaning | Mechanical form on this repo |
|---|---|---|
| 4a extractable | statement faces Set-carried; definitions transparent; extraction diff zero name loss; **Obj.magic = 0 target** (stock tracked by baseline; growth = red = treated as Prop leakage) | **gate7**: per-module single-command `Separate Extraction` driver → `.ml`/`.mli` both-face magic accounting + name-presence diff. Run after build (needs `.vo`). |
| 4b executable | flagship witnesses compile (`ocamlc`) and run to termination | gate7 runs `ocamlc` when a toolchain is present (explicit skip-note otherwise); termination is the landing-gate receipt's duty (RunAlive) |
| 4c usable | sample runs produce the promised witness content, independently checkable; **exit 0 is NOT evidence** | landing-gate manual step with output-vs-contract table in the receipt |
| 4d performant | performance/precision budget per flagship witness, numbers in module docs; **over-budget unregistered = failing** (loud declarations are a registry-admission requirement, not compliance) | budget registry §6; enforcement at landing gates |

## 4. Gate chain (CI order, single Live tree)

```
gate1 poison tokens (pre-build, fail-fast, source face)
gate4 comment hygiene (five-field header + banned words, exit1 red / exit2 yellow)
gate6 statement+field Prop census (pre-build, static; --gate vs scripts/gates/gate6_baseline.json; red on growth only)
Build Live tree (order.txt topology; fingerprint SKIP over the seeded trust cache; thermal-guarded)
gate7 extraction execution (post-build; per-module 4a; --gate vs scripts/gates/gate7_extract_baseline.json; red on growth only)
gate5 .vo/.vos/.vok binary quarantine (pre-coqchk)
coqchk full-tree certification (shared closure, single pass)
gate2 axioms sentinel (block state machine; banner generation pin 9.1)
```

Gate baselines follow the three-tier doctrine: stock is frozen (never
retroactive), growth is red, new files/modules are born-clean (zero tolerance).
Baselines regenerate ONLY with an explicit `--baseline-out` run included in the
same commit, and the diff must justify every count increase.

## 5. Exception registry (repo-scoped)

**Empty — born-clean in force.** Stock exceptions (lia/lra freeze, conversion
bridge faces, Qlt grey-zone, Qlt-in-sigT mirror custody, lw0_qpoly_eq bridge)
are registered in the workspace white paper §四 against the MAIN repo's trees;
this repo carries none of them and accepts no new rows (registry frozen
20261024). A violation here cannot be excused by a main-repo registration.

## 6. Performance budget registry (4d)

Flagship witnesses register a quantified budget here (reference precision,
evaluation time/cost order-of-magnitude). Over-budget without a row here AND a
white-paper registry admission = failing. Current rows: none yet — M10's
UpReqSumD clearance established extraction cleanliness, budgets land with the
first 4c/4d landing-gate receipt (候登记).

## 7. Trust-cache channel (both-machine CI economics)

The Windows certification job seeds its build from the local trust cache
(`ConstructiveWorld_Live/*.vo`), builds with fingerprint SKIP (`.vo` newer than
`.v` → skip), and uploads the full `.vo` set as the `vo-trust-cache-set-windows`
artifact on success. **Since d362f90 (20261028) the channel is a two-way bus**:
the macOS job runs the symmetric three steps (sync from
`vo-trust-cache-set-windows` → mirror seed from `/Users/apple/vo_ci_cache_set` →
fingerprint SKIP in its inline build loop → green-gated export + upload of
`vo-trust-cache-set-macos`), and each job starts with a fail-open sync of the
opposite side's artifact. New modules cold-compile exactly once on whichever
side runs first; every later run on both sides is SKIP-fast. Seeding uses
MIRROR semantics (wipe the checkout's `.vo`, then copy the cache in) so the
build tree is a true image of the cache — stale survivors caused digest tears
under the old grow-only scheme (P9 lesson), do not reintroduce them.
`scripts/ci_build_live.sh` stays the cold-build truth;
`scripts/ci_build_live_cached.sh` is its fingerprint-skip twin.

**Cache-application audit doctrine** (20261028, six-run evidence base #36-#46):
pull the Windows job log and read three numbers — seeded N / SKIP count /
compiled count. Zero-leakage criterion: `compiled ≤ wave-new-modules +
genuinely-washed-modules` (a source-modified module recompiling is the
fingerprint working, not leakage). Certification submissions must follow
build-locally-first; a cold compile caused by Apple's push landing before our
local build is a process-ordering cost, not a channel defect.

**Green-gated write-back (20261029)**: `ci_build_live_cached.sh` honours
`CACHE_WRITEBACK_DIR` -- on a fully green build it mirrors the freshly
compiled .vo back into the local dev-tree cache, so every green Windows run
automatically re-aligns the local cache with the run's head (the
cache-ization broken chain when Apple's push triggers CI first is closed).
Guards: green-gated (red builds write nothing), same-platform by
construction, era guard (skipped when the dev tree carries uncommitted
tracked modifications). Version-consistency architecture: certification
layer (push -> CI on our runner) + cache layer (green-gated write-back) +
optional source layer (resident cw_repo_watch fetch/ff/rebuild, design in
runbook §6.3, activation pending).

## 8. Cross-machine CI etiquette

- The Windows job (`[self-hosted, Windows]`, pinned label — bare
  `self-hosted` let the macOS runner snipe it and die in ~25 s on a
  Windows-only shell path) is the certification face.
- The macOS job is observation (`continue-on-error`): red does not stain the
  run conclusion. Its green is still treated as a collaborator asset: **never
  push while any run of this repo is in flight** — the concurrency group
  cancels in-flight runs, and that is how collaborators' jobs get killed.
  Check `runs?status=in_progress` before every push.

## 9. Revision chain

- v1.0 (2026-10-26): initial canon. gate6 (statement+field census, zero
  baseline audited: 57 files / 5,373 names / 0 hits) and gate7 (per-module
  extraction execution, 4a automation, baseline pending first green build)
  standing in CI; trust-cache channel (seed/skip/upload) on the Windows job;
  macOS observation job untouched by design.

## 10. Anti-verification anchors

```bash
grep -c "Path A" CONSTRAINTS.md                      # ≥1
grep -c "gate6" CONSTRAINTS.md                       # ≥3
grep -c "gate7" CONSTRAINTS.md                       # ≥3
python scripts/gates/gate6_statement_census.py --tree ConstructiveWorld_Live --gate --baseline scripts/gates/gate6_baseline.json   # exit 0
```
