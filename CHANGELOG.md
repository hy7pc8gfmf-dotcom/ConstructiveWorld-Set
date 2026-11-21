# Changelog

All notable changes to this library are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [2026-11-22] — root-docs alignment wash and repair pass

### Changed

- Root five-document alignment wash (`README.md` / `README.en.md` /
  `NOTICE.md` / `CONSTRAINTS.md` / this file): counts re-derived against
  the current tree (595 `.v` sources in the tree; 604 registration rows,
  9 files double-registered, 595 unique; batches `#R0`–`#R232`), stale
  links and legal-anchor coordinates refreshed, bilingual pair re-synced,
  and the CI-chain description corrected to the serial green baseline
  (the 2026-11-19 K-lane parallel `coqchk` trial was reverted the same
  day; the workflow calls the serial `scripts/ci_coqchk_live.sh`)
  (`68ed639`).
- Repair pass over the same wave (this commit): batch R229 changelog
  entry backfilled (see 2026-11-20); NOTICE.md author line completed to
  the six-author table (`Baiyuan Zeng` added) and its header de-tangled
  (this repository is ConstructiveWorld-Set, 595 registered modules —
  the old header carried the Main name with a Set row count); the `.vo`
  trust-cache license wording aligned with the tracked face (no `.vo` is
  tracked; caches circulate as CI artifacts and runner-local copies);
  CONSTRAINTS §11 anchor coordinates re-verified with three stale sites
  re-pointed and a §9 v1.2 entry added for the canon edits; the Windows
  `coqchk` step name in `.github/workflows/coq.yml` corrected from its
  stale K-lane label to the serial call it actually runs.

## [2026-11-21] — mainwash supply waves R230–R232

### Added

- mainwash-s3 supply, 7 pieces born-clean, batch R230 (`3e16c75`).
- mainwash-nl supply, 5 pieces born-clean, batch R231 (`f7f7a7d`).
- mainwash-n2 supply, 7 pieces born-clean, batch R232 (`f4dcb41`).

## [2026-11-20] — mainwash-b1/b2 supply, gate7 policy-debt registration

### Added

- mainwash-b1 supply, 6 pieces born-clean, batch R228 (`20efc43`).
- mainwash-b2 supply, 8 pieces born-clean, batch R229 (`4b8804b`).

### Changed

- gate7 baseline registered `UpAblD1S2_reqlog_UpReqCauchy` as policy-debt
  magic=41 — the wash w1-b6 declared debt, extraction evidence in run
  44562457343; red-line v2.3 4d registration: declaration in the wash
  commit, reason=policy-debt Set-gen re-baseline, improvement path=open,
  sunset=review on the next wash round (`666a957`).

## [2026-11-19] — mainwash waves begin, w1-b6 supply, chk lane round-trip, LW3 park

### Added

- mainwash-inherit supply, 5 pieces born-clean, batch R227 (`8be387e`).
- w1-b6 Main-to-Set supply, 12 pieces — carrier re-cast + Abbreviation
  re-cast + interface alignment, gates green (`6716113`).

### Changed

- CI chk lane adopted the Main CI canon — K-lane parallel coqchk
  (`SET_CHK_JOBS=14`, lane-admit partition, merged log keeps the gate2
  contract; bytecode flag per whitepaper section 8), ci-ops whitepaper
  v1.3 embedded (synced snapshot), rocqwash triage watch (observer v1)
  (`fb0cba0`); reverted the same day to the serial green baseline after
  K-lane round-robin admits tripped the admit-boundary anomaly on a
  seeded stale-generation vo — the proper parallel_chk port with
  cost-table packing is a follow-up ticket; triage watch invokes the
  driver from the local aligned clone (NETRED-immune, no checkout step)
  (`c3248fd`).
- gate7 explicit per-module extraction timeout 600s — the tiered default
  240s tree-killed heavy low-name-count modules (`LW3FamScale` /
  `LW3JointFill` in run 44530406768); the script's WF-C tier by
  names_total misses heavy low-name modules, the explicit timeout is
  honored verbatim per the script docstring (`bc6fec7`).

### Fixed

- w1-b6 desk-review split held back 2 of the 12 pieces — the
  `uabda_g13_evict_discharge` re-cast referenced `uab_ssUnit` (a Main
  UpAblP2-family name absent in the Set tree) and the
  `UpAblDeltaStarSuboptimal` re-cast broke in-tree consumer
  `UpAblDeltaStarGeneral.v`; both files restored to main bytes, the
  remaining 10 pieces proceed to CI (`5502cbf`).

### Removed

- `LW3FamScale` and `LW3JointFill` removed from the tree — Separate
  Extraction diverges (>1500s no completion, quiet machine double
  trial), red-line IV extraction-incompatible as inherited (mainwash
  R227), zero consumers verified, extraction-safe re-cast ticket to the
  wash author (`287c1d3`); registration lines removed with the source —
  7b registry-build-certification consistency law, order coverage
  assertion red (`69db5bf`).

## [2026-11-14] — MixTimeChain leaf chain supply

### Added

- MixTimeChain leaf chain landed, 2 pieces born-clean, batch R226
  (`740b525`).

## [2026-11-13] — G1 witness pipeline landing, registry hygiene

### Added

- G1 witness pipeline landing, 8 pieces + orphan restoration
  (2 pieces) (`0d58903`).

### Changed

- Registry hygiene: 12 duplicate `_CoqProject` rows deduplicated,
  keep-first per the audit fix-plan (`d5153d5`).
- Registry hygiene cycle-2: canonical form re-anchored (541 rows) +
  orphan registration (3 pieces) (`987a1b5`).

## [2026-11-12] — route2-tierA supply, mac-lane fix restoration

### Added

- route2-tierA supply, 7 pieces on top of main `429ed53` (`9b9631b`).

### Fixed

- The two mac-lane fixes lost in a rebase restored — gate7 tree
  absolutization + seed pre-check fallthrough (`074eaa4`).

## [2026-11-11] — pool-erratum rows restored, docs+comments wash, registry order move, dual-lane certification green run

### Changed

- The seven registration rows still missing at the `10a2402b` landing —
  the rows its tree carried outside the registration order, identified by
  the commit message as rows from the pool erratum disclosed in
  `9a51c74` — restored to the registration order (`2f1ffbaf`): 530 → 537
  registered rows, re-anchored in the #R97 batch.
- docs+comments wash: stale facts refreshed and oversized module headers
  compressed across 35 tree modules, plus CONSTRAINTS.md, NOTICE.md and
  the README pair (`eb4b557`).
- Registry order: `uabd_supply_S05_Z_align_pos_unit` moved directly after
  its dependency `UpAblT13c_G13` (`429ed53`).

### Certification

- Dual-lane (windows+macOS) certification green run #293 —
  `COQCHK_ALL_PASS` + gate2 CLEAN with zero axioms. Certification
  conclusions follow the Actions page's current state (the Actions page is
  the sole source of current truth); no green beyond it is claimed in
  advance.

## [2026-11-10] — Main supply batches, dual-lane certification green run

### Added

- b53–b57 Main-to-Set supply, 14 pieces (`b3ae0ad`).
- b48–b52 Main-migration supply, 13 pieces (`10a2402b`).

### Certification

- Dual-lane (windows+macOS) certification green run #292 —
  `COQCHK_ALL_PASS` + gate2 CLEAN with zero axioms, the mac lane carrying
  the gate6/gate7 alignment. Certification conclusions follow the Actions
  page's current state (the Actions page is the sole source of current
  truth); no green beyond it is claimed in advance.

## [2026-11-09] — Windows-lane source-fetch channel, gate7 recast, surface reconciliation

### Changed

- Windows-lane source fetch moved to the API tarball of the run's sha,
  with the ref-quiescence gate on the same API channel (`b943764`).
- gate7 concrete-face recast and consumer-face stitching chain
  (`022f2e9` series).
- Three supply branches merged (`f7af973a`).
- Registration surface reconciled: 503 = 503 (`d448bbd`).

### Fixed

- QltT signature-face regression reverted (`6fec74e`).

## [2026-11-08] — registration surface completion

### Changed

- Registration surface completed: +31 registered, 5 dedup rows removed →
  487 = 487 (`95e7631`).

## [2026-10-31] — M34–M38 waves, queue-mode CI, archive refreshes

### Added

- M34 fourteen-piece discharge batch — parameter-shift adaptations + nw2 wave
  (statement-face Set-carrier completion) (`5e2938d`, registration rows in
  `fba7986`).
- M38 two-piece discharge batch — nw5 wave, generational-cure generations,
  tree-world verified (`59fc860`, registration rows in `14d9c0a`).

### Changed

- CI concurrency switched to queue mode (`cancel-in-progress: false`):
  dispatched runs now wait for the current run to complete instead of
  cancelling it (`23e7368`).
- Content-addressed attestation archive refreshed after green runs —
  157-piece full-tree generation post run-83 (`678edd9`) and 158-piece
  full-tree generation post run-85 (`d2e7911`).

### Fixed

- M33a: `ToyR_UpAblP7_AbsNonNeg` extraction cure — notation-recarrier
  restructure bringing the probe `Obj.magic` count 7 → 0 after the gate7
  born-clean interception; registration anchor updated to the cured
  generation (`58b5704`, `a2aa7d9`); run #74 green.

## [2026-10-30] — M29–M33 waves, W3 report-only wiring

### Added

- W3 content-addressed attestation wiring v1, report-only (`e976bef`):
  per-run reconciliation report over the module archive; the exit code is
  always captured and never gates a run.
- M29 two-piece landing with `UpTVDoeblin` swapped to the English-form
  generation (`9f8329d`); M30 klcure wave finals (`917b36b`); M31 cure-pair
  relanding (`ffd3d4b`, registration `2863121`); M32 abl7 dependency-closure
  batch A with the fa56b_ext extraction fix (`6ac5605`, `28caa3b`); M33
  nine-piece discharge batch with gate7 retrofit (`8ea8e0a`, `3716f8b`).

### Removed

- M30R: withdrew `KLWallClosed` and `RateTheoryAblation` after the first
  gate7 born-clean interception (extraction `Obj.magic` = 2 on a new
  module) (`1aade35`); both returned cured in the M31 relanding.

### Fixed

- M29F: excluded `abl_Pr_lcm_eq` (its `abl_Pr` dependency chain had been
  trimmed from the tree — returned to the source bench, registration
  reverted) and restored the mac-job stack-wall prescription in CI Build
  (`015c4bd`).
