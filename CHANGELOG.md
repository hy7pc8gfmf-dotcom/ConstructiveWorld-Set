# Changelog

All notable changes to this library are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [2026-11-11] — pool-erratum rows restored, dual-lane certification green run

### Changed

- The seven registration rows still missing at the `10a2402b` landing —
  the rows its tree carried outside the registration order, identified by
  the commit message as rows from the pool erratum disclosed in
  `9a51c74` — restored to the registration order (`2f1ffbaf`): 530 → 537
  registered rows, re-anchored in the #R97 batch.

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
