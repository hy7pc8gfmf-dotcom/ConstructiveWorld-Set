# ConstructiveWorld: Constructive Mathematics Library (Rocq/Coq)

[![Coq CI](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/workflows/coq.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

This repository is the constructive mathematics library accompanying the paper "Constructive three representations of π": the whole library states its existential conclusions with explicit `sigT` witnesses at the `Set` layer, introduces no axioms, and is extractable end to end. Chinese version: [README.md](README.md).

## Authors and contributors

| Author | ORCID |
|---|---|
| Baojun Wang | [0009-0001-4240-9045](https://orcid.org/0009-0001-4240-9045) |
| Guangzhao Zu | [0009-0006-7811-6638](https://orcid.org/0009-0006-7811-6638) |
| Wanlan Xia | [0009-0008-7359-044X](https://orcid.org/0009-0008-7359-044X) |
| Baiyuan Zeng | [0009-0005-9811-5598](https://orcid.org/0009-0005-9811-5598) |
| Zhinong Zhou | [0009-0001-3206-5824](https://orcid.org/0009-0001-3206-5824) |
| Xuefeng Gao | [0009-0007-9904-1599](https://orcid.org/0009-0007-9904-1599) |

## 1. Library overview

- **Scale**: 595 registered modules (registration order `ConstructiveWorld_Live/order.txt`: 604 rows, no blank lines, registration batches `#R0`–`#R232`, measured 2026-11-22; it grows as registration advances; the current state governs). The 604 rows cover 595 unique registered files: 586 files carry one row each, and 9 files carry two rows each (each of the 9 keeps its original row and also holds a second row in a contiguous `#R97` block). The registration order is the library's authoritative reference surface: one row per registration event, of the form `S01_BaseRing.v#R0-5feadce2`, where the part after `#` is the registration batch fingerprint; the tree's `.v` files (595) and the unique registered files (595) have zero set difference (measured 2026-11-22).
- **Content surface**: the S01–S15 constructive reals and analysis base; the upper-bound requirements family for Banach norms and Padé approximation (`UpReqBanach*` / `UpReqPade*`); the Boltzmann/Gibbs, GRPO/DPO alignment and entropy surface (S05/S06/S08/S09); attention-chain bounds (`Attn*`); and the companion machinery surface (`b1_*`, `mach_fold_q`, `abl_z2/z3_pointwise`, `abl_Hqarch_*`, `fib_machine`).
- **Purely constructive**: the library uses no `Axiom`, no `Admitted`, and no classical logic; the kernel-level `coqchk -o` recheck convention is `Axioms: <none>` (this repository's convention requirement; the cloud-side settled status is governed by the §2 "CI certification" row, and no audit conclusion is claimed in advance).
- **Explicit `sigT` witnesses at the `Set` layer**: existential conclusions always come with computable witnesses (rational endpoints, approximate roots, etc.), never remaining at the propositional layer.
- **Extractable**: target-language code is generated via `Separate Extraction`, and gate7 mechanically checks the per-module `Obj.magic` count against a committed baseline (`scripts/gates/gate7_extract_baseline.json`; growth beyond the registered count turns the run red). As baselined, 9 of the 282 modules carry registered nonzero counts (largest: `UpReqAttnGibbs`, 809), and the other 273 carry no registered nonzero count (272 measured at zero; `S11_TP3B5` has no extraction artifact on record); a count rising beyond its registered baseline is the signal for Prop-layer content newly leaking into the extraction surface.
- **The "rate-is-algorithm" paradigm**: the executable artifact (a `Defined` computation) and its correctness certificate (a `Qed` proof) coexist in one body: theorems and programs are two faces of the same thing.

**Division of labor among sister repositories**: the full certified library (a certified surface of 1021 files, with the π ladder, the five-constants family, and the ZZ measure route) lives in [ConstructiveWorld-Main](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main); Main completed its kernel full-closure certification on Rocq 9.3.0 (2026-11-07 run #9, `coqchk` over 14 groups, `Axioms: <none>`, GPG-signed tag `GREEN-CERTIFIED-v1`; see its README §2 for the publication surface). This repository is the condensed `Set`-layer registration surface.

**The π pillar as an independent package**: the constructive strong irrationality of π is published as the independent Rocq package [rocq-pi-leibniz](https://github.com/hy7pc8gfmf-dotcom/rocq-pi-leibniz) (Leibniz window method · `Set`-layer carriers · zero axioms · extractable witnesses), at `v1.0.4` (the tag dereferences to commit `e1891fce`; that package's CI status is independent of this repository; see the rocq-pi-leibniz repository page for its current state), archived on Zenodo under DOI [10.5281/zenodo.23656983](https://doi.org/10.5281/zenodo.23656983) (the integration line, concept 23656982); the v1.0.0 batch is merged into the Rocq opam repository (rocq-prover/opam #3884), and the status of the consolidated PR [#3899](https://github.com/rocq-prover/opam/pull/3899) for v1.0.1–1.0.4 (supersedes #3896/#3897/#3898) follows the upstream PR page's current state. Earlier, its generic escape-window criterion engine was submitted upstream to the Rocq standard library rocq-prover/stdlib (Issue #312 / PR #313); following the maintainers' feedback, that route was turned into the independent-library publication path (the package above).

## 2. Version and certification record

| Item | Value |
|---|---|
| Library version | `f4dcb41` (`main` branch, measured 2026-11-22) |
| CI certification | most recent settled green run **#293** (2026-11-11 · Windows + macOS dual-track all-step green · `COQCHK_ALL_PASS` · gate2 CLEAN, 0 axioms): certification conclusions follow the Actions page's current state (the Actions page is the sole source of current truth), and no green beyond it is claimed. This snapshot was recorded on 2026-11-11; the 2026-11-22 revision could not re-verify it from the local tree. The green face previously recorded in this table ended at run #55 (head `5293f1b`, 2026-10-29); the run states between #55 and #293 are not itemized in this table |
| Axiom audit | convention requirement: a whole-library `coqchk -o` recheck must yield `Axioms: <none>`. The most recent settled green run recorded here is #293 (2026-11-11): gate2 CLEAN, 0 axioms; audit conclusions follow the Actions page's current state, and none beyond it is claimed in advance |
| Registration order | `order.txt`, 604 rows, no blank lines, covering 595 unique registered files (9 files carry two rows each; `#R0`–`#R232`; measured 2026-11-22) |
| License | Apache-2.0 (see `LICENSE`) |

On every push, continuous integration (`.github/workflows/coq.yml`) runs (Windows certification job; the macOS observation job `coq-build-macos` was unblocked on 2026-11-03): gate1 poison-token guard → gate4 comment sentinel → gate6 statement-and-field Prop census (red = growth) → vo trust-cache seed at start (mirror semantics, fail-open) → full-tree compilation (single Live tree, order topology, cold build, thermal-guarded) → gate7 extraction execution (red = growth) → tree-stats generation and upload → gate5 vo-binary quarantine (token + digest, control-calibrated) → whole-tree `coqchk` kernel recheck (shared-closure single pass on both tracks; a Windows K-lane parallel trial on 2026-11-19 was reverted to the serial green baseline the same day, with the proper parallel port left as a follow-up ticket; thermal-guarded) → vo trust-cache upload → gate2 axiom sentinel (a block state machine parses the `coqchk` log for `Axioms: <none>`) → `coqchk` log upload. The gate3 cross-tree diff was removed in the 2026-10-07 single-tree consolidation (#C-S00c); its script (`scripts/gates/gate3_cross_tree_diff.py`) is still present in the tree, and no CI step invokes it. The sentinel scripts live in `scripts/gates/`. The repository also carries `.github/workflows/rocqwash-triage.yml` (a run-result observer, added 2026-11-19), which takes no part in certification. The CI toolchain generation is pinned to `Welcome to Chicken 9.3.0` (Rocq 9.3.0, re-based 2026-11-02); the toolchain generation is not the certification conclusion (see the CI certification row above).

## 3. Environment prerequisites

- **Rocq / Coq 9.3.0** (this repository's CI generation; `.github/workflows/coq.yml` gate2 pins `Welcome to Chicken 9.3.0`). Older versions are unverified; after changing the verification environment, rerun the four steps below.
- **Sister-repository certification (cross-reference)**: ConstructiveWorld-Main completed its kernel full-closure certification on Rocq 9.3.0 (tag `GREEN-CERTIFIED-v1`, `coqchk` over 14 groups, `Axioms: <none>`, 2026-11-07); that certification belongs to the Main repository and does not represent this repository's CI current state; this repository's most recent settled green on record is run #293 (settled 2026-11-11), and the Set-side certification status follows this repository's Actions page's current state.
- No external OCaml dependencies; extraction products are plain OCaml sources kept as audit objects, and no executable OCaml environment is required.

## 4. Reproduction: four-step verification

Verbatim identical to §6 "four-step command forms" of the paper. Run the commands inside `ConstructiveWorld_Live/`; the tree uses the `-Q . ""` flat namespace. The full-tree driver is `.github/workflows/coq.yml`.

```sh
# ① Full compilation: file by file in order.txt registration order (direct local invocation; full-tree driver in the CI workflow)
rocq compile -Q . "" S01_BaseRing.v
# ② Axiom audit: **the audit statements are `Print Assumptions <statement>.` commands written verbatim inside the source files** (e.g. two in S14_B5BatchBlock.v, for `b5d1_Heps4` and `b5dE_zero_le_one`), re-verified automatically at compile time; expected output: Closed under the global context
# ③ Extraction audit: the Obj.magic count in the .ml files produced by Separate Extraction is checked against the committed gate7 baseline (scripts/gates/gate7_extract_baseline.json); growth beyond the module's registered count is red
coqtop -q -Q . "" <file>.v            # run Separate Extraction <statement>.
grep -c Obj.magic <file>.ml           # compare with the module's baseline entry (0 for most modules)
# ④ Kernel recheck: take the logical library name from the head of <file>.glob (the actual prefix under -Q . ""); do not substitute the file name
coqchk -silent -Q . "" <logical-library>.<file>
```

Notes:

- The logical library name is **not** the file name. For example, the logical name of `S01_BaseRing.v` is `FS01_BaseRing` (line 2 of `S01_BaseRing.glob`). In step ④, using the file name instead makes `coqchk` report a missing library.
- In step ①, executing files one by one in `order.txt` line order satisfies the dependency order; resolve any single-file failure before continuing.
- The four steps cover all registered files of the registration surface (595 files, current state).

## 5. Repository layout

This repository is a single-tree layout: the `ConstructiveWorld_vo/` artifact tree was removed in the 2026-10-07 baseline cut (#C-S00), and the gate3 cross-tree diff was removed with it.

| Path | Contents |
|---|---|
| `ConstructiveWorld_Live/` | Source tree: all `.v` sources (595 in the tree / 595 unique registered, measured 2026-11-22) + `order.txt` (604 rows, no blank lines) + `_CoqProject` (605 lines, `-Q . ""`) |
| `order.txt` | Registration order, the authoritative reference surface (604 rows; 9 files carry two rows each, 595 unique files). `scripts/` keeps a maintenance-use historical copy (671 lines, frozen 2026-10-07; its highest batch number `#R172` appears at line 665, and the last line is `#R171`); the freeze predates that evening's single-tree consolidation and the subsequent rebuild of the current registration surface; its line count and batch sequence cannot be compared directly with the current registration surface (`#R0`–`#R232`) and are kept for historical reference only |
| `scripts/` | Registration-order maintenance scripts and the `scripts/gates/` sentinels (poison-token guard, axiom parsing, comment sentinel, statement census, vo-dependency quarantine, extraction execution) |
| `.github/workflows/coq.yml` | CI full-tree driver (compilation + `coqchk` + sentinels · Rocq 9.3.0 generation pin); the same directory also holds `rocqwash-triage.yml`, a run-result observer with no certification role |
| `docs/` | Design and planning documents |
| `releases/` | Historical single-file merged edition `CW_ConstructiveWorld_220.v` (the 220 edition, see appendix), plus later additions: `CW220_Extensions.v`, the `_mc2_*` probe/close-out directories and scripts, an `extraction/` directory, extracted `.ml`/`.mli` pairs (`upcs`, `uphlogz`), and backup/script files (`CW_ConstructiveWorld_220.v.bak`, `_merge220_compile.ps1`) |

## 6. License, citation, and authors

- **License**: Apache-2.0. Extraction products (`.ml`/`.mli`) share the license of the sources.
- **Reference anchors**: when citing a library statement, locate it by "file name + `order.txt` line number + batch fingerprint". Batch fingerprints are fixed per registration batch and can be used to verify the version cited. 9 files carry two registration rows each; cite by line number to disambiguate them.
- **Sister-repository certification publication surface**: tag / Release / Zenodo see [ConstructiveWorld-Main](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main) README §2/§7 (that is the Main repository's certification surface, independent of this repository's CI status described here).
- **Authors**: see the "Authors and contributors" table at the top.

## 7. Public scope and exceptions

All files on the reference surface are published in full. Current state (measured 2026-11-22): the tree's `.v` files (595) and the unique registered files (595) have zero set difference, and there are no unregistered source files; the registration order carries 604 rows rather than 595 because 9 files are registered twice: each of the 9 keeps its original row and also holds a second row in a contiguous `#R97` block (fingerprints `b51a004`–`b51a012`, order.txt lines 563–571). The 9 doubly registered files are `Arch_GibbsA_01.v`, `Arch_UpAbl_01.v`, `EntropyMonoSplitInst.v`, `UpAblD1S2_reqlog_UpReqCauchy.v`, `UpAblDeltaStarSuboptimal.v`, `UpAblEps66Sum.v`, `UpAblT13_UpEntropyGainReq.v`, `abl_redischarge_sumd_inst.v`, `uabda_g13_evict_discharge.v`; their first registrations sit in the #R76/#R78/#R97 batches (e.g. `UpAblEps66Sum.v` at line 310, `#R78-5c9609c9`, and line 568, `#R97-b51a009`). Earlier out-of-registration supply files were batch-registered on 2026-11-08 (commit `95e7631`, whose message self-describes 31 registrations and 5 deduplicated rows; `git show` measures a numstat of +62/−6 lines, of which +32 are registered rows and +30 batch-separator blank lines, landing in the existing #R0/#R97 batches without opening new batch numbers), and the seven files that were in the tree but outside the registration order at the `10a2402b` landing (`PA_TempSoftmaxInstantiation.v`, `UpAblP6_GibbsFamilyExt.v`, `abl_div_chisq_twopoint.v`, `abl_z2_decay.v`, `u5c_pr_mertens_nat.v`, `u5c_zeta2_a1_sign11.v`, `u5c_zeta2_gapB.v`) were all restored to the registration order on 2026-11-11 by commit `2f1ffbaf` (re-anchored in the #R97 batch; its message self-describes restoring the 7 pool rows disclosed in `9a51c74`, 530 → 537 registered rows; as of the 2026-11-22 measurement each of the seven carries exactly one row). Should unregistered files appear later, their disposition will be registered here along with the adjudication of the repository's public-forward batches; the current registration order (604 rows, 595 unique files) is the sole authoritative reference surface, and unregistered files imply no referencing commitment of the library.

## Appendix: notes on the 220 edition (2026-09-07/08)

The following is the repository's early (220-edition) README content, describing the modular layout of that time; it has since been superseded by the registration-order system above and is preserved verbatim for reference. One measurement note, added 2026-11-22 outside the frozen text: the frozen text below says the merged edition is "129K lines", while the tracked file `releases/CW_ConstructiveWorld_220.v` measures 137,704 lines.

---

# ConstructiveWorld220 — the ConstructiveWorld 220 modular code base

The 220 edition = the 219 base (trust cache) + 28 standalone modules (deliverables of the 2026-09-07/08 workflow).

## Design goals (user planning)
Subsequent development calls the **compiled artifacts** of the local library and its cloud mirror directly, for fast compilation and fast problem isolation:
- one .v + one .vo per module — **whatever breaks, that piece locks** (the artifact name = the problem location)
- the base `CW_ConstructiveWorld_219.vo` rides the trust cache and is never recompiled (6MB-scale compilation blocks in some contexts)
- `docs/BLOCKERS-220.md` records all blocking points of the single-file 220 edition and their module-level mapping

## Directory
| Path | Contents |
|---|---|
| `ConstructiveWorld_Live/` | Live source tree: base .v + 28 module .v files + _CoqProject + build.sh |
| `ConstructiveWorld_vo/` | Artifact tree: the same, plus each module's .vo (the base .vo = trust-cache direct copy) |
| `releases/` | Single-file full merged edition CW_ConstructiveWorld_220.v (129K lines) |
| `docs/` | Merge guide, screening reports, blocking map |

## Compilation
```bash
cd ConstructiveWorld_vo
bash build.sh        # topological-order incremental compilation (skips existing .vo)
```
Full base recompilation (optional; best in an interactive terminal): `coqc -Q . "" CW_ConstructiveWorld_219.v`

## Module list (28, dependency topological order)
Layer 0: UpCS UpHlogZ UpDebtSqrtAbs UpDebtDual UpEntropyGain UpSigMigrate UpMinP UpAlignId UpProj UpFirewall UpTempWindow UpKVEv UpAuditBridge UpPredRelax UpPLA UpStepKLM3 UpRecast UpCLQuery UpSLM
Layer 1: UpBudgetReal↑UpHlogZ · UpArchAttn↑BudgetReal · UpConstitution↑BudgetReal · UpProjBPC↑Proj · UpEvictId · UpDebtGibbsT · UpDPOLip
Layer 2: UpDissip↑Constitution · UpStopTime↑BudgetReal+Constitution

Absorbed into the base (do not recompile): UpStepKL UpLogMono AttnDoeblin AttnHardLimit218 AttnSqrt UpFEP UpPPO UpGRPO(→UpGRPO219) UpExtras(→UpExtras219)
