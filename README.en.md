# ConstructiveWorld — Constructive Mathematics Library (Rocq/Coq)

[![Coq CI](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/workflows/coq.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

This repository is the constructive mathematics library accompanying the paper "Constructive three representations of π": the whole library states its existential conclusions with explicit `sigT` witnesses at the `Set` layer, introduces no axioms, and is extractable end to end. Chinese version: [README.md](README.md).

## Authors

| Author | ORCID |
|---|---|
| Baojun Wang | [0009-0001-4240-9045](https://orcid.org/0009-0001-4240-9045) |
| Guangzhao Zu | [0009-0006-7811-6638](https://orcid.org/0009-0006-7811-6638) |
| Wanlan Xia | [0009-0008-7359-044X](https://orcid.org/0009-0008-7359-044X) |
| Baiyuan Zeng | [0009-0005-9811-5598](https://orcid.org/0009-0005-9811-5598) |
| Zhinong Zhou | [0009-0001-3206-5824](https://orcid.org/0009-0001-3206-5824) |
| Xuefeng Gao | [0009-0007-9904-1599](https://orcid.org/0009-0007-9904-1599) |

## 1. Library overview

- **Scale**: 89 registered modules (registration order `order.txt`, 89 lines, registration batches `#R0`–`#R17`). The registration order is the library's authoritative reference surface: one line per registered file, of the form `S01_BaseRing.v#R0-d66910`, where the part after `#` is the registration batch fingerprint; the two trees and the registration order have zero set difference.
- **Content surface**: the S01–S15 constructive reals and analysis base; the upper-bound requirements family for Banach norms and Padé approximation (`UpReqBanach*` / `UpReqPade*`); the Boltzmann/Gibbs, GRPO/DPO alignment and entropy surface (S05/S06/S08/S09); attention-chain bounds (`Attn*`); and the companion machinery surface (`b1_*`, `mach_fold_q`, `abl_z2/z3_pointwise`, `abl_Hqarch_*`, `fib_machine`).
- **Purely constructive**: the library uses no `Axiom`, no `Admitted`, and no classical logic; the kernel-level `coqchk -o` recheck convention is `Axioms: <none>`.
- **Explicit `sigT` witnesses at the `Set` layer**: existential conclusions always come with computable witnesses (rational endpoints, approximate roots, etc.), never remaining at the propositional layer.
- **Extractable**: target-language code is generated via `Separate Extraction`, with the `Obj.magic` count mechanically checked to be zero (a nonzero count would mean Prop-layer content leaking into the extraction surface).
- **The "rate-is-algorithm" paradigm**: the executable artifact (a `Defined` computation) and its correctness certificate (a `Qed` proof) coexist in one body — theorems and programs are two faces of the same thing.

**Division of labor among sister repositories**: the full 893-file library lives in [ConstructiveWorld-Main](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main) (with the π ladder, the five-constants family, and the ZZ measure route); this repository is the condensed `Set`-layer registration surface.

**The π pillar as an independent package**: the constructive strong irrationality of π is published as the independent Rocq package [rocq-pi-leibniz](https://github.com/hy7pc8gfmf-dotcom/rocq-pi-leibniz) (Leibniz window method · `Set`-layer carriers · zero axioms · extractable witnesses), currently at `v1.0.4` (tag dereferences to commit `e1891fce`, green CI run 27), archived on Zenodo under DOI [10.5281/zenodo.23656983](https://doi.org/10.5281/zenodo.23656983) (the integration line, concept 23656982); the v1.0.0 batch is merged into the Rocq opam repository (rocq-prover/opam #3884), and the consolidated PR [#3899](https://github.com/rocq-prover/opam/pull/3899) for v1.0.1–1.0.4 is under review (supersedes #3896/#3897/#3898). Earlier, its generic escape-window criterion engine was submitted upstream to the Rocq standard library (Issue #312 / PR #313); following the maintainers' feedback, that route was turned into the independent-library publication path (the package above).

## 2. Version and certification record

| Item | Value |
|---|---|
| Library version | `ec228da` (`main` branch, measured 2026-10-29) |
| CI certification | most recent green run [#55](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Set/actions/runs) (head `5293f1b`, 2026-10-29); the run #56 for the current head `ec228da` is in flight — its certification conclusion governs once it lands, and no green is claimed in advance |
| Axiom audit | whole-library `coqchk -o` recheck, `Axioms: <none>` |
| Registration order | `order.txt`, 89 lines (`#R0`–`#R17`) |
| License | Apache-2.0 (see `LICENSE`) |

On every push, continuous integration (`.github/workflows/coq.yml`) runs: gate1 poison-token guard → gate4 comment sentinel → gate3 cross-tree diff → full-tree compilation → gate5 vo-binary quarantine → whole-tree `coqchk` kernel recheck → gate2 axiom sentinel (parsing the `coqchk` log for `Axioms: <none>`). The sentinel scripts live in `scripts/gates/`.

## 3. Environment prerequisites

- **Rocq / Coq 9.1.0** (`rocq` and `coqchk` were verified on this version). Older versions are unverified; after changing the verification environment, rerun the four steps below.
- No external OCaml dependencies; extraction products are plain OCaml sources kept as audit objects, and no executable OCaml environment is required.

## 4. Reproduction: four-step verification

Verbatim identical to §6 "four-step command forms" of the paper. Run the commands inside `ConstructiveWorld_vo/` (or `ConstructiveWorld_Live/`); both trees use the `-Q . ""` flat namespace. The full-tree driver is `.github/workflows/coq.yml`.

```sh
# ① Full compilation: file by file in order.txt registration order (direct local invocation; full-tree driver in the CI workflow)
rocq compile -Q . "" S01_BaseRing.v
# ② Axiom audit: **the audit statements are `Print Assumptions <statement>.` commands written verbatim inside the source files** (e.g. two in S14_B5BatchBlock.v, for `b5d1_Heps4` and `b5dE_zero_le_one`), re-verified automatically at compile time; expected output: Closed under the global context
# ③ Extraction audit: the Obj.magic count in the .ml files produced by Separate Extraction should be zero
coqtop -q -Q . "" <file>.v            # run Separate Extraction <statement>.
grep -c Obj.magic <file>.ml           # expected 0
# ④ Kernel recheck: take the logical library name from the head of <file>.glob (the actual prefix under -Q . ""); do not substitute the file name
coqchk -silent -Q . "" <logical-library>.<file>
```

Notes:

- The logical library name is **not** the file name. For example, the logical name of `S01_BaseRing.v` is `FS01_BaseRing` (line 2 of `S01_BaseRing.glob`). In step ④, using the file name instead makes `coqchk` report a missing library.
- In step ①, executing files one by one in `order.txt` line order satisfies the dependency order; resolve any single-file failure before continuing.
- The four steps cover all 89 registered files of the registration surface.

## 5. Repository layout

| Path | Contents |
|---|---|
| `ConstructiveWorld_Live/` | Source tree: all `.v` sources + `order.txt` (89 lines) + `_CoqProject` (`-Q . ""`) |
| `ConstructiveWorld_vo/` | Artifact tree: isomorphic to the source tree, plus `.vo`/`.glob`/`.vos`/`.vok` build products |
| `order.txt` | Registration order (one copy in each tree and in `scripts/`, identical content), the authoritative reference surface |
| `scripts/` | Registration-order maintenance scripts and the `scripts/gates/` sentinels (poison-token guard, axiom parsing, cross-tree diff, comment sentinel, vo-dependency quarantine) |
| `.github/workflows/coq.yml` | CI full-tree driver (compilation + `coqchk` + sentinels) |
| `docs/` | Design and planning documents |
| `releases/` | Historical single-file merged edition (the 220 edition, see appendix) |

## 6. License, citation, and authors

- **License**: Apache-2.0. Extraction products (`.ml`/`.mli`) share the license of the sources.
- **Reference anchors**: when citing a library statement, locate it by "file name + `order.txt` line number + batch fingerprint". Batch fingerprints are fixed per registration batch and can be used to verify the version cited.
- **Authors**: see the "Authors" table at the top.

## 7. Public scope and exceptions

All files on the reference surface are published in full. As of the 2026-10-29 measurement, the tree's `.v` files and the registration order have zero set difference and there are no unregistered source files. Should unregistered files appear later, their disposition will be registered here along with the adjudication of the upcoming public forward batches; the current registration order (89 lines) is the sole authoritative reference surface, and unregistered files imply no referencing commitment of the library.

## Appendix: notes on the 220 edition (2026-09-07/08)

The following is the repository's early (220-edition) README content, describing the modular layout of that time; it has since been superseded by the registration-order system above and is preserved verbatim for reference.

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
