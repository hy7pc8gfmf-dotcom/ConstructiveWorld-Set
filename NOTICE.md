ConstructiveWorld-Main — 构造世界模块化形式化库（662 个在册模块）
Copyright 2026 王宝军、夏挽岚（通讯作者 xiawanlan33@163.com）、祖光照、周志农、高雪峰 & Contributors

==========================================================================
SOURCE CODE LICENSE
==========================================================================

The Rocq/Coq formalization sources (.v) under ConstructiveWorld_Live/, the
compiled trust caches (.vo), the single-file release builds (releases/),
and the documentation (docs/) in this repository are licensed under the
Apache License, Version 2.0.
See LICENSE for the full license text.

==========================================================================
RUNTIME COMPONENTS — LICENSE STATUS
==========================================================================

Certain runtime components have a different copyright status. See below
for details.

==========================================================================
1. EXTRACTED EXECUTABLE CHECKERS (RLA PROTECTED) — NONE PUBLISHED YET
==========================================================================

Unlike the .vo trust caches — which are development dependencies and are
freely usable under Apache 2.0 — the RLA (Runtime License Agreement,
CLA/RLA.md) protection track of this project covers future OCaml
executable checkers and runtime components extracted from the project
modules via Coq Extraction.

No such component has been published as of this NOTICE (status verified
2026-10-06). Each component will be registered in the table below upon its
first release.

| Component | Source | Status |
|-----------|--------|--------|
| （暂无已发布组件） | Coq Extraction（模块 .v → .ml → 可执行检查器） | 首次提取发布时登记；届时按 CLA/RLA.md 对商业使用实施保护 |

The Apache 2.0 license covers the source code and the .vo trust caches
(research / learning / reference / development use); the RLA governs
commercial use (embedding in products, SaaS, production environments) of
future extracted executable runtime components.
Contact 168888@live.cn for inquiries.

Boundary statement (registered 2026-10-06): the Apache-2.0 master grant
already gives every recipient the right to extract from, use, and
commercialize the public source face, including its extraction products
(.ml/.mli), which are published in this repository as audit artifacts under
Apache-2.0. The RLA track is limited to (i) officially supported and
warranted distribution and maintenance services, and (ii) future non-public
assets and incremental technical services; it imposes no retroactive
commercial restriction on the public source face.

==========================================================================
2. UPSTREAM DUAL-TRACK SOURCES — SAME SOURCE, TWO LICENSES (REGISTERED 2026-10-06)
==========================================================================

`ConstructiveCauchyRealsSep.v` (the escape-window separation engine for
the constructive Cauchy reals, 221 lines, md5
291780525a1654fec408fedba9d35558) is a dual-track (dual-habitat) piece:

- The upstream copy has been submitted to the Rocq/Coq standard library as
  PR rocq-prover/stdlib#313 (branch `creal-escape-window-engine`, fork
  lineage ac219d6 -> 2a5eb5d; open as of 2026-10-06). Upon upstream
  acceptance, that upstream copy is governed by the standard library's own
  license (LGPL-2.1), and upstream modifications made from the merge onward
  belong to the upstream project under its contribution terms.
- Copies of the same source held or later included in this repository —
  together with sandbox/vendor copies seeded from the same md5 anchor —
  remain under Apache-2.0, with all rights and obligations unchanged.
  (As of registration, no same-named tracked file exists in this
  repository; the piece circulates via the upstream PR branch and the
  seeded vendor copies.)

Same source, two licenses — one per distribution channel. Neither
registration modifies the other's terms. See the boundary statement above
for the RLA track's scope.

==========================================================================
THIRD-PARTY DEPENDENCIES
==========================================================================

This product includes or links to the following third-party software,
each governed by its own license:

1. The Rocq/Coq Proof Assistant — LGPL 2.1 (stdlib)
   - https://rocq-prover.org/
   - Used as: the proof assistant compiling all .v sources
   - This project depends only on the Rocq/Coq standard library
     (no mathcomp, no Coquelicot).

==========================================================================
ADDITIONAL ATTRIBUTIONS
==========================================================================

Portions of this work build on:
- The Rocq/Coq proof assistant: https://rocq-prover.org/
