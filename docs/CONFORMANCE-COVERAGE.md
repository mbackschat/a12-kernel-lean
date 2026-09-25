# Kernel conformance coverage

<!-- GENERATED FILE — do not edit by hand. Regenerate with `./scripts/report-conformance-coverage.sh`. -->

**This report is derived, never authoritative.** It reads the Kernel's error catalogs and runtime formal-code constants under `../a12-kernel/`, this repository's owned documents, Lean source, and evidence JSON. Capability status stays in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), sequencing in [`PLAN.md`](PLAN.md), and provenance in [`SOURCES.md`](SOURCES.md). When this file and an owner disagree, the owner is right and this file is stale.

The identifier counts come from maximal-identifier extraction intersected with the Kernel vocabulary. `./scripts/report-conformance-coverage.sh --verify` re-derives them by multi-pattern fixed-string whole-word matching and aborts on disagreement. Run it after changing a counting mechanism; it also checks capability record boundaries and gap-shard ownership.

Working-tree counts generated on 2026-09-25; HEAD was `893a2861`. The vocabulary scans include untracked files under their named roots; the estate inventory uses tracked paths. This is not a measurement of the exact committed revision's bytes.

## Headline

**Whole-Kernel conformance is not quantified here. 459 of 495 diagnostic identifiers occur in Lean source (92%); 36 do not.**

An occurrence can be a definition, fixture, comment, request, or list of exclusions. It establishes neither implemented behaviour nor a matching Kernel observation. The vocabulary denominator also says nothing about successful evaluation, scheduling, addressing, or combinations of features. Use capability scopes, their retained evidence, and open obligations to assess semantic progress; they do not currently supply a complete behavioural denominator either.

## Terminology

| Term | Meaning in this report |
|---|---|
| Diagnostic identifier / class | A name from the selected Kernel diagnostic catalogs or runtime formal-code constants. Counting its occurrence measures vocabulary coverage. |
| Touched / untouched | A diagnostic name occurs somewhere in the scanned prose, Lean source, or evidence JSON / occurs in none of them. |
| Lean names | Diagnostic names found in Lean source, including comments and fixtures; not a count of implemented or proved behaviours. |
| Capability record (`cap`) | An entry in [the implementation map](IMPLEMENTATION-MAP.md) describing one supported semantic scope, its assurance, and its limits. It need not cover an entire operator or family. |
| Checkpoint | A source or measurement record documenting provenance, findings, and their scope; follow its links to inspect the supporting observations. |
| Checkpoint-citing capabilities (formerly `checkpoint caps`) | Capability records whose text mentions a checkpoint or calibration. This is a record count, not a count of fully calibrated capabilities. |
| Calibration / evidence pending | Calibration compares the executable account with retained Kernel observations for specified cases. An evidence-pending note identifies correspondence still to establish; a capability can have both calibrated and pending parts. |
| Open gap / remaining-work row | A gap is an unresolved semantic topic in [the gap index](SEMANTICS-GAPS.md). A remaining-work row is one entry within a topic; entries vary in size and may overlap. |
| Blocked route | The recorded way to obtain a needed observation cannot currently proceed. This blocks dependent work, not every open gap. |
| Ledger pending / handed-off | Nonterminal cross-project reconciliation states in [the synchronization ledger](A12-DMKITS-SPEC-SYNC-LEDGER.md). Neither state means the claim is accepted or closed. |
| Theory / support / evidence estate | Groups of tracked Lean source counted by nonblank lines: executable semantics, proofs and cases / supporting process and tooling / the evidence subset of support. |
| Capture directory / `inputHash` marker | A directory retaining probe artifacts / an input-identity field in the selected compact observation files. Neither count measures independent semantic cases. |
| Velocity | Changes in the historical table's selected counts. Unchanged counts can accompany semantic progress; the table is not a measure of completed behaviour per hour. |

## Axis 1 — diagnostic vocabulary, with a finite denominator

| | classes | share |
|---|---|---|
| Distinct identifiers in the selected diagnostic catalogs and runtime formal-code constants | 495 | 100% |
| Named in `spec/` or `docs/` prose | 304 | 61% |
| Named in Lean source under `A12Kernel/` | 459 | 92% |
| Named in JSON under `evidence/` | 214 | 43% |
| Touched by any of the three | 489 | 98% |
| **Untouched everywhere** | **6** | **1%** |

Two occurrence checks that may warrant an ownership lookup:

- **Named in evidence JSON but absent from prose: 0.** Inspect the occurrence before treating it as an unaccounted observation.
- **Named in archived prose but absent from live prose: 1.** Check existing ownership before proposing any new work; the name alone establishes no missing semantic fact.

### Where the untouched classes are

Ordered by count for lookup. Semantic priority remains with the plan and live gaps.

| untouched | catalog | route |
|---|---|---|
| 2 | `vk_parser_error_messages` | condition/DSL static legality — the fast `dmtool rule check` batch route |
| 2 | `_30_8` | runtime formal-error **texts** — a **document** probe (`:adapter:kernelProbe` → `validateFull`); finer than the code below, since art and sign pick the text |
| 1 | `vk_parser_common_error_messages` | shared parser diagnostics — the fast `rule check` batch route |
| 1 | `test_rule_error_messages` | on-the-fly rule testing — likely instrument-only, not a semantic class |

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour are not measured by diagnostic vocabulary. This text query counts capability records mentioning a checkpoint or calibration, not how much of each family is calibrated. The checkpoint and evidence-pending sets can overlap.

| | records | share |
|---|---|---|
| Capability records in [`implementation/`](implementation/) | 211 | 100% |
| Citing a Kernel checkpoint or calibration | 120 | 56% |
| Carrying an explicit evidence-pending note | 54 | 25% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [`gaps/`](gaps/), indexed by [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | 23 |
| `remaining` rows across those gaps | 248 |
| Gaps whose route is **blocked** | 0 |
| Ledger entries `pending` with a12-dmkits | 4 |
| Ledger entries `handed-off` | 0 |

A blocked route stops the work that depends on it. Other ready obligations can continue. Remaining-work entries differ in size and may overlap; their count is not a completion percentage.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[`CLAUDE.md`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (`Semantics/`, `Elaboration/`, `Proofs/`, `Conformance/`, core types) | 217100 | 100% |
| Support (`Evidence/`, `Reference/`, `Process/`, `Trust/`, drivers) | 8746 | 4% — ceiling 100% |
| Evidence alone | 1517 | 0% — ceiling 33% |

Tracked Lean files in neither estate: 0. A nonzero value means the ratio above measures a subset and the inventory needs review.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under `../evidence/` | 215 |
| `inputHash` markers in `*-obs.json` and `semantic-observations.json` | 584 |

The marker count excludes other observation formats, including runtime `artifact.json` files with `rows` arrays. It is neither a total observation count nor a count of independent behavioural discriminators.

## Velocity

One row is appended when one of the recorded counts changes. Flat vocabulary counts do not indicate stalled semantic work: runtime calibration, proofs, and admitted behaviour can advance without introducing a diagnostic name. Historical rows preserve the counts produced by their then-current queries.

Datetime is HEAD's commit time in ISO 8601 format, including its UTC offset; it is not the report's execution time. The revision is context for working-tree counts, not a claim that every counted byte was committed there.

<!-- velocity-history:start -->
| datetime | revision | touched | Lean names | untouched | checkpoint-citing capabilities | open gaps |
|---|---|---|---|---|---|---|
| 2026-09-07T19:17:22+02:00 | `3db574b1` | 149 | 78 | 292 | 82 | 23 |
| 2026-09-07T20:07:55+02:00 | `0fe98007` | 160 | 78 | 281 | 82 | 23 |
| 2026-09-07T20:15:59+02:00 | `d9079138` | 170 | 78 | 271 | 82 | 23 |
| 2026-09-07T20:24:59+02:00 | `199106fc` | 194 | 92 | 301 | 82 | 23 |
| 2026-09-07T20:36:42+02:00 | `a80be08d` | 202 | 106 | 293 | 83 | 24 |
| 2026-09-07T21:25:22+02:00 | `6eb95a7e` | 300 | 204 | 195 | 83 | 24 |
| 2026-09-07T22:16:10+02:00 | `53d6d3ec` | 313 | 217 | 182 | 83 | 24 |
| 2026-09-07T22:30:39+02:00 | `eb587109` | 314 | 218 | 181 | 83 | 24 |
| 2026-09-07T22:38:00+02:00 | `2716b7cc` | 317 | 220 | 178 | 83 | 24 |
| 2026-09-07T22:43:16+02:00 | `4b6d739f` | 318 | 221 | 177 | 83 | 25 |
| 2026-09-07T22:49:28+02:00 | `77623942` | 336 | 239 | 159 | 84 | 25 |
| 2026-09-07T23:38:57+02:00 | `84dcb0cc` | 371 | 275 | 124 | 85 | 25 |
| 2026-09-08T00:19:13+02:00 | `fcf31f1c` | 375 | 279 | 120 | 86 | 25 |
| 2026-09-08T01:31:14+02:00 | `534c3160` | 387 | 291 | 108 | 87 | 25 |
| 2026-09-08T01:43:17+02:00 | `eaaca020` | 396 | 297 | 99 | 88 | 25 |
| 2026-09-08T01:55:45+02:00 | `74167065` | 403 | 303 | 92 | 89 | 25 |
| 2026-09-08T02:11:12+02:00 | `8b11aa8d` | 415 | 315 | 80 | 90 | 25 |
| 2026-09-08T02:22:27+02:00 | `7e500486` | 420 | 320 | 75 | 91 | 25 |
| 2026-09-08T02:28:53+02:00 | `57293e37` | 429 | 330 | 66 | 92 | 25 |
| 2026-09-08T03:04:37+02:00 | `185d1037` | 431 | 333 | 64 | 93 | 25 |
| 2026-09-08T04:46:36+02:00 | `ab442e98` | 448 | 350 | 47 | 93 | 25 |
| 2026-09-08T04:57:38+02:00 | `ee3e6900` | 452 | 354 | 43 | 94 | 25 |
| 2026-09-08T05:09:40+02:00 | `84fc1dde` | 459 | 361 | 36 | 95 | 25 |
| 2026-09-08T05:15:21+02:00 | `76c62b38` | 467 | 371 | 28 | 96 | 25 |
| 2026-09-08T06:42:57+02:00 | `7f962e56` | 473 | 377 | 22 | 97 | 25 |
| 2026-09-08T07:33:34+02:00 | `43bc7d7a` | 475 | 379 | 20 | 98 | 25 |
| 2026-09-08T07:43:32+02:00 | `29630b55` | 477 | 381 | 18 | 99 | 25 |
| 2026-09-08T07:53:12+02:00 | `8aceedea` | 479 | 383 | 16 | 100 | 25 |
| 2026-09-08T08:04:46+02:00 | `a75240e1` | 482 | 389 | 13 | 101 | 25 |
| 2026-09-08T08:15:13+02:00 | `95b73fdb` | 483 | 392 | 12 | 102 | 25 |
| 2026-09-08T14:31:07+02:00 | `ce0c830f` | 483 | 398 | 12 | 102 | 25 |
| 2026-09-08T14:50:57+02:00 | `fad2419a` | 483 | 405 | 12 | 102 | 25 |
| 2026-09-08T15:00:11+02:00 | `8305375a` | 483 | 410 | 12 | 103 | 25 |
| 2026-09-08T15:10:47+02:00 | `1401d381` | 483 | 415 | 12 | 103 | 25 |
| 2026-09-08T15:18:40+02:00 | `c1bb20aa` | 483 | 419 | 12 | 104 | 25 |
| 2026-09-08T15:40:20+02:00 | `8b1fd94f` | 483 | 426 | 12 | 105 | 25 |
| 2026-09-08T16:11:19+02:00 | `0e22c25a` | 489 | 432 | 6 | 105 | 25 |
| 2026-09-08T16:31:46+02:00 | `c401b5b3` | 489 | 436 | 6 | 105 | 25 |
| 2026-09-08T16:57:26+02:00 | `7da15820` | 489 | 440 | 6 | 105 | 25 |
| 2026-09-08T17:26:37+02:00 | `65e2aaad` | 489 | 444 | 6 | 106 | 25 |
| 2026-09-08T17:34:57+02:00 | `8badcc6a` | 489 | 445 | 6 | 107 | 25 |
| 2026-09-08T17:45:00+02:00 | `9aad52da` | 489 | 447 | 6 | 108 | 25 |
| 2026-09-08T18:07:46+02:00 | `452fd9fb` | 489 | 448 | 6 | 108 | 25 |
| 2026-09-08T18:21:40+02:00 | `ff74d2b8` | 489 | 449 | 6 | 108 | 25 |
| 2026-09-08T18:50:16+02:00 | `176c36ba` | 489 | 450 | 6 | 108 | 25 |
| 2026-09-08T19:44:27+02:00 | `3a457eea` | 489 | 454 | 6 | 108 | 25 |
| 2026-09-08T20:40:25+02:00 | `1a163c9e` | 489 | 455 | 6 | 108 | 25 |
| 2026-09-08T21:01:33+02:00 | `29a705e7` | 489 | 455 | 6 | 107 | 25 |
| 2026-09-08T21:18:34+02:00 | `367e2e71` | 489 | 455 | 6 | 111 | 25 |
| 2026-09-08T23:50:33+02:00 | `e652d91e` | 489 | 455 | 6 | 112 | 24 |
| 2026-09-09T00:03:35+02:00 | `caca1731` | 489 | 455 | 6 | 112 | 23 |
| 2026-09-09T00:32:32+02:00 | `27c48616` | 489 | 455 | 6 | 113 | 23 |
| 2026-09-09T02:01:07+02:00 | `023fbc63` | 489 | 455 | 6 | 114 | 23 |
| 2026-09-09T02:10:04+02:00 | `aa23c313` | 489 | 455 | 6 | 115 | 23 |
| 2026-09-09T02:36:22+02:00 | `32729671` | 489 | 455 | 6 | 116 | 23 |
| 2026-09-21T22:55:36+02:00 | `e19f3a98` | 489 | 455 | 6 | 117 | 23 |
| 2026-09-22T00:41:01+02:00 | `c7573039` | 489 | 455 | 6 | 118 | 23 |
| 2026-09-23T22:35:42+02:00 | `2c2f4c36` | 489 | 455 | 6 | 117 | 23 |
| 2026-09-23T23:20:43+02:00 | `a4a91200` | 489 | 456 | 6 | 117 | 23 |
| 2026-09-23T23:55:50+02:00 | `0b62e75f` | 489 | 456 | 6 | 118 | 23 |
| 2026-09-24T12:30:49+02:00 | `01b2247b` | 489 | 456 | 6 | 120 | 23 |
| 2026-09-24T15:47:41+02:00 | `c113d38a` | 489 | 457 | 6 | 120 | 23 |
| 2026-09-25T01:09:04+02:00 | `74b7f72c` | 489 | 459 | 6 | 120 | 23 |
<!-- velocity-history:end -->
