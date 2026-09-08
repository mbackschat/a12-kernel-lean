# Kernel conformance coverage

<!-- GENERATED FILE — do not edit by hand. Regenerate with `./scripts/report-conformance-coverage.sh`. -->

**This report is derived, never authoritative.** Every number is recomputed from the Kernel's own error
catalogs under `../a12-kernel/`, this repository's owned documents, and its tracked Lean source. It owns
no fact: capability status stays in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open obligations in
[`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), sequencing in [`PLAN.md`](PLAN.md), provenance in
[`SOURCES.md`](SOURCES.md). When this file and an owner disagree, the owner is right and this file is stale.

The class counts come from one mechanism — maximal-identifier extraction intersected with the Kernel's
class set — and `./scripts/report-conformance-coverage.sh --verify` re-derives them by a structurally
different one, multi-pattern fixed-string whole-word matching, aborting on any disagreement. The audit is
not on the default path because it costs about forty seconds against this one's four. Run it after any
change to how coverage is counted; it also checks capability record boundaries and gap-shard ownership.

Measured at `367e2e71` on 2026-09-08.

## Headline

**455 of 495 Kernel refusal classes modelled in Lean (91%). 40 are not.**

That is the project's progress figure and the only one worth quoting. A secondary count, *touched*, stands
at 489 (98%): it counts a class named anywhere in the written
account, **including a checkpoint's own list of what it deliberately did not reach**. Touched is an upper
bound on what this repository knows about, and it can be raised to 100% in an afternoon by writing prose,
so it is reported to expose that gap rather than to stand in for progress. When the two are quoted
together the modelled figure leads.

## Axis 1 — static legality, the one axis with a real denominator

| | classes | share |
|---|---|---|
| Distinct refusal classes in the Kernel's `error_messages_en.properties` catalogs | 495 | 100% |
| Named in `spec/` or `docs/` prose | 300 | 60% |
| Named in tracked Lean source | 455 | 91% |
| Observed in a retained probe artifact | 204 | 41% |
| Touched by any of the three | 489 | 98% |
| **Untouched everywhere** | **6** | **1%** |

Two hygiene readings, both of which should stay at zero or be acted on:

- **Observed but absent from the written account: 0.** A class seen in a probe and never
  written down is a measurement whose result was lost.
- **Known only from archived material: 2.** These are facts this repository holds but no
  longer reads; they belong in a live owner or should be re-measured.

### Where the untouched classes are

Ordered by size, because that is the order in which they are worth attacking.

| untouched | catalog | route |
|---|---|---|
| 2 | `vk_parser_error_messages` | condition/DSL static legality — the fast `dmtool rule check` batch route |
| 2 | `_30_8` | runtime formal-error **texts** — a **document** probe (`:adapter:kernelProbe` → `validateFull`); finer than the code below, since art and sign pick the text |
| 1 | `vk_parser_common_error_messages` | shared parser diagnostics — the fast `rule check` batch route |
| 1 | `test_rule_error_messages` | on-the-fly rule testing — likely instrument-only, not a semantic class |

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour produce no
refusal class, so Axis 1 is blind to them. The capability records are the available proxy, and a coarser
one: it counts whether a record cites external calibration, not how much of its family is covered.

| | records | share |
|---|---|---|
| Capability records in [`implementation/`](implementation/) | 207 | 100% |
| Citing a Kernel checkpoint or calibration | 111 | 53% |
| Carrying an explicit evidence-pending note | 52 | 25% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [`gaps/`](gaps/), indexed by [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | 25 |
| `remaining` rows across those gaps | 235 |
| Gaps whose route is **blocked** | 1 |
| Ledger entries `pending` with a12-dmkits | 5 |
| Ledger entries `handed-off` | 0 |

A blocked route is the only figure here that should stop work; a `remaining` row is ordinary scope. If
blocked is nonzero, that is what to escalate.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[`CLAUDE.md`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and
evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (`Semantics/`, `Elaboration/`, `Proofs/`, `Conformance/`, core types) | 208111 | 100% |
| Support (`Evidence/`, `Reference/`, `Process/`, `Trust/`, drivers) | 8691 | 4% — ceiling 100% |
| Evidence alone | 1517 | 0% — ceiling 33% |

Tracked Lean files in neither estate: 0. A nonzero value means the ratio above is measuring
a subset, so it is a defect in this generator rather than in the estate.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under `../evidence/` | 192 |
| Retained observation rows across all artifacts | 476 |

## Velocity

One row is appended per run, and only when a headline number moved — so a flat `touched` column across several rows is the signal that progression has stalled. The actionable reading when it does is Axis 1's route column: a stall usually means the remaining blocks need a route this session has not set up, rather than more rows on the route it already has.

Datetime is the referenced revision's commit time in ISO 8601 format, including its UTC offset; it is not the report's execution time.

<!-- velocity-history:start -->
| datetime | revision | touched | modelled | untouched | calibrated caps | open gaps |
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
<!-- velocity-history:end -->
