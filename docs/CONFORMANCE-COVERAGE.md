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
change to how coverage is counted; it has already caught two real defects, recorded in the script.

Measured at `ab442e98` on 2026-09-08.

## Headline

**350 of 495 Kernel refusal classes modelled in Lean (70%). 145 are not.**

That is the project's progress figure and the only one worth quoting. A secondary count, *touched*, stands
at 448 (90%): it counts a class named anywhere in the written
account, **including a checkpoint's own list of what it deliberately did not reach**. Touched is an upper
bound on what this repository knows about, and it can be raised to 100% in an afternoon by writing prose,
so it is reported to expose that gap rather than to stand in for progress. When the two are quoted
together the modelled figure leads.

## Axis 1 — static legality, the one axis with a real denominator

| | classes | share |
|---|---|---|
| Distinct refusal classes in the Kernel's `error_messages_en.properties` catalogs | 495 | 100% |
| Named in `spec/` or `docs/` prose | 282 | 56% |
| Named in tracked Lean source | 350 | 70% |
| Observed in a retained probe artifact | 184 | 37% |
| Touched by any of the three | 448 | 90% |
| **Untouched everywhere** | **47** | **9%** |

Two hygiene readings, both of which should stay at zero or be acted on:

- **Observed but absent from the written account: 0.** A class seen in a probe and never
  written down is a measurement whose result was lost.
- **Known only from archived material: 4.** These are facts this repository holds but no
  longer reads; they belong in a live owner or should be re-measured.

### Where the untouched classes are

Ordered by size, because that is the order in which they are worth attacking.

| untouched | catalog | route |
|---|---|---|
| 19 | `vk_parser_error_messages` | condition/DSL static legality — the fast `dmtool rule check` batch route |
| 8 | `vk_codegen_no_meta_model_ckecks_error_messages` | codegen-time model checks — reachable through `model check` |
| 7 | `runtime_formal_codes` | runtime formal-error **codes** a `validateFull` consumer actually reads — same document probe |
| 6 | `kernel_core_errortext_error_messages` | shared error-text base utilities — carrier not yet identified |
| 3 | `vk_service_errortext_error_messages` | message templates and parameters — the fast `rule check --message` batch route |
| 2 | `_30_8` | runtime formal-error **texts** — a **document** probe (`:adapter:kernelProbe` → `validateFull`); finer than the code below, since art and sign pick the text |
| 1 | `vk_parser_common_error_messages` | shared parser diagnostics — the fast `rule check` batch route |
| 1 | `test_rule_error_messages` | on-the-fly rule testing — likely instrument-only, not a semantic class |

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour produce no
refusal class, so Axis 1 is blind to them. The capability records are the available proxy, and a coarser
one: it counts whether a record cites external calibration, not how much of its family is covered.

| | records | share |
|---|---|---|
| Capability records in [`implementation/`](implementation/) | 188 | 100% |
| Citing a Kernel checkpoint or calibration | 93 | 49% |
| Carrying an explicit evidence-pending note | 47 | 25% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | 25 |
| `remaining` rows across those gaps | 0 |
| Gaps whose route is **blocked** | 0 |
| Ledger entries `pending` with a12-dmkits | 1 |
| Ledger entries `handed-off` | 0 |

A blocked route is the only figure here that should stop work; a `remaining` row is ordinary scope. If
blocked is nonzero, that is what to escalate.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[`CLAUDE.md`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and
evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (`Semantics/`, `Elaboration/`, `Proofs/`, `Conformance/`, core types) | 201999 | 100% |
| Support (`Evidence/`, `Reference/`, `Process/`, `Trust/`, drivers) | 8535 | 4% — ceiling 100% |
| Evidence alone | 1517 | 0% — ceiling 33% |

Tracked Lean files in neither estate: 0. A nonzero value means the ratio above is measuring
a subset, so it is a defect in this generator rather than in the estate.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under `../evidence/` | 176 |
| Retained observation rows across all artifacts | 439 |

## Velocity

One row is appended per run, and only when a headline number moved — so a flat `touched` column across
several dated rows is the signal that progression has stalled. The actionable reading when it does is
Axis 1's route column: a stall usually means the remaining blocks need a route this session has not set
up, rather than more rows on the route it already has.

<!-- velocity-history:start -->
| date | revision | touched | modelled | untouched | calibrated caps | open gaps |
|---|---|---|---|---|---|---|
| 2026-09-07 | `3db574b1` | 149 | 78 | 292 | 82 | 23 |
| 2026-09-07 | `0fe98007` | 160 | 78 | 281 | 82 | 23 |
| 2026-09-07 | `d9079138` | 170 | 78 | 271 | 82 | 23 |
| 2026-09-07 | `199106fc` | 194 | 92 | 301 | 82 | 23 |
| 2026-09-07 | `a80be08d` | 202 | 106 | 293 | 83 | 24 |
| 2026-09-07 | `6eb95a7e` | 300 | 204 | 195 | 83 | 24 |
| 2026-09-07 | `53d6d3ec` | 313 | 217 | 182 | 83 | 24 |
| 2026-09-07 | `eb587109` | 314 | 218 | 181 | 83 | 24 |
| 2026-09-07 | `2716b7cc` | 317 | 220 | 178 | 83 | 24 |
| 2026-09-07 | `4b6d739f` | 318 | 221 | 177 | 83 | 25 |
| 2026-09-07 | `77623942` | 336 | 239 | 159 | 84 | 25 |
| 2026-09-07 | `84dcb0cc` | 371 | 275 | 124 | 85 | 25 |
| 2026-09-08 | `fcf31f1c` | 375 | 279 | 120 | 86 | 25 |
| 2026-09-08 | `534c3160` | 387 | 291 | 108 | 87 | 25 |
| 2026-09-08 | `eaaca020` | 396 | 297 | 99 | 88 | 25 |
| 2026-09-08 | `74167065` | 403 | 303 | 92 | 89 | 25 |
| 2026-09-08 | `8b11aa8d` | 415 | 315 | 80 | 90 | 25 |
| 2026-09-08 | `7e500486` | 420 | 320 | 75 | 91 | 25 |
| 2026-09-08 | `57293e37` | 429 | 330 | 66 | 92 | 25 |
| 2026-09-08 | `185d1037` | 431 | 333 | 64 | 93 | 25 |
| 2026-09-08 | `ab442e98` | 448 | 350 | 47 | 93 | 25 |
<!-- velocity-history:end -->
