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

Measured at `3db574b1` on 2026-09-07.

## Headline

**149 of 441 Kernel refusal classes touched (33%); 78 modelled in Lean (17%); 292 untouched.**

The two figures differ because *touched* counts a class named anywhere in the account — including a
checkpoint's own list of what it did **not** reach — while *modelled* counts one the Lean theory names.
Read the first as an upper bound on knowledge and the second as the floor on implemented behaviour.

## Axis 1 — static legality, the one axis with a real denominator

| | classes | share |
|---|---|---|
| Distinct refusal classes in the Kernel's `error_messages_en.properties` catalogs | 441 | 100% |
| Named in `spec/` or `docs/` prose | 149 | 33% |
| Named in tracked Lean source | 78 | 17% |
| Observed in a retained probe artifact | 80 | 18% |
| Touched by any of the three | 149 | 33% |
| **Untouched everywhere** | **292** | **66%** |

Two hygiene readings, both of which should stay at zero or be acted on:

- **Observed but absent from the written account: 0.** A class seen in a probe and never
  written down is a measurement whose result was lost.
- **Known only from archived material: 5.** These are facts this repository holds but no
  longer reads; they belong in a live owner or should be re-measured.

### Where the untouched classes are

Ordered by size, because that is the order in which they are worth attacking.

| untouched | catalog | route |
|---|---|---|
| 99 | `_30_8` | runtime formal errors — needs a **document** probe (`:adapter:kernelProbe` → `validateFull`), a route we hold and have barely driven |
| 81 | `vk_parser_error_messages` | condition/DSL static legality — the fast `dmtool rule check` batch route |
| 36 | `custom_field_types` | host-registered custom field types — **scope question**, may sit outside the Kernel-owned target |
| 22 | `vk_codegen_no_meta_model_ckecks_error_messages` | codegen-time model checks — reachable through `model check` |
| 17 | `kernel_core_errortext_error_messages` | shared error-text base utilities — carrier not yet identified |
| 16 | `vk_calc_error_messages` | computation authoring — the `computation add --dry-run` batch route |
| 12 | `vk_dynEnum_error_messages` | dynamic enumerations — needs a dynamic-enum declaration shape |
| 8 | `vk_service_errortext_error_messages` | message templates and parameters — the fast `rule check --message` batch route |
| 1 | `vk_parser_common_error_messages` | shared parser diagnostics — the fast `rule check` batch route |
| 1 | `test_rule_error_messages` | on-the-fly rule testing — likely instrument-only, not a semantic class |

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour produce no
refusal class, so Axis 1 is blind to them. The capability records are the available proxy, and a coarser
one: it counts whether a record cites external calibration, not how much of its family is covered.

| | records | share |
|---|---|---|
| Capability records in [`implementation/`](implementation/) | 176 | 100% |
| Citing a Kernel checkpoint or calibration | 82 | 46% |
| Carrying an explicit evidence-pending note | 45 | 25% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | 23 |
| `remaining` rows across those gaps | 231 |
| Gaps whose route is **blocked** | 0 |
| Ledger entries `pending` with a12-dmkits | 3 |
| Ledger entries `handed-off` | 0 |

A blocked route is the only figure here that should stop work; a `remaining` row is ordinary scope. If
blocked is nonzero, that is what to escalate.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[`CLAUDE.md`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and
evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (`Semantics/`, `Elaboration/`, `Proofs/`, `Conformance/`, core types) | 197856 | 100% |
| Support (`Evidence/`, `Reference/`, `Process/`, `Trust/`, drivers) | 8479 | 4% — ceiling 100% |
| Evidence alone | 1517 | 0% — ceiling 33% |

Tracked Lean files in neither estate: 0. A nonzero value means the ratio above is measuring
a subset, so it is a defect in this generator rather than in the estate.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under `../evidence/` | 164 |
| Retained observation rows across all artifacts | 367 |

## Velocity

One row is appended per run, and only when a headline number moved — so a flat `touched` column across
several dated rows is the signal that progression has stalled. The actionable reading when it does is
Axis 1's route column: a stall usually means the remaining blocks need a route this session has not set
up, rather than more rows on the route it already has.

<!-- velocity-history:start -->
| date | revision | touched | modelled | untouched | calibrated caps | open gaps |
|---|---|---|---|---|---|---|
| 2026-09-07 | `3db574b1` | 149 | 78 | 292 | 82 | 23 |
<!-- velocity-history:end -->
