# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: direct year-bearing and Base-Year-completed `MM`/`MM-dd` bounds are internally closed through extraction, fixed-Date comparison, numeric components, and consumer queries. Their fragment-bound compositions and direct `yyyy` overlap remain external evidence pending.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the exact constructor target-rendering route in the [established-kind computation checkpoint](SOURCES.md#src-first-filled-kind-computations), and the existing checked construction, target, result, and application seams.
- `route`: the verified implementation route and exclusions are owned by [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion); the implemented construction and target boundaries are owned by the [temporal comparison implementation record](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates) and [checked DateRange declaration](IMPLEMENTATION-MAP.md#cap-date-range-checked-declaration).
- `next`: compose one direct nonrepeatable full-Date `DateRange(start, finish)` construction into one checked direct nonrepeatable dotted/dash DateRange target, retaining both endpoint observations, exact target rendering, typed outcome, and application through the existing single document.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the direct year-bearing and Base-Year-completed fragment-bound families; active when the direct DateRange constructor-to-target capability closes.
- `resume`: `rg -n 'CheckedDateRangeConstruction|DateRangeTargetOutcome|DateRangeFormat|DateRangeFirstFilled' A12Kernel/Elaboration/DateRangeConstructionComparison.lean A12Kernel/Elaboration/DateRangeFirstFilledComputation.lean A12Kernel/Semantics/TemporalTarget.lean A12Kernel/Semantics/TemporalApplication.lean`
