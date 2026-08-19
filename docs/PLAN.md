# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: matching `MM` and `MM-dd` construction-versus-stored execution is represented with or without Base Year; direct stored `yyyy` and `yyyy-MM` DateRange input remains selected.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and the exact [`yyyy` Kernel checkpoint](SOURCES.md#src-date-range-year-fragment-construction).
- `route`: the completed representation boundary is owned by [Architecture](ARCHITECTURE.md#values-keep-semantic-identity-separate-from-storage-identity) and the [temporal comparison implementation record](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates).
- `next`: add direct nonrepeatable stored `yyyy` DateRange input, then admit it against a matching `yyyy` construction in both authored positions while retaining exact completed observations and refusing `yyyy-MM` or other component mismatches.
- `blocked-on`: none.
- `consumer-probe-trigger`: the configured-Base-Year mixed milestone passed its public Execute/Analyze/Explain readback; run the next bounded probe only after both stored `yyyy` and `yyyy-MM` mixed profiles close the remaining measured year-bearing fragment family.
- `resume`: `rg -n 'DateRangeInputFormat|parseYearlessRange|yearFragment|supportsStoredComparison|matchesStoredInput' A12Kernel/Elaboration/DateRangeInput.lean A12Kernel/Elaboration/DateRangeConstructionComparison.lean A12Kernel/Conformance/DateRangeInput.lean A12Kernel/Conformance/DateRangeComparison.lean`
