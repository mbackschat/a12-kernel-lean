# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: direct stored `yyyy` DateRange input and matching construction comparison are represented; stored `yyyy-MM` input remains selected.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and the exact [`yyyy-MM` Kernel checkpoint](SOURCES.md#src-date-range-year-month-fragment-construction).
- `route`: the completed representation boundary is owned by [Architecture](ARCHITECTURE.md#values-keep-semantic-identity-separate-from-storage-identity) and the [temporal comparison implementation record](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates).
- `next`: add direct nonrepeatable stored `yyyy-MM` DateRange input, then admit it against a matching `yyyy-MM` construction in both authored positions while retaining leap-aware exact observations and refusing other component profiles.
- `blocked-on`: none.
- `consumer-probe-trigger`: active when stored `yyyy-MM` mixed execution closes the remaining measured year-bearing fragment family; run the bounded Execute/Analyze/Explain readback before that capsule closes.
- `resume`: `rg -n 'DateRangeInputFormat|parseYearRange|yearMonthFragment|supportsStoredComparison|matchesStoredInput' A12Kernel/Elaboration/DateRangeInput.lean A12Kernel/Elaboration/DateRangeConstructionComparison.lean A12Kernel/Conformance/DateRangeInput.lean A12Kernel/Conformance/DateRangeComparison.lean`
