# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: verified route ready for red/green implementation.
- `gap`: [SG6 plural scalar-versus-list DateRange overlap assembly](SEMANTICS-GAPS.md#gap-sg6-plural-date-range-overlap).
- `oracle`: [canonical Date-range and overlap clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) plus the [plural overlap source checkpoint](SOURCES.md#src-date-range-plural-overlap).
- `next`: add the first plural static-admission guards in the gap's verified red locus, then implement the distinct scalar/list certificate through the shared nonempty entity-list shape without widening into checked-document execution.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until the plural scalar-versus-list capability closes, another major DateRange addressing or computation boundary changes, or public compatibility is considered.
- `resume`: `rg -n 'AtLeastOneDateRangeOverlaps|ResolvedDateRangeSlot|CheckedDateRangesOverlap|FieldEntity|GroupEntity' spec/05-dates-and-time.md docs/SEMANTICS-GAPS.md docs/IMPLEMENTATION-MAP.md A12Kernel ../a12-rulekit`
