# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 checked DateRange overlap operand assembly](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: [canonical Date-range and overlap clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap).
- `next`: inventory the existing exact `DateRangeValue` conversion, overlap operators, checked flat operand/addressing constructors, Git history, and active cross-project handoffs; verify the smallest nonredundant route before semantic edits.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until a wider reusable DateRange operand or target capability closes, or public compatibility is considered.
- `resume`: `rg -n 'DateRangeValue|toResolvedDateRange|ResolvedDateRangeOperand|DateRangesOverlap|AtLeastOneDateRangeOverlaps' spec/05-dates-and-time.md docs/SEMANTICS-GAPS.md docs/IMPLEMENTATION-MAP.md A12Kernel`
