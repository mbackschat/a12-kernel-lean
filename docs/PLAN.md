# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: verified implementation route.
- `gap`: [SG6 checked DateRange overlap operand assembly](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: [canonical Date-range and overlap clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap).
- `next`: add the first red full-validation checked-document separator for singular `DateRangesOverlap`, then assemble admitted direct, plain-star, and filtered-star cells into the existing ordered skipped/kept operand scan.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until a wider reusable DateRange operand or target capability closes, or public compatibility is considered.
- `resume`: `rg -n 'CheckedDateRangesOverlap|ResolvedCheckedEntityOperandCore|ResolvedDateRangeOperand|evalDateRangesOverlap' docs/SEMANTICS-GAPS.md docs/IMPLEMENTATION-MAP.md A12Kernel`
