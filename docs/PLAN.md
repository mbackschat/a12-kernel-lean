# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: bounded consumer probe, then read-only route discovery.
- `gap`: [SG6 remaining DateRange overlap assembly](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: [canonical Date-range and overlap clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap).
- `next`: run the milestone consumer query against the public checked singular-overlap API, requiring recovery of authored operand order, concrete addresses, skipped/kept slots, exact filter provenance, and the derived verdict without source archaeology; then discover the plural scalar-versus-list admission and checked-document route read-only.
- `blocked-on`: none.
- `consumer-probe-trigger`: active because the reusable checked singular DateRange operand capability closed.
- `resume`: `rg -n 'CheckedDateRangesOverlapResult|evaluateCheckedDocument|DateRange overlap' docs/USE-CASES.md docs/IMPLEMENTATION-MAP.md A12Kernel`
