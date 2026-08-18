# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required after the current capsule commit.
- `gap`: [SG6 DateRange bound component extraction composition](SEMANTICS-GAPS.md#gap-sg6-date-range-bound-component).
- `oracle`: [stored DateRange bound extraction](SOURCES.md#src-date-range-bound-extraction).
- `next`: inventory the existing typed Date-component projection, numeric operand/result owners, and bound-read phase projection; verify the narrow composition route before semantic edits.
- `blocked-on`: none.
- `consumer-probe-trigger`: defer the next bounded probe until component composition adds a new operator decision.
- `resume`: `rg -n 'DateNumericPart|fromFullDateObservation|resolveDateNumericOperand|DateRangeBound|DateValue' A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Conformance docs/SOURCES.md`
