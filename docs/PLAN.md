# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: bounded Execute consumer probe ready.
- `gap`: [resolved `FirstFilledValue`](IMPLEMENTATION-MAP.md#cap-first-filled-value), exact direct temporal/date-range subset.
- `next`: run the triggered artifact-only Execute probe against the canonical computation clauses and calibrated clear/value matrix; feed any missing distinction back into the owning semantic clause before selecting another capsule.
- `blocked-on`: none.
- `consumer-probe-trigger`: active and calibrated because the bounded direct temporal/date-range family is internally and externally closed for its exact clear/value matrix.
- `resume`: `rg -n 'FirstFilledValue|Temporal stored form|consumer probe' spec/02-logic-and-formal-errors.md spec/09-computations.md docs/IMPLEMENTER-GUIDE.md docs/TESTING.md docs/USE-CASES.md`
