# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: Tier 2 calibration ready.
- `gap`: [direct temporal `FirstFilledValue` literal calibration](SEMANTICS-GAPS.md#gap-sg8-temporal-first-filled-computation).
- `next`: capture literal empty and first-row-filled signatures for full Date, Time, DateTime, and DateRange through the existing `kernelProbe` route, then evaluate the triggered bounded Execute consumer probe.
- `blocked-on`: none.
- `consumer-probe-trigger`: active because the bounded direct temporal/date-range family is internally closed; run it only after literal calibration fixes the claimed observable signatures.
- `resume`: `rg -n 'src-first-filled-kind-computations|kernelProbe|FirstFilledValueKindDiffTest' docs/SOURCES.md docs/TESTING.md ../a12-rulekit/adapter/src/test ../a12-rulekit/scripts`
