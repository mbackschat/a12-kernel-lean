# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 DateRange construction-versus-construction comparison](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range equality clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) admits two constructions, while the [current source checkpoint](SOURCES.md#src-date-range-construction-equality) explicitly excludes that pairing.
- `next`: inventory the existing construction-equality carrier and evaluator, checked endpoint sources, exact a12-dmkits static route, runtime/evidence history, proofs, and separating cases; establish the smallest exact route before any edit.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until the next reusable capability or another major DateRange boundary closes, or public compatibility is considered.
- `resume`: `rg -n 'DateRange.*DateRange|DateRangeConstruction|evalDateRangeConstruction|construction-versus-construction' spec/05-dates-and-time.md docs/SEMANTICS-GAPS.md docs/IMPLEMENTATION-MAP.md docs/SOURCES.md A12Kernel ../a12-rulekit`
