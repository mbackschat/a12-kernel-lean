# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 remaining temporal `FirstFilledValue` policies](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), after closing both bounded full-Date and DateRange declaration pairs.
- `next`: determine whether any remaining authorable temporal declaration can receive a computed `FirstFilledValue` result without widening the checked value representation; reject time-only DateTime and partial or optional-check routes unless exact target admission and runtime semantics support them.
- `blocked-on`: none.
- `consumer-probe-trigger`: satisfied for the exact fixed four-carrier profile; the second full-Date and DateRange policies add no new consumer distinction beyond the already-probed declaration-owned rendering decision. Trigger again only after a reusable wider family closes or another defined milestone/risk boundary is reached.
- `resume`: `rg -n 'dateTimeIso|monthFragment|youngerThan1900Check|TemporalFirstFilledStarCarrier' A12Kernel docs/SOURCES.md ../a12-rulekit/src/test`
