# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) admits bare Date or DateFragment endpoints with matching component sets after Base-Year supplementation; current checked construction execution is intentionally full-Date only.
- `next`: inventory the existing DateFragment value/format representation, Base-Year supplementation and earliest/latest completion owners, semantic-index endpoint admission, and exact Kernel/a12-dmkits evidence before choosing the smallest executable construction extension; do not widen formats or addressing without a separating source row.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until fragment completion changes the represented equality family or public compatibility is considered; the bounded full-Date pair/mixed Execute/Analyze/Explain probe is closed without shipment qualification.
- `resume`: `rg -n 'DateFragment|PartiallyKnownDateValue|ValueAsDate|completeEarliest|completeLatest|semanticIndex|DateRangeConstruction' A12Kernel spec/05-dates-and-time.md docs/SOURCES.md`
