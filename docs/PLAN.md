# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only representation-route discovery required.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and the exact [Base-Year and yearless Kernel checkpoint](SOURCES.md#src-date-range-base-year-fragment-construction).
- `next`: inspect the existing partial-Date carriers, checked stored-DateRange path, and consumer requirements to identify the smallest representation that can express measured same-profile yearless `MM`/`MM-dd` equality without inventing an instant or creating a parallel checked-document architecture. Do not implement until the route and representation boundary are explicit.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive after the configured-Base-Year construction-pair Execute/Analyze/Explain readback; trigger again when a yearless endpoint representation changes the result domain or public compatibility is considered.
- `resume`: `rg -n 'PartiallyKnownDateValue|DateRangeValue|DateRangeEndpointFormat|unknownYear|baseYear|MM-dd' A12Kernel spec/05-dates-and-time.md docs/SOURCES.md docs/USE-CASES.md`
