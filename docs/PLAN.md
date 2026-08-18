# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only source discriminator required.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and the exact [`yyyy` Kernel checkpoint](SOURCES.md#src-date-range-year-fragment-construction); its pair rows agree across engines, while its separate construction-versus-stored row exposes an a12-dmkits interpreter defect.
- `next`: obtain one exact Kernel separator for direct nonrepeatable `yyyy-MM` endpoints, including leap and non-leap finish completion, before extending the checked construction; keep Base-Year-dependent formats, semantic indices, repeatable placement, computation targets, and rendering outside that slice.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive after the exact `yyyy` construction-pair Execute/Analyze/Explain readback; trigger again when another component profile changes the represented equality family or public compatibility is considered.
- `resume`: `rg -n 'DateRangeEndpointFormat|OmittedDayDate|yyyy-MM|datesAndFormatsToDateRange|buildRangeEndpoint' A12Kernel ../a12-kernel/ ../a12-rulekit/ spec/05-dates-and-time.md docs/SOURCES.md`
