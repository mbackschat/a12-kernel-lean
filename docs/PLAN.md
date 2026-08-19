# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: the direct nonrepeatable full-Date constructor is internally closed for both exact DateRange target policies through checked admission, single-document execution, exact rendering, typed accepted/inverted-error outcomes, application, and a public consumer query. The dotted filled output is Kernel-pinned; ISO output is internal composition; inversion is source-rederived. Direct fragment-bound compositions and direct `yyyy` overlap remain external evidence pending.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the exact constructor target-rendering route in the [established-kind computation checkpoint](SOURCES.md#src-first-filled-kind-computations), and the existing checked construction, target, result, and application seams.
- `route`: [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion) marks the next DateFragment constructor-target route as discovery-required; the two exact policies are owned by the [DateRange construction computation record](IMPLEMENTATION-MAP.md#cap-date-range-construction-computation).
- `next`: perform read-only route discovery for the smallest year-bearing DateFragment constructor-target slice, beginning with `yyyy`; identify the existing target presentation owner, first failing conformance guard, and exact exclusions before semantic edits.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the complete two-policy exact constructor-target family; active again when one DateFragment constructor-target family closes.
- `resume`: `rg -n 'DateRangeInputFormat|yearFragment|render|CheckedDateRangeConstructionComputation|targetFormat' A12Kernel/Elaboration/DateRangeInput.lean A12Kernel/Elaboration/DateRangeConstructionComputation.lean A12Kernel/Semantics/TemporalTarget.lean A12Kernel/Conformance/DateRangeConstructionComputation.lean`
