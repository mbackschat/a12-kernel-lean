# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: the direct nonrepeatable constructor target is internally closed for both exact DateRange policies and matching `yyyy`/`/` through checked admission, single-document execution, typed accepted/inverted-error outcomes, application, and public consumer queries. The dotted filled output is Kernel-pinned; ISO and `yyyy` outputs are internal composition; inversion is source-rederived. Direct fragment-bound compositions and direct `yyyy` overlap remain external evidence pending.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the exact constructor target-rendering route in the [established-kind computation checkpoint](SOURCES.md#src-first-filled-kind-computations), and the existing checked construction, target, result, and application seams.
- `route`: [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion) verifies the next matching `yyyy-MM` constructor-target route through the same [DateRange construction computation owner](IMPLEMENTATION-MAP.md#cap-date-range-construction-computation).
- `next`: red-first extend the construction-target certificate and renderer to matching `yyyy-MM`/`/`; retain exact endpoint-position month completion and refuse `MM`, `MM-dd`, cross-component pairs, repetition, and wider execution.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the complete two-policy exact family and the matching `yyyy` target; active again when the `yyyy-MM` target closes.
- `resume`: `rg -n 'yearMonthFragment|DateRangeConstructionTargetFormat|render|targetFormat' A12Kernel/Elaboration/DateRangeConstructionComputation.lean A12Kernel/Conformance/DateRangeConstructionComputation.lean A12Kernel/Proofs/DateRangeConstructionComputation.lean`
