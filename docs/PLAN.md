# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: direct nonrepeatable constructor targets are internally closed for both exact policies, matching `yyyy` and `yyyy-MM`, and matching `MM` with Base Year, including checked admission, single-document execution, accepted/inverted-error outcomes, application, and public queries. The dotted output is Kernel-pinned; all other outputs are internal composition; inversion is source-rederived. Direct fragment-bound compositions and direct `yyyy` overlap remain external evidence pending.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the exact constructor target-rendering route in the [established-kind computation checkpoint](SOURCES.md#src-first-filled-kind-computations), and the existing checked construction, target, result, and application seams.
- `route`: [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion) verifies the next configured-Base-Year `MM-dd` constructor-target route through the same [DateRange construction computation owner](IMPLEMENTATION-MAP.md#cap-date-range-construction-computation).
- `next`: red-first extend the construction-target certificate and renderer to matching direct `MM-dd`/`/` only when the checked model supplies Base Year; retain authored days and refuse unconfigured `MM-dd`, cross-component pairs, repetition, and wider execution.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the complete two-policy exact family, both year-bearing targets, and configured `MM`; active again when configured `MM-dd` closes.
- `resume`: `rg -n 'monthDayFragment|yearlessMonthDay|DateRangeConstructionTargetFormat|render|targetFormat' A12Kernel/Elaboration/DateRangeConstructionComputation.lean A12Kernel/Conformance/DateRangeConstructionComputation.lean A12Kernel/Proofs/DateRangeConstructionComputation.lean`
