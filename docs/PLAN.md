# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: the direct nonrepeatable full-Date constructor-to-dotted/dash DateRange target is internally closed through checked admission, single-document execution, exact rendering, typed accepted/inverted-error outcomes, application, and a public consumer query. Its filled output is Kernel-pinned; inversion is source-rederived; empty, formal, and static refusal rows remain internal. Direct fragment-bound compositions and direct `yyyy` overlap remain external evidence pending.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the exact constructor target-rendering route in the [established-kind computation checkpoint](SOURCES.md#src-first-filled-kind-computations), and the existing checked construction, target, result, and application seams.
- `route`: the verified implementation route and exclusions are owned by [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion); the implemented operation is owned by the [DateRange construction computation record](IMPLEMENTATION-MAP.md#cap-date-range-construction-computation).
- `next`: admit the same checked direct nonrepeatable full-Date constructor for one direct same-group nonrepeatable ISO/slash DateRange target through the shared target-result evaluator, retaining the dotted/dash route and the existing single document.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the dotted/dash constructor target; active again when the two-policy direct constructor-target family closes.
- `resume`: `rg -n 'CheckedDateRangeConstructionComputation|evaluateComputationResult|targetFormat|dayMonthYearDash' A12Kernel/Elaboration/DateRangeConstructionComputation.lean A12Kernel/Semantics/TemporalTarget.lean A12Kernel/Conformance/DateRangeConstructionComputation.lean`
