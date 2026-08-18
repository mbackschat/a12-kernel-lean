# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: verified resolved route ready for red/green implementation.
- `gap`: [SG6 DateRange construction-versus-construction comparison](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range equality clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and [construction-equality checkpoint](SOURCES.md#src-date-range-construction-equality) establish the exact filled resolved endpoint account and measured static reachability.
- `next`: add red cases for equal constructions and a finish-only mismatch, factor their exact endpoint comparison through the existing construction/stored semantic owner, and add the smallest symmetry law. Keep full checked execution and external runtime verdicts outside this resolved capsule.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until checked construction comparison closes, another major DateRange boundary changes, or public compatibility is considered.
- `resume`: `rg -n 'ResolvedDateRangeConstruction|evalDateRangeConstruction|DateRangeConstructionPosition' A12Kernel/Semantics/DateRangeComparison.lean A12Kernel/Conformance/DateRangeComparison.lean A12Kernel/Proofs/DateRangeComparison.lean`
