# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: every admitted declaration pair selects exactly one stored-input profile, proved at the input owner. The two lexical variants classify stored text and retain their measured target spelling, while direct bound, singular overlap, and first-filled target-kind selection still refuse them.
- `gap`: [SG6 DateRange declaration and temporal completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use the canonical [DateRange clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the [reviewed DateRange reconciliation checkpoint](SOURCES.md#src-date-range-2026-08-19-reconciliation), and the [checked declaration capability](IMPLEMENTATION-MAP.md#cap-date-range-checked-declaration).
- `route`: SG6 owns the verified red, green, and oracle loci for the direct-star computation route of the two lexical variants.
- `next`: give both variants a first-filled target kind red first, flipping the existing refusal cases and reaching the already-locked stored target text.
- `excluded`: do not add `interpretationOfYear`, bound or singular-overlap support, comparison widening, operand diagnostics, another document route, or a harness in that capsule.
- `blocked-on`: none.
- `consumer-probe-trigger`: armed now: both added stored policies are executable. The pending owner decision at that point is whether the probe exercises the ready DateRange material or opens non-evaluator Analyze breadth: a 2026-08-22 coverage review recommended the latter, but the only ready Analyze capability is the bounded presence-contradiction pilot, which is too small to carry an isolated implementation, so genuine Analyze breadth first needs the [solver proposal](SMT-SOLVER-SUPPORT-PROPOSAL.md) adopted under the dependency-approval rule. Absent that decision, probe the DateRange material artifact-only and leave the proposal unadopted.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
