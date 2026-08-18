# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 wider DateRange computation target/rendering](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), beyond the fixed ISO/slash direct `FirstFilledValue` profile.
- `next`: determine whether the smallest coherent widening is the existing second full-Date endpoint renderer under declaration-owned DateRange policy; verify the red conformance owner, green implementation owner, exact admitted separator boundary, and source/evidence limit before semantic edits.
- `blocked-on`: none.
- `consumer-probe-trigger`: satisfied for the exact fixed four-carrier profile; trigger again only after a reusable wider family closes or another defined milestone/risk boundary is reached.
- `resume`: `rg -n 'DateRangeTargetFormat|dateRangeIsoSlash|DateRangeDeclarationPolicy|wider computation targets' A12Kernel docs/SEMANTICS-GAPS.md docs/IMPLEMENTATION-MAP.md`
