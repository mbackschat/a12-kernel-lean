# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: blocked on an owner decision.
- `gap`: [direct temporal `FirstFilledValue` computation remainder](SEMANTICS-GAPS.md#gap-sg8-temporal-first-filled-computation).
- `next`: adopt one universal checked DateRange declaration and value representation, then route-discover the smallest foundational capsule before returning to the DateRange computation.
- `blocked-on`: the universal checked document carries only scalar `Value`, but the existing `ResolvedDateRange` is owned by a later semantics module. Choosing the foundational carrier changes the model, document, target, and future comparison consumers; do not create a parallel DateRange document or begin semantic edits before the route is verified.
- `consumer-probe-trigger`: inactive; evaluate only when the selected work reaches a reusable family, major addressing or computation boundary, or public compatibility claim.
- `resume`: `rg -n 'gap-sg8-temporal-first-filled-computation|inductive (Value|FieldKind|SurfaceScalarKind)|structure (FlatFieldDecl|CheckedAddressedCell|ResolvedDateRange)' docs/SEMANTICS-GAPS.md A12Kernel`
