# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: implementation route verified.
- `gap`: [checked DateRange declaration and admission](SEMANTICS-GAPS.md#gap-sg6-date-range-checked-declaration).
- `next`: after the independently reviewed value-core commit lands, add the declaration route's red policy/admission separators and implement it through the ordinary checked document.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive; evaluate only when the selected work reaches a reusable family, major addressing or computation boundary, or public compatibility claim.
- `resume`: `rg -n 'gap-sg6-date-range-checked-declaration|inductive (FieldKind|SurfaceScalarKind)|structure FlatFieldDecl|temporalTargetPolicyError' docs/SEMANTICS-GAPS.md A12Kernel/Semantics/Observation.lean A12Kernel/Elaboration/Flat`
