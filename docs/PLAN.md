# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: checked full-Date route ready for red/green implementation.
- `gap`: [SG6 checked DateRange construction comparison execution](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range equality clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and [construction-equality checkpoint](SOURCES.md#src-date-range-construction-equality) establish full-Date authoring, exact endpoint identity, formal-before-empty source classification, and the external-evidence limit.
- `next`: add red checked-document cases for equal constructions, finish-only mismatch, empty endpoint suppression, formal-over-empty UNKNOWN, and wrong runtime value kind; implement one checked construction/result carrier over `CheckedFullDateTarget`, retain all four endpoint observations, and delegate verdict projection to the existing symmetric DateRange comparison seam.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until checked construction comparison closes, another major DateRange boundary changes, or public compatibility is considered.
- `resume`: `rg -n 'CheckedFullDateTarget|CheckedDocument|DateRangeConstruction|evalSymmetric' A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Conformance A12Kernel/Proofs`
