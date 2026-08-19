# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: direct nonrepeatable constructor targets are internally closed for both exact policies and all four matching fragments, preserving component-only `MM` and `MM-dd` without Base Year. DateRange `FirstFilledValue` covers the six direct-star policies plus a finite direct nonrepeatable same-group list under any one of those six policies, preserving exact or yearless identity, authored source order, recursive lazy selection, and declaration-owned target rendering.
- `state`: Kernel calibration covers no-Base-Year `MM` and `MM-dd` constructor targets, dotted/dash lists at lengths two and three, three-source lists for all four fragments, and literal- or direct-String-field-keyed exact full-Date construction targets in one direct one-level String-indexed group.
- `state`: Lean closes both literal- and direct-evaluated-String-field-keyed indexed constructor-target profiles with checked key-observation and selected-address retention, clean no-match and selected-empty clearing, exact selector-formal poison, and duplicate-column poison through the shared preliminary index route.
- `state`: the bounded isolated Execute/Analyze/Explain probe reconstructed the complete String-keyed decision and inverted target trace from the canonical DateRange, path, and computation clauses plus the capability record; Q is closed for that task only.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), the [canonical DateRange clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), and the current [temporal implementation owners](IMPLEMENTATION-MAP.md#6--dates-and-time) to select the next source-closed non-overlapping semantic unit.
- `route`: SG6 has no verified route for its next unit; begin with read-only inventory and route discovery, then add the exact verified red/green loci before any semantic edit.
- `next`: select and verify the next bounded SG6 semantic route without widening the completed String-keyed profile merely by analogy; prefer an externally closed unit whose existing checked representation serves a named consumer decision.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the completed literal/direct-field String-keyed indexed DateRange Execute/Analyze/Explain decision; active again at the next reusable capability milestone.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
