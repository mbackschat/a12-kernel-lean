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
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use the [String-keyed DateRange capability](IMPLEMENTATION-MAP.md#cap-indexed-date-range-construction-computation), the bounded [consumer task catalog](USE-CASES.md), and the [consumer adequacy guide](IMPLEMENTER-GUIDE.md).
- `route`: the checked result already exposes literal-versus-field key identity, field observation, selected address, typed endpoint observation, target policy, and outcome; probe those existing facts without adding a shipment, protocol, harness, or adapter.
- `next`: run one bounded Execute/Analyze/Explain consumer-adequacy probe over the completed String-keyed indexed DateRange construction family; feed back only a reproduced representation or decision-procedure gap before selecting wider SG6 semantics.
- `blocked-on`: none.
- `consumer-probe-trigger`: active for the completed literal/direct-field String-keyed indexed DateRange construction capability milestone.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
