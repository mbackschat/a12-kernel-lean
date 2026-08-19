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
- `state`: Lean closes the literal-keyed indexed constructor-target profile with selected-address retention, clean no-match and selected-empty clearing, and duplicate-column poison through the shared preliminary index route.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), [String-index source checkpoint](SOURCES.md#src-indexed-date-range-construction-target), [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), and the current [temporal implementation owners](IMPLEMENTATION-MAP.md#6--dates-and-time).
- `route`: follow SG6's verified implementation route; no new document, index evaluator, or target renderer is needed.
- `next`: extend the checked indexed DateRange endpoint key from literal exact text to one direct nonrepeatable evaluated String field, preserving the key observation and the same selected-address, no-match, empty, and duplicate-column result boundary; keep fragments, wider index kinds, nested/cross-group selection, and comparisons excluded.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the six-policy constructor-target/direct-star decisions and the six-profile direct-list Execute/Analyze decision through the calibrated third source; active again at the next reusable capability milestone.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
