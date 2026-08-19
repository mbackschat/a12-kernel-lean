# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: direct nonrepeatable constructor targets are internally closed for both exact policies and all four matching fragments, preserving component-only `MM` and `MM-dd` without Base Year. DateRange `FirstFilledValue` covers the six direct-star policies plus a finite direct nonrepeatable same-group list under any one of those six policies, preserving exact or yearless identity, authored source order, recursive lazy selection, and declaration-owned target rendering.
- `state`: Kernel calibration covers no-Base-Year `MM` and `MM-dd` constructor targets, dotted/dash lists at lengths two and three, and three-source lists for all four fragments.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), and the current [temporal implementation owners](IMPLEMENTATION-MAP.md#6--dates-and-time) to select a source-closed non-overlapping unit.
- `route`: SG6 requires read-only route discovery before another semantic edit; the completed direct-star and six-profile direct-list slices do not establish ISO/slash list correspondence, fragment-list formal suffixes, external authorability beyond three sources, or mixed, group, filtered, nested, partial-validation, and scheduling routes.
- `next`: inventory the remaining SG6 clauses, source checkpoints, current owners, and overlapping work; select the smallest evidence-sufficient semantic unit and verify its red, green, and supporting loci before implementation.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the six-policy constructor-target/direct-star decisions and the six-profile direct-list Execute/Analyze decision through the calibrated third source; active again at the next reusable capability milestone.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
