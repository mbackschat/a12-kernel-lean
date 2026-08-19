# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: direct nonrepeatable constructor targets are internally closed for both exact policies and matching `yyyy`, `yyyy-MM`, Base-Year `MM`, and Base-Year `MM-dd`. Checked admission, single-document execution, accepted/inverted outcomes, application, and public queries are covered. Only dotted output is Kernel-pinned; other output is internal composition and inversion is source-rederived.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), and the current [temporal implementation owners](IMPLEMENTATION-MAP.md#6--dates-and-time) to select a source-closed non-overlapping unit.
- `route`: SG6 requires read-only route discovery before another semantic edit; the exact-valued constructor-target family is complete and does not establish unconfigured yearless target execution.
- `next`: inventory the remaining SG6 clauses, source checkpoints, current owners, and overlapping work; select the smallest evidence-sufficient semantic unit and verify its red, green, and supporting loci before implementation.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the complete six-policy exact-valued constructor-target family; active again at the next reusable capability milestone.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
