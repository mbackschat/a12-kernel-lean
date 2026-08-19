# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: DateRange stored input and checked consumers support six local policies, while external direct-star static admission and runtime cover all eight declaration pairs. Flat declaration validation still checks only source presence, differs from the exact eight-pair allowlist, and wrongly treats an empty separator as intrinsically invalid.
- `gap`: [SG6 DateRange declaration and temporal completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use the canonical [DateRange clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the [reviewed DateRange reconciliation checkpoint](SOURCES.md#src-date-range-2026-08-19-reconciliation), and the [checked declaration capability](IMPLEMENTATION-MAP.md#cap-date-range-checked-declaration).
- `route`: SG6 owns the verified red, green, and supporting loci for the exact declaration gate.
- `next`: implement the exact eight-pair `DateRangeDeclarationPolicy` allowlist red first, preserving the separate six-policy executable input discriminator.
- `excluded`: do not add stored parsing for `MM` with an empty separator or `dd.MM` with dash, `interpretationOfYear`, component-set comparison/target widening, operand diagnostics, another document route, or a harness in this capsule.
- `blocked-on`: none.
- `consumer-probe-trigger`: not triggered by the static declaration capsule; active again when the two additional stored policies or component-set target routing become executable.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
