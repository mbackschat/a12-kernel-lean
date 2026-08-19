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
- `state`: the bounded full-precision Date classifier now derives `yyyy-MM-dd` and `dd.MM.yyyy` values and exact format-versus-Date-invalid causes from stored text and retains UTC/GMT/Berlin midnight identity; exact DateRange endpoints reuse the same parser and resolver.
- `gap`: [SG6 full-Date checked input and temporal completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: use [SG6](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), the canonical [stored-Date floor](../spec/05-dates-and-time.md#4-the-gregorian-floor) and [legacy model-zone parsing](../spec/05-dates-and-time.md#5-time-zones-and-the-sub-day-difference) clauses, the [stored full-Date source checkpoint](SOURCES.md#src-full-date-stored-input), and the current [temporal implementation owners](IMPLEMENTATION-MAP.md#6--dates-and-time).
- `route`: the integrated build identified the existing full-Date checked-document consumers and fixtures as the exact next boundary; inventory their retained stored/raw assumptions and establish synchronized red/green loci before changing the document invariant.
- `next`: integrate the bounded full-Date classifier into the single CheckedDocument route and synchronize every affected full-Date and DateRange consumer without widening to partial Date, wider formats, Time/DateTime, or other zones.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for the completed literal/direct-field String-keyed indexed DateRange Execute/Analyze/Explain decision; active again at the next reusable capability milestone.
- `resume`: `rg -n '^- `(remains|external-gap|unresolved-source|risk|route-state)`:' docs/SEMANTICS-GAPS.md && rg -n '^- `(state|boundary|assurance|remains)`:' docs/IMPLEMENTATION-MAP.md`
