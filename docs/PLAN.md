# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: yearless stored input, the shared exact-or-yearless equality seam, construction-pair execution, and matching no-Base-Year construction-versus-stored execution are represented; configured-Base-Year mixed execution remains selected.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and the exact [Base-Year and yearless Kernel checkpoint](SOURCES.md#src-date-range-base-year-fragment-construction).
- `route`: the completed representation boundary is owned by [Architecture](ARCHITECTURE.md#values-keep-semantic-identity-separate-from-storage-identity) and the [temporal comparison implementation record](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates).
- `next`: extend checked construction-versus-stored equality to declaration-matched configured-Base-Year `MM` and `MM-dd` profiles in both authored positions, retain the exact completed construction and stored observations, delegate to the shared equality seam, and keep `yyyy`, `yyyy-MM`, and cross-profile pairs statically refused.
- `blocked-on`: none.
- `consumer-probe-trigger`: active when configured mixed execution closes the measured direct fragment-comparison family; run the bounded Execute/Analyze/Explain readback before that capsule closes.
- `resume`: `rg -n 'supportsStoredComparison|matchesStoredInput|monthFragment|monthDayFragment|storedMonthRange|unsupportedConstructionProfile' A12Kernel/Elaboration/DateRangeConstructionComparison.lean A12Kernel/Conformance/DateRangeComparison.lean`
