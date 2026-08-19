# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes.
Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: singular direct `yyyy-MM` and Base-Year-completed `MM`/`MM-dd` overlap are closed with their consumer probes; the measured without-Base-Year diagnostic is represented without widening starred or plural routes.
- `gap`: [SG6 DateRange Date/DateFragment endpoint admission and completion](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap), the exact [`yyyy` completion checkpoint](SOURCES.md#src-date-range-year-fragment-construction), and the established pure inclusive overlap predicate. Direct `yyyy` overlap remains external evidence pending.
- `route`: the completed representation boundary is owned by [Architecture](ARCHITECTURE.md#values-keep-semantic-identity-separate-from-storage-identity) and the [temporal comparison implementation record](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates).
- `next`: admit direct nonrepeatable stored `yyyy` DateRange operands in the checked singular overlap owner, retain January 1/December 31 boundary polarity and next-year non-overlap, and keep fragment stars and plural positions refused.
- `blocked-on`: none.
- `consumer-probe-trigger`: passed for configured Base-Year fragment overlap; active again when the direct year-bearing fragment-overlap family closes.
- `resume`: `rg -n 'DirectDateRangeOverlapFragmentProfile|certifyDirectDateRangeOverlapFragmentField|yearFragment|yearMonth|fragmentField' A12Kernel/Elaboration/DateRangeOverlap.lean A12Kernel/Conformance/DateRangeFragmentOverlap.lean A12Kernel/Elaboration/DateRangeInput.lean`
