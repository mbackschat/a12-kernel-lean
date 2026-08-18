# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 checked DateRange bound extraction](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion) over the now-canonical stored-input value.
- `next`: inventory the existing resolved-range, field-read, `StartOfDateRange`/`EndOfDateRange`, and full-Date consumer owners; verify whether a nonrepeatable checked field can reuse them without another operand or document representation before selecting red/green loci.
- `blocked-on`: none.
- `consumer-probe-trigger`: defer the next bounded Execute/Explain probe until checked DateRange bound extraction joins canonical stored input into one reusable field-consumer slice; raw classification alone already answers its predicted query and adds no operator decision.
- `resume`: `rg -n 'StartOfDateRange|EndOfDateRange|DateRangeValue|ResolvedDateRange|dateRange' A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Conformance docs/SOURCES.md ../a12-rulekit/interpreter`
