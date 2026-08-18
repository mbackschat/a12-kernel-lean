# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 checked DateRange construction comparison execution](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- `oracle`: the [canonical Date-range equality clause](../spec/05-dates-and-time.md#8-date-ranges-and-overlap) and [construction-equality checkpoint](SOURCES.md#src-date-range-construction-equality) establish filled endpoint identity and static reachability but leave checked empty/formal execution and external runtime verdicts open.
- `next`: inventory reusable full-Date declaration certification, immutable checked-document reads, construction result classification, and the exact Kernel/a12-dmkits empty and formal routes; establish the smallest phase-complete checked comparison boundary before any edit.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive until checked construction comparison closes, another major DateRange boundary changes, or public compatibility is considered.
- `resume`: `rg -n 'CheckedFullDateTarget|CheckedDocument|DateRangeConstruction|constructDateRange|vergleicheDATERANGE' A12Kernel/Elaboration A12Kernel/Semantics ../a12-kernel ../a12-rulekit/interpreter`
