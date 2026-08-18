# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: read-only route discovery required.
- `gap`: [SG6 DateRange raw ingestion and formal propagation](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), beyond the closed direct `FirstFilledValue` declaration policies.
- `next`: determine whether the existing checked-document route can parse stored DateRange text under both exact declaration pairs while preserving empty, malformed, and endpoint-resolution distinctions; verify the source and red/green owners before semantic edits.
- `blocked-on`: none.
- `consumer-probe-trigger`: satisfied for the direct temporal `FirstFilledValue` family; the wider DateFragment policies add no new consumer distinction beyond exact declaration matching and checked-token selection. Trigger again only after a reusable wider family closes or another defined milestone/risk boundary is reached.
- `resume`: `rg -n 'DateRange|RawCell|parse.*Range|formalCheck' A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Conformance docs/SOURCES.md ../a12-rulekit/interpreter`
