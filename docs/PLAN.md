# Implementation handoff

This is the cross-session resumption checkpoint, not an in-session task list or work log. Leave it unchanged during uninterrupted route discovery and capsule execution unless another session must resume a different selected action, a blocker must persist, or a consumer-probe trigger changes. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

- `basis`: current committed Lean state; Git owns the exact revision.
- `gate`: Tier 1 passed for that Lean state.

<a id="active-unit"></a>
## Selected work

- `state`: route discovery.
- `gap`: none selected.
- `next`: select the smallest non-overlapping open gap whose discriminator, exclusions, evidence checkpoint, and implementation route can be verified before red/green.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive; evaluate only when the selected work reaches a reusable family, major addressing or computation boundary, or public compatibility claim.
- `resume`: `rg -n '^<a id="gap-|^### (SG|SQ)' docs/SEMANTICS-GAPS.md`
