# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-17:** the shared entity-list wildcard/terminal-presence capsule passed its complete Tier 1 gate in this slice; the last exact committed full-gate baseline is `f38acf0`. Re-run the required tier commands in [`TESTING.md`](TESTING.md#tier-gates) before the next semantic edit.

<a id="active-unit"></a>
## Selected work

- `gap`: [SG5 group static-diagnostic residuals](SEMANTICS-GAPS.md#gap-sg5-group-static-diagnostic-residuals).
- `objective`: establish a verified evidence and implementation route for the unstarred equal-group result and the cardinality-versus-duplicate precedence residual before semantic edits.
- `oracle`: the gap's same-carrier multi-fault discriminator; no unmeasured result or precedence is assumed.
- `next`: inspect current shared-shape gate order and a12-dmkits authoring surfaces for one matrix that independently reaches equal-group, cardinality, direct-duplicate, and indirect-overlap states.
- `stop`: if the current dmtool surface cannot express and kernel-check the separating matrix without an upstream change, record the bounded request and leave every residual unmapped.
- `blocked-on`: none.
- `consumer-probe-trigger`: close the reusable SG5 group static-diagnostic family, then run one bounded Translate/Explain probe over admitted, mapped, and rejected-unmapped decisions; this route-discovery unit triggers no Execute or SMT probe.
- `resume`: `rg -n -C 6 'tooFewFields|duplicateOperand|overlappingOperands|firstDuplicateResolvedDirectField|firstResolvedOperandOverlap' A12Kernel/Elaboration/FieldEntityList.lean A12Kernel/Conformance/FieldEntityGroupOperand.lean`
