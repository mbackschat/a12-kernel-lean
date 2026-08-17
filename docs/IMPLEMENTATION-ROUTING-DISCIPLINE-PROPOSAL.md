# Implementation routing for open semantic gaps

**Status:** proposal only. Nothing in this document changes the adopted documentation policy until the user approves adoption.

## Recommendation

Add a small, typed implementation-route block to an open gap when that route has been verified against the current code and history. The gap owns the route because it owns the live obligation and deletes the route when the obligation closes. Keep implementation status and stable code ownership in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), keep only the selected action in [`PLAN.md`](PLAN.md), and add no routing registry, generator, linter, or repository-wide migration.

Adopt the contract through the currently selected [Date-group diagnostic gap](SEMANTICS-GAPS.md#gap-sg5-date-group-string-value-list-diagnostic) only. Another gap receives routing fields only when it is selected or its route changes for an independent reason.

## Problem

The adopted bounded-record discipline makes the current semantic task cheap to retrieve. One read of [`PLAN.md`](PLAN.md) reaches the selected gap, its implemented baseline, its source oracle, its discriminator, and its focused build command without opening a multi-kilobyte line.

The remaining avoidable search is between the open semantic obligation and the first code edit. The selected gap links the shared group-admission capability, whose correct implemented owner is `FieldEntityList.lean`. The missing behavior is operator-specific, however.

Finding the actual route still required a repository search and inspection of four current files: the red case belongs in `FieldEntityGroupOperand.lean`, the primary projection belongs in `TokenEntityValueList.lean`, the new exact diagnostic belongs in `StaticDiagnostic.lean`, and the diagnostic enumeration proofs live in `Proofs/StaticDiagnostic.lean`.

This is not a defect in implementation ownership. “What mechanism exists?” and “where does this open change begin?” are different facts with different lifecycles. Treating the second as another implementation owner would corrupt the first; leaving it undocumented makes every resuming agent repeat the same discovery.

## Scope

### Required

- Distinguish stable implementation ownership from the verified entry route for one open obligation.
- Let a resuming agent reach the first red case, primary green locus, and at most two necessary supporting loci from the selected gap.
- Make an unknown route explicit without inventing a likely owner.
- Delete routing with the completed gap.

### Optional

- A gap may name one route limit when a plausible secondary file is deliberately excluded until the red case proves it necessary.

### Excluded

- New code ownership, architectural decisions, implementation designs, symbol inventories, line-number indexes, or promises that only the linked files will change.
- Routing fields in capability, provenance, evidence, architecture, or findings records.
- A second copy of routing in `PLAN.md`.
- Repository-wide conversion of existing gaps.
- A schema, parser, generator, linter, registry, metrics file, CI gate, or dependency.

## Ownership contract

The implementation map owns the narrowest stable owner of implemented behavior. A gap owns the verified change route for its still-open obligation. Plan owns selection, next action, stop condition, blocker, and resume command, and points to the gap instead of repeating its route.

A route is a current navigation fact, not a semantic or architectural claim. It says where the first red case and smallest known green change begin on the inspected revision. It does not assert that the diagnosis is complete, that the final diff is confined to those files, or that a supporting representation must change.

Code remains authoritative. Before editing, the implementing agent still inventories the linked definitions, tests, proofs, current history, and overlapping work as required by [`CLAUDE.md`](../CLAUDE.md). Routing removes discovery search; it does not replace the code audit.

## Route record contract

The route block is part of a bounded `gap-` record and uses this closed state:

```text
RouteState ::= verified | discovery-required
```

The keys have these contracts:

| Key | Cardinality | Contract |
|---|---:|---|
| `route-state` | exactly one when the route block is present | `verified` when the linked route was checked against current code and history; `discovery-required` when no route is established |
| `red-locus` | exactly one for `verified`, absent otherwise | Existing conformance or proof file where the first failing guard belongs |
| `green-locus` | exactly one for `verified`, absent otherwise | Narrowest current source file that owns the missing behavior's primary change |
| `supporting-locus` | zero to two for `verified`, absent otherwise | Existing files that must change for a known vocabulary, proof, or assembly consequence |
| `route-limit` | zero or one for `verified`, absent for `discovery-required` | A concrete boundary that prevents a plausible file or wider mechanism from being treated as part of the established route |

Every locus is a regular relative Markdown link to an existing file plus one short local role. A route names files rather than line numbers or private symbols because file ownership is stable enough for resumption while internal declarations may move during the capsule.

### Verified example

The selected gap would gain:

```markdown
- `route-state`: verified against the current code and recent path history.
- `red-locus`: [`FieldEntityGroupOperand.lean`](../A12Kernel/Conformance/FieldEntityGroupOperand.lean) owns shared group-diagnostic conformance and is the first red-case locus.
- `green-locus`: [`TokenEntityValueList.lean`](../A12Kernel/Elaboration/TokenEntityValueList.lean) owns the operator-specific elaboration that needs the projection.
- `supporting-locus`: [`StaticDiagnostic.lean`](../A12Kernel/Elaboration/StaticDiagnostic.lean) owns the exact diagnostic vocabulary that needs the distinct code.
- `supporting-locus`: [`Proofs/StaticDiagnostic.lean`](../A12Kernel/Proofs/StaticDiagnostic.lean) owns enumeration completeness and code uniqueness.
- `route-limit`: [`TokenEntityGroup.lean`](../A12Kernel/Elaboration/TokenEntityGroup.lean) remains outside the established route unless the red case proves that the current refusal loses a cause the primary locus cannot retain.
```

The final line prevents the route from silently becoming a proposed representation change. It records the exact uncertainty discovered during inspection and leaves the red case in control.

### Unknown example

```markdown
- `route-state`: discovery-required.
```

When such a gap is selected, `PLAN.md` names route discovery as the next action and gives a read-only resume command. The agent inspects current code, tests, history, and overlapping work, then either records a verified route or surfaces a genuine blocker. It does not guess loci to make the record look complete.

## Lifecycle and triggers

1. Creating a gap may add a verified route when the current code and history already establish it; otherwise the route is `discovery-required` or omitted until selection.
2. Selecting a gap requires a verified route before semantic edits begin. If the route is unknown, route discovery is the selected action rather than implementation.
3. A file move, ownership refactor, or red result that changes the entry route updates that gap only. A changed primary mechanism updates the implementation map separately because that is a different fact.
4. A red result that merely adds a supporting file updates the route without turning the gap into an implementation plan.
5. Closing the obligation deletes the gap and its route. The implementation map then records the landed owner and assurance; Git retains the route history.

These triggers do not authorize touching every gap when code moves. Search only live route links to the moved file and update the records whose navigation fact actually changed.

## Interaction with Plan

`PLAN.md` remains a compact resumption packet. Its `gap` link reaches the route, `next` states the immediate action, `stop` states the decision boundary, and `resume` gives the command. It does not repeat filenames already owned by the gap.

For the selected capsule, the Plan record can remain semantically unchanged: “add the red conformance case at the shared entity-list group diagnostic boundary” is the action, while the gap supplies the exact file route.

## Enforcement

If adopted, the contract becomes normative in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md). The same-context capsule assessment checks only three routing invariants when a selected gap carries the block:

1. `route-state` is `verified` before semantic edits begin.
2. Every locus link resolves and its stated local role still matches the inspected file.
3. Plan and the implementation map do not duplicate the route.

The ordinary cold review at an adoption or existing risk trigger checks the same finite invariants from the frozen artifact. No permanent executable gate is proposed. The route has too little syntax and too much code-relative judgment for a parser or linter to provide value beyond Markdown link existence, and the repository already forbids new governance machinery without a repeated unmet need.

Direct queries remain sufficient:

```sh
rg -n '^- `route-state`:' docs/SEMANTICS-GAPS.md
rg -n '^- `(red|green|supporting)-locus`:' docs/SEMANTICS-GAPS.md
rg -n '^- `route-limit`:' docs/SEMANTICS-GAPS.md
```

## Acceptance criteria

The bounded adoption is acceptable only when all of the following hold:

1. The selected gap answers where the first red case and primary green change begin without a repository-wide search.
2. Every linked file exists and the role stated beside it is true on the frozen revision.
3. The route neither strengthens a semantic claim nor predetermines an unproved representation change.
4. The implementation map remains the sole owner of implemented boundaries and stable code ownership.
5. Plan remains the sole owner of selection and does not copy route fields.
6. The selected route has exactly one red locus, one green locus, at most two supporting loci, and at most one route limit.
7. A `discovery-required` route names no speculative locus.
8. No unselected gap changes, and adoption creates no migration backlog.
9. No tooling, dependency, schema, code, spec, source, evidence, ledger, architecture, or testing contract changes.
10. `git diff --check`, local Markdown link checks, and `./scripts/check-spec-sync.sh` pass.
11. A cold artifact-only reviewer finds no ownership inversion, duplicated route, speculative design claim, stale link, or widened adoption scope.

## Risks and controls

### Route staleness

File links can survive after responsibility moves. The route is updated only when its linked file moves, its role changes, or the gap is selected and the mandatory pre-edit audit disproves it. Deleting the gap at closure bounds the maintenance lifetime.

### Premature design commitment

A likely helper can be mistaken for an authorized redesign. The route names only the red and smallest known green entry points. Unproved secondary changes belong in `route-limit`, not `supporting-locus`.

### Duplicate ownership

Repeating the route in Plan or the implementation map would recreate the reconciliation problem this discipline removed. The route lives only in the open gap; other owners link to the gap for the local consequence they need.

### Record growth

The exact cardinalities prevent a gap from becoming a file inventory. If more than two supporting loci appear necessary before the red case, the route is not understood well enough to mark `verified`.

## Alternatives considered

### Keep discovery in working context

Rejected. The selected example required a repeatable repository search even though the necessary route was stable and compact. That cost recurs after context transfer and produces no canonical correction.

### Put the route in Plan

Rejected. Plan would become the second owner of details that remain useful while the gap is open but not selected. Changing selection would either discard the route or accumulate a backlog.

### Put the route in the implementation map

Rejected. The implementation map answers what exists and where it is owned. A proposed change route is volatile, may point at a different operator-specific boundary, and disappears when the gap closes.

### Add code-owner metadata or an executable routing index

Rejected. It would require a schema, synchronization rules, validation, and lifecycle ownership for a problem solved by at most six bounded Markdown bullets.

## Adoption decision

Approval would authorize one policy addition plus routing fields on the selected Date-group diagnostic gap. It would not authorize semantic implementation, changes to other gaps, wider documentation conversion, tooling, dependencies, or any public or cross-project contract change.

After the selected pilot closes and its route is deleted with the gap, the durable contract would remain in `DOC-DISCIPLINE.md`. This proposal would then be deleted rather than retained as a second policy owner.
