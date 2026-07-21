# Active implementation plan

This is the minimal continuation checkpoint. Current coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), durable semantic conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), completed work narratives in the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md), and stable workflow rules in [`../CLAUDE.md`](../CLAUDE.md) and [`TESTING.md`](TESTING.md).

## Verified baseline

- Semantic baseline before the current capsule: `e91a2cd` (`feat(dates): add admitted month and year shifts`).
- Its focused proof build, full `lake build`, 51/51 retained-observation replay, and 11,601-declaration trust audit passed.
- Reference semantics remains 0.3.0 with the V2 flat-validation and one-group-correlation suites.
- Internally closed but externally uncalibrated families remain `external evidence pending`; no per-capsule evidence machinery is planned.

## Active unit

Close signed whole-month and whole-year differences for stored/full Dates before broader temporal integration. Derive the only candidate from calendar coordinates, reduce it exactly when the matching month/year landing would pass the later date, and restore the authored operand sign.

Success means ordinary, partial-period, clamped month-end, leap-year, reverse, and equal cases are executable; general self-zero and swap-negation are proved; and the capsule explicitly excludes empty/formal operands, constructed-Date legacy-hybrid identity, DateTime, Number provenance/scale, checked lowering, and cell effects.

## Frontier queue

- **Satisfied — finalized IF202 handoff:** the handoff for a12-dmkits `6039fd3e` was reconciled as a verified no-op after `426cdb6`; the method-entry filter skip, neighboring unfiltered route, codegen research order, and inbound provenance are already owned locally.
- **Satisfied — IF193 group presence:** a12-dmkits `7f152509` matches the existing product state and consumer projections introduced by `d19f77e`; do not add another group-state representation.
- **Satisfied — IF194 nested-star tails:** `7f152509` matches the hierarchical reopened-star mechanism and laws introduced by `d285cb5`; do not add a flat tail flag or parallel aggregate scan.
- **Satisfied — semantic-index presence:** `005efb2` reuses the resolved lookup and direct-field presence projections across both phases.
- **Satisfied — semantic-index field-fill operands:** `acdd384` reuses the resolved lookup plus extensional validation tally and ordered computation-slot owners.
- **Satisfied — guarded-table common precondition:** `9894c86` left-conjoins the resolved common condition into every guarded alternative and carries the exact holding/not-true/poison laws through the resolved String consumer.
- **Satisfied — generated-validation common precondition:** `1fc3050` carries one checked common condition through both phases and keeps validation's guard outside the complete mismatch disjunction.
- **Satisfied — guarded-table breadth:** `e2f0f4a` widens the same checked literal owner to two-or-more alternatives with one declaration-ordered remainder.
- **Satisfied — computed-target guard rejection:** `d085ae2` rejects the target ID in common and every alternative guard, with operation-side checking retained for expression-valued authoring.
- **Satisfied — nonempty literal table:** `3b7fea9` admits an optionally guarded singleton beside the guarded two-or-more table without manufacturing a true condition.
- **Satisfied — checked numeric computation operation:** `6cd756d` resolves and admits the plain nonrepeatable expression before its existing computation evaluator.
- **Satisfied — warning-suppressed numeric no-fit:** `2a77643` adds the explicit bounded-storage target branch while preserving the ordinary fail-closed entry point.
- **Satisfied — checked computation suppression:** `0aeddb1` retains the legal warning flag through admission and routes the evaluated result through the matching target entry point.
- **Satisfied — shared warning gate:** `16ff14b` consolidates the exact suppression primitive after its second completed consumer.
- **Satisfied — resolved Number target constraints:** `8714edb` closes the fit-only integer-digit, zero, rendered-length, and inclusive-range suffix while preserving the no-fit decimal-error boundary.
- **Satisfied — target-policy ownership:** `3d216ff` retains one complete resolved policy on the checked numeric operation, rejects scale/signedness mismatch before evaluation, and removes caller policy choice from evaluation without duplicating constraints in `NumField` or inferring them from erased declaration data.
- **Satisfied — checked direct numeric value functions:** `bf441bd` reuses one authored-shape predicate across validation and computation for direct-field `Round`/`Abs` and direct-field/one-constant `Min`/`Max`; general wrapper traversal remains fail-closed.
- **Satisfied — admitted full-Date month/year shifts:** `e91a2cd` implements post-conversion integer `AddMonths`/`AddYears` on stored/full Dates, retains their clamp-versus-February-end distinction, and reapplies the universal Date floor without claiming constructed-Date legacy behavior.
- **Active — admitted full-Date month/year differences:** compute signed completed periods through the matching shift convention and keep the February-end year boundary distinct from month counting without claiming reason-bearing or legacy-calendar operands.
- **Blocked — checked computation-table integration:** runtime first-match selection alone is insufficient because the mandatory all-alternatives generated rule cannot yet represent checked numeric-expression leaves; share one condition representation before admitting expression-valued tables.
- **Missing approved shared refactor — expression-valued generated validation:** `CheckedResolvedFlatRule` consumes only `FlatCondition`, while checked numeric expressions have a separate evaluator. Integrating them requires one bounded shared-condition refactor across flat rule assembly and numeric comparison; do not add a parallel condition tree.
- **Missing fact — repeatable operand lowering:** needs checked star positions, capacities, row reads, and per-source metadata from one source-owned model representation.
- **Missing fact — aggregate expressions:** needs a shared checked expression-tree extension with more than one real consumer; do not add an aggregate-only comparison wrapper.
- **Missing fact — String targets:** needs declaration-owned length and line-break policy; do not infer unconstrained policy from erased model facts.
- **Missing authorization — flat literal scale and protocol-sensitive seams:** require deliberate protocol versioning or a separate adopted public-boundary change.
- **Forbidden duplicate mechanism:** no copied a12-dmkits harness, second numeric AST or scale gate, second aggregate scan, alternate group-state encoding, or parallel protocol route.

## Parked boundaries

- `DifferenceInDays` beyond the finite Berlin 2024 profile needs the versioned model-zone legacy-calendar account; proleptic `CivilDate` is not a substitute.
- Authored message integration still needs checked templates and real display providers.
- Checked group-instance enumeration and wildcardable relevance construction remain outside resolved group-presence projections.
- Public protocol expansion, semantic shipments, candidate qualification, SMT dependencies, and new evidence/process machinery require explicit adoption or approval.
- Batch external calibration by coherent family; do not create one producer request per internal capsule.

## Stop conditions

- Stop a candidate when its required model fact, consumer, or separating source witness is absent; record that absence once in the queue.
- Stop before introducing any duplicate semantic representation or any harness, schema, generator, protocol, registry, dependency, or governance layer without explicit approval.
- Keep sibling repositories read-only and preserve their visible status.
- Never push without an explicit current request.

## Resume procedure

1. Read this file, the applicable [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) clause, and the relevant [`TESTING.md`](TESTING.md) ladder rung.
2. Inspect `git status --short`, recent commits, and the current diff.
3. Reconcile the first queue item against its owner and Git history before writing a red case.
4. Close one capsule or verified no-op, run its proportional gate, update only fact owners, and commit.
