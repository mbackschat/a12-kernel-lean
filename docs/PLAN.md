# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-25:** `lake build` 469 jobs · trust audit **1322 theorem roots; 27338 declarations in 250 modules** · `lake test` 51/51 · `lake exe checkReferenceProcess` 51/51. Re-run the four commands in [`CLAUDE.md`](../CLAUDE.md#building--running) before relying on these changing counts.

- SG1 is closed at one immutable model-certified `CheckedDocument`; processing context remains separate.
- SG2 is active. Canonical topology, complete `Env`, checked addressed reads, hierarchical omitted tails, exact stored payload, filter/relevance provenance, and structural failure already compose across multiple Number, String, Enumeration, aggregate, value-list, temporal, group-presence, and one-level RNU consumers. The finite remaining checklist is in [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- The ordinary repeatable validation loop derives its scope from the checked condition, enumerates actual rows only, reads ancestor/current declarations through the checked document, and emits at exact repeatable error addresses. Current static legality is level-local and preserves `insufficient` for unclassified families.
- Validation-only mixed plain/starred `NoGroupFilled` and `AtLeastOneGroupFilled` are the latest closed SG2 family. Their checked operands and addressed tally exist, but whole-rule bound-prefix execution and its static guard classification are not yet admitted.
- The six coverage dimensions are executable, proof-closed, Kernel-locked, Kernel-calibrated, public, and consumer-qualified. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns their clause-level state; absent `Kernel-locked` rows mean not yet assessed, not no evidence.
- The universal Core IL is closed and archived. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers) owns the live family-data default and the six conditions for reconsidering a checked-plan IR.
- Repeated starred group-list admission is locally source-locked and remains pending peer reconciliation under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands). No other handoff blocks the active capsule.

## Active capsule — bound-prefix starred group lists in ordinary rules

Extend the existing validation-only mixed plain/starred group-list family through the existing ordinary addressed rule loop. Do not add another group evaluator, topology, environment, stream, or message route.

Success requires:

1. Source-ground the level-local rule from `IterationNotValidVisitor`: reached `NoGroupFilled` with an iterating operand is unguarded; `AtLeastOneGroupFilled` is guarded only when every operand references the queried level.
2. Replace the group-list leaf's `unclassified` result with that exact per-level classification while preserving `noReference` outside its derived binding prefix.
3. Admit only the already-checked group-list leaf in `supportsOrdinaryIteration`; reuse `ResolvedGroupListOperands.iterationScope`, `CheckedStarredGroupSource.rowCount`, `AddressedValidationEvaluationContext`, and the existing tally.
4. Separate an all-iterating positive list from a mixed iterating/noniterating positive list, reject a negative list unless another conjunct guards the same level, and execute a legal bound-prefix rule once per actual outer row with exact error addresses and no positional cross-subtree binding.
5. Prove classification/delegation laws, retain structural addressing failure outside UNKNOWN, run a same-context Execute/Transform/Explain assessment, and update only the existing owners.

Excluded from this capsule: partial validation, nonrepeatable terminal groups below a star, computation's ordered poison scan, message projection, protocol work, and any generic IR, schema, generator, or harness.

## Immediate sequence

1. Add the separating conformance cases first and confirm the missing classification/admission fails.
2. Implement the smallest changes in the existing group-list condition and ordinary-iteration owners.
3. Add the payoff-selected laws and inspect the touched group-star family for an `incoherentCore` branch that can be discharged without widening scope.
4. Run the narrow modules, mutation controls, trust audit, and full integration gates; perform the same-context closure assessment and commit.
5. Advance the SG2 checklist to the next ready item only after checking current owners, recent Git history, and cross-project handoffs for overlap.

## Decisions after the next semantic milestone

- Ask for an explicit decision before running the isolated nonrepeatable SG4 dependency-transitive-skip versus reached-read-poison discriminator. It does not need SG2, but it changes the adopted scheduling account and remains a distinct approved spike.
- Select a small proof-bearing Analyze or Transform pilot only after the milestone. It must consume an existing checked representation and define its artifact and checked relation first; do not prepare it with a generator, schema, trace framework, or checked-plan IL.

## Parked boundaries

- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active capsule above, its SG2 checklist item, the linked implementation owner, and the applicable [`TESTING.md`](TESTING.md) rung; inspect status, recent history, and handoffs before writing the red case.
