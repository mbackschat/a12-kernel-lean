# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-26:** `lake build` 469 jobs · trust audit **1327 theorem roots; 27347 declarations in 250 modules** · `lake test` 51/51 · `lake exe checkReferenceProcess` 51/51. Re-run the four commands in [`CLAUDE.md`](../CLAUDE.md#building--running) before relying on these changing counts.

- SG1 is closed at one immutable model-certified `CheckedDocument`; processing context remains separate.
- SG2 is active. Canonical topology, complete `Env`, checked addressed reads, hierarchical omitted tails, exact stored payload, filter/relevance provenance, and structural failure already compose across multiple Number, String, Enumeration, aggregate, value-list, temporal, group-presence, and one-level RNU consumers. The finite remaining checklist is in [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- The ordinary repeatable validation loop derives its scope from the checked condition, enumerates actual rows only, reads ancestor/current declarations through the checked document, and emits at exact repeatable error addresses. Current static legality is level-local and preserves `insufficient` for unclassified families.
- Bound-prefix mixed plain/starred `NoGroupFilled` and `AtLeastOneGroupFilled` are the latest closed SG2 family. The existing checked operand sum, captured scope, per-level positive/negative classifier, addressed tally, ordinary rule loop, and exact outer error emission compose without another evaluator or iteration carrier.
- The six coverage dimensions are executable, proof-closed, Kernel-locked, Kernel-calibrated, public, and consumer-qualified. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns their clause-level state; absent `Kernel-locked` rows mean not yet assessed, not no evidence.
- The universal Core IL is closed and archived. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers) owns the live family-data default and the six conditions for reconsidering a checked-plan IR.
- The SG4 dependency-transitive-skip ambiguity is closed in favor of reached-read poison. The static dependency graph constrains generated call order; it does not pre-propagate invalidity through an unread edge. [`LF77`](LEAN-FINDINGS.md#lf77--a-dependency-graph-can-order-every-computation-without-deciding-which-dependency-failures-propagate) owns the durable mechanism.
- Repeated starred group-list admission remains pending peer reconciliation under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands), and the newly canonized bound-prefix static rule is pending under [`SPEC-2026-07-26-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-01--starred-group-list-iteration-guards-are-operator--and-operand-sensitive).

## Latest semantic milestone

The bound-prefix starred group-list capsule is closed locally. Its new separating cases cover all-iterating positive admission, mixed fixed/star positive rejection, unguarded negative rejection, `And`-guarded negative admission, `Or` non-admission, per-actual-outer-row evaluation, exact error addresses, and structural addressing failure outside semantic UNKNOWN; they reuse the already-closed named-ancestry binding rule. Scope, exact positive/negative guard regions, supported-route, and addressed-delegation laws use the existing checked family owners.

The SG4 risk discriminator is also closed without opening SG4 infrastructure. Kernel source and generated-program templates show that the dependency graph is consumed for topological ordering only, while invalidity propagates from actual `CalculationCache` reads inside generated alternatives. Native generated `&&`/`||` short-circuiting can therefore hide an invalid producer reference. This agrees with the existing dual-strategy peer differentials and narrows the service Javadoc's “relying directly or indirectly” wording to reached dependency chains.

The next local SG2 candidate remains [the nonrepeatable group-star terminal family](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), but the approved Analyze pilot lands first.

## Active semantic unit

Implement the approved proof-bearing Analyze pilot over the existing checked flat condition tree. It detects only the exact root shapes `FieldFilled(f) And FieldNotFilled(f)` and `FieldNotFilled(f) And FieldFilled(f)`. Its typed witness records the shared field and order; a soundness theorem proves the checked condition never returns a fired verdict in any admitted context. The nearest non-laws retain the boundary: the analogous `Or` is not a tautology under formal UNKNOWN/nonrelevance, and different fields are not contradictory. Add no IR, solver, dependency, generator, schema, trace framework, command, protocol, or shipment claim.

## Immediate sequence

1. Inventory the checked flat condition/evaluator/proof/conformance owners and recent history; reuse them without a second AST or evaluator.
2. Add the exact-shape conformance witness red, then the minimum typed analyzer and checked soundness proof.
3. Lock the symmetric order and the `Or`/different-field non-laws, run the capsule closure assessment and full gates, and commit the coherent unit.
4. Resume the nonrepeatable group-star terminal SG2 capsule only after checking current owners, recent Git history, and cross-project handoffs for overlap.

## Parked boundaries

- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
