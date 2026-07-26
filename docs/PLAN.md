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
- Repeated starred group-list admission remains pending peer reconciliation under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands), and the newly canonized bound-prefix static rule is pending under [`SPEC-2026-07-26-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-01--starred-group-list-iteration-guards-are-operator--and-operand-sensitive).

## Latest semantic milestone

The bound-prefix starred group-list capsule is closed locally. Its new separating cases cover all-iterating positive admission, mixed fixed/star positive rejection, unguarded negative rejection, `And`-guarded negative admission, `Or` non-admission, per-actual-outer-row evaluation, exact error addresses, and structural addressing failure outside semantic UNKNOWN; they reuse the already-closed named-ancestry binding rule. Scope, exact positive/negative guard regions, supported-route, and addressed-delegation laws use the existing checked family owners.

The next local SG2 candidate is [the nonrepeatable group-star terminal family](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), but do not open it until the current decision checkpoint is resolved and its source packet confirms that no existing owner or cross-project handoff already closes the terminal selection.

## Decision checkpoint

- **SG4 discriminator — explicit approval required:** run one bounded nonrepeatable kernel investigation that separates dependency-transitive skip from reached-read poison by making an earlier branch decide before an invalid producer would be read. This is a read-only-plus-witness spike with the existing three-exit rule, not permission to introduce a scheduler, graph, trace model, or SG4 infrastructure. Recommendation: approve it now because SG1 supplies its inputs and the result can change the eventual SG4 representation before more assumptions accumulate.
- **Selected proof-bearing Analyze pilot — design selected, implementation not yet authorized:** detect the exact checked flat shape `FieldFilled(f) And FieldNotFilled(f)` (and the symmetric order) as a dead error condition. The artifact is a small typed contradiction witness over the existing checked condition tree; its checked relation proves that evaluation can never return a fired verdict for any admitted context. The nearest non-laws retain why this is narrow: the analogous `Or` is not a tautology under formal UNKNOWN/nonrelevance, and different fields are not contradictory. The pilot adds no IR, solver, dependency, generator, schema, trace framework, command, or shipment claim. If approved after the SG4 decision, it is the first solver-free rule-authoring lint and uses the current evaluator as its specification.

## Immediate sequence

1. Obtain the user's decision on the SG4 discriminator and on whether to implement the selected Analyze pilot.
2. If the SG4 spike is approved, execute only the bounded source/template/generated-program/probe route needed to distinguish the two accounts and exit as confirmed, refuted, or inconclusive.
3. If the Analyze pilot is approved, implement it as one red/green proof-bearing unit over the existing checked flat condition owner.
4. Resume the next SG2 capsule only after checking current owners, recent Git history, and cross-project handoffs for overlap.

## Parked boundaries

- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the decision checkpoint above and the next SG2 checklist item, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
