# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-26:** `lake build` 472 jobs · trust audit **1328 theorem roots; 27426 declarations in 252 modules** · `lake test` 51/51 · `lake exe checkReferenceProcess` 51/51. Re-run the four commands in [`CLAUDE.md`](../CLAUDE.md#building--running) before relying on these changing counts.

- SG1 is closed at one immutable model-certified `CheckedDocument`; processing context remains separate.
- SG2 is active. Canonical topology, complete `Env`, checked addressed reads, hierarchical omitted tails, exact stored payload, filter/relevance provenance, and structural failure already compose across multiple Number, String, Enumeration, aggregate, value-list, temporal, group-presence, and one-level RNU consumers. The finite remaining checklist is in [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- The ordinary repeatable validation loop derives its scope from the checked condition, enumerates actual rows only, reads ancestor/current declarations through the checked document, and emits at exact repeatable error addresses. Current static legality is level-local and preserves `insufficient` for unclassified families.
- Bound-prefix mixed plain/starred `NoGroupFilled` and `AtLeastOneGroupFilled` are the latest closed SG2 family. The existing checked operand sum, captured scope, per-level positive/negative classifier, addressed tally, ordinary rule loop, and exact outer error emission compose without another evaluator or iteration carrier.
- The six coverage dimensions are executable, proof-closed, Kernel-locked, Kernel-calibrated, public, and consumer-qualified. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns their clause-level state; absent `Kernel-locked` rows mean not yet assessed, not no evidence.
- The universal Core IL is closed and archived. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers) owns the live family-data default and the six conditions for reconsidering a checked-plan IR.
- The SG4 dependency-transitive-skip ambiguity is closed in favor of reached-read poison. The static dependency graph constrains generated call order; it does not pre-propagate invalidity through an unread edge. [`LF77`](LEAN-FINDINGS.md#lf77--a-dependency-graph-can-order-every-computation-without-deciding-which-dependency-failures-propagate) owns the durable mechanism.
- The first proof-bearing internal Analyze pilot is closed over the existing checked flat tree. It detects only the exact root-level same-field presence contradiction in either authored order and proves that every returned witness is never firing; it adds no IR, recursive simplifier, solver, command, protocol, or shipment.
- Repeated starred group-list admission remains pending peer reconciliation under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands), and the newly canonized bound-prefix static rule is pending under [`SPEC-2026-07-26-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-01--starred-group-list-iteration-guards-are-operator--and-operand-sensitive).

## Latest semantic milestone

The exact flat presence-contradiction Analyze pilot reuses `CheckedFlatCondition` and its existing evaluator. The analyzer returns an indexed field/order witness carrying an equality proof to the checked core; `FlatPresenceContradictionWitness.neverFires` proves the resulting condition cannot produce either fired polarity for any flat context or relevance predicate. Executable controls retain the nearest false generalizations: the same-field `Or` can be `unknown`, and the different-field conjunction can fire. This is an internal proof-bearing analysis result, not a public analysis surface or preparation for the pending SMT proposal.

## Active semantic unit

Source-audit the [nonrepeatable group-star terminal SG2 family](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction): a nonrepeatable terminal group reached below one or more starred ancestors, including descendant-derived group presence. Determine whether the kernel treats it as instantiated group content, a descendant-derived product, or a distinct terminal selection before changing the existing checked star plan or group product state.

## Immediate sequence

1. Inventory the existing checked star-plan, group-presence product, addressed rule-loop, proof, conformance, and peer-handoff owners plus recent history; block on overlap instead of duplicating them.
2. Build the bounded source packet and separating matrix for the three terminal-selection accounts named by the SG2 entry, preserving complete ancestor environments and structural failure.
3. Only after one account is source-closed, add the smallest red case and implement through the existing topology and group product owners; add no second group traversal or topology.

## Parked boundaries

- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
