# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-26:** `lake build` 477 jobs · trust audit **1350 theorem roots; 27762 declarations in 253 modules** · `lake test` 51/51 · `lake exe checkReferenceProcess` 51/51. Re-run the four commands in [`CLAUDE.md`](../CLAUDE.md#building--running) before relying on these changing counts.

- SG1 is closed at one immutable model-certified `CheckedDocument`; processing context remains separate.
- SG2 is active. Canonical topology, complete `Env`, checked addressed reads, hierarchical omitted tails, exact stored payload, filter/relevance provenance, and structural failure already compose across multiple Number, String, Enumeration, aggregate, value-list, temporal, group-presence, and nested RNU consumers. The finite remaining checklist is in [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- The ordinary repeatable validation loop derives its scope from the checked condition, enumerates actual rows only, reads ancestor/current declarations through the checked document, and emits at exact repeatable error addresses. Current static legality is level-local and preserves `insufficient` for unclassified families.
- Both group-terminal interpretations below stars are closed for full validation. A terminal repeatable group counts structural terminal rows; a nonrepeatable terminal reuses the same checked topology to select complete environments and derives the existing descendant-content/error group product in each. The shared tally, ordinary rule loop, and structural failure channel remain unchanged.
- The six coverage dimensions are executable, proof-closed, Kernel-locked, Kernel-calibrated, public, and consumer-qualified. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns their clause-level state; absent `Kernel-locked` rows mean not yet assessed, not no evidence.
- The universal Core IL is closed and archived. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers) owns the live family-data default and the six conditions for reconsidering a checked-plan IR.
- The SG4 dependency-transitive-skip ambiguity is closed in favor of reached-read poison. The static dependency graph constrains generated call order; it does not pre-propagate invalidity through an unread edge. [`LF77`](LEAN-FINDINGS.md#lf77--a-dependency-graph-can-order-every-computation-without-deciding-which-dependency-failures-propagate) owns the durable mechanism.
- The first proof-bearing internal Analyze pilot is closed over the existing checked flat tree. It detects only the exact root-level same-field presence contradiction in either authored order and proves that every returned witness is never firing; it adds no IR, recursive simplifier, solver, command, protocol, or shipment.
- Repeated starred group-list admission remains pending peer reconciliation under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands), the bound-prefix static rule under [`SPEC-2026-07-26-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-01--starred-group-list-iteration-guards-are-operator--and-operand-sensitive), and the nonrepeatable-terminal composition under [`SPEC-2026-07-26-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-02--a-nonrepeatable-group-below-starred-ancestors-retains-group-product-semantics).

## Latest semantic milestone

Checked ordinary full and partial rules now consume complete nested environments. RNU derives each distinct bound prefix through the existing star path, prepares one branch-independent relation per default or authored-`@From` scope, and supplies only the exact current-row result to the shared condition tree. Cases separate global cross-parent duplicates from per-parent `@From`, equal local coordinates, ancestor-key addressing, missing outer bindings, complete and incomplete composite relevance, and immutable rule-row order. No second cache, topology, document view, condition tree, or address model was added.

## Active semantic unit

Continue [`SG2` semantic-index/parallel construction](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction) from the closed nested RNU route. The group-product audit remains blocked at a precise boundary: `ResolvedGroupPresenceInput` retains NONE/PARTIAL/FULL, but the ordinary partial rule context carries the complete `CheckedDocument`, not the relevance-selected cells, rows, and silent errors owned by `CheckedPartialPreliminary`. Passing full descendants with a partial relevance label would be unsound; do not add a second view or widen the rule context inside a leaf capsule.

## Immediate sequence

1. Inventory the existing semantic-index elaboration, parallel-iteration fixtures, checked-document addressing, and static legality owners before proposing a validation-phase join.
2. Build one source decision table for exact joined environments, missing-side observations, row order, index invalidity, and structural failure; identify which distinctions the existing `Env` and checked cell owners already retain.
3. Write red cases only if the existing boundaries can express the join without a second topology or document model. Stop and report the exact missing shared invariant before adding any parallel framework or cache.

## Parked boundaries

- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
