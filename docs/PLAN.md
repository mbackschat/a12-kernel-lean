# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-26:** `lake build` 531 jobs · trust audit **1456 theorem roots; 30921 declarations in 293 modules** · `lake test` 51/51. Re-run the applicable tier commands in [`TESTING.md`](TESTING.md#tier-gates) before relying on these changing counts.

- SG1 is closed at one immutable model-certified `CheckedDocument`; processing context remains separate.
- SG2 is closed. Canonical topology, complete named `Env`, checked addressed reads, hierarchical omitted tails, exact stored payload, filter/relevance provenance, structural failure, and relevance-derived partial group products compose across Number, String, Enumeration, aggregate, value-list, temporal, group-presence, and nested RNU consumers.
- The ordinary repeatable validation loop derives its scope from the checked condition, enumerates actual rows only, reads ancestor/current declarations through the checked document, and emits at exact repeatable error addresses. Current static legality is level-local and preserves `insufficient` for unclassified families.
- Both group-terminal interpretations below stars are closed for full validation. A terminal repeatable group counts structural terminal rows; a nonrepeatable terminal reuses the same checked topology to select complete environments and derives the existing descendant-content/error group product in each. The shared tally, ordinary rule loop, and structural failure channel remain unchanged.
- The six coverage dimensions are executable, proof-closed, Kernel-locked, Kernel-calibrated, public, and consumer-qualified. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns their clause-level state; absent `Kernel-locked` rows mean not yet assessed, not no evidence.
- The universal Core IL is closed and archived. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers) owns the live family-data default and the six conditions for reconsidering a checked-plan IR.
- The SG4 dependency-transitive-skip ambiguity is closed in favor of reached-read poison. The static dependency graph constrains generated call order; it does not pre-propagate invalidity through an unread edge. [`LF77`](LEAN-FINDINGS.md#lf77--a-dependency-graph-can-order-every-computation-without-deciding-which-dependency-failures-propagate) owns the durable mechanism.
- The bounded nonrepeatable SG4 source packet is closed. Code generation topologically orders one generated method per target field; each method owns one flattened first-selected table, and a selected operation ends that target-instance scan even when it stores nothing. [`SPEC-2026-07-26-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-03--same-target-computations-flatten-into-one-first-selected-table) carries the resulting peer correction and selected-empty String separator.
- The first proof-bearing internal Analyze pilot is closed over the existing checked flat tree. It detects only the exact root-level same-field presence contradiction in either authored order and proves that every returned witness is never firing; it adds no IR, recursive simplifier, solver, command, protocol, or shipment.
- Repeated starred group-list admission remains pending peer reconciliation under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands), the bound-prefix static rule under [`SPEC-2026-07-26-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-01--starred-group-list-iteration-guards-are-operator--and-operand-sensitive), and the nonrepeatable-terminal composition under [`SPEC-2026-07-26-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-02--a-nonrepeatable-group-below-starred-ancestors-retains-group-product-semantics).

## Latest semantic milestone

The isolated repeatable Number run now admits one optionally guarded resolved Number operation whose field atoms are model-owned Number declarations under the same selected operand indexed group and complete repeatable scope. Distinct fields share one matched operand environment without adding an index column or join; each carrier retains its own field identity, while semantic observation and first-poison order remain with the shared expression evaluator. The checked payload is the existing authored numeric tree, so lowering, wrapper-literal boundaries, authoring restrictions, scale summaries, computation evaluation, target policy, result classification, and exact addressed application remain with their established owners. Plain arithmetic, `Abs`, `Round`, operand-list extrema, and exact-scale warning suppression compose without route-specific evaluators. A clean unmatched join contributes numeric zero for every admitted expression field. Literal-only trees and fields outside the selected group fail checked construction. Guards remain limited to the anchor operand, and invalid index columns still suppress the instance before guard or expression evaluation and use post-loop clearing.

## Active semantic unit

Audit presence guards over another field in the same selected operand group. Determine the exact model-relative admission needed for bare guard `FieldId` leaves and whether the executor can reuse the same carrier map without granting fields from another indexed group.

## Immediate sequence

1. Derive every guard leaf through model lookup and the selected operand group's complete scope; do not accept an uncertified `FieldId`.
2. Preserve the existing kind-neutral computation-presence semantics, including raw String presence, while reusing the selected environment and checked carrier map.
3. Keep fields from another indexed group and multi-computation repeatable overlays excluded until their additional joins, reads, or dependency order are independently source-closed.

## Parked boundaries

- Eager prepass invalidity needs no second snapshot because `CheckedDocument` already owns computation-phase checked cells. Its observable residual pointer partition remains parked until SG10 supplies a common structured computation-message/pointer owner; do not introduce an opaque stand-in.
- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
