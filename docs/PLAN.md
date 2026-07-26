# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-26:** `lake build` 483 jobs · trust audit **1360 theorem roots; 28352 declarations in 257 modules** · `lake test` 51/51. The unchanged public reference process last passed 51/51 at the preceding baseline. Re-run the applicable tier commands in [`TESTING.md`](TESTING.md#tier-gates) before relying on these changing counts.

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

The first exact-text direct-sibling parallel join now has a checked whole-rule consumer for `FieldFilled(left) And FieldFilled(right)`, with either operand as the error field. The checked plan derives both indexed groups from the validated operand declarations, evaluates the existing condition tree once per lexical join key, preserves clean-unmatched nonfiring versus invalid-unmatched UNKNOWN, keeps matched reads physical in an invalid column, and emits only at the exact matched error row. Silent union rows never receive a fabricated address. The generated-preliminary column remains shared with Number semantic index; Number parallel ordering, transparent wrappers, the one-sided repeatable frame, synthetic-pointer messages, and exact Kernel duplicate-winner correspondence remain outside this profile.

## Active semantic unit

Continue [`SG2` semantic-index/parallel construction](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction) with the smallest source-closed topology widening: transparent nonrepeatable path segments between the common parent, keyed group, and positive operand. Reuse `CheckedParallelIndexGroups`, `ResolvedParallelIndexJoin`, `CheckedParallelPresenceRule`, the existing checked model paths, optional side observations, condition tree, and emitter. Do not admit the one-sided repeatable frame, Number ordering, negative operators, partial validation, computation clearing, peer-pointer messages, a general parallel plan, or an externally exact duplicate-winner claim in that capsule. The group-product audit remains separately blocked because the ordinary partial rule context does not carry the relevance-selected preliminary slice.

## Immediate sequence

1. Audit the wrapped and asymmetric-depth maintained parallel cases against `FlatModel` group paths and the generated rule-loop parent-index projection; identify the exact transparent-segment normalization and one deliberately excluded repeatable-frame control.
2. Add red whole-rule cases for symmetric and asymmetric nonrepeatable wrappers, lexical union order, both missing directions, matched reads in an invalid column, exact physical error addressing, and an indexed or repeatable intermediate rejection.
3. Generalize only checked operand-to-keyed-group ownership and environment projection. Keep the current join, positive tree, leaf observation, result, and emitter unchanged; add no topology, document view, path AST, or general parallel evaluator.

## Parked boundaries

- Computation scheduling and state transition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); messages under SG10; Boolean/Confirm configured-token metadata under SG5; future operator-family admission and projections under their owning semantic gaps.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
