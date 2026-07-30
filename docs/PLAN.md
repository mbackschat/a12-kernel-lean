# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-07-30:** `lake build` 660 jobs · trust audit **1733 theorem roots; 39846 declarations in 378 modules** · `lake test` 51/51. Re-run the applicable tier commands in [`TESTING.md`](TESTING.md#tier-gates) before relying on these changing counts.

- SG1 is closed at one immutable model-certified `CheckedDocument`; processing context remains separate.
- SG2 is closed. Canonical topology, complete named `Env`, checked addressed reads, hierarchical omitted tails, exact stored payload, filter/relevance provenance, structural failure, and relevance-derived partial group products compose across Number, String, Enumeration, aggregate, value-list, temporal, group-presence, and nested RNU consumers.
- The ordinary repeatable validation loop derives its scope from the checked condition, enumerates actual rows only, reads ancestor/current declarations through the checked document, and emits at exact repeatable error addresses. Current static legality is level-local and preserves `insufficient` for unclassified families.
- Both group-terminal interpretations below stars are closed for full validation. A terminal repeatable group counts structural terminal rows; a nonrepeatable terminal reuses the same checked topology to select complete environments and derives the existing descendant-content/error group product in each. The shared tally, ordinary rule loop, and structural failure channel remain unchanged.
- The six coverage dimensions are executable, proof-closed, Kernel-locked, Kernel-calibrated, public, and consumer-qualified. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns their clause-level state; absent `Kernel-locked` rows mean not yet assessed, not no evidence.
- The universal Core IL is closed and archived. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers) owns the live family-data default and the six conditions for reconsidering a checked-plan IR.
- The SG4 dependency-transitive-skip ambiguity is closed in favor of reached-read poison. The static dependency graph constrains generated call order; it does not pre-propagate invalidity through an unread edge. [`LF77`](LEAN-FINDINGS.md#lf77--a-dependency-graph-can-order-every-computation-without-deciding-which-dependency-failures-propagate) owns the durable mechanism.
- The bounded nonrepeatable SG4 source packet is closed. Code generation topologically orders one generated method per target field; each method owns one flattened first-selected table, and a selected operation ends that target-instance scan even when it stores nothing. [`SPEC-2026-07-26-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-03--same-target-computations-flatten-into-one-first-selected-table) carries the resulting peer correction and selected-empty String separator.
- The first checked SG10 rule-message authoring capsule is closed over nonempty printable-ASCII text, `$$`, `$Field$`, and `$Field.value$` with one bare nonrepeatable field in the condition group. It validates model and condition membership before lowering directly to the existing one-pass post-fire plan; quoted names, wider paths, display-policy invocation, and every repeatable token remain explicit insufficiency. a12-dmkits still needs the isolated literal-dollar correction recorded under SG10, but that does not block local semantics.
- The first proof-bearing internal Analyze pilot is closed over the existing checked flat tree. It detects only the exact root-level same-field presence contradiction in either authored order and proves that every returned witness is never firing; it adds no IR, recursive simplifier, solver, command, protocol, or shipment.
- Repeated starred group-list admission and its zero-row polarity are reconciled under [`SPEC-2026-07-23-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-09--fixed-group-list-predicates-admit-field-and-group-operands). The bound-prefix static rule under [`SPEC-2026-07-26-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-01--starred-group-list-iteration-guards-are-operator--and-operand-sensitive) and nonrepeatable-terminal composition under [`SPEC-2026-07-26-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-02--a-nonrepeatable-group-below-starred-ancestors-retains-group-product-semantics) remain handed off without upstream work at the reviewed checkpoint.

## Active semantic unit

Audit and admit the corresponding field-owned validation-message template form, where source inspection identifies locale-fixed token candidates rather than a rule-relative model path. [`EXP-2026-07-30-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#exp-2026-07-30-01--field-owned-error-text-dollar-decoding-and-fixed-token-staging) now owns the representation-defining observation: whether the field route decodes `$$`, whether English accepts only lowercase `field`/`field.value`, and whether inserted value bytes remain opaque. Reuse the checked raw-template and one-pass rendering owners only where that observation proves the meanings identical.

## Immediate sequence

1. Hand off and consume [`EXP-2026-07-30-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#exp-2026-07-30-01--field-owned-error-text-dollar-decoding-and-fixed-token-staging). Do not write the Lean red case before its exact static spellings and rendered outputs select the contract.
2. Red-first, separate the measured literal-dollar, fixed-name, fixed-value, actual-name rejection, malformed delimiter, and token-looking replacement cases. Keep any unmeasured locale or producer explicit insufficiency.
3. Reuse or minimally parameterize the current checked tokenizer and direct `MessageRenderPlan` lowering only for measured shared behavior. Do not merge rule-relative lookup with fixed-token binding or force field values through the rule path's empty-display default policy.
4. Prove measured output opacity and no semantic back-effect at the field formal-message boundary. Keep unmeasured locale/provider invocation, wider rule paths, repeats/indices/categories/`BaseYear`, computation messages, and a shared message envelope excluded.

## Parked boundaries

- Eager prepass invalidity needs no second snapshot because `CheckedDocument` already owns computation-phase checked cells. Its supplied messages enter the completed SG4 partition directly; no eager-prepass reconstruction or SG10 rendering belongs in that structural boundary.
- Computation scheduling, state transition, and the computation-result pointer partition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); message rendering remains under SG10; future operator-family admission and projections remain under their owning semantic gaps.
- The a12-dmkits rule-template `$$` renderer correction is an isolated upstream implementation/test request against an already-correct canonical rule clause. It does not answer the field-owned question: that distinct source path is blocked on [`EXP-2026-07-30-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#exp-2026-07-30-01--field-owned-error-text-dollar-decoding-and-fixed-token-staging).
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
