# Active implementation plan

This file is the volatile continuation checkpoint. Stable purpose and delivery rules belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md); exact clause, proof, and evidence coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); retained observations belong in [`EVIDENCE.md`](EVIDENCE.md); durable representation conclusions belong in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Completed work remains in those owners and Git history, not in this plan.

## Verified baseline

The semantic baseline is commit `0cd607f`. Its full build, retained-evidence replay, and trust audit passed, and the theory/support/evidence ratios remain within the permanent limits in [`CLAUDE.md`](../CLAUDE.md).

The project currently has:

- Reference semantics 0.3.0 with the current V2 flat-validation and one-group-correlation process suites.
- Compact retained observations for the admitted public validation/correlation slices and String direct-cascade projection. Exact inventory and claim limits are in [`EVIDENCE.md`](EVIDENCE.md).
- Internally closed proof-bearing capsules across flat validation, one-group correlation, selected String computation, numeric arithmetic and target behavior, selected temporal behavior, resolved quantifiers and iteration, enumeration, messages, partial validation, custom callbacks, and other bounded clauses indexed in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).
- A mechanism-first numeric value-function family containing checked root rounding, `Abs`, ordered operand-list `Min`/`Max`, and resolved aggregate `MinValue`/`MaxValue`.
- Successful bounded consumer probes demonstrating that current artifacts can transport selected evaluator and refactoring knowledge while correctly refusing broader shipment claims. Results are in [`USE-CASES.md`](USE-CASES.md).

The evidence and process simplification is complete. Retired capture, packet, qualification, and generator machinery stays retired. Current semantic capsules may close internally at levels 1–2 with `external evidence pending`; external calibration is batched by coherent family.

## Active semantic unit: resolved Number `Sum`

Implement validation-side resolved Number `Sum` and correct the existing shared fold semantics before reuse.

The source audit found that [`Iteration.NumberFold.sumRows`](../A12Kernel/Semantics/Iteration.lean) is currently an exact right-recursive rational fold. Kernel `Sum` instead processes values in encounter order and applies precision-50 `HALF_UP` addition at every step. Exact rational totals can therefore agree on ordinary cases while disagreeing at precision boundaries. This is a semantic-root defect, not a test-only discrepancy.

### Required behavior

The completed capsule must:

1. Consume the existing already-expanded, already-filtered `ResolvedValueListSide .number`; do not add paths, star expansion, or another stream representation.
2. Scan left to right in encounter order.
3. Apply the existing precision-50 numeric addition at every reached present value.
4. Ignore empty cells for the numeric total but continue scanning, so a later unavailable cell still yields UNKNOWN.
5. Preserve the first reached unavailability.
6. Return zero for an all-empty selection.
7. Mark all-empty zero as both-directionally fillable, independently of signedness.
8. Treat an omitted/uninstantiated tail after a present result as grow-only for an unsigned declaration and both-directionally fillable for a signed declaration.
9. Escalate a reached resolved `Having` marker to both-directional fillability.
10. Preserve the existing filter-before-consumer behavior and all current small exact `NumberFold` witnesses.
11. Keep mixed-declaration signedness outside the admitted boundary until missing potential is represented per declaration rather than by one global bit.

### Local consolidation

Aggregate extrema and `Sum` are now two completed semantic users of the same classified-cell scan shape. Extract only that shared ordered scan, with the step function and accumulator supplied by the consumer.

Use it to specialize:

- extrema: optional selected amount plus exact `Min`/`Max` selection;
- `Sum`: zero accumulator plus staged precision-50 addition;
- the existing checked-row `NumberFold` projection where its current input classification agrees exactly.

Do not create a generic aggregate framework. Do not merge prefix-terminating `FirstFilledValue`, operand-list extrema, Date aggregates, computation aggregates, or unlike result domains into this scan.

Move universal scan facts to the shared mechanism where they genuinely agree, then make operator laws short specializations. At minimum retain laws for first unavailability, all-empty completion, fixed completion, tail/signedness fillability, and `Having`. Preserve a checked non-law or separating example showing that exact/right-associated addition is not equivalent to encounter-ordered staged addition.

### Red/green separating matrix

Before changing the fold, add a precision/order witness that fails under exact or right-associated addition. The compact matrix must independently distinguish:

- staged precision-50 addition from one exact total;
- encounter order from right association or reordering;
- full scan from stopping after the first present value;
- all-empty both-directional fillability from operator- or signedness-specific defaults;
- unsigned versus signed missing-tail polarity;
- reached `Having` from an ignored filter marker;
- first unavailable from silently skipped or delayed poison.

Temporary mutations may confirm these seams, but no mutation framework or retained campaign artifact is allowed.

### Documentation and completion

If the source-grounded encounter-order/precision rule is missing or imprecise in canonical prose, correct the owning `spec/` clause and add the corresponding entry to [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) in the same change. Update [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and this checkpoint. Add a durable finding only if the work establishes a reusable non-obvious distinction not already owned elsewhere.

Finish with focused elaboration, `lake build`, `lake test`, `./scripts/check-lean-trust.sh`, `git diff --check`, worktree review, and a local Conventional Commit. Do not push.

## Immediate next step: artifact-only aggregate consumer probe

After `Sum` closes, immediately run one bounded artifact-only consumer-adequacy probe before choosing the next family. This is a read-only knowledge-transport check, not a shipment, external implementation, protocol, qualification campaign, or permanent suite.

Give an isolated reader only the canonical spec clauses, numeric aggregate Lean definitions, proofs, conformance cases, implementation-map boundary, and consumer guidance. Ask it to act as:

1. an independent evaluator implementer; and
2. a rule-refactoring-tool author.

It must reconstruct without kernel or a12-dmkits research:

- the complete `Sum`/`MinValue`/`MaxValue` decision table;
- encounter-order and staged-precision behavior;
- empty, unavailable, tail, signedness, and `Having` treatment;
- the difference between aggregate extrema, operand-list extrema, and `FirstFilledValue`;
- which rewrites preserve full observable semantics and which fail because they reorder, reassociate, seed, terminate early, erase provenance, or collapse UNKNOWN;
- exact exclusions and the evidence status.

The probe succeeds only if it needs no semantic guessing at the admitted resolved boundary. Record its concise result in the existing probe owner only if it adds a durable consumer-facing conclusion. Any ambiguity feeds back into the semantic representation, proof obligations, separating matrix, exclusions, and this plan before another family begins.

## Likely next keystone rotation

After the probe, reassess the frontier rather than continuing numeric operators by momentum.

The leading candidate is the repeatable operand-resolution and addressing seam that connects checked authored stars/scopes to already-resolved operand streams such as `ResolvedValueListSide`. It has high consumer payoff because current aggregate semantics are executable but still begin after expansion, filtering, scope resolution, and declaration-sensitive missingness. A correct seam would serve independent evaluators, import legality, refactoring preservation, and later multi-level correlation.

Select it only if a bounded source-grounded discriminator is ready. Start with the smallest high-risk question—likely multi-level captured outer scope or per-declaration missing-potential retention—rather than a general path framework. If that boundary is not evidence-ready, rotate to the highest-ready keystone among computation scheduling/state transition, the temporal model-zone profile, or checked message integration.

Choose the next unit by:

1. downstream connectivity to named tasks in [`USE-CASES.md`](USE-CASES.md);
2. readiness of a source-grounded separating witness;
3. representation pressure and risk of invalidating later work;
4. availability of a second semantic user before extracting a shared mechanism;
5. ability to close a useful levels 1–2 capsule without new infrastructure.

## Parked boundaries

These are not repository-wide blockers:

- `DifferenceInDays` requires a profile-aware model-zone legacy-calendar step account; the zone-free proleptic `CivilDate` coordinate is not a valid substitute.
- Authored message/whole-rule integration must not hide unresolved provider/default/CRLF distinctions. Correct canonical facts may proceed, but an externally unresolved discriminator remains explicit.
- Mixed-declaration aggregate signedness requires per-declaration missing-potential representation.
- Many internally closed families remain `external evidence pending`; collect them into coherent future calibration batches rather than creating per-capsule capture work.
- Public protocol expansion, semantic shipments, external prototypes, candidate qualification, and SMT dependencies require separate adoption or approval.

## Operating guardrails

- Keep one active semantic capsule or bounded risk spike.
- Use red/green TDD and a compact separating matrix.
- Consolidate only the family being extended. Generalize only after a second completed semantic user demonstrates the same meaning, result domain, and law.
- Treat consumer adequacy as a representation requirement. A consumer must not need renewed kernel archaeology or semantic guessing; fix the semantic root rather than adding adapter compensation.
- Feed every material finding back into definitions, proof obligations, cases, exclusions, and sequencing.
- Maintain the semantic-first effort and infrastructure cadence fixed in [`CLAUDE.md`](../CLAUDE.md).
- Add no harness, generator, schema, protocol, registry, governance mechanism, migration, dependency, or product boundary without first surfacing the concrete repeated need, alternatives, lifecycle cost, and consumer payoff and obtaining explicit approval.
- Keep sibling repositories read-only. Record every behavioral `spec/` change in the sync ledger. Never push without an explicit current request.

## Resume procedure

1. Read [`CLAUDE.md`](../CLAUDE.md), this checkpoint, [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), and [`TESTING.md`](TESTING.md).
2. Inspect `git status --short`, recent commits, and the complete current diff. Do not overwrite concurrent work.
3. If `Sum` is unfinished, resume its red/green checklist above.
4. If `Sum` is complete but the aggregate consumer probe is not, run that probe and feed back its findings.
5. Otherwise select the next keystone capsule using the criteria above.
6. End each capsule with its applicable gates, honest completion/evidence levels, minimal owner-document updates, a clean worktree, and no sibling changes.
