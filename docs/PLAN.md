# Active implementation plan

This file is the volatile continuation checkpoint. Stable purpose and delivery rules belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md); exact clause, proof, and evidence coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); retained observations belong in [`EVIDENCE.md`](EVIDENCE.md); durable representation conclusions belong in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Completed work remains in those owners and Git history, not in this plan.

## Verified baseline

The verified semantic baseline before the current correction was commit `8f0f029`. The current baseline is the introducing commit for the completed empty-String placement correction below; its focused elaboration, full build, retained-evidence replay, and trust audit passed. The preceding resolved Number `Sum` capsule passed the same full gates, and the theory/support/evidence ratios remain within the permanent limits in [`CLAUDE.md`](../CLAUDE.md).

The project currently has:

- Reference semantics 0.3.0 with the current V2 flat-validation and one-group-correlation process suites.
- Compact retained observations for the admitted public validation/correlation slices and String direct-cascade projection. Exact inventory and claim limits are in [`EVIDENCE.md`](EVIDENCE.md).
- Internally closed proof-bearing capsules across flat validation, one-group correlation, selected String computation, numeric arithmetic and target behavior, selected temporal behavior, resolved quantifiers and iteration, enumeration, messages, partial validation, custom callbacks, and other bounded clauses indexed in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).
- A mechanism-first numeric value-function family containing checked root rounding, `Abs`, ordered operand-list `Min`/`Max`, and resolved aggregate `Sum`/`MinValue`/`MaxValue`.
- Successful bounded consumer probes demonstrating that current artifacts can transport selected evaluator and refactoring knowledge while correctly refusing broader shipment claims. Results are in [`USE-CASES.md`](USE-CASES.md).

The evidence and process simplification is complete. Retired capture, packet, qualification, and generator machinery stays retired. Current semantic capsules may close internally at levels 1–2 with `external evidence pending`; external calibration is batched by coherent family.

## Completed semantic unit: resolved Number `Sum`

This capsule implements validation-side resolved Number `Sum` and corrects the existing checked-row fold through the same semantic mechanism.

The source audit found that [`Iteration.NumberFold.sumRows`](../A12Kernel/Semantics/Iteration.lean) had been an exact right-recursive rational fold. Kernel `Sum` instead processes values in encounter order and applies precision-50 `HALF_UP` addition at every step. The capsule replaces that root mechanism; ordinary exact totals had hidden the precision-boundary disagreement.

### Closed behavior

The completed capsule:

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

The initial precision/order witnesses failed against the exact right-recursive checked-row fold before the root correction. The final compact matrix independently distinguishes:

- staged precision-50 addition from one exact total;
- encounter order from right association or reordering;
- full scan from stopping after the first present value;
- all-empty both-directional fillability from operator- or signedness-specific defaults;
- unsigned versus signed missing-tail polarity;
- reached `Having` from an ignored filter marker;
- first unavailable from silently skipped or delayed poison.

Temporary focused mutations confirm the precision and order seams; no mutation framework or retained campaign artifact belongs to this capsule.

### Documentation and completion

The canonical clauses now state encounter order, per-step precision, unavailable termination, and per-declaration missing directions. [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) carries the corresponding pending peer reconciliation, while [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) record the admitted Lean boundary and reusable consumer consequence.

The introducing commit passed focused elaboration, `lake build`, `lake test`, `./scripts/check-lean-trust.sh`, `git diff --check`, worktree review, and a local Conventional Commit. It was not pushed.

## Completed semantic correction: empty String input placement

The IF198 handoff exposed a representation error at the existing scalar boundary: Lean normalized a parsed empty String to the same checked cell as an omitted placement. That preserved ordinary empty observations but discarded physical placement before downstream consumers could choose whether it mattered.

The root correction adds an explicit present-empty parser-boundary state. Absence formal-checks to `rawPresent = false`; present-empty and a parsed empty String formal-check to `rawPresent = true, parsed = none`; all observe as ordinary empty in both phases. Generic laws now establish placement preservation, absent/present-empty inequality, equal empty observation, and parsed-empty-String normalization. The compact conformance cases distinguish the tempting `Option Value` collapse without adding another ingestion, document, or protocol layer.

The canonical specification and accepted sync-ledger entry record a12-dmkits revision `f78f4fc864b7be05f94736070cd2da7bf95d04b3`. Whole-`Document` adaptation, String presence/requiredness, group-content derivation, custom-validator invocation, computation-applied copy behavior, and public transport remain explicit later consumers; maintained external controls establish the correction, while this repository retains no portable IF198 observation.

The introducing commit passed focused elaboration, `lake build`, `lake test`, `./scripts/check-lean-trust.sh`, `git diff --check`, worktree review, and a local Conventional Commit. It was not pushed.

## Completed consumer checkpoint: artifact-only aggregate probe

At revision `6670ce7`, one deliberately cold read-only consumer received only the aggregate clauses, Lean semantics, laws, executable separators, adjacent operator-family definitions, implementation boundary, and consumer guidance. It consulted no kernel, a12-dmkits, web, Git history, prior discussion, or unlisted source and changed no file.

The reader reconstructed the complete admitted `Sum`/`MinValue`/`MaxValue` evaluator without semantic guessing, including order, staged precision, empty and unavailable cells, first cause, all-empty identity, tail, signedness, `Having`, and the distinctions from operand-list extrema and `FirstFilledValue`. It also classified a narrow set of resolved-stream rewrites and caught the non-obvious fact that inserting or deleting numeric zero is not universally safe because it can alter all-empty provenance or introduce another precision-50 step.

The result passes consumer adequacy for the exact resolved homogeneous-signedness validation boundary. It correctly refuses authored evaluation and source-level refactoring because checked path/star/filter lowering, partial relevance, mixed-declaration missingness, computation, messages, a source transformation relation, and external evidence remain open. [`USE-CASES.md`](USE-CASES.md#completed-probe-record-resolved-number-aggregates) owns the durable reader-facing result; no report artifact, shipment, protocol, runner, qualification campaign, or harness was added.

## Immediate next step: repeatable operand-resolution risk audit

Audit the smallest source-grounded seam that connects authored repeatable operands to the existing resolved streams. Compare the canonical clauses, existing checked path/scope representations, current one-group and raw cross-level correlation semantics, and current a12-dmkits knowledge without writing to sibling repositories. Produce one decision table and one separating witness for either complete captured outer scope or per-declaration missing-potential retention. Select a semantic capsule only if it can close levels 1–2 without a new path framework, evidence mechanism, or protocol.

## Likely next keystone rotation

Reassess the frontier rather than continuing numeric operators by momentum.

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
4. If the aggregate consumer probe is not recorded, run it and feed back its findings.
5. Otherwise perform the repeatable operand-resolution risk audit and select the next keystone capsule using the criteria above.
6. End each capsule with its applicable gates, honest completion/evidence levels, minimal owner-document updates, a clean worktree, and no sibling changes.
