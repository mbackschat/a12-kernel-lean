# Active implementation plan

This file is the volatile continuation checkpoint. Stable purpose and delivery rules belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md); exact clause, proof, and evidence coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); retained observations belong in [`EVIDENCE.md`](EVIDENCE.md); durable representation conclusions belong in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Completed work remains in those owners and Git history, not in this plan.

## Verified baseline

The verified semantic baseline before the current correction was commit `8f0f029`. The current baseline is the introducing commit for the completed checked String presence/requiredness capsule below; its focused elaboration, full build, retained-evidence replay, and trust audit passed. The preceding semantic capsules passed the same proportional gates, and the theory/support/evidence ratios remain within the permanent limits in [`CLAUDE.md`](../CLAUDE.md).

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
11. Retain each missing source's declaration signedness rather than selecting one representative global bit; the later per-declaration extension below closes this resolved boundary.

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

The canonical clauses now state encounter order, per-step precision, unavailable termination, and per-declaration missing directions. [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) records the accepted a12-dmkits reconciliation at revision `20230e403fa085c782534025f890669a975999a8`, while [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) record the narrower admitted Lean boundary and reusable consumer consequence.

The introducing commit passed focused elaboration, `lake build`, `lake test`, `./scripts/check-lean-trust.sh`, `git diff --check`, worktree review, and a local Conventional Commit. It was not pushed.

## Completed semantic correction: empty String input placement

The IF198 handoff exposed a representation error at the existing scalar boundary: Lean normalized a parsed empty String to the same checked cell as an omitted placement. That preserved ordinary empty observations but discarded physical placement before downstream consumers could choose whether it mattered.

The root correction adds an explicit present-empty parser-boundary state. Absence formal-checks to `rawPresent = false`; present-empty and a parsed empty String formal-check to `rawPresent = true, parsed = none`; all observe as ordinary empty in both phases. Generic laws now establish placement preservation, absent/present-empty inequality, equal empty observation, and parsed-empty-String normalization. The compact conformance cases distinguish the tempting `Option Value` collapse without adding another ingestion, document, or protocol layer.

The canonical specification and accepted sync-ledger entry record a12-dmkits revision `f78f4fc864b7be05f94736070cd2da7bf95d04b3`. Whole-`Document` adaptation, group-content derivation, custom-validator invocation, computation-applied copy behavior, and public transport remain explicit later consumers; the checked String presence/requiredness capsule below closes the first downstream consumer. Maintained external controls establish the correction, while this repository retains no portable IF198 observation.

The introducing commit passed focused elaboration, `lake build`, `lake test`, `./scripts/check-lean-trust.sh`, `git diff --check`, worktree review, and a local Conventional Commit. It was not pushed.

## Completed inbound semantic correction: group presence and nested-star tails

The read-only a12-dmkits handback at revision `7f152509eea76822068955055b0d57d8ed930ca2` supplied two dual-kernel/peer corrections. IF193 replaces Boolean validation group presence with the product of formally admitted content, independently propagated error state, and `NONE`/`PARTIAL`/`FULL` relevance; its consumers include scalar and list group predicates, plain multi-group counts, and parent-filled requiredness. IF194 makes a starred aggregate's omitted-tail input hierarchical at every repeatable level reopened from the first star, checked beneath each actual parent; missing finite capacity, an empty selected leaf, or an unbounded reopened level retains fillability, while capacity above the first star stays bound.

The canonical clauses, modelling traps, provenance routes, and implementation boundaries state both corrections. At the handback point the theory neither derived validation group product states nor recursively proved multi-star completeness; the two resolved capsules below now close those internal seams without claiming authored/model/document construction. Because the findings originate in the already committed and reviewed a12-dmkits revision, no outbound sync-ledger entry or second peer acknowledgement is required.

## Completed semantic unit: reopened-star structural completeness

The IF194 risk audit found one bounded seam between first-star scope binding and the existing resolved operand stream. [`StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean) represents only repeatable levels reopened from the first star downward, grouping each actual row beneath its actual parent and retaining a positive, sibling-unique coordinate invariant. It recursively derives the structural tail bit without enumerating a declared Cartesian product, then supplies that bit to `ResolvedValueListSide`; selected-cell emptiness remains in the classified cell stream.

The red shallow implementation checked only the first reopened level. It correctly caught a missing outer row and an unbounded level but falsely closed both a missing middle branch and a missing leaf branch. The corrected recursive mechanism passes outer, middle, leaf, complete, bound-ancestor, and unbounded separators. Trusted laws characterize finite closure, unbounded openness, open-child propagation, coordinate independence of the result, and exact composition with existing missing potential. A Sum case confirms that the derived bit reaches the existing operator-specific direction unchanged.

This closes levels 1–2 only for a caller-supplied reopened tree and resolved cell stream. Authored path checking, first-star discovery, repeatability lookup, scoped `Document` enumeration, tree/cell construction, `Having`, partial relevance, per-source declaration-metadata construction, computation aggregates, protocol exposure, and project-local portable evidence remain open. No path framework, Cartesian enumerator, protocol, evidence mechanism, or dependency was added.

## Completed semantic unit: resolved validation group presence

The IF193 audit found one phase-aware seam after descendant scope and group relevance are resolved. [`GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean) folds already checked descendant cells, an independently supplied instantiated-row-content bit, a structural-error bit, and `NONE`/`PARTIAL`/`FULL` relevance into one admitted-content × error × relevance state. A parsed value remains admitted through `duplicateIndex` marking but not through malformed, constraint, custom, required, or over-repetition rejection; instantiated repeatable rows supply content independently of cells and diagnostics.

The red matrix covered malformed-only, admitted-plus-malformed, duplicate-index admission, created and over-limit rows, partial positive, partial empty, full empty, group-list availability, numeric-count availability, and relative-requiredness. The completed state drives scalar `GroupFilled`/`GroupNotFilled`, all five fixed-list group predicates, plain multi-group `NumberOfFilledGroups`, and the parent-filled requiredness gate. In particular, list predicates put an admitted-but-erroneous group in the filled bucket, while the numeric count becomes unavailable; a shared Boolean count would be unsound.

Trusted laws characterize both scalar firing regions, admitted row and duplicate sources, rejected scalar exclusion, exact list-tally partition, numeric error absorption, and the requiredness bridge. This closes levels 1–2 only for resolved inputs. Authored paths, group-instance and descendant enumeration, `Document` adaptation, `NONE`/`PARTIAL`/`FULL` relevance construction from wildcardable patterns, global fields, checked condition lowering, repeatable list expansion, generated required-rule orchestration, messages, protocol exposure, and project-local portable evidence remain open.

## Completed risk audit: checked resolved-input construction

The construction audit rejected both candidate routes at the present boundary. `FlatModel` owns exact paths and repeatable level identities but no repeatability capacities; `Document` owns instantiated row addresses and raw placements but no group ancestry or declaration policy; flat partial relevance is only `FieldId → Bool` and cannot express wildcardable groups, concrete repetitions, globals, or full coverage across deeper repeatable axes. Neither `ReopenedStarDomain` nor `ResolvedGroupPresenceInput` can therefore be constructed faithfully by one current owner.

Adding those facts now would create the general model/path/relevance layer that the bounded capsule rule excludes. The audit made no code change and rotated to the already source-grounded per-declaration Sum discriminator.

## Completed semantic unit: per-declaration Number Sum missingness

[`NumericAggregate.lean`](../A12Kernel/Semantics/NumericAggregate.lean) now represents every selected Sum cell with its own declaration signedness and retains signedness separately for uninstantiated sources. The encounter-ordered arithmetic scan remains unchanged. After a present total, any missing source permits growth and exactly a missing signed source permits shrinkage; signedness on a present source is irrelevant to that decision. The all-empty identity, first-unavailable termination, and `Having` escalation remain unchanged.

The red matrix separated unsigned-present/signed-missing from signed-present/unsigned-missing for both explicit empty cells and uninstantiated sources. Trusted laws state both per-source branches and prove that the former homogeneous API is exactly the constant-signedness embedding. This closes mixed-declaration resolved evaluation at levels 1–2. Checked authored field-list/group/star lowering, tree/stream construction, actual filtering, partial relevance, computation aggregates, protocol exposure, and project-local portable evidence remain open.

## Completed consumer checkpoint: artifact-only aggregate probe

At revision `6670ce7`, one deliberately cold read-only consumer received only the aggregate clauses, Lean semantics, laws, executable separators, adjacent operator-family definitions, implementation boundary, and consumer guidance. It consulted no kernel, a12-dmkits, web, Git history, prior discussion, or unlisted source and changed no file.

The reader reconstructed the complete admitted `Sum`/`MinValue`/`MaxValue` evaluator without semantic guessing, including order, staged precision, empty and unavailable cells, first cause, all-empty identity, tail, signedness, `Having`, and the distinctions from operand-list extrema and `FirstFilledValue`. It also classified a narrow set of resolved-stream rewrites and caught the non-obvious fact that inserting or deleting numeric zero is not universally safe because it can alter all-empty provenance or introduce another precision-50 step.

The result passes consumer adequacy for the exact resolved homogeneous-signedness validation boundary it received. It correctly refused authored evaluation and source-level refactoring because checked path/star/filter lowering, partial relevance, mixed-declaration missingness, computation, messages, a source transformation relation, and external evidence were outside that artifact set. The later per-declaration capsule widens the resolved evaluator but was not part of this completed probe. [`USE-CASES.md`](USE-CASES.md#completed-probe-record-resolved-number-aggregates) owns the durable reader-facing result; no report artifact, shipment, protocol, runner, qualification campaign, or harness was added.

## Completed risk audit: computation state transition

The transition audit found no faithful bounded common seam. String already has an explicit two-step outcome-to-checked-cell overlay and direct cascade; Number intentionally stops at a cause-free `NumericDependencyObservation`. Turning Number poison into the `CheckedCell` overlay required by the shared scalar context would invent a `FormalCause`, while abstracting both domains together would add the general scheduler/state framework this risk spike was meant to avoid. `Document` also retains raw cells and instantiated rows but no computation ordering, computed-field stripping policy, or typed target overlay.

The existing mechanisms therefore remain separate and no duplicate cascade, generic transition type, or scheduler was added. A future transition unit first needs a source-grounded common poison carrier and at least two completed typed consumers, or checked model facts sufficient to build ordered target overlays.

## Completed semantic unit: fired-only structured rule messages

Checked flat rules now retain a `MessageRenderPlan` instead of pre-rendered text. The reused condition evaluator still runs exactly once; only its fired branch applies provider/default selection, preserves opaque replacement bytes including raw CRLF, renders the plan, and attaches metadata. `notFired` and `unknown` never inspect the plan and are universally independent of every alternative plan. The checked generated literal-Number computation-validation consumer uses the same corrected boundary.

The red change supplied a plan to the existing checked assembler and failed at its pre-rendered-text parameter. The final cases distinguish both silent branches from a fired rule, exact scale-two default display, raw CRLF opacity, and different fired texts. Raw template parsing, token/path legality, actual provider invocation, document display lookup, exact-default construction, repeats, custom-condition integration, and protocol exposure remain outside. No canonical clause changed, so no synchronization-ledger entry was added.

## Completed semantic unit: finite Berlin 2024 calendar-day difference

The temporal risk audit selected one explicit profile instead of a timezone abstraction. `Berlin2024Profile` replaces the old autumn-only namespace and admits fresh labels only on 2024-03-29 through 2024-04-01 plus 2024-10-27. It rejects spring `02:xx` labels, preserves the later-side autumn overlap policy, and exposes consecutive calendar-day stepping only inside the spring slice.

The red matrix first failed because no day-difference module existed. The completed evaluator counts successive stateful landings without passing the later resolved instant. A March 30 `02:30` landing becomes March 31 `01:30`, and the next step retains `01:30`; therefore a `01:45` endpoint counts one despite an elapsed-seconds quotient of zero, while April 1 `02:00` counts two. Ordinary, threshold, reverse-sign, retained-clock, and unsupported cross-slice cases separate the mechanism. Trusted laws establish gap rejection, admitted self-zero, and swap negation with symmetric failure.

This closes levels 1–2 only for fresh resolved labels in the finite spring profile. Mixed Date/DateTime admission, empty/formal operands, polarity/fillability, constructed-Date legacy-calendar identity, other Berlin dates/years, other zones, checked lowering, and protocol exposure remain open. The canonical clause and a12-dmkits reconciliation were already accepted under `SPEC-2026-07-20-08`, so no new outbound ledger entry was created. No calendar framework, timezone database, support mechanism, dependency, or harness was added.

## Completed follow-up audit: repeatable operand-resolution remains blocked at the same owner boundary

The proposed one-operand audit does not escape the earlier checked resolved-input construction blocker. `FlatModel` resolves declarations and repeatable ancestry but carries neither repeatability capacity nor a starred path position. `Document` preserves raw placement and row order but supplies no checked-cell view. `ReopenedStarDomain` deliberately begins after first-star splitting, capacity lookup, and hierarchical row construction, while `ResolvedNumericSumSide` additionally needs per-source signedness for empty and uninstantiated sources.

Implementing the narrower-sounding seam would therefore introduce the same general starred-path/model-capacity/checked-read adapter already rejected by the completed construction audit. No duplicate audit record, partial adapter, or code change was added; the plan rotated.

## Completed semantic unit: checked String presence and absolute requiredness

`FlatField` now admits `FlatStringField`, so the existing phase observation and presence evaluator handle String without a kind-specific branch. Absent, present-empty, and parsed `""` inputs all make `FieldFilled` not fire and `FieldNotFilled` fire with OMISSION; a nonempty admitted String fires VALUE, and malformed input remains UNKNOWN. Checked flat lowering resolves nonrepeatable String declarations into the same typed presence boundary.

Absolute nonrepeatable requiredness reuses that generic generated `FieldNotFilled` stage. A required present-empty String retains `rawPresent = true` when `.required` is attached, proving that evaluation emptiness does not erase physical placement. A universal separator law shows that absent and present-empty checked cells differ while both String presence predicates agree. The specialized generated two-alternative computation-validation consumer keeps its prior Number/Boolean/Confirm-only guard contract through an explicit closed-kind gate; generic presence support does not widen that unrelated capsule accidentally.

This is an internal levels 1–2 downstream closure of accepted IF198. Repeatable/parent-gated requiredness, group-content derivation, generated-computation String guards, `Document` adaptation, protocol exposure, and local portable observations remain open. The canonical clause and accepted reconciliation already own the behavior, so no new sync-ledger entry was added.

## Immediate next step: direct String inequality capsule

Audit the existing direct String equality operand resolver against the canonical `!=` clause. Select the capsule only if the same empty-on-either-side suppression, malformed precedence, nonempty comparison, checked lowering, and row-gate behavior can be expressed by extending the closed equality operator without inventing a general String expression framework.

## Likely next keystone rotation

Reassess the frontier rather than continuing numeric operators by momentum.

The leading candidate is direct String inequality because it shares the completed equality operand-resolution mechanism and has a source-grounded empty-operand discriminator without reopening path or expression infrastructure.

If that family closes, reassess adjacent String functions only by independent discriminator and consumer payoff. Keep the repeatable operand-resolution seam parked until a source-owned model representation supplies star position, capacities, checked row reads, and per-source metadata; do not retry it under another adapter name.

Choose the next unit by:

1. downstream connectivity to named tasks in [`USE-CASES.md`](USE-CASES.md);
2. readiness of a source-grounded separating witness;
3. representation pressure and risk of invalidating later work;
4. availability of a second semantic user before extracting a shared mechanism;
5. ability to close a useful levels 1–2 capsule without new infrastructure.

## Parked boundaries

These are not repository-wide blockers:

- `DifferenceInDays` outside the finite Berlin 2024 spring profile still requires a profile-aware model-zone legacy-calendar step account; the zone-free proleptic `CivilDate` coordinate is not a valid substitute.
- Authored message/whole-rule integration must still parse and check templates and construct display inputs from actual providers, document values, and exact format defaults; untested display routes and project-local portable evidence remain open.
- Validation group presence now has a resolved admitted-content/error/relevance derivation and four consumer projections; checked group-instance enumeration and wildcardable `NONE`/`PARTIAL`/`FULL` relevance construction remain open.
- Authored nested-star aggregate lowering must construct the proved reopened tree and ordered cell stream from checked paths, model repeatabilities, and scoped `Document` rows; resolved aggregate consumers do not perform that lowering themselves.
- Mixed-declaration Sum now retains per-source missing signedness at the resolved boundary; checked authored lowering must still construct that metadata.
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
5. Otherwise perform the computation transition risk audit and select the next keystone capsule using the criteria above.
6. End each capsule with its applicable gates, honest completion/evidence levels, minimal owner-document updates, a clean worktree, and no sibling changes.
