# Active implementation plan

This is the minimal continuation checkpoint. Current coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), durable semantic conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), completed work narratives in the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md), and stable workflow rules in [`../CLAUDE.md`](../CLAUDE.md) and [`TESTING.md`](TESTING.md).

## Verified baseline

- Semantic baseline: the versioned Europe/Berlin legacy-timezone profile in this revision, building on `5f11430` (`feat(time): add resolved time extrema`).
- Its focused semantics/proof/conformance builds, full 232-job `lake build`, 51/51 retained-observation replay, and trust audit over 735 theorem roots / 11,955 declarations / 136 logical modules passed.
- Reference semantics remains 0.3.0 with the V2 flat-validation and one-group-correlation suites.
- Internally closed but externally uncalibrated families remain `external evidence pending`; no per-capsule evidence machinery is planned.

## Active unit

Park concrete temporal declaration/path lowering at the heterogeneous model-context boundary. The audit found no existing owner that can store scalar `Value`, `FullDate`, `TimeOfDay`, and `Instant` under one field-ID-indexed context: `FlatFieldDecl`, `RawFlatContext`, `FlatContext`, correlation/iteration contexts, and the reference protocol are scalar-`Value` owners, while the temporal types intentionally live outside that sum. Resume only after a bounded architecture audit chooses between extracting foundational temporal value types into the shared value domain and parameterizing/dependent-indexing the model/context spine; a Date-only context or second temporal declaration tree is forbidden.

## Frontier queue

- **Satisfied — finalized IF202 handoff:** the handoff for a12-dmkits `6039fd3e` was reconciled as a verified no-op after `426cdb6`; the method-entry filter skip, neighboring unfiltered route, codegen research order, and inbound provenance are already owned locally.
- **Satisfied — IF193 group presence:** a12-dmkits `7f152509` matches the existing product state and consumer projections introduced by `d19f77e`; do not add another group-state representation.
- **Satisfied — IF194 nested-star tails:** `7f152509` matches the hierarchical reopened-star mechanism and laws introduced by `d285cb5`; do not add a flat tail flag or parallel aggregate scan.
- **Satisfied — semantic-index presence:** `005efb2` reuses the resolved lookup and direct-field presence projections across both phases.
- **Satisfied — semantic-index field-fill operands:** `acdd384` reuses the resolved lookup plus extensional validation tally and ordered computation-slot owners.
- **Satisfied — guarded-table common precondition:** `9894c86` left-conjoins the resolved common condition into every guarded alternative and carries the exact holding/not-true/poison laws through the resolved String consumer.
- **Satisfied — generated-validation common precondition:** `1fc3050` carries one checked common condition through both phases and keeps validation's guard outside the complete mismatch disjunction.
- **Satisfied — guarded-table breadth:** `e2f0f4a` widens the same checked literal owner to two-or-more alternatives with one declaration-ordered remainder.
- **Satisfied — computed-target guard rejection:** `d085ae2` rejects the target ID in common and every alternative guard, with operation-side checking retained for expression-valued authoring.
- **Satisfied — nonempty literal table:** `3b7fea9` admits an optionally guarded singleton beside the guarded two-or-more table without manufacturing a true condition.
- **Satisfied — checked numeric computation operation:** `6cd756d` resolves and admits the plain nonrepeatable expression before its existing computation evaluator.
- **Satisfied — warning-suppressed numeric no-fit:** `2a77643` adds the explicit bounded-storage target branch while preserving the ordinary fail-closed entry point.
- **Satisfied — checked computation suppression:** `0aeddb1` retains the legal warning flag through admission and routes the evaluated result through the matching target entry point.
- **Satisfied — shared warning gate:** `16ff14b` consolidates the exact suppression primitive after its second completed consumer.
- **Satisfied — resolved Number target constraints:** `8714edb` closes the fit-only integer-digit, zero, rendered-length, and inclusive-range suffix while preserving the no-fit decimal-error boundary.
- **Satisfied — target-policy ownership:** `3d216ff` retains one complete resolved policy on the checked numeric operation, rejects scale/signedness mismatch before evaluation, and removes caller policy choice from evaluation without duplicating constraints in `NumField` or inferring them from erased declaration data.
- **Satisfied — checked direct numeric value functions:** `bf441bd` reuses one authored-shape predicate across validation and computation for direct-field `Round`/`Abs` and direct-field/one-constant `Min`/`Max`; general wrapper traversal remains fail-closed.
- **Satisfied — admitted full-Date month/year shifts:** `e91a2cd` implements post-conversion integer `AddMonths`/`AddYears` on stored/full Dates, retains their clamp-versus-February-end distinction, and reapplies the universal Date floor without claiming constructed-Date legacy behavior.
- **Satisfied — admitted full-Date month/year differences:** `aadcbc3` computes signed completed periods through the shared matching shift convention, proves self-zero and swap-negation, and keeps the February-end year boundary distinct from month counting without claiming reason-bearing or legacy-calendar operands.
- **Satisfied — admitted full-Date day shift:** `b1d3dec` inverts the existing Gregorian day coordinate in bounded work, covers both signs and the value floor, and does not widen into DateTime wall-time or constructed-Date legacy-calendar behavior.
- **Satisfied — resolved full-Date comparisons:** `eaec9e3` closes the six-operator truth family over two admitted values by reusing `FullDate.before`, without claiming literal typing, empty/formal polarity, DateTime instant comparison, or checked rule integration.
- **Satisfied — bounded trust-audit optimization:** canonical local import traversal preserves the exact former logical/conformance/library source closures, the theorem registry is compared in one batch, and all adversarial guards run in one refreshed Lean session instead of one process per fixture; successful output is one inventory line while failures retain their diagnostics.
- **Satisfied — classified full-Date comparison operands:** `ec04faf` retains present full Dates with symmetric missing provenance separately from no value and formal unavailability, delegates truth to the existing six-operator family, and projects only true missing-bearing comparisons to OMISSION.
- **Satisfied — stored/full-Date extrema:** `35f4cb7` gives Date `Min`/`Max` a separate no-value fold, skips empty operands while retaining symmetric missing provenance, propagates formal unavailability, and composes through the existing Date verdict path.
- **Satisfied — resolved DateTime instant comparison:** `c9d904a` compares exact whole-second instant identity/order through all six operators, reuses the shared classified scalar verdict path, and locks the equal-looking Berlin overlap separator without adding wall-label or zone-resolution machinery.
- **Satisfied — resolved DateTime exact-instant extrema:** `53340f5` reuses the shared temporal fold at its second completed consumer, selects exact instants for `Min`/`Max`, retains empty/unavailable/missing behavior, and records the a12-dmkits adapter gap without adding another aggregate scan.
- **Satisfied — resolved Time comparison:** `2f8c08c` compares decoded times by seconds since midnight, shares one operation-neutral enum and classified verdict path across Date/Time/DateTime, and keeps format decoding plus checked lowering outside.
- **Satisfied — resolved Time extrema:** `5f11430` reuses the temporal fold and decoded coordinate, preserves the common empty/formal/missing distinctions, and widens pending `SPEC-2026-07-21-07` plus its handoff instead of creating a duplicate peer request.
- **Satisfied — resolved temporal consumer probe:** an isolated reader at documentation revision `1c4c48a` recovered the complete resolved evaluator, exact separating cases, swapped-comparison law, projection-sensitive transformations, exclusions, and assurance boundary without sibling or kernel research. Execute, Transform, and Explain pass only at that resolved boundary; no shipment or external implementation was started.
- **Satisfied — versioned Berlin legacy-timezone profile:** the current capsule implements the exact 62-entry table plus post-1997 recurrence, proves ascending-candidate smaller-offset selection, covers modern and CEMT gaps/overlaps, deletes the finite fresh-label resolver, and routes the bounded calendar-day consumer through the one general resolver.
- **Satisfied — temporal format-component admission:** direct comparisons use the kernel's coarse year/date-class plus equality-only time-class gate, while extrema require exact component equality after optional Base Year supplementation; one component representation and separating matrix own both rules.
- **Satisfied — typed checked temporal observation:** `CheckedCell α` and `CellObservation α` default to the existing scalar `Value` while sharing placement, staged findings, validation unknown, computation poison, and required-only behavior with resolved temporal value types; no parallel cell hierarchy was added.
- **Satisfied — checked full-Date comparison projection:** typed full-Date validation observations map clean values, emptiness, and formal unavailability into the existing classified operand and six-operator verdict evaluator without parsing or declaration logic.
- **Satisfied — checked Time/DateTime comparison projections:** typed decoded-time and exact-instant observations reuse the same clean/empty/unavailable classifier and their existing six-operator evaluators without adding wall-label or zone machinery.
- **Satisfied — raw typed temporal boundary:** `RawCell α` defaults to scalar `Value`; one admission-parameterized projector preserves placement and rejected causes, scalar checking retains its policy/normalization, and identity admission is available only after typed parsing and declaration checks.
- **Blocked representation boundary — heterogeneous temporal model context:** typed raw/checked observations and all three resolved comparison consumers are ready, but the checked model/path spine stores only scalar `Value`. Do not add per-kind contexts, widen `FieldKind` without a matching value/storage account, or move proof-bearing temporal types into `Value` piecemeal. The next temporal unit requires one bounded ownership/dependency audit across `Core`, `Document`, `FullDate`, `DateTime`, `Cell`, `FlatValidation`, and `Elaboration/Flat` before a red case can state the correct shared representation.
- **Missing fact — temporal computation targets:** Date/DateTime target application needs declaration-owned format/rendering and value-admission policy; do not infer it from exact-instant result semantics.
- **Blocked — checked computation-table integration:** runtime first-match selection alone is insufficient because the mandatory all-alternatives generated rule cannot yet represent checked numeric-expression leaves; share one condition representation before admitting expression-valued tables.
- **Missing approved shared refactor — expression-valued generated validation:** `CheckedResolvedFlatRule` consumes only `FlatCondition`, while checked numeric expressions have a separate evaluator. Integrating them requires one bounded shared-condition refactor across flat rule assembly and numeric comparison; do not add a parallel condition tree.
- **Missing fact — repeatable operand lowering:** needs checked star positions, capacities, row reads, and per-source metadata from one source-owned model representation.
- **Missing fact — aggregate expressions:** needs a shared checked expression-tree extension with more than one real consumer; do not add an aggregate-only comparison wrapper.
- **Missing fact — String targets:** needs declaration-owned length and line-break policy; do not infer unconstrained policy from erased model facts.
- **Missing authorization — flat literal scale and protocol-sensitive seams:** require deliberate protocol versioning or a separate adopted public-boundary change.
- **Forbidden duplicate mechanism:** no copied a12-dmkits harness, second numeric AST or scale gate, second aggregate scan, alternate group-state encoding, or parallel protocol route.

## Parked boundaries

- `DifferenceInDays` beyond the finite Berlin 2024 stepping slice needs a general model-zone legacy-calendar landing account; the now-complete Berlin offset/fresh-label profile and proleptic `CivilDate` are not substitutes.
- Authored message integration still needs checked templates and real display providers.
- Checked group-instance enumeration and wildcardable relevance construction remain outside resolved group-presence projections.
- Public protocol expansion, semantic shipments, candidate qualification, SMT dependencies, and new evidence/process machinery require explicit adoption or approval.
- Batch external calibration by coherent family; do not create one producer request per internal capsule.

## Stop conditions

- Stop a candidate when its required model fact, consumer, or separating source witness is absent; record that absence once in the queue.
- Stop before introducing any duplicate semantic representation or any harness, schema, generator, protocol, registry, dependency, or governance layer without explicit approval.
- Keep sibling repositories read-only and preserve their visible status.
- Never push without an explicit current request.

## Resume procedure

1. Read this file, the applicable [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) clause, and the relevant [`TESTING.md`](TESTING.md) ladder rung.
2. Inspect `git status --short`, recent commits, and the current diff.
3. Reconcile the first queue item against its owner and Git history before writing a red case.
4. Close one capsule or verified no-op, run its proportional gate, update only fact owners, and commit.
