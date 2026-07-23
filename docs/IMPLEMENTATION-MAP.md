# Lean implementation and evidence map

This is the sole detailed coverage index from the project-owned [`spec/`](../spec/) taxonomy to Lean owners, implemented behavior, evidence, and exclusions. Use a12-dmkits' [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) for its peer-project inventory.

The target is kernel **30.8.1**. “Implemented” means executable Lean; “proved internally” means a theorem follows from the chosen definitions. Neither establishes universal kernel correspondence. **External evidence pending** means no retained kernel observation is replayed here. This map states current boundaries and evidence; the open-only implementation and conformance backlog lives in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md).

## Evidence snapshot

- The compact validation record has 49 records for 48 distinct external observations because one directional Number witness is intentionally shared across its public and private halves.
- `lake test` replays the 24 private validation records through typed Lean projections
- `checkReferenceProcess` binds the 25 public records to exact normalized requests and externally supported projected responses.
- These two gates complement each other but are not one 49-case replay.
- Together with the 22 root-String and five direct-cascade private replays, the current `lake test` evidence total is 51.

## Taxonomy by clause

Open only the owning clause and linked cross-clause note. Every clause uses the same compact shape: owners, implemented, evidence, and excluded boundary; live next-work detail is linked to [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) instead of repeated here.

### §1 — truth and verdict algebra

#### Owners

- [`Core.lean`](../A12Kernel/Core.lean)
- [`Proofs/Verdict.lean`](../A12Kernel/Proofs/Verdict.lean)
- [`Proofs/Information.lean`](../A12Kernel/Proofs/Information.lean)

#### Implemented

- Commutativity, associativity, idempotence, identities, absorbers, absorption, distributivity, and strong-Kleene information monotonicity
- checked non-laws retain the exact unknown/polarity limits

#### Evidence

- Canonical §1 sources
- no focused portable observation

#### Excluded boundary and gap links

- **Proved internally; external evidence pending** for the finite `K`/`Verdict` algebras
- no generic negation

### §2 — empty scalar comparisons and row gate

#### Owners

- [`Semantics/NumericComparison.lean`](../A12Kernel/Semantics/NumericComparison.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Proofs/NumericComparison.lean`](../A12Kernel/Proofs/NumericComparison.lean)
- [`Proofs/StringLength.lean`](../A12Kernel/Proofs/StringLength.lean)
- [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean)
- [`Conformance/StringLength.lean`](../A12Kernel/Conformance/StringLength.lean)
- [`Conformance/Elaboration.lean`](../A12Kernel/Conformance/Elaboration.lean)

#### Implemented

- Executable Number/Boolean/Confirm empty laws, all six direct Number comparisons, direct String equality/inequality, all four `Length` ordering operators, directional numeric polarity, row gates, checked surface lowering, and model-derived evaluation
- parsed-empty String placement preservation plus operator-distinction and directional-fillability laws

#### Evidence

- The compact [validation record](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json) binds the eight public empty-logic cases and one public directional witness to exact normalized requests and externally supported responses.
- Its six private operator cases replay unsigned/signed empty Number inequality, filled-zero controls, direct String equality, `Length`, and the empty-row gate
- the directional witness intentionally occurs in both halves.
- Direct Number `<`/`>=` is anchored to pinned kernel source and focused a12-dmkits differentials but has no project-local portable observation.
- Retired 0.2.0 provenance is [archived](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md)

#### Excluded boundary and gap links

- **Implemented internally, partial; direct ordering external evidence pending:** all six nonrepeatable Number comparisons, Boolean/Confirm/String equality/inequality, six-way temporal field-to-field, field-to-typed-Date-literal, field/`Today`, field/`Now`, and field/`BaseYear` comparison in either operand order, plus numeric field/`BaseYear` comparison and Number/Boolean/Confirm/String/Date/Time/DateTime presence, are executable.
- Direct String supports equality/inequality, plus all four String `Length` ordering operators
- its empty observation retains absent versus present-empty placement at the checked-cell boundary.
- String presence and absolute nonrepeatable requiredness reuse the generic presence/required staging; the remaining String family is indexed by [`SG7`](SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion).
- This is a consuming-clause baseline, not a kind-wide empty law
- Finding: [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function).
- Finding: [`LF10`](LEAN-FINDINGS.md#lf10--numeric-polarity-needs-directional-fillability-not-a-given-bit).
- Finding: [`LF24`](LEAN-FINDINGS.md#lf24--direct-number-ordering-uses-the-same-directional-fixed-right-comparison).

### §3 — formal checking and phase observation

#### Owners

- [`Semantics/Observation.lean`](../A12Kernel/Semantics/Observation.lean)
- [`Semantics/StringComputation.lean`](../A12Kernel/Semantics/StringComputation.lean)
- [`Proofs/Observation.lean`](../A12Kernel/Proofs/Observation.lean)
- [`Proofs/StringIngestion.lean`](../A12Kernel/Proofs/StringIngestion.lean)
- [`Proofs/StringComputation.lean`](../A12Kernel/Proofs/StringComputation.lean)
- [`Conformance/Observation.lean`](../A12Kernel/Conformance/Observation.lean)
- [`Conformance/StringIngestion.lean`](../A12Kernel/Conformance/StringIngestion.lean)
- [`Conformance/StringComputation.lean`](../A12Kernel/Conformance/StringComputation.lean)

#### Implemented

- `CheckedCell α` and `CellObservation α` default to the scalar `Value` but retain any resolved semantic value type through the same placement, finding, and phase boundary. `CheckedCell.WellFormed`, preservation under staged findings, validation-unknown/computation-poison phase laws, and the required-only exception are generic in that value type.
- `RawCell α` shares that default. `checkRawCellWith` projects placement and rejected causes once through a caller-owned admission function; scalar `formalCheck` retains kind checking and String normalization, while `checkAdmittedRawCell` and `observeAdmittedRawCell` carry only already-decoded, declaration-admitted typed values. Generic laws preserve well-formedness, exact parsed values, and rejected causes in both phases; a full-Date case reaches the existing comparison evaluator through this complete typed boundary.
- `RawCell.presentEmpty` and a parsed empty String retain `rawPresent = true` with no parsed value or finding
- generic laws distinguish that checked state from absence while proving that both phases observe it as empty.
- Nonempty parsed String ingestion performs exactly one non-overlapping CRLF-to-LF pass before caching the evaluated value
- proofs connect the cached result to both phases, direct comparison, UTF-16 `Length`, and computation reads, while a checked counterexample refutes global idempotence.
- The separate reduced String target pass classifies an admitted nonempty root write as accepted or payloadful `ERRORED`, proves no-value and poison bypass for every policy, applies declaration-owned line-break permission, and preserves the exact attempt while measuring permitted CRLF through the normalized view.

#### Evidence

- Retained malformed comparison and branch-combination cases check observable authored-message suppression/firing
- the external output cannot distinguish internal `unknown` from `notFired`.
- The nine-case [compact root-String record](../evidence/kernel-30.8.1/captures/string-computation-v1/semantic-observations.json) separately exposes accepted and errored rich computation results, including attempted value and `stringZuKurz`/`stringZuLang` cause.
- Accepted [`SPEC-2026-07-21-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-03--empty-string-ingestion-preserves-present-empty-placement) links the a12-dmkits IF198 tests for present-empty String ingestion, presence, and requiredness across both kernel strategies and JVM/Node.
- this repository retains no matching portable observation.
- No retained portable observation yet exercises CRLF/LF/lone-CR ingestion
- Typed-cell generalization is an internal representation law with no new kernel-correspondence claim; concrete Date/Time/DateTime raw classification remains pending.
- Typed raw-cell projection likewise begins after parsing and declaration admission; it adds no evidence or claim about concrete temporal text.
- Temporal declaration admission retains the declared kind and component set, accepts only a matching closed temporal payload, and projects kind mismatch through the existing malformed/unknown path. The payload retains exact instant identity, decoded components, and date calendar provenance, but this boundary still starts after parsing, declared-format admission, and source-specific consistency checks.
- Checked temporal field comparison resolves both declarations, applies the Base-Year-aware direct-format gate, checks both cells through their own policies, and compares their admitted exact instants through the shared runtime evaluator. Multi-field relevance and model admission quantify over every read instead of retaining the former single-field shortcut.
- The same checked route admits an already-classified and decoded Date literal with its own component set and exact instant. Omitted-year shape requires Base Year, field and literal reuse one `FlatTemporalOperand`, literal values are fixed, and low-level comparison admission requires at least one field so constant/constant authoring cannot enter through the core.
- `Now` is a third operand of that same core, reads exact `World.now` only at evaluation, and is admitted in either authored position only when the opposite format carries time and satisfies ordinary DateTime compatibility. Checked immediate and assembled whole-rule consumers require an explicit world; partial agreement includes the world, so changing the clock cannot be hidden behind field-only agreement.
- `Today` carries the checked model's exact zone id through that operand core and resolves model-zone midnight from the injected clock through `World`'s explicit capability. Date equality and ordering plus DateTime ordering follow the ordinary date-shaped format gate; DateTime equality and Time comparison remain rejected. Unsupported concrete zones fail closed, while a consumer-supplied oracle can cover the wider kernel-legal zone domain without extending the AST.
- `BaseYear` is checked as model configuration, not a clock read. Its direct Number role lowers to the fixed declared year under the shared exact-scale gate; its temporal role resolves model-zone January 1 through the same operand core and rejects Time before year supplementation. The world capability now groups `Today` and complete local-label resolution, and partial-context agreement is proved once per temporal operand rather than by enumerating every operand pair.

#### Excluded boundary and gap links

- **Implemented internally, partial; ingestion external evidence pending:** the reduced boundary distinguishes absent from present-empty before projecting either to the empty phase observation and owns evaluated-String CRLF normalization after scalar text decoding.
- General `Document → RawCell`, placement/group-content, and validator construction obligations are indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction) and [`SG7`](SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion).
- raw storage itself remains outside this reduced account.
- The internal unknown/poison account still relies on source treatment and internal laws.
- Computed ordinary String target checking reuses the declaration-owned line-break/min/max policy, including combined/zero bounds and exact attempted-payload retention
- no-value/poison bypass, target line-break permission, and ingestion normalization are not externally exercised.
- The remaining checked-input and transition obligations are indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction) and [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).

### §4 — required property

#### Owners

- [`Semantics/Required.lean`](../A12Kernel/Semantics/Required.lean)
- [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean)
- [`Proofs/Required.lean`](../A12Kernel/Proofs/Required.lean)
- [`Proofs/GroupPresence.lean`](../A12Kernel/Proofs/GroupPresence.lean)
- [`Conformance/Required.lean`](../A12Kernel/Conformance/Required.lean)
- [`Conformance/GroupPresence.lean`](../A12Kernel/Conformance/GroupPresence.lean)

#### Implemented

- Independently stated source outcome versus generated-rule evaluation
- base-before-annotation ordering
- computation-observation preservation
- Number/Boolean/Confirm/String targets share the same presence rule; a required present-empty String retains physical placement when the finding is attached.
- parent-filled requiredness consumes the resolved group's admitted-content × error × relevance state and requires positive admitted content.

#### Evidence

- The private compact validation projection replays empty, filled, and malformed absolute/non-repeatable Number cases and retains the empty case's `mandatoryField` code and pointer
- [`RequirednessDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/RequirednessDiffTest.kt) remains broader provenance.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` adds dual-kernel/peer controls for IF193's admitted-content parent gate, but this repository retains no matching portable observation

#### Excluded boundary and gap links

- **Implemented internally, partial; focused external observations replayed:** absolute requiredness for nonrepeatable Number/Boolean/Confirm/String fields.
- The parent gate is implemented over an already-resolved group state; general group/document construction and repeatable required-rule orchestration are indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction) and [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).

### §5 — numbers and decimals

#### Owners

- [`Semantics/String.lean`](../A12Kernel/Semantics/String.lean)
- [`Semantics/NumericRounding.lean`](../A12Kernel/Semantics/NumericRounding.lean)
- [`Semantics/NumericArithmetic.lean`](../A12Kernel/Semantics/NumericArithmetic.lean)
- [`Semantics/NumericFillability.lean`](../A12Kernel/Semantics/NumericFillability.lean)
- [`Semantics/NumericComparison.lean`](../A12Kernel/Semantics/NumericComparison.lean)
- [`Semantics/NumericTolerance.lean`](../A12Kernel/Semantics/NumericTolerance.lean)
- [`Semantics/NumericComputationResult.lean`](../A12Kernel/Semantics/NumericComputationResult.lean)
- [`Semantics/NumericStoredNumber.lean`](../A12Kernel/Semantics/NumericStoredNumber.lean)
- [`Semantics/NumericTarget.lean`](../A12Kernel/Semantics/NumericTarget.lean)
- [`Semantics/NumericApplication.lean`](../A12Kernel/Semantics/NumericApplication.lean)
- [`Semantics/NumericDependency.lean`](../A12Kernel/Semantics/NumericDependency.lean)
- [`Semantics/Condition.lean`](../A12Kernel/Semantics/Condition.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Elaboration/NumericScale.lean`](../A12Kernel/Elaboration/NumericScale.lean)
- [`Elaboration/NumericExpression.lean`](../A12Kernel/Elaboration/NumericExpression.lean)
- [`Elaboration/NumericSource.lean`](../A12Kernel/Elaboration/NumericSource.lean)
- [`Elaboration/NumericValidation.lean`](../A12Kernel/Elaboration/NumericValidation.lean)
- [`Elaboration/ValidationCondition.lean`](../A12Kernel/Elaboration/ValidationCondition.lean)
- [`Elaboration/NumericComputation.lean`](../A12Kernel/Elaboration/NumericComputation.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Elaboration/SingleGroup.lean`](../A12Kernel/Elaboration/SingleGroup.lean)
- [`Elaboration/NumericStar.lean`](../A12Kernel/Elaboration/NumericStar.lean)
- [`Elaboration/NumericAggregate.lean`](../A12Kernel/Elaboration/NumericAggregate.lean)
- [`Elaboration/FirstFilledValue.lean`](../A12Kernel/Elaboration/FirstFilledValue.lean)
- [`Proofs/NumericScale.lean`](../A12Kernel/Proofs/NumericScale.lean)
- [`Proofs/NumericExpression.lean`](../A12Kernel/Proofs/NumericExpression.lean)
- [`Proofs/NumericValidation.lean`](../A12Kernel/Proofs/NumericValidation.lean)
- [`Proofs/ValidationCondition.lean`](../A12Kernel/Proofs/ValidationCondition.lean)
- [`Proofs/NumericComputation.lean`](../A12Kernel/Proofs/NumericComputation.lean)
- [`Proofs/NumericStoredNumber.lean`](../A12Kernel/Proofs/NumericStoredNumber.lean)
- [`Proofs/NumericTarget.lean`](../A12Kernel/Proofs/NumericTarget.lean)
- [`Proofs/NumericApplication.lean`](../A12Kernel/Proofs/NumericApplication.lean)
- [`Proofs/NumericDependency.lean`](../A12Kernel/Proofs/NumericDependency.lean)
- [`Proofs/NumericRounding.lean`](../A12Kernel/Proofs/NumericRounding.lean)
- [`Proofs/NumericArithmetic.lean`](../A12Kernel/Proofs/NumericArithmetic.lean)
- [`Proofs/NumericFillability.lean`](../A12Kernel/Proofs/NumericFillability.lean)
- [`Proofs/NumericComparison.lean`](../A12Kernel/Proofs/NumericComparison.lean)
- [`Proofs/NumericTolerance.lean`](../A12Kernel/Proofs/NumericTolerance.lean)
- [`Proofs/SingleGroupElaboration.lean`](../A12Kernel/Proofs/SingleGroupElaboration.lean)
- [`Proofs/NumericStarElaboration.lean`](../A12Kernel/Proofs/NumericStarElaboration.lean)
- [`Proofs/NumericAggregateElaboration.lean`](../A12Kernel/Proofs/NumericAggregateElaboration.lean)
- [`Proofs/FirstFilledValue.lean`](../A12Kernel/Proofs/FirstFilledValue.lean)
- [`Conformance/NumericScale.lean`](../A12Kernel/Conformance/NumericScale.lean)
- [`Conformance/NumericExpression.lean`](../A12Kernel/Conformance/NumericExpression.lean)
- [`Conformance/NumericValidation.lean`](../A12Kernel/Conformance/NumericValidation.lean)
- [`Conformance/ValidationCondition.lean`](../A12Kernel/Conformance/ValidationCondition.lean)
- [`Conformance/NumericComputation.lean`](../A12Kernel/Conformance/NumericComputation.lean)
- [`Conformance/NumericStoredNumber.lean`](../A12Kernel/Conformance/NumericStoredNumber.lean)
- [`Conformance/NumericTarget.lean`](../A12Kernel/Conformance/NumericTarget.lean)
- [`Conformance/NumericApplication.lean`](../A12Kernel/Conformance/NumericApplication.lean)
- [`Conformance/NumericDependency.lean`](../A12Kernel/Conformance/NumericDependency.lean)
- [`Conformance/NumericRounding.lean`](../A12Kernel/Conformance/NumericRounding.lean)
- [`Conformance/NumericArithmetic.lean`](../A12Kernel/Conformance/NumericArithmetic.lean)
- [`Conformance/NumericFillability.lean`](../A12Kernel/Conformance/NumericFillability.lean)
- [`Conformance/NumericTolerance.lean`](../A12Kernel/Conformance/NumericTolerance.lean)
- [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean)
- [`Conformance/Elaboration.lean`](../A12Kernel/Conformance/Elaboration.lean)
- [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean)
- [`Conformance/NumericAggregateElaboration.lean`](../A12Kernel/Conformance/NumericAggregateElaboration.lean)

#### Implemented

- Signed exact-or-unknown scale, constant expandability, and one shared explicit-suppression gate for the supported exact-scale warning
- authored literals/grouping
- plain authoring-region checks plus recursively staged numeric value functions at ordinary arithmetic operand positions, with immediate/grouped literal rejection at every rounding/`Abs` boundary, direct/grouped numeric-`BaseYear` admission, and list-preserving expression-valued numeric operand-list `Min`/`Max` whose nested calls retain independent immediate/grouped-literal budgets
- one order-sensitive division-lowering pass
- precision-50 `+`/`−`/`×`/`÷`, staged power, rounding, absolute value, full-precision ordered extrema, arithmetic domain failure, and directional fillability including the conservative power and Min/Max tie tables
- independent scale-19 normalization
- a checked closed validation dispatch over all six direct ordinary comparison operators and four fixed tolerance ranges, with numeric `BaseYear`, its direct/range-selected date-component extractions, admitted Date/Time/DateTime field components, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, direct Number field-list aggregates, and ordinary nonrepeatable `RangeAsNumber` supported as shared sources, including those sources beneath unary wrappers inside larger arithmetic
- one checked nonrepeatable computation-operation consumer with model-resolved target, the same shared sources and complete numeric-operation tree, recursively staged rounding/`Abs`, expression-valued and nested per-call `Min`/`Max`, default-unsuppressed result-scale admission, explicit warning bypass, nested target-reference rejection, distinct numeric value/domain-failure/inherited-poison evaluation, one-time complete target-policy attachment, and retained proof-coherent target dispatch
- separately proved ordinary and significant-digit-bounded stored-decimal conversions
- and one explicit two-branch target consumer with target classification, change-only delta, exact one-address final application, and cause-free dependency observation.
- Checked validation resolves two same-group expressions over Number fields, direct Number field-list aggregates, numeric `BaseYear`, direct numeric component extraction from direct or range-selected Base-Year date sources, direct Date/DateTime or Time/DateTime field-component sources, and Date-only month/year differences over field or Base-Year operands, lowers each once, and gates empty rows before reads. At least one actual field remains mandatory, so every source-only or literal-only condition retains the constant-expression rejection.
- Numeric comparison certificates carry an explicit `sameGroup | modelWideNonrepeatable` operand scope. Ordinary surface rules always select `sameGroup`; generated computation validation selects the wider policy only after operation elaboration has already certified nonrepeatability, target exclusion, expression shape, authoring, and scale. Both policies retain one comparison AST, evaluator, relevance/reference traversal, and checked mixed-tree route.
- One generic `ConditionTree` now owns connective shape, Boolean empty-row eligibility, field-reference traversal support, and verdict-aware short-circuit evaluation. `ValidationCondition` embeds the existing flat tree without a nested condition representation and admits resolved numeric comparisons as sibling leaves, requiring every numeric field atom to be relevant before a reached leaf evaluates. Preservation laws show that flat verdicts and references are unchanged; mixed cases lock firing, short-circuit, reached nonrelevance, and cross-family reference discovery.
- Every checked flat condition now retains the exact declaring row group supplied to surface elaboration. Semantic generated-computation desugaring obtains the same certificate from the resolved target declaration, preventing later mixed assembly from inventing or losing the rule-instance group.
- `CheckedValidationCondition` accepts only already-checked flat or numeric inputs, rechecks their flattened shared core against the same model and exact row group, and rejects mixed composition across different groups before recombination. Its coherence law exposes the retained model/core certificate; executable cases lock successful two-family composition and the mismatch diagnostic.
- `ResolvedRule` and `CheckedResolvedRule` parameterize the existing whole-rule metadata and condition certificate. Flat and mixed checked rules therefore reuse one error-field lookup/nonrepeatable/reference gate, one post-verdict message emitter, one outcome type, and the same model-derived context; mixed assembly can discover an error field referenced only inside a numeric-expression leaf. Generic and specialized laws recover the exact underlying verdict and preserve fired-message metadata.
- Admitted expressions form one complete numeric-operation tree including power, direct aggregates, rounding, `Abs`, and numeric operand-list `Min`/`Max`. Each extremum call preserves its source boundary, accepts complete numeric operations as immediate operands, checks at most one immediate or grouped literal independently of nested calls, composes inside surrounding arithmetic, and lowers to the same evaluator without flattening. Direct/grouped numeric `BaseYear` and every separately closed Number source are admitted; an immediate/grouped literal remains illegal only at each rounding/`Abs` boundary.
- The runtime preserves formal invalidity, domain failure, values, and two-sided fillability. [`LF58`](LEAN-FINDINGS.md#lf58--numeric-operand-list-extrema-combine-exact-selection-with-directional-fillability) owns the extremum constant, selection, scale, and polarity details.
- `RangeAsNumber` reuses the checked normalized UTF-16 range primitive and one shared authored-interval predicate. It accepts only a complete nonempty ASCII digit slice, maps missing, overshot, non-digit, signed, fractional, and unrepresentable half-surrogate selections to numeric zero, preserves formal causes, fixes its scale at 0, and distinguishes missing-source grow-only zero from every filled-source fixed zero. Direct rounding preserves that fillability and assigns its authored result scale; direct `Abs` is value-identical because the source is nonnegative and leaves missing zero grow-only. Computation erases only validation fillability and reuses ordinary wrappers, arithmetic, generated mismatch validation, and target checking.
- `FieldValueAsNumber` reuses the common checked String/Enumeration text operand. The String route requires an evaluated ordinary declaration with exact retained `[0-9]+` pattern source and finite maximum length at most 15, enforces that pattern through declaration-owned ingestion, and fixes scale 0. The Enumeration route certifies every selected stored/category token through one Java-21 UTF-16 `Character.isDigit(char)` decimal parser, enforces the 15-digit budget, and derives the maximum fractional scale. Runtime projects or reads each exact token once, parses an exact rational, maps missing to both-directionally fillable zero in validation and plain zero in computation, and preserves formal cause as unknown/poison. The same checked atom participates in arithmetic, scale gates, model-wide generated mismatch validation, Number target checking, and source-confirmed direct rounding/`Abs`. Rounding replaces static scale and preserves fillability; `Abs` preserves scale and applies the existing sign-sensitive fillability transformation, so missing zero becomes grow-only magnitude. Generated validation consumes the nested checked tree without rebuilding either layer.
- The explicit warning flag bypasses only equality/inequality scale admission and is runtime-irrelevant.
- Numeric and date-component `BaseYear` sources retain a non-expandable scale-0 summary and fixed runtime fillability. The latter selects direct January 1 or a range endpoint before applying Day/Month/Quarter/Year extraction. Both participate in the existing arithmetic, tolerance, and value-function evaluator. Direct/grouped numeric `BaseYear` is admitted because it is a number-like reference operation rather than literal syntax, including as an expression-valued `Min`/`Max` operand.
- Computation reads empty Number, temporal-component, or date-difference sources as zero, resolves every Base-Year numeric source to its fixed context-free amount, preflights declarations before data, preserves the exact formal cause of an unavailable temporal field, preserves domain failure through legal wrappers, and keeps left-to-right poison order. Date difference rejects a present legacy-hybrid field payload before applying the decoded-parts core, while formal invalidity and empty substitution retain their earlier precedence. Valid power uses the staged evaluator; runtime-invalid integral power reaches the shared target-invalidating domain failure. The retained warning flag bypasses only result-scale admission and selects the corresponding target branch after evaluation.
- Ordinary stored conversion universally preserves the scale-19 `HALF_UP` amount while retaining `{unscaled, scale}` form. Bounded conversion consumes that pre-rounded canonical amount, preserves it within budget, and otherwise applies the 16-significant-digit scale formula.
- After assignment-scale admission, the ordinary target entry point pads minimum fractional digits and applies the reachable basic Number checks in source order: total digits, signedness, effective integer digits, zero, rendered minimum/maximum length, and inclusive numeric bounds. Canonical rendering makes leading-zero failure unreachable. The explicit warning-suppressed entry point leaves fitting values unchanged, bounds no-fit attempts, applies only the shared total-digit/signedness prefix before the inevitable decimal mismatch, and rejects every no-fit result.
- Exact application preserves absent versus present-empty placement, yields accepted coefficient plus scale exactly, and makes the loss of cause/delta provenance explicit.
- Dependency observation retains clean empty, exact accepted stored form, and poison even when application and delta agree.
- Laws and executable separators cover the admitted summaries, authoring, lowering, arithmetic, extrema, validation, tolerance, expression-result, stored-form, target, delta, application, dependency, read-order, and fail-closed boundaries
- [`LF57`](LEAN-FINDINGS.md#lf57--numeric-absolute-value-changes-directional-provenance-at-zero) owns the sign-sensitive `Abs` account and [`LF58`](LEAN-FINDINGS.md#lf58--numeric-operand-list-extrema-combine-exact-selection-with-directional-fillability) owns numeric Min/Max

#### Evidence

- The compact validation record externally separates ordinary empty numeric polarity only.
- Pinned parser/checker, transformer, code-generation, and runtime source establish the current clauses
- a12-dmkits differentials triangulate staged power/fillability, `Abs`, Min/Max domain propagation, target fit/rejection, delta granularity, exact application, and numeric-`BaseYear` tolerance admission and fixed-band evaluation. Accepted [`SPEC-2026-07-22-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-03--numeric-baseyear-remains-number-like-inside-computation-arithmetic) records revision `9c8da06e`, whose maintained tri-engine computation cases cover direct `BaseYear`, `BaseYear + 1`, and field-plus-`BaseYear`; this repository retains no portable local observation for those computations. Base-Year range-component evaluation is separately pending the recorded peer root correction; kernel checker/code-generation source establishes its fixed unsigned scale-0 result and endpoint selection.
- Accepted [`SPEC-2026-07-21-05`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-05--runtime-invalid-integral-power-poisons-a-number-computation-target) records a12-dmkits revision `43824168`: both runtime-invalid integral regions now reuse the division-domain target/dependency mechanism, with wrapper, quiet-comparison, and valid-boundary controls.
- a12-dmkits `RangeCoercionDiffTest` at originating revision `0f2a5687822797ed7b4f897b0320793ae22eb7b6` supplies maintained dual-kernel-route ASCII selection, digits-only conversion, and fallback-zero evidence; revision `f9e591a54aa4c319baa42dfb76610d7571be5ecc` plus `FunctionFillPolarityDiffTest` supplies the grow-only missing-source account. CRLF-before-range and the Lean half-surrogate representation boundary remain internally locked and externally pending.
- a12-dmkits `FieldValueCoercionDiffTest` retains dual-kernel-route evidence for direct numeric-Enumeration conversion. Accepted [`SPEC-2026-07-22-13`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-13--fieldvalueasnumber-checks-the-complete-selected-source-domain) and reviewed revision `27afb555` add selected-category, lexical rejection, digit-budget, derived-scale, symmetric missing-polarity, String-contract, and non-ASCII BMP host-decimal-digit evidence. Lean now implements that complete nonrepeatable source contract; pending [`SPEC-2026-07-23-07`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-07--numeric-enumeration-conversion-uses-the-host-utf-16-digit-class) records the source-discovered supplementary-plane rejection, while project-local retained correspondence remains pending under SG12.
- No retained project-local observation covers checked numeric expressions, power fillability, value functions, suppression, tolerance, mixed domain/poison order, or target/application/dependency behavior.
- Mixed formal-invalid/domain-failure validation precedence is an explicit Lean refinement
- mixed computation order and division/power target invalidity are source-grounded but portable evidence pending.
- Kernel `CheckDatumExtractOpImpl` plus `DateUtils.typeToComponent` establish that direct component extraction rejects date literals, requires the matching declared component, supplements only Date Year from configured Base Year, and applies partial-known Date restrictions before that supplementation. `CheckRundenOperOpImpl`, `CheckFeldOperOpImpl`, and `CheckOpUtils.isConstant`/`isOpLikeANumber` establish direct rounding/`Abs` admission for the resulting scale-0 operations and direct numeric `BaseYear`, while rejecting only immediate or bracketed numeric literals. Reviewed a12-dmkits IF95 at revision `2abe3ced` and its maintained direct Date/Time extraction differentials triangulate the field-kind and empty-value boundary. Accepted [`SPEC-2026-07-22-04`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-04--quarter-extraction-is-the-fourth-direct-date-component-projection) records the canonical four-component family and explicit constructed-Date Quarter zero/UNKNOWN controls at revision `9c8da06e`; accepted [`SPEC-2026-07-23-04`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-04--direct-numeric-wrappers-admit-temporal-derived-number-sources) and a12-dmkits revision `27afb555aae29d3acd4ed04e3aea4772ae85505a` lock the wrapper cross-product and direct Base-Year correction.
- Kernel `CheckDatumDiffOpImpl`, `DateUtils`, and `BedingungsOperatorHelper.getDatumsDiff` establish Date-only month/year admission, scale 0, formal-before-empty precedence, symmetric empty fillability, completed-period evaluation, and authored sign; the same generic wrapper checkers admit that number-like operation beneath rounding or `Abs`. Maintained a12-dmkits `DateDifferenceDiffTest`, `EmptyOperandFiringDiffTest`, and `BaseYearDiffTest` triangulate the stored-Date, empty, and direct Base-Year branches; selected Base-Year range execution remains the recorded peer gap, while accepted [`SPEC-2026-07-23-04`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-04--direct-numeric-wrappers-admit-temporal-derived-number-sources) and revision `27afb555` lock the wrapper composition.
- [`SPEC-2026-07-23-05`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-05--numeric-operation-wrappers-compose-over-admitted-value-functions) records the source-audited nested-wrapper/direct-extremum boundary. The reviewed peer already represents arbitrary calculation children and retains nested wrapper plus `Min`/`Max` domain-failure controls, so no upstream work is pending; project-local retained kernel correspondence remains under SG12.
- [`SPEC-2026-07-23-06`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-06--numeric-operand-list-extrema-preserve-per-call-boundaries) records the newly source-audited expression-valued list and independent per-call constant budget. The reviewed peer already preserves arbitrary `Calculation` lists and recursive evaluation, but its exact authoring prose and separating admission locks remain pending reconciliation; project-local retained kernel correspondence remains under SG12.
- Accepted a12-dmkits revisions now lock signed scale/constant expandability, grouping-preserving rendering, per-node precision, one-pass lowering, tolerance, division-domain consumer projections, and numeric storage:
  - [`SPEC-2026-07-19-08`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-08--every-arithmetic-node-uses-precision-50-half_up)
  - [`SPEC-2026-07-19-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-09--numeric-scale-gating-tracks-signed-scale-and-constant-expandability)
  - [`SPEC-2026-07-19-10`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-10--power-preserves-staged-java-precision-and-reciprocal-first-negative-order)
  - [`SPEC-2026-07-19-11`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-11--arithmetic-fillability-uses-joint-terms-and-conservative-power-dispatch)
  - [`SPEC-2026-07-19-12`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-12--division-by-zero-computations-poison-despite-a-cleared-delta)
  - [`SPEC-2026-07-19-13`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-13--tolerance-normalizes-operands-first-and-uses-directional-inequality-polarity)
  - [`SPEC-2026-07-19-14`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-14--numeric-authoring-regions-are-structural-and-function-wrappers-remain-unclosed)
  - [`SPEC-2026-07-19-15`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-15--computed-number-storage-has-distinct-fit-and-warning-suppressed-no-fit-branches)
- those peer controls do not become project-local portable evidence

#### Excluded boundary and gap links

- **Implemented narrowly; external evidence pending outside the cited coercion controls.** Checked validation accepts two same-group expressions with at least one field, the admitted expression classes above including ordinary nonrepeatable `RangeAsNumber` and complete ordinary nonrepeatable String/closed-Enumeration/category `FieldValueAsNumber`, six ordinary operators, four tolerance ranges, and the exact-scale-warning bypass.
- The checked computation operation resolves one nonrepeatable Number target and every scalar or direct-aggregate Number operand through the shared authored-tree traversal, accepts constant-only or field-bearing arithmetic and power after the existing authoring/summary checks, and composes operation-form `Round`, `Abs`, and expression-valued operand-list `Min`/`Max` at ordinary operand positions. Every `Min`/`Max` call retains its source boundary and independent immediate/grouped-literal budget through lowering while delegating its complete operand tree to the common evaluator. The same route therefore covers direct/grouped numeric `BaseYear`, Number fields, `RangeAsNumber`, `FieldValueAsNumber`, aggregates, Base-Year-derived date components, stored temporal components, and Date differences without source-specific value-function evaluators. Rounding/`Abs` rejects an immediate or grouped literal at each wrapper boundary, preserves nested body and enclosing division/power errors, and evaluates staged transforms in authored order. The operation rejects its target at every nested operand position and applies the exact result-scale gate unless the one explicit warning flag is present. A dedicated attachment boundary accepts the complete externally resolved target policy once, rejects scale/signedness drift from the resolved target, and returns a wrapper whose evaluation has no policy argument. The checked core retains the warning flag, while the wrapper retains every target constraint and delegates expression evaluation to the established numeric computation result consumer before choosing ordinary or suppressed classification.
- Stored conversion is exact after scale-19 pre-rounding; its warning-suppressed no-fit renderer is structurally locked to consume that pre-rounded value before 16-digit bounding.
- `FlatFieldDecl` retains declaration pattern source independently of condition-pattern execution. Exact `[0-9]+` is the sole locally executable declared-pattern profile and serves both ordinary String ingestion and numeric-conversion admission; every other declared Java pattern remains model-valid but fails closed at checked String-value lowering until SG7 supplies the injected matcher. Pattern-bearing String computation targets remain explicitly outside the ordinary target route. Repeatable and table-backed conversion sources remain outside the ordinary closed source.
- The resolved target policy supports the ordinary scale-compatible path and the explicit warning-suppressed no-fit path with signedness, minimum/maximum fractional digits, the universal 15-digit check, effective integer-digit capacity, zero admission, rendered length, inclusive numeric range, exact stored form, prior-target delta, exact one-address final application, and cause-free dependency observation. The checked target-operation wrapper retains that complete policy after proving its scale/signedness coherence; construction of the resolved policy remains outside the flat declaration because `FlatFieldDecl` does not retain the remaining target constraints.
- Remaining numeric work is indexed by [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition) and [`SG5`](SEMANTICS-GAPS.md#sg5--numeric-authoring-and-target-completion); repeatable construction is [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), and retained correspondence is [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage). The shared checked condition/expression and generated-validation integration is closed.

### §6 — dates and time

#### Owners

- [`Core.lean`](../A12Kernel/Core.lean) for decoded component primitives and the admitted temporal payload
- [`Semantics/FullDate.lean`](../A12Kernel/Semantics/FullDate.lean)
- [`Semantics/CivilDateCoordinate.lean`](../A12Kernel/Semantics/CivilDateCoordinate.lean)
- [`Semantics/DateComparison.lean`](../A12Kernel/Semantics/DateComparison.lean)
- [`Semantics/DateAggregate.lean`](../A12Kernel/Semantics/DateAggregate.lean)
- [`Semantics/DateRangeOverlap.lean`](../A12Kernel/Semantics/DateRangeOverlap.lean)
- [`Semantics/DateRangeOverlapOperators.lean`](../A12Kernel/Semantics/DateRangeOverlapOperators.lean)
- [`Semantics/DateConstruction.lean`](../A12Kernel/Semantics/DateConstruction.lean)
- [`Semantics/DateConstructionNumeric.lean`](../A12Kernel/Semantics/DateConstructionNumeric.lean)
- [`Semantics/DateNumeric.lean`](../A12Kernel/Semantics/DateNumeric.lean)
- [`Semantics/TimeNumeric.lean`](../A12Kernel/Semantics/TimeNumeric.lean)
- [`Semantics/DateDifference.lean`](../A12Kernel/Semantics/DateDifference.lean)
- [`Semantics/DateTime.lean`](../A12Kernel/Semantics/DateTime.lean)
- [`Semantics/BerlinLegacyTimeZone.lean`](../A12Kernel/Semantics/BerlinLegacyTimeZone.lean)
- [`Semantics/ModelZone.lean`](../A12Kernel/Semantics/ModelZone.lean)
- [`Semantics/DateTimeComparison.lean`](../A12Kernel/Semantics/DateTimeComparison.lean)
- [`Semantics/DateTimeAggregate.lean`](../A12Kernel/Semantics/DateTimeAggregate.lean)
- [`Semantics/DateTimeDifference.lean`](../A12Kernel/Semantics/DateTimeDifference.lean)
- [`Semantics/DateTimeDayDifference.lean`](../A12Kernel/Semantics/DateTimeDayDifference.lean)
- [`Semantics/DateShift.lean`](../A12Kernel/Semantics/DateShift.lean)
- [`Semantics/TimeComparison.lean`](../A12Kernel/Semantics/TimeComparison.lean)
- [`Semantics/TimeAggregate.lean`](../A12Kernel/Semantics/TimeAggregate.lean)
- [`Semantics/TemporalFormat.lean`](../A12Kernel/Semantics/TemporalFormat.lean)
- the matching modules under [`Proofs/`](../A12Kernel/Proofs/) and [`Conformance/`](../A12Kernel/Conformance/)

#### Implemented

- `DateParts → CivilDate → FullDate` separates decoded components, positive-era Gregorian reality, and the inclusive 1583-10-16 value floor.
- Stored/full-Date `AddDays`, `AddMonths`, and `AddYears` start after integer offset conversion and return only floor-admitted full Dates. Day shifting inverts the Gregorian coordinate in at most 400 year steps plus 12 month steps; month/year shifts share landing-day functions while keeping target-month clamping distinct from last-of-February preservation.
- Date-only `DifferenceInMonths` and `DifferenceInYears` share one decoded-parts completed-period mechanism. Stored/full-Date wrappers retain their value-floor boundary, self-zero and swap-negation laws, and distinct February-end year behavior; direct or range-selected Base-Year sources reuse the same mechanism without imposing the unrelated stored-Date floor, so direct January 1 equals range start and precedes range finish by eleven whole months but no whole year. Checked validation and Number computation admit Date fields and direct/range-selected Base-Year operands through the shared numeric source tree, enforce Date-only/component/year compatibility, preserve formal-before-empty precedence and symmetric zero, and fail closed on present legacy-hybrid payloads. Direct operation-form rounding preserves the fixed scale-0 result and symmetric empty movement; direct `Abs` applies after the signed difference and turns symmetric empty zero into grow-only magnitude.
- Resolved full-Date equality, inequality, strict order, and inclusive order share the existing calendar chronology. Their classified validation projection reuses the symmetric scalar operand state: formal unavailability dominates, no value does not fire, and a true comparison fires OMISSION exactly when either present value retains missing provenance. Typed `CellObservation FullDate` now reaches that same path directly, with clean present values fixed, empty not evaluated, and validation unavailability retained. Laws characterize equality, operand/operator exchange across truth and verdict, strict-direction exclusion, unknown/no-value handling, both firing polarities, and checked-observation delegation.
- Stored/full-Date direct and selected-stream `Min`/`Max` use a dedicated chronological fold: empty operands do not compete, every reached formal unavailability aborts, no selected value yields no value, and any empty/tail/`Having` or nested missing provenance makes a selected result symmetrically missing. The result feeds the existing Date comparison operand and verdict path.
- DateTime direct and selected-stream `Min`/`Max` reuse that fold after its second completed temporal consumer, selecting exact epoch-millisecond `Instant` values instead of rendered wall labels. Generic laws own empty identity, unavailable-prefix abortion, fixed singleton, and empty-prefix missingness; Date and DateTime retain only their selector- and verdict-specific laws.
- Resolved three-part construction preserves incomplete, calendar-rejected, and unavailable reasons before projecting `Valid`/`Invalid` verdicts.
- Its direct day/month/quarter/year consumer reads supplied real parts, maps incomplete and unreal to equal amount zero with symmetric not-given versus fixed provenance, and maps cause-free unavailability to UNKNOWN.
- Typed full-Date and DateTime validation observations share one direct Day/Month/Quarter/Year numeric projection. Present values expose fixed decoded date components, DateTime ignores its clock, empty sources become symmetric fillable zero, and exact formal causes survive until the numeric verdict projection. The checked numeric source algebra admits the matching Date/DateTime declaration component, supplements only Year from configured Base Year, routes the same source through validation and Number computation, and admits direct rounding/`Abs` without a temporal-specific wrapper evaluator.
- Typed Time and DateTime validation observations likewise share direct Hour/Minute/Second numeric projection. Present values expose fixed decoded clock components, DateTime ignores its date, and the second completed component family reuses one generic symmetric empty-to-zero/cause-preserving numeric observation seam instead of duplicating its polarity mechanism. The same checked source enum admits only matching Time/DateTime declarations, routes both phases through the shared flat context, and uses the same direct wrapper matrix.
- One closed `TemporalValue` now gives the heterogeneous checked context a coherent representation boundary for all completed consumers: every kind retains exact `Instant` identity, Date/DateTime retain decoded `DateParts` plus calendar provenance, and Time/DateTime retain decoded `TimeOfDay`. Kind is constructor-derived. Checked comparison and both flat numeric component projections read that one payload; wrong-kind or unavailable component reads fail closed, and no consumer reconstructs labels from an instant or reads a parallel context.
- Resolved Date-range overlap keeps supplied inversion explicit, uses closed intervals, preserves occurrence multiplicity, retains ordered skipped/kept operand slots, and implements separate any-pair reached-filter and scalar-versus-list matched-container polarity scans.
- The decoded whole-second baseline adds bounded `TimeOfDay`, admitted `LocalDateTime`, executable UTC resolution, strict local chronology, and the already-truncated whole-hour shift core. Its shared scalar `Instant` now lives in `Core` as exact epoch milliseconds because `World.now` may retain a sub-second clock remainder; `Instant.ofEpochSecond` makes every decoded-value embedding explicit.
- Resolved DateTime equality, inequality, strict order, and inclusive order compare exact epoch-millisecond `Instant` identities rather than wall labels. Date and DateTime share one generic classified scalar verdict path: formal unavailability dominates, no value does not fire, and a true comparison fires OMISSION exactly when either present operand retains missing provenance. Typed `CellObservation Instant` delegates to that path, and generic plus instant-specific laws preserve truth, polarity, clean-value firing, emptiness, and unavailability.
- Resolved Time equality, inequality, strict order, and inclusive order compare decoded `TimeOfDay.secondsSinceMidnight` coordinates after comparable-component checking and the runtime's shared time-only parse anchor. Date, Time, and DateTime share one operation-neutral comparison enum and classified scalar verdict path; typed `CellObservation TimeOfDay` now delegates to it. Time-specific laws preserve equality, strict-direction exclusion, truth, polarity, clean-value firing, and unavailability.
- Resolved Time direct and selected-stream `Min`/`Max` reuse the shared temporal fold, selecting decoded whole-second times by the same seconds-since-midnight coordinate. They retain the common no-value empty identity, formal-unavailability propagation, empty/tail/`Having` missingness, and classified Time comparison polarity without a parallel scan.
- Static temporal format admission retains one six-component set and two deliberate gates. Direct comparison preserves the original date-versus-time class, checks year presence after optional Base Year supplementation, and adds equality-only time-presence agreement without exact component equality; extrema preserve that original class and require exact supplemented component equality. This prevents Base Year from making a Time-only field spuriously date-like in field/field, direct-Base-Year, or Base-Year-range comparisons. Laws establish symmetry, date-class preservation, exact-to-coarse implication, equality-to-ordering implication, and the direct Base-Year precondition; cases lock unequal date precision, Date/DateTime, unequal Time seconds display, Base Year, the with/without-Base-Year date/time separator, and full-DateTime separators.
- The resolved sub-day difference computes `(second.epochMillis − first.epochMillis).tdiv (unitSeconds * 1000)` for a closed hours/minutes/seconds enum.
- Laws establish positive divisors, self-zero, swap negation, millisecond-aware seconds and exact-unit recovery, while cases separate reverse truncation toward zero from floor division and lock the `999 ms → 0`, `1000 ms → 1` boundary.
- `CivilDate.next?` uses checked construction
- laws prove it always advances the Gregorian coordinate by one, strict civil chronology raises that coordinate, and UTC resolution preserves strict local chronology.
- `EuropeBerlinLegacyProfile` implements the exact versioned 62-transition UTC table through 1997, flat pre-first CET, post-1997 last-Sunday recurrence, and all three historical offsets. Its fresh-label resolver rejects every gap and selects the smaller/after offset in ordinary and CEMT overlaps by validating candidate instants against the same profile.
- `ModelZone.resolve?` derives `Today`'s local civil date with the offset at the exact validation instant and then resolves that date's midnight independently. The shared `ModelZoneRules` also resolves complete local labels for temporal `BaseYear` and its selected range endpoint, whose checked operands use January 1 or December 31 midnight in the model zone. UTC and the pinned Berlin profile are concrete consumers; wider consumers inject other admitted zone ids and pre-floor legacy labels without a stored-Date check. Laws preserve exact supplied resolution, January-1 source identity, selected December-31 resolution, and fail-closed unsupported-zone behavior.
- The separate `Berlin2024Profile` spring-only calendar step changes a March 30 `02:xx` landing to March 31 `01:xx` and retains that adjusted clock on the next step.
- The bounded `DifferenceInDays` core counts those stateful landings in authored order, rejects pairs outside the consecutive spring slice, and has universal self-zero and swap-negation laws.

#### Evidence

- Pinned kernel 30.8.1 format/check/decode/comparison/calendar-add/instant-difference/range-overlap source and focused a12-dmkits Date/DateTime implementation and differentials establish the source account and triangulation.
- Maintained a12-dmkits `DateArithmeticDiffTest` separates stored-Date day shifting and ordinary month/year shifts, leap-aware month clamping, February 29 demotion, February 28 promotion into a leap year, and the non-end-of-February control across both kernel strategies and the peer interpreter.
- Maintained a12-dmkits `DateDifferenceDiffTest` separates ordinary and partial periods, clamped month ends, cross-year counts, reverse truncation toward zero, February 29 demotion, and February 28 promotion across both kernel strategies and the peer interpreter.
- Maintained a12-dmkits `DateExtractDiffTest`, `TimeExtractDiffTest`, and `DateFunctionsOverDateTimeDiffTest` separate all four direct date components, all three direct time components, each ignored DateTime half, and the empty-to-zero branch across both kernel strategies and the peer interpreter.
- Maintained a12-dmkits `DateLiteralDiffTest` establishes that a typed Date literal is canonicalized before equality and ordering, so comparison follows date identity and chronology rather than stored text. Kernel `RuntimeController.vergleicheDATUM` and `VkDate` establish the separate non-relevant, null/no-value, and symmetric not-given verdict projection.
- Maintained a12-dmkits `DateAggregateDiffTest` separates the Date combiner's no-value empty identity, empty skipping, formal-unavailability propagation, symmetric missing polarity, direct versus selected-stream shapes, and computation clearing across both kernel strategies and the peer interpreter.
- Maintained a12-dmkits `DateTimeConstructDiffTest` locks resolved DateTime equality and ordering, while `DstTimeZoneDiffTest.chainedAddKeepsItsInstantIdentity` separates equal-looking Berlin overlap labels whose exact instants differ by one hour and locks the spring-gap equality control across both kernel routes plus the peer interpreter.
- a12-dmkits IF155 pins the same named 62-transition JDK 21.0.11/tzdb2026a profile, independently checks immediately before/at/after every transition plus mutation classes, and differentially verifies the complete historical vector through both kernel strategies. Lean implements that accepted canonical profile directly; no new outbound sync entry is needed.
- Kernel temporal comparison checking, time-only parse anchoring, and `VkDate` comparison establish Time ordering after decoded admission. Maintained a12-dmkits `TimeAndDateTimeReadTest` locks accepted Time ordering and round-trip shape, while `DateConstructionDiffTest` locks constructed-Time equality across both kernel routes and the peer interpreter; a focused retained Time-order differential is still absent.
- Kernel `RuntimeController.validationTime`/`getJetzt`, `VkDate`, and `BedingungsOperatorHelper` establish exact millisecond identity for `Now`, temporal comparison, shifts, and sub-day differences. Local executable cases lock same-second inequality/order and the seconds-quotient boundary. Accepted [`SPEC-2026-07-22-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-02--now-retains-exact-epoch-millisecond-identity) records a12-dmkits revision `9c8da06e`: IF206 and maintained dual-kernel-route/JVM/Node controls now cover same-rendered-second identity, both `999 ms` difference directions, and a remainder-preserving shift. This repository still retains no portable local DateTime observation.
- Kernel `RuntimeController.getHeute` copies the zone-set validation calendar and clears hour, minute, second, and millisecond; local cases distinguish UTC from Berlin local-date selection and independently re-resolve Berlin midnight across the spring offset change. a12-dmkits `ClockDiffTest` and its injected-clock controls establish date-shaped comparison behavior, but this repository retains no exact portable model-zone-midnight observation.
- Kernel `CheckKonstanteReferenzjahrImpl`, `CheckVergleichsBedingungImpl`, `CheckDatumDiffOpImpl`, `CodeGenCreator.endVisit(IDateRangeExtractionOperation)`, numeric fractional-digit checking, `RuntimeController.getReferenzjahr`, and the date-difference runtime establish declared-model admission, Number-versus-Date dispatch, exact scale-0 equality, immutable date/time class, model-zone January 1/December 31 resolution, and completed-period consumption of direct/range-selected date sources. Maintained a12-dmkits `BaseYearDiffTest` triangulates the numeric and direct-date projections across both kernel strategies; `PointInTimeSourceReadTest` locks authored range-source acceptance and roundtrip, while peer range execution and therefore Base-Year range-difference calibration remain the recorded upstream gap. This repository retains no portable Base Year observation.
- Kernel `CheckVergleichsBedingungImpl`, `DateFormat`, and `CheckEntityListenUtils` establish the coarse direct-comparison and exact aggregate component gates. Accepted [`SPEC-2026-07-22-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-01--direct-temporal-comparison-and-extrema-use-different-format-gates) records a12-dmkits revision `43824168`, whose canonical prose and maintained kernel-route law separate partial component sets, ordering from equality, date from time, and Base Year supplementation without changing the aggregate evaluator.
- Kernel temporal aggregate checkers and `DateCombiner`/`VkDate` establish comparable-component admission plus resolved Time-coordinate and DateTime-instant selection through the same empty, non-relevance, and missingness fold as Date. Accepted [`SPEC-2026-07-21-07`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-07--time-and-datetime-extrema-preserve-resolved-temporal-order) records a12-dmkits revision `43824168`: TIME operand-list extrema now fold by decoded time-of-day, DATE/DATETIME by exact instant, and star-extremum authoring/readback preserves TIME/DATETIME. DG15 explicitly parks the pre-existing adapter read/roundtrip gap for temporal operand-list extrema; evaluation is covered.
- An isolated artifact-only consumer at documentation revision `1c4c48a` recovered the complete resolved Date/Time/DateTime comparison and extremum procedures, the first-cause and missing-provenance distinctions, the one-second and Berlin-overlap separators, the swapped-comparison law, and the unsafe render/drop/reorder/seed transformations without sibling or kernel research. This establishes bounded knowledge transport, not authored integration, shipment readiness, external implementation correctness, or additional kernel correspondence.
- Groovy-dynamic kernel differentials directly establish positive and reverse fractional sub-day truncation.
- Selected whole-unit DST cases also agree through generated static Java, but that route does not separately cover the reverse-fraction discriminator.
- At reviewed a12-dmkits revision `71775c9905b057831253348c31ce39e321e61889`, focused controls lock both Date-range polarity scans through both kernel routes plus the interpreter, and separately lock constructed-Date reason/calendar consumers and `DifferenceInDays` calendar-step separators.
- This repository retains no portable Date, DateTime, construction, or Date-range observation

#### Excluded boundary and gap links

- **Status:** implemented internally on narrow domains; external evidence partly pending.
- Date coverage includes the unbounded positive-era account, resolved six-way full-Date comparison with classified validation polarity, stored/full-Date `Min`/`Max`, admitted full-Date day/month/year shifts and signed completed-period differences, resolved three-part construction classification, and the proved calendar-coordinate successor/strict-monotonicity bridge.
- Date-range coverage includes closed occurrence-preserving overlap truth, both resolved operator shapes, and their filter-derived polarity scans.
- Time coverage includes exact six-way decoded time-of-day comparison with classified validation polarity and resolved coordinate-based `Min`/`Max`. DateTime coverage includes exact six-way resolved-instant comparison with classified validation polarity, resolved exact-instant `Min`/`Max`, the proved UTC local-order bridge, resolved `DifferenceInHours/Minutes/Seconds`, the full versioned Berlin legacy offset/fresh-label profile, and resolved `DifferenceInDays` inside its consecutive spring slice.
- The admitted full-Date shifts deliberately cover only already-converted integer offsets whose result remains a stored/computed full Date. Checked month/year difference sources now accept ordinary Date fields plus direct or selected Base-Year endpoints, return fixed scale-0 values, map any check-relevant empty operand to symmetric zero, and preserve exact formal causes across validation/computation. Numeric truncation and 32-bit conversion for shifts, constructed-Date legacy identity, partially-known Date metadata, DateTime gates and wall-time behavior, temporal target formatting, and Date cell effects remain outside.
- The resolved Date, Time, and DateTime comparison owners start after static component admission and after each operand has been classified as a present full Date, decoded time of day, or exact instant with symmetric missing provenance, no value, or formal unavailability. All three accept their matching typed validation observation directly. The checked field-to-field route performs declaration/path lowering and compares already-parsed exact runtime instants; the field-to-Date-literal route begins after lexical classification plus model-zone/Base-Year decoding and preserves the literal's component shape; checked `Today`, `Now`, temporal `BaseYear`, and selected `StartOfDateRange(BaseYear)`/`EndOfDateRange(BaseYear)` inject the explicit evaluation world after their distinct component gates. Concrete token typing, AM/PM decoding, partial-Date text resolution, and model-zone-id legality checking remain outside.
- Concrete declaration/path lowering has one shared storage representation and checked presence/comparison path. The existing heterogeneous field-ID-indexed `Value` context carries one constructor-tagged `TemporalValue`; `FieldKind.temporal` retains declaration-owned components, formal checking accepts only the matching kind, and `FlatTemporalField` reuses ordinary presence, requiredness, generated guards, model-context construction, multi-field relevance, exact-instant comparison, and direct date/time numeric component reads. `FlatTemporalOperand` owns field, fixed typed literal, dynamic `Today`, temporal `BaseYear`, selected Base-Year range endpoint, and dynamic `Now` shapes without a parallel evaluator. Proof-bearing `FullDate` and `LocalDateTime` remain resolved parser refinements rather than storage alternatives.
- The shared temporal-extremum owner starts with classified stored/full-Date, decoded Time, or exact-instant operands plus resolved tail/`Having` markers. Path/star expansion, raw cells, computation target clearing/application, checked authoring, constructed-Date calendar identity, Time/DateTime parsing and zone resolution, and target rendering remain outside.
- Construction classification and its direct numeric component projection remain reason-bearing but do not yet retain calendar identity through checked lowering or implement legacy-hybrid month/year operations. Checked authored-expression lowering is closed for direct Date/DateTime Day/Month/Quarter/Year, Time/DateTime Hour/Minute/Second, Base-Year-derived date components, and stored-Date/Base-Year month/year-difference sources in plain validation, Number-computation arithmetic, and direct operation-form rounding/`Abs`. Partially-known Date declarations require earlier source-form metadata beyond the ordinary flat field, while constructed-Date differences and broader nested value-function traversal remain outside.
- Date-range raw cell classification, actual filter evaluation, paths/stars, row gates, and checked lowering remain outside the resolved operator capsule.
- Remaining temporal parsing, authoring, calendar, operator, target, and integration work is indexed by [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion); document/repeatable construction dependencies are [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction) and [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction). The shared checked-expression integration is closed.

### §7 — strings and patterns

#### Owners

- [`Cell.lean`](../A12Kernel/Cell.lean)
- [`Semantics/String.lean`](../A12Kernel/Semantics/String.lean)
- [`Semantics/StringFieldPolicy.lean`](../A12Kernel/Semantics/StringFieldPolicy.lean)
- [`Semantics/StringPattern.lean`](../A12Kernel/Semantics/StringPattern.lean)
- [`Elaboration/StringPattern.lean`](../A12Kernel/Elaboration/StringPattern.lean)
- [`Semantics/LegalCharset.lean`](../A12Kernel/Semantics/LegalCharset.lean)
- [`Semantics/CustomFieldType.lean`](../A12Kernel/Semantics/CustomFieldType.lean)
- [`Semantics/CustomFieldMessage.lean`](../A12Kernel/Semantics/CustomFieldMessage.lean)
- [`Semantics/CustomFieldFormalMessage.lean`](../A12Kernel/Semantics/CustomFieldFormalMessage.lean)
- [`Semantics/CustomFieldValidity.lean`](../A12Kernel/Semantics/CustomFieldValidity.lean)
- [`Elaboration/CustomField.lean`](../A12Kernel/Elaboration/CustomField.lean)
- [`Elaboration/LegalCharset.lean`](../A12Kernel/Elaboration/LegalCharset.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/RawString.lean`](../A12Kernel/Elaboration/RawString.lean)
- [`Semantics/StringComputation.lean`](../A12Kernel/Semantics/StringComputation.lean)
- [`Proofs/StringIngestion.lean`](../A12Kernel/Proofs/StringIngestion.lean)
- [`Proofs/StringFieldPolicy.lean`](../A12Kernel/Proofs/StringFieldPolicy.lean)
- [`Proofs/StringPattern.lean`](../A12Kernel/Proofs/StringPattern.lean)
- [`Proofs/PatternAdmission.lean`](../A12Kernel/Proofs/PatternAdmission.lean)
- [`Proofs/LegalCharset.lean`](../A12Kernel/Proofs/LegalCharset.lean)
- [`Proofs/LegalCharsetElaboration.lean`](../A12Kernel/Proofs/LegalCharsetElaboration.lean)
- [`Proofs/CustomFieldCause.lean`](../A12Kernel/Proofs/CustomFieldCause.lean)
- [`Proofs/CustomFieldType.lean`](../A12Kernel/Proofs/CustomFieldType.lean)
- [`Proofs/CustomFieldMessage.lean`](../A12Kernel/Proofs/CustomFieldMessage.lean)
- [`Proofs/CustomFieldFormalMessage.lean`](../A12Kernel/Proofs/CustomFieldFormalMessage.lean)
- [`Proofs/CustomFieldValidity.lean`](../A12Kernel/Proofs/CustomFieldValidity.lean)
- [`Proofs/CustomFieldElaboration.lean`](../A12Kernel/Proofs/CustomFieldElaboration.lean)
- [`Proofs/CustomFieldContext.lean`](../A12Kernel/Proofs/CustomFieldContext.lean)
- [`Proofs/StringLength.lean`](../A12Kernel/Proofs/StringLength.lean)
- [`Proofs/StringComputation.lean`](../A12Kernel/Proofs/StringComputation.lean)
- [`Proofs/RawString.lean`](../A12Kernel/Proofs/RawString.lean)
- [`Conformance/StringIngestion.lean`](../A12Kernel/Conformance/StringIngestion.lean)
- [`Conformance/StringFieldPolicy.lean`](../A12Kernel/Conformance/StringFieldPolicy.lean)
- [`Conformance/StringPattern.lean`](../A12Kernel/Conformance/StringPattern.lean)
- [`Conformance/PatternAdmission.lean`](../A12Kernel/Conformance/PatternAdmission.lean)
- [`Conformance/LegalCharset.lean`](../A12Kernel/Conformance/LegalCharset.lean)
- [`Conformance/LegalCharsetElaboration.lean`](../A12Kernel/Conformance/LegalCharsetElaboration.lean)
- [`Conformance/CustomFieldCause.lean`](../A12Kernel/Conformance/CustomFieldCause.lean)
- [`Conformance/CustomFieldType.lean`](../A12Kernel/Conformance/CustomFieldType.lean)
- [`Conformance/CustomFieldMessage.lean`](../A12Kernel/Conformance/CustomFieldMessage.lean)
- [`Conformance/CustomFieldFormalMessage.lean`](../A12Kernel/Conformance/CustomFieldFormalMessage.lean)
- [`Conformance/CustomFieldValidity.lean`](../A12Kernel/Conformance/CustomFieldValidity.lean)
- [`Conformance/CustomFieldElaboration.lean`](../A12Kernel/Conformance/CustomFieldElaboration.lean)
- [`Conformance/CustomFieldContext.lean`](../A12Kernel/Conformance/CustomFieldContext.lean)
- [`Conformance/StringLength.lean`](../A12Kernel/Conformance/StringLength.lean)
- [`Conformance/StringComputation.lean`](../A12Kernel/Conformance/StringComputation.lean)
- [`Conformance/RawString.lean`](../A12Kernel/Conformance/RawString.lean)

#### Implemented

- Parsed String ingestion performs one non-overlapping CRLF-to-LF pass and caches the evaluated text
- LF and lone CR are preserved.
- Direct comparison, `Length`, and computation share that cached value, and the exact overlap counterexample prevents a second pass.
- `StringFieldPolicy` retains ordinary declaration-owned line-break permission and optional min/max length. `FlatFieldDecl.checkRaw` checks nonempty input in the exact raw-break-before-normalized-UTF-16-length order, maps a failure into the shared checked-cell invalidity channel, and is reused by flat, computation, aggregate, and repeatable context construction rather than duplicating policy in consumers.
- Flat-model validation rejects String policy on other scalar kinds or registered custom types, enforces minimum/maximum consistency and the line-break/single-character-maximum exclusion, requires raw Strings to permit line breaks, and forbids a raw minimum while retaining a raw maximum as metadata. Raw runtime checking deliberately skips that retained maximum.
- `FlatFieldDecl` retains evaluated-versus-raw String mode. One declaration-owned `toStringValueField?` capability now gates checked direct comparisons, flat and starred value lists, String expressions, token aggregate sources, and String RNU keys; checked-core admission independently re-derives that gate, while presence continues through `toPresenceField`.
- The whole-rule boundary recognizes only strict `Length(raw) > integer` and mirrored `integer < Length(raw)`, retains the exact field and bound as max-length metadata, and exposes no runtime condition. Ordinary condition lowering rejects the same shape so it cannot accidentally execute; non-strict, nested, nonintegral, and computation uses fail closed.
- Direct equality/inequality and the four scale-exempt `Length` ordering operators have separate consuming clauses.
- Resolved `PatternMatched`/`PatternViolated` consume an injected already-admitted whole-value matcher through the same normalized checked String read. Empty is not evaluated, formal unavailability remains UNKNOWN, the two operators are exact complements on present input, and every firing is VALUE-typed.
- Checked pattern admission separates an injected Java-compilation decision from an independently written character scan over the finite documented kernel exclusions and the separately observed uppercase-`\P` exclusion. A successful source carries both proof facts and delegates only to the existing resolved whole-value matcher; admission makes no JavaScript-portability claim.
- The admitted legal-charset runtime has a distinct default non-supplementary BMP policy plus explicit inclusive BMP ranges and bounded two/three-character atomic entries. It scans left-to-right, chooses the longest complete atomic prefix, falls back to exactly one range character, and emits the shared `unsupportedCharacter` cause only at the full-input check boundary.
- Checked `supportedCharacters` lowering injects only Java-compatible grapheme clustering, distinguishes an empty definition from an empty entry, rejects supplementary/surrogate-bearing, overlong, plain multi-character, reversed-range, and narrowly ambiguous-overlap shapes, and retains legal shared and terminal prefixes in the bounded runtime representation.
- Registered custom field-type rejection has its own formal cause carrying the exact project code and optional message template. It remains structurally distinct from the fixed declarative `customValidation` fallback and survives unchanged as validation UNKNOWN or computation poison.
- A custom field-type declaration retains raw optional bounds; checked construction resolves its exact named pure validator from `World` or rejects the model. Relevant nonempty parsed values receive locale, effective `1`/`999` defaults, and stored-value mode `false`; nonrelevant, empty, and previously rejected cells bypass sampling. The one returned ordinary checked cell reuses the exact registered rejection across both phases.
- A supplied registered rejection template is rendered once at the resolved-label boundary. Every exact case-sensitive `$<fieldName>$` token is replaced, other bytes stay ordered, inserted label bytes are opaque, and absent text remains distinct from an explicitly supplied empty message so the caller retains fallback ownership.
- A registered rejection projects to a distinct custom formal-message payload using the caller's exact cell address, resolved label, and already-localized fallback. The project code is preserved, ERROR severity and VALUE polarity are fixed, a supplied template wins even when empty, and fallback bytes remain opaque.
- One relevance-gated custom validation output now pairs the exact reusable checked cell with its optional registered formal message. Only the leading registered custom cause projects a message; acceptance, semantic empty, preceding noncustom rejection, and nonrelevance cannot manufacture one, and the validator result is not sampled again.
- Explicit registered `Valid(field, "Name")` / `Invalid(field, "Name")` resolve their exact validator name through the same checked registry boundary as declared custom fields. One shared optional-bound context distinguishes declared effective bounds from the predicate's absent bounds; the explicit path supplies fixed `de_DE`, absent bounds, and stored-value mode. Empty and formal unavailability are UNKNOWN, while present nonempty acceptance/rejection are exact VALUE-only complements.
- Flat String declarations may retain optional custom-type metadata. Ordinary model validation rejects that metadata on non-String kinds; the checked custom overlay then validates the original model, resolves each declared validator once in declaration order, and retains exact source declaration/model identity without changing ordinary declarations or raw-context semantics.
- The prepared overlay applies at the existing heterogeneous flat read boundary: custom declarations require a runtime String and reuse the resolved locale/effective-bound/stored-mode classifier, while ordinary declarations still use `formalCheck`. Absence, present-empty, and prior rejection retain their existing cells; wrong runtime kinds, inconsistent overlays, unknown IDs, and any attempt to use the unprepared context for custom metadata fail closed as malformed.
- The checked full-evaluation entry point composes model/custom preparation, ordinary condition elaboration against the same model, the prepared locale-aware context, explicit `World`, and the existing flat evaluator. Preparation and condition errors remain distinct, and ordinary no-custom models use the same semantic owners rather than a second evaluator.
- An already-checked String cell projects directly into the existing resolved RNU token/empty/unknown component. The adapter reads the validation observation once, preserves an exact registered custom rejection as the unknown cause, and leaves nonrelevance outside so excluded cells produce no component rather than a second validator call.
- Both direct String equality operators suppress an empty field or empty literal after preserving malformed input as UNKNOWN; distinct nonempty values fire only inequality.
- a parsed empty String retains present-empty placement while supplying the same clean-empty observation as absence
- `FieldFilled`/`FieldNotFilled` consume that empty observation rather than physical placement, and checked flat lowering admits String presence.
- Absolute String requiredness reuses the generated `FieldNotFilled` staging and preserves present-empty placement when attaching `.required`.
- shared String length counts UTF-16 code units.
- The computation slice separately models empty contribution, evaluated text, root storage, declaration-owned ordinary target checking, target outcome, and delta projection. `RangeAsString` shares the checked String-field resolver, resolves the nonrepeatable field shape before validating its 1-based inclusive interval and admits the String value kind afterward, slices the normalized value at exact UTF-16 code-unit boundaries, returns evaluated empty text for a missing or overshot source, preserves poison, and explicitly rejects a low-level half-surrogate result that Lean `String` cannot represent. The target check reuses `StringFieldPolicy` for line-break/minimum/maximum first-failure order, measures permitted CRLF through the normalized view, keeps explicit zero bounds inert, admits combined bounds, and preserves the exact attempted payload on both acceptance and error.
- Checked operation lowering binds one nonrepeatable ordinary String target and its exact declaration policy to the checked expression under the same validated model; direct target self-reference, raw targets, registered-custom targets, wrong kinds, and repeatable targets fail before runtime evaluation.
- Exact accepted/rejected attempt preservation, forbidden-break precedence, no-value/poison bypass, store/delta identity, target admission/self-reference exclusion, evaluator delegation, and the nearest stronger term/application non-laws are proved.

#### Evidence

- Four operator-sensitive validation cases separate empty-content, empty-row, `"ABC"`, and six-character direct-equality/Length outcomes.
- The combined compact root-String record retains 13 copy/concatenation/root-storage cases and nine positive minimum/maximum target cases with exact boundaries, violations, absent/stale/equal priors, and padded blanks.
- Both kernel strategies agreed throughout before one-time compaction.
- The raw-String boundary is source-grounded in the parser's value-read gate and whole-condition analyzer plus the shared validation generator's rule-removal step. Maintained a12-dmkits `NvvRawTypeLawsTest`, `NvvRawTypeDiffTest`, and `NvvEliminatedLengthRuleTest` lock exact acceptance, both kernel strategies, full/partial non-firing, and unchanged presence; Lean retains no separate portable observation.
- The String formal-policy matrix separates default-forbidden breaks, permitted CRLF normalization before minimum/maximum measurement, empty bypass, exact checked-cell failure, validation UNKNOWN versus computation poison, repeatable-context reuse, every represented model-legality discriminator, and raw maximum skip. Maintained a12-dmkits `FieldConstraintFormalDiffTest` and `CrlfLengthNormalizationDiffTest` anchor the runtime clauses across both kernel strategies; Lean retains no separate portable observation.
- Maintained a12-dmkits IF198 tests separately establish the present-empty placement and downstream field/group/required outcomes across both kernel strategies plus JVM/Node.
- Combined/zero target bounds, permitted CRLF target measurement with exact-payload retention, lone-CR non-normalization, forbidden-break target error, integrated target lowering, no-value/poison bypass, and CRLF/LF/lone-CR ingestion are internal Lean laws/cases not separately exercised by retained local evidence.
- Maintained a12-dmkits `RangeCoercionDiffTest` at originating revision `0f2a5687822797ed7b4f897b0320793ae22eb7b6` locks 1-based inclusive selection and empty-on-overshoot against both kernel strategies for conservative ASCII. Lean additionally separates normalized-before-slice CRLF, the one-character bound, checked-target integration, exact poison, and aligned versus half-surrogate low-level inputs; the Unicode cases are not externally calibrated.
- Eight resolved pattern cases separate normalized match/nonmatch, both operator polarities, empty suppression, and formal unavailability; generic laws prove complement and exclude OMISSION firing.
- Thirteen pattern-admission declarations distinguish Java-syntax precedence, all four possessive suffixes, lookbehind/named/atomic group prefixes, every documented forbidden escape, uppercase `\P`, nested versus escaped/sequential class opens, admitted lookahead/flags/Java escapes, and successful versus rejected runtime delegation. Four laws characterize compiler rejection, successful two-stage classification/delegation, and inherited VALUE-only firing.
- Twelve legal-charset runtime cases separate default BMP, supplementary input, range/atomic composition, component leakage, reversal/repetition, shared prefixes, longest terminal-prefix selection, empty progress, and the exact formal cause. Generic laws lock bounded progress, exact accepted payload retention, and validation-UNKNOWN/computation-poison projection.
- Eleven definition-admission cases cover the default, accepted range/atom composition, shared and terminal prefixes, and every bounded malformed discriminator against an injected cluster corpus; empty-list and empty-entry laws lock the critical default distinction.
- Four cause cases and three generic laws distinguish registered versus fixed fallback failure and preserve the complete project rejection through both checked phases.
- Eight registered-validator cases and eight laws separate authored/defaulted context, relevance, semantic emptiness, prior parser failure, acceptance, exact project rejection, missing registration, and shared phase projection.
- Six supplied-message cases and three laws separate absent versus supplied-empty text, repeated exact replacement, near misses, empty labels, opaque replacement bytes, and project-code independence.
- Nine formal-message/output cases and eight laws lock exact address/code metadata, fixed ERROR/VALUE classification, supplied-empty priority, fallback selection/opacity, leading-cause selection, accepted/empty/malformed silence, exact rejected-cell reuse, and relevance exclusion.
- Nine explicit-validity cases and seven laws separate fixed context, declared-versus-absent bounds, exact-name resolution, empty/formal/defensive-empty UNKNOWN, acceptance/rejection, VALUE-only complement, and project-payload non-observation.
- Four checked-declaration cases and five laws separate ordinary-empty overlay, ordered multi-custom preparation, exact case-sensitive absence, non-String rejection, registered singleton identity, exact model-error propagation, and source-model preservation.
- Ten prepared-context cases and eight laws separate exact-context acceptance/rejection, ordinary String normalization and Number admission, physical/semantic empty, prior rejection, wrong runtime kind, unknown ID, exact prepared/ordinary dispatch, and the unprepared-custom bypass guard.
- Seven checked full-evaluation cases and three composition laws separate accepted/rejected/empty custom presence, ordinary-model execution, missing registration, invalid custom kind, bad condition resolution, phase ordering, and exact successful delegation.
- Five custom-key cases and four generic checked-token laws separate accepted token, semantic empty, preceding parser failure, exact registered rejection, and relevance exclusion before component construction.
- A fresh 38-file artifact-only consumer readback recovered the normalized declared-check, message, explicit-validity, and resolved-RNU procedures plus their assurance boundary without sibling, kernel, web, Git-history, prior-report, or unlisted-file access. Execute, Explain, and Qualify design pass at that boundary; authored full evaluation and shipment do not.
- Historical a12-dmkits triangulation had three final-empty-store mismatches and agreed with all nine target cases at projected delta and stored-value application granularity
- the [archive](archived/STRING-COMPUTATION-RAW-EVIDENCE.md) owns that detail.
- The retained strings remain conservative ASCII and do not externally establish broader Unicode or line-break behavior

#### Excluded boundary and gap links

- **Implemented narrowly; wider target correspondence remains pending.** Coverage includes declaration-owned ordinary String line-break/min/max policy, direct equality/inequality, four `Length` orderings, presence, absolute requiredness, present-empty placement, CRLF normalization, checked nonrepeatable literal and field-valued `AtLeastOne`/`No`/`NotAll`, scalar literal and field-valued Included/NotIncluded, resolved already-admitted pattern consumption, checked scalar String expressions including ordinary nonrepeatable `RangeAsString`, the raw-String value-read gate and eliminated maximum-length declaration, and checked ordinary String target construction with combined/zero bounds plus forbidden/permitted line-break behavior.
- Raw-mode line-break/minimum/maximum legality is checked in the flat model. Checked message-template value interpolation and not-yet-authored String operators remain open under [`SG7`](SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion) and [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).
- `Length ==`/`!=` remain outside the reduced checked surface because their numeric scale gate needs the authored literal scale that `SurfaceCondition.lengthCompare` does not retain.
- Checked ordinary String expression/target lowering is closed without defining a scheduler or document transition. Pattern-bearing, Enumeration, raw, registered-custom, and repeatable String target execution remain outside; the retained target packet still covers only positive single bounds over conservative ASCII.
- Java `Pattern` compilation and execution remain injected capabilities. The bounded kernel source gate is checked, but authored condition/declared-field lowering, association of a host matcher with the certified source, public exposure, and every undiscovered total-admission restriction remain outside; the certificate deliberately does not claim JavaScript portability.
- Java-compatible grapheme clustering remains an injected admission-time capability rather than a reimplemented Unicode subsystem. Raw JSON decoding/model-slot wiring, project-level SPI selection, general scalar-parser composition, and retained local kernel observations remain outside; the runtime representation makes empty/unbounded atomic entries impossible and is not used by computed-target basic checks.
- Registered custom validation is checked through relevance-first sampling and the ordinary cell root, one output retains that exact cell plus its optional formal message, supplied bytes render at an already-resolved label boundary, the explicit named validity pair reuses the same registry/context interface, resolved RNU consumes the same checked observation without resampling, and the flat checked full-evaluation entry point prepares and applies declaration-owned validators. The pure function-valued context guarantees extensionally stable reads but is not yet the document-addressed host cache required by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction).
- Remaining String, pattern, custom-field, requiredness, target, and repeated-consumer work is indexed by [`SG7`](SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion), with shared repeatable construction under [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- Input normalization does not itself grant a computed target permission to contain CR/LF; the target declaration's own line-break policy decides, and permitted target checking retains the exact attempted text after measuring a temporary normalized view.
- Mixed String/stored-Enumeration `FirstFilledValue` now covers direct/plain-star/filtered-star checked selection with exact normalized tokens, prefix polarity, and no-value exhaustion. Remaining coercions, repeatable/filtered list shapes, general computation lowering/scheduling, and the other String functions remain outside this boundary under [`SG7`](SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion) and [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).
- The public normalized protocol and consumer capabilities have not been expanded to String

### §8 — enumerations and value lists

#### Owners

- [`Semantics/ScalarEquality.lean`](../A12Kernel/Semantics/ScalarEquality.lean)
- [`Semantics/Enumeration.lean`](../A12Kernel/Semantics/Enumeration.lean)
- [`Semantics/CheckedEnumeration.lean`](../A12Kernel/Semantics/CheckedEnumeration.lean)
- [`Semantics/EnumerationValueList.lean`](../A12Kernel/Semantics/EnumerationValueList.lean)
- [`Semantics/EnumerationRepetitionNotUnique.lean`](../A12Kernel/Semantics/EnumerationRepetitionNotUnique.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Semantics/PartialValidation.lean`](../A12Kernel/Semantics/PartialValidation.lean)
- [`Elaboration/EnumerationComparability.lean`](../A12Kernel/Elaboration/EnumerationComparability.lean)
- [`Elaboration/Enumeration.lean`](../A12Kernel/Elaboration/Enumeration.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/StarNumberValueList.lean`](../A12Kernel/Elaboration/StarNumberValueList.lean)
- [`Elaboration/StarStringValueList.lean`](../A12Kernel/Elaboration/StarStringValueList.lean)
- [`Elaboration/StarEnumerationValueList.lean`](../A12Kernel/Elaboration/StarEnumerationValueList.lean)
- [`Semantics/ValueList.lean`](../A12Kernel/Semantics/ValueList.lean)
- their counterparts under [`Proofs/`](../A12Kernel/Proofs.lean), including [`EnumerationElaboration.lean`](../A12Kernel/Proofs/EnumerationElaboration.lean), [`CheckedEnumeration.lean`](../A12Kernel/Proofs/CheckedEnumeration.lean), [`EnumerationValueList.lean`](../A12Kernel/Proofs/EnumerationValueList.lean), [`FlatNumberValueList.lean`](../A12Kernel/Proofs/FlatNumberValueList.lean), [`StarStringValueList.lean`](../A12Kernel/Proofs/StarStringValueList.lean), [`StarEnumerationValueList.lean`](../A12Kernel/Proofs/StarEnumerationValueList.lean), [`EnumerationRepetitionNotUnique.lean`](../A12Kernel/Proofs/EnumerationRepetitionNotUnique.lean), and [`StringIngestion.lean`](../A12Kernel/Proofs/StringIngestion.lean), and under [`Conformance/`](../A12Kernel/Conformance.lean), including [`FlatEnumeration.lean`](../A12Kernel/Conformance/FlatEnumeration.lean), [`FlatStringValueList.lean`](../A12Kernel/Conformance/FlatStringValueList.lean), [`FlatNumberValueList.lean`](../A12Kernel/Conformance/FlatNumberValueList.lean), [`StarStringValueList.lean`](../A12Kernel/Conformance/StarStringValueList.lean), and [`StarEnumerationValueList.lean`](../A12Kernel/Conformance/StarEnumerationValueList.lean)

#### Implemented

- Runtime Enumeration comparison uses a clean stored token or one lockstep positional category mapping
- repeated category tokens are legal, empty is not evaluated, unavailable input stays UNKNOWN, and every firing is VALUE.
- The separate direct-field static gate classifies identity labels as effectively textless, rejects a String/display-class mismatch, and accepts two display-bearing ordinary Enumerations exactly when their common-locale stored/display relation has no forward or reverse conflict.
- One checked ordinary closed declaration now owns the nonempty unique stored-token domain, complete per-locale stored/display facts with injective display text, and unique named positional category vectors with exact arity and nonempty tokens. Identity displays remain legal and effectively textless; repeated category tokens remain legal and many-to-one. Its projections reuse the existing runtime and comparability representations.
- A proof-bearing literal comparison resolves the exact stored/category projection, admits the literal from that selected domain for either equality operator, and consumes one declaration-checked heterogeneous raw cell through the existing runtime evaluator. Empty values remain not evaluated, out-of-domain stored tokens become the declaration's formal constraint failure and therefore UNKNOWN, wrong runtime kinds become malformed UNKNOWN, and preceding raw failures retain UNKNOWN.
- A checked stored/category value-list operand maps the existing resolved Enumeration classification directly into the existing token-domain `ValueListCell`: present projected token, empty, or exact-cause unknown. It builds an already-expanded side while retaining caller-supplied tail/`Having` facts, so the three existing quantifiers consume ordinary and many-to-one category values without a second token or poison mechanism.
- The same checked stored/category projection now maps directly into the existing RNU key component. Present projected tokens, optional empty, and exact-cause unknown retain the settled eligibility, tuple equality, cluster, and polarity behavior. Literal, value-list, and RNU consumers share one proof-bearing projection owner; extending the family removed the former value-list-only wrapper rather than creating a third checked type.
- Ordinary closed Enumeration declarations are now part of the shared nonrepeatable flat model, presence, relevance, elaboration, and full-evaluation spine. Stored-token syntax and explicit category syntax both retain the exact checked projection in the core; declaration-owned raw checking rejects invalid stored tokens and wrong runtime kinds before the existing evaluator. The prepared custom-field context delegates non-custom reads to the same declaration-owned checker, so it does not bypass Enumeration admission.
- Direct nonrepeatable String/String, String/Enumeration, and Enumeration/Enumeration equality and inequality now reuse one two-field textual operand and the shared symmetric scalar evaluator. Checked lowering re-derives both exact declaration profiles and applies the effective-display comparability gate before admitting the core; hand-built cores must pass that same model-owned check. Enumeration runtime operands project stored tokens, empty operands do not fire, formal failures dominate as UNKNOWN, and a fully present fire is VALUE.
- Exact category access is now a projection-bearing textual field operand in the same flat equality path. If either side is a category, static admission bypasses direct-field display remapping exactly as the kernel checker does; category-to-String, category-to-stored-Enumeration, and category-to-category compare the resulting text. Checked core admission re-resolves the exact category name and projection, so a hand-built mismatched projection is rejected.
- A nonempty authored-order list of nonrepeatable ordinary Enumeration fields now reaches the checked flat `AtLeastOne`/`No`/`NotAll` value-list quantifiers with exact stored/category projections and a nonempty literal-token side. Exact repeated field/projection references are rejected, while stored and category access on the same field remain distinct. Every literal is admitted against the union of the selected projected domains, the core re-derives every model-owned projection, and runtime maps all relevant fields in order into the existing typed side before the shared quantifier dispatcher applies its per-cell relevance rule. The full-validation row gate delegates to `ValueListQuantifier.canFireOnEmpty`, so only `No` evaluates an all-blank row and fires OMISSION.
- The same checked quantifiers now retain an explicit field-valued right-side variant. Both nonempty authored-order sides reuse exact stored/category operands; combined exact duplicates are rejected, while different projections of one field remain distinct. No display or domain-containment gate is invented between Enumeration declarations. Empty, formally unavailable, and nonrelevant right-side cells therefore reach the established quantifier-specific poison, skipping, and OMISSION clauses without a second evaluator.
- Ordinary nonrepeatable String field lists now use the same textual operand and `ResolvedValueListSide` owners for literal and field-valued `AtLeastOne`/`No`/`NotAll`. Literal tokens are unrestricted decoded String values; field-valued sides must remain String-homogeneous and exact field references are unique across both sides. Checked reads preserve one-pass CRLF normalization, semantic empty and exact formal causes before the common quantifier applies its existing empty, poison, and OMISSION rules. The shared token-list core keeps String and Enumeration admission separate instead of weakening projected-domain checks.
- Scalar String and Enumeration `FieldValueIncludedInValueList` and `FieldValueNotIncludedInValueList` authoring reuse the same checked textual operand and literal-side admission. Included lowers exactly to one-field `AtLeastOne`; NotIncluded lowers to one-field `NotAll`, never empty-firing `No`. String values use the normalized cache, Enumeration literals retain stored/category domain checking, present member/nonmember results stay VALUE, and an empty or formally unavailable subject makes neither scalar form fire without a second membership evaluator.
- Scalar String membership also accepts a nonempty field-valued right side through the same checked homogeneous-String and combined exact-reference boundary as the multi-field quantifiers. A present empty member cannot match Included; for NotIncluded it makes a present outside witness fire OMISSION because the member remains fillable. A formally unavailable member is skipped by Included and poisons NotIncluded. Subject and member reads share normalized ingestion and partial relevance.
- Scalar Enumeration membership now accepts the kernel's nonempty field-valued right side through the same projection-bearing operands and combined exact-reference rule as multi-field quantifiers. Stored or category projections may occur on either side, different projections of one field remain distinct, and no display/domain-containment gate is invented. Empty and unavailable subjects suppress both operators; empty and unavailable members preserve the shared Included-skip versus NotIncluded-OMISSION/UNKNOWN distinctions.
- Checked nonrepeatable Number value lists now use a distinct typed adapter into the existing type-indexed Number quantifier domain. Scalar Included/NotIncluded admits only a nonempty list of signed integral literals; its field-valued variant and multi-field `AtLeastOne`/`No`/`NotAll` require nonempty homogeneous Number sides and reject duplicates across all exact references. The checked core re-admits every declaration and rejects fractional literal atoms plus the kernel-illegal multi-field/literal shape, while differing declared scales and signedness remain legal because runtime equality uses the shared scale-19 normalization.
- Number list reads deliberately do not reuse direct comparison's empty substitution: a semantic empty contributes no atom, an unavailable cell retains its exact cause, and only a present Number contributes its rational value. Partial validation removes nonrelevant operands before reads while retaining their existence outside the ordinary resolved side. The common quantifier therefore owns empty-subject suppression, empty-member no-zero behavior, all-empty `No` OMISSION, formal and relevance poison, and operator-specific skipping without a second numeric comparison or scan.
- One checked repeatable Number route resolves a general nested plain or narrow-authored-filtered starred fields side against a nonempty list of direct nonrepeatable Number value fields. Static lowering validates the model once, resolves combined direct duplicates before Number certification, and retains the existing checked star/filter owners. Full evaluation preserves canonical leaf order and hierarchical omitted-tail state, applies `Having` before target classification, checks direct members through their declaration policies, and delegates the two ordinary resolved sides unchanged. Partial evaluation skips any locally visible `Having` before topology or reads; an unfiltered source filters both sides per cell and delegates their classified views to the same asymmetric quantifier dispatcher.
- Checked nested String-star routes cover both a starred fields side against nonempty literal tokens and one direct nonrepeatable String field against a starred values side, with an optional checked `Having` on either starred operand. Both validate their exact String declarations and reuse the same topology, declaration-owned checking, normalized token cell, hierarchical omitted-tail state, per-cell partial relevance, and separate wildcard/ancestor extent fact before the common quantifier dispatcher. Full validation filters before classification and retains the unconditional OMISSION marker; partial validation skips the complete filtered leaf before topology or operand reads. Generic over-limit, relevance, and filtered selection live at the checked star-path/correlation owners; Number delegates through them.
- One checked nested Enumeration-star fields side accepts nonempty literal tokens from its exact stored or named-category domain. The proof-bearing source ties that projection to the starred field's model-owned ordinary closed declaration, then reuses the kind-neutral topology/filter/relevance routes and the existing Enumeration-to-token classifier before the shared quantifier dispatcher. Category projection stays positional and many-to-one; empty category cells, invalid stored tokens, hierarchical omitted tails, `Having` polarity, and partial relevance retain their existing distinctions.
- The complementary route pairs one exact direct nonrepeatable Enumeration projection with one exact starred values projection. Both sides are independently re-admitted against the model, so different declaration domains and stored/category choices remain legal without a display or containment gate. Full and partial evaluation reuse the flat direct side, starred topology/filter/relevance side, and common asymmetric quantifier; values-side emptiness, invalidity, extent relevance, and `Having` therefore retain their distinct `No`/`NotAll` effects.
- Full and partial flat and nested-star routes share one `ResolvedValueListQuantifierSide` and `ValueListQuantifier.evalClassified` mechanism. `AtLeastOne` skips nonrelevance on both sides, `No` treats either side as UNKNOWN, and `NotAll` skips fields-side nonrelevance but treats values-side nonrelevance as UNKNOWN after a present subject exists. Formal causes remain in `ValueListCell`; nonrelevance is retained separately so downstream aggregate and scan consumers cannot accidentally inherit validation-only poison.
- Trusted laws cover runtime projection, empty/unavailable/VALUE-only behavior, identity-label classification, pair/profile conflict symmetry, String admission, both rejection classes, and overall admission symmetry.
- The separate type-indexed Number/canonical-token value-list capsule preserves explicit present/empty/unknown cells, declared-tail and `Having` metadata, and distinct `AtLeastOne`, `No`, and `NotAll` clauses

#### Evidence

- Canonical §8 prose and pinned kernel source choose the static and runtime accounts.
- Accepted [`SPEC-2026-07-20-14`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-14--enumeration-direct-field-comparability-uses-effective-display-remapping) records a12-dmkits revision `20230e40` and its identity-label, conflict-direction, and compatible-mapping controls.
- Seventeen checked-declaration cases separate empty/duplicate stored domains, unknown/incomplete/duplicate localized mappings, category name/arity/token failures, complete multilingual and identity-label declarations, exact stored projection, exact category lookup, and many-to-one category output. Five laws retain validation, display, direct-comparability, stored-projection, and exact category-domain ownership.
- Fourteen checked-observation cases separate both equality operators, stored/category literal admission, exact category names, checked construction, stored equality/mismatch, many-to-one category equality, physical/value emptiness, out-of-domain stored values, wrong kinds, and preceding raw rejection. Five laws preserve empty, accepted/rejected stored classification, exact present-value delegation, and pre-comparison UNKNOWN for an invalid stored token.
- Thirteen Enumeration value-list cases separate stored/category projection, category-preserved physical emptiness, both stored empty routes, out-of-domain and preceding formal causes, matching category/`No`/`NotAll` outcomes, and the three quantifiers' distinct response to an invalid member. Five laws prove exact empty, unknown, present, invalid-domain, and side-cell transport through the shared resolved classifier.
- Ten checked Enumeration RNU cases separate stored/category components, empty and exact causes, many-to-one VALUE clusters and deterministic peers, optional-empty OMISSION, invalid-row exclusion/UNKNOWN, and distinct stored-token non-duplicates. Five laws preserve empty, unknown, present, same-projected-token, and invalid-domain transport through the shared classifier.
- Fourteen flat-integration cases separate stored and category lowering, stored equality and mismatch, category many-to-one firing, invalid stored and wrong-kind UNKNOWN, empty presence, relevance masking, bad literal/category/operator rejection, and missing or invalid model metadata. Declaration-owned raw admission and irrelevant-leaf suppression have direct laws, while the general elaboration laws retain exact model/field ownership.
- Twelve direct-field integration cases separate String/String and both operand orders of String/Enumeration and Enumeration/Enumeration lowering, equality and inequality fires, invalid-domain UNKNOWN, empty suppression, two-leaf relevance, compatible display profiles, both static rejection classes, and ordering-operator rejection. Generic proof obligations show that both model-derived operands are admitted and partial evaluation depends only on their reads; direct textual equality has an operand-swap law.
- One five-way static case locks category exemption against String, display-bearing Enumeration, and category operands in both directions; the universal category-admission law and the existing symmetry law cover the full resolved class. Eight flat cases separate category-to-stored-Enumeration execution from the otherwise rejected direct pair, category-to-String and category-to-category lowering, exact-name rejection, non-Enumeration rejection, and fail-closed projection mismatch.
- Nineteen checked flat value-list cases separate exact one- and two-field lowering, authored order, a match from the second field, per-cell relevance with a retained witness, direct-domain and stored/category union admission, exact duplicate rejection, stored and many-to-one category matches, direct and category-hop `No` versus `NotAll` on a blank row, stored/category literal-domain failures, empty field/value-list rejection, and non-Enumeration rejection. Trusted laws retain the ordered side projection, quantifier-owned empty-row capability, relevance masking, and the universal clean-empty `No` OMISSION result.
- Ten additional field-valued separators cover exact category/stored lowering and matching, all three empty-value-side outcomes, unavailable-value poison, values-side per-cell relevance, empty right-side rejection, combined exact-duplicate rejection, and stored/category distinctness. A trusted specialization fixes field-valued side resolution to the same ordered classifier used on the left.
- Twelve checked String list separators cover exact literal and field-valued lowering, CRLF-normalized matching on either side, all three empty-right outcomes, all three unavailable-right outcomes, both sides of per-cell relevance, both empty-side authoring errors, combined exact-duplicate rejection, String/Enumeration surface separation, and fail-closed mixed-kind core admission. A trusted ingestion law connects the String list cell directly to the same normalized checked cache used by comparison and `Length`. Maintained a12-dmkits `ValueListQuantifierDiffTest` and `EntityValueListDiffTest` triangulate the corresponding literal and field-valued String runtime families against the kernel.
- Five scalar membership cases lock Included lowering and member firing, NotIncluded nonmember firing, both empty-subject no-fire results, and many-to-one category membership. A universal theorem fixes the empty result for both scalar operators and therefore separates NotIncluded from `No`.
- Eleven scalar field-valued Enumeration separators cover both exact lowerings, projected match/outside results, empty and unavailable subject suppression, empty-member Included suppression versus NotIncluded OMISSION, unavailable-member skip versus poison, empty-side and exact-duplicate rejection, different projections of one field, category projection on the member side, and wrong-base-type rejection. They reuse the generic token empty-subject and present/empty-member laws plus the existing partial-agreement theorem rather than restating operator-specific proofs.
- Six scalar String membership separators cover both exact lowerings, normalized Included and present-outside NotIncluded firing, empty and unavailable subject suppression for both operators, empty literal-list rejection, and Enumeration-kind rejection. The shared empty-subject theorem now belongs to the textual token core, while a String ingestion law supplies the exact empty-cell premise. Kernel scalar runtime source fixes the result; maintained a12-dmkits `ValueListDiffTest` triangulates present cases and cross-engine empty behavior, and revision `e18aeabe` corrects its formerly stale empty-case name and comment.
- Six field-valued scalar String separators cover both exact lowerings, normalized match and present-outside firing, empty-member Included suppression versus NotIncluded OMISSION, unavailable-member skip versus poison, empty right-side rejection, and combined subject/member duplicate rejection. Two kind-polymorphic resolved laws lock the single-present/single-empty outcomes without restating them for String.
- Twenty-three checked Number separators cover scalar literal and field-valued lowering, present match and outside results, empty/unavailable subject suppression, exact rational field equality across different declarations, empty-member no-zero behavior, multi-field authored order and second-field matching, all-empty and partially filled polarity, fields- and values-side per-cell relevance under all three quantifiers, empty-side/type/combined-duplicate errors, mismatched declaration metadata, fractional literal atoms, and the rejected multi-field/literal core shape. The generic laws now prove full-relevance specialization and that any partial firing survives restoration of masked cells, while retaining typed projection, empty-row capability, relevance masking, scalar empty suppression, and clean-empty `No` OMISSION. Kernel scalar and multi-field source plus a12-dmkits' `ValueListDiffTest`, `EmptyValueLawsTest`, and `ValueListQuantifierStarDiffTest` triangulate the represented runtime boundary; this repository retains no portable Number-list observation.
- Nine checked nested-star Number cases separate fields-side malformed handling for all three operators, hierarchical omitted-tail polarity, direct empty and malformed value members, filter-before-target classification with OMISSION escalation, fields- and values-side partial relevance under all three operators, concrete-all-rows versus wildcard extent, `Having` skip before malformed topology/reads, and duplicate-before-kind diagnostics. Ten trusted laws retain direct-value order/metadata, uniqueness, plain and filtered star delegation, exact full and partial quantifier dispatch, partial side shape, masked-read independence, and early `Having` skip. Maintained a12-dmkits `ValueListQuantifierStarDiffTest` plus accepted [`SPEC-2026-07-22-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-09--partial-starred-value-list-extent-requires-wildcard-coverage) triangulate full validation and the wildcard-versus-concrete partial-extent account; project-local retained evidence remains pending under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).
- Twelve checked nested-star String cases separate normalized matching, malformed-cell asymmetry on both sides, hierarchical omitted-tail polarity, direct-subject membership, all three partial-relevance outcomes with masked-read independence, fields- and values-side concrete-all-rows versus wildcard extent, filter-before-classification and OMISSION escalation on both sides, complete filtered-rule partial skip, empty literal admission, and exact kind rejection. Fifteen String laws plus two shared correlation laws retain exact String identities, direct-field model admission, checked filter environments, literal/direct side shape, canonical partial order/tail state, extent classification, read locality, filter-before-classification, and exact full/partial delegation for both shapes. Kernel source plus maintained a12-dmkits `ValueListQuantifierStarDiffTest`, `EntityValueListDiffTest`, `ValueListQuantifierHavingDiffTest`, and accepted [`SPEC-2026-07-22-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-09--partial-starred-value-list-extent-requires-wildcard-coverage) triangulate the full and partial-extent routes; project-local retained evidence remains pending under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).
- Eight checked nested-star Enumeration cases separate many-to-one category matching, category-preserved emptiness, invalid stored-token poison, hierarchical omitted-tail polarity, filter-before-projection with OMISSION escalation, filtered-rule partial skip, relevance-before-projection, exact selected-domain literal admission, category identity, nonempty literals, and kind rejection. Six laws retain exact declaration ownership, nonempty admitted literals, shared filtered selection, exact full/partial dispatch, and early partial skip. Kernel source plus the maintained a12-dmkits star and Enumeration-category matrices triangulate the two reused mechanisms separately; their combined repeatable-Enumeration route remains `external evidence pending` under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).
- Six complementary starred-values separators cover independent direct/starred category projections, matching across different domains, values-side empty OMISSION for both `No` and `NotAll`, invalid-member poison, concrete-witness versus unknown-extent partial behavior, early filtered-rule skip, and exact direct category rejection. Four additional laws retain model re-admission and exact full/partial/skip delegation. The composition remains `external evidence pending`; no existing maintained differential combines a repeatable Enumeration projection with the field-valued values-side shape.
- A fresh 42-file artifact-only Enumeration readback recovered declaration admission, stored/category and direct-field comparison, scalar and multi-field literal/field-valued membership, partial relevance, row gating, exact empty/UNKNOWN polarity, one proved operand-swap rewrite, and the unsafe projection/domain/side rewrites without sibling, kernel, web, Git-history, prior-report, or unlisted-file access. Execute, narrow Transform, and Explain pass at the checked nonrepeatable boundary; authored full evaluation and shipment do not.
- a12-dmkits revision `9c8da06e` can evaluate the category expression shape, but its adapter readback accepts category-to-literal and category-to-category only and rejects the kernel-legal category-to-plain-field form. [`SOURCES.md`](SOURCES.md) records this inbound peer gap and exact routes; it is not a local semantic uncertainty or an outbound spec-feedback item.
- Accepted [`SPEC-2026-07-22-05`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-05--enumeration-field-list-literals-use-the-union-of-selected-domains) records a12-dmkits revision `e18aeabe`: its typed authoring now matches the selected-domain union and field-valued combined-reference rules, while maintained tests against both kernel strategies pin the category-hop empty separator. Lean's shared checked projection was already aligned: category access preserves EMPTY before token projection, so `No` fires OMISSION and `NotAll` remains non-firing.
- This compile-closed field-kind integration adds 277 nonblank Lean lines, slightly above the preferred capsule target: the new closed constructors require exhaustive updates across the existing flat, requiredness, partial-relevance, custom-context, String-admission, reference-adapter, proof, and conformance owners. Splitting those updates would leave a non-exhaustive or bypassable raw-checking boundary; no new AST, evaluator, module family, protocol surface, or infrastructure was introduced.
- The checked flat value-list integration adds 274 nonblank Lean lines, 24 above the preferred target. The closed condition constructor must land atomically with row eligibility, relevance/refinement, rule-reference tracking, model re-admission, and executable locks, while the new consumer triggers the required consolidation of three formerly repeated Enumeration projection fields into one shared operand. Splitting those responsibilities would retain a duplicate projection representation or an unguarded core arm; the capsule adds no evaluator, fold, module family, protocol surface, or infrastructure.
- The String extension adds 331 nonblank Lean lines because the second real token-kind consumer closes the shared textual field/value-side representation and therefore requires exhaustive updates to core admission, elaboration, partial agreement, rule-reference traversal, reference error mapping, trusted specializations, and both old and new conformance matrices. Splitting the generic consolidation from its String consumer would temporarily create an unused abstraction or leave the closed core incomplete; no evaluator, fold, protocol, process, or infrastructure was added.
- The checked Number integration expands the Lean estate by 394 nonblank lines (404 added, 10 removed) across one typed adapter, its three already-established authoring consumers, exhaustive closed-core and trust-registry updates, seven laws, and twenty-two separators. Scalar literal membership, scalar field-valued membership, and multi-field field-valued quantifiers share the same side representation and combined-reference invariant; splitting them would leave an intentionally partial closed constructor or repeat the same admission/relevance closure. The second exact-reference consumer consolidates String and Number duplicate detection while preserving their distinct admission and diagnostics. The capsule reuses the established numeric normalization and quantifier evaluator and adds no AST family, fold, protocol, process, or infrastructure.
- The focused runtime matrix currently has one kernel route plus peer triangulation
- a broader catalog smoke case exercises both kernel routes.
- This repository retains no portable §8 observation

#### Excluded boundary and gap links

- **Implemented internally through checked flat integration; external evidence pending:** ordinary stored/category-to-literal equality and inequality now run through the general nonrepeatable model, relevance, and full-evaluation boundary.
- Direct-field static comparability and runtime equality are integrated for nonrepeatable ordinary String and closed Enumeration fields.
- Multi-field String and Enumeration literal-token and field-valued `AtLeastOne`/`No`/`NotAll`, multi-field Number field-valued quantifiers, scalar String/Enumeration/Number literal Included/NotIncluded, and scalar String/Enumeration/Number field-valued membership are checked through the same flat model with per-cell partial relevance. Nested starred Number-fields/direct-Number-values plus both single-star String and Enumeration list directions own checked expansion, optional `Having`, per-cell partial relevance, and wildcard/ancestor extent before that evaluator. Mixed String/stored-Enumeration `FirstFilledValue` shares the checked token entity-list shape across direct/plain-star/filtered-star slots and keeps order-aware relevance distinct from all-rows aggregates; multiple/mixed starred value-list operands and whole-rule orchestration remain open.
- Remaining declaration profiles and kind/value-list consumers are indexed by [`SG8`](SEMANTICS-GAPS.md#sg8--enumeration-and-value-list-completion); repeatable expansion and checked RNU topology are [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), path/`@From` legality is [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion), and retained evidence is [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage). Number multi-field literal syntax is intentionally unrepresentable because the kernel checker rejects that form.

### §9 — repetition and iteration

#### Owners

- [`Semantics/Iteration.lean`](../A12Kernel/Semantics/Iteration.lean)
- [`Semantics/StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean)
- [`Semantics/StarAddressing.lean`](../A12Kernel/Semantics/StarAddressing.lean)
- [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean)
- [`Semantics/RepetitionNotUnique.lean`](../A12Kernel/Semantics/RepetitionNotUnique.lean)
- [`Semantics/EnumerationRepetitionNotUnique.lean`](../A12Kernel/Semantics/EnumerationRepetitionNotUnique.lean)
- [`Semantics/Correlation.lean`](../A12Kernel/Semantics/Correlation.lean)
- [`Semantics/CrossLevelCorrelation.lean`](../A12Kernel/Semantics/CrossLevelCorrelation.lean)
- [`Elaboration/SingleGroup.lean`](../A12Kernel/Elaboration/SingleGroup.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Elaboration/StarPath.lean`](../A12Kernel/Elaboration/StarPath.lean)
- [`Elaboration/StarGroup.lean`](../A12Kernel/Elaboration/StarGroup.lean)
- [`Elaboration/StarNumber.lean`](../A12Kernel/Elaboration/StarNumber.lean)
- [`Elaboration/RepetitionNotUnique.lean`](../A12Kernel/Elaboration/RepetitionNotUnique.lean)
- [`Elaboration/NumberEntityList.lean`](../A12Kernel/Elaboration/NumberEntityList.lean)
- [`Elaboration/NumericStar.lean`](../A12Kernel/Elaboration/NumericStar.lean)
- [`Elaboration/NumericAggregate.lean`](../A12Kernel/Elaboration/NumericAggregate.lean)
- [`Elaboration/FirstFilledValue.lean`](../A12Kernel/Elaboration/FirstFilledValue.lean)
- [`Proofs/Iteration.lean`](../A12Kernel/Proofs/Iteration.lean)
- [`Proofs/StarCompleteness.lean`](../A12Kernel/Proofs/StarCompleteness.lean)
- [`Proofs/StarAddressing.lean`](../A12Kernel/Proofs/StarAddressing.lean)
- [`Proofs/GroupPresence.lean`](../A12Kernel/Proofs/GroupPresence.lean)
- [`Proofs/RepetitionNotUnique.lean`](../A12Kernel/Proofs/RepetitionNotUnique.lean)
- [`Proofs/EnumerationRepetitionNotUnique.lean`](../A12Kernel/Proofs/EnumerationRepetitionNotUnique.lean)
- [`Proofs/Correlation.lean`](../A12Kernel/Proofs/Correlation.lean)
- [`Proofs/CrossLevelCorrelation.lean`](../A12Kernel/Proofs/CrossLevelCorrelation.lean)
- [`Proofs/SingleGroupElaboration.lean`](../A12Kernel/Proofs/SingleGroupElaboration.lean)
- [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean)
- [`Proofs/StarPathElaboration.lean`](../A12Kernel/Proofs/StarPathElaboration.lean)
- [`Proofs/StarGroupElaboration.lean`](../A12Kernel/Proofs/StarGroupElaboration.lean)
- [`Proofs/StarNumberElaboration.lean`](../A12Kernel/Proofs/StarNumberElaboration.lean)
- [`Proofs/RepetitionNotUniqueElaboration.lean`](../A12Kernel/Proofs/RepetitionNotUniqueElaboration.lean)
- [`Proofs/NumberEntityList.lean`](../A12Kernel/Proofs/NumberEntityList.lean)
- [`Proofs/NumericStarElaboration.lean`](../A12Kernel/Proofs/NumericStarElaboration.lean)
- [`Proofs/NumericAggregateElaboration.lean`](../A12Kernel/Proofs/NumericAggregateElaboration.lean)
- [`Proofs/FirstFilledValue.lean`](../A12Kernel/Proofs/FirstFilledValue.lean)
- [`Conformance/Iteration.lean`](../A12Kernel/Conformance/Iteration.lean)
- [`Conformance/StarCompleteness.lean`](../A12Kernel/Conformance/StarCompleteness.lean)
- [`Conformance/StarAddressing.lean`](../A12Kernel/Conformance/StarAddressing.lean)
- [`Conformance/GroupPresence.lean`](../A12Kernel/Conformance/GroupPresence.lean)
- [`Conformance/RepetitionNotUnique.lean`](../A12Kernel/Conformance/RepetitionNotUnique.lean)
- [`Conformance/Correlation.lean`](../A12Kernel/Conformance/Correlation.lean)
- [`Conformance/CrossLevelCorrelation.lean`](../A12Kernel/Conformance/CrossLevelCorrelation.lean)
- [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean)
- [`Conformance/StarPathElaboration.lean`](../A12Kernel/Conformance/StarPathElaboration.lean)
- [`Conformance/StarGroupElaboration.lean`](../A12Kernel/Conformance/StarGroupElaboration.lean)
- [`Conformance/StarNumberElaboration.lean`](../A12Kernel/Conformance/StarNumberElaboration.lean)
- [`Conformance/RepetitionNotUniqueElaboration.lean`](../A12Kernel/Conformance/RepetitionNotUniqueElaboration.lean)
- [`Conformance/NumericAggregateElaboration.lean`](../A12Kernel/Conformance/NumericAggregateElaboration.lean)

#### Implemented

- Exact ordered selector ↔ relation bridges
- filter-before-consumer laws
- The checked one-group Number-star source classifies each selected row through the same `FlatNumberField.valueListCell` owner used by checked nonrepeatable Number lists. Empty, present Number, wrong-kind, and exact-cause unavailable cells therefore cannot drift between flat membership and repeatable consumers; source construction and consumer scans remain separate.
- The checked unfiltered one-level Number star retains a model-owned positive capacity, binds one exact starred group and direct-child field through the shared one-star resolver, requires the runtime rows to be a contiguous 1-based prefix within that capacity, and constructs the ordered classified cell stream plus omitted-tail state before delegating separately to the existing `Sum`/extrema or prefix-terminating `FirstFilledValue` evaluator.
- Correlated Number/repetition leaves reuse the common `ConditionTree`; one strong-Kleene fold, leaf traversal, and `And`/`Or` structure replace the former private recursive connective mechanism.
- a shared full-environment correlated evaluator/relation bridge
- captured-origin, exact named-level resolution, outer-reference stability, self-match/exclusion, scalar-collapse rejection, and one-group observation-footprint results.
- Resolved RNU consumes caller-supplied ordered rows with complete repetition environments and classified composite keys. It excludes unknown keys, skips all-empty keys, applies scale-19 Number equality and exact normalized-token equality component-wise, retains complete firing clusters in scope order, and projects per-row verdicts before composition.
- Checked nested RNU now constructs those rows from one validated model and the common star topology. A nonempty authored-order composite key may mix distinct Number, ordinary String, and direct stored-Enumeration fields at ancestor-or-equal depths along one group branch; one kind-indexed key sum dispatches to the existing checked Number, normalized String, or checked Enumeration projection without another evaluator. Enumeration key construction reuses the ordinary closed declaration and forces its stored projection because RNU syntax forbids categories. The deepest key group owns row expansion, while each component retains its own repeatable-axis prefix for over-limit checking and per-cell relevance. The default scope reopens the first repeatable group below the rule group, while explicit `@From` must contain every key field and leaves higher bindings to the caller's outer environment. Runtime resolves deepest canonical rows once, filters a row unless every key instance at its own depth is relevant, and delegates unchanged to the resolved RNU relation.
- Its checked-token adapter maps a shared validation observation to present token, optional empty, or exact-cause unknown. Registered custom field rejection therefore excludes the key without losing its project payload or invoking the validator again; relevance exclusion still precedes component construction.
- Laws characterize exact cluster membership, firing, the internal false/unknown refinement, unique cluster identities, and the existence of a genuinely distinct matching peer.
- The separate checked one-star lowering retains explicit group paths, path-derived repeatable ancestry, exact singleton scope, operator-specific scale legality, model-derived raw checking, fail-closed runtime references, and pre-evaluation 1-based/unique candidate validation.
- The separate reopened-star domain recursively checks finite capacity under every actual parent, treats unbounded levels as open, validates positive sibling-unique coordinates, and bridges its structural result into resolved missing potential.
- The general star-topology resolver binds only exact named outer levels above the first star, validates path depth and parent existence across an explicit `Document`, canonicalizes every actual sibling set to its 1-based coordinate prefix independently of storage order, and constructs the existing reopened tree and deepest-level-fastest leaf `Env` stream together. Gaps and duplicates fail closed; over-limit rows stay addressable for later formal classification.
- Field and group terminals share one proof-bearing `CheckedStarPlan`; wildcard legality, first-star selection, deeper-repeatable reopening, and structural path validation therefore have one checked owner.
- Every kind-indexed value-list consumer can classify that one resolved leaf stream through `ResolvedStarTopology.toResolvedSide`; generic laws keep its cells and hierarchical tail projection tied to the same topology.
- The same topology-produced environment stream now has one general resolved validation-`Having` selector. It preserves candidate order, evaluates ordinary references against the complete candidate `Env` and `$` references against the complete captured rule `Env`, drops false and UNKNOWN candidates, and only then invokes the selected Number target reader. Existing one-level and cross-level validation-correlation adapters delegate to that selector rather than retaining parallel keep logic.
- The source-closed authored Number/`CurrentRepetition` filter fragment now lowers conjunction through the same traversal used by the one-group correlation route, but accepts an already-certified general star path. It checks ordinary references against every candidate binding, `$` references against the declaring rule's model-derived captured bindings, equality/inequality scales at each leaf, and requires at least one ordinary reference to reach a level reopened by the operand. Its checked carrier certifies the conjunction-only shape and ties captured levels to the stored declaring group; the checked Number wrapper contains that result and delegates runtime selection unchanged to the established environment selector.
- The resolved group-presence state independently folds admitted content, error, and three-level relevance, then supplies scalar predicates, fixed-list tallies, strict numeric count availability, and parent-filled requiredness.
- A checked full-validation terminal-repeatable group-star source counts the canonical terminal environments without reading descendant cells. That one structural count feeds `NoGroupFilled(G*)`, `AtLeastOneGroupFilled(G*)`, and `NumberOfFilledGroups(G*)`; created-empty and sequential over-limit terminal rows both count as instantiated content.
- Checked-wrapper theorems eliminate structural certificates
- they are not source-to-core semantic preservation

#### Evidence

- The compact validation record privately replays seven uncorrelated iteration observations and publicly binds 12 one-group captured-outer runtime cases plus four static authoring cases.
- They separate selection, origin, malformed/empty filtering, consumer observation order, comparison and scale boundaries, and neighboring rejection classes.
- Kernel source establishes the complete captured index vector
- maintained a12-dmkits RNU dual-route differentials establish duplicate outcomes, invalid exclusion, optional-empty polarity, typed equality, ordinary composition, and peer clusters as triangulation.
- Kernel parser/runtime source establishes direct value-validating key admission plus Number-versus-exact-stored-text equality for all remaining kinds; maintained a12-dmkits code independently uses that two-branch mechanism, but no reviewed wider-kind dual-route differential currently anchors it.
- Five local custom-key cases plus four generic laws lock the accepted, empty, malformed, registered-rejected, and nonrelevant bridge into the existing resolved relation.
- Twelve checked nested runtime example groups separate default cross-level scope, explicit per-parent `@From`, complete-key partial relevance, optional-empty composite polarity, formally invalid key exclusion, exact String clusters, numeric-looking String non-equivalence, mixed Number/String tuples, direct Enumeration duplicates versus category collisions, Enumeration domain failure, mixed Enumeration/Number tuples, and ancestor-key discrimination over deepest rows. Seven neighboring static failures lock duplicate-key, one-branch paths, supported-kind, prepared-custom-String, whole-key containing references, unrelated references, and missing-default-reference admission. Sixteen laws expose all three typed adapters, terminal ownership, per-key path prefixes, checked scope certificates, canonical row construction, and exact resolved-evaluator delegation.
- This repository retains neither an RNU observation nor the cross-level diagonal/off-diagonal separator
- kernel `FALSE_OR_UNKNOWN` intrinsically collapses invalid versus clean nonfiring RNU leaf truth.
- Accepted [`SPEC-2026-07-19-16`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-16---correlation-captures-every-named-outer-repetition-level) records the peer diagonal/off-diagonal complete-capture lock
- it does not become project-local portable evidence.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` adds dual-kernel/peer IF193 group-state and IF194 nested-tail separators
- neither is retained as project-local portable evidence.
- Local nested-addressing cases separate shuffled storage from canonical repetition order, outer-level binding from same-level reopening, complete from missing per-parent capacity, named-level binding from positional reuse, valid over-limit retention, gaps, orphan rows, and stream/tree order agreement.
- One nested filtered-Number case combines parent equality with child order over a two-level capture, separates the two parent branches, and makes every dropped target malformed; two generic laws characterize exact selected membership and make target classification observationally local to selected environments.
- Authored-filter cases reach the same nested selector, exercise end-to-end candidate-Number versus captured-ancestor-Number routing, accept an uncorrelated reopened-level repetition filter, and reject a bound-only filter, ordinary field and repetition references to a sibling scope, and a `$` field unavailable from the captured rule environment. Public theorems expose conjunction-only authored shape, environment well-formedness, reopened-level dependence, and exact runtime delegation from the checked wrapper.
- Group-star cases separate zero from a created-empty terminal row, both legal validation polarities from the numeric zero/count result, bound-outer from reopened-outer paths, shuffled nested storage from canonical terminal cardinality, sequential over-limit content from omission, and static/runtime topology failures.
- [`EVIDENCE.md`](EVIDENCE.md) owns the exact retained inventory and observable support

#### Excluded boundary and gap links

- **Implemented; wider cross-level and RNU additions remain external evidence pending.** Coverage includes one-group runtime/lowering, normalized firing rows, resolved RNU, checked nested mixed Number/String/stored-Enumeration RNU construction, document-derived general star topology after checked path planning, reopened-star completeness, and resolved group-presence projections.
- Correlation carries complete candidate/captured environments; RNU defines one branch-independent relation and complete peer clusters before verdict composition.
- The low-level RNU evaluator remains total over caller-supplied rows outside the checked typed route without a kernel-correspondence claim. The authored route accepts Number, ordinary String, and direct ordinary Enumeration keys along one branch. Temporal, Boolean/Confirm raw-spelling identity, and prepared custom String keys remain open because the current parsed `RawCell` boundary does not retain the kernel's exact internally stored text for those cases. Every checked key projects the deepest row environment to its declaration-owned repeatable prefix before invoking its existing classifier, so a future SG1 document view need not rediscover ancestor addressing.
- Remaining key kinds, the one-leaf-per-condition restriction, whole-rule placement, branch-associated references, and peer-pointer/message projection are indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction), [`SG8`](SEMANTICS-GAPS.md#sg8--enumeration-and-value-list-completion), [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion), and [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).
- Accepted [`SPEC-2026-07-22-10`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-10--repetitionnotunique-compares-every-non-number-key-by-stored-text) and reviewed revision `27afb555` lock the complete source-established admission/equality contract and wider-kind controls. Lean's remaining temporal and Boolean/Confirm work is a raw stored-text representation gap, not a missing semantic fact.
- The checked whole-rule correlation elaborator and public protocol remain one-group only; both it and the internal general-star filter surface admit only Number/`CurrentRepetition` comparisons and conjunction. Resolved `CorrelatedHaving` supports `Or`, but authored `Or` remains outside this capsule.
- Wider filter leaves, rule-wide partial orchestration beyond the checked aggregate/value-list/`FirstFilledValue`/RNU leaf routes, nonrepeatable terminal groups below a star, mixed starred/plain group operand lists, descendant-based group presence, and every wider repeated consumer remain indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction), [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), and [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion). The shared checked condition/expression tree, narrow authored nested-Number filter, common direct/plain-star/filtered-star field-list shape, resolved full/partial mixed Number aggregates, mixed Number and String/stored-Enumeration `FirstFilledValue`, nested mixed Number/String/stored-Enumeration RNU, and sole terminal-repeatable group-star count consumers are closed.
- `CheckedStarNumberHavingSource.resolvedValueSide` still receives the runtime captured `Env` from its caller. Static legality names every level that environment may supply, and missing or duplicate bindings fail closed, but construction of one complete runtime rule environment belongs to the reserved general checked-document/result boundary under [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction) and [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).

### §10 — paths and references

#### Owners

- [`Semantics/SemanticIndex.lean`](../A12Kernel/Semantics/SemanticIndex.lean)
- [`Elaboration/SemanticIndex.lean`](../A12Kernel/Elaboration/SemanticIndex.lean)
- [`Proofs/SemanticIndex.lean`](../A12Kernel/Proofs/SemanticIndex.lean)
- [`Proofs/SemanticIndexElaboration.lean`](../A12Kernel/Proofs/SemanticIndexElaboration.lean)
- [`Conformance/SemanticIndex.lean`](../A12Kernel/Conformance/SemanticIndex.lean)
- [`Conformance/SemanticIndexElaboration.lean`](../A12Kernel/Conformance/SemanticIndexElaboration.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/SingleGroup.lean`](../A12Kernel/Elaboration/SingleGroup.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean)
- [`Proofs/SingleGroupElaboration.lean`](../A12Kernel/Proofs/SingleGroupElaboration.lean)
- [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean)
- [`Conformance/Elaboration.lean`](../A12Kernel/Conformance/Elaboration.lean)
- [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean)

#### Implemented

- Resolved exact-text or normalized-Number key lookup over unique canonical entries plus an unavailable-column marker
- validation clean-match-before-column-invalidity, computation column-invalidity-before-match, clean no-match/matched-empty equivalence, selected-target phase observation, nonmatching-target irrelevance, signedness-aware empty-Number polarity, shared validation/computation `FieldFilled`/`FieldNotFilled`, and indexed field-fill tally/ordered-slot projections
- checked one-group literal-Number key/Number target construction from the group's declared direct-child Number index field and unique positive raw rows; declaration-owned formal checking, empty-key requiredness, all-participant duplicate exclusion, numeric-value identity, exact-text non-collapse, and phase delegation share the existing owners
- model validation including field/group hierarchy separation and path-derived repeatable-scope coherence
- order-independent unique ID/path lookup
- shared parent walking
- explicit named parent turning points across field, group, and later-star paths; the authored label checks only the group reached by the `..` count and never searches another ancestor
- corrected bare declaring-group → flag-gated model-wide unique resolution
- explicit repeatable-group path declarations
- exact one-star binding
- ambiguity, wrong group/scope, nested false-singleton scope metadata, and unsupported surface forms fail closed
- unique declaration and raw-policy coherence theorems

#### Evidence

- Maintained a12-dmkits indexed-read differentials at accepted revision `71775c9905b057831253348c31ce39e321e61889` establish match/no-match, phase precedence, selected-target invalidity, and presence as triangulation, but this repository retains no portable semantic-index observation.
- Kernel `IndexFieldCache.normalizeValue` establishes Number-value versus non-Number exact-stored-text key identity. Pending [`SPEC-2026-07-23-08`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-23-08--semantic-index-number-keys-compare-by-normalized-numeric-value) requests the missing a12-dmkits Number-spelling separator; the checked Lean route is internally closed but remains external evidence pending.
- Kernel `CheckRelativeUpImpl` and maintained a12-dmkits `NamedAncestorPathDiffTest` establish that a matching explicit turning-point name is semantically transparent, while a mismatch is `MVK_INVALID_ENTITY`; Lean locks the corresponding flat-field, later-star, and group-valued routes but retains no local portable path observation.
- The full invalid-column matrix is strongest for Number keys while the canonical-token generalization is source-grounded.
- The compact validation record privately replays parent-relative, absolute, local-precedence, model-wide fallback, and ambiguity cases.
- Its four public static correlation associations retain code/class pairs for missing inner iteration, equality-scale mismatch, and a sibling-group reference plus acceptance for the ordering control
- acceptance does not establish runtime firing rows.
- [`LF6`](LEAN-FINDINGS.md#lf6--bare-name-resolution-is-local-or-global-not-an-ancestor-walk) records the bare-name correction

#### Excluded boundary and gap links

- **Implemented for four narrow structured/resolved subsets:** non-repeatable flat paths, one absolute-or-direct-child-relative group-qualified star/correlation shape, one checked single-group literal-Number semantic-index construction route, and resolved semantic-index Number value/kind-independent presence/fill consumers.
- Parent-relative and bare forms remain outside the public correlation operation. Non-Number raw-key construction needs a storage-text owner; field-valued keys, nested/multiple index levels, general path/parser/renderer, and static-diagnostic closure remain indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction), [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion), and repeatable lookup under [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).

### §11 — computations

#### Owners

- [`Semantics/ComputationCondition.lean`](../A12Kernel/Semantics/ComputationCondition.lean)
- [`Semantics/ComputationFillQuantifier.lean`](../A12Kernel/Semantics/ComputationFillQuantifier.lean)
- [`Semantics/StringComputation.lean`](../A12Kernel/Semantics/StringComputation.lean)
- [`Semantics/StringApplication.lean`](../A12Kernel/Semantics/StringApplication.lean)
- [`Semantics/StringCascade.lean`](../A12Kernel/Semantics/StringCascade.lean)
- [`Semantics/StringAlternatives.lean`](../A12Kernel/Semantics/StringAlternatives.lean)
- [`Semantics/NumericComputationResult.lean`](../A12Kernel/Semantics/NumericComputationResult.lean)
- [`Semantics/NumericStoredNumber.lean`](../A12Kernel/Semantics/NumericStoredNumber.lean)
- [`Semantics/NumericTarget.lean`](../A12Kernel/Semantics/NumericTarget.lean)
- [`Semantics/NumericApplication.lean`](../A12Kernel/Semantics/NumericApplication.lean)
- [`Semantics/NumericDependency.lean`](../A12Kernel/Semantics/NumericDependency.lean)
- [`Elaboration/NumericComputation.lean`](../A12Kernel/Elaboration/NumericComputation.lean)
- [`Elaboration/StringComputation.lean`](../A12Kernel/Elaboration/StringComputation.lean)
- [`Elaboration/GeneratedComputationValidation.lean`](../A12Kernel/Elaboration/GeneratedComputationValidation.lean)
- their counterparts under [`Proofs/`](../A12Kernel/Proofs.lean), and their counterparts under [`Conformance/`](../A12Kernel/Conformance.lean)

#### Implemented

- Direct presence conditions distinguish clean not-true from exact-cause poison and evaluate recursive `And`/`Or` left-to-right.
- The seven computation field-fill quantifiers consume one ordered `filled | empty | uninstantiated | poison cause` stream. They retain the range fork, operator-specific stopping, two-stage composites, exact reached poison, and unread suffixes.
- trusted laws preserve the range fork, representative deciding-prefix equations, zero/one/two distinction, selected reached-poison separators, and observable read order.
- The operation-neutral selector returns no-match, the first selected operation, or first reached poison
- selection ends before operation evaluation.
- An optional resolved common precondition lowers by left-conjoining it to every guarded alternative, preserving payload order; holding preserves selection, clean not-true yields no-match, and poison aborts before an alternative-specific guard.
- One resolved String table composes that selector once with the existing expression/target/delta step
- clean no-value, target rejection, and poison from the selected operation are terminal, a holding head makes every suffix irrelevant through operation evaluation, and common false/poison decides before guard or operation reads.
- Checked String-operation lowering resolves nonrepeatable copy and `RangeAsString` leaves plus one ordinary nonrepeatable target against the same validated flat model, retains the target's exact declaration-owned line-break/min/max policy, rejects direct self-reference plus wrong-kind/raw/custom/repeatable targets, preserves literal/range/concatenation tree order, checks raw cells with the same model, and delegates expression and target evaluation to the existing semantic owners.
- One operation-parametric generated table represents every nonempty table as either one optionally guarded alternative or two-or-more fully guarded alternatives, without fabricating a true guard. Literal Number and checked numeric-expression payloads share cardinality, first-match selection, declaration order, validation-only tolerance, and the target-gate/common/body constructor. Generated validation omits an absent singleton guard, left-folds wider mismatch tables in declaration order, and places the common guard once below `FieldFilled(target)` and above the complete mismatch body.
- The checked guard traversal rejects the exact computed target ID in common and every alternative condition before phase lowering, retaining common versus one-based alternative position. Each checked numeric operation has already rejected that target throughout its expression and retained scale-warning choice; generated validation preserves the resolved tree under model-wide nonrepeatable admission, rejects a payload certified for a different target, and lowers every guarded mismatch through the shared numeric comparison and mixed whole-rule path.
- Generated numeric validation narrows checked `RangeAsNumber` and ordinary Enumeration/category `FieldValueAsNumber` atoms directly into the validation atom algebra without reconstructing or re-resolving their surface paths. Model-wide nonrepeatable source admission, normalized range or selected-token evaluation, missing-source polarity, derived conversion scale, and the computed target mismatch therefore remain the same checked expressions rather than generated-rule exceptions.
- Tolerance metadata is erased before first-match computation selection; strict alternatives retain exact-scale admission while tolerance alternatives use the established scale-gate bypass.
- Its overlap case demonstrates that selecting the stored first result does not imply generated-validation silence
- phase-specific poison/unknown, String empty/nonempty presence, and data-derived polarity remain visible.
- The separate String and Number slices keep checked expression identity, expression result, stored form, target outcome, delta, exact application, and downstream dependency meaning distinct without claiming a scheduler or document mutator

#### Evidence

- The project-reviewed [root-String compact bundle](../evidence/kernel-30.8.1/captures/string-computation-v1/semantic-observations.json) retains 22 clean/target-check observations
- the producer-certified [direct-cascade bundle](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/semantic-observations.json) and typed [`StringCascadeProjection.lean`](../A12Kernel/Evidence/StringCascadeProjection.lean) retain five cascade observations.
- The type-neutral V2 apply mechanism is source-grounded and triangulated by a12-dmkits IF126's String matrix.
- The field-fill scan is source-grounded and separately exercised by maintained a12-dmkits dual-kernel-route differentials for all seven operators, but this repository retains no portable field-fill observation.
- Kernel `CalculationUtils.expandCommonPrecondition`, `NormalisierteBerechnungsFormHelper` target-reference checking, a12-dmkits' direct common-first evaluator, and its separate common-outside-disjunction generated-validation construction ground the checked guard account; superseded [`SPEC-2026-07-21-06`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-06--computations-reject-references-to-their-own-target) records that the peer already rejected target references in operations, alternative guards, and the common guard at the audited basis. This repository retains no portable common-precondition or self-reference observation.
- a12-dmkits `RangeCoercionDiffTest` at originating revision `0f2a5687822797ed7b4f897b0320793ae22eb7b6` supplies maintained dual-kernel-route ASCII evidence for `RangeAsString` selection/overshoot and `RangeAsNumber` digits-only/fallback-zero behavior; `FunctionFillPolarityDiffTest` from revision `f9e591a54aa4c319baa42dfb76610d7571be5ecc` covers missing-source grow-only polarity. Normalized CRLF, target/generated-validation integration, poison, and non-ASCII representability remain internally locked but externally pending.
- No retained project-local observation exercises direct presence/connectives, field-fill scans, alternative selection or selected-operation terminality, generated guarded-alternative validation, numeric expression/target/delta/application/dependency, mixed domain/poison order, or the newline family
- those surfaces remain `external evidence pending`

#### Excluded boundary and gap links

- **Implemented narrowly and partially externally calibrated:** one nonrepeatable recursive direct-presence fragment
- all seven field-fill predicates over a caller-supplied already-expanded ordered slot stream
- first-match selection with resolved String selected-operation/target/delta integration
- optional common-precondition expansion over that already-guarded table
- one checked nonempty generated-rule table shared by literal Number and checked numeric-expression payloads, with an optionally guarded singleton or guarded two-or-more alternatives, an optional checked common precondition, per-alternative tolerance, and explicit model-wide nonrepeatable expression admission
- one String target and direct cascade
- and one already-resolved Number expression → ordinary-or-warning-suppressed stored form → target → delta → exact application → cause-free dependency chain.
- Shared checked guards and generated validation are closed. Scheduling/state/target breadth is indexed by [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition), family-specific operations by [`SG5`](SEMANTICS-GAPS.md#sg5--numeric-authoring-and-target-completion), [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), and [`SG7`](SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion), repeatable construction by [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), and retained evidence by [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).

### §12 — validation and polarity

#### Owners

- [`Core.lean`](../A12Kernel/Core.lean)
- [`Semantics/FieldFillQuantifier.lean`](../A12Kernel/Semantics/FieldFillQuantifier.lean)
- [`Semantics/ValidationFillQuantifier.lean`](../A12Kernel/Semantics/ValidationFillQuantifier.lean)
- [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean)
- [`Semantics/StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean)
- [`Semantics/NumericFillability.lean`](../A12Kernel/Semantics/NumericFillability.lean)
- [`Semantics/NumericComparison.lean`](../A12Kernel/Semantics/NumericComparison.lean)
- [`Semantics/NumericTolerance.lean`](../A12Kernel/Semantics/NumericTolerance.lean)
- [`Semantics/Condition.lean`](../A12Kernel/Semantics/Condition.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Semantics/ValidationRule.lean`](../A12Kernel/Semantics/ValidationRule.lean)
- [`Semantics/PartialValidation.lean`](../A12Kernel/Semantics/PartialValidation.lean)
- [`Elaboration/NumericValidation.lean`](../A12Kernel/Elaboration/NumericValidation.lean)
- [`Elaboration/ValidationCondition.lean`](../A12Kernel/Elaboration/ValidationCondition.lean)
- [`Elaboration/ValidationRule.lean`](../A12Kernel/Elaboration/ValidationRule.lean)
- [`Elaboration/GeneratedComputationValidation.lean`](../A12Kernel/Elaboration/GeneratedComputationValidation.lean)
- their counterparts under [`Proofs/`](../A12Kernel/Proofs.lean), and their counterparts under [`Conformance/`](../A12Kernel/Conformance.lean)

#### Implemented

- The verdict algebra preserves VALUE/OMISSION precedence and unknown
- Flat and numeric-expression validation leaves now share one resolved connective tree, Boolean empty-row fold, field-reference traversal, and exact left-to-right short-circuit evaluator. Existing flat conditions remain a type alias over their atomic leaves, and universal preservation laws prevent the shared embedding from changing their verdict or references.
- numeric fillability supplies directional polarity across direct comparisons, admitted arithmetic including resolved power, and fixed tolerance.
- The seven resolved unfiltered field-fill quantifiers classify instantiated observations, combine adjacent ranges by count addition, preserve declared/instantiated/mixed ranges, treat unavailable cells as neither filled nor empty, and expose fired polarity versus exact collapsed `FALSE_OR_UNKNOWN`; semantic-index reads now supply both validation tallies and ordered computation slots through the same phase lookup
- trusted laws separate the two `NotExactlyOne` firing regions, the mixed predicate from `NotAll`, and validation collapse from computation poison.
- Resolved group presence independently folds admission, error, and three-level relevance, then gives scalar predicates, fixed-list predicates, strict numeric count, and parent-requiredness their consumer-specific projections.
- The reopened-star completeness boundary recursively derives structural tail missingness per actual parent and feeds the existing resolved-side disjunction without changing operator directions.
- The checked resolved-rule boundary preserves silent distinctions and retains a structured message plan until a fired verdict renders and attaches exact address, error code, severity, polarity, and text.
- Generated-computation validation and mixed ordinary whole rules reuse the same post-fire boundary and outcome. One generic nonempty table now carries literal or checked-expression payloads; its optional common condition sits once outside the complete mismatch disjunction, guards and operations reject direct computed-target self-reference, ERROR severity does not fix message polarity, and tolerance metadata cannot affect computation selection. Expression mismatches use the same mixed tree under explicit model-wide nonrepeatable admission.
- Flat partial evaluation first skips a rule marked as containing `Having`, then applies the separate error-field gate and relevance-aware leaf evaluator for unfiltered rules.

#### Evidence

- Retained validation observations separate ordinary polarity and malformed connective outcomes but do not establish checked whole-rule assembly, generated guarded-alternative validation, error-code/severity independence, complete message rendering, hidden silent distinctions, or field-fill quantifiers.
- Maintained a12-dmkits multi-route quantifier differentials ground the seven unfiltered formulas and broader filter behavior, but this repository retains no portable field-fill observation.
- Direct ordering, arithmetic fillability, tolerance, partial relevance, mixed flat/numeric condition integration, generated-rule details, and the label/value display refinements remain source/test anchored and project-locally `external evidence pending`.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` additionally triangulates IF193 group relevance/availability and IF194 nested-star aggregate polarity across both kernel strategies and the peer interpreter, without adding project-local portable evidence.
- a12-dmkits revision `6039fd3e` and the three kernel code-generation templates ground IF202's method-entry skip for filtered partial rules; this repository retains no portable filtered-rule observation.
- Same-field alias polarity is source-inferred
- mixed formal-invalid/domain precedence is an explicit Lean refinement

#### Excluded boundary and gap links

- **Implemented internally for the named clauses:** all seven unfiltered field-fill operators over a caller-supplied resolved tally, with generic instantiated-observation classification, tally composition, and one resolved indexed-operand projection
- resolved scalar/list/count/relative-required group-presence projections over caller-supplied group slices
- hierarchical structural-tail derivation over a caller-supplied reopened tree
- reduced fixed-right Number/String-Length validation
- known arithmetic and fixed-tolerance polarity
- one same-group nonrepeatable two-expression comparison and one resolved mixed flat/numeric connective tree after checked leaf elaboration
- one exact nonrepeatable structured-plan rule message rendered only after firing, shared by checked flat and mixed flat/numeric whole rules
- one checked nonempty generated rule shared by literal Number and expression-valued payloads, split between an optionally guarded singleton and guarded two-or-more table, with an optional common condition on the same message boundary; expression operands preserve cross-group computation scope
- and one ordered nonrepeatable partial-validation filter gate, error-field gate, and relevance-aware leaf evaluator.
- General document/context construction is indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction), repeatable streams/relevance/rows by [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), scheduling/orchestration by [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition), messages by [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration), and custom-condition placement by [`SG11`](SEMANTICS-GAPS.md#sg11--custom-condition-checked-orchestration). Shared condition and generated-rule integration is closed.

### §13 — message interpolation

#### Owners

- [`Semantics/ValidationRule.lean`](../A12Kernel/Semantics/ValidationRule.lean)
- [`Proofs/ValidationRule.lean`](../A12Kernel/Proofs/ValidationRule.lean)
- [`Conformance/ValidationRule.lean`](../A12Kernel/Conformance/ValidationRule.lean)

#### Implemented

- One total one-pass renderer consumes ordered, already-decoded parts.
- Plain text, resolved field-name input, and resolved field-value input remain separate constructors, so replacement bytes are never reparsed
- a decoded `$$` is ordinary dollar text at this boundary.
- Provider output wins exactly
- otherwise a nonempty model label precedes the debug display.
- Missing or empty display values use the exact format-supplied default.
- Checked flat and generated-computation-validation rules retain the structured plan and render it only after firing
- both silent verdicts are independent of every plan input.
- Laws cover provider priority, empty fallback, append/order composition, opaque nonempty values, and post-fire gating

#### Evidence

- Maintained a12-dmkits controls at revision `20230e403fa085c782534025f890669a975999a8` make both kernel routes agree on the scale-two `DocumentV2` dot default under US/German locales and on raw-CRLF message display while evaluation reads normalized LF
- JVM and Node lock the admitted provider/default/opacity policy.
- Accepted [`SPEC-2026-07-21-04`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-04--message-format-default-follows-the-actual-documentv2-profile) records the correction to the earlier locale implication.
- `$$`, repeated order, richer token families, untested presentation routes, and project-local portable observations remain source-derived or open, so correspondence remains `external evidence pending`

#### Excluded boundary and gap links

- **Implemented internally, narrow:** parser-independent rendering after reference/display resolution and fired-only integration for checked nonrepeatable flat/mixed rules plus generated literal-Number and checked numeric-expression computation validation.
- The remaining authored-token, lookup/provider, display/format, repeatable/index/category, custom-condition, and orchestration boundary is indexed by [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).

### §14 — custom conditions

#### Owners

- [`Semantics/CustomCondition.lean`](../A12Kernel/Semantics/CustomCondition.lean)
- [`Proofs/CustomCondition.lean`](../A12Kernel/Proofs/CustomCondition.lean)
- [`Conformance/CustomCondition.lean`](../A12Kernel/Conformance/CustomCondition.lean)

#### Implemented

- A resolved invocation carries four abstract channels unchanged: effective data view, full-versus-partial relevant entities, the complete formal-invalid payload, and the current error pointer.
- A pure total reached-leaf oracle maps true to fired VALUE and false to not-fired, never UNKNOWN or OMISSION
- the leaf is empty-row eligible.
- Trusted non-laws show that purity alone supplies neither data locality nor formal-invalid monotonicity

#### Evidence

- Kernel Java/TypeScript call paths, modern wrappers, and maintained a12-dmkits dual-route/JVM/Node controls establish the invocation and empty-eligibility account
- no project-local portable observation

#### Excluded boundary and gap links

- **Implemented internally, narrow:** one successfully registered, already-reached pure callback leaf.
- Registration/name resolution, host call discipline, concrete invocation construction, checked lowering, messages, and whole-rule orchestration are indexed by [`SG11`](SEMANTICS-GAPS.md#sg11--custom-condition-checked-orchestration).
- Correspondence remains `external evidence pending`

## Cross-clause implementation notes

The §5/§11 numeric-computation entry retains each atom's declaration and rejects non-Number declarations before reads.

- Evaluation follows the lowered tree left-to-right, so rewriting may change the first poison reached.
- Invalid integral power reaches the shared target/dependency domain-failure path.
- Concrete authoring is indexed by [`SG5`](SEMANTICS-GAPS.md#sg5--numeric-authoring-and-target-completion), and portable evidence by [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).

### Resolved `FirstFilledValue`

- Owners: [`Semantics/FirstFilledValue.lean`](../A12Kernel/Semantics/FirstFilledValue.lean), [`Elaboration/NumberEntityList.lean`](../A12Kernel/Elaboration/NumberEntityList.lean), [`Elaboration/TokenEntityList.lean`](../A12Kernel/Elaboration/TokenEntityList.lean), [`Elaboration/FirstFilledValue.lean`](../A12Kernel/Elaboration/FirstFilledValue.lean), [`Elaboration/TokenFirstFilledValue.lean`](../A12Kernel/Elaboration/TokenFirstFilledValue.lean), [`Elaboration/NumericStar.lean`](../A12Kernel/Elaboration/NumericStar.lean), [`Proofs/NumberEntityList.lean`](../A12Kernel/Proofs/NumberEntityList.lean), [`Proofs/FirstFilledValue.lean`](../A12Kernel/Proofs/FirstFilledValue.lean), [`Proofs/TokenFirstFilledValue.lean`](../A12Kernel/Proofs/TokenFirstFilledValue.lean), and their focused [`Conformance/`](../A12Kernel/Conformance.lean) locks.
- Boundary: the common checked nonempty field entity-list shape is certified separately for Number and for mixed String/ordinary stored Enumeration; the two family adapters share one kind-neutral order-aware prefix scan while retaining distinct exhausted identities and phase projections across §3, §8, §10, and §11.
- The scan stops at the first present value or first unavailable cell: an invalid prefix makes validation UNKNOWN and computation poison, an invalid suffix is unread, an empty prefix retains the amount but changes validation from fixed/VALUE to fillable/OMISSION, and an empty suffix is irrelevant.
- An all-exhausted explicitly empty, marked-uninstantiated, or filtered-empty Number selection supplies the fillable zero. The combiner retains an omitted tail separately for that exhausted identity, but a reached resolved selection with no concrete cell is already a sticky not-given prefix and makes a value selected from a later slot fillable.
- Each reached slot contributes its `Having` marker before its cells. That marker survives into a later selected value, while a terminal earlier slot hides every later filter and cell.
- `CheckedNumericStarSource` reuses the neutral single-group path, direct-child Number, raw-topology, and checked-context owner before adding positive capacity and contiguous-prefix obligations; it classifies cells through the shared model owner, while the shared scan-entry mechanism turns an empty resolved selection into the runtime wrapper's not-given prefix independently of its hierarchical omitted-tail marker.
- Number lowering resolves every reference first, rejects repeated direct non-wildcard fields, applies the more-than-one-field-or-star gate, certifies Number, and derives one union/max declaration scale. Token lowering reuses the same shape gates, then admits ordinary String and stored Enumeration in one exact-token family while excluding category projection. Wildcarded plain and filtered slots remain independently consumed authored occurrences.
- The kind-neutral scan's enter/step mechanism serves both Number and token resolved evaluation. Their checked adapters keep consumer-specific relevance and filter traversal separate: the continuation-capable workers return accumulated state when one star falls through, resolve each star, evaluate each reached filter, check each reached cell's relevance, and sample each reader only after every earlier slot has fallen through.
- Number exhaustion supplies fillable zero. String/Enumeration exhaustion supplies no value; validation suppresses comparison and computation projects clean no-value. A selected exact token retains empty/no-row/filter prefix polarity for validation while computation retains the token alone.
- Trusted laws prove prefix/suffix and slot termination, ordered filter carry, no-row-selection prefix behavior, empty identities, both projections, both family-specific projection non-laws, nonrelevance before either target reader, and present-head suffix/read independence.
- Checked-source laws retain required multiplicity and direct-reference uniqueness. Number cases retain the established scale, wildcard, all-exhausted-zero, and both-phase matrix. Token cases separate cross-kind selection, String normalization, exact stored-token identity, no-value exhaustion, malformed suffix and topology invisibility, empty/no-row/filter prefix polarity, formal-prefix termination, per-cell relevance, and duplicate/cardinality/kind diagnostics.
- Kernel source and maintained a12-dmkits `FirstFilledValue` differentials establish the shared ordered mechanism and the existing single-kind behavior. Mixed String/stored-Enumeration admission is source-grounded and internally locked but awaits focused dual-kernel handback; this repository retains no portable observation, and exact formal-cause carriage is an internal refinement.
- Group operands, Boolean/Confirm, temporal, DateRange, computation-phase mixed-slot consumption, and broader repeatable consumers remain indexed by [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction) and their family gaps. General transition/target integration remains under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition), and retained evidence under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage). The general checked-document/result boundary is intentionally not defined here.
- Accepted [`SPEC-2026-07-20-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-09--firstfilledvalue-observes-only-filters-before-termination) records the peer encounter-order correction and focused locks. Rejected [`SPEC-2026-07-22-06`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-06--firstfilledvalue-keeps-omitted-tail-distinct-from-an-empty-prefix) records the runtime-wrapper evidence that corrected Lean's source-only omitted-tail inference. Accepted [`SPEC-2026-07-22-07`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-07--ordinary-aggregate-duplicate-checking-skips-wildcarded-operands) records the wildcard-duplicate admission correction and peer locks.

### Resolved Number aggregates

- Owners: [`Semantics/NumericAggregate.lean`](../A12Kernel/Semantics/NumericAggregate.lean), [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean), [`Elaboration/NumericSource.lean`](../A12Kernel/Elaboration/NumericSource.lean), [`Elaboration/StarPath.lean`](../A12Kernel/Elaboration/StarPath.lean), [`Elaboration/StarNumber.lean`](../A12Kernel/Elaboration/StarNumber.lean), [`Elaboration/FieldEntityList.lean`](../A12Kernel/Elaboration/FieldEntityList.lean), [`Elaboration/NumberEntityList.lean`](../A12Kernel/Elaboration/NumberEntityList.lean), [`Elaboration/NumericAggregate.lean`](../A12Kernel/Elaboration/NumericAggregate.lean), [`Elaboration/NumericValidation.lean`](../A12Kernel/Elaboration/NumericValidation.lean), [`Elaboration/NumericComputation.lean`](../A12Kernel/Elaboration/NumericComputation.lean), [`Elaboration/GeneratedComputationValidation.lean`](../A12Kernel/Elaboration/GeneratedComputationValidation.lean), [`Proofs/NumericAggregate.lean`](../A12Kernel/Proofs/NumericAggregate.lean), [`Proofs/NumberEntityList.lean`](../A12Kernel/Proofs/NumberEntityList.lean), [`Proofs/NumericAggregateElaboration.lean`](../A12Kernel/Proofs/NumericAggregateElaboration.lean), [`Proofs/NumericValidation.lean`](../A12Kernel/Proofs/NumericValidation.lean), [`Proofs/NumericComputation.lean`](../A12Kernel/Proofs/NumericComputation.lean), and their focused [`Conformance/`](../A12Kernel/Conformance.lean) locks.
- Implemented: direct `Sum`/`MinValue`/`MaxValue`/Number-valued `NumberOfDifferentValues` lists require at least two distinct resolved nonrepeatable Number fields; duplicate detection precedes type checking and authored order is retained. Ordinary value aggregates derive the maximum contributing declaration scale, while distinct count has integral scale 0. One `ResolvedNumericAggregateFields` source parameterizes the established fold with validation- or computation-phase observations and supplies the shared expression atom, reference traversal, and relevance traversal. Ordinary checked comparison/whole-rule evaluation, numeric computation, and every generated-validation alternative consume that same atom; no aggregate-only comparison, evaluator, or scale gate exists.
- Implemented: `ValueListCell.scanPresent` skips empty cells, stops at the first reached unavailable cell, and applies a caller-owned left-to-right step. Extrema select exact present amounts without a synthetic zero. `Sum` begins at zero and applies precision-50 `HALF_UP` addition at every present term; its resolved side retains each selected and uninstantiated declaration's signedness. Any missing source permits growth after a present total, exactly a missing signed source permits shrinkage, every all-empty Sum/extremum route is both-directionally fillable zero, and `Having` makes an available result both-directionally fillable. Number distinct count reuses the established scale-19 equality, counts filled representatives once, uses grow-only zero for an all-empty or incomplete unfiltered selection, and becomes both-directionally fillable only after a reached filter.
- Implemented: the common checked Number entity list admits mixed direct, nested plain-star, and filtered-star slots. It rejects only repeated direct fields, so every repeated wildcard occurrence resolves and contributes again. One ordered aggregate scan stops before later topology/filter/target reads after the first reached unavailable cell, appends cells and declaration-specific missing metadata in authored order, and delegates once to the same Sum/extrema/distinct-count folds. Full validation consumes every slot. Partial validation returns a distinct rule-level filtered skip before any read, requires concrete relevance for direct fields and wildcard/ancestor extent coverage for each reached star, preserves nonrelevance outside formal causes, and otherwise consumes the identical topology-derived side. Cases separate repeated plain and filtered stars, mixed staged order, both extrema, normalized distinct identity, count missing/filter polarity, non-adjacent direct duplicates, concrete-all-rows versus wildcard/ancestor relevance, early filtered skip, and unavailable/nonrelevant prefixes before malformed later topology.
- Implemented: `SumOfProducts` has a distinct checked pair because its semantics are row-aligned rather than a concatenated entity-list fold. Both operands resolve through `CheckedStarNumberSource`; admission requires two same-group Number fields, an unrestricted star only at the lowest repeatable level, and one identical model-derived `StarPath`. The pair resolves that topology once and reads both declarations in each canonical environment. Empty cells become declaration-sensitive zero operands, each row multiplication and running addition uses precision 50, first formal unavailability wins left-to-right, and any hierarchical omitted tail overrides successful validation polarity to both directions. Result scale is the sum of both declaration scales. Full validation accepts raw or caller-supplied checked cells; partial validation requires all-rows coverage for both field paths before reading either; the standalone computation projection ignores required-only emptiness and turns other formal failures into poison. Filters are statically unrepresentable. Cases separate cross-pairing, staged order, empty arithmetic polarity, omitted tails, first cause, required validation/computation divergence, poison, both-field partial relevance, kind/group/lowest-star admission, and scale.
- Implemented: aggregate atoms participate in plain arithmetic and the source-established direct aggregate rounding/`Abs` forms. Both wrappers run after the common aggregate fold; rounding preserves its directional metadata, while `Abs` transforms that metadata from the folded sign. Aggregates do not inherit operand-list `Min`/`Max` wrapper admission. Target self-reference is checked across every aggregate source, while computation erases validation-only fillability only after the common aggregate result is known.
- Implemented: `CheckedNumericStarSource` separately resolves one exact finite star through the existing group/path owner, requires positive declared capacity, rejects duplicate, noncontiguous, and over-capacity runtime rows, and maps the instantiated prefix through the same checked Number-cell classifier. Its structural-tail theorem characterizes an open side exactly by a short prefix. The older checked-row `NumberFold` deliberately projects only amount or cause, and `FirstFilledValue` retains its distinct prefix-terminating scan.
- Proofs and cases: generic scan laws cover availability, all-empty preservation, and first-cause termination; operator laws cover identity, fixed/tail results, per-source signedness, homogeneous embedding, normalized duplicate collapse, metadata separation, filter escalation, staged singleton product, left-first product unavailability, and tail override. Aggregate-delegation, shared-path, and scale laws connect checked sources to the established folds. Partial laws lock direct relevance before classification, all-rows star nonrelevance before target classification, and filter skip independence from every runtime input. Separators cover staged order, row alignment, declaration-specific polarity, extrema empty skipping, both aggregate identity classes, scale-19 distinctness, phase poison, result scale, direct-round versus scalar-wrapper admission, cardinality, duplicate-before-kind and same-group diagnostics, target self-reference, reference/relevance traversal, ordinary whole-rule emission, and all-alternative generated validation.
- Evidence: this boundary is internally complete at levels 1–2 for direct nonrepeatable lists, the finite one-level adapter, ordinary full/partial mixed direct/general-star Number `Sum`/extrema/distinct-count lists, and standalone checked full/partial/computation-result `SumOfProducts` at the resolved aggregate-leaf boundary. Accepted [`SPEC-2026-07-20-15`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-15--all-empty-number-aggregate-identity-is-both-directionally-fillable) and [`SPEC-2026-07-21-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-02--number-sum-preserves-encounter-order-staged-precision-and-missing-declaration-polarity) record the Sum/extrema all-empty, encounter-order, staged-precision, and missing-declaration corrections. Accepted [`SPEC-2026-07-22-07`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-07--ordinary-aggregate-duplicate-checking-skips-wildcarded-operands) and a12-dmkits revision `d82260d87de0c3e4576895b665819d205756f857` establish repeated plain/filtered wildcard admission and the consumed-twice Sum separator. Kernel `NumberOfDifferentValuesCombiner`, `VkBigDecimal.equals`, `RuntimeController.combineFeldListe`, and `RuntimeController.summeVonProdukten`, plus maintained a12-dmkits aggregate laws/differentials at reviewed revision `83dd514f9283b9f62dbe6ee6f238e5c67a00e9c6`, establish distinct-count identity/uncertainty, `SumOfProducts` admission/row pairing/empty behavior, and the all-rows partial gate. These are inbound facts already owned by a12-dmkits, so no feedback ledger entry is created. Project-local retained correspondence remains pending under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).
- Excluded/next: `NumberOfDifferentValues` date-like overloads, group operands, rule-wide filter discovery, error-field/global-augmentation orchestration, computation-phase mixed entity-list consumption, and whole-expression/target integration of repeatable sources remain under [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction), [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion), and [`SG5`](SEMANTICS-GAPS.md#sg5--numeric-authoring-and-target-completion). Wider numeric and temporal aggregate operation/target breadth remains under SG5 and [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion); messages remain under [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).

### String/Enumeration distinct count

- Owners: [`Semantics/NumericAggregate.lean`](../A12Kernel/Semantics/NumericAggregate.lean), [`Semantics/ValueList.lean`](../A12Kernel/Semantics/ValueList.lean), [`Elaboration/FieldEntityList.lean`](../A12Kernel/Elaboration/FieldEntityList.lean), [`Elaboration/TokenEntityList.lean`](../A12Kernel/Elaboration/TokenEntityList.lean), [`Elaboration/TokenDistinctCount.lean`](../A12Kernel/Elaboration/TokenDistinctCount.lean), [`Proofs/TokenDistinctCount.lean`](../A12Kernel/Proofs/TokenDistinctCount.lean), and [`Conformance/TokenDistinctCount.lean`](../A12Kernel/Conformance/TokenDistinctCount.lean).
- Implemented: one common checked entity-list shape resolves direct, nested plain-star, and filtered-star operands before family checking. The token family admits ordinary String and stored Enumeration together, excludes category projection, compares the checked evaluated String/stored token exactly, consumes repeated wildcard occurrences independently, and reports the integral scale 0. Full validation preserves authored order, hierarchical tail state, filter encounter, empty grow-only uncertainty, and first formal cause. Partial validation returns early filter skip, checks direct relevance and star all-rows coverage before reads, and then uses the same fold. Caller-supplied `CheckedCell`s keep prepared custom String observations representable without resampling a validator.
- Evidence and proof: laws fix exact duplicate collapse, common cardinality, direct uniqueness, integral scale, phase projection, checked-star delegation, and relevance-before-read. Cases separate cross-kind token equality, String CRLF normalization, String and Enumeration stars, omitted tails, formal-cause order, filters, concrete-versus-wildcard partial relevance, filtered skip before malformed topology, shape/kind diagnostics, repeated wildcard consumption, and scale. Kernel `NumberOfDifferentValuesCombiner<VkString>` plus maintained a12-dmkits String aggregate cases at reviewed revision `83dd514f9283b9f62dbe6ee6f238e5c67a00e9c6` establish the selected account; these are inbound facts already owned upstream, so no feedback ledger entry is created. Project-local retained correspondence remains pending under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).
- Excluded/next: date-like distinct count remains blocked on exact format-family admission and temporal identity, including TIME, plus correction of the peer check/evaluator gap recorded in [`SOURCES.md`](SOURCES.md). Group expansion, whole-rule/global partial orchestration, computation-phase filtered or mixed entity-list integration, target integration, and general checked-document construction remain with SG1, SG2, SG4, SG6, and SG9.

### Reopened-star structural completeness and addressing

- Owners: [`Semantics/StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean), [`Semantics/StarAddressing.lean`](../A12Kernel/Semantics/StarAddressing.lean), [`Elaboration/StarPath.lean`](../A12Kernel/Elaboration/StarPath.lean), [`Elaboration/StarGroup.lean`](../A12Kernel/Elaboration/StarGroup.lean), [`Elaboration/StarNumber.lean`](../A12Kernel/Elaboration/StarNumber.lean), [`Elaboration/StarNumberValueList.lean`](../A12Kernel/Elaboration/StarNumberValueList.lean), [`Elaboration/NumberEntityList.lean`](../A12Kernel/Elaboration/NumberEntityList.lean), [`Elaboration/NumericStar.lean`](../A12Kernel/Elaboration/NumericStar.lean), [`Proofs/StarCompleteness.lean`](../A12Kernel/Proofs/StarCompleteness.lean), [`Proofs/StarAddressing.lean`](../A12Kernel/Proofs/StarAddressing.lean), [`Proofs/StarPathElaboration.lean`](../A12Kernel/Proofs/StarPathElaboration.lean), [`Proofs/StarGroupElaboration.lean`](../A12Kernel/Proofs/StarGroupElaboration.lean), [`Proofs/StarNumberElaboration.lean`](../A12Kernel/Proofs/StarNumberElaboration.lean), [`Proofs/StarNumberValueList.lean`](../A12Kernel/Proofs/StarNumberValueList.lean), [`Proofs/NumberEntityList.lean`](../A12Kernel/Proofs/NumberEntityList.lean), [`Proofs/NumericStarElaboration.lean`](../A12Kernel/Proofs/NumericStarElaboration.lean), [`Conformance/StarCompleteness.lean`](../A12Kernel/Conformance/StarCompleteness.lean), [`Conformance/StarAddressing.lean`](../A12Kernel/Conformance/StarAddressing.lean), [`Conformance/StarPathElaboration.lean`](../A12Kernel/Conformance/StarPathElaboration.lean), [`Conformance/StarGroupElaboration.lean`](../A12Kernel/Conformance/StarGroupElaboration.lean), [`Conformance/StarNumberElaboration.lean`](../A12Kernel/Conformance/StarNumberElaboration.lean), [`Conformance/StarNumberValueList.lean`](../A12Kernel/Conformance/StarNumberValueList.lean), and [`Conformance/NumericAggregateElaboration.lean`](../A12Kernel/Conformance/NumericAggregateElaboration.lean).
- Boundary: IF194's structural decision, checked model/path lowering, general document-topology construction, unfiltered and checked-authored-filtered nested Number streams, the all-rows relevance gate, the common checked direct/plain-star/filtered-star Number entity list, checked mixed-slot Number `FirstFilledValue` with order-aware per-cell relevance, resolved full/partial mixed-slot Number aggregates, checked full/partial nested-star Number value lists with direct Number value fields, and full terminal-repeatable group-star count consumers.
- `ReopenedStarDomain` contains only reopened repeatable levels
- every actual child row stays beneath its actual parent, carries its 1-based coordinate, and recursively owns the next reopened level or selected leaf.
- Its executable well-formedness check requires positive, sibling-unique coordinates but permits over-limit rows.
- A finite level is structurally closed exactly when its actual count reaches the cap and every actual child subtree is closed
- an absent cap is unbounded and always open.
- The traversal is linear in the supplied tree and never constructs the declared Cartesian domain.
- `StarPath.resolve` derives that tree from `Document.instantiatedRows`, validates exact row depth, parent existence, positive contiguous sibling prefixes, and named outer bindings, then emits leaf environments in ascending lexicographic repetition order with the deepest level changing fastest. Storage encounter order is unobservable at this boundary; valid over-limit rows remain in the stream.
- `elaborateStarFieldPath` validates the model, resolves the exact field declaration, derives axes and capacities from its canonical repeatable ancestry, and lowers per-group wildcard markers to the first reopened axis. Parent navigation may precede later starred segments, while a wildcard on a nonrepeatable group, no wildcard, an unstarred repeatable level below the first wildcard, zero capacity, and incoherent model ownership fail closed.
- `elaborateStarPathPlan` is the proof-bearing shared plan used by both checked field and terminal-repeatable group paths. The group consumer counts the same topology's terminal environments directly, so row presence remains structural and cannot drift into descendant-cell presence.
- `elaborateStarNumberSource` adds exact Number-kind metadata, resolves the checked plan through the sole topology owner, and classifies each canonical leaf through the existing declaration-owned scalar and Number value-list boundary. Any over-capacity coordinate in either a bound or reopened ancestor replaces ordinary scalar findings with `overRepetition`; the selected cell is unavailable rather than consumed as a value.
- `CorrelatedHaving.selectEnvironments` applies a shared-tree numeric/repetition validation filter to those canonical leaves with distinct complete candidate and captured environments. `elaborateStarNumberHavingSource` lowers the narrow authored filter against the certified path, rejects unavailable origin-specific scopes and filters that never reach a reopened level, and packages the result with the checked Number source. Its resolved route maps the declaration-owned target reader only over retained environments and records filter presence even when none survive.
- `RelevantEntityPattern` retains the public path-aligned wildcard/concrete distinction for two operator-specific decisions. `coversAllRows` requires one target-or-ancestor entity that wildcards every repeatable path level it names; the union of every concrete leaf does not become a wildcard. `coversCell` instead matches each concrete topology environment by prefix and coordinate, so separate concrete entities may cover separate reached cells. The all-rows Number adapter gates before all target classification, while `FirstFilledValue` interleaves the per-cell gate with its shared prefix scan.

- The bridge writes this structural result to `ResolvedValueListSide.hasUninstantiatedTail`
- selected-cell emptiness remains in `cells`, so existing `hasMissingPotential` combines the two without duplicating leaf state.
- Trusted laws characterize leaf and unbounded branches, finite closure, open-child propagation, coordinate-label independence, and both bridge projections.
- Cases separate outer, middle, and leaf omissions, full closure, a bound level above the first star, an unbounded level, invalid coordinate inputs, empty-cell composition, and an unchanged unsigned Sum consumer.
- The first shallow-count implementation failed the middle and leaf cases before recursive correction.
- All-rows relevance cases separate full validation, an exact fully wildcarded field, ancestor-group descent, every actual leaf listed concretely, an incompletely wildcarded nested path, a misaligned index vector, and an unrelated sibling field. Per-cell `FirstFilledValue` cases separate later nonrelevance hidden by a present or unavailable head, earlier nonrelevance, a relevant empty before nonrelevance, and a relevant empty before a relevant value with preserved OMISSION polarity. Laws characterize both existential gates, all-rows nonrelevance before target reads and exact side preservation, per-cell nonrelevance before either reader, and present-head suffix/read independence.

- This is internally complete at levels 1–2 for checked general group-star path lowering, model-independent nested topology resolution, the common tree/stream bridge, unfiltered or narrow-authored-filtered nested Number streams, correlated selection before target classification, all-rows validation relevance, the common checked Number entity-list authoring route, resolved full/partial mixed-slot Number aggregates, mixed direct/star `FirstFilledValue` with lazy per-slot topology, filter, and relevance encounter, checked full and partial nested-star Number value lists against direct Number value fields, and full terminal-repeatable group-star counts.
- Wider authored filter leaves and Boolean surface, computation-filter poison/dependency handling, globals and broader relevance-set admission, other field kinds, nonrepeatable terminal groups below a star, mixed starred/plain group operand lists, partial group relevance, and checked consumers beyond the existing Number and sole group-count routes remain open. The resolver's construction-by-design and bridge laws tie leaves to the stream, while a stronger inductive tree/environment correspondence theorem remains part of [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- The a12-dmkits IF194 tri-engine matrix at revision `7f152509eea76822068955055b0d57d8ed930ca2` is focused external triangulation, but this repository retains no portable observation
- correspondence remains `external evidence pending`.
- Aggregate directions, computation, global augmentation, per-source declaration-metadata construction, messages, and protocol exposure retain their existing boundaries.

### Resolved validation group presence

- Owners: [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean), [`Proofs/GroupPresence.lean`](../A12Kernel/Proofs/GroupPresence.lean), and [`Conformance/GroupPresence.lean`](../A12Kernel/Conformance/GroupPresence.lean).
- Boundary: IF193's product state and consumer projections after descendant scope and relevance are resolved.
- `ResolvedGroupPresenceInput` folds existing checked descendant cells, independently resolved instantiated-row content and structural-error facts, and `noneRelevant`/`partlyRelevant`/`fullyRelevant` coverage.
- A parsed scalar with only duplicate-index marking remains admitted while every other formal cause rejects it as scalar content
- any finding independently marks the group erroneous.
- Instantiated repeatable rows supply content independently of selected cell state and structural error.

- The state drives exact scalar `GroupFilled`/`GroupNotFilled` verdicts, all five fixed-list group predicates, plain multi-group `NumberOfFilledGroups`, and the parent-filled requiredness gate.
- Group-list predicates classify every operand as definitely filled, definitely empty, or unavailable and retain independent decisive witnesses.
- The numeric count is stricter: any erroneous or not-fully-relevant operand makes the whole count unavailable.
- Trusted laws characterize the two scalar firing regions, row and duplicate admission, rejected scalar exclusion, exact tally partition, error absorption into the numeric count, and the requiredness bridge.
- Cases cover malformed-only, admitted-plus-malformed, duplicate index, created and over-limit rows, partial positive/empty, full empty, list availability, strict count availability, and requiredness activation.

- This is internally complete at levels 1–2 only for resolved inputs.
- Descendant/document/group-instance construction and required-rule orchestration are indexed by [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction) and [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction).
- The a12-dmkits IF193 tri-engine matrix at revision `7f152509eea76822068955055b0d57d8ed930ca2` is focused external triangulation, but this repository retains no portable observation
- correspondence remains `external evidence pending`.
- Message and wider validation orchestration are indexed by [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) and [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).

### Checked terminal-repeatable group-star counts

- Owners: [`Elaboration/StarPath.lean`](../A12Kernel/Elaboration/StarPath.lean), [`Elaboration/StarGroup.lean`](../A12Kernel/Elaboration/StarGroup.lean), [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean), [`Proofs/StarGroupElaboration.lean`](../A12Kernel/Proofs/StarGroupElaboration.lean), and [`Conformance/StarGroupElaboration.lean`](../A12Kernel/Conformance/StarGroupElaboration.lean).
- Boundary: full-validation paths whose terminal group is itself repeatable and starred. The caller still supplies the declaring group, document, and any exact outer bindings above the first star.
- Implemented: the shared `CheckedStarPlan` checks wildcard and reopening legality, the canonical `ResolvedStarTopology` supplies each terminal environment exactly once, and one row count drives both admitted group predicates plus `NumberOfFilledGroups`. No descendant cell is read; a created-empty or sequential over-limit row counts, and zero is a valid numeric result.
- Proofs and cases: ancestry is model-derived; zero/successor laws fix both predicate polarities; resolution laws tie every consumer to one topology cardinality. The matrix separates zero/created-empty, nested and bound-outer paths, storage order, over-limit rows, illegal star placement, missing declarations, and malformed runtime topology.
- Evidence: kernel parser/runtime source and maintained a12-dmkits dual-route group-star differentials establish the observable account. This repository retains no portable group-star observation, so correspondence remains `external evidence pending` under [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).
- Excluded/next: partial-validation group relevance, a nonrepeatable terminal group reached below a starred ancestor, mixed starred/plain group operand lists, descendant-derived group presence, filters, and whole-rule orchestration remain under [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction), [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), and [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).

### Resolved Date-range overlap truth and operator scans

- Owners: [`Semantics/DateRangeOverlap.lean`](../A12Kernel/Semantics/DateRangeOverlap.lean), [`Proofs/DateRangeOverlap.lean`](../A12Kernel/Proofs/DateRangeOverlap.lean), and [`Conformance/DateRangeOverlap.lean`](../A12Kernel/Conformance/DateRangeOverlap.lean).
- Boundary: the §6 primitive truth core over admitted `FullDate` endpoints and one flat occurrence stream.
- `DateRangeDirection` keeps inversion explicit
- primitive overlap is symmetric, rejects either inversion, and treats equal/shared endpoints as overlapping.
- The flat any-pair scan preserves occurrences rather than deduplicating values, so a singleton does not pair with itself, two equal positions do, and an internal later pair can fire despite a disjoint head.
- Trusted laws characterize direction and the closed relation, prove symmetry, self-overlap iff ordered, both invalid guards, strict separation, singleton/pair reduction, and duplicate occurrence behavior.

- The matching `DateRangeOverlapOperators` semantics/proofs/conformance modules own the two resolved ordered consuming scans.
- Slots are already classified as skipped or kept
- actual `Having` selection has already occurred, while filter presence remains attached to each operand.
- Any-pair overlap makes that marker sticky only after a kept occurrence is reached and observes the updated marker before checking the current occurrence against the seen prefix.
- Scalar-versus-list exits for a skipped scalar, ignores internal list pairs, leaves no sticky state after a filtered disjoint occurrence, and derives polarity from the first matching list operand only.
- Trusted laws exclude UNKNOWN, establish skipped-filter inertness, bridge the smallest pair and scalar/list shapes to primitive overlap, characterize the high-risk first-match polarity branches, and prove universal firing-to-flat-truth equivalences for both operators.
- Cases separate every corresponding order, shape, multiplicity, and polarity mutation.

- This is still not either complete authored predicate.
- It begins after decoding, formal checking, partial-relevance classification, and actual filter selection
- `skipped` intentionally forgets why a cell does not participate.
- Stored inverted ranges are normally skipped by formal checking, while the pure relation's invalid guard remains a source-grounded total-function defense.
- Accepted [`SPEC-2026-07-20-10`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-10--date-range-overlap-polarity-follows-the-reached-scan) links kernel source and a12-dmkits multi-route reached-scan polarity controls.
- This repository still retains no portable Date-range observation, so correspondence remains `external evidence pending`
- Authored DateRange construction/consumption is indexed by [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion), repeated/filter construction by [`SG2`](SEMANTICS-GAPS.md#sg2--general-repeatable-addressing-and-operand-construction), messages by [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration), and retained evidence by [`SG12`](SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).

### Resolved three-part Date construction and Base-Year Date sources

- Owners: [`Semantics/DateConstruction.lean`](../A12Kernel/Semantics/DateConstruction.lean), [`Semantics/DateConstructionNumeric.lean`](../A12Kernel/Semantics/DateConstructionNumeric.lean), [`Semantics/BaseYearDateSource.lean`](../A12Kernel/Semantics/BaseYearDateSource.lean), and their matching [`Proofs/`](../A12Kernel/Proofs/) and [`Conformance/`](../A12Kernel/Conformance/) modules.
- Boundary: a §6/§12 reason-and-verdict account, its direct numeric consumer, and the floor-free decoded labels used when configured Base Year is consumed by direct date or date-range extraction; this remains narrower than general `Date(...)`.
- After component authoring/checking and a separate all-present calendar decision, `classifyDateConstruction3` combines the three availability states with supplied real/unreal reality and returns real `DateParts`, incomplete, present-but-unreal, or formally unavailable.
- Trusted laws characterize incomplete and UNKNOWN precedence, exact retention of supplied reality, both fired polarities, exact truth complementation, and the full-verdict non-law: `Valid` forgets the incomplete/unreal reason while `Invalid` preserves it.
- The direct numeric component layer selects supplied real day/month/quarter/year values without re-running calendar reality, returns not-given zero for incomplete, fixed zero for unreal, and cause-free unavailability for UNKNOWN. Quarter uses the one-based three-month partition while preserving a zero sentinel.
- Configured Base Year projects to January 1 for direct date/component consumption and to January 1 or December 31 according to range endpoint position. These are decoded `DateParts`, not stored `FullDate` values, so a pre-floor configured year is not incorrectly rejected by the unrelated value floor. Checked direct comparison now consumes either selected endpoint through the existing model-zone exact-instant operand after full-Date component admission.
- Trusted laws establish exact component selection, same-zero/distinct-provenance, unavailable-to-UNKNOWN behavior, true-comparison polarity for all six fixed-right operators, exact Base-Year endpoints, and the endpoint non-collapse law
- executable cases additionally lock one false comparison, Q2 selection, both zero provenances, and a pre-floor Base-Year label.

- Kernel 30.8.1 construction/validity and empty-row eligibility source plus maintained a12-dmkits Date-construction differentials establish the four classifications and selected externally visible outcomes
- the malformed `Valid` and malformed-plus-empty precedence branches are source-established rather than separately differential.
- The maintained “all-empty” differential also fills an unrelated time field, so truly content-empty row eligibility is likewise source-established rather than independently isolated.
- Kernel date-extraction source establishes the quarter formula and Base-Year January/December labels. Maintained a12-dmkits quarter and extraction differentials cover the component family, while its adapter reads Base-Year date/range sources; reviewed peer evaluation still routes range extraction only through a range-valued operand, so Base-Year range execution is an upstream gap rather than local evidence.
- this repository retains no portable Date observation.
- Remaining construction forms, parser bounds, checked cells/gates, nested consumers, and temporal target admission are indexed by [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion) with document integration under [`SG1`](SEMANTICS-GAPS.md#sg1--general-checked-document-construction).
- Direct and range-selected Base-Year Day/Month/Quarter/Year extraction now feeds the shared checked scale-0 numeric atom in both validation and Number computation, preserving the validation constant-expression gate and computation's legal constant-only route.
- Other date differences, compositional temporal no-value propagation, and legacy-calendar identity are indexed by [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion).
- Concrete calendar resolution is deliberately not implemented: kernel 30.8.1 uses a zone-aware hybrid `GregorianCalendar`, while the reusable `CivilDate` account is zone-free and proleptic, and the two accounts have reachable cutover and zone-discontinuity separators.

### `DifferenceInDays` finite-profile closure

- Kernel source counts signed model-zone `Calendar.DAY_OF_MONTH` steps, while the obvious reuse of `CivilDate.unixEpochDay` would impose a zone-free proleptic coordinate.
- Those accounts separate on a Berlin special-hour landing and across a skipped whole date.
- [`LF47`](LEAN-FINDINGS.md#lf47--differenceindays-needs-a-model-zone-calendar-step-account) records both reproduced discriminators.
- Accepted [`SPEC-2026-07-20-08`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-08--differenceindays-counts-model-zone-calendar-steps) records both kernel-route separators and the peer calendar-step reconciliation.
- Lean now enforces the narrower option: the general versioned Berlin profile resolves fresh labels, `Berlin2024Profile` retains only stateful spring day stepping, and `DateTimeDayDifference` counts at most the three landings within that exact slice.
- Ordinary, threshold, reverse-sign, retained-adjusted-clock, elapsed-seconds non-equivalence, and unsupported cross-slice cases form the separating matrix.
- Empty/formal coercion, fillability/polarity, checked lowering, constructed-Date calendar identity, general wall-day landing, and other zones are indexed by [`SG6`](SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion) rather than inferred from this finite profile.

## Reference-process exposure

- The `a12-kernel-reference` executable exposes two disjoint intersections through the normalized [`PROTOCOL.md`](PROTOCOL.md) contract: the public §2/§3/§5/§10/§12 flat slice and the named §9 one-group captured-outer slice.
- [`Reference/Protocol.lean`](../A12Kernel/Reference/Protocol.lean) decodes bounded operation-specific models, paths, conditions or correlated `Having`, sparse flat or row-addressed cells, and row gates/candidates.
- [`Reference/Evaluator.lean`](../A12Kernel/Reference/Evaluator.lean) routes every admitted request through the corresponding existing checked elaborator and evaluator.
- [`Reference/Support.lean`](../A12Kernel/Reference/Support.lean) owns the 0.3.0 identity, finite runtime classifiers, and generated schema-2 support metadata mirrored in [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json).
- Requests have no per-request semantics selector
- the exact binary's `--manifest` plus a binary/release digest identifies the account.
- The internal §7 String-validation and §11 String-computation capsules are deliberately absent from this protocol until separate public capabilities close their transport, diagnostics, checked lowering, and support manifests.

- This process surface adds accessibility and fail-closed protocol assurance, not new kernel correspondence.
- Semantic clauses inherit the evidence statuses above. [`ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) locks transport, deterministic output, diagnostics, exits, fixtures, manifest agreement, and suite controls.
- [`CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) runs one selected suite through the shared bounded relay but does not query a candidate manifest
- neither suite execution nor agreement with Lean transfers proofs or expands evidence.
- Exact current handover material and closure gaps live in the [flat](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation](IMPLEMENTER-KIT-CORRELATION.md) kits.
- A development descriptor is not release closure, and the protocol's exclusion list does not claim to enumerate every unsupported A12 construct.

- The isolated Rust exercise is downstream knowledge-transport history, not added Lean semantic coverage or kernel evidence.
- Its exact implementation identity, accepted seven-mutation outcome, 52/52 generated-differential result, limits, deleted artifact hashes, and recovery revisions are preserved in the [archived historical record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md).
- It adds no semantic clause, support declaration, proof, kernel evidence, or correctness claim outside the historical finite profile.

## Empty-handling coverage rule

- Empty semantics is not complete at field-kind granularity.
- Coverage is clause-shaped and must record field kind, operator and operand position, enclosing consumer, selection/all-empty identity, model-derived field role, row eligibility, validation/computation phase, directional fillability, and observable polarity or store outcome.
- The current §2/§7 validation capsule covers all six direct Number field-to-literal comparisons, Boolean/Confirm equality/inequality, Number/Boolean/Confirm/String presence, direct String equality/inequality, and all four String `Length` ordering operators
- the pure §5 tolerance seam separately accepts two already-resolved numeric operands and their fillability
- the §7/§11 computation capsules cover clean String reads in bare copy and concatenation, final storage, checked ordinary target construction and declaration-owned target classification, and prior-target delta projection.
- Only the resolved semantic-index Number consumer reuses the direct-validation Number projection, and only after its phase-aware lookup has produced a `CellObservation`
- no other resolver is a default for another function, aggregate, lookup, or computation family.
- A generic given/substituted bit is also not a valid numeric default:
  - [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function) records the consuming-clause rule
  - [`LF10`](LEAN-FINDINGS.md#lf10--numeric-polarity-needs-directional-fillability-not-a-given-bit) records the directional correction
  - [`LF24`](LEAN-FINDINGS.md#lf24--direct-number-ordering-uses-the-same-directional-fixed-right-comparison) records the direct-ordering consequence
  - [`LF30`](LEAN-FINDINGS.md#lf30--tolerance-normalizes-operands-independently-and-closes-gaps-directionally) records the tolerance consequence
  - [`LF12`](LEAN-FINDINGS.md#lf12--string-computation-has-expression-store-and-delta-boundaries) records the expression/store refinement
  - [`LF13`](LEAN-FINDINGS.md#lf13--string-target-outcome-delta-and-application-are-separate-boundaries) records the target-outcome/delta/application refinement.

## Current external-evidence gate

- The clause records and cross-clause notes above together own the clause-level classification of which implemented choices are externally replayed, process-associated, partially anchored, or still pending.
- [`EVIDENCE.md`](EVIDENCE.md) owns the exact retained inventory, projection mechanics, provenance, observable support, and claim limits
- capability kits own their derived finite case classifications.
- The compact public bridge now closes exact case/request/projected-response association for the current flat and correlation suites
- it does not add richer hidden kernel state.
- Cross-cutting open obligations remain the legal arithmetic precision witness and every broader fragment excluded in the clause records or cross-clause notes.
- Internal conformance examples remain distinct from differential evidence, and a generated shipment never creates a new kernel observation.

## Trusted theorem surface

- [`A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean) is the trusted theorem root.
- [`scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh) checks proof-root completeness, the named theorem registry, source zones, forbidden dependency directions, and the elaborated logical environment through [`Trust/Environment.lean`](../A12Kernel/Trust/Environment.lean); [`Trust/Adversarial.lean`](../A12Kernel/Trust/Adversarial.lean) exercises the rejection boundary in one nonlogical driver session.
- That environment audit rejects project axioms, unsafe or unclassified opaque/partial definitions, compiler/foreign substitutions, and every axiom dependency except `propext`, `Classical.choice`, and `Quot.sound`
- conformance remains a separate nontrusted executable-check lane.
