# Lean implementation and evidence map

This is the sole detailed coverage index from the project-owned [`spec/`](../spec/) taxonomy to Lean owners, implemented behavior, evidence, and exclusions. Use a12-dmkits' [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) for its peer-project inventory.

The target is kernel **30.8.1**. “Implemented” means executable Lean; “proved internally” means a theorem follows from the chosen definitions. Neither establishes universal kernel correspondence. **External evidence pending** means no retained kernel observation is replayed here.

## Evidence snapshot

- The compact validation record has 49 records for 48 distinct external observations because one directional Number witness is intentionally shared across its public and private halves.
- `lake test` replays the 24 private validation records through typed Lean projections
- `checkReferenceProcess` binds the 25 public records to exact normalized requests and externally supported projected responses.
- These two gates complement each other but are not one 49-case replay.
- Together with the 22 root-String and five direct-cascade private replays, the current `lake test` evidence total is 51.

## Taxonomy by clause

Open only the owning clause and linked cross-clause note. Every clause uses the same compact shape: owners, implemented, evidence, and excluded / next.

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

#### Excluded / next

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

#### Excluded / next

- **Implemented internally, partial; direct ordering external evidence pending:** all six nonrepeatable Number comparisons, Boolean/Confirm/String equality/inequality, six-way temporal field-to-field, field-to-typed-Date-literal, field/`Today`, field/`Now`, and field/`BaseYear` comparison in either operand order, plus numeric field/`BaseYear` comparison and Number/Boolean/Confirm/String/Date/Time/DateTime presence, are executable.
- Direct String supports equality/inequality, plus all four String `Length` ordering operators
- its empty observation retains absent versus present-empty placement at the checked-cell boundary.
- String presence and absolute nonrepeatable requiredness reuse the generic presence/required staging; other String comparisons/functions remain rejected or unimplemented.
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
- The separate reduced String target pass classifies an admitted nonempty root write as accepted or payloadful `ERRORED`, proves no-value and poison bypass for every policy, and fails closed on produced CR/LF until target line-break permission is modeled

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

#### Excluded / next

- **Implemented internally, partial; ingestion external evidence pending:** the reduced boundary distinguishes absent from present-empty before projecting either to the empty phase observation and owns evaluated-String CRLF normalization after scalar text decoding.
- A general `Document → RawCell` bridge, public present-empty transport, group-content derivation, and custom-validator invocation remain open.
- raw storage itself remains outside this reduced account.
- The internal unknown/poison account still relies on source treatment and internal laws.
- Computed String target checking admits only one positive minimum or maximum length over no-line-break text
- no-value/poison bypass, target line-break permission, and ingestion normalization are not externally exercised.
- The rest of the reduced computed-result formal check and contextual findings beyond requiredness remain open

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

#### Excluded / next

- **Implemented internally, partial; focused external observations replayed:** absolute requiredness for nonrepeatable Number/Boolean/Confirm/String fields.
- The parent gate is implemented over an already-resolved group state; checked descendant/group-instance enumeration and wildcardable relevance construction remain open.
- Repeatable ancestor orchestration, index generation, and generated rule identity remain open.

### §5 — numbers and decimals

#### Owners

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
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Elaboration/NumericScale.lean`](../A12Kernel/Elaboration/NumericScale.lean)
- [`Elaboration/NumericExpression.lean`](../A12Kernel/Elaboration/NumericExpression.lean)
- [`Elaboration/NumericValidation.lean`](../A12Kernel/Elaboration/NumericValidation.lean)
- [`Elaboration/NumericComputation.lean`](../A12Kernel/Elaboration/NumericComputation.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Proofs/NumericScale.lean`](../A12Kernel/Proofs/NumericScale.lean)
- [`Proofs/NumericExpression.lean`](../A12Kernel/Proofs/NumericExpression.lean)
- [`Proofs/NumericValidation.lean`](../A12Kernel/Proofs/NumericValidation.lean)
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
- [`Conformance/NumericScale.lean`](../A12Kernel/Conformance/NumericScale.lean)
- [`Conformance/NumericExpression.lean`](../A12Kernel/Conformance/NumericExpression.lean)
- [`Conformance/NumericValidation.lean`](../A12Kernel/Conformance/NumericValidation.lean)
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

#### Implemented

- Signed exact-or-unknown scale, constant expandability, and one shared explicit-suppression gate for the supported exact-scale warning
- authored literals/grouping
- plain authoring-region checks plus exact direct-field root rounding/`Abs` and canonical numeric operand-list `Min`/`Max` admission over direct fields with at most one direct constant
- one order-sensitive division-lowering pass
- precision-50 `+`/`−`/`×`/`÷`, staged power, rounding, absolute value, full-precision ordered extrema, arithmetic domain failure, and directional fillability including the conservative power and Min/Max tie tables
- independent scale-19 normalization
- a checked closed validation dispatch over all six direct ordinary comparison operators and four fixed tolerance ranges, with numeric `BaseYear`, its direct/range-selected date-component extractions, and admitted Date/Time/DateTime field components supported as fixed scale-0 sources in plain arithmetic
- one checked nonrepeatable computation-operation consumer with model-resolved target, Number-field, numeric-`BaseYear`, Base-Year date-component, and admitted temporal-field component sources, shared support for plain arithmetic plus direct Number-field `Round`/`Abs` and direct Number-field/one-constant `Min`/`Max`, default-unsuppressed result-scale admission, explicit warning bypass, nested target-reference rejection, distinct numeric value/domain-failure/inherited-poison evaluation, one-time complete target-policy attachment, and retained proof-coherent target dispatch
- separately proved ordinary and significant-digit-bounded stored-decimal conversions
- and one explicit two-branch target consumer with target classification, change-only delta, exact one-address final application, and cause-free dependency observation.
- Checked validation resolves two same-group expressions over Number fields, numeric `BaseYear`, direct numeric component extraction from direct or range-selected Base-Year date sources, and direct Date/DateTime or Time/DateTime field-component sources, lowers each once, and gates empty rows before reads. At least one actual field remains mandatory, so every source-only or literal-only condition retains the constant-expression rejection.
- Admitted expressions are plain arithmetic including power, direct-field root rounding/`Abs`, or canonical Min/Max over direct fields with at most one direct constant.
- The runtime preserves formal invalidity, domain failure, values, and two-sided fillability. [`LF58`](LEAN-FINDINGS.md#lf58--numeric-operand-list-extrema-combine-exact-selection-with-directional-fillability) owns the extremum constant, selection, scale, and polarity details.
- The explicit warning flag bypasses only equality/inequality scale admission and is runtime-irrelevant.
- Numeric and date-component `BaseYear` sources retain a non-expandable scale-0 summary and fixed runtime fillability. The latter selects direct January 1 or a range endpoint before applying Day/Month/Quarter/Year extraction. Both participate in the existing plain arithmetic and tolerance evaluator; tolerance deliberately bypasses the scale gate, while unaudited Base-Year-bearing `Round`/`Abs`/Min/Max shapes remain fail-closed rather than inheriting field-only admission accidentally.
- Computation reads empty Number or temporal-component sources as zero, resolves every Base-Year numeric source to its fixed context-free amount, preflights declarations before data, preserves the exact formal cause of an unavailable temporal field, preserves domain failure through legal wrappers, and keeps left-to-right poison order. Valid power uses the staged evaluator; runtime-invalid integral power reaches the shared target-invalidating domain failure. The retained warning flag bypasses only result-scale admission and selects the corresponding target branch after evaluation.
- Ordinary stored conversion universally preserves the scale-19 `HALF_UP` amount while retaining `{unscaled, scale}` form. Bounded conversion consumes that pre-rounded canonical amount, preserves it within budget, and otherwise applies the 16-significant-digit scale formula.
- After assignment-scale admission, the ordinary target entry point pads minimum fractional digits and applies the reachable basic Number checks in source order: total digits, signedness, effective integer digits, zero, rendered minimum/maximum length, and inclusive numeric bounds. Canonical rendering makes leading-zero failure unreachable. The explicit warning-suppressed entry point leaves fitting values unchanged, bounds no-fit attempts, applies only the shared total-digit/signedness prefix before the inevitable decimal mismatch, and rejects every no-fit result.
- Exact application preserves absent versus present-empty placement, yields accepted coefficient plus scale exactly, and makes the loss of cause/delta provenance explicit.
- Dependency observation retains clean empty, exact accepted stored form, and poison even when application and delta agree.
- Laws and executable separators cover the admitted summaries, authoring, lowering, arithmetic, extrema, validation, tolerance, expression-result, stored-form, target, delta, application, dependency, read-order, and fail-closed boundaries
- [`LF57`](LEAN-FINDINGS.md#lf57--numeric-absolute-value-changes-directional-provenance-at-zero) owns the sign-sensitive `Abs` account and [`LF58`](LEAN-FINDINGS.md#lf58--numeric-operand-list-extrema-combine-exact-selection-with-directional-fillability) owns numeric Min/Max

#### Evidence

- The compact validation record externally separates ordinary empty numeric polarity only.
- Pinned parser/checker, transformer, code-generation, and runtime source establish the current clauses
- a12-dmkits differentials triangulate staged power/fillability, `Abs`, Min/Max domain propagation, target fit/rejection, delta granularity, exact application, and numeric-`BaseYear` tolerance admission and fixed-band evaluation. Numeric-`BaseYear` computation remains external evidence pending under [`SPEC-2026-07-22-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-03--numeric-baseyear-remains-number-like-inside-computation-arithmetic). Base-Year range-component evaluation is likewise pending the recorded peer root correction; kernel checker/code-generation source establishes its fixed unsigned scale-0 result and endpoint selection.
- Accepted [`SPEC-2026-07-21-05`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-05--runtime-invalid-integral-power-poisons-a-number-computation-target) records a12-dmkits revision `43824168`: both runtime-invalid integral regions now reuse the division-domain target/dependency mechanism, with wrapper, quiet-comparison, and valid-boundary controls.
- No retained project-local observation covers checked numeric expressions, power fillability, value functions, suppression, tolerance, mixed domain/poison order, or target/application/dependency behavior.
- Mixed formal-invalid/domain-failure validation precedence is an explicit Lean refinement
- mixed computation order and division/power target invalidity are source-grounded but portable evidence pending.
- Kernel `CheckDatumExtractOpImpl` plus `DateUtils.typeToComponent` establish that direct component extraction rejects constants, requires the matching declared component, supplements only Date Year from configured Base Year, and applies partial-known Date restrictions before that supplementation. Reviewed a12-dmkits IF95 at revision `2abe3ced` and its maintained direct Date/Time extraction differentials triangulate the same field-kind and empty-value boundary; this inbound reconciliation does not create an outbound sync entry.
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

#### Excluded / next

- **Implemented narrowly; external evidence pending.** Checked validation accepts two same-group expressions with at least one field, the admitted expression classes above, six ordinary operators, four tolerance ranges, and the exact-scale-warning bypass.
- The checked computation operation resolves one nonrepeatable Number target and every nonrepeatable Number operand through the shared authored-tree traversal, accepts constant-only or field-bearing plain arithmetic and power after the existing authoring/summary checks, and shares validation's separately audited direct-root admission for `Round`/`Abs` over one field and canonical `Min`/`Max` over direct fields with at most one constant. It rejects the target at every nested operand position and applies the exact result-scale gate unless the one explicit warning flag is present. A dedicated attachment boundary accepts the complete externally resolved target policy once, rejects scale/signedness drift from the resolved target, and returns a wrapper whose evaluation has no policy argument. The checked core retains the warning flag, while the wrapper retains every target constraint and delegates expression evaluation to the established numeric computation result consumer before choosing ordinary or suppressed classification. General wrapper traversal, including a wrapper around arithmetic, remains fail-closed.
- Stored conversion is exact after scale-19 pre-rounding; its warning-suppressed no-fit renderer is structurally locked to consume that pre-rounded value before 16-digit bounding.
- The resolved target policy supports the ordinary scale-compatible path and the explicit warning-suppressed no-fit path with signedness, minimum/maximum fractional digits, the universal 15-digit check, effective integer-digit capacity, zero admission, rendered length, inclusive numeric range, exact stored form, prior-target delta, exact one-address final application, and cause-free dependency observation. The checked target-operation wrapper retains that complete policy after proving its scale/signedness coherence; construction of the resolved policy remains outside the flat declaration because `FlatFieldDecl` does not retain the remaining target constraints.
- Open:
  - checked computation-table integration after one shared numeric-expression condition leaf
  - general operation-valued wrapper authoring beyond the admitted direct root functions
  - concrete computation power authoring and result-empty provenance
  - broader numeric Min/Max operands, including grouped constants and nested arithmetic or wrappers
  - concrete tie-origin retention
  - Date and aggregate Min/Max
  - general value-function wrapper traversal
  - Date-shift projection
  - concrete arithmetic rendering
  - Base-Year-bearing value-function wrappers beyond audited plain arithmetic
  - declaration-owned construction of the resolved Number target policy
  - downstream context/read integration
  - expression-valued generated implicit validation beyond the literal fragment; the flat whole-rule condition currently has no checked numeric-expression leaf, so do not add a parallel condition tree
  - partial/repeatable evaluation
  - missing-ancestor creation
  - concrete parsing/diagnostics
  - public protocol
  - portable rounding/`Abs`/Min/Max/tolerance/expression/target/application/dependency evidence

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
- Date-only `DifferenceInMonths` and `DifferenceInYears` share one decoded-parts completed-period mechanism. Stored/full-Date wrappers retain their value-floor boundary, self-zero and swap-negation laws, and distinct February-end year behavior; direct or range-selected Base-Year sources reuse the same mechanism without imposing the unrelated stored-Date floor, so direct January 1 equals range start and precedes range finish by eleven whole months but no whole year.
- Resolved full-Date equality, inequality, strict order, and inclusive order share the existing calendar chronology. Their classified validation projection reuses the symmetric scalar operand state: formal unavailability dominates, no value does not fire, and a true comparison fires OMISSION exactly when either present value retains missing provenance. Typed `CellObservation FullDate` now reaches that same path directly, with clean present values fixed, empty not evaluated, and validation unavailability retained. Laws characterize equality, operand/operator exchange across truth and verdict, strict-direction exclusion, unknown/no-value handling, both firing polarities, and checked-observation delegation.
- Stored/full-Date direct and selected-stream `Min`/`Max` use a dedicated chronological fold: empty operands do not compete, every reached formal unavailability aborts, no selected value yields no value, and any empty/tail/`Having` or nested missing provenance makes a selected result symmetrically missing. The result feeds the existing Date comparison operand and verdict path.
- DateTime direct and selected-stream `Min`/`Max` reuse that fold after its second completed temporal consumer, selecting exact epoch-millisecond `Instant` values instead of rendered wall labels. Generic laws own empty identity, unavailable-prefix abortion, fixed singleton, and empty-prefix missingness; Date and DateTime retain only their selector- and verdict-specific laws.
- Resolved three-part construction preserves incomplete, calendar-rejected, and unavailable reasons before projecting `Valid`/`Invalid` verdicts.
- Its direct day/month/quarter/year consumer reads supplied real parts, maps incomplete and unreal to equal amount zero with symmetric not-given versus fixed provenance, and maps cause-free unavailability to UNKNOWN.
- Typed full-Date and DateTime validation observations share one direct Day/Month/Quarter/Year numeric projection. Present values expose fixed decoded date components, DateTime ignores its clock, empty sources become symmetric fillable zero, and exact formal causes survive until the numeric verdict projection. The checked numeric source algebra admits the matching Date/DateTime declaration component, supplements only Year from configured Base Year, and routes the same source through validation and Number computation.
- Typed Time and DateTime validation observations likewise share direct Hour/Minute/Second numeric projection. Present values expose fixed decoded clock components, DateTime ignores its date, and the second completed component family reuses one generic symmetric empty-to-zero/cause-preserving numeric observation seam instead of duplicating its polarity mechanism. The same checked source enum admits only matching Time/DateTime declarations and routes both phases through the shared flat context.
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
- Kernel `RuntimeController.validationTime`/`getJetzt`, `VkDate`, and `BedingungsOperatorHelper` establish exact millisecond identity for `Now`, temporal comparison, shifts, and sub-day differences. Local executable cases now lock same-second inequality/order and the seconds-quotient boundary; `SPEC-2026-07-22-02` requests peer reconciliation because the reviewed a12-dmkits clock and temporal coordinate remain whole-second.
- Kernel `RuntimeController.getHeute` copies the zone-set validation calendar and clears hour, minute, second, and millisecond; local cases distinguish UTC from Berlin local-date selection and independently re-resolve Berlin midnight across the spring offset change. a12-dmkits `ClockDiffTest` and its injected-clock controls establish date-shaped comparison behavior, but this repository retains no exact portable model-zone-midnight observation.
- Kernel `CheckKonstanteReferenzjahrImpl`, `CheckVergleichsBedingungImpl`, `CheckDatumDiffOpImpl`, `CodeGenCreator.endVisit(IDateRangeExtractionOperation)`, numeric fractional-digit checking, `RuntimeController.getReferenzjahr`, and the date-difference runtime establish declared-model admission, Number-versus-Date dispatch, exact scale-0 equality, immutable date/time class, model-zone January 1/December 31 resolution, and completed-period consumption of direct/range-selected date sources. Maintained a12-dmkits `BaseYearDiffTest` triangulates the numeric and direct-date projections across both kernel strategies; `PointInTimeSourceReadTest` locks authored range-source acceptance and roundtrip, while peer range execution and therefore Base-Year range-difference calibration remain the recorded upstream gap. This repository retains no portable Base Year observation.
- Kernel `CheckVergleichsBedingungImpl`, `DateFormat`, and `CheckEntityListenUtils` establish the coarse direct-comparison and exact aggregate component gates. Accepted [`SPEC-2026-07-22-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-22-01--direct-temporal-comparison-and-extrema-use-different-format-gates) records a12-dmkits revision `43824168`, whose canonical prose and maintained kernel-route law separate partial component sets, ordering from equality, date from time, and Base Year supplementation without changing the aggregate evaluator.
- Kernel temporal aggregate checkers and `DateCombiner`/`VkDate` establish comparable-component admission plus resolved Time-coordinate and DateTime-instant selection through the same empty, non-relevance, and missingness fold as Date. Accepted [`SPEC-2026-07-21-07`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-07--time-and-datetime-extrema-preserve-resolved-temporal-order) records a12-dmkits revision `43824168`: TIME operand-list extrema now fold by decoded time-of-day, DATE/DATETIME by exact instant, and star-extremum authoring/readback preserves TIME/DATETIME. DG15 explicitly parks the pre-existing adapter read/roundtrip gap for temporal operand-list extrema; evaluation is covered.
- An isolated artifact-only consumer at documentation revision `1c4c48a` recovered the complete resolved Date/Time/DateTime comparison and extremum procedures, the first-cause and missing-provenance distinctions, the one-second and Berlin-overlap separators, the swapped-comparison law, and the unsafe render/drop/reorder/seed transformations without sibling or kernel research. This establishes bounded knowledge transport, not authored integration, shipment readiness, external implementation correctness, or additional kernel correspondence.
- Groovy-dynamic kernel differentials directly establish positive and reverse fractional sub-day truncation.
- Selected whole-unit DST cases also agree through generated static Java, but that route does not separately cover the reverse-fraction discriminator.
- At reviewed a12-dmkits revision `71775c9905b057831253348c31ce39e321e61889`, focused controls lock both Date-range polarity scans through both kernel routes plus the interpreter, and separately lock constructed-Date reason/calendar consumers and `DifferenceInDays` calendar-step separators.
- This repository retains no portable Date, DateTime, construction, or Date-range observation

#### Excluded / next

- **Status:** implemented internally on narrow domains; external evidence partly pending.
- Date coverage includes the unbounded positive-era account, resolved six-way full-Date comparison with classified validation polarity, stored/full-Date `Min`/`Max`, admitted full-Date day/month/year shifts and signed completed-period differences, resolved three-part construction classification, and the proved calendar-coordinate successor/strict-monotonicity bridge.
- Date-range coverage includes closed occurrence-preserving overlap truth, both resolved operator shapes, and their filter-derived polarity scans.
- Time coverage includes exact six-way decoded time-of-day comparison with classified validation polarity and resolved coordinate-based `Min`/`Max`. DateTime coverage includes exact six-way resolved-instant comparison with classified validation polarity, resolved exact-instant `Min`/`Max`, the proved UTC local-order bridge, resolved `DifferenceInHours/Minutes/Seconds`, the full versioned Berlin legacy offset/fresh-label profile, and resolved `DifferenceInDays` inside its consecutive spring slice.
- The admitted full-Date shifts deliberately cover only already-converted integer offsets whose result remains a stored/computed full Date. Their difference wrappers start with two such values; the additional Base-Year specialization accepts only direct and selected range endpoints from one configured year. Both return only the mathematical integer count. Mixed field/Base-Year operands, numeric truncation and 32-bit conversion, constructed-Date legacy identity, partial formats, empty/formal reason projection, numeric result metadata, DateTime gates and wall-time behavior, target formatting, and cell effects remain outside.
- The resolved Date, Time, and DateTime comparison owners start after static component admission and after each operand has been classified as a present full Date, decoded time of day, or exact instant with symmetric missing provenance, no value, or formal unavailability. All three accept their matching typed validation observation directly. The checked field-to-field route performs declaration/path lowering and compares already-parsed exact runtime instants; the field-to-Date-literal route begins after lexical classification plus model-zone/Base-Year decoding and preserves the literal's component shape; checked `Today`, `Now`, temporal `BaseYear`, and selected `StartOfDateRange(BaseYear)`/`EndOfDateRange(BaseYear)` inject the explicit evaluation world after their distinct component gates. Concrete token typing, AM/PM decoding, partial-Date text resolution, and model-zone-id legality checking remain outside.
- Concrete declaration/path lowering has one shared storage representation and checked presence/comparison path. The existing heterogeneous field-ID-indexed `Value` context carries one constructor-tagged `TemporalValue`; `FieldKind.temporal` retains declaration-owned components, formal checking accepts only the matching kind, and `FlatTemporalField` reuses ordinary presence, requiredness, generated guards, model-context construction, multi-field relevance, exact-instant comparison, and direct date/time numeric component reads. `FlatTemporalOperand` owns field, fixed typed literal, dynamic `Today`, temporal `BaseYear`, selected Base-Year range endpoint, and dynamic `Now` shapes without a parallel evaluator. Proof-bearing `FullDate` and `LocalDateTime` remain resolved parser refinements rather than storage alternatives.
- The shared temporal-extremum owner starts with classified stored/full-Date, decoded Time, or exact-instant operands plus resolved tail/`Having` markers. Path/star expansion, raw cells, computation target clearing/application, checked authoring, constructed-Date calendar identity, Time/DateTime parsing and zone resolution, and target rendering remain outside.
- Construction classification and its direct numeric component projection remain reason-bearing but do not yet retain calendar identity, compose temporal no-value reasons beyond extraction, implement date differences, or implement legacy-hybrid month/year operations. Checked authored-expression lowering is closed for direct Date/DateTime Day/Month/Quarter/Year and Time/DateTime Hour/Minute/Second field sources in plain validation and Number-computation arithmetic. Partially-known Date declarations require earlier source-form metadata beyond the ordinary flat field, while constructed-Date operations, differences, and unaudited value-function wrappers remain outside.
- Date-range raw cell classification, actual filter evaluation, paths/stars, row gates, and checked lowering remain outside the resolved operator capsule.
- Open:
  - Literal/field-format parsing, lexical Date-versus-String classification, model-zone/Base-Year decoding, and exact parser range
  - numeric offset truncation/runtime bounds for additions
  - empty/formal operands for other Date consumers and checked temporal expression integration beyond two fields
  - other operator gates and polarity
  - DateTime difference operand/result checking and Number consumption
  - Date and DateTime comparison raw-cell checking and checked integration
  - `DifferenceInDays` outside the finite spring profile and constructed-Date legacy-hybrid month/year differences
  - constructed-Date legacy-hybrid shifts and other date arithmetic
  - full `Date(...)`/Time authoring
  - optional 1900 admission
  - fragment and range construction, plus Base Year date extraction/range-source roles
  - result admission/targets
  - general model-zone dispatch
  - spring-gap formal-error/cell integration
  - other Berlin dates/transitions/history
  - complete legacy-zone profiles for every kernel-legal id, pre-floor hybrid-calendar `Today`, and `Now` outside checked direct comparison
  - checked rule lowering
  - protocol exposure

### §7 — strings and patterns

#### Owners

- [`Semantics/String.lean`](../A12Kernel/Semantics/String.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Semantics/StringComputation.lean`](../A12Kernel/Semantics/StringComputation.lean)
- [`Proofs/StringIngestion.lean`](../A12Kernel/Proofs/StringIngestion.lean)
- [`Proofs/StringLength.lean`](../A12Kernel/Proofs/StringLength.lean)
- [`Proofs/StringComputation.lean`](../A12Kernel/Proofs/StringComputation.lean)
- [`Conformance/StringIngestion.lean`](../A12Kernel/Conformance/StringIngestion.lean)
- [`Conformance/StringLength.lean`](../A12Kernel/Conformance/StringLength.lean)
- [`Conformance/StringComputation.lean`](../A12Kernel/Conformance/StringComputation.lean)

#### Implemented

- Parsed String ingestion performs one non-overlapping CRLF-to-LF pass and caches the evaluated text
- LF and lone CR are preserved.
- Direct comparison, `Length`, and computation share that cached value, and the exact overlap counterexample prevents a second pass.
- Direct equality/inequality and the four scale-exempt `Length` ordering operators have separate consuming clauses.
- Both direct String equality operators suppress an empty field or empty literal after preserving malformed input as UNKNOWN; distinct nonempty values fire only inequality.
- a parsed empty String retains present-empty placement while supplying the same clean-empty observation as absence
- `FieldFilled`/`FieldNotFilled` consume that empty observation rather than physical placement, and checked flat lowering admits String presence.
- Absolute String requiredness reuses the generated `FieldNotFilled` staging and preserves present-empty placement when attaching `.required`.
- shared String length counts UTF-16 code units.
- The computation slice separately models empty contribution, evaluated text, root storage, target-length routing/outcome, and delta projection.
- Strict violations, inclusive acceptance on both permitted sides, exact minimum/maximum boundaries, no-value/poison bypass, payload preservation, store/delta identity, and the nearest stronger term/application non-laws are proved
- its target check fails closed on produced CR/LF

#### Evidence

- Four operator-sensitive validation cases separate empty-content, empty-row, `"ABC"`, and six-character direct-equality/Length outcomes.
- The combined compact root-String record retains 13 copy/concatenation/root-storage cases and nine positive minimum/maximum target cases with exact boundaries, violations, absent/stale/equal priors, and padded blanks.
- Both kernel strategies agreed throughout before one-time compaction.
- Maintained a12-dmkits IF198 tests separately establish the present-empty placement and downstream field/group/required outcomes across both kernel strategies plus JVM/Node.
- Strict permitted-side acceptance, no-value/poison bypass, and CRLF/LF/lone-CR ingestion are internal Lean laws not separately exercised by retained local cases.
- Historical a12-dmkits triangulation had three final-empty-store mismatches and agreed with all nine target cases at projected delta and stored-value application granularity
- the [archive](archived/STRING-COMPUTATION-RAW-EVIDENCE.md) owns that detail.
- The retained strings remain conservative ASCII and do not externally establish broader Unicode or line-break behavior

#### Excluded / next

- **Implemented narrowly; ingestion external evidence pending.** Coverage includes direct equality/inequality, four `Length` orderings, presence, absolute requiredness, present-empty placement, CRLF normalization, checked scalar String expressions, and one positive target length bound.
- `Length ==`/`!=` remain outside the reduced checked surface because their numeric scale gate needs the authored literal scale that `SurfaceCondition.lengthCompare` does not retain.
- Checked expression lowering does not yet construct a target computation step: `FlatFieldDecl` retains neither String length constraints nor line-break permission, so it cannot distinguish an unconstrained target from a constrained one.
- Open: repeatable or parent-gated String requiredness, general document ingestion, group content, full target policies, patterns, enumerations, legal-charsets, custom validators, raw-type rule elimination, and target-check ordering.
- Input normalization does not grant a computed target permission to contain CR/LF.
- Coercion, lists, general computation lowering/scheduling, and every other String function remain rejected or open.
- The public normalized protocol and consumer capabilities have not been expanded to String

### §8 — enumerations and value lists

#### Owners

- [`Semantics/ScalarEquality.lean`](../A12Kernel/Semantics/ScalarEquality.lean)
- [`Semantics/Enumeration.lean`](../A12Kernel/Semantics/Enumeration.lean)
- [`Elaboration/EnumerationComparability.lean`](../A12Kernel/Elaboration/EnumerationComparability.lean)
- [`Semantics/ValueList.lean`](../A12Kernel/Semantics/ValueList.lean)
- their counterparts under [`Proofs/`](../A12Kernel/Proofs.lean), and their counterparts under [`Conformance/`](../A12Kernel/Conformance.lean)

#### Implemented

- Runtime Enumeration comparison uses a clean stored token or one lockstep positional category mapping
- repeated category tokens are legal, empty is not evaluated, unavailable input stays UNKNOWN, and every firing is VALUE.
- The separate direct-field static gate classifies identity labels as effectively textless, rejects a String/display-class mismatch, and accepts two display-bearing ordinary Enumerations exactly when their common-locale stored/display relation has no forward or reverse conflict.
- Trusted laws cover runtime projection, empty/unavailable/VALUE-only behavior, identity-label classification, pair/profile conflict symmetry, String admission, both rejection classes, and overall admission symmetry.
- The separate type-indexed Number/canonical-token value-list capsule preserves explicit present/empty/unknown cells, declared-tail and `Having` metadata, and distinct `AtLeastOne`, `No`, and `NotAll` clauses

#### Evidence

- Canonical §8 prose and pinned kernel source choose the static and runtime accounts.
- Accepted [`SPEC-2026-07-20-14`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-14--enumeration-direct-field-comparability-uses-effective-display-remapping) records a12-dmkits revision `20230e40` and its identity-label, conflict-direction, and compatible-mapping controls.
- The focused runtime matrix currently has one kernel route plus peer triangulation
- a broader catalog smoke case exercises both kernel routes.
- This repository retains no portable §8 observation

#### Excluded / next

- **Implemented internally at two resolved runtime boundaries plus one independent static gate; external evidence pending:** runtime Enumeration begins after ordinary closed-domain/category/literal checks and validation observation
- static comparability begins after valid ordinary declarations and direct equality/inequality field shape
- value lists begin after expansion, comparability checking, and `Having` filtering.
- Table/open/dynamic/partial/duplicate-display declarations, literal and category-field admission, checked model integration, category use in lists/indices/paths, scalar value-list syntax, actual filtering, row gates, protocol exposure, and project-local portable evidence remain open

### §9 — repetition and iteration

#### Owners

- [`Semantics/Iteration.lean`](../A12Kernel/Semantics/Iteration.lean)
- [`Semantics/StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean)
- [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean)
- [`Semantics/RepetitionNotUnique.lean`](../A12Kernel/Semantics/RepetitionNotUnique.lean)
- [`Semantics/Correlation.lean`](../A12Kernel/Semantics/Correlation.lean)
- [`Semantics/CrossLevelCorrelation.lean`](../A12Kernel/Semantics/CrossLevelCorrelation.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Proofs/Iteration.lean`](../A12Kernel/Proofs/Iteration.lean)
- [`Proofs/StarCompleteness.lean`](../A12Kernel/Proofs/StarCompleteness.lean)
- [`Proofs/GroupPresence.lean`](../A12Kernel/Proofs/GroupPresence.lean)
- [`Proofs/RepetitionNotUnique.lean`](../A12Kernel/Proofs/RepetitionNotUnique.lean)
- [`Proofs/Correlation.lean`](../A12Kernel/Proofs/Correlation.lean)
- [`Proofs/CrossLevelCorrelation.lean`](../A12Kernel/Proofs/CrossLevelCorrelation.lean)
- [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean)
- [`Conformance/Iteration.lean`](../A12Kernel/Conformance/Iteration.lean)
- [`Conformance/StarCompleteness.lean`](../A12Kernel/Conformance/StarCompleteness.lean)
- [`Conformance/GroupPresence.lean`](../A12Kernel/Conformance/GroupPresence.lean)
- [`Conformance/RepetitionNotUnique.lean`](../A12Kernel/Conformance/RepetitionNotUnique.lean)
- [`Conformance/Correlation.lean`](../A12Kernel/Conformance/Correlation.lean)
- [`Conformance/CrossLevelCorrelation.lean`](../A12Kernel/Conformance/CrossLevelCorrelation.lean)
- [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean)

#### Implemented

- Exact ordered selector ↔ relation bridges
- filter-before-consumer laws
- a shared full-environment correlated evaluator/relation bridge
- captured-origin, exact named-level resolution, outer-reference stability, self-match/exclusion, scalar-collapse rejection, and one-group observation-footprint results.
- Resolved RNU consumes caller-supplied ordered rows with complete repetition environments and classified composite keys. It excludes unknown keys, skips all-empty keys, uses scale-19 Number equality, retains complete firing clusters in scope order, and projects per-row verdicts before composition.
- Laws characterize exact cluster membership, firing, the internal false/unknown refinement, unique cluster identities, and the existence of a genuinely distinct matching peer.
- The separate checked one-star lowering retains explicit group paths, path-derived repeatable ancestry, exact singleton scope, operator-specific scale legality, model-derived raw checking, fail-closed runtime references, and pre-evaluation 1-based/unique candidate validation.
- The separate reopened-star domain recursively checks finite capacity under every actual parent, treats unbounded levels as open, validates positive sibling-unique coordinates, and bridges its structural result into resolved missing potential.
- The resolved group-presence state independently folds admitted content, error, and three-level relevance, then supplies scalar predicates, fixed-list tallies, strict numeric count availability, and parent-filled requiredness.
- Checked-wrapper theorems eliminate structural certificates
- they are not source-to-core semantic preservation

#### Evidence

- The compact validation record privately replays seven uncorrelated iteration observations and publicly binds 12 one-group captured-outer runtime cases plus four static authoring cases.
- They separate selection, origin, malformed/empty filtering, consumer observation order, comparison and scale boundaries, and neighboring rejection classes.
- Kernel source establishes the complete captured index vector
- maintained a12-dmkits RNU dual-route differentials establish duplicate outcomes, invalid exclusion, optional-empty polarity, typed equality, ordinary composition, and peer clusters as triangulation.
- This repository retains neither an RNU observation nor the cross-level diagonal/off-diagonal separator
- kernel `FALSE_OR_UNKNOWN` intrinsically collapses invalid versus clean nonfiring RNU leaf truth.
- Accepted [`SPEC-2026-07-19-16`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-19-16---correlation-captures-every-named-outer-repetition-level) records the peer diagonal/off-diagonal complete-capture lock
- it does not become project-local portable evidence.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` adds dual-kernel/peer IF193 group-state and IF194 nested-tail separators
- neither is retained as project-local portable evidence.
- [`EVIDENCE.md`](EVIDENCE.md) owns the exact retained inventory and observable support

#### Excluded / next

- **Implemented; wider cross-level and RNU additions remain external evidence pending.** Coverage includes one-group runtime/lowering, normalized firing rows, resolved RNU, caller-supplied reopened-star completeness, and resolved group-presence projections.
- Correlation carries complete candidate/captured environments; RNU defines one branch-independent relation and complete peer clusters before verdict composition.
- The RNU caller must supply the target in scope, unique complete repetition environments with canonical positive level coordinates, and one common declared key arity/order/kind schema
- the low-level evaluator remains total outside those obligations without a kernel-correspondence claim.
- Checked RNU scope/default or explicit `@From`, paths and key-schema validation, partial all-key relevance, one-RNU and negative/iteration/filter/parallel authoring restrictions, checked condition/whole-rule integration, error-field and peer-pointer projection, and protocol exposure remain open.
- The checked correlation elaborator and public protocol remain one-group only
- Open: `Document` adaptation, group-instance enumeration, wildcardable relevance, checked reopened-tree and cell-stream construction, nested or multiple stars, joins, cross-group execution, general consumers, filtered polarity, computation, and partial validation over repeats.

### §10 — paths and references

#### Owners

- [`Semantics/SemanticIndex.lean`](../A12Kernel/Semantics/SemanticIndex.lean)
- [`Proofs/SemanticIndex.lean`](../A12Kernel/Proofs/SemanticIndex.lean)
- [`Conformance/SemanticIndex.lean`](../A12Kernel/Conformance/SemanticIndex.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean)
- [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean)
- [`Conformance/Elaboration.lean`](../A12Kernel/Conformance/Elaboration.lean)
- [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean)

#### Implemented

- Resolved literal-key value lookup over unique canonical entries plus an unavailable-column marker
- validation clean-match-before-column-invalidity, computation column-invalidity-before-match, clean no-match/matched-empty equivalence, selected-target phase observation, nonmatching-target irrelevance, signedness-aware empty-Number polarity, shared validation/computation `FieldFilled`/`FieldNotFilled`, and indexed field-fill tally/ordered-slot projections
- model validation including field/group hierarchy separation and path-derived repeatable-scope coherence
- order-independent unique ID/path lookup
- shared parent walking
- corrected bare declaring-group → flag-gated model-wide unique resolution
- explicit repeatable-group path declarations
- exact one-star binding
- ambiguity, wrong group/scope, nested false-singleton scope metadata, and unsupported surface forms fail closed
- unique declaration and raw-policy coherence theorems

#### Evidence

- Maintained a12-dmkits indexed-read differentials at accepted revision `71775c9905b057831253348c31ce39e321e61889` establish match/no-match, phase precedence, selected-target invalidity, and presence as triangulation, but this repository retains no portable semantic-index observation.
- The full invalid-column matrix is strongest for Number keys while the canonical-token generalization is source-grounded.
- The compact validation record privately replays parent-relative, absolute, local-precedence, model-wide fallback, and ambiguity cases.
- Its four public static correlation associations retain code/class pairs for missing inner iteration, equality-scale mismatch, and a sibling-group reference plus acceptance for the ordering control
- acceptance does not establish runtime firing rows.
- [`LF6`](LEAN-FINDINGS.md#lf6--bare-name-resolution-is-local-or-global-not-an-ancestor-walk) records the bare-name correction

#### Excluded / next

- **Implemented for three narrow structured/resolved subsets:** non-repeatable flat paths, one absolute-or-direct-child-relative group-qualified star/correlation shape, and one already-resolved literal-key semantic-index Number value consumer with kind-independent scalar presence and field-fill operands.
- Parent-relative and bare forms remain outside the public correlation operation.
- Semantic-index key checking/normalization, field-keyed indices, checked path integration, named labels, quoting, `RuleGroup`, concrete parser/renderer, nested/multi-star paths, and general repeatable lookup remain excluded
- not every excluded or rejected syntax has a retained diagnostic

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
- Checked String-expression lowering resolves nonrepeatable copy leaves against one validated flat model, rejects wrong-kind and repeatable operands, preserves literal/concatenation tree order, checks raw cells with the same model, and delegates evaluation to the existing runtime expression.
- The checked literal-Number desugaring represents every nonempty table as either one optionally guarded alternative or two-or-more fully guarded alternatives, without fabricating a true guard. Computation selects a wholly unguarded singleton directly and otherwise reuses the common-expansion selector, while generated validation omits an absent singleton guard, left-folds wider mismatch tables in declaration order, and places the common guard once below `FieldFilled(target)` and above the complete mismatch body. Each alternative independently lowers to strict `!=` or its optional fixed tolerance through the shared numeric-validation dispatch.
- The checked guard traversal rejects the exact computed target ID in common and every alternative condition before phase lowering, retaining common versus one-based alternative position. The separate checked numeric-operation boundary rejects the same target throughout a plain-arithmetic or admitted direct root value-function tree, retains the exact-scale warning choice, and routes its evaluated result through the matching target branch; expression-valued table integration remains open.
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
- No retained project-local observation exercises direct presence/connectives, field-fill scans, alternative selection or selected-operation terminality, generated guarded-alternative validation, numeric expression/target/delta/application/dependency, mixed domain/poison order, or the newline family
- those surfaces remain `external evidence pending`

#### Excluded / next

- **Implemented narrowly and partially externally calibrated:** one nonrepeatable recursive direct-presence fragment
- all seven field-fill predicates over a caller-supplied already-expanded ordered slot stream
- first-match selection with resolved String selected-operation/target/delta integration
- optional common-precondition expansion over that already-guarded table
- a checked nonempty literal-Number generated-rule fragment with an optionally guarded singleton or guarded two-or-more table and an optional checked common precondition
- one String target and direct cascade
- and one already-resolved Number expression → ordinary-or-warning-suppressed stored form → target → delta → exact application → cause-free dependency chain.
- Open:
  - General computation-table authoring and operation-side target self-reference checks beyond the checked plain-arithmetic/direct-root numeric-operation fragment
  - checked zero/default authoring outside the structurally nonempty literal fragment
  - general checked common-precondition authoring beyond the guarded literal fragment
  - expression-valued generated validation
  - comparison guards
  - field-fill stream construction/path/group/star/filter expansion and AST integration
  - scheduling
  - transitive graphs
  - repeatable evaluation
  - joins
  - missing-ancestor creation
  - other value kinds/functions
  - public reference exposure
  - portable evidence

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
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Semantics/ValidationRule.lean`](../A12Kernel/Semantics/ValidationRule.lean)
- [`Semantics/PartialValidation.lean`](../A12Kernel/Semantics/PartialValidation.lean)
- [`Elaboration/NumericValidation.lean`](../A12Kernel/Elaboration/NumericValidation.lean)
- [`Elaboration/ValidationRule.lean`](../A12Kernel/Elaboration/ValidationRule.lean)
- [`Elaboration/GeneratedComputationValidation.lean`](../A12Kernel/Elaboration/GeneratedComputationValidation.lean)
- their counterparts under [`Proofs/`](../A12Kernel/Proofs.lean), and their counterparts under [`Conformance/`](../A12Kernel/Conformance.lean)

#### Implemented

- The verdict algebra preserves VALUE/OMISSION precedence and unknown
- numeric fillability supplies directional polarity across direct comparisons, admitted arithmetic including resolved power, and fixed tolerance.
- The seven resolved unfiltered field-fill quantifiers classify instantiated observations, combine adjacent ranges by count addition, preserve declared/instantiated/mixed ranges, treat unavailable cells as neither filled nor empty, and expose fired polarity versus exact collapsed `FALSE_OR_UNKNOWN`; semantic-index reads now supply both validation tallies and ordered computation slots through the same phase lookup
- trusted laws separate the two `NotExactlyOne` firing regions, the mixed predicate from `NotAll`, and validation collapse from computation poison.
- Resolved group presence independently folds admission, error, and three-level relevance, then gives scalar predicates, fixed-list predicates, strict numeric count, and parent-requiredness their consumer-specific projections.
- The reopened-star completeness boundary recursively derives structural tail missingness per actual parent and feeds the existing resolved-side disjunction without changing operator directions.
- The checked resolved-rule boundary preserves silent distinctions and retains a structured message plan until a fired verdict renders and attaches exact address, error code, severity, polarity, and text.
- The generated-computation fragment reuses that same post-fire boundary and the shared strict-or-tolerance numeric dispatch; its optional common condition sits once outside the mismatch disjunction, guards reject direct computed-target self-reference, ERROR severity does not fix message polarity, and tolerance metadata cannot affect computation selection.
- Flat partial evaluation first skips a rule marked as containing `Having`, then applies the separate error-field gate and relevance-aware leaf evaluator for unfiltered rules.

#### Evidence

- Retained validation observations separate ordinary polarity and malformed connective outcomes but do not establish checked whole-rule assembly, generated guarded-alternative validation, error-code/severity independence, complete message rendering, hidden silent distinctions, or field-fill quantifiers.
- Maintained a12-dmkits multi-route quantifier differentials ground the seven unfiltered formulas and broader filter behavior, but this repository retains no portable field-fill observation.
- Direct ordering, arithmetic fillability, tolerance, partial relevance, integrated expression comparison, generated-rule details, and the label/value display refinements remain source/test anchored and project-locally `external evidence pending`.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` additionally triangulates IF193 group relevance/availability and IF194 nested-star aggregate polarity across both kernel strategies and the peer interpreter, without adding project-local portable evidence.
- a12-dmkits revision `6039fd3e` and the three kernel code-generation templates ground IF202's method-entry skip for filtered partial rules; this repository retains no portable filtered-rule observation.
- Same-field alias polarity is source-inferred
- mixed formal-invalid/domain precedence is an explicit Lean refinement

#### Excluded / next

- **Implemented internally for the named clauses:** all seven unfiltered field-fill operators over a caller-supplied resolved tally, with generic instantiated-observation classification, tally composition, and one resolved indexed-operand projection
- resolved scalar/list/count/relative-required group-presence projections over caller-supplied group slices
- hierarchical structural-tail derivation over a caller-supplied reopened tree
- reduced fixed-right Number/String-Length validation
- known arithmetic and fixed-tolerance polarity
- one same-group nonrepeatable two-expression comparison
- one exact nonrepeatable structured-plan rule message rendered only after firing
- one checked nonempty literal-Number generated rule, split between an optionally guarded singleton and guarded two-or-more table, with an optional common condition on the same message boundary
- and one ordered nonrepeatable partial-validation filter gate, error-field gate, and relevance-aware leaf evaluator.
- Open:
  - Checked group-instance/descendant enumeration and wildcardable relevance construction
  - checked construction of reopened trees and ordered cell streams from authored/model/document inputs
  - field-fill authored expansion
  - general checked-cell/tally and ordered-slot stream construction beyond the indexed operand
  - `Having` discovery, lowering, and evaluation
  - row eligibility
  - physical read traces
  - hidden false/unknown refinement
  - integration with conditions/connectives
  - rule paths
  - referenced-field/fill-to-fix metadata
  - raw authored-template parsing and legality
  - repeatable addresses
  - row-content derivation
  - rule collections/order
  - general generated checks
  - custom-condition whole-rule integration
  - concrete computation power authoring and result-empty provenance
  - `BaseYear`
  - exact mixed-failure precedence
  - global/wildcard relevance
  - repeats/phantom rows
  - aggregates
  - uniqueness
  - orchestration

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

#### Excluded / next

- **Implemented internally, narrow:** parser-independent rendering after reference/display resolution and fired-only integration for checked nonrepeatable flat rules plus generated literal-Number computation validation.
- Raw `$...$` parsing, token/path/star/reference legality, lookup/provider invocation and locale/display conversion, repeatable/index/category/semantic-index/BaseYear tokens, field-owned format-error text, custom conditions, protocol exposure, and a complete §13 claim remain open

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

#### Excluded / next

- **Implemented internally, narrow:** one successfully registered, already-reached pure callback leaf.
- Open or outside the pure theory: registration and name resolution, host effects and call order, concrete data APIs, relevance/formal/pointer construction, orchestration, static restrictions, messages, checked lowering, protocol, and full host-data fidelity.
- Correspondence remains `external evidence pending`

## Cross-clause implementation notes

The §5/§11 numeric-computation entry retains each atom's declaration and rejects non-Number declarations before reads.

- Evaluation follows the lowered tree left-to-right, so rewriting may change the first poison reached.
- Invalid integral power reaches the shared target/dependency domain-failure path.
- Concrete authoring and portable evidence remain open.

### Resolved Number `FirstFilledValue`

- Owners: [`Semantics/FirstFilledValue.lean`](../A12Kernel/Semantics/FirstFilledValue.lean), [`Proofs/FirstFilledValue.lean`](../A12Kernel/Proofs/FirstFilledValue.lean), and [`Conformance/FirstFilledValue.lean`](../A12Kernel/Conformance/FirstFilledValue.lean).
- Boundary: one ordered Number operand after expansion, filtering, and partial-relevance classification, shared by §3, §8, §10, and §11.
- The scan stops at the first present value or first unavailable cell: an invalid prefix makes validation UNKNOWN and computation poison, an invalid suffix is unread, an empty prefix retains the amount but changes validation from fixed/VALUE to fillable/OMISSION, and an empty suffix is irrelevant.
- An explicitly empty, marked-uninstantiated, or filtered-empty Number selection supplies the fillable zero
- `Having` makes even a selected value fillable.
- The global filter bit belongs only to the admitted sole operand
- later authored operand slots and their position-sensitive filter encounter order are excluded.
- Checked authored lowering must mark a no-row star as uninstantiated because the total unmarked `[]` state is fixed zero.
- Trusted laws prove prefix/suffix termination, empty-prefix idempotence, empty identities, both projections, and the central non-law that computation forgets the empty-prefix distinction while validation preserves it.
- Kernel source and maintained a12-dmkits `FirstFilledValue` differentials establish the selected observable behavior, but this repository retains no portable observation, and exact formal-cause carriage is an internal refinement.
- Multi-operand authoring, path/star expansion, actual filter evaluation, partial relevance, model/static checking, non-Number kinds, row gating, target application, whole-rule integration, protocol support, and project-local portable evidence remain open.
- Accepted [`SPEC-2026-07-20-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-09--firstfilledvalue-observes-only-filters-before-termination) records the peer encounter-order correction and focused locks.

### Resolved Number aggregates

- Owners: [`Semantics/NumericAggregate.lean`](../A12Kernel/Semantics/NumericAggregate.lean), [`Elaboration/NumericAggregate.lean`](../A12Kernel/Elaboration/NumericAggregate.lean), [`Proofs/`](../A12Kernel/Proofs.lean), and [`Conformance/`](../A12Kernel/Conformance.lean).
- Boundary: resolved validation-side Number `Sum`/`MinValue`/`MaxValue` plus checked nonempty unfiltered nonrepeatable field lists.
- The two completed consumers share only `ValueListCell.scanPresent`: it skips empty cells, stops at the first reached unavailable cell, and applies a caller-owned step to present cells from left to right.
- Extrema select exact present amounts without a synthetic zero.
- `Sum` starts at zero and applies precision-50 `HALF_UP` addition at every present term in encounter order, so exact accumulation, reassociation, and reordering are rejected by separate cases.
- `ResolvedNumericSumSide` additionally retains signedness on every selected source and every uninstantiated source
- after a present total, any missing source permits growth and exactly a missing signed source permits shrinkage.
- A signed present source does not widen an unsigned missing source.
- The former homogeneous API embeds every cell and tail with one shared signedness.
- Every all-empty route returns zero with both directions, while `Having` makes any available result both-directionally fillable.
- Generic scan laws establish availability, all-empty preservation, and first-cause termination once
- short operator laws specialize identity, fixed/tail results, per-source signedness, homogeneous embedding, metadata separation, and filter escalation.
- `CheckedNumericAggregateFields` resolves the shared nonrepeatable Number source list once, classifies raw cells through the same validated model, and constructs exact no-tail/no-`Having` views for `Sum` and extrema.
- A trusted equality locks both views to the same classified cells in authored order
- only the Sum view adds each declaration's signedness.

- This is internally complete at levels 1–2 and remains `external evidence pending`.
- Mixed-declaration resolved Sum evaluation and direct nonrepeatable field-list construction for all three operators are represented, but group/star expansion must still construct per-source cells and uninstantiated signedness without losing declaration identity.
- Enclosing checked comparison remains open: runtime operands compose with ordinary polarity, but the checked numeric expression tree has no aggregate node and must not be bypassed by a parallel aggregate-comparison wrapper.
- The separate reopened-star capsule below can derive structural openness from a caller-supplied IF194 tree, but neither layer constructs the tree or ordered cell stream from authored paths and a `Document`.
- The older checked-row `NumberFold` uses the homogeneous embedding and projects only amount or cause, preserving its existing truth-only API while deliberately erasing fillability.
- The family does not share the prefix-terminating `FirstFilledValue` scan or operand-list empty substitution/fillability.
- Checked repeatable/star lowering, actual filter execution, partial-validation relevance and row gating, computation aggregates, Date and other overloads, messages, protocol exposure, and project-local portable evidence remain open.
- a12-dmkits revision `20230e40` accepted the all-empty correction in [`SPEC-2026-07-20-15`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-15--all-empty-number-aggregate-identity-is-both-directionally-fillable).
- The same revision accepted Sum order, precision, and missing polarity in [`SPEC-2026-07-21-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-02--number-sum-preserves-encounter-order-staged-precision-and-missing-declaration-polarity).

### Reopened-star structural completeness

- Owners: [`Semantics/StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean), [`Proofs/StarCompleteness.lean`](../A12Kernel/Proofs/StarCompleteness.lean), and [`Conformance/StarCompleteness.lean`](../A12Kernel/Conformance/StarCompleteness.lean).
- Boundary: IF194's structural decision after first-star binding.
- `ReopenedStarDomain` contains only reopened repeatable levels
- every actual child row stays beneath its actual parent, carries its 1-based coordinate, and recursively owns the next reopened level or selected leaf.
- Its executable well-formedness check requires positive, sibling-unique coordinates but permits over-limit rows.
- A finite level is structurally closed exactly when its actual count reaches the cap and every actual child subtree is closed
- an absent cap is unbounded and always open.
- The traversal is linear in the supplied tree and never constructs the declared Cartesian domain.

- The bridge writes this structural result to `ResolvedValueListSide.hasUninstantiatedTail`
- selected-cell emptiness remains in `cells`, so existing `hasMissingPotential` combines the two without duplicating leaf state.
- Trusted laws characterize leaf and unbounded branches, finite closure, open-child propagation, coordinate-label independence, and both bridge projections.
- Cases separate outer, middle, and leaf omissions, full closure, a bound level above the first star, an unbounded level, invalid coordinate inputs, empty-cell composition, and an unchanged unsigned Sum consumer.
- The first shallow-count implementation failed the middle and leaf cases before recursive correction.

- This is internally complete at levels 1–2 for a caller-supplied well-formed reopened tree and resolved cell stream.
- It does not parse paths, identify the first star, read model repeatabilities, enumerate scoped `Document` rows, classify cells, evaluate `Having`, or prove tree/stream construction correct.
- The a12-dmkits IF194 tri-engine matrix at revision `7f152509eea76822068955055b0d57d8ed930ca2` is focused external triangulation, but this repository retains no portable observation
- correspondence remains `external evidence pending`.
- Aggregate directions, computation, partial relevance, per-source declaration-metadata construction, messages, and protocol exposure retain their existing boundaries.

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
- Open: descendant/model enumeration, `Document` adaptation, group-instance row assignment, wildcardable relevance, global augmentation, starred group expansion, checked lowering, and required-rule orchestration.
- The a12-dmkits IF193 tri-engine matrix at revision `7f152509eea76822068955055b0d57d8ed930ca2` is focused external triangulation, but this repository retains no portable observation
- correspondence remains `external evidence pending`.
- Messages, protocol exposure, and wider validation orchestration remain open.

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
- checked lowering, paths/stars, filter evaluation, cells, row gates, messages, equality/inequality, DateRange construction/extraction, protocol support, and project-local evidence remain open.

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
- Exact formal causes, raw/checked date-component cells, two- and four-part forms, missing-Base-Year authoring rejection outside checked comparison/numeric-expression consumers, exact parser/component bounds, full-row gating, nested difference/addition consumers, stored/computed temporal target admission, and protocol exposure remain open.
- Direct and range-selected Base-Year Day/Month/Quarter/Year extraction now feeds the shared checked scale-0 numeric atom in both validation and Number computation, preserving the validation constant-expression gate and computation's legal constant-only route.
- Other date differences, compositional temporal no-value propagation, and legacy-calendar identity remain open.
- Concrete calendar resolution is deliberately not implemented: kernel 30.8.1 uses a zone-aware hybrid `GregorianCalendar`, while the reusable `CivilDate` account is zone-free and proleptic, and the two accounts have reachable cutover and zone-discontinuity separators.

### `DifferenceInDays` finite-profile closure

- Kernel source counts signed model-zone `Calendar.DAY_OF_MONTH` steps, while the obvious reuse of `CivilDate.unixEpochDay` would impose a zone-free proleptic coordinate.
- Those accounts separate on a Berlin special-hour landing and across a skipped whole date.
- [`LF47`](LEAN-FINDINGS.md#lf47--differenceindays-needs-a-model-zone-calendar-step-account) records both reproduced discriminators.
- Accepted [`SPEC-2026-07-20-08`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-08--differenceindays-counts-model-zone-calendar-steps) records both kernel-route separators and the peer calendar-step reconciliation.
- Lean now enforces the narrower option: the general versioned Berlin profile resolves fresh labels, `Berlin2024Profile` retains only stateful spring day stepping, and `DateTimeDayDifference` counts at most the three landings within that exact slice.
- Ordinary, threshold, reverse-sign, retained-adjusted-clock, elapsed-seconds non-equivalence, and unsupported cross-slice cases form the separating matrix.
- Empty/formal operand coercion, fillability/polarity, checked lowering, constructed-Date calendar identity, general wall-day landing, other zones, and protocol exposure remain later consumers rather than being inferred from this profile.

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
- the §7/§11 computation capsules cover clean String reads in bare copy and concatenation, final storage, target-length classification, and prior-target delta projection.
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
