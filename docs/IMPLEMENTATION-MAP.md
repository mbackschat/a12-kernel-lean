# Lean implementation and evidence map

This is the live join from the project-owned [`spec/`](../spec/) taxonomy to executable Lean definitions, trusted theorems and checked counterexamples, external kernel evidence, and exact support boundaries. It follows the map/ledger principle used by a12-dmkits' [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md), but answers a different question: what has this Lean theory actually captured and justified?

The target behavior version is kernel **30.8.1**. “Implemented” means the named Lean fragment executes. “Proved internally” means the theorem follows from the chosen Lean definitions. Neither means universal correspondence with the external kernel. A fragment remains **external evidence pending** until retained, versioned kernel observations for that fragment are portable and replayable in this repository.

## Evidence snapshot

- The compact validation record has 49 records for 48 distinct external observations because one directional Number witness is intentionally shared across its public and private halves.
- `lake test` replays the 24 private validation records through typed Lean projections
- `checkReferenceProcess` binds the 25 public records to exact normalized requests and externally supported projected responses.
- These two gates complement each other but are not one 49-case replay.
- Together with the 22 root-String and five direct-cascade private replays, the current `lake test` evidence total is 51.

## Taxonomy by clause

For targeted work, open only the owning clause and any linked cross-clause note. Every clause uses the same four fields: Lean owners, internal account, external evidence, and exact boundary.

### §1 — truth and verdict algebra

#### Lean owners

- [`Core.lean`](../A12Kernel/Core.lean)
- [`Proofs/Verdict.lean`](../A12Kernel/Proofs/Verdict.lean)
- [`Proofs/Information.lean`](../A12Kernel/Proofs/Information.lean)

#### Internal account

- Commutativity, associativity, idempotence, identities, absorbers, absorption, distributivity, and strong-Kleene information monotonicity
- checked non-laws retain the exact unknown/polarity limits

#### External evidence

- Canonical §1 sources
- no focused portable observation

#### Exact boundary

- **Proved internally; external evidence pending** for the finite `K`/`Verdict` algebras
- no generic negation

### §2 — empty scalar comparisons and row gate

#### Lean owners

- [`Semantics/NumericComparison.lean`](../A12Kernel/Semantics/NumericComparison.lean)
- [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Proofs/NumericComparison.lean`](../A12Kernel/Proofs/NumericComparison.lean)
- [`Proofs/StringLength.lean`](../A12Kernel/Proofs/StringLength.lean)
- [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean)
- [`Conformance/StringLength.lean`](../A12Kernel/Conformance/StringLength.lean)
- [`Conformance/Elaboration.lean`](../A12Kernel/Conformance/Elaboration.lean)

#### Internal account

- Executable Number/Boolean/Confirm empty laws, direct Number equality/inequality/`<`/`>=`, direct String equality, `Length <`/`>=`, directional numeric polarity, row gates, checked surface lowering, and model-derived evaluation
- parsed-empty String placement preservation plus operator-distinction and directional-fillability laws

#### External evidence

- The compact [validation record](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json) binds the eight public empty-logic cases and one public directional witness to exact normalized requests and externally supported responses.
- Its six private operator cases replay unsigned/signed empty Number inequality, filled-zero controls, direct String equality, `Length`, and the empty-row gate
- the directional witness intentionally occurs in both halves.
- Direct Number `<`/`>=` is anchored to pinned kernel source and focused a12-dmkits differentials but has no project-local portable observation.
- Retired 0.2.0 provenance is [archived](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md)

#### Exact boundary

- **Implemented internally, partial; direct ordering external evidence pending:** nonrepeatable Number equality/inequality/`<`/`>=`, Boolean/Confirm/String equality/inequality, and Number/Boolean/Confirm/String presence are executable.
- Direct String supports equality only, plus String `Length <`/`>=`
- its empty observation retains absent versus present-empty placement at the checked-cell boundary.
- String presence and absolute nonrepeatable requiredness reuse the generic presence/required staging; other String comparisons/functions remain rejected or unimplemented.
- This is a consuming-clause baseline, not a kind-wide empty law
- see [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function), [`LF10`](LEAN-FINDINGS.md#lf10--numeric-polarity-needs-directional-fillability-not-a-given-bit), and [`LF24`](LEAN-FINDINGS.md#lf24--direct-number-ordering-uses-the-same-directional-fixed-right-comparison)

### §3 — formal checking and phase observation

#### Lean owners

- [`Semantics/Observation.lean`](../A12Kernel/Semantics/Observation.lean)
- [`Semantics/StringComputation.lean`](../A12Kernel/Semantics/StringComputation.lean)
- [`Proofs/Observation.lean`](../A12Kernel/Proofs/Observation.lean)
- [`Proofs/StringIngestion.lean`](../A12Kernel/Proofs/StringIngestion.lean)
- [`Proofs/StringComputation.lean`](../A12Kernel/Proofs/StringComputation.lean)
- [`Conformance/Observation.lean`](../A12Kernel/Conformance/Observation.lean)
- [`Conformance/StringIngestion.lean`](../A12Kernel/Conformance/StringIngestion.lean)
- [`Conformance/StringComputation.lean`](../A12Kernel/Conformance/StringComputation.lean)

#### Internal account

- `CheckedCell.WellFormed`, preservation under staged findings, validation-unknown/computation-poison phase laws, and the required-only exception.
- `RawCell.presentEmpty` and a parsed empty String retain `rawPresent = true` with no parsed value or finding
- generic laws distinguish that checked state from absence while proving that both phases observe it as empty.
- Nonempty parsed String ingestion performs exactly one non-overlapping CRLF-to-LF pass before caching the evaluated value
- proofs connect the cached result to both phases, direct comparison, UTF-16 `Length`, and computation reads, while a checked counterexample refutes global idempotence.
- The separate reduced String target pass classifies an admitted nonempty root write as accepted or payloadful `ERRORED`, proves no-value and poison bypass for every policy, and fails closed on produced CR/LF until target line-break permission is modeled

#### External evidence

- Retained malformed comparison and branch-combination cases check observable authored-message suppression/firing
- the external output cannot distinguish internal `unknown` from `notFired`.
- The nine-case [compact root-String record](../evidence/kernel-30.8.1/captures/string-computation-v1/semantic-observations.json) separately exposes accepted and errored rich computation results, including attempted value and `stringZuKurz`/`stringZuLang` cause.
- Maintained a12-dmkits IF198 tests at accepted [`SPEC-2026-07-21-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-03--empty-string-ingestion-preserves-present-empty-placement) triangulate present-empty String ingestion, field/group presence, and requiredness across both kernel strategies plus JVM/Node
- this repository retains no matching portable observation.
- No retained portable observation yet exercises CRLF/LF/lone-CR ingestion

#### Exact boundary

- **Implemented internally, partial; ingestion external evidence pending:** the reduced boundary distinguishes absent from present-empty before projecting either to the empty phase observation and owns evaluated-String CRLF normalization after scalar text decoding.
- A general `Document → RawCell` bridge, public present-empty transport, group-content derivation, and custom-validator invocation remain open.
- raw storage itself remains outside this reduced account.
- The internal unknown/poison account still relies on source treatment and internal laws.
- Computed String target checking admits only one positive minimum or maximum length over no-line-break text
- no-value/poison bypass, target line-break permission, and ingestion normalization are not externally exercised.
- The rest of the reduced computed-result formal check and contextual findings beyond requiredness remain open

### §4 — required property

#### Lean owners

- [`Semantics/Required.lean`](../A12Kernel/Semantics/Required.lean)
- [`Proofs/Required.lean`](../A12Kernel/Proofs/Required.lean)
- [`Conformance/Required.lean`](../A12Kernel/Conformance/Required.lean)

#### Internal account

- Independently stated source outcome versus generated-rule evaluation
- base-before-annotation ordering
- computation-observation preservation
- Number/Boolean/Confirm/String targets share the same presence rule; a required present-empty String retains physical placement when the finding is attached.

#### External evidence

- The private compact validation projection replays empty, filled, and malformed absolute/non-repeatable Number cases and retains the empty case's `mandatoryField` code and pointer
- [`RequirednessDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/RequirednessDiffTest.kt) remains broader provenance.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` adds dual-kernel/peer controls for IF193's admitted-content parent gate, but this repository retains no matching portable observation

#### Exact boundary

- **Implemented internally, partial; focused external observations replayed:** absolute requiredness for nonrepeatable Number/Boolean/Confirm/String fields.
- Parent-filled requiredness remains open because Lean does not yet derive the admitted-content × error × relevance group state
- repeatable ancestors, index generation, and generated rule identity also remain open

### §5 — numbers and decimals

#### Lean owners

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

#### Internal account

- Signed exact-or-unknown scale and constant expandability
- authored literals/grouping
- plain authoring-region checks plus exact direct-field root rounding, `Abs`, and numeric operand-list `Min`/`Max` admission
- one order-sensitive division-lowering pass
- precision-50 `+`/`−`/`×`/`÷`, staged power, rounding, absolute value, full-precision ordered extrema, arithmetic domain failure, and directional fillability including the conservative power and Min/Max tie tables
- independent scale-19 normalization
- a checked closed validation dispatch over all six direct ordinary comparison operators and four fixed tolerance ranges
- one already-resolved computation-expression consumer with distinct numeric value, domain failure, and inherited poison
- a separately proved exact stored-decimal conversion
- and one ordinary fit-path target consumer with target classification, change-only delta, exact one-address final application, and cause-free dependency observation.
- The validation consumer resolves and checks two admitted expressions—plain arithmetic, exact direct-field root rounding/`Abs`, or one canonical direct-field Min/Max fold—before lowering each once, gates empty rows before reads, and preserves formal-invalid, domain-failure, value, and two-sided fillability distinctions.
- The computation consumer reads empty and required-empty Number as zero, preserves domain failure through clean enclosing arithmetic, rounding, `Abs`, and Min/Max, follows source-established left-to-right poison order through one shared delayed-right evaluator, and rejects every structurally invalid or unaudited power subtree before data reads.
- Stored conversion universally preserves the scale-19 `HALF_UP` amount while retaining `{unscaled, scale}` form.
- After separate assignment-scale admission, the target consumer pads to minimum fractional digits without capping a fit attempt, checks universal digit length before signedness, fails closed on the warning-suppressed no-fit branch, distinguishes no-result/accepted/rejected/domain-invalid/poison, and compares prior coefficient plus scale.
- Exact application preserves absent versus present-empty placement, yields accepted coefficient plus scale exactly, and makes the loss of cause/delta provenance explicit.
- Dependency observation retains clean empty, exact accepted stored form, and poison even when application and delta agree.
- Laws and executable separators cover the admitted summaries, authoring, lowering, arithmetic, extrema, validation, tolerance, expression-result, stored-form, target, delta, application, dependency, read-order, and fail-closed boundaries
- [`LF57`](LEAN-FINDINGS.md#lf57--numeric-absolute-value-changes-directional-provenance-at-zero) owns the sign-sensitive `Abs` account and [`LF58`](LEAN-FINDINGS.md#lf58--numeric-operand-list-extrema-combine-exact-selection-with-directional-fillability) owns numeric Min/Max

#### External evidence

- The compact validation record externally separates ordinary empty numeric polarity only.
- Pinned parser/checker, transformer, code-generation, and runtime source establish the current clauses
- a12-dmkits multi-route differentials also ground staged power/fillability, `Abs`, Min/Max computation-domain propagation, fit padding, full overflow retention, no-fit behavior, target rejection, delta granularity, and type-neutral exact application as triangulation.
- No retained project-local observation exercises resolved power fillability, checked direct-field root rounding, `Abs`, or Min/Max, integrated arithmetic-expression comparison, checked tolerance, same-field alias, numeric expression result classes, mixed domain/poison read order, or numeric target/delta/application/dependency.
- Mixed formal-invalid/domain-failure validation precedence is an explicit Lean refinement
- mixed computation order and division target invalidity are source-grounded but portable evidence pending.
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

#### Exact boundary

- **Implemented narrowly; integrated validation and numeric computation remain external evidence pending:** the checked same-group, full-validation consumer accepts two admitted expressions with at least one resolved field—plain `+`/`−`/`×`/`÷` arithmetic, exact direct-field root rounding/`Abs`, or a canonical same-selector Min/Max fold over direct fields—and a closed choice of six ordinary operators or four fixed tolerance ranges.
- The separate computation expression accepts one already-resolved admitted arithmetic/rounding/`Abs`/Min/Max tree.
- Stored conversion is exact after scale-19 pre-rounding
- the target accepts only the ordinary scale-compatible path with signedness, minimum/maximum fractional digits, the universal 15-digit check, exact stored form, prior-target delta, exact one-address final application, and cause-free dependency observation.
- Open:
  - Checked concrete computation/target authoring
  - checked power consumers and result-empty provenance
  - constant-bearing numeric Min/Max
  - concrete tie-origin retention
  - Date and aggregate Min/Max
  - general value-function wrapper traversal
  - Date-shift projection
  - concrete arithmetic rendering
  - `BaseYear`
  - warning-suppressed no-fit rendering
  - range/zero/integer-digit/other Number constraints
  - downstream context/read integration
  - general tolerance/expression-valued generated implicit validation beyond the exact two-literal fragment
  - partial/repeatable evaluation
  - missing-ancestor creation
  - concrete parsing/diagnostics
  - public protocol
  - portable rounding/`Abs`/Min/Max/tolerance/expression/target/application/dependency evidence

### §6 — dates and time

#### Lean owners

- [`Semantics/FullDate.lean`](../A12Kernel/Semantics/FullDate.lean)
- [`Semantics/DateRangeOverlap.lean`](../A12Kernel/Semantics/DateRangeOverlap.lean)
- [`Semantics/DateRangeOverlapOperators.lean`](../A12Kernel/Semantics/DateRangeOverlapOperators.lean)
- [`Semantics/DateConstruction.lean`](../A12Kernel/Semantics/DateConstruction.lean)
- [`Semantics/DateConstructionNumeric.lean`](../A12Kernel/Semantics/DateConstructionNumeric.lean)
- [`Semantics/DateTime.lean`](../A12Kernel/Semantics/DateTime.lean)
- [`Semantics/DateTimeDifference.lean`](../A12Kernel/Semantics/DateTimeDifference.lean)
- [`Semantics/DateTimeDayDifference.lean`](../A12Kernel/Semantics/DateTimeDayDifference.lean)
- the matching modules under [`Proofs/`](../A12Kernel/Proofs/) and [`Conformance/`](../A12Kernel/Conformance/)

#### Internal account

- `DateParts → CivilDate → FullDate` separates decoded components, positive-era Gregorian reality, and the inclusive 1583-10-16 value floor.
- Resolved three-part construction preserves incomplete, calendar-rejected, and unavailable reasons before projecting `Valid`/`Invalid` verdicts.
- Its direct day/month/year consumer reads supplied real parts, maps incomplete and unreal to equal amount zero with symmetric not-given versus fixed provenance, and maps cause-free unavailability to UNKNOWN.
- Resolved Date-range overlap keeps supplied inversion explicit, uses closed intervals, preserves occurrence multiplicity, retains ordered skipped/kept operand slots, and implements separate any-pair reached-filter and scalar-versus-list matched-container polarity scans.
- The separate whole-second baseline adds bounded `TimeOfDay`, admitted `LocalDateTime`, shared scalar `Instant`, executable UTC resolution, strict local chronology, and the already-truncated whole-hour shift core.
- The resolved sub-day difference computes `(second − first).tdiv unitSeconds` for a closed hours/minutes/seconds enum
- laws establish positive divisors, self-zero, swap negation, exact seconds and exact-unit recovery, while cases separate reverse truncation toward zero from floor division.
- `CivilDate.next?` uses checked construction
- laws prove it always advances the Gregorian coordinate by one, strict civil chronology raises that coordinate, and UTC resolution preserves strict local chronology.
- One finite `Berlin2024Profile` resolves fresh labels across the selected spring and autumn transition dates, rejects the spring gap, preserves the existing later-side autumn overlap policy, and fails closed elsewhere.
- Its spring-only calendar step changes a March 30 `02:xx` landing to March 31 `01:xx` and retains that adjusted clock on the next step.
- The bounded `DifferenceInDays` core counts those stateful landings in authored order, rejects pairs outside the consecutive spring slice, and has universal self-zero and swap-negation laws.

#### External evidence

- Pinned kernel 30.8.1 format/check/decode/comparison/calendar-add/instant-difference/range-overlap source and focused a12-dmkits Date/DateTime implementation and differentials establish the source account and triangulation.
- Groovy-dynamic kernel differentials directly establish positive and reverse fractional sub-day truncation.
- Selected whole-unit DST cases also agree through generated static Java, but that route does not separately cover the reverse-fraction discriminator.
- At reviewed a12-dmkits revision `71775c9905b057831253348c31ce39e321e61889`, focused controls lock both Date-range polarity scans through both kernel routes plus the interpreter, and separately lock constructed-Date reason/calendar consumers and `DifferenceInDays` calendar-step separators.
- This repository retains no portable Date, DateTime, construction, or Date-range observation

#### Exact boundary

- **Status:** implemented internally on narrow domains; external evidence partly pending.
- Date coverage includes the unbounded positive-era account, resolved three-part construction classification, and the proved calendar-coordinate successor/strict-monotonicity bridge.
- Date-range coverage includes closed occurrence-preserving overlap truth, both resolved operator shapes, and their filter-derived polarity scans.
- DateTime coverage includes the proved UTC local-order bridge, resolved `DifferenceInHours/Minutes/Seconds`, the finite Berlin 2024 transition profile, and resolved `DifferenceInDays` inside its consecutive spring slice.
- The construction classification and direct numeric component projection are implemented, but they do not yet retain calendar identity, compose temporal no-value reasons beyond extraction, implement date differences, or implement legacy month/year operations.
- Date-range raw cell classification, actual filter evaluation, paths/stars, row gates, and checked lowering remain outside the resolved operator capsule.
- Open:
  - Literal/field-format parsing and exact parser range
  - numeric offset truncation/runtime bounds for additions
  - empty/formal operands and general `Value` integration
  - other operator gates and polarity
  - DateTime difference operand/result checking and Number consumption
  - general Date/DateTime comparisons and checked integration
  - `DifferenceInDays` outside the finite spring profile and other calendar differences
  - other date arithmetic
  - full `Date(...)`/Time authoring
  - optional 1900 admission
  - fragments/range construction/Base Year
  - result admission/targets
  - general model-zone dispatch
  - spring-gap formal-error/cell integration
  - other Berlin dates/transitions/history
  - `Today`/`Now`
  - checked rule lowering
  - protocol exposure

### §7 — strings and patterns

#### Lean owners

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

#### Internal account

- Parsed String ingestion performs one non-overlapping CRLF-to-LF pass and caches the evaluated text
- LF and lone CR are preserved.
- Direct comparison, `Length`, and computation share that cached value, and the exact overlap counterexample prevents a second pass.
- Direct equality/inequality and `Length <`/`>=` have separate consuming clauses.
- Both direct String equality operators suppress an empty field or empty literal after preserving malformed input as UNKNOWN; distinct nonempty values fire only inequality.
- a parsed empty String retains present-empty placement while supplying the same clean-empty observation as absence
- `FieldFilled`/`FieldNotFilled` consume that empty observation rather than physical placement, and checked flat lowering admits String presence.
- Absolute String requiredness reuses the generated `FieldNotFilled` staging and preserves present-empty placement when attaching `.required`.
- shared String length counts UTF-16 code units.
- The computation slice separately models empty contribution, evaluated text, root storage, target-length routing/outcome, and delta projection.
- Strict violations, inclusive acceptance on both permitted sides, exact minimum/maximum boundaries, no-value/poison bypass, payload preservation, store/delta identity, and the nearest stronger term/application non-laws are proved
- its target check fails closed on produced CR/LF

#### External evidence

- Four operator-sensitive validation cases separate empty-content, empty-row, `"ABC"`, and six-character direct-equality/Length outcomes.
- The combined compact root-String record retains 13 copy/concatenation/root-storage cases and nine positive minimum/maximum target cases with exact boundaries, violations, absent/stale/equal priors, and padded blanks.
- Both kernel strategies agreed throughout before one-time compaction.
- Maintained a12-dmkits IF198 tests separately establish the present-empty placement and downstream field/group/required outcomes across both kernel strategies plus JVM/Node.
- Strict permitted-side acceptance, no-value/poison bypass, and CRLF/LF/lone-CR ingestion are internal Lean laws not separately exercised by retained local cases.
- Historical a12-dmkits triangulation had three final-empty-store mismatches and agreed with all nine target cases at projected delta and stored-value application granularity
- the [archive](archived/STRING-COMPUTATION-RAW-EVIDENCE.md) owns that detail.
- The retained strings remain conservative ASCII and do not externally establish broader Unicode or line-break behavior

#### Exact boundary

- **Implemented narrowly; ingestion external evidence pending:** direct validation equality/inequality, `Length <`/`>=`, checked String presence, absolute nonrepeatable String requiredness, present-empty checked placement, exactly-once evaluated-String CRLF normalization, checked nonrepeatable copy/literal/concatenation lowering through String root store/delta, and one positive `minLength` or `maxLength` target check with attempted-value `ERRORED` over no-line-break text.
- Repeatable/parent-gated String requiredness, a general document-ingestion bridge, group content, simultaneous or zero length bounds, patterns, enumerations, line-break permission, checked legal-charset definition/matching, registered custom-field validator context/result/message propagation, raw-type rule elimination, and general target-check ordering remain rejected or open.
- Input normalization does not grant a computed target permission to contain CR/LF.
- Coercion, lists, general computation lowering/scheduling, and every other String function remain rejected or open.
- The public normalized protocol and consumer capabilities have not been expanded to String

### §8 — enumerations and value lists

#### Lean owners

- [`Semantics/ScalarEquality.lean`](../A12Kernel/Semantics/ScalarEquality.lean)
- [`Semantics/Enumeration.lean`](../A12Kernel/Semantics/Enumeration.lean)
- [`Elaboration/EnumerationComparability.lean`](../A12Kernel/Elaboration/EnumerationComparability.lean)
- [`Semantics/ValueList.lean`](../A12Kernel/Semantics/ValueList.lean)
- their counterparts under [`Proofs/`](../A12Kernel/Proofs.lean), and their counterparts under [`Conformance/`](../A12Kernel/Conformance.lean)

#### Internal account

- Runtime Enumeration comparison uses a clean stored token or one lockstep positional category mapping
- repeated category tokens are legal, empty is not evaluated, unavailable input stays UNKNOWN, and every firing is VALUE.
- The separate direct-field static gate classifies identity labels as effectively textless, rejects a String/display-class mismatch, and accepts two display-bearing ordinary Enumerations exactly when their common-locale stored/display relation has no forward or reverse conflict.
- Trusted laws cover runtime projection, empty/unavailable/VALUE-only behavior, identity-label classification, pair/profile conflict symmetry, String admission, both rejection classes, and overall admission symmetry.
- The separate type-indexed Number/canonical-token value-list capsule preserves explicit present/empty/unknown cells, declared-tail and `Having` metadata, and distinct `AtLeastOne`, `No`, and `NotAll` clauses

#### External evidence

- Canonical §8 prose and pinned kernel source choose the static and runtime accounts.
- Maintained a12-dmkits Enum/category and comparability tests at revision `20230e403fa085c782534025f890669a975999a8` triangulate the broad classes plus identity labels, both conflict directions, identity participation in a display-bearing conflict, and compatible partial/disjoint mappings under accepted [`SPEC-2026-07-20-14`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-14--enumeration-direct-field-comparability-uses-effective-display-remapping).
- The focused runtime matrix currently has one kernel route plus peer triangulation
- a broader catalog smoke case exercises both kernel routes.
- This repository retains no portable §8 observation

#### Exact boundary

- **Implemented internally at two resolved runtime boundaries plus one independent static gate; external evidence pending:** runtime Enumeration begins after ordinary closed-domain/category/literal checks and validation observation
- static comparability begins after valid ordinary declarations and direct equality/inequality field shape
- value lists begin after expansion, comparability checking, and `Having` filtering.
- Table/open/dynamic/partial/duplicate-display declarations, literal and category-field admission, checked model integration, category use in lists/indices/paths, scalar value-list syntax, actual filtering, row gates, protocol exposure, and project-local portable evidence remain open

### §9 — repetition and iteration

#### Lean owners

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

#### Internal account

- Exact ordered selector ↔ relation bridges
- filter-before-consumer laws
- a shared full-environment correlated evaluator/relation bridge
- captured-origin, exact named-level resolution, outer-reference stability, self-match/exclusion, scalar-collapse rejection, and one-group observation-footprint results.
- The resolved RNU relation consumes caller-supplied ordered rows identified by complete repetition environments plus already-classified Number/token composite keys, excludes any UNKNOWN key, skips all-empty keys, matches optional empties within participating tuples, reuses scale-19 Number equality, retains complete firing clusters in scope order, and projects per-row UNKNOWN/not-fired/VALUE/OMISSION before ordinary verdict composition.
- Laws characterize exact cluster membership, firing, the internal false/unknown refinement, unique cluster identities, and the existence of a genuinely distinct matching peer.
- The separate checked one-star lowering retains explicit group paths, path-derived repeatable ancestry, exact singleton scope, operator-specific scale legality, model-derived raw checking, fail-closed runtime references, and pre-evaluation 1-based/unique candidate validation.
- The separate reopened-star domain recursively checks finite capacity under every actual parent, treats unbounded levels as open, validates positive sibling-unique coordinates, and bridges its structural result into resolved missing potential.
- The resolved group-presence state independently folds admitted content, error, and three-level relevance, then supplies scalar predicates, fixed-list tallies, strict numeric count availability, and parent-filled requiredness.
- Checked-wrapper theorems eliminate structural certificates
- they are not source-to-core semantic preservation

#### External evidence

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

#### Exact boundary

- **The admitted one-group runtime, checked-lowering, normalized firing-row, resolved RNU duplicate-relation, caller-supplied reopened-star completeness, and resolved group-presence/consumer slices are implemented; the wider cross-level and RNU additions remain external evidence pending:** the shared correlation core carries complete candidate/captured environments, while RNU defines one branch-independent relation and complete peer clusters before verdict composition.
- The RNU caller must supply the target in scope, unique complete repetition environments with canonical positive level coordinates, and one common declared key arity/order/kind schema
- the low-level evaluator remains total outside those obligations without a kernel-correspondence claim.
- Checked RNU scope/default or explicit `@From`, paths and key-schema validation, partial all-key relevance, one-RNU and negative/iteration/filter/parallel authoring restrictions, checked condition/whole-rule integration, error-field and peer-pointer projection, and protocol exposure remain open.
- The checked correlation elaborator and public protocol remain one-group only
- `Document` adaptation, checked group-instance/descendant enumeration and wildcardable relevance construction, checked construction of the reopened tree and ordered cell stream from model/path/document inputs, checked nested paths, multiple-star execution, joins, cross-group execution, general consumers, filtered-result polarity, optimization/refinement, computation, and partial validation over repeatable instances remain open

### §10 — paths and references

#### Lean owners

- [`Semantics/SemanticIndex.lean`](../A12Kernel/Semantics/SemanticIndex.lean)
- [`Proofs/SemanticIndex.lean`](../A12Kernel/Proofs/SemanticIndex.lean)
- [`Conformance/SemanticIndex.lean`](../A12Kernel/Conformance/SemanticIndex.lean)
- [`Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean)
- [`Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean)
- [`Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean)
- [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean)
- [`Conformance/Elaboration.lean`](../A12Kernel/Conformance/Elaboration.lean)
- [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean)

#### Internal account

- Resolved literal-key value lookup over unique canonical entries plus an unavailable-column marker
- validation clean-match-before-column-invalidity, computation column-invalidity-before-match, clean no-match/matched-empty equivalence, selected-target phase observation, nonmatching-target irrelevance, and signedness-aware empty-Number polarity
- model validation including field/group hierarchy separation and path-derived repeatable-scope coherence
- order-independent unique ID/path lookup
- shared parent walking
- corrected bare declaring-group → flag-gated model-wide unique resolution
- explicit repeatable-group path declarations
- exact one-star binding
- ambiguity, wrong group/scope, nested false-singleton scope metadata, and unsupported surface forms fail closed
- unique declaration and raw-policy coherence theorems

#### External evidence

- Maintained a12-dmkits indexed-read differentials at accepted revision `71775c9905b057831253348c31ce39e321e61889` establish match/no-match, phase precedence, selected-target invalidity, and presence as triangulation, but this repository retains no portable semantic-index observation.
- The full invalid-column matrix is strongest for Number keys while the canonical-token generalization is source-grounded.
- The compact validation record privately replays parent-relative, absolute, local-precedence, model-wide fallback, and ambiguity cases.
- Its four public static correlation associations retain code/class pairs for missing inner iteration, equality-scale mismatch, and a sibling-group reference plus acceptance for the ordering control
- acceptance does not establish runtime firing rows.
- [`LF6`](LEAN-FINDINGS.md#lf6--bare-name-resolution-is-local-or-global-not-an-ancestor-walk) records the bare-name correction

#### Exact boundary

- **Implemented for three narrow structured/resolved subsets:** non-repeatable flat paths, one absolute-or-direct-child-relative group-qualified star/correlation shape, and one already-resolved literal-key semantic-index Number value read.
- Parent-relative and bare forms remain outside the public correlation operation.
- Semantic-index key checking/normalization, presence/fill consumers, field-keyed indices, checked path integration, named labels, quoting, `RuleGroup`, concrete parser/renderer, nested/multi-star paths, and general repeatable lookup remain excluded
- not every excluded or rejected syntax has a retained diagnostic

### §11 — computations

#### Lean owners

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

#### Internal account

- Direct presence conditions distinguish clean not-true from exact-cause poison and evaluate recursive `And`/`Or` left-to-right.
- The seven resolved field-fill quantifiers consume one caller-supplied `filled | empty | uninstantiated | poison cause` stream with exact declared/instantiated range selection, operator-specific final decisions, source-level two-stage composite scans, exact internal reached poison, and suffixes unread after the full predicate decides
- trusted laws preserve the range fork, representative deciding-prefix equations, zero/one/two distinction, selected reached-poison separators, and observable read order.
- The operation-neutral selector returns no-match, the first selected operation, or first reached poison
- selection ends before operation evaluation.
- One resolved String table composes that selector once with the existing expression/target/delta step
- clean no-value, target rejection, and poison from the selected operation are terminal, and a holding head makes every suffix irrelevant through operation evaluation.
- Checked String-expression lowering resolves nonrepeatable copy leaves against one validated flat model, rejects wrong-kind and repeatable operands, preserves literal/concatenation tree order, checks raw cells with the same model, and delegates evaluation to the existing runtime expression.
- The checked two-alternative literal-Number desugaring admits direct Number/Boolean/Confirm/String presence guards, uses the same guard syntax but ordinary validation semantics, retains both guarded strict mismatches below `FieldFilled(target)`, preserves authored literal scale through exact-comparison admission, and emits through the resolved ERROR-rule boundary.
- Its overlap case demonstrates that selecting the stored first result does not imply generated-validation silence
- phase-specific poison/unknown, String empty/nonempty presence, and data-derived polarity remain visible.
- The separate String and Number slices keep checked expression identity, expression result, stored form, target outcome, delta, exact application, and downstream dependency meaning distinct without claiming a scheduler or document mutator

#### External evidence

- The project-reviewed [root-String compact bundle](../evidence/kernel-30.8.1/captures/string-computation-v1/semantic-observations.json) retains 22 clean/target-check observations
- the producer-certified [direct-cascade bundle](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/semantic-observations.json) and typed [`StringCascadeProjection.lean`](../A12Kernel/Evidence/StringCascadeProjection.lean) retain five cascade observations.
- The type-neutral V2 apply mechanism is source-grounded and triangulated by a12-dmkits IF126's String matrix.
- The field-fill scan is source-grounded and separately exercised by maintained a12-dmkits dual-kernel-route differentials for all seven operators, but this repository retains no portable field-fill observation.
- No retained project-local observation exercises direct presence/connectives, field-fill scans, alternative selection or selected-operation terminality, generated two-alternative validation, numeric expression/target/delta/application/dependency, mixed domain/poison order, or the newline family
- those surfaces remain `external evidence pending`

#### Exact boundary

- **Implemented narrowly and partially externally calibrated:** one nonrepeatable recursive direct-presence fragment
- all seven field-fill predicates over a caller-supplied already-expanded ordered slot stream
- first-match selection with resolved String selected-operation/target/delta integration
- an exact checked two-alternative literal-Number generated-rule fragment
- one String target and direct cascade
- and one already-resolved Number expression → stored form → ordinary fit-path target → delta → exact application → cause-free dependency chain.
- Open:
  - General computation authoring and target self-reference checks
  - warning-suppressed assignment and runtime target checks
  - checked singleton/default/larger-table authoring
  - common preconditions
  - tolerance/expression-valued generated validation
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

#### Lean owners

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

#### Internal account

- The verdict algebra preserves VALUE/OMISSION precedence and unknown
- numeric fillability supplies directional polarity across direct comparisons, admitted arithmetic including resolved power, and fixed tolerance.
- The seven resolved unfiltered field-fill quantifiers consume an extensional four-count tally, preserve declared/instantiated/mixed ranges, treat unavailable cells as neither filled nor empty, and expose fired polarity versus exact collapsed `FALSE_OR_UNKNOWN`
- trusted laws separate the two `NotExactlyOne` firing regions, the mixed predicate from `NotAll`, and validation collapse from computation poison.
- Resolved group presence independently folds admission, error, and three-level relevance, then gives scalar predicates, fixed-list predicates, strict numeric count, and parent-requiredness their consumer-specific projections.
- The reopened-star completeness boundary recursively derives structural tail missingness per actual parent and feeds the existing resolved-side disjunction without changing operator directions.
- The checked resolved-rule boundary preserves silent distinctions and retains a structured message plan until a fired verdict renders and attaches exact address, error code, severity, polarity, and text.
- The generated-computation fragment reuses that same post-fire boundary and demonstrates that ERROR severity does not fix message polarity.
- Flat partial evaluation remains a separate error-field/relevance consumer

#### External evidence

- Retained validation observations separate ordinary polarity and malformed connective outcomes but do not establish checked whole-rule assembly, generated two-alternative validation, error-code/severity independence, complete message rendering, hidden silent distinctions, or field-fill quantifiers.
- Maintained a12-dmkits multi-route quantifier differentials ground the seven unfiltered formulas and broader filter behavior, but this repository retains no portable field-fill observation.
- Direct ordering, arithmetic fillability, tolerance, partial relevance, integrated expression comparison, generated-rule details, and the label/value display refinements remain source/test anchored and project-locally `external evidence pending`.
- a12-dmkits revision `7f152509eea76822068955055b0d57d8ed930ca2` additionally triangulates IF193 group relevance/availability and IF194 nested-star aggregate polarity across both kernel strategies and the peer interpreter, without adding project-local portable evidence.
- Same-field alias polarity is source-inferred
- mixed formal-invalid/domain precedence is an explicit Lean refinement

#### Exact boundary

- **Implemented internally for the named clauses:** all seven unfiltered field-fill operators over a caller-supplied resolved tally
- resolved scalar/list/count/relative-required group-presence projections over caller-supplied group slices
- hierarchical structural-tail derivation over a caller-supplied reopened tree
- reduced fixed-right Number/String-Length validation
- known arithmetic and fixed-tolerance polarity
- one same-group nonrepeatable two-expression comparison
- one exact nonrepeatable structured-plan rule message rendered only after firing
- one checked two-alternative literal-Number generated rule on the same message boundary
- and one explicit nonrepeatable partial-validation gate.
- Open:
  - Checked group-instance/descendant enumeration and wildcardable relevance construction
  - checked construction of reopened trees and ordered cell streams from authored/model/document inputs
  - field-fill authored expansion
  - checked-cell/tally construction
  - `Having`
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
  - checked power integration and result-empty provenance
  - `BaseYear`
  - exact mixed-failure precedence
  - global/wildcard relevance
  - repeats/phantom rows
  - aggregates
  - uniqueness
  - orchestration

### §13 — message interpolation

#### Lean owners

- [`Semantics/ValidationRule.lean`](../A12Kernel/Semantics/ValidationRule.lean)
- [`Proofs/ValidationRule.lean`](../A12Kernel/Proofs/ValidationRule.lean)
- [`Conformance/ValidationRule.lean`](../A12Kernel/Conformance/ValidationRule.lean)

#### Internal account

- One total one-pass renderer consumes ordered, already-decoded parts.
- Plain text, resolved field-name input, and resolved field-value input remain separate constructors, so replacement bytes are never reparsed
- a decoded `$$` is ordinary dollar text at this boundary.
- Provider output wins exactly
- otherwise a nonempty model label precedes the debug display.
- Missing or empty display values use the exact format-supplied default.
- Checked flat and generated-computation-validation rules retain the structured plan and render it only after firing
- both silent verdicts are independent of every plan input.
- Laws cover provider priority, empty fallback, append/order composition, opaque nonempty values, and post-fire gating

#### External evidence

- Maintained a12-dmkits controls at revision `20230e403fa085c782534025f890669a975999a8` make both kernel routes agree on the scale-two `DocumentV2` dot default under US/German locales and on raw-CRLF message display while evaluation reads normalized LF
- JVM and Node lock the admitted provider/default/opacity policy.
- Accepted [`SPEC-2026-07-21-04`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-04--message-format-default-follows-the-actual-documentv2-profile) records the correction to the earlier locale implication.
- `$$`, repeated order, richer token families, untested presentation routes, and project-local portable observations remain source-derived or open, so correspondence remains `external evidence pending`

#### Exact boundary

- **Implemented internally, narrow:** parser-independent rendering after reference/display resolution and fired-only integration for checked nonrepeatable flat rules plus generated literal-Number computation validation.
- Raw `$...$` parsing, token/path/star/reference legality, lookup/provider invocation and locale/display conversion, repeatable/index/category/semantic-index/BaseYear tokens, field-owned format-error text, custom conditions, protocol exposure, and a complete §13 claim remain open

### §14 — custom conditions

#### Lean owners

- [`Semantics/CustomCondition.lean`](../A12Kernel/Semantics/CustomCondition.lean)
- [`Proofs/CustomCondition.lean`](../A12Kernel/Proofs/CustomCondition.lean)
- [`Conformance/CustomCondition.lean`](../A12Kernel/Conformance/CustomCondition.lean)

#### Internal account

- A resolved invocation carries four abstract channels unchanged: effective data view, full-versus-partial relevant entities, the complete formal-invalid payload, and the current error pointer.
- A pure total reached-leaf oracle maps true to fired VALUE and false to not-fired, never UNKNOWN or OMISSION
- the leaf is empty-row eligible.
- Trusted non-laws show that purity alone supplies neither data locality nor formal-invalid monotonicity

#### External evidence

- Kernel Java/TypeScript call paths, modern wrappers, and maintained a12-dmkits dual-route/JVM/Node controls establish the invocation and empty-eligibility account
- no project-local portable observation

#### Exact boundary

- **Implemented internally, narrow:** one successfully registered, already-reached pure callback leaf.
- Name resolution, missing registration, host exceptions/effects, call count/order, concrete data APIs, relevance/formal/pointer construction, parallel pointer precision, row/connective orchestration, static computation/`Having` rejection, message emission, checked lowering, protocol exposure, and full host-data fidelity remain open or explicitly outside the pure theory.
- Correspondence remains `external evidence pending`

## Cross-clause implementation notes

The §5/§11 numeric-computation entry is declaration-resolved rather than merely identified by `FieldId`: every atom retains its `FlatFieldDecl`, and the complete one-pass lowered tree rejects a non-Number declaration or unaudited power before any cell read. Its runtime then follows the lowered tree left-to-right, so a rewrite can change which of two poison causes is reached first; this source-grounded order and every numeric-computation outcome remain portable evidence pending.

### Resolved Number `FirstFilledValue`

- [`Semantics/FirstFilledValue.lean`](../A12Kernel/Semantics/FirstFilledValue.lean), [`Proofs/FirstFilledValue.lean`](../A12Kernel/Proofs/FirstFilledValue.lean), and [`Conformance/FirstFilledValue.lean`](../A12Kernel/Conformance/FirstFilledValue.lean) close one ordered Number-operand boundary shared by §3, §8, §10, and §11 after expansion, filtering, and partial-relevance classification.
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

- [`Semantics/NumericAggregate.lean`](../A12Kernel/Semantics/NumericAggregate.lean), [`Proofs/NumericAggregate.lean`](../A12Kernel/Proofs/NumericAggregate.lean), and [`Conformance/NumericAggregate.lean`](../A12Kernel/Conformance/NumericAggregate.lean) close validation-side Number `Sum`/`MinValue`/`MaxValue` after one side has already been expanded, filtered, and classified.
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

- This is internally complete at levels 1–2 and remains `external evidence pending`.
- Mixed-declaration resolved Sum evaluation is represented, but authored field-list/group expansion must still construct the per-source cells and uninstantiated signedness without losing declaration identity.
- The separate reopened-star capsule below can derive structural openness from a caller-supplied IF194 tree, but neither layer constructs the tree or ordered cell stream from authored paths and a `Document`.
- The older checked-row `NumberFold` uses the homogeneous embedding and projects only amount or cause, preserving its existing truth-only API while deliberately erasing fillability.
- The family does not share the prefix-terminating `FirstFilledValue` scan or operand-list empty substitution/fillability.
- Checked star/path lowering, actual filter execution, partial-validation relevance and row gating, computation aggregates, Date and other overloads, messages, protocol exposure, and project-local portable evidence remain open.
- a12-dmkits revision `20230e403fa085c782534025f890669a975999a8` accepted the all-empty correction under [`SPEC-2026-07-20-15`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-15--all-empty-number-aggregate-identity-is-both-directionally-fillable) and encounter order, staged precision, and per-declaration missingness under [`SPEC-2026-07-21-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-21-02--number-sum-preserves-encounter-order-staged-precision-and-missing-declaration-polarity).

### Reopened-star structural completeness

- [`Semantics/StarCompleteness.lean`](../A12Kernel/Semantics/StarCompleteness.lean), [`Proofs/StarCompleteness.lean`](../A12Kernel/Proofs/StarCompleteness.lean), and [`Conformance/StarCompleteness.lean`](../A12Kernel/Conformance/StarCompleteness.lean) close IF194's structural decision after first-star binding.
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

- [`Semantics/GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean), [`Proofs/GroupPresence.lean`](../A12Kernel/Proofs/GroupPresence.lean), and [`Conformance/GroupPresence.lean`](../A12Kernel/Conformance/GroupPresence.lean) close IF193's product-state and consumer boundary after concrete descendant scope and group relevance have been resolved.
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
- It does not enumerate descendants from paths or a model, adapt `Document`, decide which concrete repeat row belongs to which group instance, construct wildcardable `NONE`/`PARTIAL`/`FULL` relevance, auto-add globals, expand starred group lists, lower checked conditions, or orchestrate the generated mandatory rule and staged required finding.
- The a12-dmkits IF193 tri-engine matrix at revision `7f152509eea76822068955055b0d57d8ed930ca2` is focused external triangulation, but this repository retains no portable observation
- correspondence remains `external evidence pending`.
- Messages, protocol exposure, and wider validation orchestration remain open.

### Resolved Date-range overlap truth and operator scans

- [`Semantics/DateRangeOverlap.lean`](../A12Kernel/Semantics/DateRangeOverlap.lean), [`Proofs/DateRangeOverlap.lean`](../A12Kernel/Proofs/DateRangeOverlap.lean), and [`Conformance/DateRangeOverlap.lean`](../A12Kernel/Conformance/DateRangeOverlap.lean) close the §6 primitive truth core over admitted `FullDate` endpoints and one flat occurrence stream.
- `DateRangeDirection` keeps inversion explicit
- primitive overlap is symmetric, rejects either inversion, and treats equal/shared endpoints as overlapping.
- The flat any-pair scan preserves occurrences rather than deduplicating values, so a singleton does not pair with itself, two equal positions do, and an internal later pair can fire despite a disjoint head.
- Trusted laws characterize direction and the closed relation, prove symmetry, self-overlap iff ordered, both invalid guards, strict separation, singleton/pair reduction, and duplicate occurrence behavior.

- [`Semantics/DateRangeOverlapOperators.lean`](../A12Kernel/Semantics/DateRangeOverlapOperators.lean), [`Proofs/DateRangeOverlapOperators.lean`](../A12Kernel/Proofs/DateRangeOverlapOperators.lean), and [`Conformance/DateRangeOverlapOperators.lean`](../A12Kernel/Conformance/DateRangeOverlapOperators.lean) add the two resolved consuming scans over ordered operand groups.
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
- Kernel source and maintained a12-dmkits multi-route differentials establish truth and now lock the high-risk reached-scan polarity separators across both kernel routes plus the interpreter under accepted [`SPEC-2026-07-20-10`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-10--date-range-overlap-polarity-follows-the-reached-scan).
- This repository still retains no portable Date-range observation, so correspondence remains `external evidence pending`
- checked lowering, paths/stars, filter evaluation, cells, row gates, messages, equality/inequality, DateRange construction/extraction, protocol support, and project-local evidence remain open.

### Resolved three-part Date construction

- [`Semantics/DateConstruction.lean`](../A12Kernel/Semantics/DateConstruction.lean), [`Semantics/DateConstructionNumeric.lean`](../A12Kernel/Semantics/DateConstructionNumeric.lean), their matching [`Proofs/`](../A12Kernel/Proofs/) modules, and their matching [`Conformance/`](../A12Kernel/Conformance/) modules close a §6/§12 reason-and-verdict boundary and its first direct numeric consumer, both narrower than the general `Date(...)` surface still listed as open above.
- After component authoring/checking and a separate all-present calendar decision, `classifyDateConstruction3` combines the three availability states with supplied real/unreal reality and returns real `DateParts`, incomplete, present-but-unreal, or formally unavailable.
- Trusted laws characterize incomplete and UNKNOWN precedence, exact retention of supplied reality, both fired polarities, exact truth complementation, and the full-verdict non-law: `Valid` forgets the incomplete/unreal reason while `Invalid` preserves it.
- The direct numeric component layer then selects supplied real day/month/year values without re-running calendar reality, returns not-given zero for incomplete, fixed zero for unreal, and cause-free unavailability for UNKNOWN.
- Trusted laws establish exact selection, same-zero/distinct-provenance, unavailable-to-UNKNOWN behavior, and true-comparison polarity for all six fixed-right operators
- executable cases additionally lock one false comparison and separate symmetric Date missingness from the tempting grow-only encoding.

- Kernel 30.8.1 construction/validity and empty-row eligibility source plus maintained a12-dmkits Date-construction differentials establish the four classifications and selected externally visible outcomes
- the malformed `Valid` and malformed-plus-empty precedence branches are source-established rather than separately differential.
- The maintained “all-empty” differential also fills an unrelated time field, so truly content-empty row eligibility is likewise source-established rather than independently isolated
- this repository retains no portable Date observation.
- Exact component values/causes, raw/checked cells, two- and four-part forms, Base Year, constant-only authoring rejection, exact parser/component bounds, full-row gating, stored/computed target admission, checked lowering, and protocol exposure remain open.
- The current Lean result stops after direct day/month/year validation projection
- computation consumption, date differences, compositional temporal no-value propagation, and legacy-calendar identity remain open.
- Concrete calendar resolution is deliberately not implemented: kernel 30.8.1 uses a zone-aware hybrid `GregorianCalendar`, while the reusable `CivilDate` account is zone-free and proleptic, and the two accounts have reachable cutover and zone-discontinuity separators.

### `DifferenceInDays` finite-profile closure

- Kernel source counts signed model-zone `Calendar.DAY_OF_MONTH` steps, while the obvious reuse of `CivilDate.unixEpochDay` would impose a zone-free proleptic coordinate.
- Those accounts separate on a Berlin special-hour landing and across a skipped whole date.
- [`LF47`](LEAN-FINDINGS.md#lf47--differenceindays-needs-a-model-zone-calendar-step-account) records both reproduced discriminators.
- Accepted [`SPEC-2026-07-20-08`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-20-08--differenceindays-counts-model-zone-calendar-steps) records both kernel-route separators and the peer calendar-step reconciliation.
- Lean now enforces the narrower option: `Berlin2024Profile` exposes fresh-label resolution and stateful spring day stepping, and `DateTimeDayDifference` counts at most the three landings within that exact slice.
- Ordinary, threshold, reverse-sign, retained-adjusted-clock, elapsed-seconds non-equivalence, and unsupported cross-slice cases form the separating matrix.
- Empty/formal operand coercion, fillability/polarity, checked lowering, constructed-Date calendar identity, wider Berlin history, other zones, and protocol exposure remain later consumers rather than being inferred from this profile.

## Reference-process exposure

- The `a12-kernel-reference` executable exposes two disjoint intersections through the normalized [`PROTOCOL.md`](PROTOCOL.md) contract: the public §2/§3/§5/§10/§12 flat slice and the named §9 one-group captured-outer slice.
- [`Reference/Protocol.lean`](../A12Kernel/Reference/Protocol.lean) decodes bounded operation-specific models, paths, conditions or correlated `Having`, sparse flat or row-addressed cells, and row gates/candidates.
- [`Reference/Evaluator.lean`](../A12Kernel/Reference/Evaluator.lean) routes every admitted request through the corresponding existing checked elaborator and evaluator.
- [`Reference/Support.lean`](../A12Kernel/Reference/Support.lean) owns the current 0.3.0 identity, finite runtime classifiers, and generated schema-2 per-operation support, evidence boundaries, and diagnostic declaration mirrored in [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json).
- Requests have no per-request semantics selector
- the exact binary's `--manifest` plus a binary/release digest identifies the account.
- The internal §7 String-validation and §11 String-computation capsules are deliberately absent from this protocol until separate public capabilities close their transport, diagnostics, checked lowering, and support manifests.

- This process surface adds accessibility and fail-closed protocol assurance, not new kernel correspondence.
- Its accepted semantic clauses inherit the external-evidence statuses in the clause records above, while [`A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) locks transport behavior, deterministic output, diagnostics, exit codes, sample fixtures, current-manifest agreement, and current-suite controls.
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
- The current §2/§7 validation capsule covers direct Number field-to-literal equality/inequality/`<`/`>=`, Boolean/Confirm equality/inequality, Number/Boolean/Confirm presence, direct String equality, and String `Length <`/`>=`
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
- [`scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh) verifies that it imports every proof module, preserves the named human-readable theorem registry in [`A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean), rejects forbidden dependency directions, and uses [`A12Kernel/Trust/Environment.lean`](../A12Kernel/Trust/Environment.lean) to inspect every elaborated declaration in the trusted project modules.
- That environment audit rejects project axioms, unsafe or unclassified opaque/partial definitions, compiler/foreign substitutions, and every axiom dependency except `propext`, `Classical.choice`, and `Quot.sound`
- conformance remains a separate nontrusted executable-check lane.
