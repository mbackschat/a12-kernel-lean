# Cross-clause capabilities and gates

## Cross-clause owners

<a id="cross-clause-implementation-notes"></a>
<a id="resolved-number-aggregates"></a>
<a id="stringenumeration-aggregate-counts"></a>
<a id="stringenumeration-distinct-count"></a>
<a id="resolved-validation-group-presence"></a>
<a id="checked-group-star-terminals"></a>

These stable names help when a query crosses numbered clauses. Their capability status is already in the rows above.

<a id="cap-kernel-static-diagnostic-classes"></a>
#### Kernel static-diagnostic classes

- `owner-and-boundary`: [`StaticDiagnostic.lean`](../../A12Kernel/Elaboration/StaticDiagnostic.lean) owns the established `MVK_` vocabulary and exact identifiers; [`laws`](../../A12Kernel/Proofs/StaticDiagnostic.lean) guard enumeration distinctness and completeness. Each family projects its local refusals and returns `none` where no class is established. The bounded [Translate/Explain probe](../../A12Kernel/Conformance/ComputationTargetDiagnosticConsumer.lean) preserves accepted, mapped, and family-local unmapped outcomes. This is distinct from the public process's [`Reference.Support.DiagnosticCode`](../../A12Kernel/Reference/Support/Diagnostics.lean).
- `owner-and-boundary`: Coverage includes all three `FieldValuesNotUnique` overloads, the [shared group-admission gates](../IMPLEMENTATION-MAP.md#cap-shared-entity-list-group-admission), the [repeatable-operand rule locus](../IMPLEMENTATION-MAP.md#cap-date-range-repeatable-operand-locus) projected once at the resolver's own error type, singular DateRange overlap group refusal, the bounded token `FirstFilledValue` kind pair, [Boolean/Confirm constant computation target admission](../IMPLEMENTATION-MAP.md#cap-boolean-confirm-constant-computation-target-admission), fixed filled-group computation admission, computed Number, ordinary String and Enumeration targets, partial computed-Date targets, condition-pattern admission, and raw-String `Length`; the hardcoded pairings in [`ValidationProjection.lean`](../../A12Kernel/Evidence/ValidationProjection.lean) remain consolidation candidates when this vocabulary reaches them

<a id="cap-resolved-firstfilledvalue"></a>
#### Resolved `FirstFilledValue`

- `owner-and-boundary`: [`FirstFilledValue.lean`](../../A12Kernel/Semantics/FirstFilledValue.lean) and checked elaboration own ordered mixed String/stored-Enumeration selection; computation specializes the same selection rather than reimplementing it.

<a id="cap-resolved-number-aggregates"></a>
#### Resolved Number aggregates

- `owner-and-boundary`: [`NumericAggregate.lean`](../../A12Kernel/Semantics/NumericAggregate.lean) and [`NumericAggregate/`](../../A12Kernel/Elaboration/NumericAggregate/) own checked direct/plain-star/filtered-star streams, ordered precision-50 folds, validation/computation projections without a second iterator, the combiner family's normalized universal partial-extent gate, and numeric value count's existential extent per current iteration row. Full-validation `Sum` selects the exact measured in-capacity cell projection for a plain star, and checked group `NumberOfValueInFields` selects its separately measured in-capacity computation projection, while the immutable checked document retains every over-limit formal cell; extrema and distinct count retain the complete formal-cell view pending their own capacity evidence.
- `owner-and-boundary`: [`StarPath.lean`](../../A12Kernel/Elaboration/StarPath.lean) owns the separate universal and existential predicates.

<a id="cap-string-enumeration-aggregate-counts"></a>
#### String/Enumeration aggregate counts

- `owner-and-boundary`: [`TokenDistinctCount.lean`](../../A12Kernel/Elaboration/TokenDistinctCount.lean) and [`TokenValueCount.lean`](../../A12Kernel/Elaboration/TokenValueCount.lean) reuse checked entity-list topology while retaining token/category identity and family polarity. Token value count uses the same existential partial extent internally as the numeric overload; Kernel source shares the loop, but the token partial runtime matrix remains externally uncalibrated. The value-count-specific starred-group surface admits the measured sole terminal-repeatable String group through common stored-projection group certification, serves full validation and checked computation from a dedicated whole-group carrier, and selects an in-capacity projection before computation classifies content.
- `owner-and-boundary`: The fixed nonrepeatable path group remains a separate full-validation-only surface. Group-scope retention, assurance, and per-cell projection are owned by [token group expansion](../IMPLEMENTATION-MAP.md#cap-token-group-expansion).

<a id="cap-boolean-confirm-value-count"></a>
#### Boolean/Confirm value count

- `owner-and-boundary`: [`BooleanValueCount.lean`](../../A12Kernel/Elaboration/BooleanValueCount.lean) applies the distinct `True`/`False` field-kind matrix and derives fixed canonical tokens from checked direct/plain-star/filtered-star values. Existing scalar and addressed computation plus generated mismatch validation retain fixed scale 0, exact source/filter references, omitted-tail movement, and reached formal poison. Empty Confirm remains unfilled, every direct or starred `False` Confirm source is rejected statically, and scalar plans reject repeatable sources explicitly. Group-scope retention, assurance, reference projection, checked-document full validation, and fieldwise single-axis starred-group computation are owned by [Boolean/Confirm group value count](../IMPLEMENTATION-MAP.md#cap-boolean-confirm-group-value-count).

<a id="cap-reopened-star-structural-completeness-and-addressing"></a>
#### Reopened-star structural completeness and addressing

- `owner-and-boundary`: [`StarCompleteness.lean`](../../A12Kernel/Semantics/StarCompleteness.lean), [`StarAddressing.lean`](../../A12Kernel/Semantics/StarAddressing.lean), and checked document/path owners keep topology independent of filled cells.

<a id="cap-resolved-group-presence-both-arms"></a>
#### Resolved group presence, both arms

- `owner-and-boundary`: [`GroupPresence.lean`](../../A12Kernel/Semantics/GroupPresence.lean) owns one classified group-product state consumed through distinct predicate, count, requiredness, full-validation, and partial-validation projections, plus the separate computation-arm presence projection and its `Nat` count. The two must not be merged behind a phase flag: over the same descendant cells a formally invalid one is unavailable in validation and *counts* in computation. [`laws`](../../A12Kernel/Proofs/GroupPresence.lean) confine that disagreement to cells carrying a finding — monotonicity is unconditional in the measured direction, agreement holds in the clean region — and prove nothing about the row, structural, or relevance dimensions the computation projection does not consume.

<a id="cap-checked-group-star-terminals"></a>
#### Checked group-star terminals

- `owner-and-boundary`: [`StarGroup.lean`](../../A12Kernel/Elaboration/StarGroup.lean) distinguishes terminal repeatable-row counts from one evaluation per selected starred ancestor for a nonrepeatable terminal. Structural predicates retain every instantiated terminal row, while the numeric starred-group count excludes rows beyond declared capacity and uses the reduced-universal partial gate at the group operand path.

<a id="cap-resolved-date-range-overlap-truth-admission-and-scans"></a>
#### Resolved Date-range overlap truth, admission, and scans

- `owner-and-boundary`: [`DateRangeOverlap.lean`](../../A12Kernel/Semantics/DateRangeOverlap.lean) owns primitive truth, [`DateRangeOverlapOperators.lean`](../../A12Kernel/Semantics/DateRangeOverlapOperators.lean) owns ordered scans, and [`DateRangeOverlap.lean`](../../A12Kernel/Elaboration/DateRangeOverlap.lean) owns checked singular/plural admission and full-validation assembly.

<a id="cap-resolved-direct-date-construction-and-base-year-sources"></a>
#### Resolved direct Date construction and Base-Year sources

- `owner-and-boundary`: [`DateConstruction.lean`](../../A12Kernel/Semantics/DateConstruction.lean), [`BaseYearDateSource.lean`](../../A12Kernel/Semantics/BaseYearDateSource.lean), and checked component owners share typed Date construction without collapsing calendar provenance.

<a id="cap-berlin-legacy-calendar-arithmetic"></a>
#### Berlin legacy calendar arithmetic

- `owner-and-boundary`: [`BerlinLegacyCalendarArithmetic.lean`](../../A12Kernel/Semantics/BerlinLegacyCalendarArithmetic.lean) owns source-offset day mutation, compute-time month/year mutation, and completed month/year qualification over decoded labels plus exact instants. [`DateTimeDayDifference.lean`](../../A12Kernel/Semantics/DateTimeDayDifference.lean) alone owns the stateful day-count algorithm and concrete-profile dispatch; it is not elapsed-duration division.

<a id="cap-addressed-numeric-placement-and-execution-seam"></a>
#### Addressed numeric placement and execution seam

- `owner-and-boundary`: [`AddressedNumericLeaf.lean`](../../A12Kernel/Elaboration/AddressedNumericLeaf.lean) owns `CheckedAddressedNumericTarget`, which carries actual-environment selection, iteration, and the target policy for a repeatable Number target, and admits an operand at any scope that target's own scope binds rather than requiring equality. Five completed consumers: `FieldValueAsNumber`, `RangeAsNumber`, String `Length`, direct Number assignment, and a DateRange endpoint's numeric component. A further consumer joins by supplying a certified source and reusing the existing result/application owners; it does not add a second placement representation.

- `boundary`: Placement against the declaring group is **containment**, not equality: the target is admitted from its own group and from any ancestor, and refused only from a group it does not lie at or below. A declaring-group validity check runs first, because `[]` is a prefix of every path and would otherwise admit every placement vacuously. The same rule holds in the shared [`AddressedRepeatableTarget.lean`](../../A12Kernel/Elaboration/AddressedRepeatableTarget.lean) certificate and in the Enumeration, `FieldValueAsString`, `DateFromDateTime`, and `TimeFromDateTime` copies. L is the [declaring-group gate checkpoint](../SOURCES.md#src-computation-declaring-group-gate), whose correlation row is the String sibling-star representative over one enclosing repeatable parent and does not extend to other carriers or deeper nesting; fixed-target placement is a different gate and is not widened by this one.

<a id="cap-certified-direct-number-source-certificate"></a>
#### Certified direct-Number source certificate

- `owner-and-boundary`: Direct Number assignment owns the certificate carrying a Number source with exact source/target scale. `Abs`, the three `Round` modes, and `Min`/`Max` operand lists wrap that same certificate rather than introducing another source representation, so each adds only its own node semantics and result-scale contract.

<a id="cap-ordered-number-pair-certificate"></a>
#### Ordered Number-pair certificate

- `owner-and-boundary`: Shared by [`AddressedNumberField.lean`](../../A12Kernel/Elaboration/AddressedNumberField.lean) for two-operand `+`/`−`/`×`, [`AddressedNumberDivision.lean`](../../A12Kernel/Elaboration/AddressedNumberDivision.lean), and [`AddressedNumberPower.lean`](../../A12Kernel/Elaboration/AddressedNumberPower.lean). Three completed consumers, each retaining its own derived-scale rule and warning-suppression selection while delegating arithmetic to the already-separated precision-50 scalar owner.

<a id="cap-derived-numeric-scale-admission"></a>
#### Derived numeric scale admission

- `owner-and-boundary`: [`NumericScale.lean`](../../A12Kernel/Elaboration/NumericScale.lean) owns `NumericScaleSummary` and the `==`/`!=` comparison predicate that admits a declared computed-target scale rather than requiring equality. Consumed by `Min`/`Max` operand-list admission and by the comparison gate itself; a capable list may pad up to a larger declared scale while a capable larger derived scale is rejected.

<a id="cap-normalized-messagepointer"></a>
#### Normalized `MessagePointer`

- `owner-and-boundary`: [`MessagePointer.lean`](../../A12Kernel/Semantics/MessagePointer.lean) owns resolved field identity plus concrete/wildcard/unknown repetition coordinates. Four completed consumers: validation, computation, registered custom-field, and reached custom-condition error channels. Exact `CellAddr` embeds losslessly but remains a separate type, so wildcard and unknown never project as exact cells.


### SG5 group-operand capabilities

<a id="cap-shared-entity-list-group-admission"></a>
#### Shared entity-list group admission

- `state`: implemented for the represented group slot and measured gates.
- `boundary`: the shared checker resolves an authored group in both repetition shapes, satisfies arity from the slot, and reads kind and category from one recursive declaration expansion.
- `boundary`: a starred path may terminate at a nonrepeatable group through the existing terminal-presence certificate; the authored group and its equivalent explicit fields are admitted, retain the reopened star, and publish the same wildcarded expansion references.
- `boundary`: star and indirect ancestor/descendant refusals are shared; an unstarred repeatable level below an earlier star projects `MVK_NO_WILDCARD`, while expansion-kind diagnostics remain operator-specific and unmapped when no class is established.
- `boundary`: exact non-wildcard field and fixed-group identities share one authored encounter scan; the duplicate whose second occurrence arrives first supplies `MVK_DUPLICATE_PARAM1`, starred group occurrences remain distinct, strict overlap follows as `MVK_DUPLICATE_PARAM2`, and singleton direct-field cardinality stays structurally separate.
- `boundary`: the plural String-literal value-list form projects `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` only for a homogeneous Date-group expansion; its String-group control is retained, while Number and heterogeneous group refusals stay unmapped.
- `boundary`: token `FirstFilledValue` projects `MVK_NO_BOOLY_ALLOWED` for the exact two-Confirm fixed-group or two-direct-stored-field expansion and `MVK_VARYING_TYPES_NOT_ALLOWED` for the same carriers in ordinary-evaluated-String-then-Number declaration order; raw or custom String policies, reverse order, starred or filtered carriers, wider kind combinations, and wider widths remain unmapped.
- `owner`: [`FieldEntityList.lean`](../../A12Kernel/Elaboration/FieldEntityList.lean), [`StarGroup.lean`](../../A12Kernel/Elaboration/StarGroup.lean), [`TokenEntityValueList.lean`](../../A12Kernel/Elaboration/TokenEntityValueList.lean), [`TokenFirstFilledValue.lean`](../../A12Kernel/Elaboration/TokenFirstFilledValue.lean), [`StaticDiagnostic.lean`](../../A12Kernel/Elaboration/StaticDiagnostic.lean), [`ValidationCondition/Reference.lean`](../../A12Kernel/Elaboration/ValidationCondition/Reference.lean), and [`FlatModel.groupSubtreeFields`](../../A12Kernel/Elaboration/Flat/Model.lean).
- `case`: [shared group admission cases](../../A12Kernel/Conformance/FieldEntityGroupOperand.lean), [token group cases](../../A12Kernel/Conformance/TokenEntityGroupOperand.lean), and [carrier-boundary and precedence cases](../../A12Kernel/Conformance/TokenFirstFilledValue.lean).
- `assurance`: E closed for the represented admission boundary and diagnostic matrix; P partial through family completeness certificates plus diagnostic enumeration/code uniqueness; L locks the nonrepeatable Date/String value-list pair, fixed-group kind matrix, below-star terminal/refusal pair, and nine complete-code duplicate/overlap rows with both repair witnesses at a12-dmkits [source registry](../SOURCES.md); starred Date value-list remains `external evidence pending`; C/X/Q none.
- `source`: [entity-list group gates](../SOURCES.md#src-entity-list-group-gates), [group-carrier admission sweep](../SOURCES.md#src-group-carrier-admission-sweep), [group-carrier static admission](../SOURCES.md#src-group-carrier-static-admission), and [group-carrier duplicate precedence](../SOURCES.md#src-group-carrier-duplicate-precedence).
<a id="cap-number-group-aggregates"></a>
#### Number group aggregates

- `state`: partial.
- `boundary`: the Number carrier retains the authored group and a certified complete recursive Number expansion with uniform signedness.
- `boundary`: full validation resolves the operand-bounded `(row × field)` extent from model repeatability, binding only levels above the operand from the outer environment.
- `boundary`: checked-document computation resolves one shared rich group operand. Starred `Sum`, extrema, and distinct count retain its complete checked-cell projection, while Number value count selects its in-capacity projection before computation-phase content classification.
- `boundary`: `FieldValuesNotUnique`, `Sum`, extrema, distinct count, and Number value count share the checked operand resolver; ordinary aggregates and value count deliberately select different projections, and expansion-kind diagnostics remain keyed by operator.
- `limit`: non-Number, empty, and mixed-signedness expansions fail locally without inventing a Kernel class.
- `boundary`: the resolver emits cells declaration-major in stable model declaration order, with each declaration's canonical row order inside it.
- `limit`: Kernel correspondence for that order remains open on Number consumers; [token group expansion](../IMPLEMENTATION-MAP.md#cap-token-group-expansion) owns the separately calibrated fixed and direct-single-star `FirstFilledValue` fragments.
- `limit`: only instantiated rows are enumerated and `hasUninstantiatedTail` is false; correspondence for a declared but uninstantiated tail is open.
- `limit`: fixed-group computation, Number value-count validation, and Number group routes outside the measured checked computation remain `external evidence pending`; partial validation and raw-`Document` group routes remain refused.
- `owner`: [`NumberEntityList.lean`](../../A12Kernel/Elaboration/NumberEntityList.lean), [`CheckedStarDocument.lean`](../../A12Kernel/Elaboration/CheckedStarDocument.lean), and [`NumericAggregate/Entities.lean`](../../A12Kernel/Elaboration/NumericAggregate/Entities.lean).
- `case`: [group extent and admission cases](../../A12Kernel/Conformance/FieldEntityGroupOperand.lean) and [checked computation cases](../../A12Kernel/Conformance/NumberEntityGroupComputation.lean).
- `proof`: [`checkedNumberEntityGroup_expansion_complete`](../../A12Kernel/Proofs/NumberEntityList.lean), [`checkedNumberEntityGroup_checkedComputationAggregate_usesRichProjection`](../../A12Kernel/Proofs/NumericAggregateElaboration.lean), and [`checkedNumberEntityGroup_checkedComputationValueCount_usesCapacityProjection`](../../A12Kernel/Proofs/NumericAggregateElaboration.lean).
- `assurance`: E/P closed for retention, full-validation extent, checked-computation resolver delegation, ordinary rich projection, and value-count capacity projection; L Kernel-locks starred combiner computation and starred group value-count values, poison, empty identity, and over-capacity exclusion while the wider routes remain partial; C/X/Q none.
- `source`: [group runtime and reference correction](../SOURCES.md#src-group-runtime-and-reference), [group runtime differential](../SOURCES.md#src-field-values-not-unique-group-runtime), [Number group computation runtime](../SOURCES.md#src-number-group-computation-runtime), and [Number group value-count capacity](../SOURCES.md#src-number-group-value-count-computation-capacity).
- `remains`: [group runtime](../SEMANTICS-GAPS.md#gap-sg5-number-token-group-runtime).

<a id="cap-token-group-expansion"></a>
#### Token group expansion

- `state`: partial.
- `boundary`: the token carrier retains the authored group and a certified recursive expansion, pairing every reached cell with the declaration and operand that read it.
- `boundary`: a group authors no read form, so every member is read stored and homogeneity applies across the entire expansion rather than only between authored slots.
- `boundary`: full-validation `FieldValuesNotUnique` and token aggregate routes consume the shared operand-bounded extent.
- `boundary`: the `NumberOfValueInFields` group surface admits one sole terminal-repeatable starred group as an internally already-many stored-projection slot and delegates its certification to the common token mechanisms. Its dedicated checked whole-group carrier counts the complete recursive extent in full validation and selects only in-capacity cells before checked computation classifies their String content, leaving independent over-repetition findings on the immutable checked document.
- `boundary`: its separate fixed-group surface admits one sole nonrepeatable ordinary path group through the common token entity-list gates. `RuleGroup` is unrepresented, and a group inside repeatable scope remains refused rather than being assigned an implicit row.
- `boundary`: checked-document partial token value-list evaluation filters reached group cells per expanded declaration and records incomplete extent on the one authored group slot unless every expanded declaration has a covering wildcard identifier across the levels that slot reopens.
- `limit`: Kernel calibration for that partial route establishes a starred String group's equivalence to its explicit expansion under wildcard and concrete-row relevance and establishes that those shapes disagree. The exact group-fixture orientation and equal reached-cell selection remain externally unverified; fixed or nested groups, Enumeration projection, the values side, and the other quantifiers are internally executable but remain `external evidence pending`.
- `boundary`: full-validation token `FirstFilledValue` consumes the shared checked extent for exactly one fixed group whose authored terminal is nonrepeatable, including recursive repeatable descendants, or for one terminal single-level starred group whose expansion contains only direct token declarations; the measured starred form may precede one nonrepeatable direct fallback.
- `boundary`: group cells remain declaration-major with canonical row order inside each declaration; the shared stop-at-first evaluator preserves selected token and reached-empty-prefix missingness, including a no-row group star before the direct fallback, while ignoring every suffix after selection.
- `extent`: [Number group aggregates](../IMPLEMENTATION-MAP.md#cap-number-group-aggregates) owns the shared resolver's ordering and uninstantiated-tail limits.
- `limit`: Kernel calibration establishes starred String-group admission and a two-row cross-declaration full-validation count reaching the measured threshold, plus exact checked-computation counts, in-capacity malformed poison, and over-capacity content exclusion. Fixed nonrepeatable String-group static admission is measured; fixed-group runtime and stored-Enumeration group expansion with its all-expanded-declarations literal gate remain internally executable with `external evidence pending`; the surface has no `RuleGroup` constructor.
- `limit`: a fixed operand whose authored terminal is itself repeatable, multi-level or nonterminal starred groups, starred groups with nested declarations, mixed lists other than the one measured direct fallback, computation, partial validation, and legacy raw-document routes remain explicitly unsupported by this first-filled path.
- `owner`: [`TokenEntityGroup.lean`](../../A12Kernel/Elaboration/TokenEntityGroup.lean), [`TokenEntityList.lean`](../../A12Kernel/Elaboration/TokenEntityList.lean), [`TokenValueCount.lean`](../../A12Kernel/Elaboration/TokenValueCount.lean), [`TokenEntityValueList.lean`](../../A12Kernel/Elaboration/TokenEntityValueList.lean), and [`TokenFirstFilledValue.lean`](../../A12Kernel/Elaboration/TokenFirstFilledValue.lean).
- `case`: [token group cases](../../A12Kernel/Conformance/TokenEntityGroupOperand.lean) and [token group value-count cases](../../A12Kernel/Conformance/TokenGroupValueCount.lean).
- `proof`: [`checkedTokenEntityGroup_expansion_complete`](../../A12Kernel/Proofs/TokenEntityValueList.lean), [`checkedTokenEntityGroup_projections_stored`](../../A12Kernel/Proofs/TokenEntityValueList.lean), [`checkedTokenEntityGroup_partialExtentRelevant_iff`](../../A12Kernel/Proofs/TokenEntityValueList.lean), [`checkedTokenValueCountGroup_checkedComputation_usesCapacityProjection`](../../A12Kernel/Proofs/TokenValueCount.lean), and the generic [token first-filled scan and projection laws](../../A12Kernel/Proofs/TokenFirstFilledValue.lean).
- `assurance`: E/P closed for retention, per-cell projection, recursive fixed-group full-validation extent, checked partial value-list relevance, starred and fixed-group value-count authoring through shared group certification, the starred String-group checked-computation capacity projection, and the direct-single-star specialization through existing generic laws
- `assurance`: L locks starred group-versus-explicit partial `No` equivalence within each relevance shape and disagreement between shapes, sole starred String-group full-validation admission and cross-row threshold, and fixed nonrepeatable String-group value-count admission at clean a12-dmkits [source registry](../SOURCES.md), plus the checked-computation exact values, in-capacity malformed clear, and over-capacity match/malformed exclusions at clean [source registry](../SOURCES.md), and the unstarred nested-row/direct-before-nested matrix and the four fixed-order and six starred-order/polarity rows at [source registry](../SOURCES.md), C/X/Q none.
- `source`: [group-operand admission](../SOURCES.md#src-field-values-not-unique-group-admission), [group runtime differential](../SOURCES.md#src-field-values-not-unique-group-runtime), [token group partial runtime](../SOURCES.md#src-token-group-partial-runtime), [token starred-group value-count full-validation runtime](../SOURCES.md#src-token-value-count-group-runtime), [token starred-group value-count computation capacity](../SOURCES.md#src-token-group-value-count-computation-capacity), [token fixed-group value-count admission](../SOURCES.md#src-token-value-count-fixed-group-admission), [fixed-group first-filled order](../SOURCES.md#src-group-first-filled-runtime-order), and [starred-group first-filled order](../SOURCES.md#src-star-group-first-filled-runtime-order).
- `remains`: [group runtime](../SEMANTICS-GAPS.md#gap-sg5-number-token-group-runtime).

<a id="cap-temporal-group-uniqueness"></a>
#### Temporal group uniqueness

- `state`: implemented for checked-document full validation.
- `boundary`: temporal uniqueness retains one recursively complete group expansion with one exact declared format, resolves every declaration at every instantiated descendant row below the operand's own bound depth, and compares the resulting combined stream by exact stored text.
- `owner`: [`TemporalValuesNotUnique.lean`](../../A12Kernel/Elaboration/TemporalValuesNotUnique.lean).
- `case`: [temporal group cases](../../A12Kernel/Conformance/TemporalEntityGroupOperand.lean).
- `proof`: [`checkedTemporalUniquenessGroup_expansion_complete`](../../A12Kernel/Proofs/ValuesNotUnique.lean) and [`checkedTemporalUniquenessGroup_resolveValidationCore`](../../A12Kernel/Proofs/ValuesNotUnique.lean).
- `assurance`: E/P closed for retention, complete expansion, shared-resolver delegation, recursive full-validation extent, explicit-field agreement, and distinct/empty controls; L locks the exact two-row group-versus-explicit matrix at clean a12-dmkits [source registry](../SOURCES.md); C/X/Q none.
- `source`: [group-carrier static admission](../SOURCES.md#src-group-carrier-static-admission) and [temporal group runtime](../SOURCES.md#src-temporal-field-values-not-unique-group-runtime).
- `remains`: group-form message emission remains under [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration); external calibration beyond the exact unstarred two-row checkpoint remains pending.

<a id="cap-boolean-confirm-group-value-count"></a>
#### Boolean/Confirm group value count

- `state`: partial.
- `boundary`: Boolean/Confirm value count retains the authored group and every descendant declaration; the constant-specific kind gate applies to each descendant.
- `boundary`: the structural reference projection expands the retained group; checked-document full validation reads the operand-bounded recursive `(row × field)` extent and separately preserves hierarchical declared-but-uninstantiated capacity for count fillability.
- `boundary`: one constant-indexed checked computation carrier admits a sole terminal-repeatable starred group with one repeatable axis and no selected declaration below a deeper repeatable group, delegates the constant-specific fieldwise kind gate to the existing Boolean/Confirm group carrier, and selects only in-capacity cells before computation-phase token classification. `True` therefore admits Boolean and Confirm declarations in any order while `False` admits only Boolean declarations. Full validation remains on the complete projection, preserving independent over-repetition findings on the immutable checked document.
- `boundary`: a separate constant-indexed fixed computation carrier admits exactly two direct declarations in one nonrepeatable group, delegates the common group certificate, requires the measured declaration-kind sequence, and selects the complete addressed extent through the shared checked group scan. The measured `True` form contains Boolean then Confirm, and the measured `False` form contains two Booleans.
- `limit`: other fixed declaration kinds or orders, recursive or wider fixed groups, groups containing declarations below a deeper repeatable level, partial validation, and legacy raw-`Document` group routes remain refused.
- `owner`: [`BooleanValueCount.lean`](../../A12Kernel/Elaboration/BooleanValueCount.lean).
- `case`: [Boolean/Confirm group cases](../../A12Kernel/Conformance/BooleanEntityGroupOperand.lean).
- `proof`: [`checkedBooleanValueCountGroup_expansion_complete`](../../A12Kernel/Proofs/TokenValueCount.lean), [`checkedBooleanValueCountGroup_resolvedCheckedValidationSide`](../../A12Kernel/Proofs/TokenValueCount.lean), [`checkedBooleanValueCountStarredGroup_checkedComputation_usesCapacityProjection`](../../A12Kernel/Proofs/TokenValueCount.lean), [`checkedBooleanValueCountFixedGroup_checkedComputation_usesCompleteProjection`](../../A12Kernel/Proofs/TokenValueCount.lean), and the generic [`valueCount_singleton_match_tail`](../../A12Kernel/Proofs/NumericAggregate.lean).
- `assurance`: E/P closed for retention, complete expansion, shared concrete-extent plus hierarchical-tail composition, second-row agreement with the explicit expansion, open-tail growability, full-capacity fixedness, the all-false control, the fieldwise one-axis computation carrier and capacity projection, the two-direct-field fixed computation carrier and complete projection, and fixed-group validation movement.
- `assurance`: L locks the exact finite one-level full-validation matrix and `False` mixed-group refusal at clean a12-dmkits [source registry](../SOURCES.md), the starred `True` and `False` capacity and shape matrices at clean [source registry](../SOURCES.md), and the fixed-group exact `2`, `1`, `0`, malformed-clear, distinct Boolean/Confirm formal causes, and full-extent VALUE polarity at reviewed [source registry](../SOURCES.md), which accepts [`SPEC-2026-08-24-04`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-04--numberofvalueinfields-group-computation-ignores-over-capacity-cell-content-for-measured-number-string-and-booleanconfirm-overloads) and [`SPEC-2026-08-24-05`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-05--fixed-boolean-group-numberofvalueinfields-computation-expands-its-direct-fields); C/X/Q none.
- `source`: [group-carrier static admission](../SOURCES.md#src-group-carrier-static-admission), [Boolean value-count group runtime](../SOURCES.md#src-boolean-value-count-group-runtime), [Boolean/Confirm starred-group value-count computation capacity](../SOURCES.md#src-boolean-group-value-count-computation-capacity), [False Boolean-group value-count computation capacity](../SOURCES.md#src-false-boolean-group-value-count-computation-capacity), [Boolean-group value-count computation shape matrix](../SOURCES.md#src-boolean-group-value-count-computation-shape-matrix), and [Boolean fixed-group value-count computation](../SOURCES.md#src-boolean-fixed-group-value-count-computation).
- `remains`: wider fixed, nested-repeatable, partial-validation, and raw-document group routes remain under [SG5 group runtime](../SEMANTICS-GAPS.md#gap-sg5-number-token-group-runtime).

<a id="cap-group-operand-reference-projection"></a>
#### Group-operand reference projection

- `state`: implemented for admitted entity-list, group-list, nonrepeatable group-presence, and Boolean/Confirm count operands.
- `boundary`: a group contributes recursive descendant field pointers and never a group pointer; starred and unstarred forms differ by the shared coordinate rule rather than by expansion membership.
- `boundary`: one depth rule uses the referenced field's repeatable scope, preserves the bound concrete prefix, and wildcards every reopened level, including repeatable descendants of an unstarred group.
- `owner`: [`Reference.lean`](../../A12Kernel/Elaboration/ValidationCondition/Reference.lean) and [`FlatModel.groupSubtreeFields`](../../A12Kernel/Elaboration/Flat/Model.lean).
- `case`: [ordinary reference cases](../../A12Kernel/Conformance/ValidationRule/OrdinaryReference.lean).
- `proof`: [reference projection laws](../../A12Kernel/Proofs/ValidationCondition/Reference.lean).
- `separator`: retained cases fail if expansion stops at direct children, an unstarred group is wildcarded like a starred one, a fixed group is expanded only one level, or an unbound descendant is dropped or pinned.
- `assurance`: E/P closed for the named projection; L partial; C none; X none; Q none.
- `source`: [group runtime and reference correction](../SOURCES.md#src-group-runtime-and-reference).
- `consumer`: Analyze and Explain must distinguish exact-reference membership from broader reachability; a field reachable only through expansion has no direct referrer.
- `limit`: an admitted unstarred repeatable group-presence operand still fails closed when its own level is unbound because no witness selects a concrete or wildcard coordinate.
- `remains`: [unstarred repeatable group-presence coordinates](../SEMANTICS-GAPS.md#gap-sg5-unstarred-repeatable-group-presence-reference); unbound deeper descendants on other carriers, filtered-star operands, `RepetitionNotUnique`, and the message-record channel remain under [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).

## Reference-process exposure

[`Reference/Support.lean`](../../A12Kernel/Reference/Support.lean) owns the current finite normalized support declaration; [`Reference/Protocol.lean`](../../A12Kernel/Reference/Protocol.lean) and [`Reference/Evaluator.lean`](../../A12Kernel/Reference/Evaluator.lean) decode and dispatch only the declared flat and one-group correlation operations. [`PROTOCOL.md`](../PROTOCOL.md) owns the wire contract, [`ARTIFACTS.md`](../ARTIFACTS.md) the shipped files, and the current capability kits their self-contained handovers. Reference exposure never upgrades internal or external evidence status.

## Current external-evidence gate

<a id="empty-handling-coverage-rule"></a>

[`EVIDENCE.md`](../EVIDENCE.md) is the sole exact inventory of retained bundles, case identities, digests, replay commands, and finite claim limits. This map records only whether a semantic boundary has local calibration.

An internally closed capsule may remain `external evidence pending`. Before claiming kernel correspondence, select a coherent family, identify realistic wrong accounts, and retain the smallest source-maintained observation shape that separates them. Source reading, peer agreement, and theorem proof remain distinct from local calibration. The open cross-family calibration obligation is [`SG12`](../SEMANTICS-GAPS.md#sg12--retained-kernel-correspondence-coverage).

## Trusted theorem surface

[`A12Kernel/Proofs.lean`](../../A12Kernel/Proofs.lean) is the trusted theorem root and [`A12Kernel/TrustAudit.lean`](../../A12Kernel/TrustAudit.lean) is its exhaustive audit registry. Current counts belong only in [`PLAN.md`](../PLAN.md) as a verified resumption checkpoint; this map records coverage, not repository size.

## Maintenance rule

Update the affected clause or shared-owner entry when an implemented boundary, proof/non-law status, external-assurance dimension, public exposure, or consumer qualification changes. Replace the old sentence; do not append a capsule narrative. Do not copy open-work details from [`SEMANTICS-GAPS.md`](../SEMANTICS-GAPS.md), source facts from [`SOURCES.md`](../SOURCES.md), evidence inventories from [`EVIDENCE.md`](../EVIDENCE.md), or current sequencing from [`PLAN.md`](../PLAN.md).
