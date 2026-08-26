# Checked data and clauses 1 to 4

### Immutable checked-document construction

<a id="cap-physical-document-topology"></a>
#### Physical document topology

- `boundary`: Finite model-relative rows and placed raw cells; contiguous 1-based repetition identity; scope, proof-retained duplicate-placement, raw-classification, and over-repetition checks
- `owner`: [`Document.lean`](../../A12Kernel/Document.lean), [checked-document elaboration](../../A12Kernel/Elaboration/CheckedDocument.lean), [checked-document proofs](../../A12Kernel/Proofs/CheckedDocument.lean)
- `assurance`: E/P closed; L/C none; Q Analyze/Explain probe
- `remains`: SG1 closed; family ingestion stays with its clause

<a id="cap-checked-addressed-reads"></a>
#### Checked addressed reads

- `boundary`: Absent, present-empty, admitted value, formal finding, and structural address failure remain distinct; prepared field checks are cached
- `owner`: [`CheckedDocument.lean`](../../A12Kernel/Elaboration/CheckedDocument.lean), [`Observation.lean`](../../A12Kernel/Semantics/Observation.lean)
- `assurance`: E/P closed; selected C/X through flat evidence
- `remains`: Wider ingestion: [SG5–SG8](../SEMANTICS-GAPS.md)

<a id="cap-preliminary-index-findings"></a>
#### Preliminary index findings

- `boundary`: Model-derived required/unique index findings are staged over immutable topology without mutating the document
- `owner`: [`CheckedIndexPreliminary.lean`](../../A12Kernel/Elaboration/CheckedIndexPreliminary.lean)
- `assurance`: E/P closed; source-grounded; C none
- `remains`: Wider index orchestration: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-required-group-projections"></a>
#### Required/group projections

- `boundary`: Checked absolute requiredness and group-presence input consume the same checked document while retaining separate authored-validation views
- `owner`: [`CheckedRequired.lean`](../../A12Kernel/Elaboration/CheckedRequired.lean), [`CheckedGroupPresence.lean`](../../A12Kernel/Elaboration/CheckedGroupPresence.lean)
- `assurance`: E/P closed for admitted slice; selected C
- `remains`: Wider group terminals: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)


## Taxonomy by clause

### §1 — truth and verdict algebra

<a id="cap-three-valued-truth"></a>
#### Three-valued truth

- `boundary`: Closed `K` algebra with ordered `and`/`or` and no invented generic negation
- `owner`: [`Core.lean`](../../A12Kernel/Core.lean)
- `assurance`: E/P exhaustive; L/C/X/Q none
- `remains`: Closed for this algebra

<a id="cap-validation-verdict"></a>
#### Validation verdict

- `boundary`: `valid`/`invalid`/`unknown` result algebra, polarity combination, and exact laws
- `owner`: [`Core.lean`](../../A12Kernel/Core.lean), [`Verdict.lean`](../../A12Kernel/Proofs/Verdict.lean)
- `assurance`: E/P exhaustive; L/C/X/Q none
- `remains`: Closed for this algebra

<a id="cap-shared-condition-tree-control-flow"></a>
#### Shared condition-tree control flow

- `boundary`: Parametric tree shape with family-specific leaves and decisive left-to-right folds
- `owner`: [`Condition.lean`](../../A12Kernel/Semantics/Condition.lean)
- `assurance`: E/P closed for stated folds; computation ordering has L locks in the inventory above
- `remains`: New leaf families remain clause-owned


### §2 — empty scalar comparisons and row gate

<a id="cap-boolean-confirm-string-scalar-equality"></a>
#### Boolean/Confirm/String scalar equality

- `boundary`: Nonrepeatable equality/inequality with explicit no-value behavior; stored Boolean/Confirm text admits only the fixed lowercase tokens, ignores declared `@NotInD` display tokens, retains exact formal causes/codes, and is certified against its stored text by checked-document construction
- `owner`: [`ScalarText.lean`](../../A12Kernel/Semantics/ScalarText.lean), [`ScalarEquality.lean`](../../A12Kernel/Semantics/ScalarEquality.lean), [`CheckedDocument.lean`](../../A12Kernel/Elaboration/CheckedDocument.lean), [`Flat/Condition/`](../../A12Kernel/Elaboration/Flat/Condition/)
- `assurance`: E/P closed for ordinary stored Boolean/Confirm and admitted scalar values; upstream L for token ingestion; selected C/X for Boolean/Confirm
- `remains`: Wider String policy: [SG7](../SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion)

<a id="cap-number-comparison-and-empty-polarity"></a>
#### Number comparison and empty polarity

- `boundary`: All six comparisons, scale-19 normalization, and directional fillability for empty operands
- `owner`: [`NumericComparison.lean`](../../A12Kernel/Semantics/NumericComparison.lean), [`NumericValidation/`](../../A12Kernel/Elaboration/NumericValidation/)
- `assurance`: E/P closed for admitted routes; selected C/X; upstream L partial
- `remains`: Wider authoring: [SG5](../SEMANTICS-GAPS.md#sg5--numeric-authoring-and-target-completion)

<a id="cap-string-length-comparison"></a>
#### String length comparison

- `boundary`: UTF-16 length projected to Number comparison with directional empty behavior
- `owner`: [`String.lean`](../../A12Kernel/Semantics/String.lean), [`StringLength.lean`](../../A12Kernel/Proofs/StringLength.lean)
- `assurance`: E/P closed; source-grounded; C/X none
- `remains`: Wider Unicode/pattern boundary: [SG7](../SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion)

<a id="cap-temporal-comparison"></a>
#### Temporal comparison

- `boundary`: Six-way Date/Time/DateTime comparison over admitted literal, field, `Today`, `Now`, and Base-Year sources
- `owner`: [`DateComparison.lean`](../../A12Kernel/Semantics/DateComparison.lean), [`TimeComparison.lean`](../../A12Kernel/Semantics/TimeComparison.lean), [`DateTimeComparison.lean`](../../A12Kernel/Semantics/DateTimeComparison.lean)
- `assurance`: E/P closed for stated sources; peer-triangulated; C/X none
- `remains`: Wider operands and zones: [SG6](../SEMANTICS-GAPS.md#sg6--temporal-authoring-calendar-and-target-completion)

<a id="cap-presence-and-row-content"></a>
#### Presence and row content

- `boundary`: Direct presence for admitted scalar kinds plus the structural content-row gate
- `owner`: [`FlatValidation.lean`](../../A12Kernel/Semantics/FlatValidation.lean), [`GroupPresence.lean`](../../A12Kernel/Semantics/GroupPresence.lean)
- `assurance`: E/P closed for admitted slice; selected C/X
- `remains`: Repeatable/group breadth: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)


### §3 — formal checking and phase observation

<a id="cap-phase-projection"></a>
#### Phase projection

- `boundary`: One checked cell projects formal invalidity to validation UNKNOWN and computation poison while preserving exact cause
- `owner`: [`Cell.lean`](../../A12Kernel/Cell.lean), [`Observation.lean`](../../A12Kernel/Semantics/Observation.lean)
- `assurance`: E/P closed; selected C through flat evidence
- `remains`: New causes must extend the shared cell owner

<a id="cap-raw-string-ingestion"></a>
#### Raw String ingestion

- `boundary`: Absent/present-empty/decoded String, CRLF normalization, declared pattern hooks, and prepared context
- `owner`: [`RawString.lean`](../../A12Kernel/Elaboration/RawString.lean), [`StringContext.lean`](../../A12Kernel/Elaboration/StringContext.lean)
- `assurance`: E/P closed for admitted profile; selected C; arbitrary patterns injected
- `remains`: Complete String/custom ingestion: [SG7](../SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion)

<a id="cap-group-list-diagnostics"></a>
#### Group-list diagnostics

- `boundary`: Condition-level group-list/count owners retain duplicate, overlap, root, wildcard, multiplicity, and unknown classes. A separate rule-owned static projection uses the error-field declaration, not the rule group, for the exact one-level ordinary-path matrix: scalar `GroupFilled`, sole `AtLeastOneGroupFilled`, authored `AllGroupsFilled(repeatable, fixed)`, and sole/paired `NumberOfFilledGroups(...) > 0`. The first operand must be a non-root ordinary path to the exact repeatable declaration; `RuleGroup`, a repeatable root, a fixed descendant sharing the level, a root peer, or an overlapping fixed peer remains unmapped. Each represented row returns admitted, the exact diagnostic, or explicitly unmapped, and constructs no runtime condition for newly admitted shapes.
- `boundary`: The shared whole-rule projector maps the already-derived error-field-reference and negative-iteration assembly errors to their exact Kernel classes; the latter retains the directly positive-guarded admission control
- `owner`: [condition assembly](../../A12Kernel/Elaboration/ValidationCondition/Assembly.lean), [rule-owned projection](../../A12Kernel/Elaboration/ValidationRuleGroupOperand.lean), [whole-rule projection](../../A12Kernel/Elaboration/ValidationRule.lean), [group-operand proofs](../../A12Kernel/Proofs/ValidationRuleGroupOperand.lean), [whole-rule proofs](../../A12Kernel/Proofs/ValidationRule.lean), [group-operand cases](../../A12Kernel/Conformance/ValidationRule/GroupOperandDiagnostic.lean), [whole-rule cases](../../A12Kernel/Conformance/ValidationRule/OrdinaryAdmission.lean)
- `assurance`: E closed for the named static matrix and two whole-rule projections P closed for the typed decision table and negative-iteration projection the error-field-reference projection is E closed without a separate theorem L at a12-dmkits [source registry](../SOURCES.md) Q closed for the direct Translate/Explain checked-client decision C/X none
- `remains`: Nested/different repeatable scopes, other carriers, operators, arities, authored orders, executable newly admitted group-list/count conditions, and other assembly refusals: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-rnu-key-diagnostics"></a>
#### RNU key diagnostics

- `boundary`: Repeated/unknown keys and three missing-repeatable shapes; parallel paths stay unmapped.
- `owner`: [elaboration](../../A12Kernel/Elaboration/RepetitionNotUnique.lean)
- `assurance`: E mapped; L [source](../SOURCES.md#src-group-list-rnu-admission-correction); P/X/Q none
- `remains`: Parallel identity and other refusals: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-formal-output-boundary"></a>
#### Formal output boundary

- `boundary`: Checked values retain formal findings separately from later public message construction
- `owner`: [`CheckedDocument.lean`](../../A12Kernel/Elaboration/CheckedDocument.lean), [`ValidationRule.lean`](../../A12Kernel/Semantics/ValidationRule.lean)
- `assurance`: E/P closed for retained findings; selected C
- `remains`: Codes, locale, and complete output: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration)


### §4 — required property

<a id="cap-requiredness-scope"></a>
#### Requiredness scope

- `boundary`: Absolute, nearest-repeatable, and direct-parent modes resolve without erasing the declaration gate
- `owner`: [`Required.lean`](../../A12Kernel/Semantics/Required.lean), [`CheckedRequired.lean`](../../A12Kernel/Elaboration/CheckedRequired.lean)
- `assurance`: E/P closed for resolved scope; selected C on absolute scalar cases
- `remains`: Wider generated orchestration: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)

<a id="cap-generated-required-staging"></a>
#### Generated required staging

- `boundary`: Full and partial staging traverse model-owned declarations and reuse the same checked certificate
- `owner`: [`CheckedRequired.lean`](../../A12Kernel/Elaboration/CheckedRequired.lean), [`PartialValidation.lean`](../../A12Kernel/Semantics/PartialValidation.lean)
- `assurance`: E/P closed for admitted scalar boundary; selected C
- `remains`: Repeatable/group breadth: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)

<a id="cap-group-content-gate"></a>
#### Group-content gate

- `boundary`: Structural row content and group error state remain independent of field values and authored findings
- `owner`: [`GroupPresence.lean`](../../A12Kernel/Semantics/GroupPresence.lean), [`CheckedGroupPresence.lean`](../../A12Kernel/Elaboration/CheckedGroupPresence.lean)
- `assurance`: E/P closed for resolved product; source-grounded
- `remains`: Complete group lists/counts: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)
