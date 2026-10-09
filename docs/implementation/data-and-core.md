# Checked data and clauses 1 to 4

Record keys and the `L`/`C`/`X`/`Q` assurance letters are defined once in the [hub's record-key legend](../IMPLEMENTATION-MAP.md#record-key-legend).

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

<a id="cap-having-caller-capabilities"></a>
#### Having caller capabilities

- `error-membership`: Temporal comparisons count marked filter reads separately from candidate reads. DateRange overlap counts selected fields and groups without treating reopened wildcard rows as ordinary iteration. [Reader matrices](../../A12Kernel/Reference/Dm/HavingGlobalAdmissionLocks.lean) match the retained [membership](../sources/having-filter-probes.md#src-having-error-reference) and [scope](../sources/having-filter-probes.md#src-having-reference-scope) grids.
- `error-binding`: [Error-reference projection](../../A12Kernel/Elaboration/ValidationCondition/ErrorReferences.lean) distinguishes membership from binding each rule iteration level. Number/token and temporal source scopes retain actual outer reads, not the whole available binding environment. Indexed, recursive numeric and root-group-only unresolved carriers remain explicit unknown classifications.
- `iteration-guards`: Field-fill and Number/token uniqueness reuse per-level guard analysis with declared independent wildcard capacity. [Calibration](../sources/having-filter-probes.md#src-having-iteration-guards) covers finite direct/field-star lists; group/indexed and temporal-uniqueness guards remain unclassified.
- `reader-runtime`: Ordinary singular/plural DateRange conditions preserve captured binding through certification. Token first-filled computation comparisons reuse ordered selection, filter effects and producer dependencies. Internal reader-to-rule/scheduler cases cover positive/false branches, filtered selection, prefix stopping and fresh producer reads; the retained [population replay](../CONFORMANCE-COVERAGE.md#axis-r--population-replay) now exercises additional overlap and uniqueness instances. The [bounded caller replay](../sources/having-filter-probes.md#src-having-caller-runtime) calibrates 160 both-arm instances across selection, empty, malformed, capacity and kept-successor cases. Wider compositions and emitted reference-set transport remain open.
- `token-field-reader`: String/Enumeration token comparisons lower bracketed direct-field counterparts through the shared validation/computation reader. [Both-arm calibration](../sources/having-filter-probes.md#src-having-first-field) covers both orders and equality polarities; literal/first-filled counterparts remain supported. Bare String counterparts refuse without exact syntax-code projection.

- `named-validity`: [Shared type-validity evaluation](../../A12Kernel/Semantics/CustomFieldValidity.lean) preserves missing-validator failure through Having and the enclosing rule handler. [Reader locks](../../A12Kernel/Reference/Dm/HavingTypeValidityLocks.lean) distinguish VALUE from ordinary aggregate truth and retain branch bypasses; computation retains target clearing. [Runtime calibration](../sources/having-filter-probes.md#src-having-predicate-family) separates malformed predicate input from malformed selected target. Ordinary named-type composition remains [SG7](../gaps/strings-and-messages.md#gap-sg7).

- `filter-callers`: Raw validation value-list adapters, numeric aggregate views, and Number/token first-filled scans now use the existing failure-capable selector. Reached temporal conversion and missing-World failures stay outside UNKNOWN; unavailable stored/formal text or group capabilities refuse explicitly. Pure selection helpers remain semantic projections, not runtime adapters.
- `filter-caller-checks`: [Caller locks](../../A12Kernel/Conformance/HavingCallerEffects.lean) cover four executable raw callers, admitted controls, missing World, missing formal Number text/group readers, temporal conversion failure, empty selections and connective reachability. The [runtime law](../../A12Kernel/Proofs/Correlation.lean) propagates a failed filter independently of target classification. These are internal transport checks, not new Kernel calibration.
- `filter-checked-text`: A checked-document callback read now retains a Number placement’s formal text when its checked cell is unchanged. A changed parsed-only value still needs an overlay carrying its own text. Both phases are guarded against missing unchanged text and stale changed-value text; stored-text and group adapters keep their established contracts.

- `outer-uniqueness`: Ordinary validation DSL lowering now composes direct-key `RepetitionNotUnique` with filters through the existing checked whole-rule evaluator. The checked condition certifies lexical declaration separately from error-field row binding, preserving default duplicate scope when rebinding. [Reader locks](../../A12Kernel/Reference/Dm/RepetitionNotUniqueLocks.lean) cover root/row hosts, default/authored scope, composite keys and both connective orders.
- `outer-uniqueness-assurance`: A guard excluding one duplicate still leaves its partner firing; a changed lexical certificate is refused. Existing [coherence and rebinding laws](../../A12Kernel/Proofs/ValidationCondition.lean) cover both identities. These are internal composition checks against [spec/07 §6](../../spec/07-repetition-and-iteration.md#6-repetitionnotunique-precisely-), with new filter-composition calibration pending under H10.
- `outer-uniqueness-replay`: The 2026-10-09 unchanged-population [replay](../CONFORMANCE-COVERAGE.md#axis-r--population-replay) admits 32 previously unsupported uniqueness rule instances, all matching retained Kernel outcomes. That ordinary-reader gain does not calibrate the new mixed filter compositions.
- `computation-language-features`: Common and alternative preconditions refuse outer uniqueness and `CustomCondition` with `MVK_ERROR_INVALID_LANGUAGE_FEATURE`, per [spec/09 §1](../../spec/09-computations.md#1-the-ground-rules). Admitted filter twins distinguish that gate from earlier key-read failures. Unsupported uniqueness key/path forms remain [SG9](../gaps/paths-and-groups.md#gap-sg9); this adds no computation uniqueness evaluator.

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
- `assurance`: E/P closed for stated folds; computation ordering has L locks in the inventory above; Q includes a cold finite Compile consumer whose specialized conjunction plan was exhaustively reconciled with the Lean evaluator
- `remains`: New leaf families remain clause-owned


### §2 — empty scalar comparisons and row gate

<a id="cap-boolean-confirm-string-scalar-equality"></a>
#### Boolean/Confirm/String scalar equality

- `boundary`: Nonrepeatable equality/inequality with explicit no-value behavior; stored Boolean/Confirm text admits only the fixed lowercase tokens, ignores declared `@NotInD` display tokens, retains exact formal causes/codes, and is certified against its stored text by checked-document construction
- `owner`: [`ScalarText.lean`](../../A12Kernel/Semantics/ScalarText.lean), [`ScalarEquality.lean`](../../A12Kernel/Semantics/ScalarEquality.lean), [`CheckedDocument.lean`](../../A12Kernel/Elaboration/CheckedDocument.lean), [`Flat/Condition/`](../../A12Kernel/Elaboration/Flat/Condition/)
- `assurance`: E/P closed for ordinary stored Boolean/Confirm and admitted scalar values; upstream L for token ingestion; selected C/X for Boolean/Confirm
- `assurance`: the String operand's **no-value** rule is Kernel-retained under both operators at the [inequality checkpoint](../sources/having-filter-probes.md#src-string-inequality-empty-operand). Inequality is the operator that could have refuted it, since a participating empty would differ from any nonempty literal and fire; it stays silent while both live controls fire. A formally invalid String operand remains unmeasured and inequality cannot settle it, because an unknown leaf and a suppressed one both fail to fire.
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
- `boundary`: a field operand whose path names a group is refused in the Kernel's gate order, the walk's class placed by the error field's group, then a root's class, then the kind gate, on the flat and the addressed route; only a miss on the reference is displaced, so an invalid rule group answers first
- `owner`: [`FlatValidation.lean`](../../A12Kernel/Semantics/FlatValidation.lean), [`GroupPresence.lean`](../../A12Kernel/Semantics/GroupPresence.lean), [field-slot resolver](../../A12Kernel/Elaboration/Flat/Model.lean), [field-slot cases](../../A12Kernel/Conformance/GroupOperandRepetitionWalk.lean)
- `assurance`: E/P closed for admitted slice; selected C/X
- `assurance`: the row gate admits a comparison holding a `NumberOfFilledFields`, `NumberOfFilledGroups` or `NumberOfDifferentValues` count on its small side on an instance without content, and only there, from anywhere in the condition rather than composed through `And`. Both sides of all six comparisons are Kernel-measured at the [rule-bucket](../sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate) and [`And`](../sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and) checkpoints, and the gate is locked beside the group-count cases in [`ValidationCondition.lean`](../../A12Kernel/Conformance/ValidationCondition.lean), the field-count cases in [`FilledFieldGroupCount.lean`](../../A12Kernel/Conformance/FilledFieldGroupCount.lean) and the reader's cases in [`LowerLocks.lean`](../../A12Kernel/Reference/Dm/LowerLocks.lean); the tolerance comparisons follow the Kernel's source unmeasured, and every other numeric atom stays `false`.
- `assurance`: a once rule whose error field lies in a repeatable root group runs without the root's content gate, Kernel-measured at the same checkpoint; a rule reading a second root would too, but Lean refuses a cross-root read.
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
- `boundary`: The same rule-owned projection checks the exact sole text-indexed group under `NumberOfFilledGroups(...) > 0` independently through the checked group/index/token selector, then returns `MVK_SEMANTIC_INDEX_NOT_ALLOWED` at every error-field locus, as measured with the error field in the root, outside the rule group, beside the group and inside it ([checkpoint](../sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)). An unindexed group stays unmapped on this surface, and no runtime count form is added.
- `boundary`: The shared whole-rule projector maps the already-derived error-field-reference and negative-iteration assembly errors to their exact Kernel classes; the latter retains the directly positive-guarded admission control
- `boundary`: The group-operand walk: an iteration-scope mismatch whose error scope strictly prefixes the derived scope becomes `unboundOperandLevel`, classed by the computation arm's `UnboundOperandLevel` table from the rule group and the error field's group, ahead of the negative-condition gate; every validation carrier entry takes the error field's group as `writtenGroup` when its caller supplies it, and the shared entity-list, star-source and filled-field helpers take it without a default, placing the refusal by the same table, as do the rule-owned projection's outside locus and the numeric comparison's aggregate operand list, while the addressed comparison takes none ([inbound](../sources/inbound-handbacks.md#inbound-2026-09-24d-star-containment)); the group-list and count resolvers admit the repeatable root the rule sits in; and the group-list root gate precedes its star gate, alone and beside another operand
- `boundary`: the sole `NumberOfFilledGroups` over a lone repeatable group projects its arity class ahead of the walk's refusals when the rule's error field lies at or below the counted group and inside the rule's group, whichever such group declares the rule, at any depth and on a repeatable root; an error field outside the counted group projects the missing star, and one outside the rule's group the containment class ([checkpoint](../sources/group-list-and-capacity-probes.md#src-count-placement-overlap-list-grid), [checkpoint](../sources/group-list-and-capacity-probes.md#src-count-placement-by-error-field)).
- `boundary`: A read's levels are bound by the error field's scope when it lies at or below the rule group and by nothing when it lies outside, and a level holding the error field passes the walk claiming no class ([checkpoint](../sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)). At a level the rule's iteration binds, from the declaring group or the error field's, the field slot meets its kind gate, and a climbing read meets it where it lands ([inbound](../sources/inbound-handbacks.md#inbound-2026-09-25i-rule-iteration), [inbound](../sources/inbound-handbacks.md#inbound-2026-09-26-climbing-read)). The group list walks a starred operand's levels above its first star before its own gates ([inbound](../sources/inbound-handbacks.md#inbound-2026-09-25-operator-gates-wait)).
- `owner`: [condition assembly](../../A12Kernel/Elaboration/ValidationCondition/Assembly.lean), [rule-owned projection](../../A12Kernel/Elaboration/ValidationRuleGroupOperand.lean), [whole-rule projection](../../A12Kernel/Elaboration/ValidationRule.lean), [group-operand proofs](../../A12Kernel/Proofs/ValidationRuleGroupOperand.lean), [whole-rule proofs](../../A12Kernel/Proofs/ValidationRule.lean), [group-operand cases](../../A12Kernel/Conformance/ValidationRule/GroupOperandDiagnostic.lean), [whole-rule cases](../../A12Kernel/Conformance/ValidationRule/OrdinaryAdmission.lean), [validation-bound resolver](../../A12Kernel/Elaboration/SingleGroup.lean), [walk cases](../../A12Kernel/Conformance/GroupOperandRepetitionWalk.lean), [reading-scope cases](../../A12Kernel/Conformance/ReadingScope.lean)
- `assurance`: E closed for the named static matrix and two whole-rule projections P closed for the typed decision table and negative-iteration projection the error-field-reference projection is E closed without a separate theorem L at a12-dmkits [source registry](../SOURCES.md) Q closed for the direct Translate/Explain checked-client decision C/X none
- `assurance`: E closes the walk rows on every carrier the rule surface represents, the position rows on its eleven group carriers, the projection's shapes and the three operand-level sources, and the containment row on a field read, plus the walk batch grid's rows on the carriers the reading-scope cases name, [SG9](../gaps/paths-and-groups.md#gap-sg9) listing the rows a carrier still refuses ([checkpoint](../sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)); P keeps the negative-iteration theorem as a disjunction with the walk's refusal; L at the [walk inbound](../sources/inbound-handbacks.md#inbound-2026-09-24c-group-operand-walk); C/X/Q none.
- `assurance`: E closes the walk's index gates for a level beside the error field's group on the peer's route model, and its outermost-first order and the type gate's measured kind table, every row and its reverse locked on `FieldKind.indexTypeGate` directly and the route rows on the local route model, with the within-kind configuration and the walk past a legal pair of two kinds locked as assumptions: the name, type and multiple-index classes, the index class into an unkeyed error field, an unkeyed level below an admitted one, and a legal parallel iteration refused without a class, plus the group rows on nine carriers, where under the legal pair only the field slot meets its own gate; P proves the walk refuses exactly the scope lists that leave a level; L at the [route inbound](../sources/inbound-handbacks.md#inbound-2026-09-25-parallel-index-gates) and the [type-table inbound](../sources/inbound-handbacks.md#inbound-2026-09-25b-index-type-table).
- `assurance`: E/P close the indexed carrier's exact refusal, group/index/token retention, locus-irrelevant refusal, and invalid-selection fail-closed control. L locks the exact indexed `NumberOfFilledGroups` row at the [reviewed PR2 carrier checkpoint](../sources/inbound-group-operand-batches.md#src-pr2-semantic-index-carrier-matrix); C/X/Q none.
- `remains`: Nested/different repeatable scopes, other indexed carriers, comparisons, operators, arities, authored orders, executable newly admitted group-list/count conditions, and other assembly refusals: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-rnu-key-diagnostics"></a>
#### RNU key diagnostics

- `boundary`: every key and the `@From` scope are read and walked from the error field's group, which the entry requires, the scope's walk before its emptiness, then the duplicate gate asked, then the group and raw gates over the whole list, then one branch: with `@From` the scope's field, repeat and containment classes and the parallel-iteration class for keys in parallel repeatable groups, without it the shared-path, rule-group and three missing-repeatable shapes. A rule at a repeatable root holding every key directly takes the root as its reference group. Keys whose own groups diverge below one repeatable group are refused without a class.
- `owner`: [elaboration](../../A12Kernel/Elaboration/RepetitionNotUnique.lean)
- `assurance`: E mapped; L [source](../sources/group-list-and-capacity-probes.md#src-group-list-rnu-admission-correction), the [gate-order](../sources/inbound-handbacks.md#inbound-2026-09-26f-gate-order), [empty-scope](../sources/inbound-handbacks.md#inbound-2026-09-26h-empty-scope), [paired-gate](../sources/inbound-handbacks.md#inbound-2026-09-26k-paired-gates) and [repeatable-root](../sources/inbound-handbacks.md#inbound-2026-09-26l-repeatable-root) handbacks, locked in [cases](../../A12Kernel/Conformance/RepetitionNotUniqueDiagnostic.lean) on every row a plain field path and this model spell, the index-free scope rows on the unkeyed `Notes`, and the repeatable-root runtime in [whole-rule cases](../../A12Kernel/Conformance/RepetitionNotUniqueValidationRule.lean); P/X/Q none
- `remains`: category, starred, index-selected and marked keys or scopes, an empty fixed scope, the carried-over parallel index-gate classes, and keys diverging below one repeatable group: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

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

- `boundary`: Structural row content and group error state remain independent of field values and authored findings. Content therefore has **two constituents and either suffices**: an admitted descendant cell anywhere in the subtree, or an instantiated row anywhere in it.
- `boundary`: The computation arm's `NumberOfFilledGroups` folds a **mixed** operand list whose forms contribute unlike quantities: a fixed operand's zero-or-one by descendant content, and a starred repeatable operand's instantiated row count, which no presence predicate expresses. `GroupCountOperandReading` owns the forms and their contributions add **once per authored position**, so the same group named twice contributes twice. A fixed operand carries both measured content constituents — its descendant cells and whether a repeatable descendant has an instantiated row — because row instantiation is not expressible as a cell read at any width. The starred constructor takes the in-capacity count; excluding an over-limit row stays with the caller.
- `boundary`: A third form, `instances`, reads a fixed group below a star once per in-capacity environment as a fixed operand, and a law states its contribution is exactly those fixed readings' ([checkpoint](../sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation)).
- `boundary`: The fold merges nothing on containment either, but that branch is unreachable through elaboration: both arms refuse a containment pair statically, so the fold's total-function behavior there carries no kernel claim ([static-gate checkpoint](../sources/group-list-and-capacity-probes.md#src-group-count-static-gates-both-arms)).
- `owner`: [`GroupPresence.lean`](../../A12Kernel/Semantics/GroupPresence.lean), [`CheckedGroupPresence.lean`](../../A12Kernel/Elaboration/CheckedGroupPresence.lean)
- `case`: [group-presence separators](../../A12Kernel/Conformance/GroupPresence.lean) fix the product state from supplied constituents; [repeatable-descendant cases](../../A12Kernel/Conformance/GroupPresenceRepeatableDescendant.lean) derive them from a model instead, on the one shape that isolates the row constituent — a group owning no field anywhere, whose only content is a repeatable descendant.
- `case`: [starred group-count cases](../../A12Kernel/Conformance/StarredGroupCountComputation.lean) replay the seven measured documents at both targets, with three instantiated empty rows counting three as the discriminator and the emptied fixed operand as the mixed separator. They also replay the peer-measured two-star rows, where the same group named twice counting six is what separates a per-position sum from a per-group one. The [static-gate cases](../../A12Kernel/Conformance/NumericComputation/StarredGroupCount.lean) add the containment and root refusals with their admitted controls; the ancestor/descendant counting cases that stood there were deleted, because the Kernel refuses that pair at authoring time and the answer they locked was this project's own invention.
- `assurance`: E/P closed for resolved product; source-grounded. The disjunction is now **externally measured** rather than only source-grounded: the row constituent alone at the [repeatable-descendant checkpoint](../sources/group-and-iteration-probes.md#src-repeatable-descendant-group-count), and both constituents separated against one operand in the peer fixture that checkpoint reviews, with a neither-constituent control ruling out an unconditional count. The measurement is on the count carrier; this arm is shown to agree rather than measured itself.
- `assurance`: **Repetition depth is measured too** at the [deep checkpoint](../sources/group-and-iteration-probes.md#src-deep-repeatable-descendant-group-count): a descendant two repetition levels below the operand counts as one level does, so the constituent follows subtree containment rather than an axis count and the compute arm's depth gate is lifted. The half-instantiated shape — an outer row with no inner row — stays this project's own reading.
- `assurance`: E/P closed for the mixed fold, externally calibrated at the [starred group-count checkpoint](../sources/group-and-iteration-probes.md#src-starred-group-count-computation) on both codegen strategies. `numberOfFilledGroupsForComputationOperands_fixed` constrains the new fold by the established plain multi-group count in that direction only; `_append` states the decomposition a consumer needs. The addressed evaluator now consumes this fold, while the scalar route keeps refusing fail-closed; [`numeric.md`](numeric.md#cap-scalar-number-computation) owns that elaboration coverage.
- `remains`: Complete group lists/counts: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)

<a id="cap-model-declaration-legality"></a>
#### Model declaration legality

- `boundary`: Two declaration-admission gates that run before any condition is read. A root group may not be named `Id`, matched case-insensitively over the whole name and on the root carrier alone; a nested group or field of that name is ordinary. A repeatable group's declared maximum is bounded by its declaring carrier rather than by one global constant, the root bound sitting an order of magnitude below the nested one; the [inbound checkpoint](../sources/inbound-group-operand-batches.md#src-group-declaration-admission-peer-measurement) owns the exact pair.
- `boundary`: The reader tier below those verdicts is deliberately outside this representation. A count past a signed 32-bit integer is not read by the Kernel at all and draws no class; `Nat` cannot express that boundary and no clause here claims it.
- `owner`: [`Flat/Model.lean`](../../A12Kernel/Elaboration/Flat/Model.lean) (`FlatModel.validate`, `repeatabilityCap`), [`Flat/Types.lean`](../../A12Kernel/Elaboration/Flat/Types.lean) (`reservedRootGroupName`, `repeatabilityAboveCap`)
- `case`: [declaration-admission locks](../../A12Kernel/Conformance/ModelDeclarationLegality.lean). The four reserved spellings sit against `Identity`, `BinId`, and `Idx`, so a prefix or substring reading fails; the nested-group and field rows separate the root carrier from a model-wide ban. Both caps are walked at their exact boundary pair, and the row that is legal nested while illegal at the root is what a single-bound account cannot produce.
- `assurance`: E closed for both gates. No law is stated: each is a decidable predicate whose content is the two measured constants and one carrier test, and a theorem restating that adds nothing a case does not already fix.
- `evidence`: `L` by peer measurement, consumed rather than re-measured — the [inbound declaration-admission checkpoint](../sources/inbound-group-operand-batches.md#src-group-declaration-admission-peer-measurement) owns the revision, the two locking tests, and the exact rows. This project ran no kernel probe of its own for either gate, and the reader tier below A12's verdicts is outside this representation.
- `remains`: the remaining declaration-level laws SG28 lists — the String `hintList`, a group's sort list and its two ordering members, the thirteen-name `fieldType` vocabulary and which five tolerate a missing body: [SG28](../gaps/targets-and-derivation.md#gap-sg28).
