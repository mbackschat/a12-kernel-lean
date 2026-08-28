# Repetition and path capabilities

### §9 — repetition and iteration

<a id="reopened-star-structural-completeness-and-addressing"></a>

<a id="cap-named-environments-and-addresses"></a>
#### Named environments and addresses

- `boundary`: One-group/nested environments, physical-row enumeration, recursive validation-only implicit child row 1 below existing parents, ancestor projection, checked `CellAddr`, a validation addressed view that reads an implicit leaf as absent without materializing topology, and a one-field starred projection whose caller-supplied exact leaf read cannot replace the immutable topology, environment, address, or physical stored text
- `owner`: [`Iteration.lean`](../../A12Kernel/Semantics/Iteration.lean), [`StarAddressing.lean`](../../A12Kernel/Semantics/StarAddressing.lean), [`CheckedDocument.lean`](../../A12Kernel/Elaboration/CheckedDocument.lean), [`CheckedStarDocument.lean`](../../A12Kernel/Elaboration/CheckedStarDocument.lean)
- `assurance`: E/P closed for admitted scopes; the immutable starred-field projection is proved to specialize the caller-view form to the checked document's base read, and executable cases separate a reached caller-view poison from unchanged sibling topology and other parent-local scans; implicit validation row membership and pointers kernel-locked at a12-dmkits [source registry](../SOURCES.md); relative concrete/implicit emission order is a deterministic Lean account with external order unverified; selected C/X/Q
- `remains`: Wider path grammar: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-star-selection-and-correlation"></a>
#### Star selection and correlation

- `boundary`: Reopened-star extent, direct/plain/filtered selection, captured outer correlation, and one-star checked lowering
- `owner`: [`StarCompleteness.lean`](../../A12Kernel/Semantics/StarCompleteness.lean), [`Correlation.lean`](../../A12Kernel/Semantics/Correlation.lean), [`Correlation.lean`](../../A12Kernel/Elaboration/Correlation.lean)
- `assurance`: E/P closed for bounded shapes; selected C/X/Q, the only Q carrying an external cold implementation result ([fresh Rust runtime probe](../IMPLEMENTER-KIT-CORRELATION.md#fresh-rust-runtime-consumer-probe)); upstream L partial
- `remains`: Multi-level/wider correlation: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-field-values-not-unique"></a>
#### Field-values-not-unique

- `boundary`: Number, String/stored-Enumeration, and temporal overloads of `FieldValuesNotUnique` over the shared checked entity-list shape. `FieldEntityList` owns the four comparability categories and whole-list kind/category scans: Number selects the Number category, the token overload selects one String or Enumeration category, and temporal selects its format-keyed category. Two Strings or two stored Enumerations are admitted while any mix of those categories is refused in either order.
- `boundary`: The temporal overload's gate is one identical declared **format** string across every operand, keyed on the format rather than the kind, so a DATE `yyyy` beside a DATE_FRAGMENT `yyyy` is admitted across two kinds while two DATE fields differing only in format are refused; kind and category failures retain the offending path and actual kind, while temporal declarations without a coherent format and temporal format mismatches remain distinct; every refusal projects to its **Kernel diagnostic class** or honestly to `none`. The kind gate is applied over the whole operand list before any category decision, because gate order is observable and a fail-fast walk in authored order reports the mixing class where the Kernel reports the kind class.
- `boundary`: Its compared identity is the operand's **exact stored text**, which reuses the canonical token atom exactly rather than rendering a decoded value, and is deliberately a different reading from the decoded date `NumberOfDifferentValues` uses over the same entity lists. Common to all three: one **ordered fused scan** decides truth and polarity together, because the engine answers at the first duplicate it finds; membership stays on the shared comparable primitives with the scale-19 boundary for Number and exact identity for tokens; and empty *and formally unavailable* cells are skipped alike, so an unavailable cell neither suppresses nor compares. The operator's own result therefore carries no UNKNOWN at all.
- `boundary`: Every consumer therefore collects its operands through the non-suppressing `collectTaggedValueListCells`, never the aggregate families' availability-gated operand scan; the skip is locked at that checked-document boundary rather than only at the pure verdict, and one mechanism law specialized per overload proves that no such route can answer UNKNOWN. All three overloads return a polarity-bearing verdict whose filter escalation is **positional**: the scan walks operands in authored order, marks a filter only when it collects a present value from a filtered operand, and answers at the duplicate, so a filter authored after the duplicate never retypes it and one contributing only empties never marks anything.
- `boundary`: A firing the scan reached through a filter is omission-typed because the filter selects which values are compared; every other firing stays value-typed, and no missing potential in the selected cells escalates it
- `owner`: [`NumberValuesNotUnique.lean`](../../A12Kernel/Elaboration/NumberValuesNotUnique.lean), [`TokenValuesNotUnique.lean`](../../A12Kernel/Elaboration/TokenValuesNotUnique.lean), [`TemporalValuesNotUnique.lean`](../../A12Kernel/Elaboration/TemporalValuesNotUnique.lean), [`NumericAggregate.lean`](../../A12Kernel/Semantics/NumericAggregate.lean), [`ValueList.lean`](../../A12Kernel/Semantics/ValueList.lean), [comparison proofs](../../A12Kernel/Proofs/NumericAggregate.lean), [boundary proofs](../../A12Kernel/Proofs/ValuesNotUnique.lean), [cases](../../A12Kernel/Conformance/NumberValuesNotUnique.lean), [token cases](../../A12Kernel/Conformance/TokenValuesNotUnique.lean), [temporal cases](../../A12Kernel/Conformance/TemporalValuesNotUnique.lean)
- `assurance`: E/P closed for the Number, String/stored-Enumeration, and temporal overloads, clean dmtool `0.12.1` at a12-dmkits [source registry](../SOURCES.md) Kernel-confirms exact arity, category, BOOLEAN/CONFIRM kind, and two-order pre-emption diagnostics for Number and token lists, with accepted representatives persisted and read back, real-kernel authoring admits the two- and three-field list over differing scales, the starred single-field form, a mixed direct-plus-starred list, and the filtered starred form, and rejects a single operand plus a mixed-kind list, `DM_INTERPRETER` separates typed cross-scale firing and empty skipping at [source registry](../SOURCES.md), and one-message unfiltered VALUE versus filtered OMISSION at [source registry](../SOURCES.md)
- `assurance`: that route's apparent formal *suppression* was disproved at [source registry](../SOURCES.md), where the kernel skips an unavailable cell instead
- `assurance`: Kernel-locked for cardinality, first-row anchoring, placement invariance, and single-operand filter polarity by `FieldValuesNotUniqueDiffTest` at a12-dmkits [source registry](../SOURCES.md), both the **positional** polarity rule and the unavailable-cell skip are Kernel-locked at [source registry](../SOURCES.md) across dynamic Groovy, generated Java, and the interpreter under accepted [`SPEC-2026-08-05-01`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-05-01--fieldvaluesnotunique-filter-escalation-is-positional-not-static), including the filtered operand that contributes only unconvertible cells and the two-equal-unconvertible pair
- `assurance`: the temporal overload's format-keyed admission gate is Kernel-locked by the same revision's 25-case admission tier, including the cross-kind same-format row and the differing-format refusal, though the local matrix asserts that gate rather than replaying retained observations, its stored-text identity is kernel-source grounded with one unmeasured residual under pending [`SPEC-2026-08-05-03`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-05-03--the-temporal-fieldvaluesnotunique-identity-is-stored-text-and-its-agreement-with-decoded-values-is-an-assumption-rather-than-a-measured-equivalence), C none
- `remains`: The Custom category, the stored-text residual, and the format-versus-kind-family annotation: [SG7](../SEMANTICS-GAPS.md#sg7--string-pattern-and-custom-field-completion). The message reference and first-row anchoring channels this clause now specifies remain unmodeled: [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration). Group-scope admission, family retention, full-validation extent, reference projection, source assurance, and live remainders are owned by [shared admission](../IMPLEMENTATION-MAP.md#cap-shared-entity-list-group-admission), [Number](../IMPLEMENTATION-MAP.md#cap-number-group-aggregates), [token](../IMPLEMENTATION-MAP.md#cap-token-group-expansion), [temporal](../IMPLEMENTATION-MAP.md#cap-temporal-group-uniqueness), and [reference projection](../IMPLEMENTATION-MAP.md#cap-group-operand-reference-projection).
- `remains`: Group-form message emission remains under [SG10](../SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).

<a id="cap-repetition-not-unique"></a>
#### Repetition-not-unique

- `boundary`: Branch-independent clusters, mixed admitted key kinds, validation-domain implicit descendants, deepest-key-parent row selection independent of authored component order, and the admitted `@From` reference boundary
- `owner`: [`RepetitionNotUnique.lean`](../../A12Kernel/Semantics/RepetitionNotUnique.lean), [`RepetitionNotUnique.lean`](../../A12Kernel/Elaboration/RepetitionNotUnique.lean)
- `assurance`: E/P closed for admitted keys; upstream L locked for guarded composition, implicit optional-empty duplicates, mixed-depth key order, and admitted `@From`; C none
- `remains`: Remaining key/path forms: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-semantic-index"></a>
#### Semantic index

- `boundary`: Checked normalized key column with ordered occurrences, duplicate/unavailable state, shared duplicate exclusion for semantic and parallel selection, and one ordinary read route. The checked source carries the declared index **declaration** rather than a Number field, so any index kind is admitted and one dispatch chooses between the numeric-value and exact-text identities; a literal key's identity domain must be that index's own. The reduced raw-context route keeps a Number index and Number target as its own stated refinement, because it rebuilds the column from a one-group scan instead of projecting the shared one.
- `boundary`: A **DateRange** selected target is closed on the endpoint-component carrier through [`SemanticIndexDateRange.lean`](../../A12Kernel/Elaboration/SemanticIndexDateRange.lean), which refines the same certificate and projects the keyed read through the direct route's own payload rule. A field-valued key read from **inside the indexed group itself** carries its own measured placement class, `MVK_SEMANTIC_INDEX_CONTAINED_IN_INDEX`, rather than the generic repeatable-reference refusal, and a repeatable key outside that group still reaches the ordinary nonrepeatable boundary. The Kernel's declaration-format check on an authored literal, `MVK_INDEX_VALUE_INVALID`, is an explicit exclusion: this project performs no lexing, so a literal reaches the surface already decoded.
- `boundary`: A duplicated side is unmatched when a clean far side supplies the join key and contributes no key when both sides duplicate it
- `owner`: [`SemanticIndex.lean`](../../A12Kernel/Semantics/SemanticIndex.lean), [`SemanticIndex.lean`](../../A12Kernel/Elaboration/SemanticIndex.lean), [`CheckedIndexColumn.lean`](../../A12Kernel/Elaboration/CheckedIndexColumn.lean)
- `assurance`: E/P closed for the named selection boundary, with the general delegation law and its Number specialization proved so the two routes cannot describe two policies; upstream L locked for ordinary match/column timing and full parallel duplicate exclusion, and index-kind independence plus the four-state read are locally Kernel-locked at the [kind-independence](../SOURCES.md#src-semantic-index-kind-independence) and [endpoint-shape](../SOURCES.md#src-date-range-endpoint-shapes) checkpoints; C none
- `remains`: Remaining non-Number selected targets, the literal format check, and wider keys: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-repeatable-validation"></a>
#### Repeatable validation

- `boundary`: Ordinary full/partial rule loops over concrete outer rows plus recursive implicit nested child row 1; partial rule admission projects error-path relevance onto the levels bound by the checked reference-derived iteration plan and ignores deeper coordinates, while admitted ordinary field and Number-aggregate reads consume the call-local generated-preliminary view, including requiredness, relevance-scoped duplicate-index findings, and cause-free default suppression; parallel presence retains concrete indexed topology
- `owner`: [`ValidationRule.lean`](../../A12Kernel/Elaboration/ValidationRule.lean), [`ValidationCondition/Iteration.lean`](../../A12Kernel/Elaboration/ValidationCondition/Iteration.lean), [`ParallelPresenceRule.lean`](../../A12Kernel/Elaboration/ParallelPresenceRule.lean), [partial-preliminary projection law](../../A12Kernel/Proofs/CheckedIndexPreliminary.lean)
- `assurance`: E/P closed for admitted loops, ordinary field leaves, and unfiltered Number aggregates, including three-level projection, empty-as-zero full/partial execution, no-outer control, nonmaterialization, row-exact admission, relevance-scoped duplicate suppression, requiredness, and a zero-bound once plan admitted by another concrete error row; upstream L locked at a12-dmkits [source registry](../SOURCES.md) for the row-domain and iteration-bound gate splits and [source registry](../SOURCES.md) for duplicate-partner relevance; selected C/X
- `remains`: Wider leaves/parallel shapes: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-repeatable-number-computation"></a>
#### Repeatable Number computation

- `boundary`: Checked route tables, invalid-index suppression, target-specific clearing, exact-address overlay, and finite supplied-order execution
- `owner`: [`ParallelNumericAlternativeTable.lean`](../../A12Kernel/Elaboration/ParallelNumericAlternativeTable.lean), [`ParallelNumericRun.lean`](../../A12Kernel/Elaboration/ParallelNumericRun.lean)
- `assurance`: E/P closed for finite Number plan, including universal operation/table target exclusion, table/whole-fold target-field ownership, and exact successful-output address uniqueness; upstream L partial; C none
- `remains`: Cross-family/repeatable breadth: [SG4](../SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition)

<a id="cap-group-list-count-terminals"></a>
#### Group-list/count terminals

- `boundary`: Terminal repeatable groups count structural rows; nonrepeatable terminals below stars evaluate once per selected ancestor environment
- `owner`: [`StarGroup.lean`](../../A12Kernel/Elaboration/StarGroup.lean), [`ValidationCondition/`](../../A12Kernel/Elaboration/ValidationCondition/)
- `assurance`: E/P closed for bounded terminals, including repeated-star occurrence preservation, zero-row polarity, bound-prefix admission, and nonrepeatable-terminal composition; upstream L at [source registry](../SOURCES.md), [source registry](../SOURCES.md), and [source registry](../SOURCES.md); C none
- `remains`: Complete group-list/count surface: [SG13](../SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion)


### §10 — paths and references

<a id="cap-flat-resolution"></a>
#### Flat resolution

- `boundary`: Absolute, parent-relative, and bare flat names plus quote-aware structured names
- `owner`: [`Flat/`](../../A12Kernel/Elaboration/Flat/)
- `assurance`: E/P closed for admitted grammar; selected C/X
- `remains`: Full concrete grammar/renderer: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-star-correlation-paths"></a>
#### Star/correlation paths

- `boundary`: Bounded group-qualified star and correlation paths lower to named scopes/environments
- `owner`: [`StarPath.lean`](../../A12Kernel/Elaboration/StarPath.lean), [`StarAddressing.lean`](../../A12Kernel/Semantics/StarAddressing.lean)
- `assurance`: E/P closed for admitted shapes; selected C/X/Q
- `remains`: Wider nesting/legality: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-rulegroup-and-index-routes"></a>
#### `RuleGroup` and index routes

- `boundary`: Declaring-group resolution, checked semantic-index construction, and duplicate-excluding index-group routes consumed by bounded full parallel validation/computation
- `owner`: [`ValidationContext.lean`](../../A12Kernel/Elaboration/ValidationContext.lean), [`SemanticIndex.lean`](../../A12Kernel/Elaboration/SemanticIndex.lean), [`CheckedIndexColumn.lean`](../../A12Kernel/Elaboration/CheckedIndexColumn.lean)
- `assurance`: E/P closed for named routes; upstream L partial; selected C
- `remains`: Partial parallel relevance and wider static diagnostics: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-guarded-nonrepeatable-root-currentrepetition"></a>
#### Guarded nonrepeatable-root `CurrentRepetition`

- `boundary`: One indivisible validation leaf retains a direct same-root filled-field guard, an ordinary nonrepeatable root, and the closed `== 1` / `!= 1` tag. It reuses the shared filled-presence, numeric-verdict, connective, and reference owners; only the guard contributes a field pointer, and partial validation is structurally unsupported
- `owner`: [`CurrentRepetition.lean`](../../A12Kernel/Elaboration/CurrentRepetition.lean), [`Core.lean`](../../A12Kernel/Elaboration/ValidationCondition/Core.lean), [`Assembly.lean`](../../A12Kernel/Elaboration/ValidationCondition/Assembly.lean), [proofs](../../A12Kernel/Proofs/ValidationCondition/CurrentRepetition.lean), [cases](../../A12Kernel/Conformance/ValidationCondition/CurrentRepetition.lean)
- `assurance`: E/P closed for the exact shape; dynamic Groovy, generated Java, and interpreter L at a12-dmkits [source registry](../SOURCES.md); C/X/Q none
- `remains`: Captured row lookup, fixed nested groups, wider root comparisons, computation, filters, partial validation, arithmetic wrappers, and parsing: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)

<a id="cap-guarded-same-group-repeatable-currentrepetition"></a>
#### Guarded same-group repeatable `CurrentRepetition`

- `boundary`: One indivisible validation leaf retains a direct filled guard, the shared model-owned repeatable coordinate source, and closed `> 1`, `> 2`, or `>= 1` tags. Ordinary iteration supplies the complete selected environment; missing, duplicate, or zero named bindings remain structural errors; the shared numeric owner compares the 1-based coordinate; every firing is VALUE and carries the guard's concrete row pointer. The guard alone supplies iteration scope, legality, field dependency, and reference projection; partial validation is structurally unsupported
- `owner`: [`CurrentRepetition.lean`](../../A12Kernel/Elaboration/CurrentRepetition.lean), [`Core.lean`](../../A12Kernel/Elaboration/ValidationCondition/Core.lean), [`Assembly.lean`](../../A12Kernel/Elaboration/ValidationCondition/Assembly.lean), [proofs](../../A12Kernel/Proofs/ValidationCondition/CurrentRepetition.lean), [cases](../../A12Kernel/Conformance/ValidationCondition/CurrentRepetition.lean)
- `assurance`: E/P closed for the checked same-group shape exact one-level `> 1` row/value/pointer L at a12-dmkits [source registry](../SOURCES.md) `> 2` and `>= 1` have cross-engine agreement but exact cross-threshold coordinates remain external evidence pending admission L at [source registry](../SOURCES.md) deeper model-owned levels remain external evidence pending C/X/Q none
- `remains`: Captured `$`, fixed nonrepeatable descendants, other validation comparisons, computation beyond the bounded complete-scope `> 0` fixed chains, filters outside the established `Having` owner, partial validation, arithmetic wrappers, and parsing: [SG9](../SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion)
