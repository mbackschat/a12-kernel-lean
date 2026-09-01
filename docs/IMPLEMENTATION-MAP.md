# Lean implementation and evidence map

This hub and its bounded [`implementation/`](implementation/) records are the sole live map from the project-owned [`spec/`](../spec/) taxonomy to Lean owners, implemented boundaries, proof/counterexample status, and external assurance. Open obligations are linked from [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) rather than copied here; exact retained observations are owned by [`EVIDENCE.md`](EVIDENCE.md); source provenance is owned by [`SOURCES.md`](SOURCES.md).

The target is kernel **30.8.1**.

## Query contract

Start from the matching stable entry with `rg -n '^<a id="cap-' docs/IMPLEMENTATION-MAP.md`, then follow its link to the bounded family record under [`implementation/`](implementation/). Search the shard directly when updating a record.

Each record answers four questions directly: what exists, where its primary owner lives, how certain the stated slice is, and what remains. A current answer must not require Git archaeology; Git owns chronology, not live state. This map does not narrate capsule history, source-audit chronology, gate counts, or immediate next work.

Coverage uses six independent dimensions:

- **E — executable:** checked definitions and separating executable cases exist.
- **P — proof-closed:** the named boundary has its required proof spine and nearest useful non-law.
- **L — Kernel-locked:** a maintained a12-dmkits test executes the real kernel for the named behavior. `—` means not yet assessed, not “no lock exists.”
- **C — Kernel-calibrated:** retained versioned kernel observations replay through a typed local projection.
- **X — publicly exposed:** the normalized reference process exposes the named behavior.
- **Q — consumer-qualified:** a bounded consumer probe exercised the representation for its named decision. The letter itself never carries the probe class: read the row or record prose for it, and treat the probe as in-context or artifact-only unless that prose names an external cold implementation. `Q` is never cold-consumer qualification, shipment research closure, or release support; [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#consumer-probes-before-shipment) owns those later stages.

`closed` applies only to the boundary stated in that row. `partial` means at least one named slice is implemented while the canonical clause remains open. `none` means no current capability in that dimension.

## Coverage summary

<a id="coverage-dimensions"></a>
| Boundary | E | P | L | C | X | Q |
|---|---|---|---|---|---|---|
| Immutable checked document | closed | closed | — | none | none | closed |
| §1 truth and verdict algebra | closed | closed | — | none | none | none |
| §2 empty scalar comparisons and row gate | partial | partial | partial | partial | partial | none |
| §3 formal checking and phase observation | partial | partial | partial | partial | partial | none |
| §4 required property | partial | partial | partial | partial | none | none |
| §5 numbers and decimals | partial | partial | partial | partial | partial | partial |
| §6 dates and time | partial | partial | partial | none | none | partial |
| §7 strings and patterns | partial | partial | partial | partial | none | partial |
| §8 enumerations and value lists | partial | partial | partial | none | none | partial |
| §9 repetition and iteration | partial | partial | partial | partial | partial | partial |
| §10 paths and references | partial | partial | partial | partial | partial | partial |
| §11 calculations and formal checking | partial | partial | partial | partial | none | partial |
| §12 validation and polarity | partial | partial | partial | partial | partial | partial |
| §13 message interpolation | partial | partial | partial | partial | none | partial |
| §14 custom conditions | partial | partial | — | none | none | partial |

The six columns must not be collapsed into one completion percentage. Internal proof does not establish kernel correspondence; an upstream kernel-executing lock is not locally replayable calibration; finite calibration does not prove the whole clause; public exposure and consumer qualification are separate product decisions.

### Coverage denominator

<a id="the-capability-denominator--mined-from-the-kernel-not-from-spec"></a>
<a id="the-capability-denominator-mined-from-the-kernel-not-from-spec"></a>

The eventual-completeness denominator is mined from the Kernel rather than inferred from the current spec. Runtime observables follow a12-dmkits’ guard-checked [`RT-SEMANTICS-LEDGER`](../../a12-rulekit/docs/RT-SEMANTICS-LEDGER.md). Required static legality follows the Kernel’s `MVK_`-prefixed diagnostic constants: the complete 30.8.1 inventory contains 280 constants across eight enums, while the semantic center’s current in-scope static-legality denominator is approximately 57 after excluding bilingual parser, H-model, and on-the-fly rule-testing scopes. The 57 still includes the code-generation `NoMetaModelCheckErrorType` region that the peer’s model-authoring ledger does not classify. These figures bound inventory work; they are not a completion percentage and must be re-mined on a Kernel-version change.

### Kernel assurance drill

<a id="upstream-kernel-locked-inventory-composition-triage-2026-07-25"></a>

Capability records state the current `L` boundary. The reusable lock and deliberate-non-lock receipts are maintained in the [Kernel lock source index](SOURCES.md#src-kernel-lock-index); exact retained observations remain in [`EVIDENCE.md`](EVIDENCE.md).

<a id="evidence-snapshot"></a>

## Capability index

<a id="owners"></a>
<a id="implemented"></a>
<a id="coverage"></a>
<a id="evidence"></a>
<a id="excludednext"></a>
<a id="excluded-boundary-and-gap-links"></a>

This is the operational lookup layer. Search the exact capability or type, then read its keyed record:

- `boundary` states the implemented semantic boundary, not a historical milestone.
- `owner` is the narrowest primary module or directory; matching proof and conformance owners use the same basename unless named separately.
- `assurance` reports internal executable/proof status first, then external status using `L`, `C`, `X`, and `Q`. “Source-grounded” and “peer-triangulated” are intentionally not `L` or `C`.
- `remains` links the live open owner or states that the named slice is closed. It never repeats that gap’s checklist.

For an assurance drill, use the row’s linked owner, then the matching [`Proofs/`](../A12Kernel/Proofs/) and [`Conformance/`](../A12Kernel/Conformance/) family; irregular proof owners are linked in the row. [`Proofs.lean`](../A12Kernel/Proofs.lean) is the theorem inventory, [`Conformance.lean`](../A12Kernel/Conformance.lean) is the executable separator inventory, and [`TrustAudit.lean`](../A12Kernel/TrustAudit.lean) is the exhaustive trusted-theorem registry. Exact retained Kernel observations remain in [`EVIDENCE.md`](EVIDENCE.md), while upstream Kernel locks and source-grounded claims route through [`SOURCES.md`](SOURCES.md).

### Detailed capability shards

Each stable anchor remains here as a compatibility entry point. Follow its link to read or update the bounded detailed record.

#### Checked data and clauses 1 to 4

<a id="immutable-checked-document-construction"></a>
- [Immutable checked-document construction](implementation/data-and-core.md#immutable-checked-document-construction)
<a id="cap-physical-document-topology"></a>
- [Physical document topology](implementation/data-and-core.md#cap-physical-document-topology)
<a id="cap-checked-addressed-reads"></a>
- [Checked addressed reads](implementation/data-and-core.md#cap-checked-addressed-reads)
<a id="cap-preliminary-index-findings"></a>
- [Preliminary index findings](implementation/data-and-core.md#cap-preliminary-index-findings)
<a id="cap-required-group-projections"></a>
- [Required/group projections](implementation/data-and-core.md#cap-required-group-projections)
<a id="cap-three-valued-truth"></a>
- [Three-valued truth](implementation/data-and-core.md#cap-three-valued-truth)
<a id="cap-validation-verdict"></a>
- [Validation verdict](implementation/data-and-core.md#cap-validation-verdict)
<a id="cap-shared-condition-tree-control-flow"></a>
- [Shared condition-tree control flow](implementation/data-and-core.md#cap-shared-condition-tree-control-flow)
<a id="cap-boolean-confirm-string-scalar-equality"></a>
- [Boolean/Confirm/String scalar equality](implementation/data-and-core.md#cap-boolean-confirm-string-scalar-equality)
<a id="cap-number-comparison-and-empty-polarity"></a>
- [Number comparison and empty polarity](implementation/data-and-core.md#cap-number-comparison-and-empty-polarity)
<a id="cap-string-length-comparison"></a>
- [String length comparison](implementation/data-and-core.md#cap-string-length-comparison)
<a id="cap-temporal-comparison"></a>
- [Temporal comparison](implementation/data-and-core.md#cap-temporal-comparison)
<a id="cap-presence-and-row-content"></a>
- [Presence and row content](implementation/data-and-core.md#cap-presence-and-row-content)
<a id="cap-phase-projection"></a>
- [Phase projection](implementation/data-and-core.md#cap-phase-projection)
<a id="cap-raw-string-ingestion"></a>
- [Raw String ingestion](implementation/data-and-core.md#cap-raw-string-ingestion)
<a id="cap-group-list-diagnostics"></a>
- [Group-list diagnostics](implementation/data-and-core.md#cap-group-list-diagnostics)
<a id="cap-rnu-key-diagnostics"></a>
- [RNU key diagnostics](implementation/data-and-core.md#cap-rnu-key-diagnostics)
<a id="cap-formal-output-boundary"></a>
- [Formal output boundary](implementation/data-and-core.md#cap-formal-output-boundary)
<a id="cap-requiredness-scope"></a>
- [Requiredness scope](implementation/data-and-core.md#cap-requiredness-scope)
<a id="cap-generated-required-staging"></a>
- [Generated required staging](implementation/data-and-core.md#cap-generated-required-staging)
<a id="cap-group-content-gate"></a>
- [Group-content gate](implementation/data-and-core.md#cap-group-content-gate)

#### Numeric and temporal capabilities

<a id="5--numbers-and-decimals"></a>
- [§5 numbers and decimals](implementation/numeric-and-temporal.md#5--numbers-and-decimals)
<a id="6--dates-and-time"></a>
- [§6 dates and time](implementation/numeric-and-temporal.md#6--dates-and-time)
<a id="cap-arithmetic-and-scale-analysis"></a>
- [Arithmetic and scale analysis](implementation/numeric-and-temporal.md#cap-arithmetic-and-scale-analysis)
<a id="cap-fillability-and-comparison"></a>
- [Fillability and comparison](implementation/numeric-and-temporal.md#cap-fillability-and-comparison)
<a id="cap-numeric-wrappers-and-extrema"></a>
- [Numeric wrappers and extrema](implementation/numeric-and-temporal.md#cap-numeric-wrappers-and-extrema)
<a id="cap-number-source-conversions"></a>
- [Number source conversions](implementation/numeric-and-temporal.md#cap-number-source-conversions)
<a id="cap-number-aggregates"></a>
- [Number aggregates](implementation/numeric-and-temporal.md#cap-number-aggregates)
<a id="cap-stored-number-formal-read"></a>
- [Stored Number formal read](implementation/numeric-and-temporal.md#cap-stored-number-formal-read)
<a id="cap-stored-decimal-identity"></a>
- [Stored decimal identity](implementation/numeric-and-temporal.md#cap-stored-decimal-identity)
<a id="cap-number-target-and-delta"></a>
- [Number target and delta](implementation/numeric-and-temporal.md#cap-number-target-and-delta)
<a id="cap-scalar-number-computation"></a>
- [Scalar Number computation](implementation/numeric-and-temporal.md#cap-scalar-number-computation)
<a id="cap-addressed-numeric-operation-consumer"></a>
- [Addressed numeric-operation consumer](implementation/numeric-and-temporal.md#cap-addressed-numeric-operation-consumer)
<a id="resolved-date-range-overlap-truth-and-operator-scans"></a>
- [Date construction and Base Year](implementation/numeric-and-temporal.md#resolved-date-range-overlap-truth-and-operator-scans)
<a id="resolved-direct-date-construction-and-base-year-date-sources"></a>
- [Date construction and Base Year](implementation/numeric-and-temporal.md#resolved-direct-date-construction-and-base-year-date-sources)
<a id="differenceindays-concrete-profile-closure"></a>
- [Date construction and Base Year](implementation/numeric-and-temporal.md#differenceindays-concrete-profile-closure)
<a id="cap-date-construction-and-base-year"></a>
- [Date construction and Base Year](implementation/numeric-and-temporal.md#cap-date-construction-and-base-year)
<a id="cap-model-zone-profile"></a>
- [Model-zone profile](implementation/numeric-and-temporal.md#cap-model-zone-profile)
<a id="cap-temporal-differences"></a>
- [Temporal differences](implementation/numeric-and-temporal.md#cap-temporal-differences)
<a id="cap-calendar-shifts"></a>
- [Calendar shifts](implementation/numeric-and-temporal.md#cap-calendar-shifts)
<a id="cap-component-authoring"></a>
- [Component authoring](implementation/numeric-and-temporal.md#cap-component-authoring)
<a id="cap-temporal-target-computation-application"></a>
- [Temporal target/computation/application](implementation/numeric-and-temporal.md#cap-temporal-target-computation-application)
<a id="cap-full-date-stored-classifier"></a>
- [Bounded full-Date stored classifier](implementation/numeric-and-temporal.md#cap-full-date-stored-classifier)
<a id="cap-datetime-stored-input"></a>
- [Bounded DateTime stored classifier](implementation/numeric-and-temporal.md#cap-datetime-stored-input)
<a id="cap-omitting-date-input"></a>
- [Component-omitting Date stored classifier](implementation/numeric-and-temporal.md#cap-omitting-date-input)
<a id="cap-filled-field-count"></a>
- [`NumberOfFilledFields` validation count](implementation/numeric-and-temporal.md#cap-filled-field-count)
<a id="cap-date-from-datetime"></a>
- [`DateFromDateTime` extractor](implementation/numeric-and-temporal.md#cap-date-from-datetime)
<a id="cap-value-as-date-locus"></a>
- [`ValueAsDate` reading locus](implementation/numeric-and-temporal.md#cap-value-as-date-locus)
<a id="cap-document-temporal-coherence"></a>
- [Placed-temporal-cell coherence property](implementation/numeric-and-temporal.md#cap-document-temporal-coherence)
<a id="cap-time-stored-input"></a>
- [Bounded Time stored classifier](implementation/numeric-and-temporal.md#cap-time-stored-input)
<a id="cap-partial-date-stored-input"></a>
- [Bounded partially known Date stored classifier](implementation/numeric-and-temporal.md#cap-partial-date-stored-input)
<a id="cap-temporal-value-identity"></a>
- [Universal temporal value identity](implementation/numeric-and-temporal.md#cap-temporal-value-identity)
<a id="cap-date-range-checked-declaration"></a>
- [Checked DateRange declaration and admission](implementation/numeric-and-temporal.md#cap-date-range-checked-declaration)
<a id="cap-date-range-construction-computation"></a>
- [Direct DateRange construction computation](implementation/numeric-and-temporal.md#cap-date-range-construction-computation)
<a id="cap-indexed-date-range-construction-computation"></a>
- [String-keyed DateRange construction computation](implementation/numeric-and-temporal.md#cap-indexed-date-range-construction-computation)
<a id="cap-checked-date-range-bound"></a>
- [Checked direct DateRange bound extraction, fixed-Date comparison, and components](implementation/numeric-and-temporal.md#cap-checked-date-range-bound)
<a id="cap-stored-date-range-equality"></a>
- [Checked stored-versus-stored DateRange equality](implementation/numeric-and-temporal.md#cap-stored-date-range-equality)
<a id="cap-unconfigured-yearless-date-range-bound"></a>
- [Unconfigured yearless DateRange bound extraction and components](implementation/numeric-and-temporal.md#cap-unconfigured-yearless-date-range-bound)
<a id="cap-date-range-bound-pair-comparison"></a>
- [Checked DateRange endpoint-pair comparison](implementation/numeric-and-temporal.md#cap-date-range-bound-pair-comparison)
<a id="cap-date-range-bound-component-operand"></a>
- [The numeric Date component of a selected DateRange endpoint](implementation/numeric-and-temporal.md#cap-date-range-bound-component-operand)
<a id="cap-iterated-date-range-conditions"></a>
- [DateRange conditions read at the rule's iterating row](implementation/numeric-and-temporal.md#cap-iterated-date-range-conditions)
<a id="cap-date-range-repeatable-operand-locus"></a>
- [Repeatable-operand rule locus across the DateRange carriers](implementation/numeric-and-temporal.md#cap-date-range-repeatable-operand-locus)
<a id="cap-temporal-comparison-and-aggregates"></a>
- [Temporal comparison and aggregates](implementation/numeric-and-temporal.md#cap-temporal-comparison-and-aggregates)

#### String and enumeration capabilities

<a id="7--strings-and-patterns"></a>
- [§7 strings and patterns](implementation/strings-and-enumerations.md#7--strings-and-patterns)
<a id="8--enumerations-and-value-lists"></a>
- [§8 enumerations and value lists](implementation/strings-and-enumerations.md#8--enumerations-and-value-lists)
<a id="cap-string-value-and-length"></a>
- [String value and length](implementation/strings-and-enumerations.md#cap-string-value-and-length)
<a id="cap-pattern-and-charset-admission"></a>
- [Pattern and charset admission](implementation/strings-and-enumerations.md#cap-pattern-and-charset-admission)
<a id="cap-string-target-policy"></a>
- [String target policy](implementation/strings-and-enumerations.md#cap-string-target-policy)
<a id="cap-string-aggregates-value-lists"></a>
- [String aggregates/value lists](implementation/strings-and-enumerations.md#cap-string-aggregates-value-lists)
<a id="cap-string-computation-execution"></a>
- [String computation execution](implementation/strings-and-enumerations.md#cap-string-computation-execution)
<a id="resolved-firstfilledvalue"></a>
- [Resolved `FirstFilledValue`](implementation/strings-and-enumerations.md#resolved-firstfilledvalue)
<a id="cap-first-filled-value"></a>
- [Resolved `FirstFilledValue`](implementation/strings-and-enumerations.md#cap-first-filled-value)
<a id="cap-first-filled-value-assurance"></a>
- [Resolved `FirstFilledValue` — assurance and calibration](implementation/strings-and-enumerations.md#cap-first-filled-value-assurance)
<a id="cap-enumeration-identity-and-categories"></a>
- [Enumeration identity and categories](implementation/strings-and-enumerations.md#cap-enumeration-identity-and-categories)
<a id="cap-direct-comparability"></a>
- [Direct comparability](implementation/strings-and-enumerations.md#cap-direct-comparability)
<a id="cap-typed-value-lists"></a>
- [Typed value lists](implementation/strings-and-enumerations.md#cap-typed-value-lists)
<a id="cap-enumeration-rnu-and-computation"></a>
- [Enumeration RNU and computation](implementation/strings-and-enumerations.md#cap-enumeration-rnu-and-computation)
<a id="cap-enumeration-result-and-application"></a>
- [Enumeration result and application](implementation/strings-and-enumerations.md#cap-enumeration-result-and-application)
<a id="cap-exact-row-enumeration-dependency-cascade"></a>
- [Exact-row Enumeration dependency cascade](implementation/strings-and-enumerations.md#cap-exact-row-enumeration-dependency-cascade)
<a id="cap-two-producer-enumeration-firstfilledvalue-join"></a>
- [Two-producer Enumeration `FirstFilledValue` join](implementation/strings-and-enumerations.md#cap-two-producer-enumeration-firstfilledvalue-join)
<a id="cap-number-dependency-in-enumeration-having"></a>
- [Computed Number dependency inside Enumeration `Having`](implementation/strings-and-enumerations.md#cap-number-dependency-in-enumeration-having)
<a id="cap-computed-enumeration-number-having-join"></a>
- [Computed Enumeration value plus Number `Having` join](implementation/strings-and-enumerations.md#cap-computed-enumeration-number-having-join)

#### Repetition and path capabilities

<a id="9--repetition-and-iteration"></a>
- [§9 repetition and iteration](implementation/repetition-and-paths.md#9--repetition-and-iteration)
<a id="10--paths-and-references"></a>
- [§10 paths and references](implementation/repetition-and-paths.md#10--paths-and-references)
<a id="reopened-star-structural-completeness-and-addressing"></a>
- [Named environments and addresses](implementation/repetition-and-paths.md#reopened-star-structural-completeness-and-addressing)
<a id="cap-named-environments-and-addresses"></a>
- [Named environments and addresses](implementation/repetition-and-paths.md#cap-named-environments-and-addresses)
<a id="cap-star-selection-and-correlation"></a>
- [Star selection and correlation](implementation/repetition-and-paths.md#cap-star-selection-and-correlation)
<a id="cap-field-values-not-unique"></a>
- [Field-values-not-unique](implementation/repetition-and-paths.md#cap-field-values-not-unique)
<a id="cap-repetition-not-unique"></a>
- [Repetition-not-unique](implementation/repetition-and-paths.md#cap-repetition-not-unique)
<a id="cap-semantic-index"></a>
- [Semantic index](implementation/repetition-and-paths.md#cap-semantic-index)
<a id="cap-over-repetition-findings"></a>
- [Over-repetition finding set](implementation/repetition-and-paths.md#cap-over-repetition-findings)
<a id="cap-computation-over-repetition-channel"></a>
- [Computation over-repetition channel](implementation/repetition-and-paths.md#cap-computation-over-repetition-channel)
<a id="cap-repeatable-validation"></a>
- [Repeatable validation](implementation/repetition-and-paths.md#cap-repeatable-validation)
<a id="cap-repeatable-number-computation"></a>
- [Repeatable Number computation](implementation/repetition-and-paths.md#cap-repeatable-number-computation)
<a id="cap-group-list-count-terminals"></a>
- [Group-list/count terminals](implementation/repetition-and-paths.md#cap-group-list-count-terminals)
<a id="cap-flat-resolution"></a>
- [Flat resolution](implementation/repetition-and-paths.md#cap-flat-resolution)
<a id="cap-star-correlation-paths"></a>
- [Star/correlation paths](implementation/repetition-and-paths.md#cap-star-correlation-paths)
<a id="cap-rulegroup-and-index-routes"></a>
- [`RuleGroup` and index routes](implementation/repetition-and-paths.md#cap-rulegroup-and-index-routes)
<a id="cap-guarded-nonrepeatable-root-currentrepetition"></a>
- [Guarded nonrepeatable-root `CurrentRepetition`](implementation/repetition-and-paths.md#cap-guarded-nonrepeatable-root-currentrepetition)
<a id="cap-guarded-same-group-repeatable-currentrepetition"></a>
- [Guarded same-group repeatable `CurrentRepetition`](implementation/repetition-and-paths.md#cap-guarded-same-group-repeatable-currentrepetition)

#### Computation capabilities

<a id="11--calculations-and-formal-checking"></a>
- [§11 calculations and formal checking](implementation/computations.md#11--calculations-and-formal-checking)
<a id="11--computations"></a>
- [Computation conditions](implementation/computations.md#11--computations)
<a id="11-computations"></a>
- [Computation conditions](implementation/computations.md#11-computations)
<a id="cap-computation-conditions"></a>
- [Computation conditions](implementation/computations.md#cap-computation-conditions)
<a id="cap-boolean-confirm-constant-computation-target-admission"></a>
- [Boolean/Confirm constant computation target and result/application](implementation/computations.md#cap-boolean-confirm-constant-computation-target-admission)
<a id="cap-first-selected-tables"></a>
- [First-selected tables](implementation/computations.md#cap-first-selected-tables)
<a id="cap-scalar-execution-plans"></a>
- [Scalar execution plans](implementation/computations.md#cap-scalar-execution-plans)
<a id="cap-mixed-scalar-failure-transitions"></a>
- [Mixed scalar failure transitions](implementation/computations.md#cap-mixed-scalar-failure-transitions)
<a id="cap-repeatable-number-plan"></a>
- [Repeatable Number plan](implementation/computations.md#cap-repeatable-number-plan)
<a id="cap-finite-row-structural-guard-number-cascade"></a>
- [Finite-row structural-guard Number cascade](implementation/computations.md#cap-finite-row-structural-guard-number-cascade)
<a id="cap-finite-row-structural-guard-number-to-string-cascade"></a>
- [Finite-row structural-guard Number-to-String cascade](implementation/computations.md#cap-finite-row-structural-guard-number-to-string-cascade)
<a id="cap-finite-row-structural-guard-string-to-number-cascade"></a>
- [Finite-row structural-guard String-to-Number cascade](implementation/computations.md#cap-finite-row-structural-guard-string-to-number-cascade)
<a id="cap-finite-row-structural-guard-alternating-chain"></a>
- [Finite-row structural-guard alternating chain](implementation/computations.md#cap-finite-row-structural-guard-alternating-chain)
<a id="cap-repeatable-number-aggregate-and-root-suffix-cascades"></a>
- [Repeatable Number aggregate and root suffix cascades](implementation/computations.md#cap-repeatable-number-aggregate-and-root-suffix-cascades)
<a id="cap-repeatable-number-aggregate-and-repeatable-suffix-cascades"></a>
- [Repeatable Number aggregate and repeatable suffix cascades](implementation/computations.md#cap-repeatable-number-aggregate-and-repeatable-suffix-cascades)
<a id="cap-checked-direct-field-formal-input"></a>
- [Checked direct-field formal-input inventory](implementation/computations.md#cap-checked-direct-field-formal-input)
<a id="cap-selected-computation-preliminary"></a>
- [Selected computation-preliminary whole calls](implementation/computations.md#cap-selected-computation-preliminary)
<a id="cap-selected-computation-preliminary-assurance"></a>
- [Selected computation-preliminary whole calls — assurance](implementation/computations.md#cap-selected-computation-preliminary-assurance)
<a id="cap-result-and-application"></a>
- [Result and application](implementation/computations.md#cap-result-and-application)
<a id="cap-fixed-string-firstfilledvalue-result-application"></a>
- [Fixed ordinary String `FirstFilledValue` result/application](implementation/computations.md#cap-fixed-string-firstfilledvalue-result-application)
<a id="cap-repeatable-string-constant-computation"></a>
- [Repeatable ordinary String constant](implementation/repeatable-computations.md#cap-repeatable-string-constant-computation)
<a id="cap-repeatable-time-constant-computation"></a>
- [Repeatable Time constant](implementation/repeatable-computations.md#cap-repeatable-time-constant-computation)
<a id="cap-repeatable-datetime-constant-computation"></a>
- [Repeatable DateTime constant](implementation/repeatable-computations.md#cap-repeatable-datetime-constant-computation)
<a id="cap-repeatable-date-constant-computation"></a>
- [Repeatable Date constant](implementation/repeatable-computations.md#cap-repeatable-date-constant-computation)
<a id="cap-repeatable-number-constant-computation"></a>
- [Repeatable ordinary Number constant](implementation/repeatable-computations.md#cap-repeatable-number-constant-computation)
<a id="cap-exact-address-repeatable-string-firstfilledvalue-result-application"></a>
- [Exact-address repeatable ordinary String `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-string-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-number-firstfilledvalue-result-application"></a>
- [Exact-address repeatable Number `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-number-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-boolean-firstfilledvalue-result-application"></a>
- [Exact-address repeatable Boolean `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-boolean-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-custom-firstfilledvalue-result-application"></a>
- [Exact-address repeatable Custom `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-custom-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-datefragment-firstfilledvalue-result-application"></a>
- [Exact-address repeatable DateFragment `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-datefragment-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-daterange-firstfilledvalue-result-application"></a>
- [Exact-address repeatable DateRange `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-daterange-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-datetime-firstfilledvalue-result-application"></a>
- [Exact-address repeatable DateTime `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-datetime-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-datetime-subday-shift"></a>
- [Exact-address repeatable DateTime sub-day shift](implementation/repeatable-computations.md#cap-exact-address-repeatable-datetime-subday-shift)
<a id="cap-exact-address-repeatable-datetime-day-shift"></a>
- [Exact-address repeatable DateTime calendar-day shift](implementation/repeatable-computations.md#cap-exact-address-repeatable-datetime-day-shift)
<a id="cap-repeatable-number-datetime-shift-cascade"></a>
- [Repeatable Number-to-DateTime shift cascade](implementation/repeatable-computations.md#cap-repeatable-number-datetime-shift-cascade)
<a id="cap-exact-address-repeatable-full-date-firstfilledvalue-result-application"></a>
- [Exact-address repeatable FULL Date `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-full-date-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-time-firstfilledvalue-result-application"></a>
- [Exact-address repeatable Time `FirstFilledValue` result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-time-firstfilledvalue-result-application)
<a id="cap-exact-address-repeatable-time-constant-construction"></a>
- [Exact-address repeatable constant `Time(...)` construction](implementation/repeatable-computations.md#cap-exact-address-repeatable-time-constant-construction)
<a id="cap-exact-address-repeatable-time-construction"></a>
- [Exact-address repeatable `Time(...)` construction](implementation/repeatable-computations.md#cap-exact-address-repeatable-time-construction)
<a id="cap-world-backed-repeatable-time-construction"></a>
- [World-backed repeatable `Time(...)` construction](implementation/repeatable-computations.md#cap-world-backed-repeatable-time-construction)
<a id="cap-nonrepeatable-daterange-source-placement"></a>
- [Nonrepeatable DateRange source placement](implementation/computations.md#cap-nonrepeatable-daterange-source-placement)
<a id="cap-exact-address-repeatable-time-result-application"></a>
- [Exact-address repeatable Time result/application](implementation/repeatable-computations.md#cap-exact-address-repeatable-time-result-application)
<a id="cap-nonrepeatable-daterange-result"></a>
- [Nonrepeatable DateRange result](implementation/computations.md#cap-nonrepeatable-daterange-result)
<a id="cap-nonrepeatable-daterange-application"></a>
- [Nonrepeatable DateRange application](implementation/computations.md#cap-nonrepeatable-daterange-application)
<a id="cap-aggregate-seeded-mixed-result"></a>
- [Aggregate-seeded mixed result](implementation/computations.md#cap-aggregate-seeded-mixed-result)
<a id="cap-computation-message-partition"></a>
- [Computation message partition](implementation/computations.md#cap-computation-message-partition)
<a id="cap-computation-self-validation-type"></a>
- [Implicit self-validation message type](implementation/computations.md#cap-computation-self-validation-type)
<a id="cap-generated-computation-validation"></a>
- [Generated computation validation](implementation/computations.md#cap-generated-computation-validation)

#### Validation, message, and custom capabilities

<a id="12--validation-and-polarity"></a>
- [§12 validation and polarity](implementation/validation-messages-and-custom.md#12--validation-and-polarity)
<a id="13--message-interpolation"></a>
- [§13 message interpolation](implementation/validation-messages-and-custom.md#13--message-interpolation)
<a id="14--custom-conditions"></a>
- [§14 custom conditions](implementation/validation-messages-and-custom.md#14--custom-conditions)
<a id="cap-whole-rule-semantics"></a>
- [Whole-rule semantics](implementation/validation-messages-and-custom.md#cap-whole-rule-semantics)
<a id="cap-ordinary-once-repeatable-execution"></a>
- [Ordinary/once/repeatable execution](implementation/validation-messages-and-custom.md#cap-ordinary-once-repeatable-execution)
<a id="cap-partial-validation"></a>
- [Partial validation](implementation/validation-messages-and-custom.md#cap-partial-validation)
<a id="cap-fill-group-quantifiers"></a>
- [Fill/group quantifiers](implementation/validation-messages-and-custom.md#cap-fill-group-quantifiers)
<a id="cap-presence-contradiction-analyzer"></a>
- [Presence contradiction analyzer](implementation/validation-messages-and-custom.md#cap-presence-contradiction-analyzer)
<a id="cap-whole-rule-authoring-and-rendering"></a>
- [Whole-rule authoring and rendering](implementation/validation-messages-and-custom.md#cap-whole-rule-authoring-and-rendering)
<a id="cap-string-pattern-field-messages"></a>
- [String-pattern field messages](implementation/validation-messages-and-custom.md#cap-string-pattern-field-messages)
<a id="cap-structural-message-references"></a>
- [Structural message references](implementation/validation-messages-and-custom.md#cap-structural-message-references)
<a id="cap-shared-message-pointer"></a>
- [Shared message pointer](implementation/validation-messages-and-custom.md#cap-shared-message-pointer)
<a id="cap-computation-formal-messages"></a>
- [Computation formal messages](implementation/validation-messages-and-custom.md#cap-computation-formal-messages)
<a id="cap-custom-field-formal-messages"></a>
- [Custom-field formal messages](implementation/validation-messages-and-custom.md#cap-custom-field-formal-messages)
<a id="cap-custom-condition-callback"></a>
- [Custom-condition callback](implementation/validation-messages-and-custom.md#cap-custom-condition-callback)
<a id="cap-custom-field-validation"></a>
- [Custom-field validation](implementation/validation-messages-and-custom.md#cap-custom-field-validation)
<a id="cap-explicit-validity-predicates"></a>
- [Explicit validity predicates](implementation/validation-messages-and-custom.md#cap-explicit-validity-predicates)

#### Cross-clause capabilities and gates

<a id="current-external-evidence-gate"></a>
- [Current external-evidence gate](implementation/cross-clause.md#current-external-evidence-gate)
<a id="cross-clause-implementation-notes"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#cross-clause-implementation-notes)
<a id="resolved-number-aggregates"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#resolved-number-aggregates)
<a id="stringenumeration-aggregate-counts"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#stringenumeration-aggregate-counts)
<a id="stringenumeration-distinct-count"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#stringenumeration-distinct-count)
<a id="resolved-validation-group-presence"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#resolved-validation-group-presence)
<a id="checked-group-star-terminals"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#checked-group-star-terminals)
<a id="cap-kernel-static-diagnostic-classes"></a>
- [Kernel static-diagnostic classes](implementation/cross-clause.md#cap-kernel-static-diagnostic-classes)
<a id="cap-resolved-firstfilledvalue"></a>
- [Resolved `FirstFilledValue`](implementation/cross-clause.md#cap-resolved-firstfilledvalue)
<a id="cap-resolved-number-aggregates"></a>
- [Resolved Number aggregates](implementation/cross-clause.md#cap-resolved-number-aggregates)
<a id="cap-string-enumeration-aggregate-counts"></a>
- [String/Enumeration aggregate counts](implementation/cross-clause.md#cap-string-enumeration-aggregate-counts)
<a id="cap-boolean-confirm-value-count"></a>
- [Boolean/Confirm value count](implementation/cross-clause.md#cap-boolean-confirm-value-count)
<a id="cap-reopened-star-structural-completeness-and-addressing"></a>
- [Reopened-star structural completeness and addressing](implementation/cross-clause.md#cap-reopened-star-structural-completeness-and-addressing)
<a id="cap-resolved-group-presence-both-arms"></a>
- [Resolved group presence, both arms](implementation/cross-clause.md#cap-resolved-group-presence-both-arms)
<a id="cap-checked-group-star-terminals"></a>
- [Checked group-star terminals](implementation/cross-clause.md#cap-checked-group-star-terminals)
<a id="cap-fixed-group-bound-repeatable-ancestry"></a>
- [Fixed groups under bound repeatable ancestry](implementation/cross-clause.md#cap-fixed-group-bound-repeatable-ancestry)
<a id="cap-mixed-validation-filled-group-count"></a>
- [Mixed validation `NumberOfFilledGroups`](implementation/cross-clause.md#cap-mixed-validation-filled-group-count)
<a id="cap-resolved-date-range-overlap-truth-admission-and-scans"></a>
- [Resolved Date-range overlap truth, admission, and scans](implementation/cross-clause.md#cap-resolved-date-range-overlap-truth-admission-and-scans)
<a id="cap-resolved-direct-date-construction-and-base-year-sources"></a>
- [Resolved direct Date construction and Base-Year sources](implementation/cross-clause.md#cap-resolved-direct-date-construction-and-base-year-sources)
<a id="cap-berlin-legacy-calendar-arithmetic"></a>
- [Berlin legacy calendar arithmetic](implementation/cross-clause.md#cap-berlin-legacy-calendar-arithmetic)
<a id="cap-addressed-numeric-placement-and-execution-seam"></a>
- [Addressed numeric placement and execution seam](implementation/cross-clause.md#cap-addressed-numeric-placement-and-execution-seam)
<a id="cap-certified-direct-number-source-certificate"></a>
- [Certified direct-Number source certificate](implementation/cross-clause.md#cap-certified-direct-number-source-certificate)
<a id="cap-ordered-number-pair-certificate"></a>
- [Ordered Number-pair certificate](implementation/cross-clause.md#cap-ordered-number-pair-certificate)
<a id="cap-derived-numeric-scale-admission"></a>
- [Derived numeric scale admission](implementation/cross-clause.md#cap-derived-numeric-scale-admission)
<a id="cap-normalized-messagepointer"></a>
- [Normalized `MessagePointer`](implementation/cross-clause.md#cap-normalized-messagepointer)
<a id="cap-having-correlated-direct-field-identity"></a>
- [Correlated direct-field identity inside `Having`](implementation/cross-clause.md#cap-having-correlated-direct-field-identity)
<a id="cap-shared-entity-list-group-admission"></a>
- [Shared entity-list group admission](implementation/cross-clause.md#cap-shared-entity-list-group-admission)
<a id="cap-number-group-aggregates"></a>
- [Number group aggregates](implementation/cross-clause.md#cap-number-group-aggregates)
<a id="cap-token-group-expansion"></a>
- [Token group expansion](implementation/cross-clause.md#cap-token-group-expansion)
<a id="cap-temporal-group-uniqueness"></a>
- [Temporal group uniqueness](implementation/cross-clause.md#cap-temporal-group-uniqueness)
<a id="cap-boolean-confirm-group-value-count"></a>
- [Boolean/Confirm group value count](implementation/cross-clause.md#cap-boolean-confirm-group-value-count)
<a id="cap-group-operand-reference-projection"></a>
- [Group-operand reference projection](implementation/cross-clause.md#cap-group-operand-reference-projection)
<a id="empty-handling-coverage-rule"></a>
- [Trusted theorem surface](implementation/cross-clause.md#empty-handling-coverage-rule)
