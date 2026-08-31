# a12-kernel-lean — encoding architecture and decisions

<a id="a12-kernel-lean-encoding-architecture-decisions"></a>
<a id="a12-kernel-lean--encoding-architecture--decisions"></a>

This document owns stable Lean representation choices, semantic ownership boundaries, dependency direction, and adopted or rejected encodings. The language-neutral behavior is in [`../spec/`](../spec/); live implementation and evidence status is in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); open behavior is in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md); source provenance is in [`SOURCES.md`](SOURCES.md).

## Query contract

Search for the representation or boundary name and read that decision section. This is not a capability inventory, work log, source packet, or evidence ledger. A routine widening inside an existing owner does not update this file. A change belongs here only when it changes a public representation contract, semantic owner, dependency edge, composition invariant, or adopted/rejected encoding alternative.

## Layering and dependency direction

<a id="architecture-boundary"></a>
<a id="the-whole-model-critical-path-shares-one-checked-document-and-one-addressed-operand-stream"></a>
<a id="dependency-layout"></a>

The executable center is pure Lean:

1. [`Core.lean`](../A12Kernel/Core.lean), [`Cell.lean`](../A12Kernel/Cell.lean), and [`Document.lean`](../A12Kernel/Document.lean) own shared values, observations, addresses, and document primitives.
2. [`Semantics/`](../A12Kernel/Semantics/) owns total meanings over already-resolved inputs.
3. [`Elaboration/`](../A12Kernel/Elaboration/) owns model validation, name and path resolution, static legality, checked construction, and lowering.
4. [`Proofs/`](../A12Kernel/Proofs/) states trusted laws over the first three layers; [`Conformance/`](../A12Kernel/Conformance/) contains executable separators and checked non-laws.
5. [`Evidence/`](../A12Kernel/Evidence/), [`Reference/`](../A12Kernel/Reference/), and process/IO entry points may consume the semantic center but never define it or enter the trusted theorem root.

Dependencies point downward through that list. A semantic module never imports elaboration, evidence, protocol, or IO. Evidence, reference, and candidate-process code remain untrusted adapters around the library.

[`A12Kernel.lean`](../A12Kernel.lean), [`A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean), and [`A12Kernel/Conformance.lean`](../A12Kernel/Conformance.lean) are import-only roots and the authoritative import inventories. Feature-to-module navigation belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), not here.

Every semantic meaning is version-scoped. [`Basic.lean`](../A12Kernel/Basic.lean) records kernel 30.8.1; the reference adapter advertises its separate normalized semantics identity. Before a second kernel behavior version or stable multi-version library API makes the current unversioned meaning ambiguous, migrate the semantic namespace to the reserved `A12Kernel.V30_8_1` shape rather than hiding a parallel evaluator behind the current names.

## Core representation decisions

<a id="core-encoding-decisions"></a>

### Extrinsic ASTs with checked elaboration

<a id="extrinsic-untyped-ast-not-an-intrinsically-typed-one"></a>
<a id="checked-elaboration-resolves-names-and-owns-field-policy-coherence"></a>

Semantic ASTs remain closed, extrinsic inductives, usually parametric in their leaf representation. They are not indexed by model schema or A12 field kind. A12 legality depends on expanded declarations, scale summaries, display/category compatibility, pattern preparation, repeatable scope, and custom integration; forcing those facts into type indices would move the main proof burden into transports without removing runtime distinctions.

Checked elaboration resolves those facts once and returns a model-relative value with explicit certificates. Pure evaluators then operate on resolved leaves and cannot silently re-resolve names or invent field policy. Low-level semantic functions remain total on broader inputs for isolated laws, but kernel-correspondence claims attach only to checked entry points.

The common [`ConditionTree`](../A12Kernel/Semantics/Condition.lean) is shared only where tree shape and control flow agree. Family leaf types, observation domains, and result algebras remain distinct. New universal expression, poison, result, or checked-plan carriers require two completed consumers with the same meaning and result domain.

### Values keep semantic identity separate from storage identity

<a id="valuenum-remains-rat-number-targets-use-a-separate-exact-decimal"></a>
<a id="full-date-uses-separate-component-calendar-and-value-admission-types"></a>
<a id="time-uses-a-day-coordinate-datetime-keeps-wall-labels-separate-from-instant-identity"></a>
<a id="string-support-begins-at-two-named-consuming-clauses"></a>
<a id="resolved-enumeration-categories-are-positional-projections"></a>
<a id="enumeration-direct-field-comparability-is-a-separate-static-relation"></a>
<a id="resolved-value-list-quantifiers-are-type-indexed-and-operation-specific"></a>
<a id="string-computation-separates-expression-root-store-target-check-application-and-delta"></a>

Expression Numbers remain exact `Rat`. Static scale and literal-expandability live in checked summaries. A checked stored Number retains whether its source was decimal-valued or String-valued; decimal input keeps its exact signed coefficient/scale identity independently of the strip-and-minimum-scale text selected for formal reads, while String input remains verbatim. Computed Number identity uses its separate canonical nonnegative-scale form because numerically equal `7` and `7.00` may differ as a computation change. Formal-read checking, rounding, precision-50 arithmetic, scale-19 comparison, target admission, source-relative delta, and application are separate boundaries.

Temporal values retain both exact `Instant` identity and the decoded components exposed by their field kind. Date-bearing values also retain stored-Gregorian versus constructed legacy-hybrid provenance. A consumer never invents a missing semantic shape from an instant alone. An operation whose Kernel mechanism constructs a calendar from an exact `Date` intentionally decodes the next wall label from that instant under the selected profile while retaining the carried calendar basis; equal instants with different semantic shapes are not collapsed. Fresh local-label resolution, calendar addition, elapsed-duration arithmetic, and completed-period differences remain separate operations even when they sometimes agree. `DateRangeValue` remains the exact two-endpoint carrier. `DateRangeCellValue` wraps it or retains a yearless ordered `MM`/`MM-dd` component pair without a synthetic year or instant, and `DateRangeComputationResult` carries that same cell identity from checked producers to checked targets. `DateRangeFormat` remains the exact-presentation discriminator shared by full-Date input and target rendering. `DateRangeInputFormat` retains all six checked declaration profiles across input classification and bounded target presentation without turning yearless values into exact ranges.

String evaluation uses decoded/evaluated text, while target policy retains declaration-owned line-break, pattern, and length behavior. Target checking may measure a normalized view without replacing the attempted stored payload. Enumeration values retain stored-token identity and explicit category projection; display text is not value identity.

### The checked document owns immutable topology and prepared cell meaning

<a id="document--instantiated-rows-independent-of-cell-values"></a>
<a id="document-instantiated-rows-independent-of-cell-values"></a>

[`Document`](../A12Kernel/Document.lean) records instantiated rows independently of cell contents. Blank but instantiated repeatable rows are observable, so topology is never inferred from filled cells. Ordered lists are used where encounter order is semantically relevant; sets are used only for extensional projections whose order is not observable.

[`CheckedDocument`](../A12Kernel/Elaboration/CheckedDocument.lean) is the single model-certified input boundary. It validates row and cell placement, retains raw placement distinctions, prepares declaration-owned scalar/custom checks once, and exposes checked addressed reads. For Number placements it verifies the caller classification against the exact storage regime's selected formal-read text. Canonical Boolean/Confirm tokens and all six bounded DateRange declaration pairs are likewise reclassified from stored text and checked against the supplied raw state. Exact DateRange profiles require a supported zone before classifying any text. Configured `MM`/`MM-dd` fragments require one after successful parsing, while their yearless forms need no zone because they create no instant. The checked document preserves its caller-classified boundary for wider policies. The checked String-computation context projects retained text into the existing expression evaluator, so `FieldValueAsString` adds a typed leaf but no second document read channel or renderer. Processing context, generated findings, computation activation, public results, and caller-supplied application destinations remain separate.

Structural address failure is not semantic UNKNOWN. Checked address construction returns an explicit failure; phase observation later maps a valid checked cell to validation UNKNOWN, computation poison, clean empty, or a typed value as required by the consuming clause.

Physical topology and validation iteration are distinct projections of that same checked input. The physical addressed read, stars, auto-checks, parallel identity, and computation see only stored rows. Ordinary validation keeps the outermost repeatable level physical, recursively contributes implicit child row 1 below an existing parent with no concrete child, and reads that exact projected address as clean absent input without inserting a row. `RepetitionNotUnique` shares the validation projection because it is a validation leaf; the projection never becomes stored group content.

### Observation and control flow are phase-specific

<a id="numeric-polarity-carries-directions-not-one-substituted-bit"></a>
<a id="unified-verdict-not-a-bare-firednotfired-outcome"></a>
<a id="whole-rule-messages-attach-after-the-condition-verdict"></a>
<a id="two-level-cell-model-checkedcell--observecellphase--cellobservation"></a>
<a id="two-level-cell-model-checkedcell-observecellphase-cellobservation"></a>
<a id="partial-validation-separates-rule-gating-from-reference-masking"></a>

[`CheckedCell`](../A12Kernel/Cell.lean) retains the facts needed by both phases. `observeCell` projects them through an explicit phase, yielding validation and computation observations without pretending those result domains are interchangeable.

Validation truth uses the closed `K`/`Verdict` algebras. Computation conditions use holds/not-true/poison. The shared tree evaluators preserve the relevant ordered short-circuit behavior, but a validation UNKNOWN is not a computation poison and a public message is not an evaluator result.

Polarity and partial validation are one-sided abstractions. VALUE/OMISSION does not encode an exact future-fill classification, and partial validation does not prove equivalence with full validation. Broader theorems must state the relevant agreement, refinement, row, world, and locality assumptions.

### Repeatable semantics use named environments and checked addresses

<a id="single-level-iteration-starts-from-an-ordered-candidate-list"></a>
<a id="resolved-repetition-uniqueness-is-a-two-phase-relation"></a>
<a id="resolved-semantic-index-reads-keep-key-role-separate-from-target-observation"></a>
<a id="captured-outer-correlation-is-a-closed-filter-only-core"></a>
<a id="checked-one-star-correlation-lowering-owns-the-admitted-static-boundary"></a>
<a id="checked-finite-number-star-construction-is-shared-before-consumption"></a>

Repeatable execution uses complete named `Env` bindings and model-derived scopes, not positional row lists or flattened synthetic IDs. An address is constructed only after the checked path and environment agree. Ancestor projection shortens a complete environment through its declaration-owned scope; incompatible or ambiguous bindings fail structurally.

Candidate enumeration comes from immutable document topology. Omitted declared capacity is represented separately from instantiated empty rows. Filters preserve their own encounter/relevance facts, and consumers choose whether omitted tails, filtered rows, or missing values affect their result.

Semantic indices and parallel iteration share checked index-column facts but not a universal join engine. The checked column retains ordered normalized-key occurrences, duplicate-key information, and column unavailability. Duplicate exclusion is the one shared admission relation: no duplicated key is selectable by either projection. After admission, each consumer owns its own lookup and missing-side policy, so semantic-index reads, parallel validation, and computation clearing do not acquire one another’s runtime policy by reuse.

### Whole-model computation execution keeps definition, activation, result, application, and validation separate

The computation boundary follows the accepted decision recorded in the archived [`A12 Lean computation execution proposal`](archived/A12-LEAN-COMPUTATION-EXECUTION-PROPOSAL.md).

- A checked computation definition owns target policy, guarded alternatives, static references, and any family-specific route certificates. It retains the authored declaration context separately from resolved target placement whenever the checked family permits them to differ.
- Fixed-target execution derives its single implicit instance from target placement rather than using the declaration context as an iteration source. Repeatable placement retains its separate static relation to the declaration context; the exact behavioral boundaries remain in [the computation specification](../spec/09-computations.md#1-the-ground-rules).
- A checked plan owns execution order, target uniqueness, and the dependency restrictions established by that family. Bounded authored pair and triple wrappers may retain caller order separately when their exact dependency decisions change execution order. Neither form is a graph or general scheduler.
- A transient overlay hides stored values at every computed target and exposes only completed rich outcomes at the exact address or field key. It is private execution state, not an applied document or public result.
- Family outcomes retain no-value, accepted, rejected-with-attempt, local invalidity, and inherited poison distinctions as applicable. Dependency projection is cause-blind only where the kernel cache is cause-blind.
- Result construction classifies outcomes relative to the immutable source. Change, error, clearing, and residual-message collections are projections, not execution state.
- Application consumes an already-classified result against a separately supplied compatible destination. Shared String/Number results retain two independently applied typed destinations and two structural results rather than inventing a merged document or fail-fast family precedence. Application does not recompute source-relative change or invoke validation.
- Generated computation validation is a later validation concern and retains every relevant alternative; it never reuses computation’s first-selected execution rule.

String, scalar Number, and repeatable Number keep typed owners because their target keys, state, and result domains differ. The finite repeatable Number executor is the sole owner of that family’s multi-target path; narrower duplicate executors are retired rather than bridged. The exact two- and three-step nonrepeatable String/Number wrappers retain authored and checked execution order around the existing typed mixed executor. Wider cross-family scheduling remains open and is not a reason to introduce a universal Core IR.

All runtime message channels share A12's `PartiallyKnownDocumentMultiPointer`, which remains distinct from exact document addresses. Lean's normalized `MessagePointer` retains resolved field identity plus concrete, wildcard, or unknown repetition coordinates and is now used by validation, computation, registered custom-field, and custom-condition message boundaries. Exact computed-instance association is structural equality on that complete message pointer, not display text, prefix matching, or wildcard interpretation. Message payload rendering is separate and may depend on locale; partition membership does not. Raw pointer-factory names, malformed name/index arity, root accessors, and conversion behavior remain an SG10 public-boundary obligation rather than widening `CellAddr` or inventing a textual codec.

### `World` and host callbacks are explicit boundaries

<a id="injected-world-and-explicit-puretotal-oracles"></a>

Clock-dependent semantics receive an explicit [`World`](../A12Kernel/Document.lean). Checking does not sample time. Evaluation samples the supplied instant and applies the checked model-zone profile. Pure and clock-dependent entry points stay distinct so a theorem cannot accidentally quantify over hidden host state.

Resolved custom conditions receive an explicit pure total oracle and invocation data. The oracle is not stored in `World`: environmental time and a host callback registry have different ownership and proof obligations. Purity and totality do not imply locality, monotonicity, or stability under partial validation; consumers needing those properties must request an explicit oracle contract.

### Family data is the default derived-consumer boundary

The failed universal Core IL experiment is archived in [`SEMANTIC-CORE-IL-PROPOSAL.md`](archived/SEMANTIC-CORE-IL-PROPOSAL.md). The adopted default is to expose existing checked family structures and prove family-specific preservation laws. A shared checked-plan representation is reconsidered only under the six conditions in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers). An analyzer or transformer should consume the narrowest checked owner that answers its query rather than demand a universal intermediate language.

### External adapters transport semantics; they do not own it

<a id="the-reference-process-is-a-transport-adapter-not-a-second-evaluator"></a>
<a id="candidate-conformance-uses-the-shared-bounded-process-lane"></a>

The reference process decodes a closed normalized request, calls existing checked evaluators, and encodes a deterministic response. It defines transport validation, limits, diagnostics, and compatibility identity, not a second semantic implementation. [`PROTOCOL.md`](PROTOCOL.md) owns that public contract.

Evidence projections pin immutable observations and compare them with typed semantic results. They never enter the proof root or strengthen finite observations into universal correspondence. [`EVIDENCE.md`](EVIDENCE.md) owns exact bundles, digests, case counts, and claim limits.

Candidate conformance and bounded process control are downstream products. They may import the reference adapter; the semantic library, proofs, and conformance roots may not import them. Resource isolation is cooperative execution control, not a security boundary.

## Proof and assurance discipline

<a id="proof-discipline"></a>
<a id="polarity-and-partial-validation-are-one-sided-sound-abstract-interpretations--verify-dont-assume-the-iff"></a>
<a id="polarity-and-partial-validation-are-one-sided-sound-abstract-interpretations-verify-dont-assume-the-iff"></a>

- Trusted semantics are total pure definitions. No `partial`, `unsafe`, `IO`, external process, or retained observation enters the theorem root.
- [`TrustAudit.lean`](../A12Kernel/TrustAudit.lean) is the sole exhaustive registry. It reports theorem axioms and audits the elaborated environment; theorem counts and source-token scans are not assurance by themselves.
- A proof statement names its supported fragment, hypotheses, direction, and result domain. The nearest plausible stronger false claim is retained as a checked non-law when that distinction protects the representation.
- Conformance examples are executable separators, not kernel evidence. Kernel-locked and locally retained kernel-calibrated status remain separate dimensions in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).
- The core has no external Lake package dependency. A dependency change requires an explicit decision; substantial library-grade proof needs should prefer a separately scoped proof target over reimplementing a theorem library inside the executable core.

## Maintenance rule

Change this document only when the architecture changes. Capability growth, theorem additions, new external locks, current exclusions, and immediate next work update their own live owners. When a paragraph starts enumerating recent modules, cases, revisions, counts, or pending operators, it belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), [`EVIDENCE.md`](EVIDENCE.md), [`SOURCES.md`](SOURCES.md), [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), or [`PLAN.md`](PLAN.md) instead.
