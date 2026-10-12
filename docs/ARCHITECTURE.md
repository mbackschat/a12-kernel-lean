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

[`ValidationRelevance.lean`](../A12Kernel/Elaboration/ValidationRelevance.lean) owns relevance patterns, coordinate coverage and group relevance independently of authored star-path lowering. [`StarPath.lean`](../A12Kernel/Elaboration/StarPath.lean) consumes that boundary; declared-slot coverage partitions the input patterns while runtime group traversal retains its separate topology and short-circuit policy.

Every semantic meaning is version-scoped. [`Basic.lean`](../A12Kernel/Basic.lean) records kernel 30.8.1; the reference adapter advertises its separate normalized semantics identity. Before a second kernel behavior version or stable multi-version library API makes the current unversioned meaning ambiguous, migrate the semantic namespace to the reserved `A12Kernel.V30_8_1` shape rather than hiding a parallel evaluator behind the current names.

## Core representation decisions

<a id="core-encoding-decisions"></a>

### Extrinsic ASTs with checked elaboration

<a id="extrinsic-untyped-ast-not-an-intrinsically-typed-one"></a>
<a id="checked-elaboration-resolves-names-and-owns-field-policy-coherence"></a>

Semantic ASTs remain closed, extrinsic inductives, usually parametric in their leaf representation. They are not indexed by model schema or A12 field kind. A12 legality depends on expanded declarations, scale summaries, display/category compatibility, pattern preparation, repeatable scope, and custom integration; forcing those facts into type indices would move the main proof burden into transports without removing runtime distinctions.

Checked elaboration resolves those facts once and returns a model-relative value with explicit certificates. Pure evaluators then operate on resolved leaves and cannot silently re-resolve names or invent field policy. Low-level semantic functions remain total on broader inputs for isolated laws, but kernel-correspondence claims attach only to checked entry points.

The [raw reference AST](../A12Kernel/Reference/Dm/Syntax.lean) preserves authored attachment ownership before static admission: a reference owns its filter and its optional literal or recursive-reference key; `@From` stores the same reference type. Call arguments retain only their expression and optional range end. Readers, printers and rewrites traverse this single representation; lowerers must consume or refuse metadata rather than silently drop it ([implemented boundary](implementation/cross-clause.md#cap-semantic-index-admission)).

Pattern leaves retain an exact compiler-associated matcher through [`CompiledStringPattern`](../A12Kernel/Semantics/StringPattern.lean); ordinary checked conditions and correlated filters share its admission owner. The resolved filter tree carries this opaque capability and has no decidable structural equality. Authored filter syntax retains equality; consumers must not identify runtime matchers by source text alone.

Ordinary validation iteration keeps reached temporal runtime failure outside the verdict algebra until the rule handler consumes it. The addressed result exposes structural and temporal failure separately. The loop stops on temporal failure while retaining the failing environment beside the outcome; the emitted error pointer belongs to the iterator's first environment. Thus consumers must not infer the evaluated row solely from the message address ([execution owner](../A12Kernel/Elaboration/ValidationRule.lean)).

The checked mixed [`ValidationCondition`](../A12Kernel/Elaboration/ValidationCondition/Assembly.lean) keeps `declaringGroup` for lexical origin and `rowGroup` for its certified execution binding. A descendant error field can supply the latter without relocating authored paths. Rebinding rechecks the same resolved core; rule containment uses the original declaration, and combining conditions requires both contexts to agree. Numeric comparisons and field-fill lists use this distinction through their existing elaborators and evaluators.

The [scalar temporal and numeric boundary](../A12Kernel/Elaboration/TemporalExpression/Types.lean) uses mutually recursive data to retain numeric shift amounts and temporal component sources. Its total evaluator specializes the existing ordered temporal traversal and authored numeric traversal; it does not store evaluator functions or use a recursion limit. Standalone numeric resolution and expression evaluation sit below this boundary, while complete temporal projections enter numeric validation and computation above it. This dependency direction permits reciprocal expressions without making primitive numeric checking depend on the complete temporal evaluator.

The common [`ConditionTree`](../A12Kernel/Semantics/Condition.lean) is shared only where tree shape and control flow agree. Family leaf types, observation domains, and result algebras remain distinct. New universal expression, poison, result, or checked-plan carriers require two completed consumers with the same meaning and result domain.

The shared [`HavingRepetitionRef`](../A12Kernel/Semantics/Correlation.lean) retains origin plus either a repeatable level or a fixed group path. A fixed group's runtime index is one, but replacing its reference with a numeric literal would erase the ancestry needed for binding, filter-scope admission, and static rule iteration. Elaboration derives that ancestry from the model and rejects a fixed constructor naming a repeatable group; the semantic layer stores the path as name segments without importing model declarations. Consumers comparing or rewriting references must retain path and origin even when their values agree. The [correlation implementation owner](implementation/repetition-and-paths.md#cap-star-selection-and-correlation) records the supported routes and assurance.

### Values keep semantic identity separate from storage identity

<a id="valuenum-remains-rat-number-targets-use-a-separate-exact-decimal"></a>
<a id="full-date-uses-separate-component-calendar-and-value-admission-types"></a>
<a id="time-uses-a-day-coordinate-datetime-keeps-wall-labels-separate-from-instant-identity"></a>
<a id="string-support-begins-at-two-named-consuming-clauses"></a>
<a id="resolved-enumeration-categories-are-positional-projections"></a>
<a id="enumeration-direct-field-comparability-is-a-separate-static-relation"></a>
<a id="resolved-value-list-quantifiers-are-type-indexed-and-operation-specific"></a>
<a id="string-computation-separates-expression-root-store-target-check-application-and-delta"></a>

Expression Numbers remain exact `Rat`. [`NumericLiteral.lean`](../A12Kernel/Semantics/NumericLiteral.lean) owns decoded literal identity and the shared measured Java-rounded signed-32-bit conversion because both iteration legality and rule-set analysis consume it; elaboration-owned scale summaries import that semantic owner rather than defining a conversion that semantic analysis would have to depend on upward. Authored decimal scale remains separate from value and converted host identity. A checked stored Number retains whether its source was decimal-valued or String-valued; decimal input keeps its exact signed coefficient/scale identity independently of the strip-and-minimum-scale text selected for formal reads, while String input remains verbatim. Computed Number identity uses its separate canonical nonnegative-scale form because numerically equal `7` and `7.00` may differ as a computation change. Formal-read checking, rounding, precision-50 arithmetic, scale-19 comparison, target admission, source-relative delta, and application are separate boundaries.

Temporal values retain both exact `Instant` identity and the decoded components exposed by their field kind. Date-bearing values also retain stored-Gregorian versus constructed legacy-hybrid provenance. A consumer never invents a missing semantic shape from an instant alone. An operation whose Kernel mechanism constructs a calendar from an exact `Date` intentionally decodes the next wall label from that instant under the selected profile while retaining the carried calendar basis; equal instants with different semantic shapes are not collapsed. Fresh local-label resolution, calendar addition, elapsed-duration arithmetic, and completed-period differences remain separate operations even when they sometimes agree. `DateRangeValue` remains the exact two-endpoint carrier. `DateRangeCellValue` wraps it or retains a yearless ordered `MM`/`MM-dd` component pair without a synthetic year or instant, and `DateRangeComputationResult` carries that same cell identity from checked producers to checked targets. `DateRangeFormat` remains the exact-presentation discriminator shared by full-Date input and target rendering. `DateRangeInputFormat` retains all eight checked declaration profiles across classification and target presentation. `DateRangeRuntimeInput` separates declared document conversion from first-definition shared runtime policy and target formal checking. Endpoint completion retains its own calendar identity rather than reapplying storage restrictions.

String evaluation uses decoded/evaluated text, while target policy retains declaration-owned line-break, pattern, and length behavior. Target checking may measure a normalized view without replacing the attempted stored payload. Enumeration values retain stored-token identity and explicit category projection; display text is not value identity.

### The checked document owns immutable topology and prepared cell meaning

<a id="document--instantiated-rows-independent-of-cell-values"></a>
<a id="document-instantiated-rows-independent-of-cell-values"></a>

[`Document`](../A12Kernel/Document.lean) records instantiated rows independently of cell contents. Blank but instantiated repeatable rows are observable, so topology is never inferred from filled cells. Ordered lists are used where encounter order is semantically relevant; sets are used only for extensional projections whose order is not observable.

[`CheckedDocument`](../A12Kernel/Elaboration/CheckedDocument.lean) is the single model-certified input boundary. It validates row and cell placement, retains raw placement distinctions, prepares declaration-owned scalar/custom checks once, retains their world and locale for computed-target callbacks, and exposes checked addressed reads. For Number placements it verifies the caller classification against the exact storage regime's selected formal-read text. Canonical Boolean/Confirm tokens and all eight DateRange declaration pairs are likewise reclassified from stored text and checked against the supplied raw state. DateRange coherence checks runtime text through the model’s shared policy without repeating declared conversion. Anchored endpoints require a supported zone; uninterpreted yearless forms without Base Year create no instant and need no zone. The checked document preserves its caller-classified boundary for wider policies. The checked String-computation context projects retained text into the existing expression evaluator, so `FieldValueAsString` adds a typed leaf but no second document read channel or renderer. Processing context, generated findings, computation activation, public results, and caller-supplied application destinations remain separate.

The [checked-cell placement](../A12Kernel/Elaboration/CheckedCellPlacement.lean) representation and [model-capacity lookup](../A12Kernel/Elaboration/Flat/Capacity.lean) are independent of document construction. [Group-presence projection](../A12Kernel/Elaboration/GroupPresenceInput.lean) consumes those inputs directly; [checked-document adapters](../A12Kernel/Elaboration/CheckedGroupPresence.lean) retain the existing entry points. The private document constructor stays with validation. This boundary lets projection checks compile without parser preparation or the complete computation reader. [Constructed-date admission](../A12Kernel/Elaboration/ConstructedDateComponents.lean) likewise imports the model interface directly; document-dependent evaluation remains in its separate owner.

A checked evaluation view retains optional `filterRows` separately from immutable physical topology. Whole-program computation entry points derive that view once; nested plans inherit it. `readDocument` carries the view into raw evaluators, and filter adapters explicitly use declared-cell reads for virtual coordinates while preserving the supplied overlay on concrete rows. [Star addressing](../A12Kernel/Semantics/StarAddressing.lean) enumerates bounded candidates without materializing rows; public physical addressing continues to reject missing ancestors.

Structural address failure is not semantic UNKNOWN. Checked address construction returns an explicit failure; phase observation later maps a valid checked cell to validation UNKNOWN, computation poison, clean empty, or a typed value as required by the consuming clause.

Physical topology and validation iteration are distinct projections of that same checked input. The physical addressed read, stars, auto-checks, parallel identity, and computation see only stored rows. Ordinary full validation uses a separate root-dispatched coordinate domain and reads its implicit cells without inserting rows. The uniqueness relation has its own sparse coordinate domain rather than inheriting the enclosing rule’s domain. Both reuse the traversal owned by [RuleIterationDomain](../A12Kernel/Semantics/RuleIterationDomain.lean); [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) owns their distinct selection rules. Partial validation retains its separately bounded projection.

### Observation and control flow are phase-specific

<a id="numeric-polarity-carries-directions-not-one-substituted-bit"></a>
<a id="unified-verdict-not-a-bare-firednotfired-outcome"></a>
<a id="whole-rule-messages-attach-after-the-condition-verdict"></a>
<a id="two-level-cell-model-checkedcell--observecellphase--cellobservation"></a>
<a id="two-level-cell-model-checkedcell-observecellphase-cellobservation"></a>
<a id="partial-validation-separates-rule-gating-from-reference-masking"></a>

[`CheckedCell`](../A12Kernel/Cell.lean) retains the facts needed by both phases. Blocking `findings` control availability; separate `reports` retain readable custom findings. `formalReports` supplies both to output consumers. `observeCell` projects availability through an explicit phase, yielding validation and computation observations without pretending those result domains are interchangeable.

Computed custom targets reuse the [String target checker](../A12Kernel/Semantics/StringComputation.lean), retaining attempted text and the callback payload in `StringTargetError.custom`. The [dependency bridge](../A12Kernel/Semantics/StringCascade.lean) admits the reserved report while result application still clears the errored target. The [custom-ingestion mode decision](../A12Kernel/Semantics/CustomFieldFormalMessage.lean) is separate from cell readability; it contributes only the custom formal gate to whole-call orchestration.

Validation truth uses the closed `K`/`Verdict` algebras. Computation conditions use holds/not-true/poison. Ordinary mixed validation separates short-circuit Boolean truth from statically enabled eager message classification; reached temporal failure in either phase stays outside the verdict algebra. Checked leaves retain classification eligibility, including the authored membership-versus-quantifier form that pure value-list evaluation can erase. The non-firing UNKNOWN projection remains internal information, not another observable kernel pass. A validation UNKNOWN is not a computation poison and a public message is not an evaluator result ([phase owner](../A12Kernel/Elaboration/ValidationCondition/Iteration.lean), [canonical contract](../spec/10-validation-and-polarity.md#31-truth-testing-and-message-classification)).

Rule message emission takes the already-resolved coordinates of its `MessagePointer` after the verdict. Physical error paths specialize that boundary with concrete coordinates; unmatched indexed rows retain unknown coordinates without entering `CellAddr` or document topology. The message retains ordinary-condition versus caught-runtime-failure origin because the reference projection needs that distinction: a caught failure has empty reference sets even though its polarity is VALUE.

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

Semantic indices and parallel iteration share checked index-column facts but not a universal join engine. The checked column retains ordered normalized-key occurrences, duplicate-key information, and column unavailability. Duplicate exclusion is the one shared admission relation: no duplicated key is selectable by either projection. Parallel validation also retains the declaration-rendered iteration token independently of normalized lookup identity: distinct Number tokens can select the same pair and require separate visits. After admission, each consumer owns its own lookup and missing-side policy, so semantic-index reads, parallel validation, and computation clearing do not acquire one another’s runtime policy by reuse.

### Whole-model computation execution keeps definition, activation, result, application, and validation separate

The computation boundary follows the accepted decision recorded in the archived `A12 Lean computation execution proposal` (`docs/archived/A12-LEAN-COMPUTATION-EXECUTION-PROPOSAL.md` at `a050f150`).

- A checked computation definition owns target policy, guarded alternatives, static references, and any family-specific route certificates. It retains the authored declaration context separately from resolved target placement whenever the checked family permits them to differ.
- Fixed-target execution derives its single implicit instance from target placement rather than using the declaration context as an iteration source. Repeatable placement retains its separate static relation to the declaration context; the exact behavioral boundaries remain in [the computation specification](../spec/09-computations.md#1-the-ground-rules).
- A checked plan owns execution order, target uniqueness, and the dependency restrictions established by that family. An authored scalar plan retains caller order separately from the dependency order it certifies over flat scalar steps; repeatable scheduling is not part of it.
- A transient overlay hides stored values at every computed target and exposes only completed rich outcomes at the exact address or field key. It is private execution state, not an applied document or public result.
- Family outcomes retain no-value, accepted, rejected-with-attempt, local invalidity, and inherited poison distinctions as applicable. Dependency projection is cause-blind only where the kernel cache is cause-blind.
- Result construction classifies outcomes relative to the immutable source. Change, error, clearing, and residual-message collections are projections, not execution state. Pure String and Number classification lives in [String result semantics](../A12Kernel/Semantics/StringComputationRunResult.lean) and [Number result semantics](../A12Kernel/Semantics/NumericComputationRunResult.lean), keeping private constructors with their construction functions. Checked adapters attach document source state and execute plans; pure classification and mixed-result laws do not import those adapters.
- Application consumes an already-classified result against a separately supplied compatible destination. The pure [String](../A12Kernel/Semantics/StringComputationApplicationFold.lean) and [Number](../A12Kernel/Semantics/NumericComputationApplicationFold.lean) folds own duplicate-action rejection and ordered clear/error/change transitions. Checked application adapters own target legality and row materialization; their source-state accessors do not depend on execution. Shared String/Number results retain two independently applied typed destinations and two structural results rather than inventing a merged document or fail-fast family precedence. Application does not recompute source-relative change or invoke validation.
- Generated computation validation is a later validation concern and retains every relevant alternative; it never reuses computation’s first-selected execution rule.

String, scalar Number, and repeatable Number keep typed owners because their target keys, state, and result domains differ. The finite repeatable Number executor is the sole owner of that family’s multi-target path; narrower duplicate executors are retired rather than bridged. The exact two- and three-step nonrepeatable String/Number wrappers retain authored and checked execution order around the existing typed mixed executor. Wider cross-family scheduling remains open and is not a reason to introduce a universal Core IR.

All runtime message channels share A12's `PartiallyKnownDocumentMultiPointer`, which remains distinct from exact document addresses. Lean's normalized `MessagePointer` retains resolved field identity plus concrete, wildcard, or unknown repetition coordinates and is now used by validation, computation, registered custom-field, and custom-condition message boundaries. Exact computed-instance association is structural equality on that complete message pointer, not display text, prefix matching, or wildcard interpretation. Message payload rendering is separate and may depend on locale; partition membership does not. Raw pointer-factory names, malformed name/index arity, root accessors, and conversion behavior remain an SG10 public-boundary obligation rather than widening `CellAddr` or inventing a textual codec.

### `World` and host callbacks are explicit boundaries

<a id="injected-world-and-explicit-puretotal-oracles"></a>

Clock-dependent semantics receive an explicit [`World`](../A12Kernel/Document.lean). Checking does not sample time. Evaluation samples the supplied instant and applies the checked model-zone profile. Pure and clock-dependent entry points stay distinct so a theorem cannot accidentally quantify over hidden host state.

Checked custom-condition authoring retains the lexer-distinguished unquoted or quote-escaped spelling beside its normalized callback key. The locale-specific reserved-terminal predicate stays caller-owned: quoting bypasses terminal classification but not the narrower quoted-name character grammar. Resolved custom conditions then receive an explicit pure total oracle and invocation data. The oracle is not stored in `World`: environmental time and a host callback registry have different ownership and proof obligations. Purity and totality do not imply locality, monotonicity, or stability under partial validation; consumers needing those properties must request an explicit oracle contract.

### Family data is the default derived-consumer boundary

The failed universal Core IL experiment is archived in `SEMANTIC-CORE-IL-PROPOSAL.md` (`docs/archived/SEMANTIC-CORE-IL-PROPOSAL.md` at `a050f150`). The adopted default is to expose existing checked family structures and prove family-specific preservation laws. A shared checked-plan representation is reconsidered only under the six conditions in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers). An analyzer or transformer should consume the narrowest checked owner that answers its query rather than demand a universal intermediate language.

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
