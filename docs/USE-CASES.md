# Consumer probes and what this Lean semantics can enable

This is the user-facing map of bounded consumer probes and possible later products built from `a12-kernel-lean`. It explains the potential of the project, not the set of tools implemented today. The current public process surface remains the narrow evaluator described in the top-level [`README.md`](../README.md); current internal clause-level support is recorded only in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

The central idea is simple: once A12 behavior is represented as explicit executable semantics, linked to retained kernel observations, and surrounded by named theorems and counterexamples, the result can support more than an interpreter. Different consumers ask different questions of the same semantic foundation. The canonical category taxonomy is defined in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#general-consumer-task-categories); this document is its reader-facing explanation.

## The ten general categories

| Category | General task | First bounded consumer probe | Possible later products |
|---|---|---|---|
| Execute | A12 artifact + runtime input → semantic outcome | Have an isolated implementer reconstruct one named evaluator fragment's decision procedure and predict its separating outcomes from existing artifacts | Reference evaluator, independent interpreter, validation/computation service |
| Translate | Source representation ↔ checked A12 artifact or target projection | Lower one pinned external subset into a closed A12 target and expose every rejection or loss | JSON Schema importer, concrete-DSL lowering, legacy-model migration, bounded export |
| Transform | A12 artifact → behavior-related A12 artifact | Apply one rule rewrite under explicit preconditions and check its complete named observation relation | Rule refactoring, simplification, normalization |
| Compile | A12 artifact → executable plan or target program | Replace one evaluator step with a specialized plan and test a narrow refinement claim | Specialized evaluator, indexed correlation plan, WASM/Rust generator |
| Analyze | A12 artifact → facts or witnesses | Run one solver-free reachability, overlap, dependency, or redundancy analysis over a closed fragment | Equivalence, redundancy, dependency, impact, satisfiability |
| Verify | Artifact + independently stated claim → checked proof/certificate, counterexample, or explicit inconclusive result | State and check one business or preservation claim for a small admitted model | Business invariants, preservation theorems, model approval |
| Synthesize | Goal or constraint → document, rule, repair, or counterexample | Generate one bounded witness and replay it through the Lean semantics | Test-data generation, minimal repair, missing-case witness |
| Qualify | Implementation/version + reference → agreement or differences | Seed one predicted semantic defect and check that existing fixtures, laws, or differentials detect it | Conformance, differential, property, fuzz, and mutation testing |
| Explain | Execution/proof/change → human-understandable account | Give an isolated reader one checked non-trivial trace and test whether they can reconstruct the outcome and limits | Evaluation traces, debugging, checked tutorials, change reports |
| Govern | Versioned artifacts and evidence → compatibility or release decision | Simulate one semantic correction and identify the affected clauses, claims, and candidate capabilities | Support manifests, migration reports, audits, release gates |

These categories describe task contracts, not programming languages or maturity levels, and a real product may combine several of them. Rust and Python versions of the same evaluator remain in **Execute**; their test program also uses **Qualify**. Moving from an evaluator to a JSON Schema importer changes the primary task to **Translate**, even if both programs happen to be written in Rust, and a production importer may additionally use **Verify**, **Explain**, and **Govern**.

## Consumer probes first

A consumer probe is a small pre-product experiment over one named task profile. It uses the current semantics, examples, laws/non-laws, evidence limits, and exclusions to test whether the material is useful and whether a consumer would have to repeat A12 research. It may end with a successful readback or prototype, but it may also return a missing semantic distinction, an unsupported prerequisite, an awkward interface, a new use case, or a better task boundary.

The lifecycle is intentionally conditional:

```text
semantic capsules → consumer probe → research-closed shipment → cold qualification → optional product
```

Catalog inclusion commits the project to none of these stages. When [`PLAN.md`](PLAN.md) explicitly selects a probe, only that bounded probe is authorized; shipment, qualification, infrastructure, and product work remain separate decisions. A successful probe demonstrates potential for its exact task. New potential discovered by a probe is classified under the ten categories when one fits, or proposed as a new task category when its input/output relation is genuinely different.

### What completed probes established

<a id="completed-probe-record-generated-computation-alternatives"></a>
<a id="completed-probe-record-whole-rule-messages-and-cross-level-capture"></a>
<a id="completed-probe-record-resolved-firstfilledvalue"></a>
<a id="completed-probe-record-resolved-date-range-overlap"></a>
<a id="completed-probe-record-computation-field-fill-quantifiers"></a>
<a id="completed-probe-record-validation-field-fill-quantifiers"></a>
<a id="completed-probe-record-fresh-rust-correlation-runtime"></a>
<a id="completed-probe-record-resolved-number-aggregates"></a>
<a id="completed-probe-record-resolved-temporal-comparison-and-extrema"></a>
<a id="completed-probe-record-registered-custom-fields"></a>
<a id="completed-probe-record-checked-nonrepeatable-enumerations"></a>
<a id="completed-same-context-probe-record-rule-wide-having-discovery"></a>
<a id="completed-same-context-probe-record-checked-starred-field-projection"></a>
<a id="completed-same-context-probe-record-addressed-filter-failure"></a>
<a id="completed-probe-record-immutable-checked-document"></a>
<a id="completed-probe-record-sg2-checked-addressed-operand-construction"></a>

Completed probes have repeatedly shown that the normalized semantic owners are usable without renewed kernel archaeology, while also finding real representation defects before shipment. Their durable implementation and evidence state belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); capability-specific external handover results belong in the two implementation kits. The reader-facing results are:

| Probe family | Tasks exercised | Durable result and limit |
|---|---|---|
| Generated computation alternatives and whole-rule messages | Execute, Transform, Explain | Consumers recovered first-selection versus all-alternatives validation, exact verdict/message timing, and unsafe overlapping-guard accounts. No public compiler or transformation shipment was created. |
| Resolved first-filled, aggregates, Date ranges, and temporal extrema | Execute, Transform, Analyze, Explain | Consumers recovered prefix sensitivity, filter/missingness provenance, rounding and order constraints, and exact-instant temporal identity. The direct temporal computation profile reconstructs its fixed UTC carriers, clearing/application, and twelve outcomes from canonical clauses plus the calibrated source record. The checked direct DateRange-bound subset exposes both stored policies, exact endpoint identity, fixed-Date comparison in either position, all four numeric components, and non-value behavior. The checked construction-pair subset exposes all four DateFragment profiles, including configured-Base-Year and yearless `MM` and `MM-dd`, all four typed endpoint observations, component mismatch, and the equality verdict without source-identity carry or a synthetic year. The checked mixed subset additionally exposes authored side, construction endpoints, exact year-bearing or configured stored identity, component-only yearless identity, and same-profile equality while refusing cross-profile pairs. The checked constructor-target subset exposes target and endpoint identities across both exact policies and all four matching fragments, retains component-only `MM` and `MM-dd` without Base Year, and reports accepted or inverted-error attempts plus value/clear application. The checked singular-overlap subset exposes authored operand order, source identity, concrete addresses, topology, skipped/kept occurrence identity, operand-local filter provenance, duplicate same-address occurrences, and the derived any-pair verdict without a global filter shortcut. The checked plural-overlap subset separates complete checked source from the reached list prefix, exposes scalar-first unread-list termination and first-match filter polarity, and retains direct, starred, fixed-group, and starred-group identities plus complete addresses. Its declaration-major group trace is a project normalization, not an external witness-order claim. Partial validation, rule/message integration, wider policies and zones, wider computation targets, research-closed shipment, and public compatibility remain separate. |
| String-indexed DateRange construction | Execute, Analyze, Explain | An isolated reader reconstructed literal and direct evaluated String selector identity, exact-text row selection, selected addresses, clean no-selection versus selected-empty, selector-formal versus duplicate-column poison, authored endpoint position, and inverted attempted-target rejection from the canonical DateRange, path, and computation clauses plus the bounded capability record. The first readback correctly stopped when the computation-target clause was omitted from its allowlist; adding that existing owner completed the trace without a semantic change. Reversed field-key output remains internally determined rather than externally pinned, and no shipment or public compatibility was created. |
| Fill quantifiers and checked Enumeration | Execute, Transform, Explain | Consumers retained value-list order, three-way cell classification, positional categories, union admission, and non-complement laws. They did not establish complete authored/repeatable Enumeration support. |
| Registered custom fields | Execute, Explain, Qualify design | Consumers recovered one-observation validation, exact rejection/message projection, and host-boundary limits. Pure Lean evaluation does not itself prove host caching or exception behavior. |
| Immutable checked document and addressed operands | Execute, Analyze, Explain | Cold readers reconstructed row topology, placement, relevance, checked values, environments, exact addresses, and structural failures. The probes found and drove fixes for default leakage, incomplete required inventories, positional environment lookup, and duplicate bindings. |
| Cross-family computation formal inputs | Execute, Analyze, Explain, Compile | Cold consumers recovered exact root, enclosing, and leaf placements across Time, FullDate, and String-shaped Enumeration results, then transported the multi-operation union through homogeneous Enumeration and heterogeneous Number-to-DateTime whole-call results. A checked numeric-table probe additionally retained all alternative guards and operations, expanded fixed group-count operands, separated raw computed dependencies from the globally target-excluded formal-input set, and reconstructed one labeled three-target cycle plus an acyclic dependency-first order. A generated-table Compile refinement then retained its common and row-local guards, all operation dependencies, target exclusion, common-before-local selection, and reached poison across all 27 finite guard assignments. Its first Execute successor carried the same admitted table through selected source-copy or Date-year evaluation and declaration-owned zero rejection: two independently structured consumer evaluators agreed on exact result and labeled read trace for all 108 finite assignments, ten wrong accounts failed, and Lean matched every result. A second Execute probe transported seven completed target outcomes across six immutable source placements and four separate destination placements: its two independent evaluators agreed on all 168 exact public-result and applied-state combinations, ten wrong accounts failed, and Lean matched every exact signature. Group containment beyond this fixed numeric shape and resolved filters, wider execution, supplied-message partition beyond the derived value-less target message, later validation, scheduling, structural failures, shipment, and Kernel correspondence remain outside the probes. |
| Correlation and repeatable addressing | Execute, Transform, Qualify | A fresh independent runtime probe and later checked-address probes preserved outer capture, row identity, filter timing, and structural failure. The current public correlation kit owns the self-contained handover and finite qualification limits. |
| Computed-target diagnostics | Translate, Explain | A bounded Number/String probe translates measured scale and self-reference refusals to their exact Kernel codes while retaining uncovered family-local refusals separately from acceptance. Number scale suppression exposes the reached self-reference rather than manufacturing a valid operation. The probe adds no mapping beyond the measured shapes. |
| Whole-rule diagnostics | Translate, Explain | An in-context checked client separated admission, the exact error-field-reference and negative-iteration Kernel codes, and an unmapped iteration-scope refusal through the existing public projector. An absent mapping remained a typed local refusal rather than becoming admission or an invented external class; no wrapper, protocol, adapter, runner, or shipment was added. |
| Proof-bearing flat analysis | Analyze | The checked-flat pilot proves one exact contradiction family and retains false `Or` and different-field generalizations. It is not a recursive linter, command, solver, or general reachability engine. |
| Repeatable textual Number leaves | Analyze, Transform | The checked-family probe separates expression-operand read, prior target-state read, and target write, retaining target policy plus selected Enumeration projection or range interval. Fingerprint comparison distinguishes stored/category, endpoint, and cross-family changes without claiming inequivalence; exact identity is the sole proved Transform. There is no rewrite engine or public shipment. |
| Structural `CurrentRepetition` Number cascade | Execute, Analyze | An in-context checked client imported only the owning elaboration module, executed the ordered rich outcomes, recovered the structural group separately from the exact field edges, rejected a manufactured reverse edge, and preserved multi-row insufficient information. No wrapper, graph, evaluator, protocol, runner, or shipment was added. |
| Cross-family Number-to-DateTime cascade | Execute, Analyze, Transform | An isolated Python standard-library implementer reconstructed outer-to-inner dependency, source-first poison, complete outcomes, source-relative actions, and separate application from frozen artifacts plus one fixture. Five tests killed stale fallback, eager poison, address flattening, and destination-relative classification without renewed A12 research. This is finite Q only, not Kernel correspondence, shipment research closure, or public compatibility. |
| [Cross-category feasibility laboratory](consumer-probes/README.md) | All ten categories | All ten categories now have a green bounded task with disposable independent consumers and Lean reconciliation. Analyze is green for presence reachability and checked scalar numeric-table cycles, while broader family-neutral graph reconstruction remains amber because Lean has no general graph certificate. Explain became green after SG4 supplied the missing checked direct-field formal-input inventory and exact result projection. Compile now covers both a finite condition and one admitted generated numeric table, including common-before-local selection and complete static input projection. Execute now covers that generated table through exact selected-operation and target-check outcomes over 108 finite assignments, then through source-relative public result and separate-destination application over 168 finite combinations. One initially green-looking calendar-day Execute candidate was rejected by Lean and corrected after a handover retrieval defect was fixed. The lab supports the overall semantic-factory approach for bounded tasks, but does not establish general consumers, Kernel correspondence, shipment readiness, or public compatibility. |

The general lesson is that a useful consumer surface must expose exact distinctions and explicit insufficient-information results; a successful readback is not a new support claim. Historical per-probe chronology remains in Git. The current flat and correlation handovers are in [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md).

The exact revisions for the consolidated probe families remain queryable without restoring their narratives: generated alternatives `9a52b34`, whole-rule messages/cross-level capture `e53eab3`, resolved `FirstFilledValue` `4e51f90`, resolved Number aggregates `8e08136`, and resolved temporal comparison/extrema `678c799` over semantic source revision `c6c80e7`.

## 1. Execute

**What it enables:** a reference evaluator, an independent interpreter, validation and computation services, partial validation, batch execution, interactive form evaluation, or a debug oracle for a faster production runtime.

**How Lean helps:** the evaluator is an executable definition of the chosen semantics rather than prose interpreted separately by every team. Closed data types preserve distinctions such as empty versus invalid, inner versus outer row, unknown versus not-fired, and VALUE versus OMISSION. Theorems establish internal laws for all modeled inputs, while retained kernel observations empirically anchor the primitive choices. A downstream implementation can compare normalized results with the Lean reference without embedding Lean in production.

**Limit:** Lean proofs about the reference do not automatically prove a Rust, Python, Kotlin, or TypeScript evaluator correct. That implementation still needs conformance, differential, property, and operational testing over a pinned capability.

## 2. Translate

**What it enables:** importing a selected JSON Schema or OpenAPI subset, lowering the concrete A12 DSL, migrating a legacy model, translating database or form schemas, or exporting a bounded A12 projection to another format.

**How Lean helps:** the source language, supported A12 target, and mapping can be modeled separately. The importer can be required to return either a well-formed target or an explicit rejection or approximation. Lean can prove target well-formedness and, for a closed subset, the precise direction in which source satisfaction and A12 validation correspond. Counterexamples expose the first unsupported case instead of allowing silent information loss.

**Limit:** the format name is not a correctness claim. A JSON Schema capability must pin a dialect and keyword subset, model source meaning, define how JSON instances correspond to A12 Documents, and either check parsing/reference resolution or declare a pre-parsed source-AST trust boundary. Source-validator evidence, a translation theorem, and target A12 kernel evidence are separate assurances.

## 3. Transform

**What it enables:** simplifying or normalizing rules, desugaring generated rules, eliminating redundancy, renaming paths, splitting or merging rules, reordering safe conditions, rewriting computations, or checking a manually authored model patch.

**How Lean helps:** a transformation receives explicit preconditions and an exact relation between its input and output. Lean can prove equivalence, one-way refinement, reduction, relaxation, or another accurately named relation over the complete declared observation domain. The project can retain the nearest counterexample outside the safe preconditions. An untrusted refactoring frontend can optionally emit a compact certificate checked by a smaller trusted Lean-defined verifier.

**Current narrow example:** the internal addressed numeric-operation probe admits only the identity Transform over checked `FieldValueAsNumber`, `RangeAsNumber`, direct Number, root `Abs`, root Round, and nonempty bounded `Min`/`Max` operations over direct or operand-local-`Abs`/Round fields plus at most one immediate literal, and proves that it preserves every rich addressed outcome and complete source-relative result view for every checked document. A separate Analyze fingerprint retains target, ordered source fields, repeatable scope, full target policy, conversion projection or interval, root wrapper/mode/result scale, and extremum operation plus exact ordered direct-field/local-wrapper/literal identity; executable controls show that stored/category, changed-endpoint, direct/root-`Abs`, root-Round mode, extremum-operation, source order, cardinality, direct/local-`Abs`, local-Round mode/places, literal position, literal authored scale, and cross-family fingerprints differ, but make no semantic-inequivalence claim. The fingerprint additionally decides **which declared target scales an operation could legally carry**, and that decision provably runs through the elaborator's own admission gate rather than a second rule, so a retargeting consumer needs no re-elaboration: two operations with the same derived scale admit different target scales when only one is capability-carrying, and a fieldless list reports an empty read set with its write target and repeatable scope intact.

**Limit:** equal Boolean truth is often insufficient. Depending on the fragment, preservation may also need unknown or poison, message polarity and location, computation deltas, clearing, stored form, read footprints, and observable order.

## 4. Compile

**What it enables:** generating specialized evaluators, compiling rules to Rust, Kotlin, JavaScript, WASM, SQL, or another target, replacing relational correlation with indexed execution, adding caches, or constructing incremental and parallel evaluation plans.

**How Lean helps:** source semantics and target-plan semantics can be related explicitly. Compiler or optimizer passes can carry preservation theorems, and multi-pass pipelines can compose those results. A simple reference evaluator provides an independent specification against which a faster plan is compared. Certificates can keep the large generator outside the trusted core.

**Limit:** code generation is justified only after a concrete target and consumer exist. A compiler implemented in Lean is not automatically verified; the relevant translation and target-runtime assumptions still need proofs or qualification.

## 5. Analyze

**What it enables:** type, scale, path, and scope checking; dependency and cycle analysis; satisfiability; always- or never-firing detection; equivalence, implication, redundancy, overlap, conflict, read/write footprint, partial-validation relevance, and change-impact analysis.

**How Lean helps:** analyses can be defined against the same semantics used for execution, so their claims have precise meanings. A sound analysis theorem can state exactly what a successful answer guarantees and which residual errors remain. When a universal answer is unavailable, the executable semantics can validate a concrete witness or counterexample. Checked non-laws prevent an analyzer from relying on attractive but false algebraic assumptions.

**Current narrow examples:** the internal checked-flat pilot recognizes only the exact root shapes `FieldFilled(f) And FieldNotFilled(f)` and its reverse, returns a proof-bearing witness, and proves that the error condition can never fire. The addressed numeric-operation probe separately reports one checked computation's ordered expression-operand dependencies, prior-target-state classification read, and written target, proves every operand differs from the target, and retains the bounded fingerprint used to detect conversion, root-wrapper, rounding, and direct-field/literal/operand-local-wrapper extremum changes. The checked scalar numeric-table projection derives every alternative guard and operation dependency against the validated model, including fixed group-count expansion; an isolated consumer used those exact lists to verify one labeled three-target cycle and one acyclic execution order. None is a recursive lint, general reachability procedure, command, protocol, or supported shipment. Their precise boundaries are recorded in the [implementation map](IMPLEMENTATION-MAP.md).

**Limit:** an analysis must state whether it is exact, sound but incomplete, complete but approximate in another direction, or merely a bounded search. “No counterexample found” is not a proof unless the searched domain is known to be complete.

## 6. Verify

**What it enables:** proving that validation success implies a business invariant, computations preserve ranges or conservation laws, two model versions are equivalent over an admitted domain, or a migration preserves accepted documents.

**How Lean helps:** business intent is stated independently of the evaluator, then related to the formal A12 semantics. A checked proof covers every modeled input satisfying its hypotheses, not just a test sample. The theorem statement exposes model, document, world, schedule, oracle, and supported-fragment assumptions that would otherwise remain implicit.

**Limit:** kernel compatibility alone cannot prove business correctness, because the kernel does not define the business intent. Conversely, a model-level proof is only as externally relevant as the A12 clauses and environmental assumptions on which it depends.

## 7. Synthesize

**What it enables:** generating valid or invalid documents, boundary data, minimal counterexamples, values that trigger a rule, minimal repairs, missing-case witnesses, refactoring counterexamples, or candidate rules satisfying a stated property.

**How Lean helps:** the executable semantics can check every produced witness. Search or generation may run in an ordinary fast external program; Lean need only validate the result or certificate. Formal relations define what counts as a repair, minimal change, satisfying document, or counterexample, avoiding a generator-specific interpretation of success.

**Limit:** checking a produced witness is usually easier than proving the generator complete or the repair globally minimal. Those stronger claims require their own bounded-domain argument, optimization proof, or certificate.

## 8. Qualify

**What it enables:** conformance suites for independent interpreters, Lean-versus-candidate differentials, retained kernel replay, kernel-version comparisons, property-based and fuzz testing, mutation sensitivity, regression generation, and third-party candidate qualification records.

**How Lean helps:** the same typed capability can generate normalized fixtures, expected observations, supported-fragment metadata, laws, non-laws, and valid-input profiles. The Lean reference supplies exact answers inside that profile. Mutation and counterexample exercises test whether the shipment actually transported important distinctions rather than merely enough examples to pass accidentally.

**Limit:** finite agreement qualifies only the executed inputs. It does not transfer Lean proofs to the candidate or create new kernel evidence. Kernel correspondence, internal theorem coverage, and downstream conformance remain separate claim classes.

## 9. Explain

**What it enables:** showing why a rule fired, was suppressed, or became unknown; tracing row selection and `$` correlation; explaining computation order, poison, clearing, or storage; presenting counterexamples; producing semantic change reports; and building checked tutorials, API documentation, or Verso presentations.

**How Lean helps:** an explanation can be a checked trace or certificate whose acceptance implies the corresponding evaluation or transformation judgment. User-facing examples can import live definitions and theorem names, so documentation becomes a regression consumer rather than a detached description. Exact evidence and support links show which parts are observed, proved, project-defined, or still open.

**Limit:** presentation remains a projection. Markdown, Verso, an IDE, or a trace viewer must not become a second hand-maintained semantics or imply that a friendly explanation proves external kernel correspondence.

## 10. Govern

**What it enables:** support manifests, compatibility identities, semantic versioning, kernel-version delta reports, model migration planning, release qualification, theorem/evidence trust reports, reproducible audits, and coordinated regeneration of affected consumer shipments.

**How Lean helps:** definitions, theorems, counterexamples, evidence projections, and generated consumer artifacts can be tied to explicit versions and digests. Explicitly maintained dependency information can identify which claims and shipments a semantic correction affects. Mechanical gates can reject stale fixtures, incomplete proof roots, unsupported fallthrough, or a release whose advertised capability is not research-closed.

**Limit:** formal provenance does not replace organizational approval, production security, platform qualification, or legal review. It makes the semantic part of those decisions precise and reproducible.

## Cross-category use case: a derived simplified language variant

**What it enables:** producing a smaller language from the full one—a reduced set of constructs that provably means the same thing on the fragment it covers, together with the mapping from full A12 into it. Consumers who cannot afford the whole surface get something implementable, analyzable, and teachable without re-deriving A12 semantics from prose.

**This is an output, not a boundary.** The theory continues to target 100% of the observable language; the variant is something the theory produces, and the full account remains its source. An unmodeled clause stays a debt in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) whether or not a variant omits it.

**How Lean helps:** the negative universal Core IL experiment showed that the useful source is not a new universal representation but the normalized family boundaries and their evaluator-agreement laws. A concrete variant needs a construct inventory with an admission predicate, a reduced evaluator, a desugaring, and a conformance suite for exactly the families whose existing normalized forms support the required agreement. The live six-condition reopening policy is in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#representation-policy-for-derived-consumers), and the failed universal route is preserved in the [archived study](archived/SEMANTIC-CORE-IL-PROPOSAL.md).

**Limit:** a variant covers exactly the families with proved lowerings and must preserve every observation its contract names, including poison, unknown, structural failure, exact decimals, rounding stages, and authored order. Selecting its construct set remains a product decision for a concrete consumer.

## Turning a use case into a shipment

Before adopting any concrete tool, answer five questions:

1. What are the exact input and output artifacts?
2. Which source and target language versions and fragments are supported?
3. What observable relation is claimed: execution result, equivalence, refinement, sound analysis, checked witness, or something weaker?
4. What is rejected, approximated, trusted externally, or still unknown?
5. Which assurance class supports each claim: retained evidence, Lean theorem, certificate checker, or finite downstream qualification?

Those answers define the task profile. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) owns the stable semantics-factory and shipment model, [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) owns the canonical category taxonomy and proposed product progression, and [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) owns the detailed consumer contract and qualification playbooks.
