# Consumer probes and what this Lean semantics can enable

This is the user-facing map of bounded consumer probes and possible later products built from `a12-kernel-lean`. It explains the potential of the project, not the set of tools implemented today. The current executable surface remains the narrow evaluator described in the top-level [`README.md`](../README.md); current clause-level support is recorded in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

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

## Current probe record: generated computation alternatives

The first post-simplification cross-category probe used the checked two-alternative literal-Number capsule at revision `b73d11e`. Two isolated read-only consumers received only project-local spec, Lean, status, and general task-contract files: an evaluator reader reconstructed the first-match selector and all-alternatives generated-rule shape, while a refactoring reader independently identified the shadowed-row deletion and reordering counterexamples. Neither could consult the kernel, a12-dmkits, the web, Git history, or prior discussion. Translate and Analyze/Synthesize were reviewed as task-profile probes rather than cold implementations.

| Category | What the probe established | What remains before a real consumer |
|---|---|---|
| Execute | The exact selector, generated condition shape, central overlap outcome, controls, phase split, polarity, scale checks, and fail-closed cases can be recovered from the current artifacts | A standalone implementer still has to chase imported Lean definitions for model validation, cell observation, scale admission, flat verdict/polarity, and assembly; there is no language-neutral capability packet, normalized fixture set, public operation, or retained external observation for this fragment |
| Translate | The target obligations are explicit enough to reject a lossy mapping: order, every guard, both literal value and authored scale, target identity, code, severity, and text cannot be collapsed | No pinned JSON Schema dialect/keyword or other source construct was supplied whose source meaning includes this ordered derived-value behavior. A useful first importer should instead select a source subset with an independently defined satisfaction relation and an A12 target whose field constraints are already first-class |
| Transform | Deleting a later row merely because first-match computation shadows it is demonstrably unsafe; reordering different overlapping rows changes computation, and replacing all-alternatives validation with selected-result validation loses an error | No general transformation, preservation relation, mutual-exclusivity/equal-result certificate, checker, or theorem exists. Safety must preserve elaboration, exact selection/no-match/poison, and exact generated message outcome, with wider computation state added when admitted |
| Compile | A target compiler must preserve two consumers of one authored table rather than compile one shared selector | No target language semantics, generated plan, selection-to-target integration, or preservation theorem exists |
| Analyze | Guard overlap alone is not a defect: the equal-result control is silent, while overlap with disagreeing operation results is the useful table-consistency question | The current direct-presence fragment could support a small solver-free disagreement analysis, but no finite checked query context or analyzer theorem exists. This does not justify adopting an SMT dependency |
| Verify | The trusted root establishes first-row selection, exact two-branch construction, and empty-target suppression | It does not prove a computation-to-generated-validation agreement theorem. Such a theorem needs explicit phase-compatible guard, overlap/result, and observation hypotheses |
| Synthesize | The checked central case is already a concrete witness that two guards can hold, computation can select the first result, and generated validation can still fire | There is no general witness generator, minimality claim, finite transport, or replay contract |
| Qualify | The finite cases distinguish unequal/equal overlap, nonholding rows, `And`, phase behavior, polarity, both scale positions, kinds, and repeatability; an `And → Or` source mutation failed exactly at the intended case | No machine-readable downstream suite or external kernel observation exists for this fragment; finite internal cases transfer no proof to a candidate |
| Explain | The counterexample gives a compact trace: select `1`, store `1`, retain the holding row expecting `2`, then fire at the target | A language-neutral trace and terminology layer is still needed; forcing users to infer error precedence and imported primitives from Lean would make Lean fluency an accidental onboarding dependency |
| Govern | The fragment, exclusions, source basis, theorem boundary, evidence status, and affected a12-dmkits reconciliation entry are identifiable | It has no shipment identity, support-manifest entry, release claim, or regeneration dependency graph |

The overall verdict is positive for semantic reuse and negative for shipment readiness. The current material prevents consumers from repeating the hardest kernel insight, but a standalone evaluator would still need a purpose-specific language-neutral projection of its imported semantic dependencies. Refactoring and analysis already receive valuable counterexamples without new infrastructure. The Translate result is a boundary correction, not a failed project goal: it prevents a JSON importer from inventing source meaning. The sharper computation-table consistency probe remains within **Analyze** and **Explain**, so this exercise discovered no eleventh task category. The same categories will be probed again after the cross-level-correlation risk capsule to test whether the approach survives nested addressing and captured environments.

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

**Limit:** equal Boolean truth is often insufficient. Depending on the fragment, preservation may also need unknown or poison, message polarity and location, computation deltas, clearing, stored form, read footprints, and observable order.

## 4. Compile

**What it enables:** generating specialized evaluators, compiling rules to Rust, Kotlin, JavaScript, WASM, SQL, or another target, replacing relational correlation with indexed execution, adding caches, or constructing incremental and parallel evaluation plans.

**How Lean helps:** source semantics and target-plan semantics can be related explicitly. Compiler or optimizer passes can carry preservation theorems, and multi-pass pipelines can compose those results. A simple reference evaluator provides an independent specification against which a faster plan is compared. Certificates can keep the large generator outside the trusted core.

**Limit:** code generation is justified only after a concrete target and consumer exist. A compiler implemented in Lean is not automatically verified; the relevant translation and target-runtime assumptions still need proofs or qualification.

## 5. Analyze

**What it enables:** type, scale, path, and scope checking; dependency and cycle analysis; satisfiability; always- or never-firing detection; equivalence, implication, redundancy, overlap, conflict, read/write footprint, partial-validation relevance, and change-impact analysis.

**How Lean helps:** analyses can be defined against the same semantics used for execution, so their claims have precise meanings. A sound analysis theorem can state exactly what a successful answer guarantees and which residual errors remain. When a universal answer is unavailable, the executable semantics can validate a concrete witness or counterexample. Checked non-laws prevent an analyzer from relying on attractive but false algebraic assumptions.

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

## Turning a use case into a shipment

Before adopting any concrete tool, answer five questions:

1. What are the exact input and output artifacts?
2. Which source and target language versions and fragments are supported?
3. What observable relation is claimed: execution result, equivalence, refinement, sound analysis, checked witness, or something weaker?
4. What is rejected, approximated, trusted externally, or still unknown?
5. Which assurance class supports each claim: retained evidence, Lean theorem, certificate checker, or finite downstream qualification?

Those answers define the task profile. [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) owns the stable semantics-factory and shipment model, [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) owns the canonical category taxonomy and proposed product progression, and [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) owns the detailed consumer contract and qualification playbooks.
