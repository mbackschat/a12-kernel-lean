# Semantic consumer and implementer guide

**Status:** stable contract for transporting this project's semantics into independent software. It defines what must be portable across implementations, what changes with the consumer's task, and what this project must provide before an evaluator, importer, refactoring tool, or other semantic capability is shipment-ready. Product adoption and production release require the additional gates in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) and [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md). Current capability status remains in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), the evaluator wire contract in [`PROTOCOL.md`](PROTOCOL.md), and immediate work in [`PLAN.md`](PLAN.md).

## Promise and boundary

An independent consumer implementer must not need access to the external kernel, the sibling a12-dmkits checkout, or undocumented maintainer knowledge for any capability that a shipment or release advertises as supported. If the supplied material does not determine an observable case and answering it requires fresh A12 research, that capability is not shipment-ready: the gap belongs in this semantics project, not in each downstream evaluator or tool.

This is a per-capability promise, not a claim that the entire A12 language has already been captured. Internal Lean work may precede consumer material while a semantic capsule is under development, but a shipment support declaration must admit only capabilities whose research-closure and task-appropriate cold-consumer gates below are complete. The existing evaluator development manifest predates this rule and is not by itself a shipment- or public-release-readiness claim.

Lean is the precision engine and executable backstop behind the shipment. It is not the primary onboarding language, a dependency that a downstream runtime must embed, or source code to transliterate. The consumer receives language-neutral rules or relations, normalized data, checked examples, evidence limits, and qualification tools; links to Lean declarations make the account auditable and answer exact questions when useful.

The short reader-facing explanation is in the top-level [`README.md`](../README.md#how-knowledge-travels-to-other-software). In the precise model, this repository is the **semantics factory**, a **semantic shipment** is a versioned purpose-specific projection, and an evaluator, importer, refactoring tool, or other independent program is the **consumer**. Consumer feedback returns here; a semantic correction creates a new shipment identity instead of private downstream behavior.

## Responsibility split

| Role | Responsibility |
|---|---|
| Semantics maintainer | Centralize and maintain ambiguous-behavior research through the clean-room evidence process; state the language-neutral rule; implement it in Lean; retain evidence; prove useful laws; preserve counterexamples; publish the shipment material |
| Independent consumer implementer | Implement only the advertised task capability; preserve its distinctions and claimed relation; run the supplied fixtures, properties, differentials, transformation checks, or conformance tools; report underspecified cases instead of guessing |
| Lean theory, reference, or checker | Give an exact executable answer or checked relation inside the admitted fragment; reject unsupported forms; expose stable support metadata and diagnostics; check internal universal laws or certificates |
| Retained evidence | Anchor named observable choices to kernel 30.8.1 without making the kernel a dependency or claiming universal equivalence |

The a12-dmkits interpreter remains a clean-room triangulation peer and the kernel remains the external behavioral authority for A12 behavior. Neither becomes required reading or a runtime dependency for the independent consumer. A shipment that also models an external source language, such as a selected JSON Schema dialect, must name that source language's separate authority and must not confuse source-semantics evidence with target A12 kernel evidence.

## What stays portable and what changes

Three kinds of artifact must remain separate:

| Artifact | What it contains | What it must not do |
|---|---|---|
| **Semantic shipment** | Common A12 foundation, exact capability projection, task contract, evidence and assurance limits, examples, laws/non-laws, and task-level qualification requirements | Depend on one consumer's source layout, toolchain, packaging, or test logs |
| **Implementation profile** | Idiomatic representation guidance, host-boundary choices, process/library integration, packaging, resource policy, and adapters for a language/runtime | Change the shipment's normative semantics or silently choose an unresolved host behavior |
| **Candidate qualification record** | Exact shipment digest, candidate revision and toolchain, commands, executed fixtures/properties/differentials or preservation-oriented checks, optional mutations, raw results, and assurance verdict | Become new A12 semantics, universal proof, or kernel evidence |

A Rust and Python evaluator should consume the same evaluator shipment, but they may have different implementation profiles, deployment policies, optimizations, and qualification records. A JSON Schema importer or rule-refactoring tool needs a different task profile because it promises a mapping or transformation rather than evaluation.

## Portable shipment contents

Every shipment-ready consumer capability contains:

1. **Identity and scope:** stable capability identifier, source and target versions, A12 semantics and kernel-behavior versions where applicable, task-interface and support-declaration versions where applicable, owning `§n` clauses, accepted forms, and explicit exclusions.
2. **Language-neutral model:** source, target, checked-state, environment, and observable result types with every semantically relevant distinction named.
3. **Task contract:** an original semantic decision procedure, mapping, transformation relation, or staged decision table written from the distilled behavior, never a kernel source expression translated into another syntax.
4. **Ordinary and separating scenarios:** minimal controls, boundary cases, empty and malformed cases, order-sensitive cases, and the nearest tempting but false generalizations.
5. **Runnable fixtures:** normalized inputs and expected observable outputs, diagnostics, or before/after relations exercised by the same task-level gate users run.
6. **Assurance and evidence account:** classify each claim as source-authority knowledge, retained A12 kernel evidence, Lean definition/theorem/counterexample, project-defined task contract, certificate-checked result, or finite consumer qualification; state the projection actually supported and every unobserved dimension that must not be inferred.
7. **Law and non-law index:** language-neutral property statements with exact hypotheses, observable result domain, generator guidance, and stated non-applicability cases, paired with checked counterexamples that bound those properties; each entry links to the exact Lean theorem, checker/transformation declaration, or conformance declaration for audit rather than requiring the implementer to interpret Lean, and finite tables or law vectors have a generated machine-readable companion when downstream transcription would otherwise become a new error source.
8. **Worked trace:** a readable staged explanation of at least one non-trivial case, distinguishing normative semantic steps from evidence observations and implementation freedom.
9. **Reference/checker and qualification tools:** the applicable reference or checker invocation, support query, fixture runner, differential or preservation-oriented workflow, deterministic-output rules, expected diagnostics, and a language-neutral conformance or transformation dataset linked to the relevant maintained semantics and evidence.
10. **Escalation rule:** how an implementer reports a missing distinction or disagreement and how a corrected, newly evidenced shipment version reaches every consumer.
11. **Artifact-role inventory:** every exported file is labeled as normative semantics, task interface, executable fixture, provenance-only evidence, qualification material, or source-maintainer material, so audit inputs cannot be mistaken for implementation instructions and maintainer mechanics cannot obscure the downstream path.

A link to a Lean definition alone is not a task contract, a corpus count is not an evidence account, and a list of expected outputs without the separating reason is not a consumer guide. The downstream path should present one concise normative shipment first; Lean theorem links, Lake commands, generation internals, and other source-maintainer mechanics belong in a clearly labeled appendix or maintainer surface rather than competing with the consumer sequence.

An implementation profile must make every relevant host choice visible, including exact-number representation, Unicode/regex facilities, clocks and external oracles, limits, failure behavior, process or library integration, and packaging. A candidate qualification record then pins the shipment and implementation revision, toolchain, executed commands, task-appropriate fixture/property/differential or preservation-oriented results, unresolved questions, and final assurance class. If mutation sensitivity is part of that qualification, each transient mutation additionally retains its prediction, exact patch or semantic change, command and raw result, restoration check, and final natural-source digest; mutation mechanics are not mandatory semantics for every task profile.

For an evaluator shipment produced from retained evidence, build the machine-readable capability descriptor and checked projection-to-protocol bridge before the first downstream implementation. The bridge must derive normalized requests from typed replay inputs, prove operationally that the public decoder reaches the same checked input, run the public evaluator, classify exactly what the external observation supports, and generate or reject drift in the fixtures and conformance suite. Importer and refactoring shipments need the analogous checked source-to-target projection and generated qualification artifacts before the first downstream tool. This sequencing tests a repeatable shipment-production process rather than the quality of one manually assembled document.

## Task profiles

The product taxonomy in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#general-consumer-task-categories) covers Execute, Translate, Transform, Compile, Analyze, Verify, Synthesize, Qualify, Explain, and Govern. The three profiles below are the first concrete shapes motivating this contract: an evaluator combines Execute and Qualify, JSON Schema import is Translate, and rule refactoring is Transform. Future profiles use the same portable-shipment, implementation-profile, qualification-record, and assurance-class separation rather than inheriting evaluator protocol machinery by default.

### Evaluator

An evaluator shipment promises an observable result for a normalized A12 model, rule, document, and world. It therefore needs the decision procedure, response protocol, support manifest, verdict and diagnostic fixtures, property/non-law index, retained evidence projection, Lean reference invocation, and black-box candidate differential. Its evidence account uses an explicit matrix separating externally established outcome and polarity, Lean-account hidden verdict and causal ordering, project-defined transport, and behavior that remains externally undistinguished. The existing flat and correlation kits are evaluator-shaped development shipments.

### JSON Schema importer

A JSON Schema shipment must select and pin a dialect, version, and closed keyword subset; “JSON Schema” alone is not a capability identity. It must state whether it imports declarations, generates validation rules, preserves accepted instances, carries annotations/defaults, or promises an explicitly named combination. Its source model and satisfaction semantics are independent formal objects, connected to the supported A12 target by an explicit JSON-instance-to-Document relation. Raw parsing and reference resolution must either have a checked soundness bridge or be declared as a pre-parsed source-AST trust boundary.

The shipment must declare the treatment of absence versus `null`, exact numbers, objects and repeatable arrays, requiredness, references and recursion, composition and alternatives, additional or unevaluated content, regular expressions, Unicode, formats, defaults, and annotations wherever the admitted subset reaches them. Unsupported or lossy constructs fail closed or carry an explicit approximation result; they are never silently discarded. Finite qualification exercises source parsing/resolution, target well-formedness, expected models and diagnostics, and cases in each claimed preservation direction. Universal satisfaction preservation is established only by a theorem-covered transformation or outputs accepted by a proved certificate checker. Source-validator differentials, the transformation proof, finite importer qualification, and retained A12 kernel evidence remain separate assurances.

### Rule refactoring

A refactoring shipment names the checked source and target A12 fragments, transformation, preconditions, and exact observation relation. Both source and result must elaborate against their declared models. “Equivalent” means preservation over every relevant supported input and over the full declared observation projection; it cannot mean only that a few fixtures produce the same Boolean truth.

Where the fragment exposes them, the preservation domain includes unknown or poison, polarity, message identity/location/order, computation deltas, clearing, stored form, read/write footprints, and observable order. A one-directional refinement, validation-only preservation, or deliberately normalized presentation must use that narrower relation name. The shipment carries the nearest checked counterexample outside its preconditions and, when transformation runs outside trusted Lean code, may require a certificate checked by a smaller trusted verifier. Finite before/after qualification does not establish universal equivalence without the theorem or certificate bridge.

## Research-closure gate

A consumer capability is research-closed only when:

- every observable branch, mapping choice, or transformation case needed by the task profile is documented or explicitly rejected;
- unknown behavior is marked unknown and cannot silently inherit a nearby type or operator default;
- operator behavior is resolved at every applicable kind, operand-position, context, field-role, phase, row-eligibility, iteration/correlation, and output-polarity layer;
- every claimed kernel-semantic choice has retained external evidence; `external evidence pending` explicitly means the capability is not research-closed and remains out of the shipment-ready set and therefore any release-supported set;
- any external source language has a separately pinned authority, modeled subset, and evidence boundary rather than borrowing credibility from the A12 kernel evidence;
- transport, mapping, diagnostic, resource-limit, approximation, and other project-defined choices are labeled as normative compatibility decisions, justified independently, and tested rather than misrepresented as kernel observations;
- the consumer-facing task contract, fixtures, evidence account, Lean definitions, theorem/non-law boundary, and support declarations describe the same source and target fragments and the same observable relation;
- no step tells the downstream consumer to inspect the kernel or reconstruct A12 semantics from a12-dmkits source.

The high-complexity planning matrix in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#planning-high-complexity-operator-families) is the preparation method for A12 clauses. Research closure packages its result for reuse by every independent consumer; an importer additionally closes its selected source-language choices, and a refactoring tool closes its transformation preconditions and observation relation.

## Cold-consumer gate

Before a capability is shipment-ready, test it with a developer or isolated coding agent that has no kernel access, no sibling checkout, and no undocumented conversation context. Give it only the proposed shipment and a normal toolchain. It must be able to:

1. identify the exact supported and unsupported surface without guessing;
2. implement the normalized representation and task contract idiomatically rather than copying Lean syntax;
3. reproduce every canonical output and required diagnostic or transformation relation;
4. run the supplied language-neutral properties, preservation checks, and checked non-laws with their stated hypotheses or record a shipment-declared non-applicability;
5. explain the worked non-trivial case and the separate limits of kernel evidence, source-language evidence, Lean proofs, and finite consumer testing;
6. diagnose an injected divergence at the first applicable decoding, elaboration, evaluation, mapping, transformation, projection, or encoding boundary;
7. produce a candidate qualification record naming the exact shipment, versions, evidence identities, tool revision, executed checks, and assurance class.

Any A12 semantic question that forces the cold consumer to inspect the kernel is a shipment defect. Record the question, close it through this project's evidence workflow, and repeat the test; do not accept successful guesswork as documentation adequacy. An importer exercise may consult only the source-language authority explicitly allowed by its shipment; if even that is intended to be research-closed, the allowed source material must be bundled and digest-pinned as well.

Retain the cold-consumer section of the candidate qualification record beside the shipment or in an explicitly linked location. “Reviewed by another consumer” without the supplied artifact identity, isolation boundary, executable results, seeded disagreement, and unresolved-question log does not satisfy the gate.

## Lessons from the first cold implementation

Under its recorded isolation boundary, the first Rust run for [`flat-validation-empty-logic-v1`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-and-qualification-outcome-2026-07-1415) reported recovering an idiomatic typed evaluator from the hash-locked language-neutral model, staged decision procedure, complete verdict tables, worked traces, separating fixtures, exclusions, and evidence classifications without consulting Lean source, the kernel, or a12-dmkits. This validates the basic evaluator-shipment shape for one finite capability while keeping isolation an attested experimental condition. Lean theorem names and source paths remain source-maintainer audit links; the isolated implementer did not need them to write the evaluator. Repetition between the model, algorithm, traces, laws, and non-laws helped the cold reader, while exact normative rules repeated verbatim increased navigation cost; retain the distinct explanatory views but generate cross-references from one canonical rule statement.

The run also tightens the process contract. Freeze and identify the first naturally green implementation before introducing the Lean executable. Keep the downstream report, README, and agent instructions synchronized with the lifecycle stage so a later session is not told that a now-green evaluator is still an intentionally red scaffold. Inventory every consulted file, use portable repository-relative locations such as `.`, and distinguish a reproducible command from an attested historical action.

A seeded-divergence gate must have one unambiguous required mutation set shared by the source shipment and downstream prompt. Predict each affected case before mutation, inject one defect at a time, preserve the exact patch and raw command streams, restore the frozen natural implementation, and rerun the complete gate. A report that exercises only a representative subset must name that subset rather than claiming the shipment's complete mutation qualification.

The first post-cold qualification implementation adds a reusable packet pattern. Export one closed capability packet that binds the semantics-project revision, frozen candidate revision and build-input closure, capability identity, generated mutation plan, canonical fixture-driven observer, observer-only baseline patch, one exact patch per mutation, expected observations, execution profile, ordered commands, and every payload byte by SHA-256. The observer must consume the shipment's canonical suite and request fixtures rather than rebuild requests in a second harness. This keeps the executable qualification projection downstream of the same maintained capability material that the implementer used.

Predictions and observations are different data. The mutation plan states the predicted case and algebra changes; the result record must copy the parsed case and algebra values from the observer's actual stdout. A strict checker then binds those recorded values back to the raw log bytes, compares the actual observation with the packet prediction, validates exact command order and status, rejects missing, additional, reordered, reused, unsafe, or oversized artifacts, and checks the packet-pinned path-and-byte inventory after every restoration. Digest consistency cannot by itself prove that an external session executed the recorded commands, so the record's assurance class must say how it was produced.

Use `sourceExecutedReplay` only when a source-owned runner actually executed the packet commands and captured the returned streams. Use `isolatedSessionAttestation` for a record returned by a separate consumer session: the checker may establish that the packet, record, logs, observations, and restoration inventories are digest-bound and internally consistent, but it must not relabel that consistency result as independently witnessed execution. Cedar supplies the useful structural precedent of separating specification, validation, theorems, differential tests, unit tests, and FFI; the two assurance classes and digest-bound external-attestation model are A12-specific adaptations required by this project's clean-room and independent-shipment boundaries.

Validate a returned record with the checker from the packet's exact source revision. A newer source checkout—even one changed only in documentation—must not silently reconstruct and approve an older source-owned packet; use a disposable checkout at the pinned revision instead. Candidate history may advance beyond the packet's base only through commits that leave the classified build-input closure unchanged, such as retaining the qualification record outside that closure.

The broader operation manifest was useful context but increased the risk that the implementer would infer support beyond the capability. Each future evaluator shipment should therefore provide a closed capability-specific positive generation profile with explicit exclusions, generated from the same typed descriptor when practical, while retaining the wider manifest only as explicitly non-expanding context. Rejected inputs belong in that profile only when the compared rejection projection is already normative; the profile must not imply exact negative-diagnostic compatibility that the capability excludes.

## Evaluator implementation playbook

1. Query the reference manifest and select one closed capability; pin its complete compatibility tuple.
2. Read the evaluator shipment before the Lean source. Map its language-neutral sum types and staged boundaries to idiomatic language constructs, preserving raw-versus-checked, inner-versus-outer, empty-versus-malformed, phase, order, and provenance distinctions.
3. Implement the smallest admitted core and fail closed on every excluded shape. Do not add convenience behavior for a nearby unsupported operator.
4. Run the canonical fixtures as the first red/green loop, then implement the language-neutral law index as property tests with its supplied hypotheses and generators and preserve the non-law index as fixed regressions.
5. Define a versioned or digest-pinned, machine-readable generation profile before differential testing, with deterministic enumeration or a recorded seed and exact reference/candidate revisions. Generate valid in-profile requests; add rejected cases only when their compared rejection projection is already normative. Execute the cases through the independent implementation and the Lean reference, retain minimized counterexamples, compare only the observable projection promised by the shipment, and label the results as Lean-account conformance rather than new kernel evidence.
6. Replay the shipment's language-neutral conformance dataset through both implementations using its documented command or adapter. That dataset must be derived from and linked to the retained evidence rather than requiring the downstream implementation to parse Lean-internal evidence schemas. Agreement with the Lean reference does not replace the external evidence anchor, and finite evidence does not inherit Lean's proofs into the independent code.
7. Publish the evaluator candidate qualification record with implementation revision, capability and version tuple, manifest and evidence digests, fixture result, differential strategy, property set, assurance class, and deliberate exclusions.
8. Expand only by consuming the next research-closed shipment. A downstream implementation must not become a private second semantics-of-record.

## Importer playbook

1. Pin the exact source dialect/subset and target A12 capability; state whether the claim covers structural import, generated validation, satisfaction preservation, annotations/defaults, or another named projection.
2. Define closed source and target support predicates, source resolution environment, source-instance-to-A12-Document relation, and fail-closed diagnostic domain before translating examples.
3. Implement checked lowering that returns either a well-formed supported A12 result or an explicit rejection/approximation; never silently drop a source construct.
4. Run ordinary, boundary, lossiness, unsupported, and nearest-counterexample fixtures through the independent importer and the task reference or checker.
5. Exercise finite cases in every claimed preservation direction and identify the theorem-covered transformation or proved certificate checker, if any, that establishes a universal result; keep source-validator differentials, Lean transformation results, finite importer qualification, and target-kernel evidence separately identified.
6. Publish the importer candidate qualification record pinning source dialect, shipment, target semantics, implementation revision, fixtures/properties, claimed relation, assurance class, and exclusions.

## Rule-refactoring playbook

1. Pin the source and target A12 fragments, model assumptions, transformation, preconditions, and exact observation projection.
2. Require checked elaboration of both sides and fail closed when a precondition or supported-fragment boundary cannot be established.
3. For a universal equivalence/refinement claim, provide a theorem-covered transformation or proved certificate checker; otherwise report only finite qualification over the executed inputs. Include the nearest counterexample outside the claimed hypotheses and preserve all in-scope polarity, unknown/poison, message, computation, storage, and ordering observations.
4. If the transformer itself is outside the trusted Lean core, emit a small certificate or normalized before/after obligation that a separately trusted checker can validate when this is economically justified.
5. Qualify composition explicitly when several refactorings are chained; individual pass claims do not automatically establish a stronger pipeline claim.
6. Publish the refactoring candidate qualification record pinning the shipment, transformation implementation, certificate/checker if any, executed cases, theorem or property boundary, assurance class, and deliberate exclusions.

## Disagreement and missing-semantics protocol

When an independent consumer and its reference or checker disagree, first preserve the complete normalized input and classify the first divergent boundary: source decoding/resolution, static elaboration, formal checking, row or path environment, semantic evaluation, mapping/transformation, observable projection, or response encoding. Do not immediately change an expected result.

If the shipment already determines the case, fix the consumer that violates it. If the documents, fixtures, Lean behavior, transformation claim, and relevant evidence disagree, open a semantics or shipment defect here and suspend the affected compatibility claim. If an A12 case is not determined, mark the capability incomplete; a semantics maintainer performs any necessary kernel research through the external a12-dmkits adapter, retains a portable observation, updates the language-neutral rule and Lean capsule, and releases a new version. If an external source-language case is not determined, resolve it against that profile's named authority and update the source model separately. Downstream repositories consume the versioned resolution rather than repeating the archaeology.

The kernel observation remains authoritative when it conflicts with the local theory. The correction must update the full chain—finding or source trail, evidence, Lean behavior, counterexample or law, shipment material, fixture, support declaration, and compatibility version—rather than patching one consumer.

## Complexity lens for implementers

The default implementation question is not “which operator is this?” but “which consuming clause is active?” For empty or invalid input in particular, evaluate the documented layers in order:

```text
field-kind baseline
  → operator and operand-position override
  → enclosing expression or storage context
  → field role and generated formal checks
  → validation or computation phase
  → row eligibility and iteration/correlation environment
  → value, unknown, poison, clearing, firing, and polarity projection
```

This layering prevents a type-only dispatch table from erasing the exact distinctions catalogued in [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function). Each evaluator shipment should omit irrelevant layers explicitly rather than leaving the implementer to wonder whether they were forgotten.

## Assurance boundary

Lean proofs establish universal consequences of the Lean definitions over their hypotheses. They do not automatically prove an independent Rust, Python, Kotlin, or TypeScript consumer correct. Canonical fixtures, differential testing, and transformation tests establish conformance only over executed inputs; a preservation theorem applies only to its modeled transformation and hypotheses; retained evidence establishes kernel correspondence only over its recorded projection. The candidate qualification record must keep those claims separate.

A later production consumer may justify stronger integration such as checked evaluation certificates, a verified translation, or a refinement proof for an optimized implementation. Those are additional assurance products, not prerequisites for the initial oracle-and-conformance playbook.

## Current tools and limits

The current executable tools and shipped development materials are evaluator-shaped. The reference executable and manifest are documented in [`PROTOCOL.md`](PROTOCOL.md); runnable inputs live under [`../examples/reference-cli/`](../examples/reference-cli/); retained observations and their limits are in [`EVIDENCE.md`](EVIDENCE.md); theorem, counterexample, and trust methodology is in [`TESTING.md`](TESTING.md). [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) is the first development cold-consumer exercise, backed by its generated [`capability descriptor`](../reference/flat-validation-empty-logic-v1.capability.json), [`conformance suite`](../reference/flat-validation-empty-logic-v1.conformance.json), and [evidence-derived fixtures](../examples/reference-cli/flat-evidence/). [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) remains the higher-complexity captured-outer shipment, backed by [`single-group-correlation-v1.conformance.json`](../reference/single-group-correlation-v1.conformance.json). No JSON Schema importer or rule-refactoring shipment is currently implemented; their task profiles are forward design constraints, not advertised support. The basic flat-spike interaction is:

```sh
lake exe a12-kernel-reference --manifest
lake exe syncFlatHandover --check
lake exe a12-kernel-reference < examples/reference-cli/flat-evidence/number-empty-equals-zero-content.request.json
lake exe checkReferenceProcess
lake exe checkBoundedProcess
lake exe checkGeneratedDifferential --self-test
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v1.conformance.json
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/flat-validation-empty-logic-v1.conformance.json
```

`lake exe syncFlatHandover --check` is the non-writing drift gate. After an intentional change to the typed capability or one of its owned inputs, `lake exe syncFlatHandover --write` regenerates the flat descriptor, suite, fixtures, and source-maintainer mutation plan; review the result and rerun `--check`. The [`flat kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) owns the exact case-level external-versus-Lean response classification, cold outcome, and qualification state. Generated testing metadata never expands the retained evidence boundary.

The flat packet/checker workflow is intentionally a separate source-maintainer qualification surface:

```sh
lake build checkMutationQualification
lake exe checkMutationQualification --self-test --candidate-repo ../a12-kernel-rust-spike
lake exe checkMutationQualification --export --candidate-repo ../a12-kernel-rust-spike --output .lake/qualification/flat-validation-empty-logic-v1-rust-v1
lake exe checkMutationQualification --verify-packet --candidate-repo ../a12-kernel-rust-spike --packet .lake/qualification/flat-validation-empty-logic-v1-rust-v1/PACKET.json
lake exe checkMutationQualification --check --candidate-repo ../a12-kernel-rust-spike --packet .lake/qualification/flat-validation-empty-logic-v1-rust-v1/PACKET.json --result <returned-result>/RESULT.json
```

The self-test is a `sourceExecutedReplay`; `--check` deliberately expects an `isolatedSessionAttestation`. Both are finite mutation-sensitivity qualification for the pinned candidate and capability, not kernel evidence, proof transfer, or general evaluator conformance.

The flat and correlation operations are narrow development references, not a complete A12 interpreter kit. Their exact readiness and integrity gaps belong in the owning [flat](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation](IMPLEMENTER-KIT-CORRELATION.md) kits. Generically, the candidate runner validates the selected suite's closed compatibility identity, finite evidence scope, case classifications, referenced evidence, deterministic process behavior, and structural JSON results; agreement establishes only that suite's observable cases. The reference-process gate runs each suite's integrity checks and Lean-reference control. `checkCandidateConformance` and the mutation replay still buffer child output without a wall-clock timeout, while the separate generated-differential lane now enforces streamed stdout/stderr caps, process and cleanup deadlines, aggregate input/output/elapsed/result budgets, exact clean revisions, and executable digests for a closed 52-case positive profile. That boundary is cooperative macOS/Linux process control for same-credential candidates, not an untrusted-code sandbox. Batch or long-running process architecture still requires measurement and a separate protocol decision; the [`flat kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#post-cold-generated-differential) owns the pending pinned-run state.
