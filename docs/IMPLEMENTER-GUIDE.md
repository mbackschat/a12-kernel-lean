# Independent interpreter implementer guide

**Status:** stable handover contract for independent interpreter work. It defines what this project must provide before a semantic capability is release-ready for Rust, Kotlin, TypeScript, or another implementation language. Current capability status remains in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), the wire contract in [`PROTOCOL.md`](PROTOCOL.md), and immediate handover work in [`PLAN.md`](PLAN.md).

## Promise and boundary

An independent implementer must not need access to the external kernel, the sibling a12-dmkits checkout, or undocumented maintainer knowledge for any capability that a release advertises as supported. If the released material does not determine an observable case and answering it requires fresh kernel research, that capability is not handover-ready: the gap belongs in this semantics project, not in each downstream interpreter.

This is a per-capability promise, not a claim that the entire A12 language has already been captured. Internal Lean work may precede handover material while a capsule is under development, but a release supported-fragment manifest must admit only capabilities whose research-closure and cold-implementer gates below are complete. The existing development manifest predates this rule and is not by itself a public-release readiness claim.

Lean is the precision engine and executable backstop behind the handover. It is not the primary onboarding language, a dependency that the downstream runtime must embed, or source code to transliterate. The implementer consumes language-neutral rules, normalized data, checked examples, evidence limits, and tools; links to Lean declarations make the account auditable and answer exact questions when useful.

## Responsibility split

| Role | Responsibility |
|---|---|
| Semantics maintainer | Research ambiguous behavior once through the clean-room evidence process; state the language-neutral rule; implement it in Lean; retain evidence; prove useful laws; preserve counterexamples; publish the handover material |
| Independent implementer | Implement only the advertised normalized capability; preserve its distinctions; run the supplied fixtures, properties, differentials, and conformance tools; report underspecified cases instead of guessing |
| Lean reference | Give an exact executable answer inside the admitted fragment; reject unsupported forms; expose stable support metadata and diagnostics; check internal universal laws |
| Retained evidence | Anchor named observable choices to kernel 30.8.1 without making the kernel a dependency or claiming universal equivalence |

The a12-dmkits interpreter remains a clean-room triangulation peer and the kernel remains the external behavioral authority. Neither becomes required reading or a runtime dependency for the independent implementer.

## Handover unit: the implementation capsule

Every release-ready semantic capability must hand over one navigable implementation capsule containing:

1. **Identity and scope:** stable capability identifier, semantics version, kernel-behavior version, protocol and manifest versions, owning `§n` clauses, accepted forms, and explicit exclusions.
2. **Language-neutral model:** input, checked-state, environment, and observable result types with every semantically relevant distinction named.
3. **Decision procedure:** an original semantic algorithm or staged decision table written from the distilled behavior, never a kernel source expression translated into another syntax.
4. **Ordinary and separating scenarios:** minimal controls, boundary cases, empty and malformed cases, order-sensitive cases, and the nearest tempting but false generalizations.
5. **Runnable fixtures:** normalized requests and expected observable responses that are exercised by the same process gate users run.
6. **Evidence account:** the retained kernel cases supporting each claimed kernel-semantic choice, the projection actually compared, and every unobserved dimension that must not be inferred; an explicit matrix separates externally established outcome and polarity, Lean-account hidden verdict, Lean-account causal ordering, project-defined transport, and behavior that remains externally undistinguished.
7. **Law and non-law index:** language-neutral property statements with exact hypotheses, observable result domain, generator guidance, and stated non-applicability cases, paired with checked counterexamples that bound those properties; each entry links to the exact Lean theorem or conformance declaration for audit rather than requiring the implementer to interpret Lean, and finite tables or law vectors have a generated machine-readable companion when downstream transcription would otherwise become a new error source.
8. **Worked trace:** a readable staged explanation of at least one non-trivial case, distinguishing normative semantic steps from evidence observations and implementation freedom.
9. **Oracle and conformance tools:** the reference invocation, support-manifest query, fixture runner, differential workflow, deterministic-output rules, expected diagnostics, and a language-neutral conformance dataset or documented adapter from retained evidence into the normalized operation.
10. **Escalation rule:** how an implementer reports a missing distinction or disagreement and how a corrected, newly evidenced semantic release reaches every consumer.
11. **Cold-test record:** the exact kit/version and artifact digests supplied, isolation assumptions, downstream implementation revision and toolchain, conformance and property results, seeded disagreement and its classification, unresolved questions, and final handover verdict; transient mutations retain their predicted cases, exact patch or semantic change, command and raw result, restoration check, and final source digest.
12. **Artifact-role inventory:** every exported file is labeled as normative semantics, transport contract, executable fixture, provenance-only evidence, or source-maintainer material, so audit inputs cannot be mistaken for implementation instructions and maintainer mechanics cannot obscure the downstream path.

A link to a Lean definition alone is not a decision procedure, a corpus count is not an evidence account, and a list of expected outputs without the separating reason is not an implementation guide. The downstream path should present one concise normative capsule first; Lean theorem links, Lake commands, generation internals, and other source-maintainer mechanics belong in a clearly labeled appendix or maintainer surface rather than competing with the implementation sequence.

For a handover produced from retained evidence, build the machine-readable capability descriptor and checked projection-to-protocol bridge before the first downstream implementation. The bridge must derive normalized requests from typed replay inputs, prove operationally that the public decoder reaches the same checked input, run the public evaluator, classify exactly what the external observation supports, and generate or reject drift in the fixtures and conformance suite. This sequencing tests a repeatable handover-production process rather than the quality of one manually assembled document.

## Research-closure gate

A capability is research-closed only when:

- every observable branch needed by the normalized capability is documented or explicitly rejected;
- unknown behavior is marked unknown and cannot silently inherit a nearby type or operator default;
- operator behavior is resolved at every applicable kind, operand-position, context, field-role, phase, row-eligibility, iteration/correlation, and output-polarity layer;
- every claimed kernel-semantic choice has retained external evidence; `external evidence pending` explicitly means the capability is not research-closed and remains out of the released supported set;
- transport, diagnostic, resource-limit, and other project-defined protocol choices are labeled as normative compatibility decisions, justified independently, and process-tested rather than misrepresented as kernel observations;
- the implementer-facing algorithm, fixtures, evidence account, Lean definition, theorem/non-law boundary, and manifest describe the same fragment;
- no step tells the downstream implementer to inspect the kernel or reconstruct semantics from a12-dmkits source.

The high-complexity planning matrix in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#planning-high-complexity-operator-families) is the preparation method. Research closure packages its result for reuse by every independent interpreter.

## Cold-implementer gate

Before a capability is release-ready, test the handover with a developer or isolated coding agent that has no kernel access, no sibling checkout, and no undocumented conversation context. Give it only the proposed compatibility-kit artifacts and a normal language toolchain. It must be able to:

1. identify the exact supported and unsupported surface without guessing;
2. implement the normalized checked representation and decision procedure idiomatically rather than copying Lean syntax;
3. reproduce every canonical response and required diagnostic;
4. implement and run the supplied language-neutral properties with their stated generators, or record a capsule-declared non-applicability, and preserve the checked non-laws;
5. explain the worked non-trivial case and the limits of its kernel evidence;
6. diagnose an injected divergence as transport, elaboration, evaluation, or unspecified behavior;
7. produce a compatibility report naming the exact versions and evidence identity it passed.

Any semantic question that forces the cold implementer to inspect the kernel is a handover defect. Record the question, close it through this project's evidence workflow, and repeat the test; do not accept successful guesswork as documentation adequacy.

Retain the cold-test record beside the implementation capsule or in an explicitly linked compatibility-report location. “Reviewed by another implementer” without the supplied artifact identity, isolation boundary, executable results, seeded disagreement, and unresolved-question log does not satisfy the gate.

## Lessons from the first cold implementation

Under its recorded isolation boundary, the first Rust run for [`flat-validation-empty-logic-v1`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-outcome-2026-07-14) reported recovering an idiomatic typed evaluator from the hash-locked language-neutral model, staged decision procedure, complete verdict tables, worked traces, separating fixtures, exclusions, and evidence classifications without consulting Lean source, the kernel, or a12-dmkits. This validates the basic handover shape for one finite capability while keeping isolation an attested experimental condition. Lean theorem names and source paths remain source-maintainer audit links; the isolated implementer did not need them to write the evaluator. Repetition between the model, algorithm, traces, laws, and non-laws helped the cold reader, while exact normative rules repeated verbatim increased navigation cost; retain the distinct explanatory views but generate cross-references from one canonical rule statement.

The run also tightens the process contract. Freeze and identify the first naturally green implementation before introducing the Lean executable. Keep the downstream report, README, and agent instructions synchronized with the lifecycle stage so a later session is not told that a now-green evaluator is still an intentionally red scaffold. Inventory every consulted file, use portable repository-relative locations such as `.`, and distinguish a reproducible command from an attested historical action.

A seeded-divergence gate must have one unambiguous required mutation set shared by the source capsule and downstream prompt. Predict each affected case before mutation, inject one defect at a time, preserve the exact patch and command result or explicitly label the record as self-attested, restore the frozen natural implementation, and rerun the complete gate. A report that exercises only a representative subset must name that subset rather than claiming the capsule's complete mutation qualification.

The broader operation manifest was useful context but increased the risk that the implementer would infer support beyond the capability. Each future capsule should therefore provide a closed capability-specific positive generation profile with explicit exclusions, generated from the same typed descriptor when practical, while retaining the wider manifest only as explicitly non-expanding context. Rejected inputs belong in that profile only when the compared rejection projection is already normative; the profile must not imply exact negative-diagnostic compatibility that the capability excludes.

## Independent implementation playbook

1. Query the reference manifest and select one closed capability; pin its complete compatibility tuple.
2. Read the implementation capsule before the Lean source. Map its language-neutral sum types and staged boundaries to idiomatic language constructs, preserving raw-versus-checked, inner-versus-outer, empty-versus-malformed, phase, order, and provenance distinctions.
3. Implement the smallest admitted core and fail closed on every excluded shape. Do not add convenience behavior for a nearby unsupported operator.
4. Run the canonical fixtures as the first red/green loop, then implement the language-neutral law index as property tests with its supplied hypotheses and generators and preserve the non-law index as fixed regressions.
5. Define a versioned or digest-pinned, machine-readable generation profile before differential testing, with deterministic enumeration or a recorded seed and exact reference/candidate revisions. Generate valid in-profile requests; add rejected cases only when their compared rejection projection is already normative. Execute the cases through the independent implementation and the Lean reference, retain minimized counterexamples, compare only the observable projection promised by the capsule, and label the results as Lean-account conformance rather than new kernel evidence.
6. Replay the capsule's language-neutral conformance dataset through both implementations using its documented command or adapter. That dataset must be derived from and linked to the retained evidence rather than requiring the downstream implementation to parse Lean-internal evidence schemas. Agreement with the Lean reference does not replace the external evidence anchor, and finite evidence does not inherit Lean's proofs into the independent code.
7. Publish a compatibility report with implementation revision, capability and version tuple, manifest and evidence digests, fixture result, differential strategy, property set, and deliberate exclusions.
8. Expand only by consuming the next research-closed capsule. A downstream implementation must not become a private second semantics-of-record.

## Disagreement and missing-semantics protocol

When the independent implementation and Lean disagree, first preserve the complete normalized input and classify the first divergent boundary: decoding, static elaboration, formal checking, row or path environment, semantic evaluation, observable projection, or response encoding. Do not immediately change an expected result.

If the handover already determines the case, fix the implementation that violates it. If the documents, fixtures, Lean behavior, and retained evidence disagree, open a semantics defect here and suspend the affected compatibility claim. If the case is not determined, mark the capability incomplete; a semantics maintainer performs any necessary kernel research through the external a12-dmkits adapter, retains a portable observation, updates the language-neutral rule and Lean capsule, and releases a new version. Downstream repositories consume that versioned resolution rather than repeating the archaeology.

The kernel observation remains authoritative when it conflicts with the local theory. The correction must update the full chain—finding or source trail, evidence, Lean behavior, counterexample or law, handover material, fixture, manifest, and compatibility version—rather than patching one consumer.

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

This layering prevents a type-only dispatch table from erasing the exact distinctions catalogued in [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function). Each implementation capsule should omit irrelevant layers explicitly rather than leaving the implementer to wonder whether they were forgotten.

## Assurance boundary

Lean proofs establish universal consequences of the Lean definitions over their hypotheses. They do not prove an independent Rust, Kotlin, or TypeScript implementation correct. Canonical fixtures and differential testing establish conformance only over executed inputs; retained evidence establishes correspondence only over its recorded projection. The compatibility report must keep those claims separate.

A later production consumer may justify stronger integration such as checked evaluation certificates, a verified translation, or a refinement proof for an optimized implementation. Those are additional assurance products, not prerequisites for the initial oracle-and-conformance playbook.

## Current tools and limits

The current reference executable and manifest are documented in [`PROTOCOL.md`](PROTOCOL.md); runnable inputs live under [`../examples/reference-cli/`](../examples/reference-cli/); retained observations and their limits are in [`EVIDENCE.md`](EVIDENCE.md); theorem, counterexample, and trust methodology is in [`TESTING.md`](TESTING.md). [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) is the first development cold-handover exercise, backed by its generated [`capability descriptor`](../reference/flat-validation-empty-logic-v1.capability.json), [`conformance suite`](../reference/flat-validation-empty-logic-v1.conformance.json), and [evidence-derived fixtures](../examples/reference-cli/flat-evidence/). [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) remains the higher-complexity captured-outer capsule, backed by [`single-group-correlation-v1.conformance.json`](../reference/single-group-correlation-v1.conformance.json). The basic flat-spike interaction is:

```sh
lake exe a12-kernel-reference --manifest
lake exe syncFlatHandover --check
lake exe a12-kernel-reference < examples/reference-cli/flat-evidence/number-empty-equals-zero-content.request.json
lake exe checkReferenceProcess
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v1.conformance.json
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/flat-validation-empty-logic-v1.conformance.json
```

`lake exe syncFlatHandover --check` is the non-writing drift gate. After an intentional change to the typed capability or one of its owned inputs, `lake exe syncFlatHandover --write` regenerates the flat descriptor, suite, fixtures, and source-maintainer [mutation qualification plan](../reference/flat-validation-empty-logic-v1.mutation-plan.json); review the result and rerun `--check`. The bridge classifies four fired cases as externally supporting exact final firing and polarity. For the four cases where the focused authored message is absent, external evidence supports only silence and the exact `NotFired` or `Unknown` response is explicitly a Lean runtime projection. The mutation plan is post-cold testing metadata rather than an expansion of that evidence boundary.

The flat and correlation operations are narrow development references, not a complete A12 interpreter kit. In particular, `flat-validation-empty-logic-v1` has status `developmentColdHandover`: it exists to measure whether the project can transfer a finite semantic slice to an isolated implementer without renewed A12 kernel research, not to claim release closure for the wider flat operation. The candidate runner uses bounded duplicate-safe parsing, enforces closed suite/case/evidence objects, checks the full compatibility identity, finite evidence scope, retained runtime/static counts, and per-case claim-source classification, structurally compares suite JSON, and verifies retained evidence identifiers. The flat suite is mechanically projected; the correlation suite retains reviewed manual projection links. The reference-process gate runs every suite's integrity checks and Lean-reference control. The runner does not close unrelated manifest/projection members, impose a process timeout, or cap streamed output. High-volume cross-language fuzzing may later justify a batch runner or long-running process, but process architecture changes require measurement and a separate protocol decision. [`PLAN.md`](PLAN.md) owns the remaining generated-differential and release-closure work.
