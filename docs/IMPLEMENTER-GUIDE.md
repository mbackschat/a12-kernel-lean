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
6. **Evidence account:** the retained kernel cases supporting each claimed kernel-semantic choice, the projection actually compared, and every unobserved dimension that must not be inferred; project-defined transport choices are labeled separately.
7. **Law and non-law index:** language-neutral property statements with exact hypotheses, observable result domain, generator guidance, and stated non-applicability cases, paired with checked counterexamples that bound those properties; each entry links to the exact Lean theorem or conformance declaration for audit rather than requiring the implementer to interpret Lean.
8. **Worked trace:** a readable staged explanation of at least one non-trivial case, distinguishing normative semantic steps from evidence observations and implementation freedom.
9. **Oracle and conformance tools:** the reference invocation, support-manifest query, fixture runner, differential workflow, deterministic-output rules, expected diagnostics, and a language-neutral conformance dataset or documented adapter from retained evidence into the normalized operation.
10. **Escalation rule:** how an implementer reports a missing distinction or disagreement and how a corrected, newly evidenced semantic release reaches every consumer.
11. **Cold-test record:** the exact kit/version and artifact digests supplied, isolation assumptions, downstream implementation revision and toolchain, conformance and property results, seeded disagreement and its classification, unresolved questions, and final handover verdict.

A link to a Lean definition alone is not a decision procedure, a corpus count is not an evidence account, and a list of expected outputs without the separating reason is not an implementation guide.

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

## Independent implementation playbook

1. Query the reference manifest and select one closed capability; pin its complete compatibility tuple.
2. Read the implementation capsule before the Lean source. Map its language-neutral sum types and staged boundaries to idiomatic language constructs, preserving raw-versus-checked, inner-versus-outer, empty-versus-malformed, phase, order, and provenance distinctions.
3. Implement the smallest admitted core and fail closed on every excluded shape. Do not add convenience behavior for a nearby unsupported operator.
4. Run the canonical fixtures as the first red/green loop, then implement the language-neutral law index as property tests with its supplied hypotheses and generators and preserve the non-law index as fixed regressions.
5. Differentially execute generated normalized cases through the independent implementation and the Lean reference. Compare only the observable projection promised by the capsule.
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

The current reference executable and manifest are documented in [`PROTOCOL.md`](PROTOCOL.md); runnable inputs live under [`../examples/reference-cli/`](../examples/reference-cli/); retained observations and their limits are in [`EVIDENCE.md`](EVIDENCE.md); theorem, counterexample, and trust methodology is in [`TESTING.md`](TESTING.md). The first concrete handover spike is [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md), backed by the language-neutral [`single-group-correlation-v1.conformance.json`](../reference/single-group-correlation-v1.conformance.json) suite. The basic interaction is:

```sh
lake exe a12-kernel-reference --manifest
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
lake exe a12-kernel-reference < examples/reference-cli/correlation-direction.request.json
lake exe checkReferenceProcess
lake exe checkCandidateConformance --self-test --suite reference/single-group-correlation-v1.conformance.json
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/single-group-correlation-v1.conformance.json
```

The flat and correlation operations are narrow development references, not a complete A12 interpreter kit. The candidate runner uses bounded duplicate-safe parsing, enforces closed suite/case/evidence objects, checks the full compatibility identity, finite evidence scope, retained runtime/static counts, and per-case claim-source classification, structurally compares suite JSON, and verifies retained evidence identifiers. Its canonical all-case validation, sixteen negative guards, and full Lean-reference suite control are run by the reference-process gate. It does not close unrelated manifest/projection members, mechanically derive fixtures from retained projections, impose a process timeout, or cap streamed output. High-volume cross-language fuzzing may later justify a batch runner or long-running process, but process architecture changes require measurement and a separate protocol decision. [`PLAN.md`](PLAN.md) owns the remaining suite-integrity, cold-implementation, and release-closure work.
