# Product proposal — A12 semantic compatibility kit

**Status:** proposal, not an adopted release commitment. Current implemented coverage and evidence readiness are reported only in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), and the immediate engineering sequence remains in [`PLAN.md`](PLAN.md).

## Product thesis

The first releasable product should be a versioned semantic compatibility kit: a Lean-built executable reference for explicitly supported A12 30.8.1 validation and computation fragments, surrounded by a stable portable protocol, retained kernel evidence, a fail-closed support boundary, and machine-readable proof and trust information. It should let independent interpreters and tools ask the same normalized semantic question, compare observable results, and identify unsupported or divergent behavior without linking to the kernel. The longer-lived product asset is the semantics factory behind that first evaluator: it should later produce task-specific shipments for checked importers, rule refactoring, analysis, and certification without making those future profiles claims of the initial release.

This product realizes the durable mission in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) without turning every long-term potential into a first release. It is Cedar-like at the product and ecosystem boundary: a separately consumable executable specification, a production implementation that remains independent, and differential conformance between them. It is Radix-like only where a compact evaluator/relation or transformation-preservation proof adds an independently meaningful internal result. It is specifically A12 in its clean-room portable evidence bridge and in the richer semantics of validation, computation, document structure, absence, iteration, correlation, polarity, and phase-sensitive reads.

## General consumer task categories

The semantics factory should be able to produce purpose-specific shipments across ten general categories. These are task contracts, not implementation-language choices, and each concrete capability still needs a closed source/target fragment and assurance boundary. Categories may overlap and compose; they are a vocabulary for consumer contracts, not ten release commitments or a development sequence.

| Category | Abstract contract | Representative products |
|---|---|---|
| **Execute** | A12 artifact + runtime input → semantic outcome | Reference evaluator, independent interpreter, validation/computation service |
| **Translate** | Source representation ↔ checked A12 artifact or target projection | JSON Schema importer, concrete-DSL lowering, legacy-model migration, bounded export |
| **Transform** | A12 artifact → behavior-related A12 artifact | Rule refactoring, simplification, normalization |
| **Compile** | A12 artifact → executable plan or target program | Specialized evaluator, indexed correlation plan, target-code generator |
| **Analyze** | A12 artifact → facts or witnesses | Equivalence, redundancy, dependency, satisfiability, impact analysis |
| **Verify** | Artifact + independently stated claim → checked proof/certificate, counterexample, or explicit inconclusive result | Business invariants, preservation theorems, model approval |
| **Synthesize** | Goal or constraint → document, rule, repair, or counterexample | Test-data generation, minimal repair, missing-case witness |
| **Qualify** | Implementation/version + reference → agreement or differences | Conformance, differential, property, fuzz, and mutation testing |
| **Explain** | Execution/proof/change → human-understandable account | Traces, debugging, checked documentation, change reports |
| **Govern** | Versioned artifacts and evidence → compatibility or release decision | Support manifests, migration reports, audits, release gates |

The first compatibility-kit release is intentionally concentrated on **Execute** and **Qualify**, with a limited **Explain** and **Govern** surface through checked examples, manifests, evidence, and trust reports. Later stages add other categories only when their semantic prerequisites and concrete consumer contracts exist. [`USE-CASES.md`](USE-CASES.md) is the user-facing explanation of how Lean contributes to each category and what it does not establish automatically.

## Proposed first 0.x release

A useful first 0.x release could contain:

- a Lean-built command-line reference evaluator for the explicitly supported fragment;
- a stable JSON input/output protocol for each explicitly supported operation's normalized models, rules, runtime inputs, observable outcomes, and diagnostics, extended to documents, worlds, messages, and computation deltas only as those semantic stages land;
- the retained A12 kernel 30.8.1 evidence bundle and a conformance runner that replays its supported projection;
- a machine-readable supported-fragment manifest that fails closed rather than guessing outside the implemented theory;
- a machine-readable descriptor and conformance suite for every released capability, reproducibly projected from its retained typed evidence where that evidence is the claim source;
- a theorem and checked-counterexample index with a report of trusted roots, dependencies, and exclusions;
- a language-neutral consumer handbook whose initial evaluator profile contains, for every released evaluator capability, a research-closed decision procedure, worked trace, evidence limits, property/non-law guidance, and escalation path;
- reproducible binaries or packages suitable for CI use on the supported platforms;
- a concise user-facing compatibility guide whose displayed examples are executed or elaborated by a documentation regression gate and whose support metadata comes from canonical sources, using whatever publication mechanism best fits the material.

The proposed public claim is deliberately narrow:

> Mechanized executable reference semantics for the named A12 30.8.1 fragment, internally proved at the documented boundaries and empirically checked against retained kernel evidence.

The release must not claim that it verifies the external kernel implementation, covers all A12 semantics, replaces the production runtime, or proves an independent Rust, Python, Kotlin, or TypeScript implementation correct for inputs outside a separately established conformance boundary. An unsupported construct is a structured rejection, never permission to extrapolate from a nearby supported operator.

## Product boundary and integration

The stable integration boundary should use normalized, versioned data rather than require every consumer to implement the bilingual authoring parser. Parser, editor, or model-tooling integrations may lower their own surface structures into the supported protocol and must receive explicit diagnostics for constructs the reference does not admit.

```text
expanded A12 model + resolved rule + document + world
                         |
               versioned normalized protocol
                         |
          +--------------+---------------+
          |                              |
 Lean reference evaluator       independent interpreter
          |                              |
          +----- normalized outcomes ----+
                         |
              comparison in consumer CI
                         |
       retained kernel 30.8.1 evidence replay
```

The diagram is a target integration shape, not a claim that all adapters already exist. The kernel remains outside this repository and outside the released process. Existing a12-dmkits corpus and differential facilities in the sibling `a12-rulekit/` checkout may execute focused kernel probes externally when their observation shape fits; otherwise a concrete semantic family must justify the smallest purpose-specific upstream handback. This repository consumes only retained clean-room evidence and never assumes a standing generic exporter. The a12-dmkits interpreter remains a useful independent peer for triangulation and disagreement discovery, never the behavioral oracle.

Future consumer profiles reuse the versioned A12 foundation but have different task boundaries. A JSON Schema importer accepts only a named source dialect/subset and produces a checked normalized A12 model or explicit diagnostic; a rule-refactoring tool accepts a checked A12 rule and produces a checked result plus the obligation or certificate for its named preservation relation. They do not masquerade as additional evaluator operations, and they do not become release capabilities until their source/target fragments, evidence, relation, and qualification gates are closed.

The reference CLI should optimize for determinism, stable structured output, and diagnostic precision before terminal presentation. Human formatting can be layered over the JSON contract. A library API may coexist with the CLI, but the process-level protocol is the safer ecosystem boundary for Rust, Python, Kotlin, TypeScript, CI, and future languages because it avoids coupling consumers to Lean runtime internals.

## Semantic consumer shipments

The compatibility kit should remove repeated kernel archaeology from downstream implementation and tooling work. A capability may be under internal Lean development before its shipment is complete, but it becomes eligible for a released supported set only when the research-closure gate in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) is green: language-neutral types and task contract, runnable fixtures, retained evidence and its limits, theorem-inspired properties, checked non-laws, a worked non-trivial trace, qualification tooling, and an escalation protocol all describe the same source and target fragments. The remaining product and production gates still apply.

The repeatable production chain is part of that product, not internal convenience. For an evaluator, define a machine-readable capability descriptor, project retained typed evidence inputs through the public protocol, verify that decoding reconstructs the same checked input, evaluate through the existing reference route, and generate the fixtures, suite, and per-case claim-source classification before asking an independent implementer to write code. An importer or refactoring shipment needs the analogous checked source-to-target projection and generated validity/preservation qualification material. A hand-curated guide may explain the result, but it must not be the only connection between maintained semantics and the normalized shipment.

The corresponding product test is a cold-consumer exercise by a developer or isolated coding agent with no kernel access, sibling checkout, or private conversation context. An evaluator exercise must implement the normalized fragment idiomatically and pass conformance; an importer or refactoring exercise must implement the named mapping or transformation and pass its validity, rejection, boundary, and preservation-oriented qualification checks. These finite checks qualify that implementation only over executed inputs unless its outputs are covered by a proved transformation or certificate checker. Any A12 question that forces fresh kernel research is a product defect to close in this repository and release once for every consumer, not work to repeat in Rust, Python, Kotlin, TypeScript, or another tool.

This shipment does not automatically transfer Lean proofs to an independent implementation. The kit distinguishes proved properties of the Lean theory or modeled transformation, executed consumer qualification, source-language evidence where applicable, and retained empirical kernel correspondence; the candidate qualification record names each without collapsing them.

## Supported-fragment manifest

Each release should ship a machine-readable manifest beside its binary and evidence bundle. Current [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json) demonstrates separate operation records and finite evidence boundaries for reference semantics 0.3.0; appearance there is not release approval. Protocol 1 has no per-request reference-semantics selector, so a product integration must inspect `--manifest` from the exact binary and pin the binary or release digest. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns live semantic and evidence readiness; the current 0.3.0/V2 [flat](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation](IMPLEMENTER-KIT-CORRELATION.md) kits own their exact projection integrity and consumer gaps. Retired 0.2.0/V1 identities and Rust results remain only in the [historical record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md) and its pinned Git revisions. The broader release shape below remains illustrative because proof-root and whole-bundle evidence identity are not yet packaged into the process manifest.

```json
{
  "semanticsVersion": "0.x",
  "kernelBehaviorVersion": "30.8.1",
  "protocolVersion": 1,
  "supportedFragments": ["named-fragment-identifiers"],
  "unsupportedFragments": ["explicit-exclusions"],
  "theoremRoots": ["reviewed-trusted-roots"],
  "evidenceBundle": {
    "version": "bundle-version",
    "digest": "content-digest"
  }
}
```

This is an illustrative release contract shape, not the current two-operation process schema. The current manifest is generated from finite Lean support declarations and mechanically checked against its readable shipped mirror; its relationship to semantic and external-evidence status is recorded in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md). A future release manifest should additionally consume proof-root and whole-evidence-bundle metadata rather than duplicate them by hand.

## User-facing documentation as a regression consumer

The transferable lesson from the audited Cedar and Radix practices is that an explanation is more trustworthy when the examples users see consume the live theory and are also exercised by automation. A compatibility guide should therefore execute or elaborate its displayed semantic scenarios and consume maintained support declarations, theorem names, counterexamples, and evidence summaries wherever possible instead of copying results into prose that can silently drift.

This makes user documentation an additional regression consumer, not a replacement for the ordinary test surfaces. Its examples need not be the test suite's exact fixtures: purpose-built pedagogical cases can explain the public behavior more clearly and provide an independent documentation gate. What matters is that the displayed examples themselves execute or elaborate, their outcomes are checked at the surface being presented, and canonical support or theorem metadata is referenced rather than retyped. The normal unit, property, conformance, differential, process-integration, and trust gates remain authoritative for their respective claims.

The publication mechanism should match the material and a concrete reader or maintenance need; it must not become another semantic authority. [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#128-use-markdown-docstrings-and-verso-for-different-jobs) owns the detailed comparison of Markdown, Lean docstrings, generated API documentation, Verso, and Blueprint, together with the adoption criteria and researched precedent.

## Release gates

This section owns the product-level credibility conditions. Concrete artifact qualification, reproducibility, platform support, packaging, signing, optimization, publication, and rollback are governed by [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md); creating that engineering contract does not by itself adopt this proposal.

A 0.x compatibility-kit release is credible only when:

1. the normalized protocol is versioned, deterministic, documented, and protected by process-level conformance tests;
2. every accepted input belongs to a machine-readable supported fragment and every unsupported construct fails closed with a structured diagnostic;
3. each claimed kernel-semantic choice has retained, versioned kernel observations; any `external evidence pending` capability stays out of the released supported set, while project-defined transport and diagnostic choices are labeled separately and process-tested;
4. the theorem and counterexample index names exact hypotheses, result domains, exclusions, and trusted roots rather than advertising theorem counts;
5. the trust audit, executable examples, retained evidence replay, protocol tests, and reproducible build are green from a clean checkout;
6. the released source, binaries, evidence, and documentation respect the clean-room boundary and contain no kernel-linked or transcribed implementation;
7. user-facing executable examples, if shipped, are fed by the corresponding regression surface and clearly separate internal proof claims from empirical kernel correspondence.
8. every release-listed consumer capability is research-closed, ships its complete semantic shipment, and has passed a recorded task-appropriate cold-consumer test without kernel or sibling-source access.

## Recommended progression

1. **Compatibility kit:** stabilize the normalized protocol, reference CLI, support manifest, retained evidence bundle, conformance runner, CI integration, research-closed evaluator shipment and cold-evaluator gate, and a concise user guide with its own executable-documentation regression gate.
2. **Complete validation reference:** add whole-rule evaluation, message location and type, iteration, correlation, polarity, and partial validation across explicitly versioned fragments.
3. **Computation reference:** add ordered state transition, clearing, poison, target rendering, and implicit validation rules while preserving read-order observability.
4. **Checked model import:** select one concrete external source profile—JSON Schema is the leading example—and ship a fail-closed source-to-A12 mapping with pinned dialect/subset, source satisfaction model, instance/Document relation, target well-formedness, explicit lossiness, and only the preservation directions actually established.
5. **Rule analysis and refactoring:** expose equivalence, implication, redundancy, overlap, counterexample generation, dependency analysis, and domain-invariant checks, then ship selected refactorings with exact preconditions, full declared observation relations, checked boundary counterexamples, and certificates where they reduce downstream trust.
6. **Verified compilation or certificates:** add compilation, optimization, or certificate generation only after a concrete production consumer supplies a target contract and a preservation obligation.
7. **Optional Lean runtime integration:** consider an FFI or long-running service boundary only if measured deployment and performance requirements justify tighter coupling than the CLI protocol.

Each stage extends the applicable support declaration and public claim only after its semantic capsules and task-specific source/target obligations close their internal and external gates. A future stage is not implied support in the current release, and importer/refactoring work must not bypass unresolved A12 validation or computation prerequisites.

## Adoption and reevaluation

The historical 0.2.0/V1 flat shipment and its first isolated non-Lean implementation provide initial evidence that the proposed knowledge-transport shape is viable for one finite evaluator capability; they do not establish release readiness, current 0.3.0/V2 qualification, or broader language coverage. The exact cold implementation, mutation qualification, later 52-case generated differential, and Git recovery points are preserved in the [archived experiment record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md), while current semantic and external-evidence readiness is owned by [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md). Adopt the full proposal as product strategy when a real non-Lean consumer completes the entire selected current capability gate, is willing to run the reference or suite in CI, and retained evidence plus proof metadata can be packaged reproducibly. Until then, it guides product-shaped architecture without treating development shipments as a release commitment or forcing process infrastructure into every semantic capsule.

Reevaluate the shape if process startup dominates realistic conformance workloads, consumers require interactive high-volume evaluation, a stable parser boundary proves more valuable than normalized input, or protocol versioning cannot express the semantic support boundary without duplicating the Lean theory. Those findings may justify a service, FFI, generated bindings, or certificates, but only with a concrete consumer and documented trust tradeoff.
