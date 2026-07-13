# Product proposal — A12 semantic compatibility kit

**Status:** proposal, not an adopted release commitment. Current implemented coverage and evidence readiness are reported only in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), and the immediate engineering sequence remains in [`PLAN.md`](PLAN.md).

## Product thesis

The first releasable product should be a versioned semantic compatibility kit: a Lean-built executable reference for explicitly supported A12 30.8.1 validation and computation fragments, surrounded by a stable portable protocol, retained kernel evidence, a fail-closed support boundary, and machine-readable proof and trust information. It should let independent interpreters and tools ask the same normalized semantic question, compare observable results, and identify unsupported or divergent behavior without linking to the kernel.

This product realizes the durable mission in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) without turning every long-term potential into a first release. It is Cedar-like at the product and ecosystem boundary: a separately consumable executable specification, a production implementation that remains independent, and differential conformance between them. It is Radix-like only where a compact evaluator/relation or transformation-preservation proof adds an independently meaningful internal result. It is specifically A12 in its clean-room portable evidence bridge and in the richer semantics of validation, computation, document structure, absence, iteration, correlation, polarity, and phase-sensitive reads.

## Proposed first 0.x release

A useful first 0.x release could contain:

- a Lean-built command-line reference evaluator for the explicitly supported fragment;
- a stable JSON input/output protocol for each explicitly supported operation's normalized models, rules, runtime inputs, observable outcomes, and diagnostics, extended to documents, worlds, messages, and computation deltas only as those semantic stages land;
- the retained A12 kernel 30.8.1 evidence bundle and a conformance runner that replays its supported projection;
- a machine-readable supported-fragment manifest that fails closed rather than guessing outside the implemented theory;
- a theorem and checked-counterexample index with a report of trusted roots, dependencies, and exclusions;
- a language-neutral implementer handbook containing a research-closed decision procedure, worked trace, evidence limits, property/non-law guidance, and escalation path for every released capability;
- reproducible binaries or packages suitable for CI use on the supported platforms;
- a concise user-facing compatibility guide whose displayed examples are executed or elaborated by a documentation regression gate and whose support metadata comes from canonical sources, using whatever publication mechanism best fits the material.

The proposed public claim is deliberately narrow:

> Mechanized executable reference semantics for the named A12 30.8.1 fragment, internally proved at the documented boundaries and empirically checked against retained kernel evidence.

The release must not claim that it verifies the external kernel implementation, covers all A12 semantics, replaces the production runtime, or proves an independent Rust, Kotlin, or TypeScript implementation correct for inputs outside a separately established conformance boundary. An unsupported construct is a structured rejection, never permission to extrapolate from a nearby supported operator.

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

The diagram is a target integration shape, not a claim that all adapters already exist. The kernel remains outside this repository and outside the released process. The a12-dmkits adapter in the sibling `a12-rulekit/` checkout may execute focused kernel probes externally and export portable observations; this repository consumes only the retained clean-room evidence. The a12-dmkits interpreter remains a useful independent peer for triangulation and disagreement discovery, never the behavioral oracle.

The reference CLI should optimize for determinism, stable structured output, and diagnostic precision before terminal presentation. Human formatting can be layered over the JSON contract. A library API may coexist with the CLI, but the process-level protocol is the safer ecosystem boundary for Rust, Kotlin, TypeScript, CI, and future languages because it avoids coupling consumers to Lean runtime internals.

## Independent-interpreter handover

The compatibility kit should remove repeated kernel archaeology from downstream implementation work. A capability may be under internal Lean development before its handover is complete, but it enters a released supported set only when the research-closure gate in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) is green: language-neutral types and decision procedure, runnable fixtures, retained evidence and its limits, theorem-inspired properties, checked non-laws, a worked non-trivial trace, oracle/conformance tooling, and an escalation protocol all describe the same fragment.

The corresponding product test is a cold implementation by a developer or isolated coding agent with no kernel access, sibling checkout, or private conversation context. It must be able to implement the normalized fragment idiomatically, pass its conformance surface, explain the evidence boundary, and diagnose a seeded disagreement. Any question that forces fresh kernel research is a product defect to close in this repository and release once for every consumer, not work to repeat in Rust, Kotlin, or TypeScript.

This handover does not transfer Lean proofs to the independent implementation. The kit distinguishes proved properties of the Lean theory, executed cross-language conformance, and retained empirical kernel correspondence; a compatibility report names all three without collapsing them.

## Supported-fragment manifest

Each release should ship a machine-readable manifest beside its binary and evidence bundle. The implemented flat and one-group correlation slices now have separate exact Lean-generated operation records in schema-2 [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json), documented by [`PROTOCOL.md`](PROTOCOL.md). The correlation record includes its narrower external-evidence boundary, and [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) plus [`single-group-correlation-v1.conformance.json`](../reference/single-group-correlation-v1.conformance.json) form the first concrete handover spike. The broader release shape below remains illustrative because theorem roots and whole-bundle evidence identity are not yet packaged into that process manifest.

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

The checking mechanism should follow the artifact being explained:

| User-facing material | Natural regression surface | Possible publication form |
|---|---|---|
| Lean definitions, evaluations, and theorem statements | Lean elaboration and executable examples | Lean module documentation, generated API pages, or Verso when a curated narrative adds value |
| Reference CLI and JSON protocol | Process-level integration tests over arguments, exit status, standard output, and standard error | Markdown or a generated walkthrough that renders the already-checked scenarios; Verso is optional |
| Supported fragments and retained kernel observations | Manifest validation and the evidence replay runner | Generated tables or pages linked to the canonical coverage and evidence records |
| Project purpose, architecture decisions, provenance, and limitations | Link checks, review, and same-change documentation discipline | Plain Markdown |

This makes user documentation an additional regression consumer, not a replacement for the ordinary test surfaces. Its examples need not be the test suite's exact fixtures: purpose-built pedagogical cases can explain the public behavior more clearly and provide an independent documentation gate. What matters is that the displayed examples themselves execute or elaborate, their outcomes are checked at the surface being presented, and canonical support or theorem metadata is referenced rather than retyped. The normal unit, property, conformance, differential, process-integration, and trust gates remain authoritative for their respective claims.

Verso has a natural but narrower opportunity when the explanation itself needs Lean awareness: elaborated snippets, checked declaration references, live evaluation results, theorem-linked prose, proof-state presentation, or Radix-style slides that import the actual library. It is not inherently the right tool for command transcripts, ordinary design prose, evidence provenance, or a language-neutral compatibility guide. No Verso target should be scheduled merely because the project now has enough Lean material to populate one.

For users, Verso would earn its cost if a published semantic handbook makes conditions, computations, absence, iteration, correlation, or proof boundaries materially easier to learn while keeping its Lean-bearing examples checked. For Lean contributors, it can provide a curated path through declarations and theorems that generated API pages alone do not explain. For an LLM or coding agent, its useful contribution would be stable, checked examples and navigable links from a semantic claim to the actual declaration, theorem, counterexample, and evidence status. It becomes counterproductive if canonical project knowledge moves out of easy-to-read Markdown, if understanding requires first building a documentation DSL, or if generated prose duplicates the ownership map.

The adoption trigger is therefore a concrete reader or maintenance problem: repeated public examples have begun to drift, users need a coherent semantic learning path, theorem-rich material is hard to navigate, or presentations must remain synchronized with the theory. At that point, run the smallest experiment that addresses that problem and compare its benefit with ordinary Markdown plus shared fixtures. [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#128-use-markdown-docstrings-and-verso-for-different-jobs) records the detailed tool boundary and researched precedent.

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
8. every manifest-listed release capability is research-closed, ships its complete implementation capsule, and has passed a recorded cold-implementer test without kernel or sibling-source access.

## Recommended progression

1. **Compatibility kit:** stabilize the normalized protocol, reference CLI, support manifest, retained evidence bundle, conformance runner, CI integration, research-closed implementer handbook, cold-implementation gate, and a concise user guide with its own executable-documentation regression gate.
2. **Complete validation reference:** add whole-rule evaluation, message location and type, iteration, correlation, polarity, and partial validation across explicitly versioned fragments.
3. **Computation reference:** add ordered state transition, clearing, poison, target rendering, and implicit validation rules while preserving read-order observability.
4. **Model-audit tooling:** expose equivalence, implication, redundancy, overlap, counterexample generation, dependency analysis, and domain-invariant checks over admitted models.
5. **Verified compilation or certificates:** add compilation, optimization, or certificate generation only after a concrete production consumer supplies a target contract and a preservation obligation.
6. **Optional Lean runtime integration:** consider an FFI or long-running service boundary only if measured deployment and performance requirements justify tighter coupling than the CLI protocol.

Each stage extends the manifest and public claim only after its semantic capsules close their internal and external gates. A future stage is not implied support in the current release.

## Adoption and reevaluation

The first condition is now more concretely realized: the non-repeatable flat fragment and one-group correlation fragment are exposed through the coherent normalized process contract in [`PROTOCOL.md`](PROTOCOL.md), with deterministic black-box tests, a generated per-operation support manifest, a manually evidence-cross-referenced language-neutral suite with explicit claim-source metadata, and a candidate runner exercised against the Lean reference. The correlation kit still records release-blocking suite-integrity, evidence, negative-protocol, process-hardening, and cold-implementation gaps. Adopt the full proposal as product strategy when a real non-Lean consumer completes that cold gate and is willing to run the reference or suite in CI, and retained evidence plus proof metadata can be packaged reproducibly. Until then, it guides product-shaped architecture without treating these development capsules as a release commitment or forcing process infrastructure into every semantic capsule.

Reevaluate the shape if process startup dominates realistic conformance workloads, consumers require interactive high-volume evaluation, a stable parser boundary proves more valuable than normalized input, or protocol versioning cannot express the semantic support boundary without duplicating the Lean theory. Those findings may justify a service, FFI, generated bindings, or certificates, but only with a concrete consumer and documented trust tradeoff.
