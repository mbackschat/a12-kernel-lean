# Proposal: amortized semantic-capsule pipeline

## Status

This is an a12-kernel-lean architecture proposal, not current implementation state. It complements the upstream [`a12-dmkits portable-capture proposal`](A12-DMKITS-CAPTURE-PROPOSAL.md). The source-maintained packet schema and capture boundary now exist and have passed generic process qualification plus a disposable first-client smoke run. The official direct-cascade packet is still pending, so the input-only scenario investment is active while the shared Lean packet binder and registry remain deliberately unimplemented. Do not redesign frozen historical evidence or shipments merely for uniformity.

## Goal

Make the bespoke work in a future semantic capsule consist primarily of the semantic clause, separating cases, projection, useful laws, and nearest non-laws. Scenario transport, engine execution, packet verification, inventory binding, status indexing, and shipment metadata should reuse maintained infrastructure.

The intended pipeline has two one-way inputs that meet only at nontrusted replay and reporting:

```text
input-only scenario pack ──→ a12-dmkits ──→ portable packet ──→ strict binding ──┐
                                                                                 ├─→ nontrusted evidence replay ──→ capsule registry and shipment metadata
Lean semantics ──→ executable evaluator ─────────────────────────────────────────┘
       └─→ proofs and laws
```

The registry and reporting layer may index declarations and evidence, but semantics and proofs never import evidence, the registry, or generated shipment/process drivers. This pipeline preserves the current authority boundary: a12-dmkits never needs to understand Lean, and Lean never needs kernel-facing Kotlin or Java instrumentation.

## Why invest early

The present evidence pipeline proved that strict binding is valuable, but its transport mechanics are repeating. [`StringComputationBinding.lean`](../A12Kernel/Evidence/StringComputationBinding.lean) has 722 lines and [`StringTargetValidationBinding.lean`](../A12Kernel/Evidence/StringTargetValidationBinding.lean) has 901; both separately define receipt structures, closed-member checks, relative-path safety, uniqueness, inventories, revision binding, runner binding, and artifact digests. Their operation-specific checks are necessary, but this common plumbing should not be rewritten for every capsule.

The Rust experiment exposed the same issue one layer later: a carefully assembled handover worked, but repeated normative identity, evidence, fixture, and capability facts are expensive to keep synchronized unless generated from a checked owner.

The early investments below therefore target repeated mechanisms already observed at least twice. They deliberately avoid speculative universal languages or frameworks.

## Route each future change to one owner

Classify a requested change before editing code. This keeps an ordinary new case cheap and makes an actual compatibility change explicit.

| Change | Normal work unit | Identity consequence |
|---|---|---|
| Another case within an existing operation, input-support version, and observation profile | Add one input-only scenario case and recapture; no a12-dmkits source change | New scenario-set version or ID and new packet digest |
| Another operator or shape already representable by the same payload but outside current interpreter support | Add scenario data; the interpreter may report `unsupported` or divergence while both kernel routes still characterize it | New scenario/capsule identity; no payload-schema claim expansion |
| A required observation the current payload cannot express | Add one closed operation-payload or projection version upstream, then its explicit Lean decoder | New immutable payload/projection ID; old packets remain valid |
| A new execution route or richer published fidelity | Add a new versioned compile-time runner descriptor or route upstream; never reinterpret a published descriptor in place | New runner/fidelity ID and implementation-closure digest |
| An a12-dmkits interpreter, runner, or capture-mapper fix that preserves its published schema and fidelity contract | Change the upstream implementation, recapture unchanged scenarios, and structurally diff the packets and reports | New a12-dmkits revision, implementation-closure, packet, and report digests; schema and runner IDs stay stable and old packets remain valid |
| A kernel-version upgrade | Replay unchanged scenario packs, produce new packets, and use structural diff before changing Lean | New kernel compatibility tuple; never overwrite old evidence |
| A new Lean semantic clause over already captured data | Add the clause, separating locks, law/non-law, typed projection, and capsule descriptor | New Lean semantic/capsule version as required; packet bytes stay unchanged |
| A new downstream interpreter, importer, auditor, or refactoring tool | Reuse the capsule registry and common shipment envelope; add only the task-specific capability and fixtures | New shipment/capability identity; no universal consumer-task IR |

If a proposed change touches more rows than expected, stop and identify the hidden boundary instead of spreading a one-off adaptation through capture, Lean, and shipment code.

## Investment 1 — input-only scenario packs

a12-kernel-lean should own the questions it asks of the external oracle as closed scenario packs containing complete model and input-document bytes, stable case IDs, operation profile, required observation channels, probe scope, world inputs where relevant, and short non-normative rationale or varied-axis labels.

a12-dmkits owns the versioned scenario schema and generic exporter self-tests; this repository owns each capsule-specific instance after that schema is available. The capture command consumes the external pack and copies its exact bytes into the packet. The same capsule scenario is not committed independently in both repositories, and any later a12-dmkits corpus promotion has a new explicit projection and ownership lifecycle.

Scenario packs must never contain expected verdicts, values, diagnostics, error codes, agreement flags, or mutation answers. A structural checker should reject such members and verify that claimed one-axis pairs differ only on their declared input axes. Complete DM-JSON models remain the portable authored form; conveniences may generate them, but the contract must not become a second A12 authoring DSL.

V1 uses explicit cases with shared ordinary-data defaults only if that representation remains closed and fully expands before capture. A later input-only matrix expander may cover repeated kind × operator × emptiness × context combinations, but it must retain the expanded manifest and must not branch on observed output.

## Investment 2 — shared strict packet and qualification-sidecar binding

After the upstream packet/receipt and qualification-report/receipt schemas stabilize, add reusable IO-only Lean support with one-way references: the packet binder knows only the immutable capture packet and receipt, while the sidecar binder independently verifies a qualification report that names the packet receipt digest. Add common support for:

- exact closed-object decoding;
- safe relative artifact references without traversal or symlinks;
- sorted complete inventories, byte counts, and SHA-256 identities;
- request, model, document, case, observation, and packet-receipt references;
- qualification profile, report, sidecar-receipt, and bound packet-receipt references without a backward packet-to-report edge;
- kernel, exporter, source-revision, schema, runner, and policy identities;
- duplicate and missing ID rejection;
- exact engine inventories and named projection-comparison assertions;
- machine-specific-data rejection.

This shared binder belongs outside the trusted semantics, elaboration, proof, and conformance roots. It verifies transport and provenance; it does not assign semantic meaning to operation fields and does not prove correspondence to the external kernel.

Each operation keeps a closed typed decoder and explicit semantic projection. Computation result, delta, application state, and diagnostics must not disappear behind generic maps. The framework eliminates receipt boilerplate without hiding the claim boundary.

Apply the framework first to the new direct-cascade packet. Do not migrate or regenerate frozen reference semantics 0.2.0, historical Rust artifacts, or completed evidence packets just to make their shape uniform.

## Investment 3 — typed capsule registry

Introduce one nontrusted, typed descriptor per capsule that links maintained facts without becoming a semantic dependency. Each descriptor should name:

- capsule ID and version;
- read-only `spec/` clauses and writable source findings;
- semantic and elaboration declaration roots;
- theorem roots and checked non-laws;
- external packet, model, case, and projection IDs;
- exact externally observable fields and evidence exclusions;
- protocol capability and operation, when exposed;
- consumer shipment and qualification identity, when one exists;
- open semantic, proof, evidence, protocol, shipment, and qualification boundaries.

Status must remain multidimensional. “Implemented internally,” “proved internally,” “externally observed,” “publicly supported,” “shipped,” and “independently qualified” are distinct facts and must never collapse into one `complete` Boolean.

A registry checker should resolve Lean declaration names, verify referenced artifact IDs and digests, ensure every public capability names a capsule, and detect orphaned or contradictory registered status. Any claim that every maintained semantic or theorem root is registered requires an independent enumeration mechanism—for example dedicated Lean attributes plus a source-root manifest whose discovered set must equal registry membership. Without that independent set, the checker may claim completeness only for registered entries. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) remains the explanatory human owner, but its mechanical identities should be generated from or checked against the registry rather than copied independently.

The registry may import and inspect semantics, proofs, evidence, and protocol metadata; none of those trusted layers may import the registry back. This preserves the Cedar-style one-way assurance boundary.

## Investment 4 — checked evidence import

Once two official packets demonstrate a stable shape, add a local command conceptually equivalent to `importEvidence` that:

1. verifies the complete upstream packet/receipt and required qualification sidecars against their supplied out-of-band digests;
2. checks the upstream source and kernel identities against the requested compatibility tuple;
3. copies the complete portable packet into a new project-owned evidence location without rewriting existing evidence;
4. creates or checks an input-only capsule index selecting case IDs;
5. scaffolds operation-specific projection references and registry entries;
6. refuses to invent expected Lean results, semantic field mappings, laws, or proof statements.

The command should have `--check` reproduction from the committed packet and descriptor. It may generate mechanical indexes and references, but human review still owns the semantic projection and correspondence claim.

## Investment 5 — reusable shipment builder

After a second downstream consumer profile confirms the pattern, generate or check the mechanical portion of capability shipments from the capsule registry:

- compatibility tuple;
- task and operation profile;
- supported and excluded fragments;
- normalized fixtures and conformance-suite inventory;
- case-level external-evidence, Lean-law, and Lean-refinement classification;
- theorem and checked-non-law index;
- artifact inventory and digests;
- verification commands and qualification hooks.

Human implementer guides and worked traces remain curated. Their referenced identities should be checked rather than manually duplicated. The builder must preserve whether a fact comes from a kernel observation, an internal Lean refinement, or a project-defined transport contract.

The envelope and lifecycle can be reused for evaluator, importer, and refactoring consumers, but their payloads remain task-specific. Do not invent a universal consumer-task IR.

## Investment 6 — efficient recapture and review

Request the upstream capture tool's deterministic `diff` in V1. It should classify request/input changes, provenance-only changes, each kernel route's observation changes, new cross-route splits, interpreter-only changes, projection changes, and case/inventory additions or removals. This makes a12-dmkits fixes and kernel-version upgrades reviewable without manually comparing bespoke receipts.

Keep full uncached capture authoritative. Case filtering is useful for local development, but final qualification runs the complete scenario set. Add content-addressed incremental reuse only after measured case volume justifies it; reused-plus-new output must be byte-identical to a clean full run at the same identities.

Keep full Lean CI authoritative as well. Focused capsule commands and a capsule-to-command index are useful now; dependency-based regression selection is not justified until measured runtime becomes a problem.

## Investment 7 — explicit trust-zone classification

The current trust audit recursively rejects imports from known nontrusted directories such as evidence, reference, qualification, differential, process, and trust drivers. Before the pipeline adds packet-binding, registry, import, or generation directories, strengthen that mechanism so an unclassified future directory cannot enter a trusted closure merely because it is absent from the blacklist.

Use explicit allowed zones for each root class: the logical theorem closure admits only declared foundations, core semantics, elaboration, and proof modules; the executable conformance closure may additionally admit conformance modules; evidence, packet binding, registry, generators, process drivers, and qualification remain outside both unless deliberately classified. Every newly introduced directory must fail the gate until assigned to a zone. Preserve the existing recursive theorem-root completeness and axiom audit.

## Recommended staging

### Stage A — upstream observation contract

The source-maintained schema, capabilities, non-executing scenario validation, public computation observations, deterministic packet, sidecar qualification, and diff boundary are implemented and repaired upstream at the revision recorded in [`PLAN.md`](PLAN.md). This repository has authored and structurally validated the exact five-case [`direct-cascade pack`](../evidence/scenarios/string-direct-cascade-v1/README.md). Stage A completes only when that unchanged external pack produces the official qualified packet without capsule-specific Java or Kotlin source or a second canonical scenario copy upstream.

### Stage B — first shared Lean binding

Verify and retain the returned cascade packet, classify the new binding/registry paths outside the trusted zones, build the common envelope/receipt binder only to the extent exercised by that real packet, and keep the cascade's computation projection explicit. Implement the direct-cascade semantics, proofs, non-law, and evidence binding through that path.

### Stage C — prove operation extensibility

Add one second upstream operation payload—prefer existing validation-message or static-authoring observations whose semantics and artifacts already exist—and route one new or deliberately recaptured non-frozen packet through the same envelope. Extend shared code only where the second real operation demonstrates a common mechanism.

### Stage D — capsule registry

Register the cascade and the next new capsule, add registered-root/artifact/status checks, and project the mechanical status facts into the human implementation map. Claim global source-root completeness only after the independent attribute/source-manifest enumeration mechanism exists. Do not rewrite historical capsule identities.

### Stage E — shipment generation

Use the next real interpreter, importer, or refactoring handover to factor the mechanical shipment builder. The consumer task determines the task-specific payload; the common lifecycle supplies identity, evidence, laws, fixtures, and qualification.

### Stage F — scenario matrices and incremental capture

Add input-only matrix expansion and content-addressed reuse only after repeated explicit scenario sets or measured capture time make their payoff concrete.

## Success criteria

The pipeline is paying for itself when:

- an ordinary new computation case is added as scenario data without Java or Kotlin capture changes;
- a new packet uses the shared receipt/inventory binder rather than another private receipt parser;
- an unavailable observation channel is rejected mechanically before research begins;
- an a12-dmkits or kernel revision can be recaptured and structurally diffed with one maintained workflow;
- a capsule's semantics, law, non-law, evidence, protocol, shipment, and qualification identities are checked from one typed descriptor;
- every project source directory is explicitly classified for logical, executable-conformance, or nontrusted use before it can enter a root closure;
- a downstream implementer receives a generated mechanical inventory plus curated semantic explanation without researching the kernel;
- frozen historical evidence and shipments remain byte-for-byte unchanged.

## Avoid

Do not build another patched or copied `RuntimeLaws` harness, put expected output in capture requests, treat interpreter agreement as an oracle prerequisite, use compact signature strings as canonical evidence, sort observable order away, auto-promote characterization data, rewrite frozen artifacts, generate semantic prose as authority, add a universal A12 scenario DSL, add a universal consumer-task IR, implement automatic semantic minimization, or optimize CI/caching before measurement justifies it.

The practical target is simple: future work begins with a data-only question, receives one official portable answer packet, and follows a mostly standard binding, registry, and shipment route. Only the semantics and the evidence-sensitive distinctions should remain bespoke.
