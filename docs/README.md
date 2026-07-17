# a12-kernel-lean documentation

This is the sole documentation registry: it gives reader routes, identifies the stable reader-facing paths, and assigns one owner and lifecycle to every maintained document. Documentation policy lives in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md); mandatory repository rules remain in [`../CLAUDE.md`](../CLAUDE.md).

## Choose a route

| Reader or task | Start here | Continue with |
|---|---|---|
| New reader | Top-level [`README.md`](../README.md) | [`USE-CASES.md`](USE-CASES.md) for potential, then [`ARTIFACTS.md`](ARTIFACTS.md) for repository data |
| Reference CLI user | [`PROTOCOL.md`](PROTOCOL.md) | Runnable [`examples/reference-cli/`](../examples/reference-cli/), current support from `--manifest`, and the 0.2.0 → 0.3.0 compatibility lineage |
| Independent evaluator implementer | [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) | The frozen 0.2.0 [`flat empty-logic kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) or [`correlation kit`](IMPLEMENTER-KIT-CORRELATION.md), then current v2 controls from [`PROTOCOL.md`](PROTOCOL.md) |
| Future importer or rule-tool designer | [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#task-profiles) | [`USE-CASES.md`](USE-CASES.md); no importer or refactoring shipment is implemented yet |
| Product stakeholder | [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) | [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) for the adopted constitution and [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md) for release engineering |
| Reader evaluating Lean | [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) | [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), then [`ARCHITECTURE.md`](ARCHITECTURE.md) |
| Semantics contributor | [`../CLAUDE.md`](../CLAUDE.md) | Read-only [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md), writable deltas in [`SOURCES.md`](SOURCES.md), then [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and [`TESTING.md`](TESTING.md) |
| Resuming agent | [`../CLAUDE.md`](../CLAUDE.md) | [`PLAN.md`](PLAN.md), then the relevant gate in [`TESTING.md`](TESTING.md) |
| Evidence or assurance reviewer | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | [`EVIDENCE.md`](EVIDENCE.md), [`TESTING.md`](TESTING.md), [`SOURCES.md`](SOURCES.md), and [`ARTIFACTS.md`](ARTIFACTS.md) |
| Mutation-qualification maintainer or reviewer | [`TESTING.md`](TESTING.md) | [`ARCHITECTURE.md`](ARCHITECTURE.md) for the source boundary, [`ARTIFACTS.md`](ARTIFACTS.md) for packet and record lifecycle, then the capability-specific [`flat kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) |
| Generated-differential maintainer or reviewer | [`TESTING.md`](TESTING.md#bounded-generated-lean-account-differential) | [`ARCHITECTURE.md`](ARCHITECTURE.md) for process/trust boundaries, [`ARTIFACTS.md`](ARTIFACTS.md#generated-differential-profile-and-result-lifecycle) for profile/result lifecycle, then the capability-specific [`flat kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#post-cold-generated-differential) |
| a12-dmkits capture or coordination maintainer | [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) | While the current handoff is open, follow [`A12-DMKITS-COMPACT-EVIDENCE-PROPOSAL.md`](A12-DMKITS-COMPACT-EVIDENCE-PROPOSAL.md); otherwise use the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule), the live upstream [`CONFORMANCE-CORPUS-SPEC.md` §15–§15g](../../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md), and the accepted [`string-direct-cascade-v1` capture](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/README.md) |
| Semantic-evidence pipeline maintainer | [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) | Follow the accepted compact-bundle migration, budgets, deletion gate, producer-side consolidation, and stop conditions |

The language-neutral semantic body under [`../spec/`](../spec/) is read-only upstream input. Start with [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) and follow its numbered deep-dives. New Lean findings, implementation state, evidence state, and plans belong under `docs/`, not `spec/`.

## Stable reader-facing paths

The following names and locations form the intentional reader-facing surface. Their content evolves through the ownership rules below, but they should not be moved, renamed, or folded into maintainer logs without an explicit documentation-interface decision:

- top-level [`README.md`](../README.md) — concise project front door and quick start;
- this [`docs/README.md`](README.md) — navigation and canonical ownership registry;
- [`USE-CASES.md`](USE-CASES.md) — approachable potential and concrete ways Lean helps;
- [`ARTIFACTS.md`](ARTIFACTS.md) — user-facing explanation of repository artifact contents, authority, and evolution;
- [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) — adopted project constitution, full potential, and durable delivery model;
- [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) — product-stakeholder proposal and progression;
- [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) — technical evaluation of Lean's role, limits, precedents, and practices;
- [`PROTOCOL.md`](PROTOCOL.md) — public normalized process contract;
- [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) — language-neutral consumer and qualification playbook;
- [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) — self-contained frozen 0.2.0 capability handovers.

The remaining documents are public technical or maintainer surfaces. They may be consolidated, split, or reorganized when doing so makes their single ownership clearer, provided links and stable reader paths remain intact.

## Canonical ownership registry

| Surface | Primary audience | Lifecycle | Sole ownership |
|---|---|---|---|
| [`../README.md`](../README.md) | New users | Stable entry, concise live summary | Purpose, qualitative status, quick start, and routes into this registry |
| [`../CLAUDE.md`](../CLAUDE.md) | Contributors and agents | Mandatory operational policy | Hard repository rules and required contributor workflow |
| Read-only [`../spec/`](../spec/) | Semantics readers | Upstream input | Language-neutral semantic baseline; never implementation status or working notes |
| [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) | Contributors and stakeholders | Stable constitution | Mission, audience, authority and evidence doctrine, semantic capsules, consumer shipments, durable milestones, success criteria, and long-term potential |
| [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) | Product stakeholders | Proposal until adopted or replaced | Consumer-task taxonomy, proposed release boundary, public product claim, product gates, and progression |
| [`USE-CASES.md`](USE-CASES.md) | General users | Stable reader guide | Reader-facing projection of potential categories and Lean's concrete contribution and limits |
| [`ARTIFACTS.md`](ARTIFACTS.md) | Users and reviewers | Stable lifecycle guide | Contents, authority, generation, retention, immutability, and drift policy for scenario questions, `evidence/`, `reference/`, `examples/`, mutation packets/results, and generated-differential profiles/receipts |
| [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md) | Release maintainers | Evolving engineering contract and measured experiment record | Artifact qualification, platform support, reproducibility, packaging, dependencies, signing, size experiments, publication, and rollback |
| [`PLAN.md`](PLAN.md) | Active maintainers and resuming agents | Volatile checkpoint, never an archive | Current verified baseline summary, active objective, immediate order, blockers, and minimal resume procedure |
| [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) | Technical readers and proof contributors | Researched guidance | Lean's role and limits, required proof spine, case studies, proof engineering, trust discipline, and publication-tool research |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | Implementers | Current-state design | Concrete Lean representations, dependency direction, module boundaries, and adopted or rejected encoding decisions |
| [`PROTOCOL.md`](PROTOCOL.md) | CLI and integration users | Versioned public contract | Invocation, wire algebra, diagnostics, limits, runtime reference-semantics detection, support-manifest interpretation, and representative runnable samples |
| [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) | Independent consumers | Stable general contract | Portable shipment model, task/language profiles, research closure, cold-consumer gates, downstream playbooks, and disagreement protocol |
| [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) | Capability implementers | Frozen 0.2.0 development handover and experiment record | Exact flat capability, decision procedure, laws/non-laws, evidence limits, cold-test outcome, and capsule-specific gaps |
| [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) | Capability implementers | Frozen 0.2.0 development handover | Exact one-star correlation capability, algorithm, evidence/law/non-law map, candidate workflow, and capsule-specific gaps |
| [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) | Semantics and proof maintainers | Append-only corrected findings | Durable numbered mechanisms, rationale, evidence basis, Lean consequence, and limits; never live task status |
| [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | Maintainers and reviewers | Live status | Sole detailed map of implemented fragments, proof/counterexample coverage, external evidence, support boundaries, and open adequacy obligations |
| [`EVIDENCE.md`](EVIDENCE.md) | Evidence reviewers | Versioned empirical inventory | Exact retained observations, provenance, projection and replay boundary, current evidence coverage, and claim limits |
| [`TESTING.md`](TESTING.md) | Contributors | Maintained methodology | Red/green workflow, executable and process harness mechanics, bounded generated differentials, mutation-qualification packet/replay/checker mechanics, proof/trust gates, evidence replay procedure, and final verification commands |
| [`SOURCES.md`](SOURCES.md) | Researchers and maintainers | Maintained drill map | Writable navigation from semantic areas to kernel and a12-dmkits sources, plus every post-spec correction, narrowing, or extension notice and its source trail |
| [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) | a12-kernel-lean architecture and evidence maintainers | Accepted migration contract until consolidation completes | Compact producer-certified bundle boundary, assurance tiers, line budgets, direct-cascade migration/deletion gate, upstream proposal rule, frozen-V1 sunset conditions, and stop criteria; current implementation facts remain in `ARCHITECTURE.md`, `TESTING.md`, `ARTIFACTS.md`, and `IMPLEMENTATION-MAP.md` |
| [`A12-DMKITS-COMPACT-EVIDENCE-PROPOSAL.md`](A12-DMKITS-COMPACT-EVIDENCE-PROPOSAL.md) | a12-dmkits implementer and cross-project reviewer | Temporary handoff until accepted or rejected | Exact post-capture direct-cascade exporter, compact bytes, acceptance tests, handback contract, and separate capture-contract V1 retirement gate |
| [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md) | Documentation maintainers | Stable policy | Document creation criteria, history/volatility rules, findings lifecycle, same-change triggers, evidence documentation discipline, and Markdown conventions |

When a fact is useful elsewhere, link to its owner and add only the local consequence. Intentional repetition is limited to reader orientation and self-contained capability handovers; exact live counts, revision histories, support matrices, roadmaps, and detailed inventories must have only one owner.
