# a12-kernel-lean documentation

This is the sole documentation registry: it gives reader routes, identifies the stable reader-facing paths, and assigns one owner and lifecycle to every maintained document. Documentation policy lives in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md); mandatory repository rules remain in [`../CLAUDE.md`](../CLAUDE.md).

## Choose a route

| Reader or task | Start here | Continue with |
|---|---|---|
| New reader | Top-level [`README.md`](../README.md) | [`USE-CASES.md`](USE-CASES.md) for potential, then [`ARTIFACTS.md`](ARTIFACTS.md) for repository data |
| Consumer-probe designer | [`USE-CASES.md`](USE-CASES.md#consumer-probes-first) | Select a task profile and maturity boundary in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#consumer-probes-before-shipment), then check prerequisites in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) |
| Reference CLI user | [`PROTOCOL.md`](PROTOCOL.md) | Runnable [`examples/reference-cli/`](../examples/reference-cli/) and current 0.3.0/V2 support from `--manifest` |
| Independent evaluator implementer | [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) | The current 0.3.0/V2 [`flat empty-logic kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) or [`correlation kit`](IMPLEMENTER-KIT-CORRELATION.md) and controls from [`PROTOCOL.md`](PROTOCOL.md) |
| Future importer or rule-tool designer | [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#task-profiles) | [`USE-CASES.md`](USE-CASES.md); no importer or refactoring shipment is implemented yet |
| Future satisfiability or SMT maintainer | [`SMT-SOLVER-SUPPORT-PROPOSAL.md`](SMT-SOLVER-SUPPORT-PROPOSAL.md) | [`USE-CASES.md`](USE-CASES.md#5-analyze) and [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#task-profiles); no analysis shipment or solver dependency is implemented yet |
| Product stakeholder | [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) | [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) for the adopted constitution and [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md) for release engineering |
| Reader evaluating Lean | [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) | [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), then [`ARCHITECTURE.md`](ARCHITECTURE.md) |
| Semantics contributor | [`../CLAUDE.md`](../CLAUDE.md) | Project-owned [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md), provenance in [`SOURCES.md`](SOURCES.md), outbound changes in [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md), then [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and [`TESTING.md`](TESTING.md) |
| Resuming agent | [`../CLAUDE.md`](../CLAUDE.md) | Read [`PLAN.md`](PLAN.md), then the relevant gate in [`TESTING.md`](TESTING.md) |
| Evidence or assurance reviewer | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | [`EVIDENCE.md`](EVIDENCE.md), [`TESTING.md`](TESTING.md), [`SOURCES.md`](SOURCES.md), and [`ARTIFACTS.md`](ARTIFACTS.md) |
| Historical 0.2.0/V1 or Rust experiment reviewer | [`archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md`](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md) | Use its exact Git recovery revisions; no retired artifact or qualification command remains live |
| Historical root-String raw-evidence reviewer | [`archived/STRING-COMPUTATION-RAW-EVIDENCE.md`](archived/STRING-COMPUTATION-RAW-EVIDENCE.md) | Use its exact agreement revision, Git trees, and capture identities; current replay consumes only the combined compact bundle |
| Historical direct-cascade raw-evidence reviewer | [`archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md`](archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md) | Use its exact project revision, Git trees, and receipt identities; current replay consumes only the compact bundle |
| Historical validation raw-evidence reviewer | [`archived/VALIDATION-RAW-EVIDENCE.md`](archived/VALIDATION-RAW-EVIDENCE.md) | Use its dual-path agreement checkpoint, source digests, and Git recovery identities; current replay consumes only the compact validation bundle |
| a12-dmkits evidence-coordination maintainer | [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) | Use the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule), current upstream corpus/differential facilities when they fit, and a demand-driven request when they do not; the retired portable capture history lives only in a12-dmkits' [`archived proposal`](../../a12-rulekit/docs/archived/A12-DMKITS-CAPTURE-PROPOSAL.md) |
| Semantic-evidence pipeline maintainer | [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) | Follow the accepted compact-bundle boundary, assurance tiers, measured budgets, upstream engagement rule, and stop conditions |
| Historical reference/evidence simplification reviewer | [`archived/REFERENCE-AND-EVIDENCE-SIMPLIFICATION-PROPOSAL.md`](archived/REFERENCE-AND-EVIDENCE-SIMPLIFICATION-PROPOSAL.md) | Use its measured before/after estate, deletion sequence, and recovery routes; the live compact boundary is owned by [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) |

The language-neutral semantic body under [`../spec/`](../spec/) is owned by this project and is the bridge to a12-dmkits. Start with [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) and follow its numbered deep-dives. Verified kernel behavior belongs in the relevant spec clause; every correction, narrowing, or addition is queued in [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md). Lean representations, proof findings, implementation state, evidence state, and plans remain under `docs/`.

## Stable reader-facing paths

The following names and locations form the intentional reader-facing surface. Their content evolves through the ownership rules below, but they should not be moved, renamed, or folded into maintainer logs without an explicit documentation-interface decision:

- top-level [`README.md`](../README.md) — concise project front door and quick start;
- this [`docs/README.md`](README.md) — navigation and canonical ownership registry;
- [`USE-CASES.md`](USE-CASES.md) — approachable consumer-probe catalog, later product potential, and concrete ways Lean helps;
- [`ARTIFACTS.md`](ARTIFACTS.md) — user-facing explanation of repository artifact contents, authority, and evolution;
- [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) — adopted project constitution, full potential, and durable delivery model;
- [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) — product-stakeholder proposal and progression;
- [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) — technical evaluation of Lean's role, limits, precedents, and practices;
- [`PROTOCOL.md`](PROTOCOL.md) — public normalized process contract;
- [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) — language-neutral consumer-probe, shipment, and qualification playbook;
- [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) — current self-contained 0.3.0/V2 capability handovers.

The remaining documents are public technical or maintainer surfaces. They may be consolidated, split, or reorganized when doing so makes their single ownership clearer, provided links and stable reader paths remain intact.

## Canonical ownership registry

| Surface | Primary audience | Lifecycle | Sole ownership |
|---|---|---|---|
| [`../README.md`](../README.md) | New users | Stable entry, concise live summary | Purpose, qualitative status, quick start, and routes into this registry |
| [`../CLAUDE.md`](../CLAUDE.md) | Contributors and agents | Mandatory operational policy | Hard repository rules and required contributor workflow |
| Project-owned [`../spec/`](../spec/) | Semantics readers and cross-project maintainers | Evolving versioned bridge | Canonical language-neutral semantic body; never implementation status, Lean design, evidence inventory, or working notes |
| [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) | Contributors and stakeholders | Stable constitution | Mission, audience, authority and evidence doctrine, semantic capsules, consumer-probe lifecycle, consumer shipments, controlled-interleaving and risk-first method, coverage horizons, success criteria, and long-term potential |
| [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) | Product stakeholders | Proposal until adopted or replaced | Consumer-task taxonomy, proposed release boundary, public product claim, product gates, and progression |
| [`USE-CASES.md`](USE-CASES.md) | General users and probe designers | Stable reader guide | Reader-facing consumer-probe catalog, possible later products, and Lean's concrete contribution and limits across the general task categories |
| [`ARTIFACTS.md`](ARTIFACTS.md) | Users and reviewers | Stable lifecycle guide | Contents, authority, generation, retention, immutability, and drift policy for scenario questions, `evidence/`, `reference/`, `examples/`, and retained historical qualification records |
| [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md) | Release maintainers | Evolving engineering contract and measured experiment record | Artifact qualification, platform support, reproducibility, packaging, dependencies, signing, size experiments, publication, and rollback |
| [`PLAN.md`](PLAN.md) | Active maintainers and resuming agents | Volatile checkpoint, never an archive | Verified baseline, one active unit, compact frontier queue, parked boundaries, stop conditions, and minimal resume procedure |
| [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) | Technical readers and proof contributors | Researched guidance | Lean's role and limits, required proof spine, case studies, proof engineering, trust discipline, and publication-tool research |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | Implementers | Current-state design | Concrete Lean representations, dependency direction, module boundaries, and adopted or rejected encoding decisions |
| [`PROTOCOL.md`](PROTOCOL.md) | CLI and integration users | Versioned public contract | Invocation, wire algebra, diagnostics, limits, runtime reference-semantics detection, support-manifest interpretation, and representative runnable samples |
| [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) | Consumer-probe designers and independent consumers | Stable general contract | Consumer-probe boundary, portable shipment model, task/language profiles, research closure, cold-consumer gates, downstream playbooks, and disagreement protocol |
| [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) | Capability implementers | Current 0.3.0/V2 development handover | Exact flat capability, decision procedure, laws/non-laws, evidence limits, candidate workflow, and capsule-specific gaps |
| [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) | Capability implementers and consumer-probe reviewers | Current 0.3.0/V2 development handover | Exact one-star correlation capability, algorithm, evidence/law/non-law map, accepted fresh Rust runtime-probe result and identities, candidate workflow, and capsule-specific gaps |
| [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) | Semantics and proof maintainers | Durable corrected findings | Non-obvious numbered mechanisms, representation choices, semantic surprises, rejected stronger accounts, evidence basis, Lean consequence, and limits; never routine closure or live status |
| [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | Maintainers and reviewers | Live status | Sole detailed map of implemented fragments, proof/counterexample coverage, external evidence, support boundaries, and open adequacy obligations |
| [`EVIDENCE.md`](EVIDENCE.md) | Evidence reviewers | Versioned empirical inventory | Exact retained observations, provenance, projection and replay boundary, current evidence coverage, and claim limits |
| [`TESTING.md`](TESTING.md) | Contributors | Maintained methodology | Red/green workflow, executable and bounded candidate-process mechanics, proof/trust gates, evidence replay procedure, historical Rust experiment limits, and final verification commands |
| [`SOURCES.md`](SOURCES.md) | Researchers and maintainers | Maintained drill map | Provenance and navigation from semantic areas to kernel and a12-dmkits sources; never a second semantic-delta ledger |
| [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) | Cross-project semantics maintainers | Maintained reconciliation ledger; pending entries form the outbound queue | Same-change transport record for project-owned spec corrections and additions, handoff prompts, reviewed upstream revision receipts, and per-entry dispositions; never a second semantic specification |
| [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) | a12-kernel-lean architecture and evidence maintainers | Accepted operating contract | Compact retained-observation boundary, assurance tiers, measured line budgets, completed capture-V1 retirement, demand-driven future engagement, and stop criteria; current implementation facts remain in `ARCHITECTURE.md`, `TESTING.md`, `ARTIFACTS.md`, and `IMPLEMENTATION-MAP.md` |
| [`SMT-SOLVER-SUPPORT-PROPOSAL.md`](SMT-SOLVER-SUPPORT-PROPOSAL.md) | Future Analyze/Synthesize maintainers and cross-project integrators | Proposal until adopted, replaced, or graduated into concrete task-profile owners | Query taxonomy, accepted-document contract, hybrid Lean/SMT architecture, trust and bound classes, staged support profiles, early Lean design invariants, and a12-dmkits engagement gates; never current implementation state |
| [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md) | Documentation maintainers | Stable policy | Document creation criteria, history/volatility rules, findings lifecycle, same-change triggers, evidence documentation discipline, and Markdown conventions |
| [`archived/SEMANTIC-WORK-LOG-2026-07.md`](archived/SEMANTIC-WORK-LOG-2026-07.md) | Historical reviewers | Immutable completed-work archive | July 2026 completed semantic-unit and risk-audit narratives removed from the live plan; never current coverage or continuation state |

When a fact is useful elsewhere, link to its owner and add only the local consequence. Intentional repetition is limited to reader orientation and self-contained capability handovers; exact live counts, revision histories, support matrices, roadmaps, and detailed inventories must have only one owner.
