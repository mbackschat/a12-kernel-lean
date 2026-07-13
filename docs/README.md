# a12-kernel-lean documentation

This is the canonical index and ownership map for the project's documentation. It follows the useful a12-dmkits pattern of routing each kind of knowledge to one maintained document rather than making every document repeat the same overview. Documentation lifecycle rules live in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md); repository rules that must stop an unsafe action before it happens remain in [`../CLAUDE.md`](../CLAUDE.md).

## Charter, product, release, and current plan

- **[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md)** — the stable project constitution: purpose, users, semantic and evidence boundaries, delivery-unit definition, durable milestones, success criteria, and long-term potential.
- **[`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md)** — the proposed releasable product boundary: compatibility-kit artifacts, public claims and nonclaims, integration model, release gates, staged progression, and user-facing documentation as a regression consumer. It is a proposal until explicitly adopted.
- **[`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md)** — the production-release engineering contract and experiment log: artifact qualification, version identity, platform matrix, reproducibility, packaging, signing, size work, publication, rollback, and open blockers. It does not itself adopt a release.
- **[`PLAN.md`](PLAN.md)** — the resumable working checkpoint: the landed verification boundary, next delivery unit, immediate continuation order, and resume procedure. It may change often and does not redefine the charter or product direction.

## Semantics, formalization, and implementation

- **[`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md)** — why Lean, what it can and cannot establish, audited project studies, theorem and trust discipline, proof opportunities, publication-tool comparison, and adoption criteria.
- **[`ARCHITECTURE.md`](ARCHITECTURE.md)** — the Lean structure that exists now: representations, module boundaries, dependency direction, and adopted or rejected design choices.
- **[`PROTOCOL.md`](PROTOCOL.md)** — the exact normalized reference-process contract: invocation, closed JSON request and response algebra, diagnostics, limits, support manifest, and regression-checked sample data.
- **[`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md)** — the language-neutral handover contract for independent interpreters: implementation-capsule contents, research closure, cold implementation, downstream conformance, and missing-semantics escalation.
- **[`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md)** — the first concrete implementation capsule: exact one-star captured-outer model and algorithm, worked traces, evidence/law/non-law maps, Rust playbook, candidate suite commands, and open release boundary.
- **[`LEAN-FINDINGS.md`](LEAN-FINDINGS.md)** — durable numbered conclusions and rationale learned while formalizing the semantics and studying local evidence.
- **[`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md)** — the live `§n`-to-Lean map: implemented fragments, theorem and counterexample coverage, retained kernel evidence, exact support boundaries, and open adequacy obligations.

## Evidence, testing, and sources

- **[`EVIDENCE.md`](EVIDENCE.md)** — the retained kernel-observation contract: portable formats, focused Lean projections, provenance, replay guarantees, and external-adequacy limits.
- **[`TESTING.md`](TESTING.md)** — the red/green Lean workflow, executable conformance harness, proof and trust gates, differential replay method, and final verification checklist.
- **[`SOURCES.md`](SOURCES.md)** — the drill path from a semantic topic to the read-only kernel and a12-dmkits knowledge layers, including the local `a12-rulekit/` checkout's documentation, interpreter, adapter, corpus, and differential locks.
- **[`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md)** — document lifecycle, finding rules, same-change update triggers, evidence discipline, and Markdown conventions.

## Read-only semantic input

The language-neutral semantic body lives under [`../spec/`](../spec/) and is treated as read-only. Start with [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md), then follow the numbered deep-dives. For this repository, `spec/` has the same consulted-upstream role that a12-kernel's merged BA/developer documentation has for a12-dmkits: it supplies semantic input, while new Lean findings, implementation state, evidence state, and plans are recorded under `docs/`.

## Canonical ownership map

| Knowledge or artifact | Owning surface |
|---|---|
| Repository entry point, concise current status, and build command | [`../README.md`](../README.md) |
| Operational hard rules and mandatory contributor workflow | [`../CLAUDE.md`](../CLAUDE.md) |
| Language-neutral semantic baseline | Read-only [`../spec/`](../spec/) |
| Stable mission, audience, authority model, evidence doctrine, durable milestones, and long-term potential | [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) |
| Proposed release artifacts, public product claim, integration boundary, release gates, and product progression | [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) |
| Artifact qualification, platform support, reproducibility, packaging, signing, size experiments, publication, and rollback | [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md) |
| Current checkpoint, immediate sequencing, and session-resume state | [`PLAN.md`](PLAN.md) |
| Lean's role, theorem/trust contract, external project studies, and publication strategy | [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) |
| Current module and representation design | [`ARCHITECTURE.md`](ARCHITECTURE.md) |
| Normalized process/JSON contract, diagnostics, limits, manifest, and runnable samples | [`PROTOCOL.md`](PROTOCOL.md) |
| Independent-interpreter handover, research-closure and cold-implementer gates, and downstream playbook | [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) |
| Concrete `single-group-correlation-v1` implementer material, algorithm, tools, and capsule-specific gaps | [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) |
| Settled formalization conclusions and rationale | [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) |
| Live semantic coverage and open evidence/proof obligations | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) |
| Retained external-observation and replay contract | [`EVIDENCE.md`](EVIDENCE.md) |
| Test methodology and verification gates | [`TESTING.md`](TESTING.md) |
| Provenance and source drill paths | [`SOURCES.md`](SOURCES.md) |
| Documentation lifecycle and update triggers | [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md) |
| Checked or generated user-facing publication rendered from maintained sources | Tool chosen for the artifact being explained; publication view only, never an additional authority |

When a fact is useful elsewhere, link to its owner and add only the local consequence. Do not maintain parallel inventories, roadmaps, support claims, or semantic explanations in several files.
