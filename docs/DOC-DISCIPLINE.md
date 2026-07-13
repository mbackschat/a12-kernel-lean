# Documentation discipline

This project adopts the useful a12-dmkits documentation principles in [`../../a12-rulekit/docs/DOC-DISCIPLINE.md`](../../a12-rulekit/docs/DOC-DISCIPLINE.md), adapted to a Lean formalization and the repository's stricter write boundary. The purpose is to keep semantic truth, settled knowledge, current structure, live status, and future intent from collapsing into one document that inevitably drifts.

## Document roles

- [`../spec/`](../spec/) is read-only language-neutral semantic input. It plays the same consulted-upstream role for this repository that a12-kernel's merged BA/dev documentation plays for a12-dmkits; it is not a work log, findings ledger, implementation map, or roadmap.
- [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) owns the stable project argument, goals, evidence doctrine, success gates, durable milestones, and long-term outlook.
- [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) owns the proposed releasable product boundary, public claims and nonclaims, integration shape, release gates, staged product progression, and user-facing documentation strategy until that proposal is explicitly adopted or replaced.
- [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md) owns the production artifact contract, version binding, platform qualification, reproducibility, packaging, signing, release-size experiments, publication, and rollback. It records how a release would be engineered without adopting the product proposal or redefining semantic support.
- [`PLAN.md`](PLAN.md) owns the resumable current checkpoint, preserved observations, immediate continuation order, and session-resume procedure. It is operational state, not a second roadmap.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) owns the current Lean structure, representations, dependency boundaries, and adopted/rejected encoding decisions. It describes what exists, not a feature-status board.
- [`PROTOCOL.md`](PROTOCOL.md) owns the normalized reference process and JSON contract, including invocation, exit behavior, closed wire shapes, diagnostics, limits, support-manifest interpretation, and runnable sample data.
- [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) owns the independent-interpreter handover contract, implementation-capsule contents, research-closure and cold-implementer gates, downstream playbook, and disagreement protocol.
- [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) owns Lean's role, theorem and trust contract, external case studies, and publication strategy.
- [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) owns durable, numbered findings about this project's formalization treatment and research conclusions. A finding is settled knowledge and rationale, not an open task.
- [`EVIDENCE.md`](EVIDENCE.md) owns the retained external-observation format, projection boundary, replay guarantees, and evidence-specific limitations.
- [`TESTING.md`](TESTING.md) owns the red/green workflow, executable-example conventions, proof/trust harness, external replay method, and final verification gate.
- [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) is the live join from the read-only `§n` taxonomy to Lean definitions, proofs/counterexamples, kernel evidence, status, and exact support boundaries.
- [`SOURCES.md`](SOURCES.md) owns the drill path into the read-only kernel and a12-dmkits evidence layers.
- [`README.md`](README.md) indexes the documentation set and its ownership rules; the top-level [`../README.md`](../README.md) remains the concise project front door.

## Finding lifecycle

Record a non-obvious formalization or research conclusion in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) before relying on it across several changes. Give it a stable `LF<n>` identifier, the date, its semantic section(s), its evidence basis, the claim, its Lean treatment, and its limits. Findings are not deleted or renumbered; if later evidence corrects one, amend it visibly and link the correcting finding.

Kernel-behavior discoveries are not invented or canonized here. They remain grounded in the read-only `spec/`, kernel documentation/source, and a12-dmkits' findings and real-kernel differentials. `LEAN-FINDINGS.md` records what this project learned from those sources and how the Lean theory should represent or bound it.

Open work does not belong in the findings ledger. Until a separate gaps ledger is justified by volume, current open obligations and `external evidence pending` states live in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), immediate sequencing lives in [`PLAN.md`](PLAN.md), durable milestone and reevaluation criteria live in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), and proposed release progression lives in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md).

## Same-change update triggers

- A new or changed Lean module, representation, or dependency boundary updates [`ARCHITECTURE.md`](ARCHITECTURE.md).
- A changed reference-process invocation, wire shape, diagnostic, limit, manifest field, or runnable sample updates [`PROTOCOL.md`](PROTOCOL.md).
- A changed implementer handover artifact, research-closure requirement, cold-implementer test, downstream conformance playbook, or missing-semantics escalation path updates [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md).
- A new supported semantic clause updates [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) with its exact fragment, proof/counterexample state, kernel version, and external evidence status.
- A non-obvious mechanism, research conclusion, or rejected alternative updates [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).
- A changed evidence format, capture provenance, or replay boundary updates [`EVIDENCE.md`](EVIDENCE.md).
- A changed test layer, Lean example convention, trust gate, or final verification workflow updates [`TESTING.md`](TESTING.md).
- A changed stable goal, evidence rule, durable milestone, success criterion, or long-term project potential updates [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md).
- A changed proposed release artifact, public claim, integration boundary, release gate, product stage, or user-facing product-documentation strategy updates [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md).
- A changed production artifact format, version binding, supported platform, reproducibility rule, packaging/signing/SBOM process, size policy, publication process, or rollback rule updates [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md).
- A changed current checkpoint, preserved observation, immediate step order, or resume instruction updates [`PLAN.md`](PLAN.md).
- A changed theorem/trust discipline or external-study conclusion updates [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md).
- A new, renamed, or removed document updates [`README.md`](README.md) in the same change.
- A user-visible status change updates the top-level [`../README.md`](../README.md) without turning it into a detailed status table.

## Evidence discipline

Kernel differential testing is the empirical backbone. Internal examples are executable semantic locks, and proofs establish universal consequences of the Lean definitions, but neither is portable evidence of correspondence with the real kernel. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) must mark a fragment `external evidence pending` until retained, versioned kernel observations for that fragment are replayable in this repository.

The a12-dmkits interpreter is a clean-room peer used for triangulation and finding disagreements. It is never the oracle. A kernel mismatch changes the Lean definition or opens an explicit divergence; it is never hidden by relaxing an expected result.

## Markdown and links

Write one Markdown paragraph per line and do not hard-wrap prose. Link every referenced Markdown document with a regular relative Markdown link. Prefer stable document anchors and theorem names over copied prose, and avoid duplicating a detailed inventory that already has one owning surface.
