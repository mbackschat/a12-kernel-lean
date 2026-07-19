# Documentation discipline

This project adopts the useful a12-dmkits documentation principles in [`../../a12-rulekit/docs/DOC-DISCIPLINE.md`](../../a12-rulekit/docs/DOC-DISCIPLINE.md), adapted to a Lean formalization and the repository's stricter write boundary. The purpose is to keep semantic truth, settled knowledge, current structure, live status, and future intent from collapsing into one document that inevitably drifts.

## Registry and document creation

[`README.md`](README.md) is the sole registry of document audiences, lifecycles, and canonical ownership. Do not reproduce that complete catalog here, in the top-level README, in [`CLAUDE.md`](../CLAUDE.md), or in a project charter. Those surfaces link to the registry and retain only their local operational consequence.

Create a new document only when it has a distinct audience, a fact set not already owned elsewhere, and a lifecycle that would make a section in the existing owner misleading or unwieldy. Otherwise add a section to the current owner. The stable reader-facing paths listed in [`README.md`](README.md#stable-reader-facing-paths) are a documentation interface: moving, renaming, or dissolving one requires an explicit decision and same-change link migration.

Project-owned [`../spec/`](../spec/) is the canonical language-neutral semantic body and the bridge to a12-dmkits. It is never a work log, findings ledger, implementation map, roadmap, evidence inventory, or destination for Lean-specific status.

## Volatility and history

Exact live state belongs only in its volatile owner. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns detailed support/proof/evidence status; [`EVIDENCE.md`](EVIDENCE.md) owns the retained observation inventory; [`PLAN.md`](PLAN.md) owns immediate sequencing; capability kits own their historical consumer experiments. The top-level [`README.md`](../README.md) carries only a qualitative summary and links.

[`PLAN.md`](PLAN.md) is not an archive. Keep only a concise verified baseline, the active objective, ordered next actions, blockers or guardrails, and the minimal resume procedure. Move durable results to their owning design, evidence, implementation, release, or capability document and rely on Git history for completed sequences and old revisions.

## Finding lifecycle

Record a non-obvious formalization or research conclusion in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) before relying on it across several changes. Give it a stable `LF<n>` identifier, the date, its semantic section(s), its evidence basis, the claim, its Lean treatment, and its limits. Findings are not deleted or renumbered; if later evidence corrects one, amend it visibly and link the correcting finding.

Kernel-behavior discoveries are grounded in the real kernel, its documentation/source, retained observations, and a12-dmkits' findings and real-kernel differentials. Once verified, their language-neutral account is canonized in the relevant `spec/` clause and queued for a12-dmkits reconciliation in [`A12-DMKITS-SPEC-SYNC.md`](A12-DMKITS-SPEC-SYNC.md). [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) records the separate formalization consequence: what this project learned from those sources and how the Lean theory should represent or bound it.

Open work does not belong in the findings ledger. Until a separate gaps ledger is justified by volume, current open obligations and `external evidence pending` states live in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), immediate sequencing lives in [`PLAN.md`](PLAN.md), durable milestone and reevaluation criteria live in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), and proposed release progression lives in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md).

## Same-change update triggers

- A new or changed Lean module, representation, or dependency boundary updates [`ARCHITECTURE.md`](ARCHITECTURE.md).
- A changed reference-process invocation, wire shape, diagnostic, limit, manifest field, reference-semantics identity or detection rule, compatibility lineage, or runnable sample updates [`PROTOCOL.md`](PROTOCOL.md); immutable-versus-current artifact consequences update [`ARTIFACTS.md`](ARTIFACTS.md) in the same change.
- A changed semantic-shipment artifact, consumer task/language profile, research-closure requirement, cold-consumer test, downstream qualification playbook, or missing-semantics escalation path updates [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md).
- A changed capability-specific semantic handover, descriptor, suite, candidate tool, evidence mapping, law/non-law guidance, cold-test outcome, or release gap updates its owning implementation kit: currently [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) or [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md).
- A new supported semantic clause updates [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) with its exact fragment, proof/counterexample state, kernel version, and external evidence status.
- A non-obvious mechanism, research conclusion, or rejected alternative updates [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).
- A changed evidence format, capture provenance, or replay boundary updates [`EVIDENCE.md`](EVIDENCE.md).
- A verified behavioral correction, narrowing, or extension updates its canonical `spec/` clause and adds or updates the matching entry in [`A12-DMKITS-SPEC-SYNC.md`](A12-DMKITS-SPEC-SYNC.md) in the same change. Update [`SOURCES.md`](SOURCES.md) only when the provenance or drill path changes; add a numbered Lean finding when the formalization rationale is non-obvious and durable.
- A concrete a12-dmkits improvement first records the local semantic, evidence, or process gap in its existing owner, with the audited upstream revision, exact source links, broken or missing invariant, recommendation, compatibility consequence, and separating acceptance check. Prepare the upstream request using the [`upstream engagement rule`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule); create a temporary registered cross-project proposal only for a coherent capability with its own architecture and acceptance lifecycle. The user transfers the request to the a12-dmkits agent; this project never implements it in a sibling or copied worktree. Once upstream work is reported in progress, leave that handoff stable, do not send a parallel request, and reconcile only after the user supplies the committed revision and disposition. Move durable results into their semantic, evidence, testing, source, architecture, or plan owner, then delete the completed temporary handoff and rely on Git history. The compact accepted/superseded entries in [`A12-DMKITS-SPEC-SYNC.md`](A12-DMKITS-SPEC-SYNC.md) are the deliberate exception: they remain as cross-project semantic reconciliation receipts. No temporary handoff owns a12-dmkits' live status.
- A changed role, ownership boundary, generation policy, versioning rule, retained-versus-transient policy, or drift mechanism for `evidence/`, `reference/`, `examples/`, or `qualification/` updates [`ARTIFACTS.md`](ARTIFACTS.md).
- A changed test layer, Lean example convention, trust gate, or final verification workflow updates [`TESTING.md`](TESTING.md).
- A changed stable goal, evidence rule, durable milestone, success criterion, or long-term project potential updates [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md).
- A changed proposed release artifact, public claim, integration boundary, release gate, product stage, or user-facing product-documentation strategy updates [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md).
- A changed general consumer-task taxonomy starts in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) and updates its reader-facing projection in [`USE-CASES.md`](USE-CASES.md); a changed user-facing account of Lean's contribution or limits updates [`USE-CASES.md`](USE-CASES.md) without redefining the taxonomy there.
- A changed production artifact format, version binding, supported platform, reproducibility rule, packaging/signing/SBOM process, size policy, publication process, or rollback rule updates [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md).
- A changed current checkpoint, preserved observation, immediate step order, or resume instruction updates [`PLAN.md`](PLAN.md).
- A changed theorem/trust discipline or external-study conclusion updates [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md).
- A new, renamed, or removed document updates [`README.md`](README.md) in the same change.
- A user-visible status change updates the top-level [`../README.md`](../README.md) without turning it into a detailed status table.

## Evidence discipline

[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#artifact-and-authority-model) owns the differential doctrine and source roles; [`EVIDENCE.md`](EVIDENCE.md) owns the exact retained observations and claim boundary. The documentation consequence is simple: internal examples and proofs are never labeled kernel evidence, the a12-dmkits interpreter is never labeled the oracle, and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) marks a fragment `external evidence pending` until retained versioned kernel observations are replayable here. A mismatch changes the theory or opens an explicit divergence; it never justifies relaxing an expected result.

## Markdown and links

Write one Markdown paragraph per line and do not hard-wrap prose. Link every referenced Markdown document with a regular relative Markdown link. Prefer stable document anchors and theorem names over copied prose, and avoid duplicating a detailed inventory that already has one owning surface.
