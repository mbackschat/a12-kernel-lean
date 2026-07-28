# Documentation discipline

This policy keeps semantic truth, provenance, architecture, live status, open work, and history in different owners. The canonical registry of documents, audiences, and lifecycles is [`README.md`](README.md); mandatory contributor rules remain in [`../CLAUDE.md`](../CLAUDE.md).

## Exclusive ownership

Ownership is exclusive, not merely primary. A detailed fact has one canonical owner. Another document may state only the consequence needed by its own audience and link to that owner.

Before editing documentation, classify each changed fact:

| Fact | Sole owner |
|---|---|
| Kernel behavior and static legality | the relevant project-owned [`spec/`](../spec/) clause |
| Reusable provenance and source-navigation route | [`SOURCES.md`](SOURCES.md) |
| Implemented fragment, proof/non-law state, and external-evidence status | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) |
| Retained observation inventory and claim boundary | [`EVIDENCE.md`](EVIDENCE.md) |
| Open semantic obligation, prerequisite, discriminator, or reopening trigger | [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) |
| Immediate active unit, queue, blocker, and resume command | [`PLAN.md`](PLAN.md) |
| Stable representation, semantic ownership, dependency direction, composition invariant, or accepted/rejected encoding decision | [`ARCHITECTURE.md`](ARCHITECTURE.md) |
| Durable non-obvious formalization or research lesson | [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) |
| Cross-project semantic reconciliation state | [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) |
| Test method and executable gate contract | [`TESTING.md`](TESTING.md) |
| Public process, artifact, consumer, product, or release contract | the exact owner named in [`README.md`](README.md#canonical-ownership-registry) |

The update trigger is also an exclusion rule. If a document's owned responsibility did not change, leave it untouched. A routine semantic capsule normally updates the implementation map, shrinks or changes the selected gap only when its open set changed, and advances the plan; it does not automatically update architecture, sources, findings, README, or public contracts.

Adding a fact to its owner requires deleting or replacing any displaced detailed copy in the same change. Correcting a stale sentence is always in scope, but the correction should point to the owner instead of creating another maintained account. “Prefer links” means consequence plus link, not a shorter duplicate inventory.

## Normative semantics and implementation guidance

Project-owned [`../spec/`](../spec/) is the canonical language-neutral behavioral account and the bridge to a12-dmkits. It is never a work log, implementation map, evidence inventory, roadmap, or Lean status surface. Clearly labeled non-normative implementation notes may explain a representation constraint that follows from the clause, but Lean-specific workflow and proof guidance belongs under `docs/`.

A verified behavioral correction, narrowing, or extension updates the canonical clause. If it originated here and still needs a12-dmkits reconciliation, the same change adds or updates the matching entry in [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md). An inbound correction already committed and reviewed in a12-dmkits is recorded as provenance in [`SOURCES.md`](SOURCES.md), not sent back as a new outbound request.

## Update procedure

For every documentation change:

1. Name the changed fact and its canonical owner.
2. Apply only the exact triggers below; “not triggered” means the document must remain unchanged.
3. Search the live documentation for detailed copies of the changed fact.
4. Replace stale copies with the local consequence and a link, or delete them when they add no local consequence.
5. Delete completed work from volatile owners. Git history is the work log and archive unless an immutable public or reconciliation record has a distinct continuing audience.
6. Verify links, stable anchors, and the document's query contract before commit.

The capsule closure assessment in [`TESTING.md`](TESTING.md#same-context-capsule-closure-assessment) must reject an unnecessary document touch, a duplicated detailed fact, an appended completed narrative in an open-only owner, and a new paragraph that leaves superseded prose in place.

## Same-change triggers

- Change [`ARCHITECTURE.md`](ARCHITECTURE.md) only for a representation or semantic-ownership boundary, dependency direction, composition invariant, or adopted/rejected encoding alternative. A new module or a wider implemented family is not by itself architecture.
- Change [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) when executable, proof, non-law, protocol, or evidence support changes.
- Change [`SOURCES.md`](SOURCES.md) only when a reusable provenance checkpoint, authoritative source locus, or drill route changes. Capsule-specific source narratives and review chronology stay in working context and Git history.
- Change [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) only when the open set, prerequisite, discriminator, consumer consequence, evidence need, or reopening trigger changes. Delete a completed entry; never append a shipped-status narrative.
- Change [`PLAN.md`](PLAN.md) only for current resumption state. Completed-unit narratives, broad backlog, and durable findings do not belong there.
- Change [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) only for a durable non-obvious lesson or a visible correction to an existing finding.
- Change [`EVIDENCE.md`](EVIDENCE.md) only for retained observations, provenance, projections, replay, or claim limits.
- Change [`TESTING.md`](TESTING.md) only for test layers, executable gates, assurance cadence, or contributor test method.
- Change a public process, artifact, consumer, product, release, or formalization document only when the responsibility assigned to it by [`README.md`](README.md#canonical-ownership-registry) changes.
- Change the top-level [`README.md`](../README.md) only for a user-visible purpose, qualitative status, quick-start, or navigation change. Change this registry when a document is added, removed, renamed, or its audience/lifecycle/ownership changes.

## Intentional historical records

[`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) and [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) are the only append-preserving live records. Findings retain stable IDs and visible corrections. Reconciliation entries retain stable IDs and terminal dispositions. Neither may absorb routine status, source-review narrative, or a second copy of the spec.

Capability implementation kits may repeat the minimum semantics and procedure required to remain self-contained for their external audience. That exception does not authorize copied live counts, roadmaps, or provenance histories. Files under [`archived/`](archived/) are immutable historical records; correct live owners instead of silently rewriting an archive.

## Scale and consolidation

Document size is a symptom, not the ownership test. Consolidate before extending a live non-ledger document when it has acquired a second lifecycle, repeats another owner's detailed inventory, contains completed chronology in a current-state section, or requires readers to reconcile several descriptions of the same fact.

**Live-map usability invariant:** after consolidation, a new agent must be able to answer “what exists, where is its primary owner, how certain is it, and what remains?” from the current documentation without Git archaeology. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) therefore keeps capability-level lookup records with the implemented boundary, narrowest useful owner, internal and external assurance, and a link to the live remainder. Git history may replace chronology and superseded reasoning; it may not replace a current capability, assurance distinction, source route, or open obligation. A smaller file that forces broad repository search or historical reconstruction is a failed consolidation.

The safe consolidation order is harvest, redirect, delete:

1. move every unique live fact to its canonical owner;
2. replace legitimate secondary uses with a local consequence and link;
3. delete copied status, source history, and completed narrative;
4. preserve stable anchors or migrate every incoming link in the same change.

Query contracts and stable headings improve navigation; they do not justify accumulation. Do not create a second index, summary document, metrics file, or governance report to compensate for an overgrown owner.

## Markdown and links

Write one Markdown paragraph per line and do not hard-wrap prose. Reference Markdown files with regular relative links. Prefer stable semantic, finding, mechanism, and public-contract anchors over copied prose.
