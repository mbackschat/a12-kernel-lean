# Documentation discipline

This policy keeps semantic truth, provenance, architecture, live status, open work, and history in different owners. The canonical registry of documents, audiences, and lifecycles is [`README.md`](README.md); mandatory contributor rules remain in [`../CLAUDE.md`](../CLAUDE.md).

## Exclusive ownership

Ownership is exclusive, not merely primary. A detailed fact has one canonical owner. Another document may state only the consequence needed by its own audience and link to that owner.

Before editing documentation, classify each changed fact:

| Fact | Sole owner |
|---|---|
| Kernel behavior and static legality | the relevant project-owned [`spec/`](../spec/) clause |
| Reusable source or measurement checkpoint, revision, route, and source-level claim limit | [`SOURCES.md`](SOURCES.md) |
| Implemented fragment, proof/non-law state, and external-evidence status | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) |
| Retained observation, artifact identity, projection, replay, and empirical claim limit | [`EVIDENCE.md`](EVIDENCE.md) |
| Open semantic obligation, prerequisite, discriminator, or reopening trigger | [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) |
| Selected action, oracle, stop condition, handoff baseline, blocker, and resume command | [`PLAN.md`](PLAN.md) |
| Stable representation, semantic ownership, dependency direction, composition invariant, or accepted/rejected encoding decision | [`ARCHITECTURE.md`](ARCHITECTURE.md) |
| Durable non-obvious formalization or research lesson | [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) |
| Cross-project semantic reconciliation state | [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) |
| Test method and executable gate contract | [`TESTING.md`](TESTING.md) |
| Public process, artifact, consumer, product, or release contract | the exact owner named in [`README.md`](README.md#canonical-ownership-registry) |

The update trigger is also an exclusion rule. If a document's owned responsibility did not change, leave it untouched. A routine semantic capsule normally updates the implementation map and changes a gap or the plan only when their owned current facts changed; it does not automatically update architecture, sources, findings, README, or public contracts.

Adding a fact to its owner requires deleting or replacing any displaced detailed copy in the same change. Correcting a stale sentence is always in scope, but the correction should point to the owner instead of creating another maintained account. “Prefer links” means consequence plus link, not a shorter duplicate inventory.

Links point from a record that needs a fact to the record that owns it. Canonical records do not maintain reverse consumer inventories. Bidirectional navigation is allowed only when both records own distinct current facts, such as a gap linking to its implemented baseline while that capability links to its open remainder.

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

Reading a source, running a gate, or completing work is not by itself a documentation trigger. A partially closed gap is split when necessary and its closed obligation is deleted. A completed gap is deleted completely.

| Event | Required owners | Conditional owners | Owners normally untouched |
|---|---|---|---|
| Select existing open work | `PLAN.md` | None | Implementation map, gaps, sources, spec |
| Add or refine an open discriminator | `SEMANTICS-GAPS.md` | `PLAN.md` only if selection or blocker changes | Implementation map, sources, spec |
| Confirm existing behavior externally | `SOURCES.md` | Implementation map if assurance changes; gap if the open set changes; plan if selection changes | Spec |
| Retain or change a replayed observation | `EVIDENCE.md` | Implementation map if calibration changes; gap if the open set changes; plan if selection changes | Sources, spec |
| Correct behavior | `spec/` plus the applicable synchronization owner | Sources for inbound provenance; implementation map, gap, or plan only when their facts change | Unrelated owners |
| Implement without new external evidence | Implementation map | Gap if an obligation closes; plan if selection changes | Sources, spec |
| Refresh a verified baseline | `PLAN.md` | None | Every other owner |

This table is a trigger contract, not a document-count quota. A unit that genuinely changes several distinct facts changes each canonical owner, but every edit remains record-local.

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

For human-facing Markdown, write natural paragraphs and do not wrap them at a cosmetic fixed column. For agent-facing operational owners, rendered readability and paragraph shape are irrelevant: choose physical lines solely for bounded retrieval, precise mutation, and unambiguous diffs. Reference Markdown files with regular relative links and prefer stable semantic, finding, mechanism, and public-contract anchors over copied prose.

### Bounded detailed records

Detailed capability, gap, plan, and provenance records use keyed bullets instead of wide table rows or omnibus prose. Compact summary tables remain allowed when every cell is a short status or link and owns no detailed prose.

- Every repeatable detailed record has one stable explicit anchor and one searchable local identifier. Its descriptive heading must not generate the same anchor.
- Singleton records such as the active plan use one fixed explicit anchor with a distinct heading slug.
- Record identifiers use the local prefixes `cap-`, `gap-`, and `src-`; they are anchors, not entries in a global registry.
- Every bullet carries one semantic claim. Keys are short, lower-case, and backtick-delimited; a key may repeat for independent claims of the same class.
- A claim line has a soft ceiling of 500 characters. Split by semantic claim, never by visual width.
- One record must be understandable in a window of at most 80 lines including its heading.
- Links target the narrowest stable owner or record anchor. Record text states current truth only; Git owns chronology unless an intentional historical owner applies.

The 500-character threshold is an agent-efficiency guard, not a readability target. Review an over-limit line for multiple claims and choose the representation that makes retrieval and mutation cheapest. Prefer a semantic split; an indivisible claim may stay on one line or use a structured continuation when that is more efficient for agents.

Implementation records answer what exists, primary owner, executable/proof/external assurance, and live remainder. Gap records contain only open obligations, prerequisites, discriminators, consumer consequences, evidence needs, blockers, and reopening triggers. `PLAN.md` is a compact resumption packet, and source records own exact revisions, routes, claims, and claim limits without reverse consumer inventories.

Query converted records directly:

```sh
rg -n '^<a id="cap-' docs/IMPLEMENTATION-MAP.md
rg -n '^<a id="gap-' docs/SEMANTICS-GAPS.md
rg -n '^<a id="src-' docs/SOURCES.md
rg -n '^- `state`:|^- `blocked-on`:|^- `reopen-when`:' docs/SEMANTICS-GAPS.md
rg -n '^- `assurance`:|^- `remains`:' docs/IMPLEMENTATION-MAP.md
```

This contract is adopted through the SG5 group-operand slice. Existing unconverted sections remain valid, and this adoption creates no repository-wide migration backlog or standing cleanup campaign. Converting another existing section requires a separate user decision.
