# Agent-efficient documentation ownership discipline

> **Status:** proposal, pending adoption, 2026-08-17. This document proposes a stricter lifecycle for the existing documentation owners and an agent-efficient Markdown record shape. It changes no current ownership, update trigger, semantic claim, or active plan. If adopted, durable policy moves into [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md), navigation changes move into [`README.md`](README.md), and this proposal is retired or narrowed to unresolved work.

## Recommendation

Preserve exclusive fact ownership. Replace the current multi-kilobyte table rows and narrative gap bullets with stable, bounded Markdown records whose fields each carry one semantic claim.

Tighten the update rules so a document changes only when its own fact changed. A semantic capsule must not update `PLAN.md` merely because work completed, `SOURCES.md` merely because evidence was consulted, or `SEMANTICS-GAPS.md` merely to narrate newly implemented state.

Adopt this through one SG5 pilot across the four volatile coordination owners, measure the result, and convert other sections only when their semantic family is next touched. Add no schema, generator, registry, linter, or second index.

## Problem statement

The current ownership model is sound in intent. Kernel behavior, provenance, implementation status, open work, and immediate sequencing have distinct owners. The failure is in the physical and lifecycle realization of that model.

Detailed Markdown tables make one capability an atomic physical line. Broad gap bullets combine implemented baseline, provenance, rejected designs, open obligations, consumer needs, and immediate sequencing. `PLAN.md` repeats completed state to explain the next step. The result is expensive for a coding agent to retrieve, edit, diff, and verify even when the semantic change is small.

### Measured baseline

The measurements below were taken at `a91a2f8` plus a clean worktree on 2026-08-17. Character counts exclude newline bytes.

| Document | Lines | Characters | Lines over 500 characters | Lines over 1,000 characters | Longest line |
|---|---:|---:|---:|---:|---:|
| [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | 316 | 110,640 | 59 | 27 | 7,913 |
| [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | 158 | 74,317 | 20 | 15 | 11,526 |
| [`PLAN.md`](PLAN.md) | 56 | 15,201 | 9 | 4 | 2,584 |
| [`SOURCES.md`](SOURCES.md) | 452 | 157,304 | 93 | 61 | 4,033 |

The last 40 commits touching these four documents or `DOC-DISCIPLINE.md` divide as follows: 14 touched one document, nine touched two, 12 touched three, and five touched four. Seventeen of 40 therefore changed at least three coordination owners.

These counts are not quality scores and do not say whether each multi-document change was necessary. They establish two independent costs: detailed records are physically indivisible lines, and 17 of 40 recent coordination changes crossed at least three owners. When one claim inside a long row changes, Git must replace the whole line, retrieval loads every adjacent claim, and truncated tool output can hide the rest of the record.

### Concrete failure modes

- **Retrieval amplification:** an `rg` match can return several thousand characters before the surrounding record is visible.
- **Edit amplification:** changing one assurance or open obligation replaces an entire table row or gap paragraph.
- **Diff ambiguity:** a one-fact change appears as deletion and addition of a large unrelated narrative.
- **Ownership drift:** secondary documents retain enough detail to become competing accounts even though the policy declares one owner.
- **Lifecycle mixing:** open-only gaps and volatile plans preserve completed-state narrative that belongs in the implementation map, provenance owner, or Git history.
- **Review loss:** truncated command output can hide a stale clause at the far end of the same physical line.
- **Merge pressure:** independent changes to different claims in one row conflict because Git sees one shared line.

Document size is only the symptom. The unit of retrieval and mutation is the root problem.

## Required outcome

An agent must be able to answer the following questions without reading a multi-kilobyte line or reconciling repeated narratives:

1. What behavior is canonical?
2. What is implemented and proved?
3. What external assurance supports that implemented boundary?
4. What exact obligation remains open?
5. What is selected now, and what command resumes it?

The answer to each question must come from one canonical owner. Other documents may carry one local consequence and a direct link, but not the detailed answer.

## Ownership contract

A semantic capsule can create several distinct facts. Exclusive ownership applies to each fact separately; it does not require every consequence of one capsule to live in one document.

| Fact type | Sole owner | Secondary representation |
|---|---|---|
| Kernel behavior or static legality | Relevant [`spec/`](../spec/) clause | One local consequence plus a link |
| Reusable source or measurement checkpoint, revision, route, and source-level claim limit | [`SOURCES.md`](SOURCES.md) | Source-assurance label plus a link |
| Retained observation, artifact identity, projection, replay, and empirical claim limit | [`EVIDENCE.md`](EVIDENCE.md) | Calibration label plus a link |
| Implemented boundary, proof status, and external-assurance status | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | Capability link only |
| Live obligation, discriminator, blocker, or reopening trigger | [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | Gap link plus the consequence needed by the caller |
| Selected action, oracle, stop condition, and resume command | [`PLAN.md`](PLAN.md) | No secondary copy |

The remaining owners in the current registry keep their existing responsibilities. This proposal does not alter `ARCHITECTURE.md`, `EVIDENCE.md`, `LEAN-FINDINGS.md`, `TESTING.md`, the synchronization ledger, public contracts, or self-contained implementer kits.

### Pointer-only secondary rule

A secondary document may state one consequence required to understand its own record and link directly to the canonical owner. It must not repeat revision history, case inventories, proof inventories, rejected designs, or the full open checklist.

If a secondary use needs more than one short claim to remain intelligible, either the canonical record is too coarse or the secondary document is assuming a second responsibility. Split the canonical record or remove the secondary narrative.

Links point from a record that needs a fact to the record that owns it. Canonical records do not maintain reverse consumer inventories. Bidirectional navigation is allowed only where both sides own distinct current facts, such as a gap linking to its implemented baseline while that capability links to its open remainder.

### Lifecycle rules

The following rules replace the habit of touching every coordination document after every capsule:

1. A new uncertainty creates or changes one gap record.
2. A measurement that confirms an existing spec clause changes `SOURCES.md`; it changes the implementation map only when external assurance for an implemented capability changed.
3. A newly retained observation changes `EVIDENCE.md`; it changes the implementation map only when calibration status for an implemented capability changed.
4. A behavioral correction changes `spec/` and follows the existing inbound or outbound synchronization rule.
5. An implementation changes the implementation record for that capability.
6. A partially closed gap is split if necessary, then its closed obligation is deleted rather than narrated as history.
7. A completed gap is deleted completely.
8. `PLAN.md` changes only when the selected record, next action, blocker, oracle, stop condition, handoff baseline, or resume command changed.
9. Reading a source, running a gate, or completing work is not by itself a trigger for any document.

### Update decision table

| Event | Required owners | Conditional owners | Owners normally untouched |
|---|---|---|---|
| Select existing open work | `PLAN.md` | None | Implementation map, gaps, sources, spec |
| Add or refine an open discriminator | `SEMANTICS-GAPS.md` | `PLAN.md` only if selection or blocker changes | Implementation map, sources, spec |
| Confirm existing behavior externally | `SOURCES.md` | Implementation map if assurance changes; gap if the open set changes; plan if selection changes | Spec |
| Retain or change a replayed observation | `EVIDENCE.md` | Implementation map if calibration changes; gap if the open set changes; plan if selection changes | Sources, spec |
| Correct behavior | `spec/` plus the applicable synchronization owner | Sources for inbound provenance; implementation map, gap, or plan only when their facts change | Unrelated owners |
| Implement without new external evidence | Implementation map | Gap if an obligation closes; plan if selection changes | Sources, spec |
| Refresh a verified baseline | `PLAN.md` | None | Every other owner |

This table is a trigger contract, not a document-count quota. A unit that genuinely changes four distinct facts may touch four owners, but each edit must be a small record-local change.

## Physical record contract

The live documents remain Markdown. Detailed capability, gap, plan, and provenance records stop using wide tables or omnibus prose bullets.

The links in the examples below whose anchors start with `cap-`, `gap-`, or `src-` name records that the pilot would create. They are illustrative until the proposal is adopted and the records exist together.

### Common mechanics

- Every repeatable detailed record has one stable explicit anchor and one searchable identifier. Its descriptive heading must not generate the same anchor. Singleton records such as the active plan use one fixed explicit anchor with a distinct heading slug.
- Every bullet carries one semantic claim.
- Keys are short, lower-case, backtick-delimited vocabulary.
- A key may repeat when the record has several independent claims of that class.
- Detailed records use bullets, not table rows.
- Compact summary tables remain allowed when every cell is a short status or link and no cell owns detailed prose.
- A claim line has a soft ceiling of 500 characters. Split by semantic claim, never by visual column width.
- One record should be understandable in a window of at most 80 lines, including its heading.
- Links target the narrowest stable owner or record anchor.
- Record text states current truth only. Git owns chronology unless an intentional historical owner applies.

Identifiers are local anchors, not entries in a new global registry. Their prefixes expose record kind: `cap-` for implementation, `gap-` for an obligation, and `src-` for provenance.

The 500-character threshold is an agent-efficiency guard, not hard wrapping. A coherent claim remains one line; a line that exceeds the threshold is reviewed for multiple claims and split at their semantic boundary.

### Implementation record

An implementation record answers what exists, where it lives, what guards it, how certain it is, and what remains.

```markdown
<a id="cap-temporal-group-uniqueness"></a>
#### Temporal group uniqueness

- `state`: partial
- `boundary`: temporal group uniqueness retains one recursively complete group expansion with one exact declared format.
- `owner`: [`TemporalValuesNotUnique.lean`](../A12Kernel/Elaboration/TemporalValuesNotUnique.lean)
- `case`: [temporal group cases](../A12Kernel/Conformance/TemporalEntityGroupOperand.lean)
- `proof`: [`checkedTemporalUniquenessGroup_expansion_complete`](../A12Kernel/Proofs/ValuesNotUnique.lean)
- `assurance`: E closed; P closed for the named boundary; L none; C none; X none; Q none.
- `source`: [group-carrier static admission](SOURCES.md#src-group-carrier-static-admission)
- `calibration`: none
- `remains`: [SG5 temporal group runtime](SEMANTICS-GAPS.md#gap-sg5-temporal-group-runtime)
```

Exact revisions, observation inventories, and historical corrections do not belong in this record. They remain behind the source or calibration link.

### Gap record

A broad `SG<n>` heading remains the stable family anchor. Independent live obligations become subordinate records so closing one does not require rewriting unrelated work.

```markdown
<a id="gap-sg5-boolean-group-runtime"></a>
#### Boolean/Confirm group runtime

- `state`: open
- `missing`: execute a retained Boolean/Confirm group operand without inventing omitted-tail fillability.
- `baseline`: [Boolean/Confirm value-count capability](IMPLEMENTATION-MAP.md#cap-boolean-value-count)
- `evidence-needed`: observe a declared but uninstantiated row under the group operand.
- `discriminator`: compare no declared tail with one declared but uninstantiated row while every instantiated value is unchanged.
- `consumer`: Execute must preserve growability without reconstructing the authored group.
- `reopen-when`: SG5 runtime work is selected and the kernel runtime route can express the discriminator.
```

A gap record contains no completed capsule narrative. Its `baseline` is a link plus only the minimum local premise needed to state the missing obligation.

### Plan record

`PLAN.md` becomes a small resumption packet. It does not summarize the project or reproduce closed work.

```markdown
<a id="active-unit"></a>
## Selected work

- `gap`: [SG5 Date-group diagnostic](SEMANTICS-GAPS.md#gap-sg5-date-group-string-value-list-diagnostic)
- `objective`: project the already measured operator-specific diagnostic without widening other group refusals.
- `oracle`: the retained static-admission receipt linked by the gap.
- `next`: add the red conformance case in the owning elaboration family.
- `stop`: stop if the current refusal cannot distinguish homogeneous wrong kind from heterogeneous mixing.
- `resume`: `lake build <focused-module>`
```

The verified baseline remains a separate compact record. Parked work belongs in gap records with reopening triggers, not in a second backlog inside the plan.

The baseline is a handoff checkpoint, not a receipt for every successful routine gate. It records the last selected-work checkpoint and applicable tier result. Volatile job, theorem, declaration, and module counts are omitted unless a diagnosed guard consumes them; the gate recomputes those counts when needed.

### Provenance record

`SOURCES.md` keeps exact revisions and claim limits, but each reusable receipt becomes a bounded record rather than part of a multi-purpose paragraph.

```markdown
<a id="src-group-carrier-static-admission"></a>
#### Group-carrier static admission

- `claim`: `FieldValuesNotUnique` admits a nonrepeatable group containing two Date fields with one declared format.
- `claim`: `NumberOfValueInFields` admits `True` and `False` over a Boolean group and `True` over a Boolean/Confirm group.
- `route`: source-shipped dmtool `rule check` through the real-kernel consistency oracle.
- `revision`: a12-dmkits `57ddd442f2f609b645c0030280662bc96d8ac49c`.
- `kernel`: 30.8.1 built and runtime.
- `limit`: static admission only; no runtime account follows.
- `limit`: `False` over a Boolean/Confirm group is not measured.
```

The normative semantic clause remains prose in `spec/`. This proposal does not impose record syntax on the specification.

## Query contracts after adoption

The record shapes support direct, bounded retrieval:

```sh
rg -n '^<a id="cap-' docs/IMPLEMENTATION-MAP.md
rg -n '^<a id="gap-' docs/SEMANTICS-GAPS.md
rg -n '^<a id="src-' docs/SOURCES.md
rg -n '^- `state`:|^- `blocked-on`:|^- `reopen-when`:' docs/SEMANTICS-GAPS.md
rg -n '^- `assurance`:|^- `remains`:' docs/IMPLEMENTATION-MAP.md
```

An agent starts from one stable record, follows at most one link for each adjacent concern, and does not need to read an entire clause table or gap family to update one fact.

The existing top-level `§n`, `SG<n>`, and source-area anchors remain stable. Record anchors refine them; they do not replace public incoming links.

## Pilot scope

The proposed first adoption unit is deliberately narrow. It validates the ownership lifecycle across one active family before any wider conversion.

### Required pilot changes

1. Add the lifecycle and record contracts to `DOC-DISCIPLINE.md` and update the query routes in `README.md`.
2. Preserve the `sg5--numeric-authoring-and-target-completion` anchor and convert only its group-scope entity-list omnibus bullet into subordinate open-only records.
3. Leave SG5's other numeric-authoring records unchanged during the pilot.
4. Create bounded implementation records for shared group admission, Number aggregation, token expansion, temporal uniqueness, Boolean/Confirm value count, and group-operand reference projection.
5. Shorten the existing broad implementation rows to the local consequence and a link when one of the new records becomes the detailed owner.
6. Replace only `PLAN.md`'s completed group-operand narrative with the compact active-unit record and direct gap links.
7. Convert only the group-operand source checkpoints directly linked by the new records; add no reverse consumer inventory to `SOURCES.md`.
8. Preserve every unique current fact at its canonical owner using harvest, redirect, delete.
9. Preserve or explicitly redirect every incoming anchor touched by the pilot.

### Optional pilot change

If one converted capability still needs more than 80 lines, split it into two independently queryable capability records only when they have distinct boundaries, owners, assurance, or open remainders.

### Excluded from the pilot

- Repository-wide conversion of every capability, gap, or source receipt.
- Changes to `spec/`, Lean source, evidence artifacts, public contracts, or the synchronization ledger.
- New schemas, parsers, generators, linters, registries, indexes, or CI gates.
- Renaming existing top-level clause and SG anchors.
- Rewriting historical or self-contained implementer documents.
- Compressing claims merely to meet a line count.

## Pilot acceptance criteria

The pilot is accepted only when all of the following hold:

1. The group-operand capability, assurance, provenance, open-work, and next-action queries each have one canonical answer.
2. Converted detailed records have no line over 500 characters unless the review names the indivisible claim and accepts it explicitly.
3. Every converted record fits within an 80-line retrieval window.
4. `IMPLEMENTATION-MAP.md` carries no exact group-operand revision narrative that belongs in `SOURCES.md` and no retained-observation inventory that belongs in `EVIDENCE.md`.
5. The converted group-operand subsection in `SEMANTICS-GAPS.md` carries no completed implementation narrative.
6. `PLAN.md` carries no group-operand history or secondary backlog.
7. Every group-operand open obligation, blocker, discriminator, consumer consequence, and reopening trigger remains represented.
8. Every current implemented boundary, proof/non-law status, external-assurance distinction, and owner link remains represented.
9. All existing incoming links either resolve unchanged or are redirected in the same change.
10. `git diff --check` and `./scripts/check-spec-sync.sh` pass.
11. A cold artifact-only reviewer finds no fact loss, ownership inversion, orphaned link, or new duplicate account.

No new permanent gate enforces these criteria. The pilot uses ordinary searches and review because a new governance harness would cost more than the demonstrated problem warrants.

## Beyond the pilot

Broader adoption is excluded from this decision. If the pilot meets the acceptance criteria, a later user decision may adopt touch-local conversion for other sections. This proposal creates no migration backlog or standing cleanup campaign.

Once adopted policy and the pilot are stable, retire this proposal. Durable rules belong in `DOC-DISCIPLINE.md` and current query routes in `README.md`.

## Risks and controls

### Loss of a unique live fact

Deleting completed narrative can accidentally delete the only statement of an assurance limit or rejected account. The pilot must inventory each source record before deletion and map every retained fact to its canonical owner. Cold review attacks omissions from the frozen before/after slice.

### Excessive fragmentation

One sentence per file or record would make retrieval worse. Records are split by independently changing capability or obligation, not by sentence count. Closely related claims with the same owner, assurance, and remainder stay together.

### Link chasing

Strict pointer-only use can force too many hops. Each record therefore retains the local consequence required by its own question, and links directly to the next canonical owner. A normal query should need no more than one hop per adjacent concern.

### Anchor churn

Generated heading anchors can change when prose changes. Stable records use explicit anchors, and existing top-level anchors remain in place.

### Accidental schema creation

The keyed bullets are a writing convention, not a parsed format or compatibility contract. Keys may evolve through policy review without migration tooling.

### Superficial line compression

The proposal forbids visual hard wrapping and compressed prose. The line threshold exists to expose multiple claims, not to shorten an indivisible claim or reduce total knowledge.

### Policy without practical benefit

The pilot must compare retrieval window, long-line count, changed-line count for a representative one-fact edit, and duplicated detail before and after. If those measures do not improve without fact loss, do not roll the format out.

## Alternatives considered

### Keep the current format

Rejected. The recent edit history and direct tool friction show that the cost is recurring rather than hypothetical.

### Loosen exclusive ownership

Rejected. Duplication would make retrieval initially convenient but increase reconciliation work and stale claims. The proposal makes ownership stricter while making canonical records cheaper to access.

### Move the records to YAML, JSON, or a database

Rejected. Structured storage would require a schema, validation, rendering, link conventions, and migration ownership. Markdown already supports the required anchors, links, diffs, and direct agent searches.

### Split every capability or gap into a separate file

Rejected. File proliferation would add discovery and navigation cost without fixing lifecycle duplication. Section-local records provide bounded retrieval inside the existing owners.

### Hard-wrap existing paragraphs

Rejected. Visual wrapping would reduce line length but preserve omnibus records and make future edits ambiguous. Claims must be separated semantically.

### Rewrite every live document at once

Rejected. A repository-wide conversion creates a large fact-loss and anchor-risk surface, interrupts semantic throughput, and cannot prove the record contract is better before paying the full cost.

## Adoption decision

The recommended adoption is one policy change plus the bounded SG5 pilot, with no tooling and no wider migration promise.

Approval of this proposal would authorize only that pilot. It would not authorize changes to semantic behavior, dependencies, evidence machinery, public contracts, or unrelated documentation sections.
