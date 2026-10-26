# Specification contributor instructions

These directory-scoped instructions supplement the repository root [`CLAUDE.md`](../CLAUDE.md) and the exclusive ownership rules in [`docs/DOC-DISCIPLINE.md`](../docs/DOC-DISCIPLINE.md).

Before editing any file under `spec/`, find the owning clause through [`SEMANTICS-MAP.md`](SEMANTICS-MAP.md), which navigates but does not define, inspect the reusable provenance route in [`docs/SOURCES.md`](../docs/SOURCES.md), and determine whether the change is behavioral.

## What `spec/` holds

- `spec/` is the canonical language-neutral account of Kernel behavior and static legality, and the only semantic input a cold implementer receives. It is not an implementation map, evidence inventory, source-review history, roadmap, work log, or Lean status surface.
- No Lean def names, implementation status or "the reference account" in rule text. Lean workflow, proof engineering, module ownership and current implementation state belong under `docs/` or in Lean docstrings.
- A **Non-normative implementation note** may carry implementation advice only. A rule found only inside a note moves into the rules.
- Do not append implementation milestones, evidence counts, current gaps, or review chronology. Link to their owners.

## How a chapter states a rule

- **Mechanism first.** Lead each section with its general rule, then its exceptions as bounded cases, then closed tables for operator- or carrier-specific facts. State each fact once and point to it from elsewhere.
- **Operator membership lives in [`14-operator-reference.md`](14-operator-reference.md).** A chapter defines a mechanism and its named classes, with their measured scope; spec/14 assigns each operator its class per column. Add or change a cell there instead of listing members in a chapter. A cell is a class, `n/a` only where a chapter states the refusal, or `not stated`.
- **Scope, not confidence prose.** A list given by example is either closed, when a chapter or Lean closes it, or written "measured members: …; others unmeasured". A rule that only Lean or source reading decides is marked unmeasured unless a `docs/sources/` checkpoint measures it.
- **No negative existentials without a measurement.** Never write "unreachable", "no legal model" or "never authorable"; write "no witness known" and keep the semantic clause total.
- **Provenance after the rules.** No checkpoint, inbound or a12-dmkits links inside rule sentences. Each section ends with one `Sources:` line.
- **Message catalogs are protected expression.** Name message codes only; never reproduce a rendered Kernel message sentence.
- **Link labels.** `§n` means the taxonomy number of the target chapter, not its file number; label links into spec/12 as "concrete syntax §n".
- Write one Markdown paragraph per line; do not hard-wrap.

## Behavioral changes and the ledger

- A verified behavioral correction, narrowing, or extension updates the canonical clause. If it originated here and still needs a12-dmkits reconciliation, update [`docs/A12-DMKITS-SPEC-SYNC-LEDGER.md`](../docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) in the same change. Removing a distinction, trap marker or measured-scope limit is behavioral too.
- An inbound correction already committed and reviewed in a12-dmkits records its exact revision and route in [`docs/SOURCES.md`](../docs/SOURCES.md); do not create a feedback-loop ledger entry.
- Navigation, terminology, and non-normative cleanup that changes no behavior does not enter the sync ledger. State that classification explicitly during review, and pass `A12_SPEC_CHANGE_IS_NONBEHAVIORAL=1` to [`check-spec-sync.sh`](../scripts/check-spec-sync.sh).
- Before committing, run `check-spec-sync.sh`, [`check-no-kernel-prose.sh`](../scripts/check-no-kernel-prose.sh) and `python3 scripts/check-doc-links.py`.

If a cleanup appears to change the semantic claim, stop treating it as cleanup and follow the behavioral-change and ledger rules.
