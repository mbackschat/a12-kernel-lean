# Specification contributor instructions

These directory-scoped instructions supplement the repository root [`CLAUDE.md`](../CLAUDE.md) and the exclusive ownership rules in [`docs/DOC-DISCIPLINE.md`](../docs/DOC-DISCIPLINE.md).

Before editing any file under `spec/`, start from [`SEMANTICS-MAP.md`](SEMANTICS-MAP.md), inspect the reusable provenance route in [`docs/SOURCES.md`](../docs/SOURCES.md), and determine whether the change is behavioral.

- `spec/` is the canonical language-neutral account of Kernel behavior and static legality. It is not an implementation map, evidence inventory, source-review history, roadmap, work log, or Lean status surface.
- Keep normative behavior distinguishable from clearly labeled **Non-normative implementation notes**. Put Lean workflow, proof engineering, module ownership, and current implementation state under `docs/` or in Lean docstrings.
- A verified behavioral correction, narrowing, or extension updates the canonical clause. If it originated here and still needs a12-dmkits reconciliation, update [`docs/A12-DMKITS-SPEC-SYNC-LEDGER.md`](../docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) in the same change.
- An inbound correction already committed and reviewed in a12-dmkits records its exact revision and route in [`docs/SOURCES.md`](../docs/SOURCES.md); do not create a feedback-loop ledger entry.
- Navigation, terminology, and non-normative cleanup that changes no behavior does not enter the sync ledger. State that classification explicitly during review.
- Do not append implementation milestones, evidence counts, current gaps, or review chronology. Link to their owners.
- Write one Markdown paragraph per line; do not hard-wrap.

If a cleanup appears to change the semantic claim, stop treating it as cleanup and follow the behavioral-change and ledger rules.
