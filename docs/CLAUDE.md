# Documentation contributor instructions

These directory-scoped instructions supplement the repository root [`CLAUDE.md`](../CLAUDE.md).

Before editing any file under `docs/`, read [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md) and the canonical ownership registry in [`README.md`](README.md#canonical-ownership-registry).

- Classify every changed fact by its sole owner before editing.
- Treat each update trigger as exclusive: if a document's owned responsibility did not change, leave it untouched.
- When adding detail to the owner, delete or replace displaced copies in the same change. A secondary document may state only its local consequence and link to the owner.
- Keep [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) open-only, [`PLAN.md`](PLAN.md) current-only, [`ARCHITECTURE.md`](ARCHITECTURE.md) free of capability status, and [`SOURCES.md`](SOURCES.md) free of capsule-review chronology.
- Preserve the live-map usability invariant: a new agent must locate a capability, its primary owner, its assurance, and its remaining gap without Git archaeology.
- Only [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) and [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) preserve numbered historical entries. Do not use their append pattern elsewhere.
- Preserve stable reader-facing paths and migrate every incoming link when a heading or path changes.
- Write one Markdown paragraph per line; do not hard-wrap.

Do not create another documentation policy, inventory, metrics file, or review report. Fix the owning document and rely on Git history.
