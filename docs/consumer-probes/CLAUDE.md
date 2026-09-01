# Consumer-probe contributor instructions

These directory-scoped instructions supplement the repository root [`CLAUDE.md`](../../CLAUDE.md) and the documentation instructions in [`../CLAUDE.md`](../CLAUDE.md).

Before editing a lab record, read the laboratory [`README.md`](README.md#common-protocol) and the probe type's frozen task and acceptance boundary.

## Run identity

- Every new probe run and every material rerun must record `Executed at` and `Semantic basis` in its lab-ledger row. Use table columns with those exact names so every row remains independently identifiable.
- Record `Executed at` when the retained run finishes, using an RFC 3339 timestamp with a numeric UTC offset, for example `2026-09-01T14:25:00+02:00`.
- Record `Semantic basis` as the exact 40-character commit returned by `git rev-parse HEAD` for the frozen repository material supplied to the consumer. Run `git status --short` first and retain a lab row only from a clean committed basis; exploratory dirty-worktree results must be rerun after the semantic material is committed.
- When first extending a legacy table that lacks these columns, add both columns and write `not recorded` for historical rows whose identity is not already proven by retained evidence.
- Never infer or backfill a run timestamp or semantic basis from a file modification time, a conversation date, the current `HEAD`, or a later report commit.

Keep the existing compact result and cost discipline. The timestamp identifies when the consumer ran; the semantic basis identifies what it tested; Git history identifies when the report itself changed.
