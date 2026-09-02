# Consumer-probe contributor instructions

These directory-scoped instructions supplement the repository root [`CLAUDE.md`](../../CLAUDE.md) and the documentation instructions in [`../CLAUDE.md`](../CLAUDE.md).

Before starting or recording a probe, read the laboratory [`README.md`](README.md#common-protocol), its [run-record contract](README.md#run-record-format), and the probe type's frozen task and acceptance boundary.

## Frozen basis

- Give every new task contract a stable explicit anchor in its consumer-type document. Commit the task, finite acceptance boundary, wrong accounts, and exclusions before exposing them to the isolated consumer.
- Immediately before the handover, require `git status --short` to be empty and record the exact 40-character commit returned by `git rev-parse HEAD`. That commit is the `semantic-basis` for all repository material supplied to the consumer.
- Do not qualify an exploratory dirty-worktree result. Commit the frozen material and rerun it.

## Run timing

- Capture `started-at` immediately before the isolated consumer receives the frozen handover.
- Capture `finished-at` immediately after the consumer returns its final output and before root reconciliation begins.
- Record both as RFC 3339 timestamps with numeric UTC offsets, for example `2026-09-01T14:25:00+02:00`, and record their measured elapsed time as integer `duration-seconds`.
- If a timestamp was not captured at its boundary, do not estimate it from a later clock reading. Rerun before qualifying the result.

## Reporting

- Give each run a unique stable `run-` anchor and use the keyed record in the [run-record contract](README.md#run-record-format). Do not add another prose-heavy row to a legacy lab table.
- Use exactly one status from `green`, `amber`, `red`, or `blocked`. A corrected or materially changed run receives a new run ID rather than a composite status or an overwritten record.
- Never infer or backfill timing, semantic basis, cost, oracle, or consumer access from file metadata, a conversation date, the current `HEAD`, or a later report commit.
- Keep each field claim-local. Git history owns superseded text; the type document owns the current bounded result and any still-material earlier comparator.
