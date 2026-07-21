# Active implementation plan

This is the minimal continuation checkpoint. Current coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), durable semantic conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), completed work narratives in the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md), and stable workflow rules in [`../CLAUDE.md`](../CLAUDE.md) and [`TESTING.md`](TESTING.md).

## Verified baseline

- Semantic baseline: `5e62217` (`feat(validation): admit extremum constants`).
- Its focused proof build, full `lake build`, 51/51 retained-observation replay, and 10,968-declaration trust audit passed.
- Reference semantics remains 0.3.0 with the V2 flat-validation and one-group-correlation suites.
- Internally closed but externally uncalibrated families remain `external evidence pending`; no per-capsule evidence machinery is planned.

## Active unit

Implement IF202's partial-validation filtered-rule skip from a12-dmkits revision `6039fd3e`, after confirming the exact current partial-validation owner and source boundary. The gate must precede relevance and condition evaluation while leaving unfiltered partial semantics unchanged.

Success means each handoff has an exact disposition: implement a missing semantic capsule, update an existing owner without duplication, or record a verified no-op. Inbound facts go to [`SOURCES.md`](SOURCES.md) and existing owner records; they do not create new outbound ledger entries unless they answer an already-open entry.

## Frontier queue

- **Ready — IF202 partial validation:** implement the method-entry skip for every filtered rule before relevance gating or condition evaluation. Preserve the neighboring unfiltered relevance/unknown route and add full-versus-partial separators.
- **Satisfied — IF193 group presence:** a12-dmkits `7f152509` matches the existing product state and consumer projections introduced by `d19f77e`; do not add another group-state representation.
- **Satisfied — IF194 nested-star tails:** `7f152509` matches the hierarchical reopened-star mechanism and laws introduced by `d285cb5`; do not add a flat tail flag or parallel aggregate scan.
- **Missing fact — repeatable operand lowering:** needs checked star positions, capacities, row reads, and per-source metadata from one source-owned model representation.
- **Missing fact — aggregate expressions:** needs a shared checked expression-tree extension with more than one real consumer; do not add an aggregate-only comparison wrapper.
- **Missing fact — String targets:** needs declaration-owned length and line-break policy; do not infer unconstrained policy from erased model facts.
- **Missing authorization — flat literal scale and protocol-sensitive seams:** require deliberate protocol versioning or a separate adopted public-boundary change.
- **Forbidden duplicate mechanism:** no copied a12-dmkits harness, second numeric AST or scale gate, second aggregate scan, alternate group-state encoding, or parallel protocol route.

## Parked boundaries

- `DifferenceInDays` beyond the finite Berlin 2024 profile needs the versioned model-zone legacy-calendar account; proleptic `CivilDate` is not a substitute.
- Authored message integration still needs checked templates and real display providers.
- Checked group-instance enumeration and wildcardable relevance construction remain outside resolved group-presence projections.
- Public protocol expansion, semantic shipments, candidate qualification, SMT dependencies, and new evidence/process machinery require explicit adoption or approval.
- Batch external calibration by coherent family; do not create one producer request per internal capsule.

## Stop conditions

- Stop a candidate when its required model fact, consumer, or separating source witness is absent; record that absence once in the queue.
- Stop before introducing any duplicate semantic representation or any harness, schema, generator, protocol, registry, dependency, or governance layer without explicit approval.
- Keep sibling repositories read-only and preserve their visible status.
- Never push without an explicit current request.

## Resume procedure

1. Read this file, the applicable [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) clause, and the relevant [`TESTING.md`](TESTING.md) ladder rung.
2. Inspect `git status --short`, recent commits, and the current diff.
3. Reconcile the first queue item against its owner and Git history before writing a red case.
4. Close one capsule or verified no-op, run its proportional gate, update only fact owners, and commit.
