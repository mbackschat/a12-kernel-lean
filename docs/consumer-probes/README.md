# Consumer probe laboratory

This directory tests whether the Lean semantics factory can make diverse independent consumers cheap to implement without renewed Kernel archaeology. It owns probe design, frozen material, task-specific acceptance, measured consumer cost, and the current lab result for each consumer type. It does not own A12 behavior, implemented capability status, product commitments, or shipment support.

## Authority and acceptance

Lean definitions, checked elaboration, theorems, and conformance cases are the sole decision authority for this project's semantic account. The language-neutral [`spec/`](../../spec/) clauses and bounded capability records are the consumer handover under test. A consumer result is untrusted until the implementing session reconciles it against the applicable Lean-owned equality, relation, witness replay, certificate checker, or finite decision.

Retained Kernel evidence separately bounds correspondence to A12 Kernel 30.8.1. Cold consumers receive neither Kernel access nor a12-dmkits source. A probe may therefore establish that the project account transports cheaply while Kernel correspondence for that capability remains pending.

## Common protocol

1. Select one existing bounded capability and one concrete task contract. Do not build missing semantics merely to make a probe pass.
2. Freeze a minimal language-neutral allowlist, fixture, acceptance matrix, wrong accounts, and explicit exclusions under a stable task anchor in the consumer-type document. Commit that boundary before the run. Lean source and expected semantic outputs stay hidden from the isolated implementer unless the task's declared shipment includes an executable checker.
3. Use a fresh context and ordinary task-appropriate tooling. Consumer code remains disposable outside the repository unless a later shipment decision explicitly adopts it.
4. Reconcile every claimed result against the Lean authority. A consumer's tests and self-reported PASS do not certify the result.
5. Classify the run as `green`, `amber`, `red`, or `blocked`. `green` means the exact bounded task worked cheaply; `amber` means useful output exists but the claimed relation needs a larger bridge, certificate, or trust boundary; `red` means the task or handover failed; `blocked` means an unavailable external prerequisite prevented the experiment.
6. Record every new or materially rerun result as a [keyed run record](#run-record-format) under the directory-scoped [capture discipline](CLAUDE.md#frozen-basis). Git owns superseded report text; each type document keeps only the current bounded results and still-material comparators needed to evaluate that consumer type.

## Run record format

New runs use independently addressable keyed records rather than adding wider prose-table rows. Existing tables remain valid historical records and are not bulk-migrated. A material rerun replaces its superseded row with a keyed record when that row has no continuing comparative value; Git retains the displaced text. Never backfill unknown legacy metadata.

Each task link targets the committed stable anchor for the exact bounded handover. Each `oracle` names the Lean-owned equality, relation, witness replay, certificate, or finite matrix used during root reconciliation and states whether reconciliation passed. `consumer-access` states repository, source, tool, dependency, external-knowledge, and code access rather than leaving independence implicit. `cost` records implementation and test lines, dependencies, capability-local versus reusable machinery, implementation time, and checker cost where applicable. `questions-and-guesses` says `none` only when the isolated consumer made no semantic guess or unresolved decision.

Use this field order so run identity and assurance remain searchable across consumer types:

```markdown
<a id="run-{run-id}"></a>
### {task label} — `{run-id}`

- `task`: [{task label}](#{stable-task-anchor})
- `status`: green | amber | red | blocked
- `started-at`: {RFC 3339 timestamp with numeric offset}
- `finished-at`: {RFC 3339 timestamp with numeric offset}
- `duration-seconds`: {nonnegative integer}
- `semantic-basis`: `{exact 40-character commit}`
- `oracle`: {Lean authority and reconciliation outcome}
- `consumer-access`: {repository, source, tools, dependencies, external knowledge, and produced code}
- `cost`: {implementation effort, line counts, reuse boundary, and checker effort}
- `result`: {bounded result only}
- `wrong-accounts`: {finite discriminator outcome}
- `questions-and-guesses`: {none, or each unresolved item and its effect}
- `exclusions`: {explicit non-claims}
```

The start and finish timestamps bound the isolated consumer run only; root reconciliation happens afterward and is reported under `oracle`. The semantic basis identifies the committed handover and theory under test, while the later report commit identifies when the record itself entered Git. A corrected run gets a new run ID and record instead of a composite status such as “green after correction.”

## Portfolio

| Consumer type | Current status | Current bounded tasks |
|---|---|---|
| [Execute](EXECUTE.md) | green | Exact-address DateTime and repeatable Number constant application, addressed extrema with division/power domain and target-policy preservation, generated numeric-table evaluation/application, selected-preliminary execution across Boolean, token, String, and temporal carriers plus three composition seams, explicit Number/String validation after one- and two-level application, and materialized generated Number targets |
| [Translate](TRANSLATE.md) | green | Computed-target refusal to exact external diagnostic or typed local refusal |
| [Transform](TRANSFORM.md) | green | Checked numeric-operation identity, including addressed division/power/suppression fingerprints, plus fixed Boolean/Confirm declaration relocation under an exact runtime observation relation |
| [Compile](COMPILE.md) | green | Specialized finite condition, generated numeric-table, selected-preliminary whole calls, three selected conversion-composition plans, and addressed multi-star Number selection with exact bounded refinement |
| [Analyze](ANALYZE.md) | green; broader graph reconstruction amber | SMT-backed presence reachability, addressed extremum scale/capability and ordered identity, checked numeric-table cycle analysis, generated-computation phase-alias safety, heterogeneous fixed scalar declaration placement, and flat mandatory-information derivation including list guards, count identity and isolation, severity, cycles, whole-rule exclusions, exact generated identities, and the direct-repeatable-child presence matrix |
| [Verify](VERIFY.md) | green | Proof-bearing same-field contradiction certificate and counterexample boundary |
| [Synthesize](SYNTHESIZE.md) | green | SMT-produced presence witness replayed through Lean semantics |
| [Qualify](QUALIFY.md) | green | Four independent DateTime consumer mutations and restoration |
| [Explain](EXPLAIN.md) | green | Structured source-first traces, exact whole-call inventories on success and post-plan failure, generated-preliminary parent-local DateRange explanation, implicit computation message polarity plus `fillToFix`, origin-sensitive filtered-token pointers, plain/filtered String/Boolean/Confirm plus filtered Number capacity and movement, checked token `FirstFilledValue` capacity/laziness, and flat mandatory-information threshold, guard, count, severity, cycle, exclusion, generated-identity, and direct-repeatable-child presence decisions checked against Lean |
| [Govern](GOVERN.md) | green | Impact and compatibility decision for the calendar-day handover correction |

The user-facing potential and consolidated results remain in [`USE-CASES.md`](../USE-CASES.md). General shipment and qualification contracts remain in [`IMPLEMENTER-GUIDE.md`](../IMPLEMENTER-GUIDE.md). Implemented E/P/L/C/X/Q status remains in [`IMPLEMENTATION-MAP.md`](../IMPLEMENTATION-MAP.md).
