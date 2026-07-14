# Repository artifact lifecycle

This guide explains what belongs under [`evidence/`](../evidence/), [`reference/`](../reference/), [`examples/`](../examples/), and `qualification/`, which facts each tree owns, and how each tree should evolve. These directories deliberately have different lifecycles; treating all of them as either source files or disposable generated output would break the project's evidence and consumer contracts.

## The short answer

| Directory | Role | Source of truth? | Normal evolution |
|---|---|---|---|
| [`evidence/`](../evidence/) | Retained external observations and exact probe inputs plus project-owned Lean-facing projections | Raw observation records preserve what a pinned kernel run observed; projections are reviewed bridges, not external authority | Append, version, or explicitly correct raw observations; evolve projections only through a checked bridge change |
| [`reference/`](../reference/) | Portable consumer shipments and the readable support-manifest mirror | Mostly derived from Lean and retained evidence; the correlation suite remains a reviewed manual index | Regenerate typed outputs, maintain reviewed indices explicitly, and version incompatible supported changes |
| [`examples/`](../examples/) | Runnable user examples, golden process regressions, and generated shipment fixtures | No; expected outputs are reviewed regression locks, not kernel evidence | Curate the small human-facing set and regenerate owned fixture sets |
| `qualification/` | Candidate-specific execution records and, if adopted, compact audit receipts | No; a qualification record reports checks against a pinned shipment | Keep work transient; retain selected records immutably rather than updating them |

The authority chain remains:

```text
external kernel execution
        ↓
retained evidence of the observation
        ↓
reviewed projection + Lean semantic account
        ↓
generated language-neutral reference shipment
        ↓
independent candidate qualification
```

The real kernel remains the behavioral authority. The Lean theory is the executable semantics-of-record for the project's chosen account. Retained evidence connects that account empirically to particular kernel observations. Generated shipments expose a closed part of the account to independent consumers. Qualification records describe what a particular candidate actually passed. None of these roles should silently absorb another.

Detailed evidence claims remain in [`EVIDENCE.md`](EVIDENCE.md), process and manifest compatibility in [`PROTOCOL.md`](PROTOCOL.md), executable gates in [`TESTING.md`](TESTING.md), consumer shipment and qualification contracts in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md), and current unfinished work in [`PLAN.md`](PLAN.md). This guide owns only the directory-level classification and lifecycle connecting those contracts.

## `evidence/`: retained empirical inputs

### Contents

The versioned [`evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/) bundle currently contains:

- runtime observation records under [`cases/`](../evidence/kernel-30.8.1/cases/);
- static authoring observations under [`diagnostics/`](../evidence/kernel-30.8.1/diagnostics/);
- complete standalone DM-JSON probe inputs under [`models/`](../evidence/kernel-30.8.1/models/);
- an auxiliary interpreter-versus-kernel disagreement record under [`triangulation/`](../evidence/kernel-30.8.1/triangulation/);
- four reviewed Lean-facing projection files for flat/path/required, uncorrelated iteration, captured-outer correlation, and checked correlation elaboration.

The case, diagnostic, and model files preserve the input and externally observable result of a focused experiment. The projections are narrower structured translations into the input boundary understood by the current Lean capsules. A projection is therefore a reviewed bridge, not an additional kernel observation and not a replacement for the retained full model and output.

### Responsibility and authority

This tree answers: **what exactly was run against which kernel version, and what was observed?** It supports empirical correspondence claims only over the retained observable projection. It does not prove that the kernel universally agrees with Lean, and it does not make a manually classified hidden Lean verdict externally observed when the kernel output exposed only message presence or silence.

The complete provenance and claim boundary are owned by [`EVIDENCE.md`](EVIDENCE.md). The replay schemas and binders live under [`A12Kernel/Evidence/`](../A12Kernel/Evidence/); they are test infrastructure rather than part of the trusted theorem root.

### Evolution policy

- A pure Lean refactor must not change raw retained observations. A reviewed projection also remains unchanged unless the Lean-facing bridge itself intentionally changes.
- A protocol, fixture-layout, or shipment change must not change raw retained observations.
- A changed Lean semantic account must replay against the same retained observations. A disagreement is investigated; the raw evidence is never refreshed merely to make the test green.
- A project-owned projection may intentionally evolve with the supported Lean bridge, but that change creates no new evidence and must remain bound to the same raw artifacts through `lake test`.
- A newly modeled semantic clause may remain explicitly `external evidence pending`. Before claiming external correspondence or evidence-complete status, add the smallest focused observation and reviewed projection needed to anchor it.
- A new kernel version gets a new versioned bundle. It must not silently rewrite [`kernel-30.8.1/`](../evidence/kernel-30.8.1/).
- A faulty capture is corrected only as an explicit provenance-bearing evidence correction.
- Full probe models remain complete and readable even when they share substantial structure; exact executed input is more important than reducing a small amount of repository storage.

Run `lake test` to replay the supported projection of all retained observations. Nothing under `evidence/` is written by `syncFlatHandover --write`; that command only regenerates downstream shipment artifacts.

### Current integrity gaps

Some runtime projections still repeat cells, rows, paths, and structured conditions that were manually read from retained placements. Those transcriptions are reviewed but not all mechanically derived from the full case and model. Only the narrow binders implemented by each evidence lane protect the relationship today. A complete evidence-bundle inventory with a digest, capture revision, per-file role, and exact-file checks—and additional narrow placement-to-projection binders—should land before the corpus grows substantially.

## `reference/`: portable consumer shipments

### Contents

[`reference/`](../reference/) currently contains:

- [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json), the readable mirror of the support manifest generated from finite Lean declarations in [`Reference/Support.lean`](../A12Kernel/Reference/Support.lean);
- the generated [`flat-validation-empty-logic-v1` capability descriptor](../reference/flat-validation-empty-logic-v1.capability.json);
- its generated [conformance suite](../reference/flat-validation-empty-logic-v1.conformance.json);
- its generated source-maintainer [mutation qualification plan](../reference/flat-validation-empty-logic-v1.mutation-plan.json);
- the [`single-group-correlation-v1` conformance suite](../reference/single-group-correlation-v1.conformance.json), whose evidence and fixture associations are still reviewed manual projections.

### Responsibility and authority

This tree answers: **what exact, language-neutral capability can an independent consumer implement or check?** These files are committed because a Rust, Python, Kotlin, or TypeScript consumer should not need a Lean installation to inspect or use a shipment.

They are distribution projections, not the authoring source of the semantics. Generated members are owned by typed Lean support or capability declarations plus the retained evidence they cite; the correlation suite remains a reviewed manual index until its bridge is mechanized. Once an exact bundle or packet is exported or digest-pinned for an independent consumer, those exported files and their declared compatibility tuple form an immutable record. A working development projection may evolve and be exported under a new digest or revision; an incompatible supported compatibility change requires a new identity or version.

### Evolution policy

- Never hand-edit an artifact with a typed generator to make a check pass. Change its owning Lean declaration or evidence input, regenerate, and review the complete diff.
- An internal Lean refactor that preserves the public account should produce no reference diff.
- During development, an intentional semantic, protocol, or classification change regenerates the affected current-development shipment and reruns all drift gates.
- After a shipment becomes a supported external contract, an incompatible semantic or protocol change creates a new capability or schema version rather than mutating the old identity.
- Removing a generated case must also remove every generated file and index entry; exact-directory checks should reject stale output.

For the flat shipment, `lake exe syncFlatHandover --check` performs a non-writing comparison of the descriptor, suite, mutation plan, exact fixture set, and manifest evidence boundary. `lake exe syncFlatHandover --write` intentionally regenerates those files and must be followed by diff review and another `--check`. `lake exe checkReferenceProcess` independently compares the live CLI manifest with its committed mirror and exercises the committed process fixtures.

### Current integrity gap

The correlation suite is structurally validated and executed, but its projection-to-protocol association is still maintained manually. It should be converted to the same typed descriptor and checked generation pattern as the flat shipment before another large correlation capability is added. The support-manifest mirror is drift-checked but does not yet share the flat shipment's first-class regeneration command.

## `examples/`: human examples and regression fixtures

### Contents

[`examples/reference-cli/`](../examples/reference-cli/) currently combines two roles:

1. curated request/response pairs intended to be readable and runnable by a user;
2. complete fixture sets used by process and downstream conformance tests.

The eight pairs under [`flat-evidence/`](../examples/reference-cli/flat-evidence/) are generated from the typed flat capability and retained projection. The root request/response pairs are maintained as readable golden examples and are explicitly enumerated by the reference-process test; the correlation subset is also referenced by its conformance suite.

### Responsibility and authority

This tree answers: **how can a user run the current reference process, and which exact public responses must remain stable for these inputs?** A committed response is a golden regression lock over the normalized protocol. It is not external kernel evidence merely because the Lean executable can reproduce it.

### Evolution policy

- Keep the human-facing set deliberately small, separating, and understandable.
- Edit a curated request only when its teaching or boundary role changes, and review the resulting response semantically.
- Regenerate generated fixture sets only through their owning typed bridge.
- An expected-response change requires the same review as the semantic or protocol change that caused it. Blindly accepting output from the current evaluator would make the regression self-confirming.
- The generated flat directory has an exact-set check and must fail on a missing, changed, or stale fixture. Curated root fixtures are currently enumerated explicitly, so an additional unreferenced file can survive; repository-wide exact inventory remains desired drift work.

As the shipment corpus grows, generated conformance matrices should move conceptually—and, at a versioned layout boundary, physically—beside their capability under the shipment surface. `examples/` should remain the concise human entry point instead of becoming the complete test corpus.

Run `lake exe checkReferenceProcess` to execute the committed request/response pairs through the real process boundary. Run `lake exe syncFlatHandover --check` for the generated flat subset.

## `qualification/`: candidate-specific historical records

### Contents

There are currently no tracked qualification artifacts. Any local empty subdirectories are working scaffolding for the unfinished strict post-cold qualification path; they are not project source and do not establish a result.

A future accepted qualification record may contain a compact result and receipt identifying the shipment tuple, candidate revision, toolchain, commands, mutations or properties exercised, outcomes, and SHA-256 references to supporting logs or bundles. It must keep finite qualification separate from Lean proof and kernel evidence.

### Responsibility and authority

This tree answers: **what did this exact candidate revision pass against this exact shipment, under which recorded conditions?** It never defines A12 semantics, changes the shipment, transfers Lean proofs to a candidate, or creates new kernel evidence.

### Evolution policy

- Candidate checkouts, extracted packets, binaries, toolchains, raw logs, patches, and temporary observations belong under ignored `.lake/` storage, a temporary directory, or an external CI/release artifact—not as visible worktree files.
- A retained qualification record is immutable and digest-pinned. A changed candidate, shipment, plan, or toolchain produces a new record rather than updating the old one.
- Commit a compact receipt only when its historical audit value justifies retaining it. Large raw payloads should remain in durable external artifact storage and be referenced by digest.
- A record that passed a finite suite claims only those executed checks. It is neither release approval nor a universal implementation-correctness proof.

The strict result checker remains pending. Until it exists and validates a complete retained record, the current mutation plan is test planning rather than mechanically accepted qualification evidence.

## Evolution by change type

| Project change | `evidence/` | `reference/` | `examples/` | `qualification/` |
|---|---|---|---|---|
| Internal refactor, same observable account | Unchanged | Unchanged | Unchanged | Existing records remain historical |
| Lean semantic correction | Replay unchanged observations; add evidence only if the old boundary was insufficient | Regenerate development shipment or publish a new supported version | Update affected generated/golden responses with review | Run a new qualification for affected candidates |
| Protocol or manifest change | Unchanged | Regenerate or version affected contract | Update affected requests/responses | Run a new protocol qualification |
| New semantic capability | Add focused observation and projection before claiming external correspondence, or mark it `external evidence pending` | Add a closed capability shipment only when its task boundary is research-closed | Add a few curated examples plus generated cases as applicable | Qualify selected consumers separately |
| New kernel version | Add a new evidence bundle | Publish capabilities with the new kernel-behavior identity | Add only separating version examples | Create new candidate records against that identity |
| Evidence correction | Preserve correction provenance and explain why | Regenerate every affected derived shipment | Regenerate affected evidence-derived fixtures | Invalidate or supersede affected qualification claims explicitly |

## Desired repository-wide drift contract

The flat shipment demonstrates the intended pattern but the repository does not yet have one global artifact graph. Before these trees grow substantially, every committed artifact path or glob should have one recorded owner, role, input set, generator or capture method, compatibility identity, update policy, and non-writing check. A repository-wide gate should derive expected generated output in memory or ignored temporary storage, reject changed, missing, and stale files, validate retained evidence and exported shipment digests, and never rewrite the worktree in CI.

Generation remains an explicit maintainer action followed by review. A green generator run cannot create kernel evidence, approve a semantic correction, or qualify an independent consumer by itself.
