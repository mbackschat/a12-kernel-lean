# Repository artifact lifecycle

This guide explains what belongs under [`evidence/`](../evidence/), [`reference/`](../reference/), [`examples/`](../examples/), and the three qualification locations—tracked source, ignored generated packet, and immutable downstream result—which facts each owns, and how each should evolve. These artifacts deliberately have different lifecycles; treating all of them as either hand-authored source or disposable generated output would break the project's evidence and consumer contracts.

## The short answer

| Directory | Role | Source of truth? | Normal evolution |
|---|---|---|---|
| [`evidence/`](../evidence/) | Retained external observations and exact probe inputs plus project-owned Lean-facing projections | Raw observation records preserve what a pinned kernel run observed; projections are reviewed bridges, not external authority | Append, version, or explicitly correct raw observations; evolve projections only through a checked bridge change |
| [`reference/`](../reference/) | Portable consumer shipments and the readable support-manifest mirror | Mostly derived from Lean and retained evidence; the correlation suite remains a reviewed manual index | Regenerate typed outputs, maintain reviewed indices explicitly, and version incompatible supported changes |
| [`examples/`](../examples/) | Runnable user examples, golden process regressions, and generated shipment fixtures | No; expected outputs are reviewed regression locks, not kernel evidence | Curate the small human-facing set and regenerate owned fixture sets |
| [`A12Kernel/Qualification/`](../A12Kernel/Qualification/) | Tracked packet/result contracts, Rust packet projection, canonical observer, runner, checker, and adversarial self-test | Source of the project-owned qualification policy and projection; frozen candidate Git bytes and toolchain identity remain separate packet inputs | Change through ordinary reviewed source development and rerun the complete qualification self-test |
| ignored `.lake/qualification/` | Generated exact packet for a pinned source/candidate tuple | No; it is a reproducible, digest-pinned projection of tracked source and frozen candidate Git bytes | Export to a new directory, verify, distribute with an out-of-band index digest, then discard or archive unchanged |
| Downstream `qualification/` or external artifact storage | Returned `RESULT.json` and exact raw logs for one reported packet run | No; it reports finite checks under one assurance class | Retain selected results immutably; a changed packet, candidate, profile, or run produces a new record |

The authority chain remains:

```text
external kernel execution
        ↓
retained evidence of the observation
        ↓
reviewed projection + Lean semantic account
        ↓
exported language-neutral reference shipment
        ↓
independent candidate qualification
```

The real kernel remains the behavioral authority. The Lean theory is the executable semantics-of-record for the project's chosen account. Retained evidence connects that account empirically to particular kernel observations. Generated shipments expose a closed part of the account to independent consumers. Qualification records preserve what was source-replayed or externally reported under their explicit assurance class. None of these roles should silently absorb another.

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
- A project-owned projection may intentionally evolve with the supported Lean bridge, but that change creates no new evidence and must remain bound through `lake test` to every retained raw artifact it claims.
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

## Qualification artifacts: tracked source, ignored packet, and immutable result

### Contents

The tracked qualification source lives under [`A12Kernel/Qualification/`](../A12Kernel/Qualification/), with [`A12Kernel/MutationQualificationMain.lean`](../A12Kernel/MutationQualificationMain.lean) as its command-line boundary and [`A12Kernel/Process/Sha256.lean`](../A12Kernel/Process/Sha256.lean) as shared IO-only digest support. `Artifact.lean`, `Packet.lean`, and `MutationResult.lean` define the pure closed identities, codecs, and invariants. `RustPacket.lean` projects the typed plan and frozen Rust Git bytes into an exact packet. `Checker.lean`, `Runner.lean`, and `SelfTest.lean` verify, execute, and adversarially test that process. [`Assets/flat_validation_observer.rs`](../A12Kernel/Qualification/Assets/flat_validation_observer.rs) is tracked source for the canonical fixture-driven observer. These files are process source, not a candidate qualification result and not part of the trusted theorem root.

An exported packet normally lives under ignored `.lake/qualification/<packet-id>/`. Its exact tree contains `PACKET.json`, the generated mutation plan, frozen candidate build inputs with executable modes, the observer, observer-only and semantic patches, expected baseline and mutation observations, source inventories, packet-local verification tools and instructions, and a SHA-256 payload manifest. The packet index binds every role-bearing file and command to the source revision, candidate base revision, compatibility tuple, and execution profile. It is generated output, not committed source and not evidence that any mutation ran.

A returned result is a separate exact directory containing `RESULT.json` and only the raw stdout/stderr logs named and digested by that record. It binds the packet-index digest, source and candidate revisions, plan, baseline inventory, toolchain, exact commands and statuses, actual parsed case/algebra observations, restoration inventories, and assurance class. The current Rust experiment retains its accepted [`flat-validation-empty-logic-v1-rust-v1` result](../../a12-kernel-rust-spike/qualification/flat-validation-empty-logic-v1-rust-v1/RESULT.json) under the downstream candidate's `qualification/` tree at candidate revision `d213005b3972c2acd8f67e87f523a923d69f6a54`; this repository tracks no duplicate candidate-specific result. A compact receipt may later be retained here only when its historical audit value justifies it and every referenced large payload remains durably available by digest.

### Responsibility and authority

Together these locations answer two different questions: **what exact qualification experiment did this source define and ship?** and **what did this exact candidate revision report or execute against that packet under the recorded profile?** The tracked source owns the former. A checked result owns only the latter finite record. Neither location defines A12 semantics, changes retained kernel evidence, transfers Lean proofs to a candidate, approves a release, or creates universal correctness.

The result's assurance class is part of its authority. `sourceExecutedReplay` means this repository's runner invoked the packet commands in a disposable baseline copy and captured their streams, after which the checker validated the resulting finite record. `isolatedSessionAttestation` means the checker accepted a digest-bound, internally consistent record returned by another session; it checks byte-level consistency with the declared natural gate, seven mutations, finite observations, exact logs, and path-and-byte restoration projection, but does not claim to have witnessed that external process history.

### Evolution policy

- Change the tracked qualification modules or observer only when the packet contract, candidate projection, or checker behavior intentionally changes. Run the complete source replay and all adversarial guards; do not hand-edit a generated packet to follow the new source.
- Export requires a clean Lean source checkout and clean candidate checkout. Packet verification and returned-result acceptance use a clean source checkout at the packet's exact source revision; later source commits do not reinterpret an existing packet. The frozen candidate build-input closure is read from Git objects; the sibling checkout remains unmodified. A later candidate commit is admissible only when the frozen base remains an ancestor and the classified build-input paths, bytes, and executable modes are unchanged.
- Candidate copies, generated packets, binaries, toolchains, raw logs, patches, and temporary observations belong under ignored `.lake/` storage, an automatically removed temporary directory, or external CI/release artifact storage—not as visible untracked files in this repository or a sibling.
- Once the `PACKET.json` digest has been supplied to a consumer, treat that packet tree as immutable. A changed source revision, candidate closure, mutation plan, observer, command policy, toolchain profile, or payload produces a new packet and digest rather than an in-place update.
- A retained result is immutable and digest-pinned. A changed packet, candidate, profile, command outcome, or rerun produces a new record rather than updating the old one.
- Commit a compact receipt or downstream result only when its historical audit value justifies retaining it. Large raw payloads should remain in durable external artifact storage and be referenced by digest.
- A record that passed a finite suite claims only those checked observations and mutations under its assurance class. It is neither release approval nor a universal implementation-correctness proof.

A mutation plan remains test planning by itself. It contributes to candidate qualification evidence only as a digest-bound packet input paired with a complete result accepted by the strict checker. That result remains candidate-process evidence, never retained kernel evidence. [`TESTING.md`](TESTING.md#rust-mutation-qualification) owns the exact commands, checker coverage, resource caps, and remaining process-sandbox limits.

## Evolution by change type

| Project change | `evidence/` | `reference/` | `examples/` | Qualification artifacts |
|---|---|---|---|---|
| Internal refactor, same observable account | Unchanged | Unchanged | Unchanged | Existing records remain historical |
| Lean semantic correction | Replay unchanged observations; add evidence only if the old boundary was insufficient | Regenerate development shipment or publish a new supported version | Update affected generated/golden responses with review | Run a new qualification for affected candidates |
| Protocol or manifest change | Unchanged | Regenerate or version affected contract | Update affected requests/responses | Run a new protocol qualification |
| New semantic capability | Add focused observation and projection before claiming external correspondence, or mark it `external evidence pending` | Add a closed capability shipment only when its task boundary is research-closed | Add a few curated examples plus generated cases as applicable | Qualify selected consumers separately |
| New kernel version | Add a new evidence bundle | Publish capabilities with the new kernel-behavior identity | Add only separating version examples | Create new candidate records against that identity |
| Evidence correction | Preserve correction provenance and explain why | Regenerate every affected derived shipment | Regenerate affected evidence-derived fixtures | Invalidate or supersede affected qualification claims explicitly |

## Desired repository-wide drift contract

The flat shipment and Rust qualification packet demonstrate checked local artifact graphs, but the repository does not yet have one global graph. Before these trees grow substantially, every committed artifact path or glob should have one recorded owner, role, input set, generator or capture method, compatibility identity, update policy, and non-writing check. A repository-wide gate should derive expected generated output in memory or ignored temporary storage, reject changed, missing, and stale files, validate retained evidence and exported shipment digests, and never rewrite the worktree in CI.

Generation remains an explicit maintainer action followed by review. A green generator run cannot create kernel evidence, approve a semantic correction, or qualify an independent consumer by itself.
