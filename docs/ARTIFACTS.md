# Repository artifact lifecycle

This guide explains what belongs under [`evidence/`](../evidence/), [`reference/`](../reference/), [`examples/`](../examples/), and the four qualification locations—tracked policy source, ignored generated packet, project-local retained receipt, and immutable downstream result—which facts each owns, and how each should evolve. These artifacts deliberately have different lifecycles; treating all of them as either hand-authored source or disposable generated output would break the project's evidence and consumer contracts.

## The short answer

| Directory | Role | Source of truth? | Normal evolution |
|---|---|---|---|
| [`evidence/`](../evidence/) | Retained external observations and exact probe inputs plus project-owned Lean-facing projections | Raw observation records preserve what a pinned kernel run observed; projections are reviewed bridges, not external authority | Append, version, or explicitly correct raw observations; evolve projections only through a checked bridge change |
| [`evidence/scenarios/`](../evidence/scenarios/) | Project-authored, expectation-free questions for the maintained external capture boundary | Yes, for the exact scenario request bytes; never a source of observed behavior | Version the question when its input or requested observation contract changes; retain returned answers elsewhere |
| [`reference/`](../reference/) | Portable consumer shipments and the readable support-manifest mirror | Mostly derived from Lean and retained evidence; the correlation suite remains a reviewed manual index | Derive new current identities from their owners, maintain reviewed indices explicitly, and never regenerate a frozen compatibility line in place |
| [`examples/`](../examples/) | Runnable user examples, golden process regressions, and generated shipment fixtures | No; expected outputs are reviewed regression locks, not kernel evidence | Curate the small human-facing set and regenerate owned fixture sets |
| [`A12Kernel/Qualification/`](../A12Kernel/Qualification/) | Tracked packet/result contracts, Rust packet projection, canonical observer, runner, checker, and adversarial self-test | Source of the project-owned qualification policy and projection; frozen candidate Git bytes and toolchain identity remain separate packet inputs | Change through ordinary reviewed source development and rerun the complete qualification self-test |
| ignored `.lake/qualification/` | Generated exact packet for a pinned source/candidate tuple | No; it is a reproducible, digest-pinned projection of tracked source and frozen candidate Git bytes | Export to a new directory, verify, distribute with an out-of-band index digest, then discard or archive unchanged |
| Project-local [`qualification/`](../qualification/) | Compact receipts from source-owned differential campaigns | No; a receipt reports one finite historical run and its explicit claim boundary | Retain a reviewed result immutably; a changed profile, source, candidate, or run gets a new identity rather than replacing it |
| Downstream `qualification/` or external artifact storage | Returned mutation `RESULT.json` and exact raw logs for one reported packet run | No; it reports finite checks under one assurance class | Retain selected results immutably downstream; a changed packet, candidate, profile, or run produces a new record |

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

## `evidence/scenarios/`: questions, not observations

[`evidence/scenarios/`](../evidence/scenarios/) contains versioned scenario roots authored by this project for a source-maintained a12-dmkits capture command. A root contains the complete input model or models intended for the later legality gate, explicit document placements, operation, requested runners, probes, required channels, qualification policy, and projection identities. It contains no expected value, verdict, diagnostic, agreement flag, mutation outcome, or Lean result. Its exact bytes are the canonical request and are copied into any returned packet; a12-dmkits must not commit a second authoritative copy.

The first member is [`string-direct-cascade-v1`](../evidence/scenarios/string-direct-cascade-v1/README.md). The scenario bytes remain only a question, while their separately retained [`Set Z4 answer`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/README.md) supplies the complete qualified packet, sidecars, process receipt, and no-drift report. The project-owned [`StringCascadeBinding.lean`](../A12Kernel/Evidence/StringCascadeBinding.lean) now closes the exact transport, qualification, typed public projection, and five-case Lean replay; its claim deliberately excludes hidden dependency state, scheduling, and exact absent-versus-present-empty Lean application semantics.

Changing scenario meaning requires a new scenario version or identity; reusing an existing ID with different bytes is forbidden. Structural validation checks only the closed request shape, references, digests, requested capabilities, and static transport constraints; kernel authoring legality is a separate capture-time gate. The official answer is a separate immutable unit: the complete packet and packet receipt, packet-local capabilities declaration, out-of-band packet-receipt digest, separate qualification profile/report/receipt sidecars and their out-of-band receipt digest, and a later project-owned typed projection. A scenario-specific mutation receipt and two-clean-capture no-drift report are retained as process-qualification companions, never reclassified as kernel observations. Retain every runner observation and declared fidelity gap, not only rows that agree.

## `evidence/`: retained empirical inputs

### Contents

The versioned [`evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/) bundle currently contains:

- runtime observation records under [`cases/`](../evidence/kernel-30.8.1/cases/);
- static authoring observations under [`diagnostics/`](../evidence/kernel-30.8.1/diagnostics/);
- complete standalone DM-JSON probe inputs under [`models/`](../evidence/kernel-30.8.1/models/);
- digest-pinned capture receipts under [`captures/`](../evidence/kernel-30.8.1/captures/), currently [`operator-sensitive-empty-2026-07-15.json`](../evidence/kernel-30.8.1/captures/operator-sensitive-empty-2026-07-15.json), [`string-computation-2026-07-15.json`](../evidence/kernel-30.8.1/captures/string-computation-2026-07-15.json), and [`string-target-validation-2026-07-15.json`](../evidence/kernel-30.8.1/captures/string-target-validation-2026-07-15.json), plus the complete version-owned [`string-direct-cascade-v1`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/README.md) packet, packet receipt, packet-local capabilities, qualification sidecars, process receipt, and recapture diff;
- an auxiliary interpreter-versus-kernel disagreement record under [`triangulation/`](../evidence/kernel-30.8.1/triangulation/);
- seven reviewed Lean-facing projection files: [`projection.json`](../evidence/kernel-30.8.1/projection.json) for flat/path/required, [`iteration-projection.json`](../evidence/kernel-30.8.1/iteration-projection.json) for uncorrelated iteration, [`correlation-projection.json`](../evidence/kernel-30.8.1/correlation-projection.json) for captured-outer correlation, [`correlation-elaboration-projection.json`](../evidence/kernel-30.8.1/correlation-elaboration-projection.json) for checked correlation elaboration, [`operator-empty-projection.json`](../evidence/kernel-30.8.1/operator-empty-projection.json) for operator-sensitive empty values, [`string-computation-projection.json`](../evidence/kernel-30.8.1/string-computation-projection.json) for the first clean String expression/store/delta capsule, and [`string-target-validation-projection.json`](../evidence/kernel-30.8.1/string-target-validation-projection.json) for positive String target-length checking, payloadful `ERRORED`, and the value-level application projection.

The case, diagnostic, and model files preserve the input and externally observable result of a focused experiment. A capture receipt binds provenance, file identities, and strategy outputs that do not fit the portable case shape; it remains a retained historical report, not proof that an unavailable temporary harness or validator command ran. The projections are narrower structured translations into the input boundary understood by the current Lean capsules. A projection is therefore a reviewed bridge, not an additional kernel observation and not a replacement for the retained full model and output.

### Responsibility and authority

This tree answers: **what exactly was run against which kernel version, and what was observed?** It supports empirical correspondence claims only over the retained observable projection. It does not prove that the kernel universally agrees with Lean, and it does not make a manually classified hidden Lean verdict externally observed when the kernel output exposed only message presence or silence.

The complete provenance and claim boundary are owned by [`EVIDENCE.md`](EVIDENCE.md). The replay schemas and binders live under [`A12Kernel/Evidence/`](../A12Kernel/Evidence/); they are test infrastructure rather than part of the trusted theorem root.

### Evolution policy

- A pure Lean refactor must not change raw retained observations. A reviewed projection also remains unchanged unless the Lean-facing bridge itself intentionally changes.
- A protocol, fixture-layout, or shipment change must not change raw retained observations.
- A changed Lean semantic account must replay against the same retained observations. A disagreement is investigated; the raw evidence is never refreshed merely to make the test green.
- A project-owned projection may intentionally evolve with the supported Lean bridge, but that change creates no new evidence and must remain bound through `lake test` to every retained raw artifact it claims.
- A newly modeled semantic clause may remain explicitly `external evidence pending`. Before claiming external correspondence or evidence-complete status, add the smallest focused observation and reviewed projection needed to anchor it.
- Historical evidence layouts and disposable-harness receipts remain immutable. Once the source-maintained a12-dmkits packet contract is available, each new capture is retained as the complete verified portable packet and receipt, the required qualification profile/report/receipt sidecars with their out-of-band receipt digests, and the project-owned typed projection. Do not retain only selected agreeing observations. Kernel binaries, kernel-linked types or implementation code, volatile execution logs, and generated machine-specific state remain outside `evidence/`.
- A new kernel version gets a new versioned bundle. It must not silently rewrite [`kernel-30.8.1/`](../evidence/kernel-30.8.1/).
- A faulty capture is corrected only as an explicit provenance-bearing evidence correction.
- Full probe models remain complete and readable even when they share substantial structure; exact executed input is more important than reducing a small amount of repository storage.

Run `lake test` to replay the supported projection of all retained observations. Nothing under `evidence/` is written by `syncFlatHandover`; its `--check` mode is non-writing and its `--write` mode rejects the frozen v1 shipment identity.

### Current integrity gaps

Some runtime projections still repeat cells, rows, paths, and structured conditions that were manually read from retained placements. Those transcriptions are reviewed but not all mechanically derived from the full case and model. Only the narrow binders implemented by each evidence lane protect the relationship today. The operator-sensitive, String-computation, and String target-validation lanes are the strongest current local patterns. The clean String lane owns a version-specific exact case directory, recursively closed projection decoder, capture/source/model/case digests, exact retained field and computation shapes, structural operation and placement binding, two kernel strategy lists, a mechanically reconstructed interpreter delta projection, and an exact triangulation mismatch set. The target-validation lane additionally binds rich clean/error results, attempted values and causes, accepted-equality versus unconditional-error behavior, and exact absent-versus-present-empty application state while keeping the Lean replay's application claim value-only. Their model files and receipts remain individually routed and digest-bound in shared directories so a later packet does not invalidate an earlier capsule merely by coexisting. A complete bundle-wide inventory with the same per-file role and exact-file discipline—and additional narrow placement-to-projection binders for the older lanes—should land before the corpus grows substantially.

## `reference/`: portable consumer shipments

### Contents

[`reference/`](../reference/) currently contains two explicit compatibility lines plus campaign infrastructure pinned to historical reference semantics 0.2.0:

- current [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json), the readable 0.3.0 support manifest generated from finite Lean declarations in [`Reference/Support.lean`](../A12Kernel/Reference/Support.lean);
- [`reference-semantics-lineage-v1.json`](../reference/reference-semantics-lineage-v1.json), the generated readable 0.2.0 → 0.3.0 lineage whose lines each carry a complete compatibility tuple and capability identities, plus [`reference-semantics-0.2.0.lock.json`](../reference/reference-semantics-0.2.0.lock.json), whose 152 path/digest entries close the selected historical evidence/example/principal-artifact inventory, and the separately retained [`0.2.0 separating replay receipt`](../reference/reference-semantics-0.2.0-separating-replay.json); human handover documents are outside the lock, while the post-revision separating request and replay receipt are bound separately by the lineage;
- current [`flat-validation-empty-logic-v2`](../reference/flat-validation-empty-logic-v2.conformance.json) and [`single-group-correlation-v2`](../reference/single-group-correlation-v2.conformance.json) conformance suites for 0.3.0;
- frozen historical [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json), [`flat-validation-empty-logic-v1` capability descriptor](../reference/flat-validation-empty-logic-v1.capability.json), [flat v1 suite](../reference/flat-validation-empty-logic-v1.conformance.json), [mutation qualification plan](../reference/flat-validation-empty-logic-v1.mutation-plan.json), and [correlation v1 suite](../reference/single-group-correlation-v1.conformance.json) for the completed 0.2.0 handovers;
- the frozen reviewed [`flat-validation-empty-logic-v1` generated-differential profile](../reference/flat-validation-empty-logic-v1.generated-differential-v1.json), which pins the closed 0.2.0 generator, compatibility tuple, source and candidate revisions, response projection, execution contract, and resource budgets for one finite campaign.

### Responsibility and authority

This tree answers: **what exact, language-neutral capability can an independent consumer implement or check?** These files are committed because a Rust, Python, Kotlin, or TypeScript consumer should not need a Lean installation to inspect or use a shipment.

They are distribution projections, not the authoring source of the semantics. Generated members are owned by typed Lean support, lineage, or capability declarations plus the retained evidence they cite; the correlation suites remain reviewed manual indices until their bridge is mechanized. A generated-differential profile is a campaign definition rather than a support declaration: it may select only already admitted inputs, and its revision pins and budgets make one execution repeatable without expanding the capability. Once an exact bundle, packet, or differential profile is exported or digest-pinned for an independent consumer, those files and their declared compatibility tuple form an immutable record. That rule now applies concretely to every listed v1 artifact. A working development projection may evolve only under a new identity, digest, or revision; an incompatible supported compatibility change requires a new identity or version.

### Evolution policy

- Never hand-edit an artifact with a typed generator to make a check pass. Change its owning Lean declaration or evidence input, regenerate, and review the complete diff.
- An internal Lean refactor that preserves the public account should produce no reference diff.
- During development, an intentional semantic, protocol, or classification change regenerates the affected current-development shipment and reruns all drift gates.
- After a shipment becomes a supported external contract, an incompatible semantic or protocol change creates a new capability or schema version rather than mutating the old identity.
- Removing a generated case must also remove every generated file and index entry; exact-directory checks should reject stale output.
- Do not update a differential profile in place after it has a retained result. A changed generator, bound, projection, source revision, or candidate revision creates a new profile identity and a new result.

For the frozen flat v1 shipment, `lake exe syncFlatHandover --check` performs a non-writing comparison of the descriptor, suite, mutation plan, exact fixture set, and historical manifest evidence boundary. `lake exe syncFlatHandover --write` now rejects that historical identity; a future writable shipment must use a new capability and generator path. `lake exe checkReferenceProcess` independently compares the live CLI manifest with current v2, compares the readable lineage with its Lean source, verifies the historical lock file's own digest, requires its exact closed schema/count/identities, rehashes all 152 inventoried dependencies, and exercises the committed process fixtures. The same gate requires the current flat suite's ninth case to equal its typed [`OperatorProtocolBridge`](../A12Kernel/Evidence/OperatorProtocolBridge.lean) artifact rather than trusting a hand-written evidence association.

### Current integrity gap

The current and historical correlation suites are structurally validated, but their projection-to-protocol associations are still maintained manually. The current v2 suite is executed against the current reference; v1 receives only structural integrity checks and remains frozen handover history. Correlation should be converted to a typed descriptor and checked generation pattern before another large capability is added. The current support-manifest and lineage mirrors are drift-checked by the process gate but do not have an independent write command.

## `examples/`: human examples and regression fixtures

### Contents

[`examples/reference-cli/`](../examples/reference-cli/) currently combines two roles:

1. curated request/response pairs intended to be readable and runnable by a user;
2. complete fixture sets used by process and downstream conformance tests.

The eight pairs under [`flat-evidence/`](../examples/reference-cli/flat-evidence/) are frozen outputs generated from the typed 0.2.0 flat capability and retained projection; they are shared as the unchanged eight-case prefix of current flat v2 rather than regenerated in place. The root request/response pairs are maintained as readable golden examples and are explicitly enumerated by the reference-process test; this includes the 0.3.0 directional-polarity control [`empty-unsigned-number-not-equal-negative.request.json`](../examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json), while the correlation subset is referenced by both versioned suites.

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

## Qualification artifacts: tracked policy, ignored packet, project-local receipt, and downstream result

### Contents

The tracked qualification source lives under [`A12Kernel/Qualification/`](../A12Kernel/Qualification/), with [`A12Kernel/MutationQualificationMain.lean`](../A12Kernel/MutationQualificationMain.lean) as its command-line boundary. Pure portable paths and SHA-256 file identities live in shared [`Process/Artifact.lean`](../A12Kernel/Process/Artifact.lean); bounded exact-tree and digest verification lives in [`Process/ArtifactTree.lean`](../A12Kernel/Process/ArtifactTree.lean), with [`Process/Sha256.lean`](../A12Kernel/Process/Sha256.lean) as the hashing boundary. Qualification-specific `Packet.lean` and `MutationResult.lean` define the closed codecs and invariants. `RustPacket.lean` projects the typed plan and frozen Rust Git bytes into an exact packet. `Checker.lean`, `Runner.lean`, and `SelfTest.lean` verify, execute, and adversarially test that process. [`Assets/flat_validation_observer.rs`](../A12Kernel/Qualification/Assets/flat_validation_observer.rs) is tracked source for the canonical fixture-driven observer. These files are process source, not a candidate qualification result and not part of the trusted theorem root.

An exported packet normally lives under ignored `.lake/qualification/<packet-id>/`. Its exact tree contains `PACKET.json`, the generated mutation plan, frozen candidate build inputs with executable modes, the observer, observer-only and semantic patches, expected baseline and mutation observations, source inventories, packet-local verification tools and instructions, and a SHA-256 payload manifest. The packet index binds every role-bearing file and command to the source revision, candidate base revision, compatibility tuple, and execution profile. It is generated output, not committed source and not evidence that any mutation ran.

A returned mutation result is a separate exact directory containing `RESULT.json` and only the raw stdout/stderr logs named and digested by that record. It binds the packet-index digest, source and candidate revisions, plan, baseline inventory, toolchain, exact commands and statuses, actual parsed case/algebra observations, restoration inventories, and assurance class. The current Rust experiment retains its accepted [`flat-validation-empty-logic-v1-rust-v1` mutation result](../../a12-kernel-rust-spike/qualification/flat-validation-empty-logic-v1-rust-v1/RESULT.json) under the downstream candidate's `qualification/` tree at candidate revision `d213005b3972c2acd8f67e87f523a923d69f6a54`; this repository tracks no duplicate mutation result. It separately retains the compact [52-case generated-differential receipt](../qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json). The profile reproduces the compared requests, but the compact green receipt deliberately omits the agreeing per-case response transcripts; it records aggregate distributions and the run identity instead.

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

### Generated differential profile and result lifecycle

The tracked runner source lives under [`A12Kernel/Differential/`](../A12Kernel/Differential/), with [`A12Kernel/GeneratedDifferentialMain.lean`](../A12Kernel/GeneratedDifferentialMain.lean) as its command-line boundary and [`A12Kernel/Process/`](../A12Kernel/Process/) supplying the bounded relay and digest support. The profile belongs under `reference/` because it is a language-neutral, inspectable campaign definition. It is reviewed input, not generated kernel evidence, a support-manifest extension, or a second semantics source.

Run output is first written to an absolute, absent path whose existing non-symlink parent is outside both pinned repositories, such as a new file under `/private/tmp`; an ignored directory inside either checkout is deliberately rejected. A disagreement result retains every differing normalized request and both projected responses plus deterministic minimal witnesses; it must be classified before any expected result changes. The first green run is retained as [`generated-differential-v1.RESULT.json`](../qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json), a compact immutable receipt recording exact source and candidate revisions, profile and executable digests, budgets and actual usage, verdict distributions, and the explicit finite-Lean-account claim. `checkGeneratedDifferential --check-result PROFILE RESULT` is its non-writing strict receipt-consistency gate: it accepts only a profile-bound green agreement receipt, checks the finite counts, distributions, bounds, and claim, and deliberately does not authenticate the historical execution or compare recorded executable digests with a later platform build. The receipt contains no kernel observation and does not transfer a Lean proof to the candidate.

The compact green receipt deliberately omits 52 duplicate per-case request/response transcripts. Its non-profile artifact digests, platform target, elapsed time, and output usage are runner-recorded historical assertions; the checker validates their schema, syntax, platform admission, and bounds but cannot prove that an external historical process produced them. It compares both recorded distributions with the frozen historical distribution rather than recomputing them through today's evaluator. Git review, the runner's preflight/postflight checks, immutable profile/result identities, and the retained receipt therefore form the audit trail; the later checker is a consistency guard, not an execution authenticator. The generator self-test's separate execution of historical requests through today's reference is only a current backward-compatibility audit and does not alter this retained history.

The profile must pin a clean source revision that already contains the generator, relay, and runner. Because adding the profile itself changes the repository revision, the first execution uses a clean disposable checkout at the pinned source revision and supplies the later committed profile by path. The candidate runs from its own clean pinned checkout; build outputs may exist only where that repository ignores them. Any postflight revision, worktree, profile-byte, or executable-digest change makes the run an integrity failure rather than an agreement result.

Once retained, a profile/result pair is historical and immutable. A semantics correction, generator change, response-projection change, resource-bound change, executable change, or candidate revision requires a new profile/result identity. [`TESTING.md`](TESTING.md#bounded-generated-lean-account-differential) owns execution mechanics and commands; the capability kit owns the finite outcome and remaining semantic boundary.

## Evolution by change type

| Project change | `evidence/` | `reference/` | `examples/` | Qualification artifacts |
|---|---|---|---|---|
| Internal refactor, same observable account | Unchanged | Existing shipments unchanged; create a new pinned differential profile only when rerunning | Unchanged | Existing records remain historical |
| Lean semantic correction | Replay unchanged observations; add evidence only if the old boundary was insufficient | Regenerate development shipment or publish a new supported version | Update affected generated/golden responses with review | Run a new qualification for affected candidates |
| Protocol or manifest change | Unchanged | Regenerate or version affected contract | Update affected requests/responses | Run a new protocol qualification |
| New semantic capability | Add focused observation and projection before claiming external correspondence, or mark it `external evidence pending` | Add a closed capability shipment only when its task boundary is research-closed | Add a few curated examples plus generated cases as applicable | Qualify selected consumers separately |
| New kernel version | Add a new evidence bundle | Publish capabilities with the new kernel-behavior identity | Add only separating version examples | Create new candidate records against that identity |
| Evidence correction | Preserve correction provenance and explain why | Regenerate every affected derived shipment | Regenerate affected evidence-derived fixtures | Invalidate or supersede affected qualification claims explicitly |

## Desired repository-wide drift contract

The flat shipment and Rust qualification packet demonstrate checked local artifact graphs, but the repository does not yet have one global graph. Before these trees grow substantially, every committed artifact path or glob should have one recorded owner, role, input set, generator or capture method, compatibility identity, update policy, and non-writing check. A repository-wide gate should derive expected generated output in memory or ignored temporary storage, reject changed, missing, and stale files, validate retained evidence and exported shipment digests, and never rewrite the worktree in CI.

Generation remains an explicit maintainer action followed by review. A green generator run cannot create kernel evidence, approve a semantic correction, or qualify an independent consumer by itself.
