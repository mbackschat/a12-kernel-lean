# Testing methodology

This document owns the test harness and working method for `a12-kernel-lean`. The project tests seven different semantic and process claims—execution of the Lean theory, universal consequences inside that theory, empirical correspondence with kernel 30.8.1, compatibility of the public reference process, finite retained-case conformance of an independent candidate, bounded generated agreement with the Lean account, and mutation sensitivity of a pinned candidate shipment—and deliberately does not collapse them or repository hygiene into one green check.

## The eight harness layers

| Layer | Repository surface | What a pass establishes | What it does not establish |
|---|---|---|---|
| Focused executable locks | [`../A12Kernel/Conformance/`](../A12Kernel/Conformance/) imported by [`../A12Kernel/Conformance.lean`](../A12Kernel/Conformance.lean) | Concrete inputs execute through the Lean definitions and produce the stated values, truth states, verdicts, or rejections | Universal correctness or agreement with the external kernel |
| Trusted proofs and checked non-laws | [`../A12Kernel/Proofs/`](../A12Kernel/Proofs/), [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean), and [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean) | Named theorems hold for every modeled input satisfying their hypotheses; counterexamples prevent a plausible stronger claim from being mistaken for a law | Correctness of the chosen primitive semantics or universal correspondence with kernel code |
| Retained external evidence replay | [`../evidence/`](../evidence/), [`../A12Kernel/Evidence/`](../A12Kernel/Evidence/), and [`../A12Kernel/EvidenceMain.lean`](../A12Kernel/EvidenceMain.lean) | The focused Lean projection agrees with retained portable observations produced by the real pinned kernel on those cases | Exhaustive agreement, hidden kernel intermediate states, or correctness outside the projected fragment |
| Reference-process black box | [`../A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean), [`../examples/reference-cli/`](../examples/reference-cli/), and [`../reference/supported-fragment-v1.json`](../reference/supported-fragment-v1.json) | The compiled public executable obeys its documented JSON bytes, exit status, output-channel, determinism, strict-input, fixture, and manifest contract | New semantic correspondence with the kernel or universal correctness of the transport |
| Independent candidate conformance | [`../A12Kernel/CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean), the [`flat-validation-empty-logic-v1`](../reference/flat-validation-empty-logic-v1.conformance.json) and [`single-group-correlation-v1`](../reference/single-group-correlation-v1.conformance.json) suites, and their indexed fixtures/evidence classifications | A candidate process reproduces the named observable JSON cases deterministically; all compatibility identifiers match the manifest; each case declares whether its response is externally supported, project-defined, or a Lean runtime projection; retained evidence IDs still exist | Correctness outside the selected finite suite, inheritance of Lean proofs, or release readiness of the candidate or capsule; the flat bridge derives its fixtures mechanically, while the correlation suite still has reviewed manual projection links |
| Bounded generated Lean-account differential | [`../A12Kernel/Differential/`](../A12Kernel/Differential/), [`../A12Kernel/Process/Bounded.lean`](../A12Kernel/Process/Bounded.lean), and [`../A12Kernel/GeneratedDifferentialMain.lean`](../A12Kernel/GeneratedDifferentialMain.lean) | Two revision- and digest-pinned black-box executables agree on the complete generated cases of one closed profile within declared process and campaign bounds, or every disagreement and a minimal witness are retained | New kernel evidence, external-kernel correspondence, correctness outside the profile, inheritance of Lean proofs, security isolation, or release approval |
| Mutation qualification | [`../A12Kernel/Qualification/`](../A12Kernel/Qualification/) and [`../A12Kernel/MutationQualificationMain.lean`](../A12Kernel/MutationQualificationMain.lean) | A digest-pinned Rust packet is structurally reproducible; its natural baseline and seven declared mutants execute with the predicted finite observations in a source replay; exact command logs and path-and-byte restoration are checkable in a returned record | Universal candidate correctness, kernel correspondence beyond retained evidence, release approval, or proof that an externally returned attestation's recorded commands historically ran |
| Structural and hygiene gates | [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), `git diff --check`, and worktree checks | Trusted roots contain no banned proof escape hatch, every exported theorem is audited, axiom dependencies are classified, patches are clean, and sibling worktrees remain untouched | Any new semantic fact by itself |

`lake build` runs the first two layers because the library root imports both the conformance root and the trusted proof root, and it builds the reference executable because that executable is a default target. `lake test` runs the retained-evidence executable separately and checks the generated flat handover artifacts against their projection. `lake exe checkReferenceProcess` runs the compiled CLI through an independent process driver, invokes every candidate-runner integrity self-test, and runs both candidate suites against the compiled Lean reference as controls. `lake exe checkCandidateConformance --candidate … --suite …` runs only the selected language-neutral capability suite against an independent process. `lake exe checkBoundedProcess` exercises the bounded relay lifecycle and adversarial resource cases, while `lake exe checkGeneratedDifferential --self-test` checks the closed profile decoder, generator, reference projection, result-contract helpers, and runner guards without claiming that an independent candidate ran. A pinned `checkGeneratedDifferential --run …` is an explicit qualification action because its profile names two exact repository revisions and executables. `lake exe checkMutationQualification --self-test …` exports and validates a packet, executes its complete Rust source replay in a temporary copy, checks the result, and then exercises the strict rejection surface. The trust script inspects the proof closure separately again because successful elaboration alone does not reveal an accidental axiom, omitted theorem-root import, or accidental dependency from a trusted root into differential, process, or qualification code.

## Red/green semantic development

Every new semantic capsule uses red/green TDD.

1. State the exact supported fragment, its observable result domain, its evidence source, the useful law, and the nearest false generalization before adding a general abstraction.
2. Add concrete separating examples under `A12Kernel/Conformance/` against the intended public API.
3. Run the focused module and confirm a meaningful red result: the module, definition, constructor, or behavior is absent or wrong for the expected semantic reason.
4. Implement the smallest total pure definition that makes those examples green.
5. Add an independent declarative relation or judgment only when it exposes a useful boundary, then prove its connection to the executable definition in `A12Kernel/Proofs/`.
6. Capture and retain focused kernel observations through the external a12-dmkits adapter, extend the narrow replay projection, and make `lake test` green.
7. Apply the ownership triggers in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md), update only the documents whose owned facts changed, then run every final gate.

A red run is part of the evidence for the workflow, not a file committed to the repository. A test that was green before the semantic implementation is either not testing the requested behavior or is accidentally passing through an older path.

For a public process or protocol change, write the independent process expectation before adding the decoder or IO route, run `lake exe checkReferenceProcess`, and confirm that it fails for the missing or wrong public behavior. Make the existing checked semantic route satisfy the test; never make a protocol fixture green by introducing a second evaluator.

## Executable Lean examples

A conformance lock is an `example` whose proof evaluates a decidable proposition. For example:

```lean
example : (filteredCounts 1).sumSelected source = .value 7 := by
  native_decide
```

The left side executes the pure Lean function on the concrete fixture. Equality for the result type is decidable, so `native_decide` compiles and evaluates the decision procedure; if it produces `false`, elaboration fails and therefore `lake build` fails. Use `decide` for small structural propositions that reduce economically in the kernel, and `native_decide` for concrete executable fixtures where compiled evaluation materially reduces cost.

Lean tests do not require a JUnit-style runtime runner. The conformance modules are ordinary Lean modules imported by the conformance root: a false `example`, an ill-typed fixture, or an unprovable expected equality prevents elaboration and fails the build. `#eval` remains useful while exploring a new definition and for deliberate smoke output, but printed output alone is not an assertion; once behavior matters, move it behind an `example`, theorem, or retained-evidence comparison that can fail automatically.

`native_decide` is permitted only in conformance examples and other explicitly untrusted executable test surfaces. It is forbidden from the trusted semantics/proof closure by [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), because a general theorem should be supported by an inspectable proof term rather than trusted native execution.

Concrete cases should be separating, not merely numerous. Hold the model, kind, document, and condition fixed while varying one semantic axis. For filtered iteration, pair an invalid consumed cell in a filter-dropped row with the same cell in a kept row; this distinguishes filter-before-consumer semantics from an eager whole-column scan. For captured-outer correlation, pair equality with and without explicit repetition self-exclusion, then add an asymmetric inner-less-than-outer case so reversed or collapsed origins cannot pass accidentally. Keep guard, filter key, and starred consumer in distinct fields: `Count` is the filled outer guard and error target, `StockQty` is the numeric key when the filter needs one, and `UnitWeight` is the selected presence consumer. This separation prevents guard suppression, key classification, and consumer observation from masking one another. For the selected-consumer footprint, use two duplicate-key rows: malformed consumer row 1 must fire only on outer row 1 because it self-drops there and is kept from row 2; moving the malformed consumer to row 2 must mirror the firing row. For filter-state evidence, hold guards and consumers valid while comparing explicit empty with zero, then use a three-row malformed-local witness in which the malformed row is observably not kept while two healthy equal-key siblings still select each other. For operator evidence, place consumer values asymmetrically so the selected relation is recoverable from firing rows: numeric inequality uses keys `5, 5, 9` with only row 3's consumer filled, repetition equality fills only row 2, and repetition less-than fills all consumers to expose predecessors. Include the all-valid control and ordinary, boundary, empty, malformed, and order-sensitive cases whenever that axis is observable.

For checked one-star lowering, separate static legality from runtime routing. [`CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean) varies path form, field kind/group/scope, operator, scale, and origin while holding the expanded model fixed. Equality and inequality reject mixed numeric scales while ordering admits the same fields; missing inner and missing outer origins are distinct route outcomes; invalid, duplicate-path, duplicate-level, and path-derived repeatable-scope inconsistencies are rejected before lowering. The nested false-singleton case locks the root invariant that a field below two repeatable ancestors cannot claim only the inner level, while the sibling-repeatable control remains valid. The public model-derived runtime route formally checks raw cells with the same declaration policy admitted during elaboration, converts unknown, ambiguous, cross-group, and wrong-scope IDs to malformed cells, and rejects row zero or duplicate candidate identities before evaluation. A trusted theorem connects successful raw candidate validation to the semantic context's 1-based/unique `WellFormed` predicate. These cases lock the checked boundary without pretending that arbitrary low-level contexts are valid documents.

Run a focused executable file after its imports have been built:

```sh
lake build A12Kernel.Semantics.Iteration
lake env lean A12Kernel/Conformance/Iteration.lean
lake build A12Kernel.Semantics.Correlation
lake env lean A12Kernel/Conformance/Correlation.lean
lake build A12Kernel.Elaboration.Correlation
lake env lean A12Kernel/Conformance/CorrelationElaboration.lean
```

Run `lake build` before handoff so the same examples also pass through the actual library import graph.

## Reference-process harness and sample data

[`A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) discovers the sibling `a12-kernel-reference` build artifact and invokes it as an operating-system process. It does not call `evaluateText` or any protocol decoder directly, so it covers executable wiring, arguments, stdin/stdout/stderr, and exit behavior in addition to JSON semantics. Lake's `needs` edge builds the tested executable first without making this gate part of the retained-kernel `lake test` claim.

The requests and adjacent expected responses under [`examples/reference-cli/`](../examples/reference-cli/) are committed sample data as well as test inputs. The harness parses each readable expected JSON file and compares the executable's deterministic compact encoding, so whitespace in the maintained fixture is irrelevant while every JSON value is locked. [`PROTOCOL.md`](PROTOCOL.md#regression-checked-sample-data) gives representative runnable examples, and the machine-readable suites own the complete finite capability inventories; this methodology document does not duplicate either list.

The eight fixtures under [`examples/reference-cli/flat-evidence/`](../examples/reference-cli/flat-evidence/) are not manually assembled duplicates. [`FlatProtocolBridge.lean`](../A12Kernel/Evidence/FlatProtocolBridge.lean) projects them from the retained typed flat cases, checks that each generated request decodes to the same replay input, evaluates it through the public reference, classifies the evidence boundary, and generates the [`capability descriptor`](../reference/flat-validation-empty-logic-v1.capability.json), [`conformance suite`](../reference/flat-validation-empty-logic-v1.conformance.json), and post-cold [`mutation qualification plan`](../reference/flat-validation-empty-logic-v1.mutation-plan.json). `lake exe syncFlatHandover --check` compares every generated artifact and the manifest boundary without writing; `lake exe syncFlatHandover --write` regenerates the descriptor, suite, mutation plan, and fixtures after an intentional owned-input change.

The mutation plan is source-maintainer test planning, not retained kernel evidence and not proof that a candidate was mutated. It derives the baseline and predicted deltas from the typed capability and live verdict algebra, requires one mutation at a time plus restoration, and distinguishes observable suite sensitivity from evidence that the requested internal mechanism actually changed. [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#seeded-divergence-exercises) owns the exact exercises and candidate record requirements; the [qualification harness](#rust-mutation-qualification) owns their executable packet and strict result check.

Generated-in-test adversaries cover hostile transport, numeric and path bounds, closed-object decoding, version and operation mismatches, model/cell/repeatable validation, operation-specific near misses, candidate topology, unsupported semantic constructors, invocation classes, and deterministic repeated success. The executable test source is authoritative for the exact adversarial matrix. `--manifest` output is compared structurally with [`reference/supported-fragment-v1.json`](../reference/supported-fragment-v1.json), ensuring the shipped readable mirror agrees with the Lean-generated manifest without requiring identical whitespace.

Run the public process gate with:

```sh
lake exe checkReferenceProcess
```

[`PROTOCOL.md`](PROTOCOL.md) owns the exact public contract and gives the invocation pattern shared by every request fixture. This harness establishes compatibility of that boundary; it adds no kernel observation and therefore does not change the external-evidence count.

### Independent candidate suites

[`flat-validation-empty-logic-v1.conformance.json`](../reference/flat-validation-empty-logic-v1.conformance.json) and [`single-group-correlation-v1.conformance.json`](../reference/single-group-correlation-v1.conformance.json) are portable downstream indices. Each pins the capability, operation, reference-semantics, protocol, manifest-schema, and kernel-behavior identities plus the support-manifest path, and each case names a normalized request, expected response, separating coverage labels, evidence kind, projection, retained case ID, exact externally supported projection, and expected-response source. [`A12Kernel/CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) uses bounded duplicate-safe JSON parsing for all inputs, enforces closed suite/case/evidence objects, validates the compatibility tuple and finite evidence boundary against selected support-manifest members, checks the allowed evidence/source combination and case-ID existence, invokes the candidate directly without a shell, requires exit `0`, empty standard error, normalized JSON plus a final newline, and byte-identical repeated output, then compares expected and actual JSON structurally so language-specific object-key ordering is irrelevant. Support-manifest and retained-projection objects intentionally remain extensible outside the members this runner consumes.

The flat [`capability descriptor`](../reference/flat-validation-empty-logic-v1.capability.json), suite, and [fixtures](../examples/reference-cli/flat-evidence/) are generated through the checked projection-to-protocol bridge before an independent implementation starts. The bridge preserves a case-specific distinction between what the external observation supports and what the exact Lean response supplies; [`EVIDENCE.md`](EVIDENCE.md) and the [`flat kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) own that classification. The correlation kit owns its different projection-association boundary. These integrity levels must not be blurred.

The selected manifest operation must be unique and its `externalEvidenceBoundary` must agree with the suite's identity, finite claim scope, and case composition. The runner's in-memory integrity self-test validates the canonical metadata and evidence links, then mutates compatibility, manifest, count, evidence, duplicate-member, and closed-object boundaries and requires rejection. Run a suite explicitly:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/flat-validation-empty-logic-v1.conformance.json
```

Run the suite against the reference as a control:

```sh
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/flat-validation-empty-logic-v1.conformance.json
```

Replace `--candidate` with a Rust, Kotlin, or TypeScript executable to test that implementation without requiring it to implement the other operation, `--manifest`, or Lean's compact key order. A suite establishes only its indexed observable cases and does not transfer Lean's theorems to the candidate; use the law index in [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#law-index-for-downstream-tests) or [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md#law-index-for-property-tests) as applicable. The flat capability remains a development cold-handover slice, not full flat release closure. This retained-case candidate runner has no wall-clock timeout or streamed output cap and must not be used for untrusted binaries; the separately bounded generated-differential lane below does not retroactively add those controls here.

### Bounded generated Lean-account differential

[`A12Kernel/Differential/Profile.lean`](../A12Kernel/Differential/Profile.lean) and [`Generated.lean`](../A12Kernel/Differential/Generated.lean) define and validate the first closed generated profile without adding a second evaluator. Every request is normalized public protocol JSON, is decoded back through the existing strict public decoder, and is evaluated by the existing reference adapter. The generator requires unique case IDs and request bytes, the exact expected model and operation, strict cell ordering, exact structural metrics, deterministic enumeration, and declared per-case and aggregate budgets.

The complete domain has 52 requests over one non-repeatable `GeneratedForm` model with absolute paths and exactly three fields: unsigned scale-2 Number `N`, Boolean `B`, and Confirm `C`.

- Twelve leaf/cell-state cases cross `N == 0`, `B == true`, `C != true`, and `FieldNotFilled(B)` with sparse empty, parsed Boolean true, and rejected-malformed input.
- Thirty-two verdict-algebra cases cross `And` and `Or` with every ordered pair drawn from concrete atoms producing `notFired`, `fired.value`, `fired.omission`, and `unknown` in the fixed content-bearing context.
- Eight row-gate cases cross `And` and `Or` with every ordered pair of an empty-row-ineligible comparison and an empty-row-eligible `FieldNotFilled(N)` clause while `hasContent` is false.

The self-test requires all 52 generated requests to be distinct and repeatable and checks the in-process Lean reference distribution of 14 `notFired`, 11 `fired.value`, 13 `fired.omission`, and 14 `unknown`. These counts guard the generator and projection; they are not an independent-candidate result or new kernel evidence.

Run the bounded process and generator/runner self-tests with:

```sh
lake exe checkBoundedProcess
lake exe checkGeneratedDifferential --self-test
```

Validate a committed or proposed profile without executing either target with:

```sh
lake exe checkGeneratedDifferential --check-profile <profile.json>
```

Run an actual pinned comparison only from the exact clean checkouts named by the profile. The result must be an absolute, absent file whose existing non-symlink parent is outside both repositories:

```sh
lake exe checkGeneratedDifferential --run \
  --profile <profile.json> \
  --reference-repo <clean-reference-checkout> \
  --reference .lake/build/bin/a12-kernel-reference \
  --candidate-repo <clean-candidate-checkout> \
  --candidate <relative-candidate-executable> \
  --result /private/tmp/a12-flat-generated-result.json
```

[`A12Kernel/Differential/Runner.lean`](../A12Kernel/Differential/Runner.lean) requires both repository roots to be clean and at the profile revisions before and after the campaign, accepts only portable relative executable paths contained by those roots, and binds the profile, runner, relay, reference, and candidate bytes by SHA-256. The closed profile names `a12-kernel-lean` and `a12-kernel-rust-spike`; these are stable metadata identities, while the runner verifies the supplied local roots through exact clean `HEAD` revisions, containment, and file digests rather than a remote URL. It runs exactly one job and invokes reference then candidate for every case. Each invocation must exit zero, leave stderr empty, and emit exactly one strict UTF-8 JSON response line in the declared four-verdict projection. The result records measured monotonic campaign wall-clock usage as `elapsedMilliseconds`, both distributions, every disagreement with its full request and response pair, and one deterministic minimal witness per distinct reference/candidate projection pair. A process or integrity failure is recorded separately from a semantic disagreement.

The profile declares request shape and bytes, aggregate request and dual-process input bytes, per-process timeout and cleanup deadlines, poll interval, stdout and stderr caps, aggregate elapsed and output budgets, and maximum result bytes. The runner reserves aggregate capacity before an invocation, streams each output channel with a limit-plus-one overflow check, terminates the owned process group on timeout, overflow, and successful completion, bounds cleanup, and refuses to overwrite an existing result. [`A12Kernel/ProcessTestMain.lean`](../A12Kernel/ProcessTestMain.lean) locks exact-cap acceptance, cap-plus-one and infinite-output rejection, simultaneous channel pressure, blocked large input, timeout, nonzero candidate status separation, invalid UTF-8 transparency, strict relay-status parsing, and descendant cleanup on failure and success.

This is a resource-bounded cooperative process harness for the pinned macOS/Linux POSIX contract, not a security sandbox. The candidate inherits the caller's credentials, working directory, and environment, and could deliberately escape or attack that context. Use it only with implementation candidates under the caller's control. Its result claim is `finiteLeanAccountDifferential` for the generated profile cases only: agreement means that the two black boxes produced the same projected verdicts for those cases; `kernelEvidence` remains `none`, so the run establishes neither new external-kernel correspondence nor correctness outside the profile.

### Rust mutation qualification

[`A12Kernel/Qualification/`](../A12Kernel/Qualification/) turns the generated flat mutation plan into an exact executable shipment for the frozen Rust implementation revision. The packet index pins this Lean source revision, the Rust candidate base revision and complete classified build-input closure, the compatibility tuple, a macOS/Homebrew Rust execution profile, tool versions, every payload digest, exact commands, expected observations, complete baseline and mutant inventories, and seven one-at-a-time patches. Export reads candidate bytes from Git objects and requires clean source and candidate checkouts; it never patches or builds in the sibling checkout. The packet is generated under ignored project storage or another new disposable directory and must be distributed with the SHA-256 of `PACKET.json` supplied out of band.

The packet-owned Rust observer consumes the frozen canonical conformance suite and each indexed request fixture instead of reconstructing those eight requests. It rejects a missing, extra, reordered, or renamed case, sends the fixture bytes through the candidate's public evaluator, and captures all eight verdicts. The natural baseline and connective mutations also capture all 32 ordered verdict-algebra inputs. The checker binds the parsed captured observation to the record before comparing it with the packet expectation, so a result cannot substitute predicted case or algebra values for the observer's actual stdout.

Run the complete source-side replay and checker self-test with:

```sh
lake exe checkMutationQualification \
  --self-test \
  --candidate-repo ../a12-kernel-rust-spike
```

This command writes only in an automatically removed temporary directory. It exports and verifies the real packet, runs the natural gate, all seven mutations, their reverse-patch and full verification commands, and the final restoration gate, then requires the strict checker to accept the captured `sourceExecutedReplay`. It subsequently runs 36 independent adversarial guards over packet shape and digests, compatibility and revision identity, mutation order and source-owned patch bytes, strict result JSON, exact file trees, globally collision-free log paths, command records, log identities and content, actual observation records, assurance class, restoration inventories, resource limits, candidate-revision closure, and preservation of a pre-existing export directory. One guard replaces a captured mutation observer log with different but syntactically valid observation JSON, updates that log's digest, leaves the record unchanged, and requires rejection specifically because the recorded case results differ from captured stdout. Another replaces one mutation with a valid-applying observer-only patch and updates its local inventory, proving that packet self-consistency cannot substitute for the reviewed source-owned mutation projection. Each guard must fail with the intended diagnostic fragment; merely throwing at some unrelated boundary does not count as a passing negative test.

Export and independently preflight a packet with:

```sh
lake exe checkMutationQualification \
  --export \
  --candidate-repo ../a12-kernel-rust-spike \
  --output .lake/qualification/flat-validation-empty-logic-v1-rust-v1

lake exe checkMutationQualification \
  --verify-packet \
  --candidate-repo ../a12-kernel-rust-spike \
  --packet .lake/qualification/flat-validation-empty-logic-v1-rust-v1/PACKET.json
```

`--output` must name a new directory. After a separate isolated session returns its exact result directory, check it with:

```sh
lake exe checkMutationQualification \
  --check \
  --candidate-repo ../a12-kernel-rust-spike \
  --packet .lake/qualification/flat-validation-empty-logic-v1-rust-v1/PACKET.json \
  --result <returned-result>/RESULT.json
```

Packet verification and result checking must execute from a clean source checkout whose `HEAD` equals the packet's `sourceRevision`. This is a source-owned-projection guard: even a later documentation-only commit is intentionally rejected rather than silently reinterpreting a historical packet through new source. When the main checkout has advanced, use a disposable checkout at the pinned revision and pass the retained packet, candidate, and result paths into that checker. A later candidate commit may contain the qualification record or other out-of-closure material only when the packet's candidate base remains its ancestor and every classified build-input path, byte, and executable mode is unchanged.

The assurance-class distinction is part of the claim. The built-in runner emits `sourceExecutedReplay` because this process invoked and captured the commands in a disposable baseline copy. `--check` accepts `isolatedSessionAttestation`: it establishes that the returned packet identity, command/status records, exact log tree and digests, observer outputs, and restored path-and-byte inventories are internally consistent with the packet, but files cannot prove the historical execution of an external session. Both are finite qualification results, not candidate correctness proofs, release approval, or new kernel evidence.

The strict artifact boundary rejects symlinks, non-files, empty directories, unsafe or case-fold-colliding portable paths, and missing or additional files. A portable path is capped at 1,024 UTF-8 bytes, 255 bytes per segment, and 64 segments; packet/result JSON is capped at 4 MiB; each payload or raw log is capped at 16 MiB; and each exact packet, result, or candidate source inventory is capped at 512 files and depth 16. These are post-execution artifact limits, not complete process sandboxing. The mutation-qualification runner and retained-case candidate-conformance process still have no wall-clock timeout, no streamed stdout/stderr cap before `IO.Process.output` buffers them, and no aggregate byte budget across all packet or result files. Add those bounds before using either of those runners with untrusted binaries or high-volume qualification suites. The generated-differential runner has its own narrower bounded process path and does not change this qualification lane's execution contract.

The architecture follows Cedar's separation of `Spec`, `Validation`, and `Thm` from `DiffTest`, unit-test, and FFI roots, but this lane deliberately remains subprocess-based. The clean-room rule forbids a kernel FFI, and binding the packet to Rust through an in-process FFI would weaken its language-neutral consumer boundary. The digest-bound external-attestation model is A12-specific rather than a claim inherited from Cedar. [`ARCHITECTURE.md`](ARCHITECTURE.md#mutation-qualification-is-a-separate-replayable-process-lane) owns that dependency decision; [`ARTIFACTS.md`](ARTIFACTS.md#qualification-artifacts-tracked-source-ignored-packet-and-immutable-result) owns packet and result retention.

## Universal proofs and counterexamples

Proof modules quantify over arbitrary inputs and use induction, case analysis, rewriting, or previously proved laws to construct proof terms. Lean's kernel checks those terms. The theorem statement—especially its hypotheses, direction, and result domain—is the claim; theorem counts and proof-line counts are not quality measures.

When an executable enumerator has meaningful independent content, follow the audited Cedar pattern: define an ordered declarative relation separately, prove execution-to-relation soundness and relation-to-execution completeness, and package them as an exact bridge. Preserve ordered-list equality when order or multiplicity can become observable; a membership equivalence is too weak for an ordered A12 document.

Read-footprint theorems should be stated at the semantic observation boundary. The correlated `evalGuardedAnyFilledOn_filter_before_consumer` theorem assumes equal selection, equal validation observation of the outer guard, and equal validation observations of consumer cells in selected rows; it deliberately does not require equality of raw checked cells or any dropped consumer. This makes the proved noninterference exactly as strong as the evaluator's read surface and no stronger.

The checked-elaboration theorems in [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean) establish structural obligations: checked wrappers expose stored model/core certificates, admitted references have a unique matching declaration, the raw-to-checked route uses that declaration's policy, other IDs fail closed, and one-group well-formedness implies the operator-specific scale law. These are not source-to-core semantic-preservation theorems. Such a claim would require an independent dynamic semantics for the surface language, which this capsule deliberately does not yet define.

Each useful law should be paired with the nearest plausible false generalization as a concrete checked non-law. For example, a same-group star reopens the group and spans all candidate rows; the proposition that it collapses to the current row must have an explicit counterexample before `$` correlation is introduced.

Every exported theorem under `A12Kernel/Proofs/` must be imported by [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean) and registered with `#print axioms` in [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean). The trust script fails if a proof file is missing from the root, a theorem is missing from the audit, a trusted source contains `sorry`, `admit`, a project axiom, `unsafe`, `partial`, or `native_decide`, or the audited closure depends on an unexpected axiom.

## Kernel evidence and differential replay

Kernel differential testing is the empirical backbone, but the kernel never becomes a dependency of this repository. Focused scenarios run externally through the a12-dmkits adapter in the local `../a12-rulekit/` checkout. The Groovy-dynamic kernel result is the observation anchor, the static-Java kernel strategy detects a strategy split, and the a12-dmkits interpreter is a clean-room triangulation peer that may reveal a disagreement but is never the oracle.

Only portable own-domain artifacts—standalone model, placements or complete diagnostic draft, operation, complete observed signatures or structured diagnostics, kernel version, and any divergence record—are retained under `evidence/`. A narrow typed projection contains the input needed by the current Lean fragment but never a separately hand-authored expected Lean result or diagnostic code. The replay driver derives the focused expectation from the complete external observation, executes the public Lean semantics or checked elaborator, and exits nonzero on mismatch. The current driver keeps flat/path/required, uncorrelated iteration, captured-outer correlation, and checked correlation elaboration in four separate closed projections.

Runtime correlation replay validates 1-based unique rows, declared guard and consumer references, a complete ordered outer-row pointer map, and both inner and outer origins. It derives firing membership from the retained canonically sorted focused signatures, restores those firings to the projection's document-row order, and compares the result with Lean; the external evidence therefore establishes firing membership, not kernel emission order. The replay also binds the typed filter to the retained model without a general parser: unique group and Number-field paths and configurations, a unique focused rule, authored absolute-or-relative condition group/field paths resolving to the projected absolute entities, the error entity resolving to the guard field, and a canonical rendering of the admitted condition subset must all match exactly. Classified projected cells and row IDs remain a review-trusted transcription of the retained placements until a general instance decoder exists.

[`correlation-elaboration-projection.json`](../evidence/kernel-30.8.1/correlation-elaboration-projection.json) adds a separate closed static-authoring lane defined by [`CorrelationElaborationSchema.lean`](../A12Kernel/Evidence/CorrelationElaborationSchema.lean) and replayed by [`CorrelationElaborationReplay.lean`](../A12Kernel/Evidence/CorrelationElaborationReplay.lean). Its four cases retain two exact seeded DM-JSON model snapshots and the complete diagnostic candidate drafts. The driver first pins each whole model file by SHA-256, then requires `en_US`, unique declaring/projected groups with canonical names and physical parents, repeatability without a repeatable proper ancestor, unique Number fields with canonical names/immediate parents and exact kind/scale/signedness, the stored valid seed rule identity, complete candidate draft identity, capture provenance, and diagnostic source/routing before it calls the public elaborator. The projection renderer accepts only unquoted ASCII identifiers that are not English lexer keywords, so a structured path cannot inject or collide with concrete condition syntax; general quoted identifiers remain outside the lane. Replay compares the Lean result with the full ordered `diagnostics[].code` list from the observation; the projection and artifacts contain no separate expected code, and the accepted mixed-scale `<` case is therefore checked against the retained empty diagnostic list. Generic executable guards reject moved or renamed projected entities and hierarchy errors. Focused mutations of one real retained diagnostic fixture exercise the digest, language, nested-ancestry, complete-draft and seed-identity, provenance, and diagnostic source/routing rejection paths, while every retained case crosses the positive binding gate; additional examples lock renderer injection and keyword collisions, error/guard routing outside the star, and unmapped `missingOuter`.

This static lane maps only `missingInner` to `MVK_NO_ITERATION_FOR_WILDCARD`, `equalityScaleMismatch` to `MVK_INVALID_COMPARE_DEC_PLACES`, and inner-origin `fieldOutsideGroup` to `MVK_INVALID_ITERATION_IN_FILTER_CONDITION`. Outer-origin `fieldOutsideGroup` and every other Lean error fail closed as unclassified. In particular, `missingOuter` is not assigned a kernel diagnostic because all-inner `Having` is valid uncorrelated authoring and must be handled by the earlier route.

For `$` evidence, retain the actual executed stored condition in the standalone DM-JSON model. A typed origin projection is useful for Lean replay but cannot replace the raw condition because a formatter or conversion path may silently lose a `$`-bearing conjunct. Preserve full VALUE/OMISSION signatures even while the current truth-only replay deliberately compares only firing rows and pointers.

Observable boundaries must stay explicit. Validation output can establish that an authored message fired or was silent and can preserve its observed VALUE/OMISSION signature; it cannot generally distinguish the kernel's hidden `unknown` from `false`. When the Lean capsule deliberately defers a dimension such as filtered-result polarity, replay compares only the admitted truth/firing projection while retaining the full external signature for the later capsule.

[`EVIDENCE.md`](EVIDENCE.md) owns the exact retained case inventory, current coverage, provenance, and limits. Testing changes when the replay mechanism or capture procedure changes; adding cases updates the evidence inventory without copying their live count or complete semantic list here.

External capture may write only under paths already ignored by the sibling repository. Before capture, record the sibling's visible status and verify the disposable path with `git check-ignore`. Create an ignored disposable adapter copy under `../a12-rulekit/build/`, invoke the existing [`CorpusEngines`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusEngines.kt) or [`CorpusCapture`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusCapture.kt) patterns there, and collect Groovy-dynamic, static-Java, and interpreter results without modifying live tracked sources. Do not run the live [`CorpusGenerator`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusGenerator.kt), because its normal job rewrites tracked corpus output. Copy only the portable own-domain model and observation artifacts into this repository, remove the disposable source and output, and confirm afterward that the sibling's tracked and visible-untracked status is exactly unchanged. Never leave a temporary source, model, projection, or generated corpus case visible in a sibling worktree.

## Final gate

Run the complete gate from the repository root:

```sh
lake build
lake test
lake exe syncFlatHandover --check
lake exe checkReferenceProcess
lake exe checkBoundedProcess
lake exe checkGeneratedDifferential --self-test
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v1.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/flat-validation-empty-logic-v1.conformance.json
lake exe checkCandidateConformance --self-test --suite reference/single-group-correlation-v1.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/single-group-correlation-v1.conformance.json
lake exe checkMutationQualification --self-test --candidate-repo ../a12-kernel-rust-spike
./scripts/check-lean-trust.sh
git diff --check
git diff --exit-code -- spec/
git status --short
git -C ../a12-kernel status --short
git -C ../a12-rulekit status --short
git -C ../a12-kernel-rust-spike status --short
```

Interpret failures by layer. A conformance failure means a concrete Lean behavior changed. A proof failure means the definition no longer supports the stated universal law or the proof needs legitimate repair. An evidence mismatch means the Lean projection and retained kernel observation disagree and must be investigated at the semantic definition or projection boundary; never relax the expected result merely to make it green. A reference-process failure means the public transport, executable wiring, fixture, or manifest changed and must be reconciled with [`PROTOCOL.md`](PROTOCOL.md). A candidate-suite failure means the suite/evidence linkage or candidate observable changed and must be classified using [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md); agreement with the reference is not allowed to overwrite external evidence. A bounded-process failure means the relay lifecycle, byte/deadline limit, status separation, or process-group cleanup invariant changed. A generated-differential failure means profile/generator integrity, a pinned input, the process contract, or a candidate/reference projection disagreed; preserve the result and classify the recorded failure or minimal witness without turning Lean agreement into a kernel-evidence claim. A qualification failure means the packet projection, frozen candidate closure, mutation sensitivity, actual captured observation, command policy, or restoration invariant disagrees; preserve the exact packet/result and investigate that boundary instead of editing an expected observation or weakening the checker. A trust failure means the theorem closure or audit is incomplete even if ordinary compilation passed. Sibling status must be unchanged from the recorded pre-run baseline and should be clean; if a sibling was already visibly dirty, report that pre-existing state rather than touching or concealing it.

## Capsule test checklist

- The red run failed for the intended missing or incorrect behavior.
- Concrete cases separate ordinary, boundary, empty, malformed, selection, and ordering behavior as applicable.
- Unsupported syntax or semantic axes fail closed or are unrepresentable.
- The useful theorem states the smallest defensible law with exact hypotheses.
- The nearest stronger false claim has a checked counterexample.
- Every exported theorem is in the trusted root and axiom audit.
- Focused portable kernel observations exist, or the implementation map says `external evidence pending`.
- The replay derives expectations from retained external output rather than duplicating them in Lean-shaped data.
- If the flat shipment or mutation plan changed, the exact qualification packet source replay and adversarial checker self-test pass, with actual observer output distinct from typed expectations.
- If a generated profile or differential result changed, its closed generator self-test, bounded-process gate, profile check, and exact pinned run pass, with the finite Lean-account claim kept separate from retained kernel evidence.
- `lake build`, `lake test`, any applicable reference-process, bounded-process, generated-differential, candidate-conformance, and mutation-qualification gates, the trust audit, and patch/worktree hygiene gates all pass.
