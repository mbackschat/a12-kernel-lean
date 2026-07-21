# Testing methodology

This document owns the test harness and working method for `a12-kernel-lean`. The project tests five live semantic and process claims—execution of the Lean theory, universal consequences inside that theory, empirical correspondence with kernel 30.8.1, compatibility of the public reference process, and finite retained-case conformance of an independent candidate—and deliberately does not collapse them or repository hygiene into one green check. The completed Rust generated-differential and mutation campaigns remain historical records, not live harness layers.

## Default assurance cadence

The accepted evidence consolidation divides work into three tiers. Tier 1 is the default for a semantic capsule: red/green executable examples, the smallest total definition, proof spine, nearest non-law, assumptions, trust audit, and an explicit evidence status. Tier 2 batches related clauses into one focused external calibration family and replays a compact retained semantic account from an existing suitable route or an accepted purpose-specific handback. Tier 3 runs protocol, independent-candidate, mutation, packaging, and release qualification only for a real shipment or consumer. [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) owns the exact trust split, budgets, migration, and stop conditions.

An unavailable external observation no longer blocks unrelated internal semantics or theorem work. Mark the capsule `external evidence pending`, keep the claim narrow, and schedule the smallest useful family calibration. It still blocks a kernel-correspondence-complete or shipment-ready claim.

## The six harness layers

| Layer | Repository surface | What a pass establishes | What it does not establish |
|---|---|---|---|
| Focused executable locks | [`../A12Kernel/Conformance/`](../A12Kernel/Conformance/) imported by [`../A12Kernel/Conformance.lean`](../A12Kernel/Conformance.lean) | Concrete inputs execute through the Lean definitions and produce the stated values, truth states, verdicts, or rejections | Universal correctness or agreement with the external kernel |
| Trusted proofs and checked non-laws | [`../A12Kernel/Proofs/`](../A12Kernel/Proofs/), [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean), and [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean) | Named theorems hold for every modeled input satisfying their hypotheses; counterexamples prevent a plausible stronger claim from being mistaken for a law | Correctness of the chosen primitive semantics or universal correspondence with kernel code |
| Retained external evidence binding | [`../evidence/`](../evidence/), [`../A12Kernel/Evidence/`](../A12Kernel/Evidence/), [`../A12Kernel/EvidenceMain.lean`](../A12Kernel/EvidenceMain.lean), and the public association checks in [`../A12Kernel/CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) | The focused Lean projection agrees with 51 compact non-public observations, and the 25 public suite cases match their exact retained normalized inputs and supported observations | Exhaustive agreement, hidden kernel intermediate states, or correctness outside the projected fragment |
| Reference-process black box | [`../A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean), [`../examples/reference-cli/`](../examples/reference-cli/), and current [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json) | The compiled public executable obeys its documented JSON bytes, exit status, output-channel, determinism, strict-input, fixture, current-manifest, and current V2 control contract | New semantic correspondence with the kernel or universal correctness of the transport |
| Independent candidate conformance | [`../A12Kernel/CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) and the current [`flat-validation-empty-logic-v2`](../reference/flat-validation-empty-logic-v2.conformance.json) and [`single-group-correlation-v2`](../reference/single-group-correlation-v2.conformance.json) suites | A candidate process reproduces the selected observable JSON cases deterministically within the runner's per-invocation resource bounds; the suite's compatibility identifiers agree with its committed support manifest; each case declares whether its response is externally supported, project-defined, or a Lean runtime projection; retained evidence IDs still exist | Correctness outside the selected finite suite, inheritance of Lean proofs, release readiness, security isolation, an aggregate campaign budget, or an independently advertised candidate identity—the runner does not invoke the candidate's `--manifest` |
| Structural and hygiene gates | [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), `git diff --check`, and worktree checks | Every project Lean source has an explicit zone; logical, conformance, and library closures contain only positively admitted zones; every elaborated declaration in logical modules is checked for logical and compiled-behavior escape hatches; the named proof-spine registry is complete for manually authored exported theorems; patches are clean; and sibling worktrees remain untouched | Any new semantic fact by itself |

`lake build` runs the first two layers because the library root imports both the conformance root and the trusted proof root, and it builds the reference executable because that executable is a default target. `lake test` separately replays 51 compact non-public evidence cases. `lake exe checkReferenceProcess` runs the compiled CLI through an independent process driver, verifies the current manifest, binds the 25 public suite cases to their exact compact evidence associations, invokes structural integrity self-tests for the current V2 suites, and runs those suites against the compiled Lean reference as controls. `lake exe checkCandidateConformance --candidate … --suite …` runs only the selected language-neutral suite against an independent process through the shared bounded relay; it does not query that process for a manifest. `lake exe checkBoundedProcess` exercises the bounded relay lifecycle and adversarial resource cases. The trust script enumerates every project Lean source, rejects an unclassified path, checks each root's positive zone closure, and separately inspects the actual imported logical environment because successful elaboration alone does not classify unused project axioms, opaque/partial stubs, compiler substitutions, foreign entry points, omitted theorem-root imports, or accidental process dependencies.

## Red/green semantic development

Every new semantic capsule uses red/green TDD.

1. State the exact supported fragment, its observable result domain, its evidence source, the useful law, and the nearest false generalization before adding a general abstraction.
2. Add concrete separating examples under `A12Kernel/Conformance/` against the intended public API.
3. Run the focused module and confirm a meaningful red result: the module, definition, constructor, or behavior is absent or wrong for the expected semantic reason.
4. Implement the smallest total pure definition that makes those examples green.
5. Add an independent declarative relation or judgment only when it exposes a useful boundary, then prove its connection to the executable definition in `A12Kernel/Proofs/`.
6. Replay any already available matching observation. Otherwise mark the capsule `external evidence pending` and add it to the smallest coherent Tier 2 calibration family; do not build packet machinery in the semantic change.
7. Apply the ownership triggers in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md), update only the documents whose owned facts changed, then run the applicable tier gate below.

A red run is part of the evidence for the workflow, not a file committed to the repository. A test that was green before the semantic implementation is either not testing the requested behavior or is accidentally passing through an older path.

For a public process or protocol change, write the independent process expectation before adding the decoder or IO route, run `lake exe checkReferenceProcess`, and confirm that it fails for the missing or wrong public behavior. Make the existing checked semantic route satisfy the test; never make a protocol fixture green by introducing a second evaluator.

## Executable Lean examples

A conformance lock is an `example` whose proof evaluates a decidable proposition. For example:

```lean
example : (filteredCounts 1).sumSelected source = .value 7 := by
  native_decide
```

The left side executes the pure Lean function on the concrete fixture. Equality for the result type is decidable, so `native_decide` compiles and evaluates the decision procedure; if it produces `false`, elaboration fails and therefore `lake build` fails. Its successful proof is admitted through Lean's native-decision axiom rather than reconstructed by kernel reduction, so the native compiler and runtime join the trust base for that example. Use `decide` for small structural propositions whose proof reduces economically in the kernel, and reserve `native_decide` for concrete executable fixtures in explicitly nontrusted test lanes where compiled evaluation materially reduces cost.

Lean tests do not require a JUnit-style runtime runner. The conformance modules are ordinary Lean modules imported by the conformance root: a false `example`, an ill-typed fixture, or an unprovable expected equality prevents elaboration and fails the build. `#eval` remains useful while exploring a new definition and for deliberate smoke output, but printed output alone is not an assertion; once behavior matters, move it behind an `example`, theorem, or retained-evidence comparison that can fail automatically.

`native_decide` is permitted only in conformance examples and other explicitly nonlogical executable test surfaces. It is forbidden from the logical semantics/proof closure by [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), because an axiom-backed native result is suitable as a regression lock but not as evidence that the theorem root depends only on the audited logical axioms. Adding a new source directory is itself a red trust test until that directory receives an explicit zone; a name omitted from an old blacklist is never admitted by default.

Concrete cases should be separating, not merely numerous. Name the realistic wrong account—wrong order, empty substitution, polarity, unknown collapse, scope or row, or poison timing—hold unrelated inputs fixed, vary one semantic axis, and retain one case per independent branch. Exact matrices belong in their family conformance modules rather than this generic method; [`Correlation.lean`](../A12Kernel/Conformance/Correlation.lean), [`CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean), [`NumericTarget.lean`](../A12Kernel/Conformance/NumericTarget.lean), the String computation modules, and [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) are worked examples.

For checked lowering, distinguish static rejection from runtime routing. Reject unresolved, ambiguous, wrong-kind, wrong-scope, and invalid-topology inputs before lowering; prove only that successful checked wrappers carry their structural certificates; keep exact rejection matrices in the owning family module. Do not describe those certificates as surface-to-core semantic preservation.

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

The eight fixtures under [`examples/reference-cli/flat-evidence/`](../examples/reference-cli/flat-evidence/) were mechanically produced from retained typed flat cases, the historical 0.2.0 verdict table, and case-level observation classifications. They remain unchanged inputs for the corresponding current V2 cases. The deleted bridge, artifacts, hashes, and recovery revisions are recorded in the [historical archive](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md); `checkReferenceProcess` tests the retained fixtures and current V2 suites rather than reconstituting or digest-checking the retired shipment.

Generated-in-test adversaries cover hostile transport, numeric and path bounds, closed-object decoding, version and operation mismatches, model/cell/repeatable validation, operation-specific near misses, candidate topology, unsupported semantic constructors, invocation classes, and deterministic repeated success. The executable test source is authoritative for the exact adversarial matrix. `--manifest` output is compared structurally with current [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json), ensuring the shipped readable mirror agrees with the Lean-generated manifest without requiring identical whitespace. The candidate-conformance control also loads the SHA-pinned compact [validation bundle](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), requires each selected evidence case's exact normalized request, and compares the suite response only at the observation's declared fidelity. This single association check covers all 25 current public cases, including the directional witness, without a case-specific bridge.

Run the public process gate with:

```sh
lake exe checkReferenceProcess
```

[`PROTOCOL.md`](PROTOCOL.md) owns the exact public contract and gives the invocation pattern shared by every request fixture. This harness establishes compatibility of that boundary; it adds no kernel observation and therefore does not change the external-evidence count.

### Independent candidate suites

[`flat-validation-empty-logic-v2.conformance.json`](../reference/flat-validation-empty-logic-v2.conformance.json) and [`single-group-correlation-v2.conformance.json`](../reference/single-group-correlation-v2.conformance.json) are the current portable downstream indices for reference semantics 0.3.0. Each pins the capability, operation, reference-semantics, wire-protocol, manifest-schema, and kernel-behavior identities plus the support-manifest path, and each case names a normalized request, expected response, separating coverage labels, evidence kind, projection, retained case ID, exact externally supported projection, and expected-response source. [`A12Kernel/CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) uses bounded duplicate-safe JSON parsing for all inputs, enforces closed suite/case/evidence objects, validates the suite's compatibility tuple and finite evidence boundary against selected members of its committed support manifest, checks the allowed evidence/source combination and case-ID existence, invokes the candidate directly without a shell, requires exit `0`, empty standard error, normalized JSON plus a final newline, and byte-identical repeated output, then compares expected and actual JSON structurally so language-specific object-key ordering is irrelevant. It does not query a candidate manifest; a separate qualification record must pin the candidate and selected suite. Support-manifest and retained-projection objects intentionally remain extensible outside the members this runner consumes.

The eight flat [fixtures](../examples/reference-cli/flat-evidence/) were produced through the historical checked projection-to-protocol bridge before the independent implementation started and remain current V2 inputs. Their case-specific distinction between what the external observation supports and what the exact Lean response supplies remains normative; [`EVIDENCE.md`](EVIDENCE.md) and the [flat kit](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) own that classification. The correlation kit owns its different projection-association boundary. Historical machinery and results are [archived](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md); these integrity levels must not be blurred.

The selected committed-manifest operation must be unique and its `externalEvidenceBoundary` must agree with the suite's identity, finite claim scope, and case composition. The runner's in-memory integrity self-test validates the canonical metadata and evidence links, then mutates compatibility, manifest, count, evidence, duplicate-member, and closed-object boundaries and requires rejection. Run the current flat suite explicitly:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/flat-validation-empty-logic-v2.conformance.json
```

Run the suite against the reference as a control:

```sh
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/flat-validation-empty-logic-v2.conformance.json
```

Replace `--candidate` with a Rust, Kotlin, or TypeScript executable to test that implementation without requiring it to implement the other operation, `--manifest`, or Lean's compact key order. Because the runner does not query a candidate manifest, pin the candidate bytes and claimed suite identity separately in any qualification record. A suite establishes only its indexed observable cases and does not transfer Lean's theorems to the candidate; use the current [flat kit's law and non-law index](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#law-and-non-law-index) or [correlation kit's law index](IMPLEMENTER-KIT-CORRELATION.md#law-index-for-property-tests) as applicable. The current flat v2 suite is still a development slice, not full flat release closure. Each candidate invocation has a 10-second deadline, 1-second cleanup deadline, 1 MiB stdin and stdout caps, and a 64 KiB stderr cap. The relay streams both output channels and terminates the owned process group on timeout or overflow. This is cooperative macOS/Linux resource control for same-credential candidates, not a security sandbox, and the suite currently has no aggregate elapsed or byte budget.

### Historical Rust qualification experiment

The completed Rust experiment is immutable history rather than a live harness. The [archived record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md) owns its exact source and candidate revisions, packet and result hashes, seven-mutation outcome, 52/52 generated-differential result, verdict distribution, limits, and recovery route. Those outcomes establish finite knowledge transport and mutation sensitivity only. They add no kernel evidence, transfer no Lean proof, approve no release, and say nothing beyond the pinned historical profile and mutations.

## Universal proofs and counterexamples

Proof modules quantify over arbitrary inputs and use induction, case analysis, rewriting, or previously proved laws to construct proof terms. Lean's kernel checks those terms. The theorem statement—especially its hypotheses, direction, and result domain—is the claim; theorem counts and proof-line counts are not quality measures.

For effectful proof failures, first preserve the exact elaborated goal and classify every visible `Except` or enum layer. Trial definitional `rfl`, a named domain equation plus `rw`, a reviewed local `simp only` set, and explicit cases without changing the claim. Use `rfl` only for intentionally transparent constructor equations; prefer `simp only` after exposing one effect layer; retain explicit cases when they communicate the residual error domain. A helper belongs in a proof-only owner only when it states a reusable domain boundary, not merely because a tactic needs a different shape. Validate an adopted pattern on a second theorem family before documenting it as reusable. Do not add a global `[simp]` rule unless its normal form is canonical and terminating on nested representatives, preserves every success/error branch, needs no reverse rewrite, and leaves unrelated proofs unchanged.

When an executable enumerator has meaningful independent content, follow the audited Cedar pattern: define an ordered declarative relation separately, prove execution-to-relation soundness and relation-to-execution completeness, and package them as an exact bridge. Preserve ordered-list equality when order or multiplicity can become observable; a membership equivalence is too weak for an ordered A12 document.

Read-footprint theorems should be stated at the semantic observation boundary. The correlated `evalGuardedAnyFilledOn_filter_before_consumer` theorem assumes equal selection, equal validation observation of the outer guard, and equal validation observations of consumer cells in selected rows; it deliberately does not require equality of raw checked cells or any dropped consumer. This makes the proved noninterference exactly as strong as the evaluator's read surface and no stronger.

The checked-elaboration theorems in [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean) establish structural obligations: checked wrappers expose stored model/core certificates, admitted references have a unique matching declaration, the raw-to-checked route uses that declaration's policy, other IDs fail closed, and one-group well-formedness implies the operator-specific scale law. These are not source-to-core semantic-preservation theorems. Such a claim would require an independent dynamic semantics for the surface language, which this capsule deliberately does not yet define.

Each useful law should be paired with the nearest plausible false generalization as a concrete checked non-law. For example, a same-group star reopens the group and spans all candidate rows; the proposition that it collapses to the current row must have an explicit counterexample before `$` correlation is introduced.

Every manually authored exported theorem under `A12Kernel/Proofs/` must be imported by [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean) and remain in the human-readable `#print axioms` registry in [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean); duplicate basenames are rejected before that presentation check. The authoritative gate does not depend on those source spellings. [`../A12Kernel/Trust/Environment.lean`](../A12Kernel/Trust/Environment.lean) inspects every elaborated constant owned by the imported trusted project modules and rejects project axioms whether used or unused, `unsafe`, unclassified opaque declarations, source-partial wrappers, nonstandard axiom dependencies, `implemented_by` substitutions, and `extern` entry points. Lean's generated `_unsafe_rec` helper is admitted only when its parent is a kernel-visible safe total definition with the same type. Conformance is intentionally outside this environment root because its executable examples may use `native_decide`.

The shell gate retains source scanning as defense in depth, but environment inspection is the authority because modifiers, multiline or late attributes, and command macros can make spelling-based checks incomplete. Its adversarial probes elaborate attributed and macro-generated axioms, unsafe and partial definitions, late compiler/foreign attributes, `sorry`, `native_decide`, and a bodyless opaque; an accepted control contains the same words in an ordinary String and uses an ordinary attribute plus the reviewed logical axioms. The script separately computes the transitive project-source closure of the library, proof, and conformance roots and rejects current evidence, reference, process, trust, and IO-driver sources from the logical closure. Exact representative-path self-tests require known logical and process paths to retain their assigned zones and require an unknown future path to remain unclassified.

## Kernel evidence and differential replay

Kernel differential testing is the empirical backbone, but the kernel never becomes a dependency of this repository. Existing focused scenarios run externally through maintained a12-dmkits corpus or differential facilities in the local `../a12-rulekit/` checkout; a new scenario uses that route only when it exposes the required own-domain observation, otherwise it needs an accepted purpose-specific handback. The Groovy-dynamic kernel result is the observation anchor, the static-Java kernel strategy detects a strategy split, and the a12-dmkits interpreter is a clean-room triangulation peer that may reveal a disagreement but is never the oracle.

Only three compact [`ObservationBundle`](../A12Kernel/Evidence/ObservationBundle.lean) files remain under [`evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/): validation core, root String computation, and direct String cascade. The shared reader's tests lock portable-path, bounded-file, duplicate-identity, and regular non-symlink contracts. Each typed projection hashes the exact bundle before decoding, pins its closed family and case shape plus historical provenance references, and compares the retained typed observation with the live semantics.

`lake test` owns 51 non-public replays: 24 validation cases through [`ValidationProjection.lean`](../A12Kernel/Evidence/ValidationProjection.lean), 22 root-String cases through [`StringComputationProjection.lean`](../A12Kernel/Evidence/StringComputationProjection.lean), and five direct-cascade cases through [`StringCascadeProjection.lean`](../A12Kernel/Evidence/StringCascadeProjection.lean). `checkReferenceProcess` owns the other 25 validation/correlation associations through the candidate-conformance control: it requires the exact normalized request tied to each SHA-pinned public evidence case and compares the expected response only at the external observation's supported fidelity. The validation bundle has 49 records but 48 distinct external observations because its directional Number witness intentionally appears in both the public and private partitions.

The 24 private validation cases cover path and absolute-required behavior, the six-case String/`Length` and directional Number matrix, and seven uncorrelated iteration cases. Both kernel routes agreed for the runtime cases; static path rejections are kernel-confirmed authoring observations rather than runtime route comparisons. The historical a12-dmkits interpreter disagreed on the malformed local iteration-filter witness; that fact remains explicit triangulation rather than being flattened into agreement. Operator replay retains focused code, pointer, and VALUE/OMISSION polarity, while externally silent validation retains only suppression and therefore does not pretend to distinguish hidden `NotFired` from `Unknown`.

Public runtime correlation retains exact firing-row membership, not kernel emission order or every richer output channel. Public static observations retain paired kernel diagnostic code and Lean rejection class for three rejected forms. The accepted unequal-scale ordering case establishes static acceptance only; its public empty runtime answer is a Lean-account projection, not an externally observed firing result. Unlisted elaboration errors fail closed rather than receiving guessed kernel codes.

The root-String bundle preserves 13 clean final-delta observations and nine target-checked outcome/delta/exact-application observations. The direct-cascade bundle preserves five producer-certified value-only application observations. Their typed projection tests lock the important distinctions and focused mutation seams, but synthetic mutation fixtures are tests of the consumer contract rather than external evidence.

Ordinary replay does not reopen archived models, placements, runner tables, packets, qualifications, receipts, or historical binder source. The one-time legacy/compact comparisons and exact recovery identities live in the [validation](archived/VALIDATION-RAW-EVIDENCE.md), [root-String](archived/STRING-COMPUTATION-RAW-EVIDENCE.md), and [direct-cascade](archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md) archives. Restoring those deleted stacks merely for routine replay would recreate the maintenance burden that compact projection removed.

Observable boundaries must stay explicit. A retained authored message can establish firing and VALUE/OMISSION polarity; silence generally establishes only suppression. A static checker acceptance does not establish runtime evaluation. A value/delta observation does not expose Lean's hidden expression, poison, dependency, or scheduling representation. [`EVIDENCE.md`](EVIDENCE.md) owns the exact current inventory, family-specific provenance, claim limits, and triangulation facts.

For a future family, first use an existing source-maintained a12-dmkits corpus or differential route when it can retain the required own-domain observation without changing its meaning. If no current route exposes the required channel, record a specific upstream request and leave the capsule `external evidence pending`; use a temporary proposal only for a coherent capability with its own architecture and acceptance lifecycle. Never patch `RuntimeLaws`, add a temporary capture test, resurrect capture V1, or modify a cloned, archived, or copied a12-dmkits source tree. Exclude kernel binaries, linked types or code, volatile logs, and machine-specific state, and preserve the sibling's tracked and visible-untracked status exactly. The accepted [`compact pipeline plan`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) owns future engagement and scaling limits.

## Tier gates

Run this Tier 1 gate for an internal semantic capsule:

```sh
lake build
lake test
./scripts/check-lean-trust.sh
git diff --check
git status --short -- spec/ docs/A12-DMKITS-SPEC-SYNC-LEDGER.md
git status --short
```

If the scoped status lists a behavioral `spec/` change, classify its synchronization direction before committing. A locally originated delta that still needs a12-dmkits reconciliation must also list the synchronization ledger. An inbound correction already committed and reviewed in a12-dmkits must instead list [`SOURCES.md`](SOURCES.md) with the exact source revision and evidence routes and must not create an outbound ledger entry merely to echo the finding back to its origin. If an inbound result answers an existing pending or handed-off entry, update that same entry. Pure spelling, formatting, link, or navigation-only spec changes are exempt. A ledger-only status receipt may legitimately list only the ledger. Add only the focused replay or producer-bundle check owned by a Tier 2 calibration family. `lake test` already replays every retained non-public compact observation, while `checkReferenceProcess` owns the 25 public evidence associations and current shipment process integrity; do not invent another family-independent gate.

Run the complete Tier 3 gate only when the change affects a public process, independent-consumer shipment, qualification mechanism, packaging, or release—or before an actual release:

```sh
lake build
lake test
lake exe checkReferenceProcess
lake exe checkBoundedProcess
lake exe checkCandidateConformance --self-test --suite reference/single-group-correlation-v2.conformance.json
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v2.conformance.json
./scripts/check-lean-trust.sh
git diff --check
git status --short -- spec/ docs/A12-DMKITS-SPEC-SYNC-LEDGER.md
git status --short
git -C ../a12-kernel status --short
git -C ../a12-rulekit status --short
```

Do not run a Tier 3 gate merely because it was needed by a historical experiment. Interpret failures by layer. A conformance failure means a concrete Lean behavior changed. A proof failure means the definition no longer supports the stated universal law or the proof needs legitimate repair. An evidence mismatch means the Lean projection and retained kernel observation disagree and must be investigated at the semantic definition or projection boundary; never relax the expected result merely to make it green. A reference-process failure means the public transport, executable wiring, fixture, current manifest, or current-suite control changed and must be reconciled with [`PROTOCOL.md`](PROTOCOL.md). A candidate-suite failure means the suite/evidence linkage, resource boundary, or candidate observable changed and must be classified using [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md); agreement with the reference is not allowed to overwrite external evidence. A bounded-process failure means the relay lifecycle, byte/deadline limit, status separation, or process-group cleanup invariant changed. A trust failure means the theorem closure or audit is incomplete even if ordinary compilation passed. Sibling status must be unchanged from the recorded pre-run baseline and should be clean; if a sibling was already visibly dirty, report that pre-existing state rather than touching or concealing it.

## Capsule test checklist

- The red run failed for the intended missing or incorrect behavior.
- Concrete cases separate ordinary, boundary, empty, malformed, selection, and ordering behavior as applicable.
- Unsupported syntax or semantic axes fail closed or are unrepresentable.
- The useful theorem states the smallest defensible law with exact hypotheses.
- The nearest stronger false claim has a checked counterexample.
- Every exported theorem is in the trusted root and axiom audit.
- Focused portable kernel observations exist, or the implementation map says `external evidence pending`.
- The replay derives expectations from retained external output rather than duplicating them in Lean-shaped data.
- Current 0.3.0/V2 shipment controls remain green. Historical 0.2.0/Rust identities and hashes remain immutable in the archive rather than current `checkReferenceProcess`; a successor campaign receives a new identity and uses only a newly justified, adopted Tier 3 qualification path.
- The applicable tier gate passes. A Tier 1 semantic capsule does not inherit unrelated historical shipment and qualification gates.
