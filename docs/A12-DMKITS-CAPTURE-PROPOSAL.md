# Proposal: source-maintained portable evidence capture in a12-dmkits

## Status and handoff timing

This proposal was adopted by a12-dmkits. The initial implementation handback at `c0c29b76` was rejected by a12-kernel-lean's pre-acceptance audit; no external packet or accepted V1 identity had escaped. a12-dmkits repaired V1 in place and returned clean revision `3ebe756422e8f2dea447fbd62f9b26c2f774b7e5`. a12-kernel-lean then ran the exact finalized external scenario through real `capture` and `captureVerify` successfully. That disposable packet was deleted and supplies no retained semantic evidence, but it ended the pre-acceptance period: the repaired V1 transport identities and capabilities bytes are frozen.

The repaired implementation enforces the five invariants that the first handback missed: the request selects and binds the qualification policy, qualifying runners, channels, and projections; every packet relationship and closed member set is checked centrally; every runner records the placement stream it actually consumes; the canonical capabilities declaration travels inside and is bound to the packet; and source/tree, kernel/Groovy artifact closure, and JVM runtime identity—also binding the in-memory Java compiler—are checked before and after staged execution. The 40-mutation receipt at `e7242b09` qualifies those process guards but supplies no kernel-semantic observation. [`A12-DMKITS-FEEDBACK.md`](A12-DMKITS-FEEDBACK.md#capture-boundary-audit-disposition) owns the exact audit disposition.

The generic boundary implementation and mutation work are complete. The retained first-client handback remains active: supply the exact Lean-owned [`string-direct-cascade-v1` question](../evidence/scenarios/string-direct-cascade-v1/README.md), obtain the clean qualified packet and sidecars, and verify and retain them independently here. The original proposal body below remains design history; live upstream command and schema truth belongs to a12-dmkits' [`CONFORMANCE-CORPUS-SPEC.md` §15](../../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md) and [`corpus/README.md`](../../a12-rulekit/corpus/README.md).

The repaired machine contract uses request `capture-scenario-set-v1`, envelope `evidence-packet-v1`, payload `compute-observation-v1` with `non-repeatable-compute-targets-v1`, receipt `capture-receipt-v1`, legality `capture-legality-v1`, qualification profile/report `qualification-profile-v1`/`qualification-report-v1`, packet/report diff `packet-diff-report-v1`/`report-diff-report-v1`, world `local-wallclock-v1`, and capabilities `a12-dmkits-capture-capabilities-v1`. Its canonical capabilities bytes at the reconciled revision have SHA-256 `b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca`. The request-declared `kernel-route-confirmed-v1` policy qualifies only `kernel-groovy-dynamic` and `kernel-java-static` under `compute-projection-kernel-route-v1`; the requested `a12-dmkits-interpreter` remains non-qualifying triangulation and may retain its declared fidelity gaps. Every Gradle `-Pcapture.*` path resolves relative to the upstream `adapter/` project, so cross-repository invocations must pass absolute paths.

## Decision requested

Add a source-maintained developer command to a12-dmkits that executes explicitly supplied semantic scenarios through the registered runners and emits a deterministic, language-neutral evidence packet to a caller-selected directory. a12-dmkits owns the command, runner adapters, portable schema, verifier, and qualification/promotion policies. a12-kernel-lean supplies scenario questions, consumes only official portable packets, independently verifies and projects their observations, and never patches a copied a12-dmkits source tree.

The command belongs to kernel-linked adapter developer tooling, not to dmtool-release and not to the clean-room interpreter's published runtime dependency surface. The portable packet—not a kernel-linked Java or Kotlin API—is the cross-project interface.

## Why this is the leverage point

Today each new semantic capsule can require a temporary capture test, temporary extensions to a helper such as `RuntimeLaws.java`, a new receipt format, and another custom Lean binder. That proves a case but does not preserve the capability that produced it. It also makes later recapture, kernel-version comparison, finer projections, and independent review unnecessarily expensive.

A maintained capture boundary turns recurring integration work into data:

1. The consumer authors a closed scenario set containing models, documents, requested operations, and observation probes—but no expected behavior.
2. a12-dmkits validates and executes it using maintained runner adapters.
3. The tool writes one deterministic packet containing each runner's portable observations.
4. Named verification policies classify the same packet without rewriting it.
5. a12-kernel-lean verifies the packet, adds only its fragment-specific projection, and implements or corrects the Lean account.

The important future-proofing choice is to separate observation from judgment. Capture records what every runner exposed. A verifier later decides whether a named projection satisfies a named policy. Interpreter disagreement therefore remains useful characterization instead of blocking kernel evidence, while a12-dmkits conformance under an exact named projection remains strict.

## Ownership boundary

| Concern | Owner |
|---|---|
| Scenario-set, packet, projection, policy, and capability schemas; capture command; runner adapters; portable observations; packet verifier; and generic self-test fixtures | a12-dmkits |
| Real behavioral observations | The two kernel routes, with their exact roles and shared kernel artifact recorded |
| Clean-room triangulation | a12-dmkits interpreter, never the oracle |
| Capsule-specific scenario-pack bytes, observation-requirement instance, and Lean projection | a12-kernel-lean |
| Semantic interpretation, laws, counterexamples, and supported-fragment claim | a12-kernel-lean |
| Decision to accept or reject an upstream change | Repository owner, recorded in the owning repository |

Owning both repositories makes this integration practical, but it does not merge their worktrees or authorities. This project sends a reviewed request; a12-dmkits implements and commits it in its own repository; this project consumes the returned revision and packet.

## Proposed architecture

### 1. Closed scenario-set input

Define a versioned `capture-scenario-set-v1` input. It should contain a stable scenario-set ID and version, one explicit operation schema ID, complete model and input-document references with SHA-256 digests, case IDs, requested operation, explicit probe pointers, a versioned execution-context/world profile or reference, selected required registered runner IDs, a required qualification-policy ID, and an observation-requirement profile that predeclares required channels, fields, and comparison projection IDs. References must resolve within the supplied scenario root, reject traversal, and be copied byte-for-byte into the output packet.

The request asks questions; it never contains expected runner results. An observation-requirement profile selects information and equality projections before execution but contains no expected value. Expected outcomes belong only in a separately reviewed conformance artifact produced after observation. This prevents a case-specific helper from accidentally manufacturing its own oracle or selecting a weaker comparison after seeing a split.

a12-dmkits owns and versions the schema and generic exporter fixtures. a12-kernel-lean owns each capsule-specific scenario-pack instance, supplies its exact bytes to the command, and retains the copied request inside the returned packet. The upstream repository must not commit a second authoritative copy of `string-direct-cascade-v1`; importing a reviewed observation into its conformance corpus is a later explicit promotion. Reusing a scenario ID with different bytes is forbidden—change the version or identity.

V1 should accept explicit cases, not invent a general semantic scenario DSL. Later tooling may expand a declarative matrix of ordinary data axes into explicit cases, but the expanded scenario set must remain inspectable and must still contain no expected semantics.

### 2. Common packet envelope with tagged operation payloads

Define a small stable `evidence-packet-v1` envelope and a separate closed payload schema for each natural kernel-facing operation. Start with `compute-observation-v1`; later validation and static-authoring observations receive new tagged payload schemas. Do not make this adapter boundary a universal importer or consumer framework, and do not create one sparse schema whose optional members attempt to cover every future operation.

The envelope should bind:

- envelope and operation-payload schema IDs;
- kernel behavior version;
- clean a12-dmkits source revision, capture-tool version, and capture build artifact or declared implementation-closure digest;
- scenario-set identity and exact copied-input inventory;
- runner IDs, roles, and fidelity descriptors;
- operation and case inventory;
- references to the exact request, copied-input, legality, and per-runner observation artifacts;
- the deterministic command arguments that affect semantic output;
- each case's request, legality, execution, and runner-availability status.

Generated provenance, command, runtime, diagnostic, packet, and qualification metadata must not contain absolute local paths, usernames, hostnames, credentials, kernel class names, serialized kernel objects, stack traces, or kernel implementation source details or excerpts. Consumer-authored A12 DSL/model/document bytes are copied exactly and may legitimately contain arbitrary String values resembling paths or hostnames; scenario review governs those inputs, and a metadata leak guard must not rewrite or globally scan their semantic contents. Built-in Java hashing is sufficient; this proposal does not request a new dependency. Request, envelope, operation-payload, comparison-projection, qualification-policy, and capability-schema versions are independent parts of the compatibility identity. A published ID is immutable; because the schemas are closed, an added or reinterpreted field requires a new schema or projection version rather than a silent additive change. Requests must pin explicit IDs and never mean “latest,” and old packets must remain verifiable after new versions are added.

Use a separate `RECEIPT.json` for the exact sorted artifact inventory. It inventories every packet file including `PACKET.json`, excludes itself to avoid a self-hash cycle, and records relative path, artifact role, byte count, and SHA-256. The command prints the SHA-256 of `RECEIPT.json` for out-of-band handoff. That digest supplies integrity relative to the separately trusted handoff value; it does not authenticate historical execution by itself. Two clean executions at the same source, runner, kernel artifact, model, input, runtime, and world versions must produce byte-identical packet contents. Omit capture timestamps and other volatile host metadata from the packet identity.

### 3. Adapter-internal runners and kernel-free portable DTOs

Provide reusable internal runners for:

- `kernel-groovy-dynamic`, the behavioral anchor;
- `kernel-java-static`, cross-route confirmation through the same kernel artifact;
- `a12-dmkits-interpreter`, clean-room triangulation.

Kernel types must terminate inside the two kernel-route mappers. The neutral observation model must import no kernel package and must use closed enums or sealed variants with exhaustive `when` handling. A static import/dependency guard should enforce this boundary. A scenario may select required registered runner IDs, but runner identity, implementation, role, and fidelity are defined only by the compile-time registry and echoed from the resolved runner. A focused guard and route-specific mutation checks must establish that the two names invoke distinct registered adapter/code-generation routes, but the claim remains cross-route agreement within one kernel implementation—not agreement between independent engines.

Each runner execution has an explicit status such as `success`, `unsupported`, `timeout`, or `technicalFailure`; successful empty semantic output is data inside `success`, never the encoding of a failed run. Qualification policies fail closed when a required runner or channel is unavailable.

Every case and runner starts with a fresh engine/evaluation context, exact fresh input document, fresh application copy, and explicit injected world, locale, timezone, and clock where those can affect semantics. No cache or global state may leak between cases or routes unless a separately versioned scenario explicitly models a stateful sequence. Re-running the full set in a different case order and comparing it with filtered single-case runs must preserve each case's packet observation while keeping genuinely observable result ordering intact.

Prefer a dedicated internal capture application/source set inside the adapter boundary, with no published component and no dependency from dmtool-release or the clean-room interpreter. If current Gradle structure makes that disproportionate, a maintained internal adapter command is acceptable; a test class named by callers is not the stable contract. Do not widen a published `KernelAdapter` API solely for evidence capture. If the source set or module changes dependencies, packaging, or licensing, stop and consult the owner before making that change.

Use a closed compile-time registry for operation payloads and runners rather than runtime plugin discovery. Adding an ordinary scenario must require data only; adding a genuinely new operation deliberately adds one typed request/observation mapper and its projections. A small kernel-free shared value vocabulary may cover exact decimals, dates, strings, pointers, diagnostics, and cell states, while operation results remain separately typed.

Bind the resolved kernel artifact coordinate and SHA-256 of the resolved artifact bytes, route entrypoint/implementation identity, capture implementation closure, interpreter closure, and semantics-affecting JVM/compiler/runtime identity. A dependency-verification or closure record may carry the artifact identity only when it transitively includes that exact resolved artifact checksum. The final qualified packet must be recaptured after all implementation commits from that clean committed HEAD, must record the same identity after execution, and must be rejected if the checkout or resolved closure changes during the run.

### 4. Exact public computation observations before derived outcomes

`compute-observation-v1` must first preserve the public computation-result collections as separate multiplicity-preserving channels, including their observed enumeration sequence, rather than pretending to expose the kernel's internal cache or overlay:

1. every entry from `getComputedFieldInstancesWithoutErrors`, including a value equal to the prior document value;
2. the independently exposed changed subset or membership from `getComputedFieldInstancesWithChanges`;
3. every entry from `getComputedFieldInstancesWithErrors`, including target pointer, attempted value, structured cause/code, and error pointer where exposed;
4. every pointer from `getClearedFieldInstances`;
5. every entry from `getFormalErrorsInOperands`;
6. the exact post-application state after applying the public result to a fresh copy through the supported `DocumentV2` route, with `absent`, `present-empty`, and `present-value(kind, value)` kept distinct.

Every result item identifies the authored computation declaration and full target cell-instance address and preserves the observed enumeration sequence and multiplicity. Per-channel fidelity states whether order is contractually meaningful, merely observed, or not applicable. Equality projections compare order only where the public contract makes it semantic; otherwise they compare an explicitly declared canonical multiset while the raw observation still retains the sequence. The portable value carries typed `valueV2` and rendered/string form as separate explicitly available fields so later normalization or rendering research does not require recapture. The initial V1 capability rejects repeatable computation targets and scopes even though the address type is future-capable; repeat support requires a new declared input-support version and separating evidence. One packet contains exactly one operation payload schema.

The request names the complete application probe scope and automatically includes every computation target. A packet therefore cannot imply whole-document correspondence from a few inspected cells; an optional canonical subtree or document digest may reveal unanticipated changes outside those probes.

A separately versioned projector may derive portable target classifications from the public collections. It can derive accepted-changed versus accepted-equal from all-clean and changed-subset membership, retain target errors and coarse cleared membership, and emit `silentOrIndeterminate` when no public collection determines a target result. It must preserve conflicts and field provenance. It must not label silence as clean no-value, infer a clear cause, manufacture dependency poison, or reconstruct a structured cause from text or applied state.

The public `CLEARED` collection is intentionally coarse: it can cover no-value, inapplicable precondition, cascading error, or formal operand error. The Lean overlay/no-value/poison model is a source-informed explanatory account tested by separating external observations, not a directly captured kernel field. In particular, a downstream `CLEARED` result plus final empty state can show that neither attempted nor stale data was stored, but it does not by itself reveal an internal poison tag or dependent-read value.

Every field whose fidelity differs by runner needs an explicit availability value such as `available`, `notExposedByRunner`, or `notApplicable`. Missing interpreter cause transport must never be rendered as “no cause,” inferred from kernel output, or counted as rich-result agreement. A required unavailable field fails the named qualification; a deliberately excluded field is listed with rationale, and the claim is conformance only under that exact projection.

The existing compact corpus signature may remain byte-for-byte compatible, but its documentation must identify it as a deliberately lossy projection. The new rich route should reuse the interpreter's actual structured result before that compact projection erases information.

### 5. Capture once, qualify separately

The capture command should always preserve completed runner observations, including divergences. A separate verifier applies named policies and emits a report that digest-binds the immutable packet receipt:

- `characterization-v1` requires schema, inventory, legality classification, and truthful runner availability; it may retain a runner failure or disagreement and can never promote a corpus case.
- `kernel-route-confirmed-v1` requires a kernel-legal scenario, both kernel routes, and equality under every field of the immutable projection profile pinned before capture; interpreter agreement is reported but not required. This is the policy needed by a12-kernel-lean and claims only exact cross-route agreement on that projection.
- `dmkits-projected-conformance-v1` additionally requires the a12-dmkits interpreter to make every field required by its pinned portable projection available and equal. An unavailable required field fails; deliberately excluded fields are named with rationale, so the result is never called full rich-result conformance.

Every portable qualification policy rejects a development-mode or otherwise dirty-source packet before semantic comparison. A clean `characterization-v1` packet may retain runner failure or disagreement; dirty packets are temporary engineering output, not retained characterization evidence.

The observation-requirement and comparison-profile bytes are pinned in the request before execution. Qualification may produce additional weaker diagnostic comparisons, but they cannot qualify the scenario for its declared purpose or conceal an unavailable required channel. Qualification reports and structured comparison diffs are separate derived artifacts; verification must never add files to or rewrite the observation packet. Give each report its own closed schema and receipt or digest, and bind the exact upstream `RECEIPT.json` SHA-256, policy/profile definition digests, projection versions, verifier implementation closure, and comparison results.

Corpus promotion remains a separate hard boundary but is not a mandatory generic V1 command. When a concrete a12-dmkits corpus client justifies it, a corpus-specific promotion command must reverify the packet and qualifying report, use an explicitly versioned rich-to-corpus projection, require separate human authorization, and emit the updated corpus receipt. Capturing or verifying must never rewrite committed corpus files.

Do not use one global `agrees` Boolean. Each comparison names the two runners, projection ID and version, included fields, unavailable fields, and equal/divergent status. This prevents agreement at delta granularity from being mistaken for agreement on attempted values, causes, or application shape.

### 6. Legality before runtime

For runtime computation and validation payloads, run the kernel's authoring/consistency acceptance surface before executing a scenario. Record the validator runner, profile/configuration/version, complete structured legality result, and exact supplied and adapted model/operation digests. An illegal model may produce a characterization artifact describing the rejection, but it must not be executed as runtime evidence and cannot satisfy either confirmed or conformance policy. Every runtime route must echo the exact supplied and adapted digests it consumed; if adaptation creates a canonical intermediate form, bind both forms so normalization cannot make the gate inspect one program while runtime executes another. A future static-authoring-diagnostic payload is itself the legality observation and may deliberately ask about rejected drafts; it must not route those drafts onward to runtime.

This gate is part of the evidence claim, not merely an implementation precondition. A runtime generator accepting some bytes does not establish that the authored rule or computation is legal.

### 7. Deterministic layout and commands

A packet should be directory-shaped and reviewable rather than one growing monolith. One suitable logical layout is:

```text
packet/
  PACKET.json
  RECEIPT.json
  request/scenarios.json
  inputs/models/...
  inputs/documents/...
  observations/<case>/<runner>.json
qualification/
  <policy>/PROFILE.json
  <policy>/REPORT.json
  <policy>/RECEIPT.json
```

Exact names may follow a12-dmkits conventions, but the invariants matter: UTF-8, LF, final-newline, object-key, exact-number, and array-order rules are pinned; one case and runner can be diffed without rewriting unrelated observations; the receipt inventory is closed; ordered semantic lists preserve order; unordered maps and sets serialize canonically; decimal and typed values never travel through binary floating point; and a verifier rejects additions, removals, renames, symlinks, byte drift, unknown members, unsafe references, and source/schema/runner mismatches. Locale, timezone, injected clock, Unicode/newline treatment, and other context that can change semantics must be explicit request or allowlisted runtime identity rather than ambient machine state.

Provide maintained commands equivalent to:

```text
capabilities
validate-scenarios --scenarios <file>
capture [--development] --scenarios <file> --output <new-packet-directory>
verify --packet <directory> --packet-receipt-sha256 <digest> --policy <policy-id> --output <new-report-directory>
diff-packets --before <packet> --after <packet> --projection <projection-id> --output <new-report-directory>
diff-reports --before <report> --after <report> --output <new-report-directory>
```

The exact Gradle syntax belongs to a12-dmkits. The mandatory V1 surface is versioned capability discovery, non-executing scenario validation through the same closed decoder used by capture, capture, verification, and deterministic structural packet/report diff; corpus promotion is deliberately deferred until its first reviewed client. `validate-scenarios` checks schema identity, closed members, references, digests, traversal safety, requested capabilities, runners, channels, context profile, and qualification policy without running a semantic engine or writing evidence. By default, `capture` repeats that validation and requires a clean committed source checkout. An explicit `--development` mode may run against modified source so red/green and mutation tests can exercise the real command without copying the repository; its packet records the dirty state and exact capture-source closure digest and is permanently ineligible for every portable qualification policy. Both modes require an explicit new or empty caller-owned output directory, refuse the committed corpus tree, keep temporary compiler/runtime products in already ignored storage, and leave source bytes and visible status exactly as they found them. `verify` and both diff operations likewise write only to distinct new report directories. Packet diff distinguishes input/provenance and each runner's observation drift; report diff distinguishes policy/profile/verifier and qualification-result drift.

### 8. Capability discovery

Add a closed, independently versioned machine-readable `capabilities` output listing supported request/envelope/operation schemas, exact input-scope versions, runner IDs, observation channels and field fidelity, projection IDs, policy IDs, limits, and verifier/diff support. The scenario pins the required capability identity and capture rejects unknown versions, repeatable input under the non-repeatable V1 profile, or unavailable required fields before any runner executes. A mutation that changes a schema or projection without changing its ID must fail a compatibility fixture.

Capabilities describe transport, not A12 semantic support. For example, supporting `compute-observation-v1` means the tool can capture its closed fields; it does not claim that the interpreter implements every computation operator.

## Initial acceptance scenario: direct String cascade

The first end-to-end client should be the existing finite `string-direct-cascade-v1` question. It proves that the capture surface handles multiple computation targets and the distinctions that motivated the design; it does not prove a general scheduler.

Use one legal non-repeatable model with the upstream computation authored before the dependent computation:

- `Mid := [Source]`;
- `Mid.maxLength = 3`;
- `Out := [Mid] + "-X"`.

Seed `Out = "STALE"` in every case and capture exactly:

| Case | Input and prior Mid | Public observation to verify across the two kernel routes |
|---|---|---|
| accepted-changed | `Source = "ABC"`, `Mid = "OLD"` | Mid appears in the all-clean and changed collections; Out reports/stores `"ABC-X"` |
| accepted-equal | `Source = "ABC"`, `Mid = "ABC"` | Mid appears in all-clean but not the changed subset; Out still reports/stores `"ABC-X"` |
| no-value-over-stale | Source absent, `Mid = "OLD"` | Mid appears in the coarse cleared collection; Out reports/stores `"-X"`, never `"OLD-X"` |
| no-value-over-absent | Source absent, Mid absent | Mid may be silent/indeterminate in the public collections and remains absent after application; Out nevertheless reports/stores `"-X"` |
| target-error | `Source = "ABCD"`, `Mid = "OLD"` | Mid reports attempted `"ABCD"` plus `stringZuLang`; Out reports `CLEARED`, does not store `"ABCD-X"` or `"OLD-X"`, and the requested applied states preserve present-empty versus absent exactly |

These are hypotheses to verify, not expected values to embed in the capture request. If the two kernel routes disagree, retain both observations as characterization and stop route-confirmed qualification. Keep the interpreter lane separate and classify unavailable cause transport accurately. The source-informed Lean account explains the last case with dependency poison and the two absent-source cases with clean no-value overlay, but those hidden tags are not fields captured from the public kernel result; their adequacy rests on this separating matrix plus the already retained single-target clauses.

The scenario closes only one direct authored dependency edge. It does not establish graph construction, arbitrary scheduling order, transitive chains, false-precondition clearing, unread-poison short-circuiting, alternatives, aggregates, repeats, or general document mutation.

## Required tests and mutation sensitivity

Implementation is complete only when focused tests independently detect:

- an illegal authored model reaching runtime execution;
- omission of either kernel route or a hidden cross-route divergence;
- an accepted-equal computation disappearing from the all-clean collection;
- an accepted-equal computation being incorrectly added to the changed subset;
- a source-absent cascade producing stale `"OLD-X"` instead of the observed `"-X"`;
- an attempted rejected value reaching the dependent computation;
- the errored attempted value being dropped or altered;
- each structured cause field—code, message type, and pointer—being dropped or altered independently;
- `absent` and `present-empty` application states being collapsed;
- use of a deprecated or mutating application route instead of applying the result to a fresh `DocumentV2` copy;
- interpreter disagreement blocking characterization or being mislabeled route confirmation;
- unavailable fidelity being treated as semantic equality;
- a compact legacy signature changing unintentionally;
- packet or qualification-report member, digest, revision, runner, schema, symlink, or relative-path drift;
- an absolute path, username, hostname, environment dump, or other machine-specific value entering generated metadata or a qualification report, without falsely rejecting the copied own-domain input bytes;
- an unknown version or an in-place schema/projection mutation under an existing ID;
- a verifier or diff command mutating the packet it consumes;
- the legality checker and runtime receiving different adapted bytes;
- the two kernel runner labels accidentally selecting the same execution route;
- a runtime failure or unsupported operation being serialized as a successful empty observation;
- standalone scenario validation and capture making different structural acceptance decisions for the same fixture before cleanliness, legality, or runtime checks;
- case or route state leaking across a reordered full run or disagreeing with the corresponding filtered single-case run;
- a final qualified capture occurring before the implementation revision is committed and clean;
- a second identical run producing different semantic packet bytes;
- output entering the committed corpus without explicit promotion;
- a kernel import or type crossing into the neutral DTO boundary.

Each source mutation should run the actual command in explicit development mode, predict its narrow failing guard before execution, restore exact source bytes afterward, and finish with the natural full gate green. Mutant packets are disposable and qualification-ineligible. Retain a new scenario-specific machine-checkable mutation receipt listing mutation ID, request/model/capability identities, implementation revision, expected guard, actual guard, pre/post classified source-tree digest, restoration, and final natural-gate result; never rewrite the generic boundary receipt. A single black-box cause value cannot prove that a mapper did not reconstruct an observationally identical cause, so provenance additionally requires direct source review or a later second-cause discriminator. Recapture twice from the final clean committed source, require identical packet receipts plus a no-drift packet diff, and retain one designated handback packet with the qualification sidecars.

## Future work deliberately prepared, not included in V1

Once `compute-observation-v1` is stable, the same envelope and runner registry can add validation-message, static-authoring-diagnostic, and other operation payloads without changing existing packets. A generic data-axis expander can later produce explicit scenario matrices for kind/operator/emptiness/context combinations, while keeping expected results outside capture input. Incremental recapture keyed by exact input and runner identities may reduce runtime, but clean uncached capture must remain the qualification path so caching cannot hide nondeterminism.

On the Lean side, the stable packet envelope enables one shared strict inventory/hash/provenance verifier instead of redefining receipt structures in every evidence binder. Operation-specific closed decoders and semantic bindings remain separate. A later local `importEvidence` command can validate an official packet and scaffold references and projection stubs, but it must never invent the semantic projection or expected Lean result.

Do not build a universal capture DSL, automatic semantic minimizer, distributed service, corpus database, or plugin framework before at least computation and one second operation demonstrate the need. The V1 extensibility point is the tagged operation payload and runner registry, not speculative infrastructure.

## Handback contract

The a12-dmkits implementation handback should contain:

- the exact upstream revision and clean-worktree status;
- proposal/architecture and user documentation paths;
- capability, scenario-validation, capture, verify, and packet/report diff commands, plus any later corpus-specific promotion command;
- scenario, envelope, computation-payload, projection, and policy schema IDs;
- two byte-identical clean packets produced from the externally supplied `string-direct-cascade-v1` scenario pack, both out-of-band `RECEIPT.json` SHA-256 values, their no-drift packet-diff report, and the complete designated packet;
- each applicable qualification profile, report, receipt, and out-of-band receipt digest;
- a five-case table showing both kernel routes and interpreter observations without collapsing fidelity gaps;
- a new versioned scenario-specific machine-checkable mutation receipt, its out-of-band digest, and human summary, without rewriting the generic boundary receipt;
- dependency, packaging, licensing, and compatibility effects;
- unresolved limitations and the next recommended operation payload.

a12-kernel-lean should first verify the returned bytes and source identity, then retain the complete verified portable packet and receipt, applicable qualification sidecars and their receipt digests, and its own typed projection under the local evidence lifecycle. It excludes kernel binaries, kernel-linked implementation code or objects, volatile logs, and machine-specific state. It must not copy capture implementation code or ask the downstream implementer to research kernel behavior again.

## Prompt templates

Prompt 1 is completed historical context: it produced the first handback and the subsequent pre-acceptance repair through `3ebe7564`. Prompt 2 is now active and must consume the exact committed [`string-direct-cascade-v1`](../evidence/scenarios/string-direct-cascade-v1/README.md) bytes; Prompt 3 remains the independent review after that official capture. Do not rerun Prompt 1 or reinterpret its original wording as live implementation truth.

### Prompt 1 — reconcile and implement the reusable boundary

```text
Continue in the a12-dmkits repository only. The earlier A12-DMKITS-FEEDBACK.md work has completed, so first inspect the current branch, worktree, recent commits, and the recorded dispositions of F4, F5, F7, F8, and F11. Reconcile them with A12-DMKITS-CAPTURE-PROPOSAL.md and build on the landed mechanisms; do not duplicate or revert them.

Implement the smallest source-maintained portable evidence-capture boundary described by that proposal. Use red/green TDD and follow this repository's own instructions. Do not add or change dependencies, modules, publication, kernel linkage, or release boundaries without consulting me first.

Keep observation separate from qualification: one command records closed, deterministic, kernel-free portable public observations from the Groovy-dynamic route, Java-static route, and a12-dmkits interpreter; separate named policies classify characterization, kernel-route confirmation, and a12-dmkits conformance under an exact named projection. Corpus promotion is a later corpus-specific action. Preserve every public clean, changed-subset, errored, cleared, and formal-error collection, exact fresh-copy DocumentV2 application states, and typed versus rendered values as independent channels. Retain accepted-equal values, attempted errored values, structured causes where exposed, and absent versus present-empty. Never reconstruct one channel from another, manufacture internal no-value/poison state, or treat unavailable fidelity as agreement.

Use a closed external scenario-set input with no expected semantic output, a standalone non-executing validator that shares capture's exact structural decoder, a predeclared observation-requirement profile, a common packet envelope, a closed non-repeatable compute-observation-v1 payload, per-runner fidelity descriptors, immutable named comparison projections, deterministic per-case artifacts, immutable packet plus sidecar qualification reports, a digest-bound verifier, explicit caller-owned output, clean qualification behavior plus an explicitly ineligible development mode, and a versioned capability-discovery command. Preserve the legacy compact signature unless an intentional compatibility change is separately approved, and label its limitations.

First return a concise implementation plan mapping the proposal to the current post-feedback architecture and identifying any approval decision. If no such decision is needed, implement it, run the focused and full gates, and commit coherent units with Conventional Commits. Report exact commands, schemas, changed public/internal boundaries, compatibility effects, revisions, and remaining limitations.
```

### Prompt 2 — test-drive the official surface

```text
Continue only in the a12-dmkits repository. The last verified clean handoff revision is `9e97c517eb5df3d87060281a1cdf5136ad8f66c4`, a docs-only descendant of the accepted and frozen capture baseline `3ebe756422e8f2dea447fbd62f9b26c2f774b7e5`. Do not begin while the worktree contains concurrent owner work, and never discard, overwrite, or absorb that work; wait for it to land cleanly. The compatibility boundary is kernel behavior 30.8.1 plus canonical capabilities SHA-256 `b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca`; the capture implementation and those capabilities bytes are unchanged between the two revisions. If clean HEAD has advanced, first prove and report that `3ebe7564` remains an ancestor, the resolved behavior anchor is still kernel 30.8.1, and the capture implementation, schemas, projections, policies, and canonical capabilities bytes are unchanged. Otherwise stop rather than silently reinterpret frozen V1. Any newly discovered contract defect requires a new version and owner decision, never another in-place V1 repair.

First correct the a12-dmkits status documentation that still calls V1 unfrozen. Record that a12-kernel-lean's exact external smoke run at `3ebe7564` successfully completed `capture` and `captureVerify` for request SHA-256 `4c5d4911ecacde819618b3b921b0bd30aa34b514cb0bbf3f0d2b735f21a0fd43` and model SHA-256 `3d21add02d259a8d1ad2e14475582513aec2f4e60176f1c02c81d40de88a895d`, printing packet-receipt SHA-256 `f84e38fa6307cda755dbf660e31044db54d5e1ff0e4332c7d416de096c034463` and qualification-receipt SHA-256 `2a0db1f4f6a16fb576c9dbe21944ac950b522ecc2b056336aae2470ce43cc9df`. The artifacts were deleted, so this freezes transport compatibility but is not retained kernel evidence. Commit that documentation correction without changing V1 contract bytes.

Do not write into a12-kernel-lean. Consume the externally owned `string-direct-cascade-v1` request and model bytes introduced by a12-kernel-lean commit `ee681564446907b363f7f5d435daf8b8a7397205`:

- `../a12-kernel-lean/evidence/scenarios/string-direct-cascade-v1/scenarios.json`, SHA-256 `4c5d4911ecacde819618b3b921b0bd30aa34b514cb0bbf3f0d2b735f21a0fd43`
- `../a12-kernel-lean/evidence/scenarios/string-direct-cascade-v1/models/string-direct-cascade.json`, SHA-256 `3d21add02d259a8d1ad2e14475582513aec2f4e60176f1c02c81d40de88a895d`

Verify those exact bytes and the expected capabilities hash, then run the maintained non-executing scenario validator using absolute `-Pcapture.*` paths. Do not commit or generate a second canonical scenario copy in a12-dmkits, add cascade-specific capture code, add expected results to the request, modify the scenario bytes, or promote anything into the corpus. No explicit clock instant is supplied because this model is time-free; make no time-semantics claim.

Treat every outcome described in this proposal as a hypothesis. The labels map to exact case IDs: accepted-changed → `source-abc-mid-old`; accepted-equal → `source-abc-mid-abc`; no-value-over-stale → `source-absent-mid-old`; no-value-over-absent → `source-absent-mid-absent`; target-error → `source-abcd-mid-old`.

Run the deferred scenario-semantic mutations one at a time through the real maintained development mode only. Each mutant packet is disposable and qualification-ineligible; do not run portable qualification over it. Record each prediction before execution, the actual narrow guard afterward, and exact source restoration. Independent mutations must catch: accepted-equal `Mid` missing from `withoutErrors`; accepted-equal `Mid` incorrectly entering `changedSubset`; absent `Source` allowing stale `OLD-X`; rejected attempted `ABCD` reaching `Out`; attempted value being dropped or altered; cause code `stringZuLang` being dropped or altered; cause message type `VALUE_ERROR` being dropped or altered; cause pointer `/Cascade[1]/Mid` being dropped or altered; and absent versus present-empty applied states being collapsed.

Create a new versioned `string-direct-cascade-v1` scenario-qualification receipt; do not append to or rewrite the generic 40-mutation boundary receipt. Bind the scenario and model hashes, capabilities hash, kernel behavior version, capture-implementation revision under test, exact commands, each mutation's prediction and actual guard, pre/post classified tree digests, restoration result, and final natural gate. Give this receipt its own out-of-band SHA-256. Direct source review may establish that the runner records fields from the consumed public result, and the mutations establish that each field is observable and guarded; the single `stringZuLang` case cannot prove from black-box output alone that an identical cause was not reconstructed, so do not make that stronger provenance claim.

Commit the status correction and new scenario-qualification receipt, finish the natural full gate green, and verify that capture source and frozen V1 contract bytes still match the accepted baseline. From that final clean committed HEAD, perform two complete captures into distinct new caller-owned output directories. Require equal printed packet-receipt SHA-256 values and run `captureDiffPackets` under the predeclared kernel-route projection to obtain an explicit no-drift report before designating either packet as the retained answer. Preserve both packets and the diff output until handback acceptance.

Run `captureVerify` on the designated packet with its receipt digest and request-declared `kernel-route-confirmed-v1` policy into a separate new directory; the CLI policy argument is only an exact confirmation. Preserve every public channel, typed and rendered value, applied-state probe, structured cause and formal-operand diagnostic where exposed, complete target identity, runner fidelity, consumed-placement identity, packet-local capabilities, and pre/post implementation/runtime closure. If the two kernel routes disagree under `compute-projection-kernel-route-v1`, preserve the packet and failed report as characterization and stop; never weaken the request or projection after observing the result. Record the qualification `RECEIPT.json` SHA-256 and confirm the visible worktree is unchanged and clean.

Return: the exact final a12-dmkits revision and its relationship to `3ebe7564`; exact reproduction commands; the new scenario-qualification receipt and out-of-band digest; both clean packet-receipt digests; packet-diff inventory and digest; complete designated packet inventory and receipt digest; complete PROFILE/REPORT/RECEIPT qualification inventory and receipt digest; concise per-mutation guard results; and a five-case table keyed by the exact case IDs. The table must keep interpreter fidelity exclusions explicit: typed values, changed subset, structured causes, formal operand errors, and absent-versus-present-empty are unavailable there, while rendered values remain available. Report the policy result, every divergence, the V1 freeze correction, and unresolved limits. State explicitly that the two kernel routes are distinct routes through one kernel implementation, the interpreter is triangulation rather than oracle, and the packet establishes only this finite direct-cascade question.
```

### Prompt 3 — independent review and handback

```text
Review the completed a12-dmkits portable capture boundary and `string-direct-cascade-v1` independently. Begin read-only and report findings before fixing them.

Verify that capture observes existing runner behavior rather than reimplementing A12 semantics; no kernel type or dependency crosses the neutral DTO boundary or enters dmtool-release; input contains no expected result; standalone validation and capture share one structural decoder and make the same pre-execution decision; required observations and projections are pinned before execution; legality precedes runtime over the same bound bytes; the two registered kernel names invoke distinct routes through the same bound kernel artifact; interpreter output is triangulation; public result collections, derived projection, application state, and diagnostics remain separate; unavailable fidelity is explicit and fails any projection that requires it; qualification comparisons name their exact immutable projection; development packets cannot qualify; characterization cannot promote; legacy compact output remains compatible; deterministic packet and sidecar-report receipts detect all inventory and byte drift; explicit output leaves the worktree unchanged; and the five-case scenario required no new capsule-specific capture source.

Exercise the proposal's independent mutations, predict each narrow failure, restore exact bytes, and finish with the full natural gate. Report findings by severity with exact loci and broken invariants. After reporting, fix only proposal-scoped findings that require no new dependency, publication, linkage, public-API, or release decision; stop for owner direction on any such boundary. If clean after allowed fixes, provide the final revision, packet/report digests, commands, policy results, mutation receipt, remaining semantic limits, and a concise handback addressed to the a12-kernel-lean maintainer.
```

## Acceptance decision

The architecture and repaired pre-acceptance V1 implementation are accepted at a12-dmkits revision `3ebe7564`. The project explicitly accepts the one-time in-place V1 repair because the rejected `c0c29b76` handback produced no accepted external packet or consumer contract; this exception and the changed capabilities digest are part of the reconciliation record. The subsequent successful external smoke capture froze the repaired V1 identities and does not authorize another in-place schema, projection, policy, or capability mutation. Because the smoke packet was deleted, it does not close the cascade's evidence: the complete official packet, sidecars, scenario-semantic mutation record, local strict binding, and Lean replay remain pending.
