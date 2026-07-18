# Repository artifact lifecycle

This guide explains what belongs under [`evidence/`](../evidence/), [`reference/`](../reference/), [`examples/`](../examples/), and the retained [`qualification/`](../qualification/) history, which facts each owns, and how each should evolve. These artifacts deliberately have different lifecycles; treating all of them as either hand-authored source or disposable generated output would break the project's evidence and consumer contracts.

## The short answer

| Directory | Role | Source of truth? | Normal evolution |
|---|---|---|---|
| [`evidence/`](../evidence/) | Retained external observations, complete certified raw audit units, exact probe inputs, and compact producer-certified semantic bundles | Raw units preserve what a pinned kernel run observed and how the producer qualified it; accepted compact bundles are the ordinary Lean replay interface, not a second oracle | Append, version, or explicitly correct raw observations; add compact bundles under versioned producer identities only after their producer contract is accepted; never rewrite an accepted raw unit |
| [`evidence/scenarios/`](../evidence/scenarios/) | Project-authored, expectation-free questions for the maintained external capture boundary | Yes, for the exact scenario request bytes; never a source of observed behavior | Version the question when its input or requested observation contract changes; retain returned answers elsewhere |
| [`reference/`](../reference/) | Portable consumer shipments and the readable support-manifest mirror | Mostly derived from Lean and retained evidence; the correlation suite remains a reviewed manual index | Derive new current identities from their owners, maintain reviewed indices explicitly, and never regenerate a frozen compatibility line in place |
| [`examples/`](../examples/) | Runnable user examples, golden process regressions, and generated shipment fixtures | No; expected outputs are reviewed regression locks, not kernel evidence | Curate the small human-facing set and regenerate owned fixture sets |
| Project-local [`qualification/`](../qualification/) | Compact retained receipt from the completed Rust generated-differential campaign | No; it reports one finite historical run and its explicit claim boundary | Retain immutably; a future real consumer receives a newly designed qualification identity rather than extending the retired one-off runner |
| Historical Git revision `03186c1` | Retired flat bridge, mutation packet/checker, and generated-differential source | No; Git history preserves how the accepted records were produced and checked | Inspect or reproduce at the pinned revision only; do not restore the machinery to current source for possible future reuse |

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

The direct-cascade migration demonstrates how the complete raw audit unit and compact Lean replay bundle coexist without duplicating responsibility. a12-dmkits verifies and certifies the raw packet, runner, input, capability, qualification, closure, receipt, recapture relations, and compact export. This repository retains those bytes but ordinary replay treats the raw unit as opaque: one small generic reader checks the compact bundle contract, and a typed family decoder checks only the pinned semantic input/observation projection. The migration ran the former complete binder and compact lane together once before deleting the packet-specific Lean machinery.

Detailed evidence claims remain in [`EVIDENCE.md`](EVIDENCE.md), process and manifest compatibility in [`PROTOCOL.md`](PROTOCOL.md), executable gates in [`TESTING.md`](TESTING.md), consumer shipment and qualification contracts in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md), and current unfinished work in [`PLAN.md`](PLAN.md). This guide owns only the directory-level classification and lifecycle connecting those contracts.

## `evidence/scenarios/`: questions, not observations

[`evidence/scenarios/`](../evidence/scenarios/) contains versioned scenario roots authored by this project for a source-maintained a12-dmkits capture command. A root contains the complete input model or models intended for the later legality gate, explicit document placements, operation, requested runners, probes, required channels, qualification policy, and projection identities. It contains no expected value, verdict, diagnostic, agreement flag, mutation outcome, or Lean result. Its exact bytes are the canonical request and are copied into any returned packet; a12-dmkits must not commit a second authoritative copy.

The first member is [`string-direct-cascade-v1`](../evidence/scenarios/string-direct-cascade-v1/README.md). The scenario bytes remain only a question, while their separately retained [`Set Z4 answer`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/README.md) supplies the complete qualified packet, sidecars, process receipt, no-drift report, and producer-certified [`semantic-observations.json`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/semantic-observations.json). [`ObservationBundle.lean`](../A12Kernel/Evidence/ObservationBundle.lean) and [`StringCascadeProjection.lean`](../A12Kernel/Evidence/StringCascadeProjection.lean) pin the compact file at exporter revision `1b5f463b89adc6cfb81b41121cd6c97855e8cbe3` and SHA-256 `1d8d253e553eba70fa990975666884833748bed9d9b2b6483f472767a9837c7a`, then perform the typed five-case Lean replay; this compact claim deliberately excludes hidden dependency state, scheduling, and exact-state correspondence even though a separate internal one-address application capsule now exists.

Changing scenario meaning requires a new scenario version or identity; reusing an existing ID with different bytes is forbidden. Structural validation checks only the closed request shape, references, digests, requested capabilities, and static transport constraints; kernel authoring legality is a separate capture-time gate. The official answer is a separate immutable unit: the complete packet and packet receipt, packet-local capabilities declaration, out-of-band packet-receipt digest, separate qualification profile/report/receipt sidecars and their out-of-band receipt digest, and the producer-certified compact bundle consumed by the project-owned typed projection. A scenario-specific mutation receipt and two-clean-capture no-drift report are retained as process-qualification companions, never reclassified as kernel observations. Retain every runner observation and declared fidelity gap, not only rows that agree.

## `evidence/`: retained empirical inputs

### Contents

The versioned [`evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/) bundle currently contains:

- runtime observation records under [`cases/`](../evidence/kernel-30.8.1/cases/);
- static authoring observations under [`diagnostics/`](../evidence/kernel-30.8.1/diagnostics/);
- complete standalone DM-JSON probe inputs under [`models/`](../evidence/kernel-30.8.1/models/);
- digest-pinned capture receipts under [`captures/`](../evidence/kernel-30.8.1/captures/), currently [`operator-sensitive-empty-2026-07-15.json`](../evidence/kernel-30.8.1/captures/operator-sensitive-empty-2026-07-15.json), [`string-computation-2026-07-15.json`](../evidence/kernel-30.8.1/captures/string-computation-2026-07-15.json), and [`string-target-validation-2026-07-15.json`](../evidence/kernel-30.8.1/captures/string-target-validation-2026-07-15.json), plus the complete version-owned [`string-direct-cascade-v1`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/README.md) packet, packet receipt, packet-local capabilities, qualification sidecars, process receipt, recapture diff, and compact semantic-observation bundle;
- an auxiliary interpreter-versus-kernel disagreement record under [`triangulation/`](../evidence/kernel-30.8.1/triangulation/);
- seven reviewed Lean-facing projection files: [`projection.json`](../evidence/kernel-30.8.1/projection.json) for flat/path/required, [`iteration-projection.json`](../evidence/kernel-30.8.1/iteration-projection.json) for uncorrelated iteration, [`correlation-projection.json`](../evidence/kernel-30.8.1/correlation-projection.json) for captured-outer correlation, [`correlation-elaboration-projection.json`](../evidence/kernel-30.8.1/correlation-elaboration-projection.json) for checked correlation elaboration, [`operator-empty-projection.json`](../evidence/kernel-30.8.1/operator-empty-projection.json) for operator-sensitive empty values, [`string-computation-projection.json`](../evidence/kernel-30.8.1/string-computation-projection.json) for the first clean String expression/store/delta capsule, and [`string-target-validation-projection.json`](../evidence/kernel-30.8.1/string-target-validation-projection.json) for positive String target-length checking, payloadful `ERRORED`, and exact accepted/errored application over absent and filled priors.

The case, diagnostic, and model files preserve the input and externally observable result of a focused experiment. A capture receipt binds provenance, file identities, and strategy outputs that do not fit the portable case shape; it remains a retained historical report, not proof that an unavailable temporary harness or validator command ran. The projections are narrower structured translations into the input boundary understood by the current Lean capsules. A projection is therefore a reviewed bridge, not an additional kernel observation and not a replacement for the retained full model and output.

### Responsibility and authority

This tree answers: **what exactly was run against which kernel version, and what was observed?** It supports empirical correspondence claims only over the retained observable projection. It does not prove that the kernel universally agrees with Lean, and it does not make a manually classified hidden Lean verdict externally observed when the kernel output exposed only message presence or silence.

The complete provenance and claim boundary are owned by [`EVIDENCE.md`](EVIDENCE.md). The replay schemas and binders live under [`A12Kernel/Evidence/`](../A12Kernel/Evidence/); they are test infrastructure rather than part of the trusted theorem root.

### Evolution policy

- A pure Lean refactor must not change raw retained observations. A reviewed projection also remains unchanged unless the Lean-facing bridge itself intentionally changes.
- A protocol, fixture-layout, or shipment change must not change raw retained observations.
- A changed Lean semantic account must replay against the same retained observations. A disagreement is investigated; the raw evidence is never refreshed merely to make the test green.
- For direct cascade, the producer-certified bundle names the raw audit identity and ordinary Lean replay binds only the typed family projection to that compact bundle; it does not rebind every raw artifact. Existing focused projection lanes remain unchanged until their own measured migration is justified.
- A newly modeled semantic clause may remain explicitly `external evidence pending`. Before claiming external correspondence or evidence-complete status, add the smallest focused observation and reviewed projection needed to anchor it.
- Historical evidence layouts and disposable-harness receipts remain immutable. Each new capture retains the complete verified portable packet and receipt plus required qualification sidecars and their out-of-band receipt digests as the raw audit unit, and retains the producer-certified compact semantic bundle as the ordinary Lean replay unit. Do not retain only selected agreeing observations in place of the raw unit. Kernel binaries, kernel-linked types or implementation code, volatile execution logs, and generated machine-specific state remain outside `evidence/`.
- A new kernel version gets a new versioned bundle. It must not silently rewrite [`kernel-30.8.1/`](../evidence/kernel-30.8.1/).
- A faulty capture is corrected only as an explicit provenance-bearing evidence correction.
- Full probe models remain complete and readable even when they share substantial structure; exact executed input is more important than reducing a small amount of repository storage.

Run `lake test` to replay the supported projection of all retained observations. `checkReferenceProcess` separately rehashes the frozen 0.2.0 shipment and qualification artifacts; neither gate writes under `evidence/`.

### Current integrity gaps

Some older runtime projections still repeat cells, rows, paths, and structured conditions that were manually read from retained placements. Those transcriptions are reviewed but not all mechanically derived from the full case and model. Direct cascade has removed that scalability gap for its own family: the compact producer-certified bundle passed one-time old/new agreement, after which the packet-specific Lean binder was deleted. The deliberate trade is that routine replay now trusts a12-dmkits' certified raw verification and checks the pinned compact semantics instead of re-verifying the complete packet tree. Only migrate the older String lanes when measured maintenance savings justify the work; no new placement-to-packet binder or repository-wide raw inventory should be added merely for uniformity.

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

They are distribution projections, not the authoring source of the semantics. Current generated members are owned by typed Lean support or lineage declarations plus the retained evidence they cite; the correlation suites remain reviewed manual indices until their bridge is mechanized. The frozen v1 capability, suite, mutation plan, and generated-differential profile are immutable historical outputs whose retired source remains in Git at revision `03186c1`. A generated-differential profile is a campaign definition rather than a support declaration: it selects only already admitted inputs and does not expand the capability. Once an exact bundle, packet, or differential profile is exported or digest-pinned for an independent consumer, those files and their declared compatibility tuple form an immutable record. A working development projection may evolve only under a new identity, digest, or revision; an incompatible supported compatibility change requires a new identity or version.

### Evolution policy

- Never hand-edit an artifact with a typed generator to make a check pass. Change its owning Lean declaration or evidence input, regenerate, and review the complete diff.
- An internal Lean refactor that preserves the public account should produce no reference diff.
- During development, an intentional semantic, protocol, or classification change regenerates the affected current-development shipment and reruns all drift gates.
- After a shipment becomes a supported external contract, an incompatible semantic or protocol change creates a new capability or schema version rather than mutating the old identity.
- Removing a generated case must also remove every generated file and index entry; exact-directory checks should reject stale output.
- Do not update a differential profile in place after it has a retained result. A changed generator, bound, projection, source revision, or candidate revision creates a new profile identity and a new result.

For the frozen flat v1 shipment, `lake exe checkReferenceProcess` compares the live CLI manifest with current v2, compares the readable lineage with its Lean source, verifies the historical lock file's own digest, requires its exact closed schema/count/identities, rehashes all 152 inventoried dependencies plus the principal frozen artifacts, and exercises the committed process fixtures. The same gate requires the current flat suite's ninth case to equal its typed [`OperatorProtocolBridge`](../A12Kernel/Evidence/OperatorProtocolBridge.lean) artifact rather than trusting a hand-written evidence association. A future writable shipment must use a new capability identity and current production path; it must not revive the historical bridge merely to rewrite frozen bytes.

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

Run `lake exe checkReferenceProcess` to execute the committed request/response pairs through the real process boundary and rehash the frozen generated flat subset.

## Retained Rust qualification records

The Rust knowledge-transport exercise is complete and its one-off source machinery is retired. The project retains the language-neutral [mutation plan](../reference/flat-validation-empty-logic-v1.mutation-plan.json), [52-case profile](../reference/flat-validation-empty-logic-v1.generated-differential-v1.json), and compact [generated-differential result](../qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json). [`Reference/Lineage.lean`](../A12Kernel/Reference/Lineage.lean) pins each exact byte identity, and `checkReferenceProcess` rehashes them without reconstructing the historical execution.

The generated campaign profile pins Lean revision `2cdc37746737d83241f91cd89fa0b56c99c2d47a` and candidate revision `d213005b3972c2acd8f67e87f523a923d69f6a54`. The result records 52/52 agreement, identical 14/11/13/14 verdict distributions, bounded usage, and no process or integrity failure. The compact green receipt deliberately omits the 52 agreeing request/response transcripts and does not authenticate its own historical execution.

The mutation packet was exported from source revision `e408c9bd87ab8de576c900f2e42e0f13e868da76` with `PACKET.json` SHA-256 `28b1e0e074a53dc3abb7fe69f4ae97286f4fdf1e81a1d80e92e8a29709a8ab16`. Candidate revision `d213005b3972c2acd8f67e87f523a923d69f6a54` passed the natural gate, all seven declared mutations, exact restoration checks, and the 138-log isolated attestation. This repository does not duplicate that raw downstream result tree; the exact accepted outcome and assurance limits are preserved in the frozen [`flat implementer kit`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-and-qualification-outcome-2026-07-1415).

These records answer only what the pinned experiment reported. They do not define A12 semantics, change retained kernel evidence, transfer Lean proofs, approve a release, or establish candidate correctness beyond the finite profile and mutations. Their bridge, packet, checker, observer, and generated-differential implementation remain inspectable at Git revision `03186c1`. Reproducing those old commands requires a clean checkout of that revision and the exact pinned candidate inputs; they are not current project gates.

The artifacts are immutable. A future consumer or shipment receives a newly designed qualification identity against the then-current semantics, runner, and operational constraints. Do not restore this one-off machinery for anticipated reuse, and do not update its profile, result, revisions, digests, or historical wording in place.

## Evolution by change type

| Project change | `evidence/` | `reference/` | `examples/` | Qualification artifacts |
|---|---|---|---|---|
| Internal refactor, same observable account | Unchanged | Existing shipments unchanged | Unchanged | Existing records remain historical |
| Lean semantic correction | Replay unchanged observations; add evidence only if the old boundary was insufficient | Regenerate development shipment or publish a new supported version | Update affected generated/golden responses with review | Run a new qualification for affected candidates |
| Protocol or manifest change | Unchanged | Regenerate or version affected contract | Update affected requests/responses | Run a new protocol qualification |
| New semantic capability | Add focused observation and projection before claiming external correspondence, or mark it `external evidence pending` | Add a closed capability shipment only when its task boundary is research-closed | Add a few curated examples plus generated cases as applicable | Qualify selected consumers separately |
| New kernel version | Add a new evidence bundle | Publish capabilities with the new kernel-behavior identity | Add only separating version examples | Create new candidate records against that identity |
| Evidence correction | Preserve correction provenance and explain why | Regenerate every affected derived shipment | Regenerate affected evidence-derived fixtures | Invalidate or supersede affected qualification claims explicitly |

## Desired repository-wide drift contract

The lineage, reference-process gate, evidence replay, and per-family compact bundle owners form the current drift contract. Every committed artifact path or closed inventory must have one recorded owner, role, compatibility identity, update policy, and non-writing check, but the retired flat packet machinery is not a template for a repository-wide generator or receipt graph.

Generation remains an explicit maintainer action for current artifacts followed by review. A green generator run cannot create kernel evidence, approve a semantic correction, or qualify an independent consumer by itself.
