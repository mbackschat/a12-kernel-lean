# Repository artifact lifecycle

This guide explains what belongs under [`evidence/`](../evidence/), [`reference/`](../reference/), [`examples/`](../examples/), and the historical records under [`docs/archived/`](archived/), which facts each owns, and how each should evolve. These artifacts deliberately have different lifecycles; treating all of them as either hand-authored source or disposable generated output would break the project's evidence and consumer contracts.

## The short answer

| Directory | Role | Source of truth? | Normal evolution |
|---|---|---|---|
| [`evidence/`](../evidence/) | Retained external observations, exact probe inputs, and compact accepted semantic bundles | Checked-out observations preserve the current empirical claim; accepted compact bundles are the ordinary Lean replay interface, not a second oracle | Append, version, explicitly correct, or compact under a reviewed migration; archive superseded raw estates at an exact Git revision before deletion |
| [`reference/`](../reference/) | Portable consumer shipments and the readable support-manifest mirror | Mostly derived from Lean and retained evidence; the correlation suite remains a reviewed manual index | Derive new current identities from their owners, maintain reviewed indices explicitly, and never regenerate a frozen compatibility line in place |
| [`examples/`](../examples/) | Runnable user examples, golden process regressions, and generated shipment fixtures | No; expected outputs are reviewed regression locks, not kernel evidence | Curate the small human-facing set and regenerate owned fixture sets |
| [`docs/archived/`](archived/) plus exact Git revisions | Retired compatibility identities, campaign outcomes, deleted artifact digests, and recovery instructions | Yes, for the documented historical claim and recovery boundary; no, for current behavior | Preserve concise immutable records; inspect deleted bytes at their pinned revision rather than restoring them to current source |

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

The direct-cascade migration demonstrates how a complete raw audit unit can certify a compact Lean replay bundle without remaining in every checkout. The producing a12-dmkits revisions verified the raw packet, runner, input, capability, qualification, closure, receipt, recapture relations, and compact export. One small generic reader checks the compact bundle contract, and a typed family decoder checks the pinned semantic input/observation projection. The migration ran the former complete binder and compact lane together once; the current tree retains only the compact bundle, while the [archive](archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md) names the exact raw recovery revision and identities.

Detailed evidence claims remain in [`EVIDENCE.md`](EVIDENCE.md), process and manifest compatibility in [`PROTOCOL.md`](PROTOCOL.md), executable gates in [`TESTING.md`](TESTING.md), consumer shipment and qualification contracts in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md), and current unfinished work in [`PLAN.md`](PLAN.md). This guide owns only the directory-level classification and lifecycle connecting those contracts.

## `evidence/`: retained empirical inputs

### Contents

The versioned [`evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/) bundle currently contains:

- runtime observation records under [`cases/`](../evidence/kernel-30.8.1/cases/);
- static authoring observations under [`diagnostics/`](../evidence/kernel-30.8.1/diagnostics/);
- complete standalone DM-JSON probe inputs under [`models/`](../evidence/kernel-30.8.1/models/);
- digest-pinned capture receipts under [`captures/`](../evidence/kernel-30.8.1/captures/), currently [`operator-sensitive-empty-2026-07-15.json`](../evidence/kernel-30.8.1/captures/operator-sensitive-empty-2026-07-15.json), [`string-computation-2026-07-15.json`](../evidence/kernel-30.8.1/captures/string-computation-2026-07-15.json), and [`string-target-validation-2026-07-15.json`](../evidence/kernel-30.8.1/captures/string-target-validation-2026-07-15.json), plus the producer-certified direct-cascade [`semantic-observations.json`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/semantic-observations.json);
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
- For direct cascade, the producer-certified bundle names the archived raw audit identity and ordinary Lean replay binds only the typed family projection to that compact bundle. Existing focused projection lanes remain unchanged until their own measured migration is justified.
- A newly modeled semantic clause may remain explicitly `external evidence pending`. Before claiming external correspondence or evidence-complete status, add the smallest focused observation and reviewed projection needed to anchor it.
- Historical evidence layouts and disposable-harness receipts remain immutable at their named recovery revision. A future accepted handback retains the complete observation and assurance material required by its own reviewed contract long enough to certify the smallest compact semantic account needed for ordinary Lean replay; its lifecycle must say whether the raw unit remains checked out or moves to Git history. It does not automatically reproduce the retired V1 packet, capabilities, qualification, or receipt graph. Do not retain only selected agreeing observations when the accepted contract claims a richer raw boundary. Kernel binaries, kernel-linked types or implementation code, volatile execution logs, and generated machine-specific state remain outside `evidence/`.
- A new kernel version gets a new versioned bundle. It must not silently rewrite [`kernel-30.8.1/`](../evidence/kernel-30.8.1/).
- A faulty capture is corrected only as an explicit provenance-bearing evidence correction.
- Full probe models remain complete and readable while they are the active replay source. A reviewed compact migration may move them to an exact recovery revision only after preserving the claimed semantic inputs and observations.

Run `lake test` to replay the supported projection of all retained observations. `checkReferenceProcess` checks the current 0.3.0 manifest, fixtures, transport behavior, and V2 controls; neither gate writes under `evidence/`.

### Current integrity gaps

Some older runtime projections still repeat cells, rows, paths, and structured conditions that were manually read from retained placements. Those transcriptions are reviewed but not all mechanically derived from the full case and model. Direct cascade removed that scalability gap for its own family: the compact producer-certified bundle passed one-time old/new agreement, after which the packet-specific Lean binder was deleted. The deliberate trade is that routine replay trusts the pinned historical producer certification and checks the compact semantics instead of re-verifying the complete packet tree. Only migrate the older String lanes when measured maintenance savings justify the work; no new placement-to-packet binder or repository-wide raw inventory should be added merely for uniformity.

## `reference/`: portable consumer shipments

### Contents

[`reference/`](../reference/) contains only the current reference-semantics 0.3.0/V2 shipment:

- current [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json), the readable 0.3.0 support manifest generated from finite Lean declarations in [`Reference/Support.lean`](../A12Kernel/Reference/Support.lean);
- current [`flat-validation-empty-logic-v2`](../reference/flat-validation-empty-logic-v2.conformance.json) and [`single-group-correlation-v2`](../reference/single-group-correlation-v2.conformance.json) conformance suites for 0.3.0.

The deleted reference-semantics 0.2.0/V1 files, their SHA-256 identities, the Rust campaign outcome, and exact recovery revisions are consolidated in the [archived historical record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md). They are not current shipment files or process-gate inputs.

### Responsibility and authority

This tree answers: **what exact, language-neutral capability can an independent consumer implement or check?** These files are committed because a Rust, Python, Kotlin, or TypeScript consumer should not need a Lean installation to inspect or use a shipment.

They are distribution projections, not the authoring source of the semantics. Current generated members are owned by typed Lean support plus the retained evidence they cite; the correlation suite remains a reviewed manual index until its bridge is mechanized. Once an exact bundle, packet, or profile is exported or digest-pinned for an independent consumer, its declared compatibility tuple forms an immutable record. A working development projection may evolve only under a new identity, digest, or revision; an incompatible supported compatibility change requires a new identity or version.

### Evolution policy

- Never hand-edit an artifact with a typed generator to make a check pass. Change its owning Lean declaration or evidence input, regenerate, and review the complete diff.
- An internal Lean refactor that preserves the public account should produce no reference diff.
- During development, an intentional semantic, protocol, or classification change regenerates the affected current-development shipment and reruns all drift gates.
- After a shipment becomes a supported external contract, an incompatible semantic or protocol change creates a new capability or schema version rather than mutating the old identity.
- Removing a generated case must also remove every generated file and index entry; exact-directory checks should reject stale output.
- Do not update a qualification or differential profile in place after it has a retained result. A changed generator, bound, projection, source revision, or candidate revision creates a new profile identity and a new result.

`lake exe checkReferenceProcess` compares the live CLI manifest with the current readable V2 mirror, exercises the committed process fixtures, and runs the current flat and correlation suite controls against the compiled reference. The current flat suite's directional witness remains independently bound by [`OperatorProtocolBridge`](../A12Kernel/Evidence/OperatorProtocolBridge.lean) rather than trusting a hand-written evidence association. A future shipment must use a current production path and a reviewed identity; it must not revive the historical V1 bridge merely to reconstruct deleted bytes.

### Current integrity gap

The current correlation suite is structurally validated and executed against the current reference, but its projection-to-protocol associations are still maintained manually. Correlation should be converted to a typed descriptor and checked generation pattern before another large capability is added. The current support-manifest mirror is drift-checked by the process gate but does not have an independent write command.

## `examples/`: human examples and regression fixtures

### Contents

[`examples/reference-cli/`](../examples/reference-cli/) currently combines two roles:

1. curated request/response pairs intended to be readable and runnable by a user;
2. complete fixture sets used by process and downstream conformance tests.

The eight pairs under [`flat-evidence/`](../examples/reference-cli/flat-evidence/) originated in the retired 0.2.0 handover and remain useful unchanged fixtures for the corresponding current flat V2 cases; their historical generation is recorded in the [archive](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md). The root request/response pairs are maintained as readable golden examples and are explicitly enumerated by the reference-process test; this includes the current directional-polarity control [`empty-unsigned-number-not-equal-negative.request.json`](../examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json), while the correlation subset is referenced by the current suite.

### Responsibility and authority

This tree answers: **how can a user run the current reference process, and which exact public responses must remain stable for these inputs?** A committed response is a golden regression lock over the normalized protocol. It is not external kernel evidence merely because the Lean executable can reproduce it.

### Evolution policy

- Keep the human-facing set deliberately small, separating, and understandable.
- Edit a curated request only when its teaching or boundary role changes, and review the resulting response semantically.
- Regenerate generated fixture sets only through their owning typed bridge.
- An expected-response change requires the same review as the semantic or protocol change that caused it. Blindly accepting output from the current evaluator would make the regression self-confirming.
- The generated flat directory has an exact-set check and must fail on a missing, changed, or stale fixture. Curated root fixtures are currently enumerated explicitly, so an additional unreferenced file can survive; repository-wide exact inventory remains desired drift work.

As the shipment corpus grows, generated conformance matrices should move conceptually—and, at a versioned layout boundary, physically—beside their capability under the shipment surface. `examples/` should remain the concise human entry point instead of becoming the complete test corpus.

Run `lake exe checkReferenceProcess` to execute the committed request/response pairs through the real process boundary and run the current suite controls.

## Archived Rust qualification record

The Rust knowledge-transport exercise is complete, and its checked-out profile, result, and one-off source machinery have been retired. The [archived historical record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md) preserves the exact compatibility identity, source and candidate revisions, packet and result hashes, 52/52 verdict distribution, assurance limits, and recovery instructions. These facts answer only what the pinned experiment reported: they do not define current A12 semantics, add kernel evidence, transfer Lean proofs, approve a release, or establish candidate correctness beyond the finite historical profile. A future consumer receives a newly designed qualification identity against the then-current semantics and operational constraints; do not restore the retired machinery for anticipated reuse.

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

The current support declarations, reference-process gate, evidence replay, and per-family compact bundle owners form the current drift contract. Every committed artifact path or closed inventory must have one recorded owner, role, compatibility identity, update policy, and non-writing check, but the retired flat packet machinery is not a template for a repository-wide generator or receipt graph.

Generation remains an explicit maintainer action for current artifacts followed by review. A green generator run cannot create kernel evidence, approve a semantic correction, or qualify an independent consumer by itself.
