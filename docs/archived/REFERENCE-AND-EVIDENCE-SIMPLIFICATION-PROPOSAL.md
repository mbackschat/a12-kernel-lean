# Reference and evidence simplification proposal

> **Status:** archived 2026-07-19 after completion. All three decisions are implemented; current semantics, proofs, V2 controls, and empirical observations remain live through the compact boundary. Durable architecture and artifact rules have moved to their owners.

## Outcome

Migrate every active reference-semantic handover and control to current 0.3.0/V2, remove the checked-out 0.2.0/V1 compatibility estate, and collapse older evidence families onto the already-settled compact observation-bundle boundary. Preserve historical claims through archived documentation and exact Git revisions rather than runnable legacy code. Preserve current external correspondence through compact checked observations rather than verbose raw models and family-specific binders in `HEAD`.

This proposal concerns this repository's reference-semantics identities and evidence layout. It is separate from a12-dmkits' portable capture-contract V1, the kernel's deprecated document API called V1, and the still-current normalized wire `protocolVersion: 1`.

## Measured baseline

All figures below count tracked file bytes and exclude ignored `.DS_Store` files. Finder or `du` reports larger allocation sizes because of filesystem blocks.

| Area | Tracked bytes | Nonblank lines | Position |
|---|---:|---:|---|
| `A12Kernel/` | 825,091 | 17,278 | Reduction target, but not at the expense of the theory |
| Trusted semantics, elaboration, proofs, and conformance | 288,513 | 5,453 | Keep |
| Trust audit | 14,285 | 256 | Keep |
| Reference CLI, candidate tooling, and tests | 179,810 | 3,583 | Active product boundary |
| Bounded process code and tests | 27,302 | 600 | Active safety boundary |
| Evidence modules and driver | 315,181 | 5,893 | Primary source-reduction target |
| `evidence/` | 969,605 | 25,128 | Primary data-reduction target |

The existing compact direct-cascade reader, typed projection, and tests occupy 42,356 bytes and 746 nonblank lines. The other evidence modules occupy 217,746 bytes and 4,163 lines, while [`EvidenceMain.lean`](../../A12Kernel/EvidenceMain.lean) adds another 55,079 bytes and 984 lines. This is the imbalance to remove.

The `evidence/` mass is mostly repeated complete input material: `models/` alone is 630,297 bytes, captures are 146,049 bytes, and cases are 110,649 bytes. These files are valuable audit inputs, but most are not needed by current V2 candidate execution and need not remain checked out after compact replay and exact historical recovery are established.

The durable ratio guard is defined in [`CLAUDE.md`](../../CLAUDE.md): after this wave, total Evidence/Reference/Process support code and its IO/test drivers must not exceed the Semantics/Elaboration/Proofs/Conformance estate in tracked nonblank Lean lines, and evidence alone should remain below one third of that theory estate. Until then, support-only changes must be net-negative. These are stop-and-redesign thresholds, not incentives to compress readable code or weaken tests.

Use this exact `zsh` count while the proposal is active:

```sh
theory_files=(A12Kernel/Core.lean A12Kernel/Cell.lean A12Kernel/Document.lean A12Kernel/Basic.lean A12Kernel/Proofs.lean A12Kernel/Conformance.lean A12Kernel/Semantics/*.lean A12Kernel/Elaboration/*.lean A12Kernel/Proofs/*.lean A12Kernel/Conformance/*.lean)
support_files=(A12Kernel/Evidence/*.lean A12Kernel/Reference/*.lean A12Kernel/Process/*.lean A12Kernel/EvidenceMain.lean A12Kernel/ReferenceMain.lean A12Kernel/ReferenceProcessTestMain.lean A12Kernel/CandidateConformanceMain.lean A12Kernel/ProcessTestMain.lean)
evidence_files=(A12Kernel/Evidence/*.lean A12Kernel/EvidenceMain.lean)
awk 'NF { n++ } END { print n+0 }' "${theory_files[@]}"
awk 'NF { n++ } END { print n+0 }' "${support_files[@]}"
awk 'NF { n++ } END { print n+0 }' "${evidence_files[@]}"
```

At this baseline it prints 5,453 theory, 10,076 support, and 5,893 evidence lines. After local V1 retirement and before writing any replacement family, recount and compute the final evidence allowance as the smaller of one third of theory and `theory − non-evidence support`. Budget the existing compact lane and every remaining family together against that allowance. If readable closed projections and their separating tests do not fit, remove more obsolete support, retain the affected old family temporarily, or request an explicit owner exception; never meet the ratio by compression, untyped shortcuts, weakened checks, or deleting an observation still claimed by current documentation.

After the root-String deletion, the same count printed 5,453 theory, 8,009 support, and 4,121 evidence lines. Non-evidence support was 3,888, so both ratio limits converged on a final evidence allowance of 1,565 lines. The settled generic reader/tests and the two compact String lanes occupied 1,082, leaving 483 readable nonblank lines for every remaining typed family plus the final driver. Step 10 therefore began with a shape-and-budget preflight against that real limit rather than forcing the number through compression, untyped shortcuts, or weakened checks.

The completed wave measures 5,453 theory, 5,449 support, and 1,528 evidence nonblank Lean lines. Tracked `A12Kernel/` is 577,449 bytes and tracked `evidence/` is 135,047 bytes. Evidence is below one third of theory, total support is four lines below theory, and the checked-out evidence is exactly three compact bundles. The permanent validation projection and focused tests occupy 428 readable lines; the final common driver remains small.

## Decision 1 — retire local reference-semantics V1 (completed)

Current V2 already subsumes the finite V1 behavior:

- [`flat-validation-empty-logic-v2.conformance.json`](../../reference/flat-validation-empty-logic-v2.conformance.json) contains the complete eight-case V1 body unchanged and adds the corrected directional Number witness.
- [`single-group-correlation-v2.conformance.json`](../../reference/single-group-correlation-v2.conformance.json) has the same sixteen-case body as V1; only the identity, reference-semantics version, and manifest association differ.
- [`supported-fragment-v2.json`](../../reference/supported-fragment-v2.json) retains protocol 1, manifest schema 2, kernel 30.8.1, the same operations, and the same admitted surface while naming the current account.
- The current reference executable passes both old finite suites as well as V2.

V2 therefore replaces every active V1 conformance use. It does not retroactively relabel the Rust candidate or its 52/52 result as a V2 qualification. Move that historical experiment to one archived document with its exact revisions, verdict distribution, and key hashes, then remove it from live compatibility gates and current handover instructions.

The stale `checkGeneratedDifferential` invocations were already removed from [CI](../../.github/workflows/lean_action_ci.yml) in commit `c2287d5`; the retired Lake target is no longer called. The completed migration:

1. Update the two existing implementer-kit paths in place to describe current V2 semantics, manifests, suites, commands, and exclusions. Do not create parallel V1/V2 kits.
2. Move the historical Rust experiment and reference-semantics 0.2.0 provenance into `docs/archived/`; remove V1 compatibility history from live docs.
3. Deleted `Reference/Lineage.lean` and moved its four current constants directly into [`Reference/Support.lean`](../../A12Kernel/Reference/Support.lean); a separate one-record identity module would have added indirection without a second live account.
4. Remove historical lock traversal, separating-replay serialization, V1-prefix comparison, and lineage-mirror checks from [`ReferenceProcessTestMain.lean`](../../A12Kernel/ReferenceProcessTestMain.lean), while retaining current manifest, directional regression, V2 suite integrity, and current candidate controls.
5. Delete the V1 manifest, descriptor, two V1 suites, mutation plan, generated profile, Rust result, artifact lock, separating replay, and lineage mirror. Delete the empty `qualification/` tree if nothing remains.
6. Remove redundant trust-script probes for already-deleted source names; the general source-zone inventory remains the owning guard.
7. Sweep live docs for reference-semantics 0.2.0/V1 compatibility claims. Preserve the current wire protocol 1 and never rename it V2.

This stage removed 88,535 checked-out bytes and 2,196 nonblank data/source lines across the explicit V1 estate, plus the historical process-gate branch. Its direct `A12Kernel/` saving is modest; its main value is removing compatibility coupling and unlocking the larger evidence deletion. The current gate still checks the current manifest, fixtures, V2 integrity suites, and compiled-reference controls. The [archive](REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md) owns the deleted identities, hashes, Rust outcome, and recovery revisions.

## Decision 2 — perform one final evidence-compaction wave (completed)

Do not create another general harness. Reuse the existing closed [`ObservationBundle`](../../A12Kernel/Evidence/ObservationBundle.lean) contract and write only small family-specific typed projections. For each old family, establish exact old/new agreement once at a named revision, retain the compact bundle and projection, then delete the old schema/replay/binder code and verbose raw artifacts from `HEAD`.

The compact family must retain enough information to replay the same empirical claim: kernel behavior version, stable case identity and order, normalized semantic input, externally observed output at the claimed fidelity, provenance revision, and digest references to the archived raw source. If a current upstream route can certify those bytes without resurrecting the retired capture V1, use that certification. Otherwise label the result honestly as a project-reviewed compact projection, bind the exact pre-compaction Git revision and raw digests, and keep the full raw material recoverable there.

Any one-off converter or dual-reader used for migration is deleted in the same change after its agreement record is accepted. No new permanent generator, receipt graph, schema registry, qualification framework, or compatibility layer survives the wave.

### Highest-return family — completed

The two older String stacks were migrated together before further computation-control semantics so the one-time infrastructure wave can finish and stay finished:

| Removable estate | Code | Data | Gross total |
|---|---:|---:|---:|
| String computation schema/replay/binder and retained data | 53,283 bytes | 47,091 bytes | 100,374 bytes |
| String target-validation schema/replay/binder and retained data | 61,521 bytes | 33,399 bytes | 94,920 bytes |
| Combined | 114,804 bytes | 80,490 bytes | 195,294 bytes |

Commit `19733d9` is the immutable dual-path checkpoint: the complete old binders, a migration-only typed comparator, and the compact replay agreed on all 22 ordered cases. The deletion then removes the six old modules, the temporary comparator, and 33 raw files. One 13,104-byte compact bundle retains two independent source records, while one 271-nonblank-line typed projection and 65 lines of focused mutation tests preserve the two original observation fidelities without adding a route, reader, registry, or generator. The source replacement is 336 lines versus the old permanent 2,106, a net removal of 1,770 nonblank Lean lines; the data replacement removes 67,386 bytes. Exact recovery identities and limits live in [`archived/STRING-COMPUTATION-RAW-EVIDENCE.md`](STRING-COMPUTATION-RAW-EVIDENCE.md).

### Remaining families — completed

The final migration compacted the remaining old families together because their public cases could reuse the current process gate and their non-public cases fit one closed typed projection:

| Removed family data | Bytes |
|---|---:|
| Flat/path/required | 340,292 |
| Correlation | 221,666 |
| Iteration | 101,086 |
| Operator-sensitive | 72,000 |
| Correlation elaboration | 26,266 |

Commit `a04d6d9f51227dbe47014a5181590507e1b269bd` is the immutable validation dual-path checkpoint. Its legacy readers checked all 48 validation cases, the new compact lane replayed all 24 private validation cases, and the current V2 process gates checked the 25 public associations against exact normalized requests and projected responses. The already-compact 22-case root-String and five-case cascade lanes also passed, while their own archives retain their earlier complete-binder comparisons. The public/private directional witness is deliberately shared, so the validation bundle has 49 records for 48 distinct external observations.

The final deletion removes 85 raw files totaling 761,310 bytes and 12 schema/replay/bridge modules totaling 2,061 nonblank Lean lines, then replaces the legacy driver with a small dispatcher. The 116,974-byte validation bundle and 428-line projection/test lane retain the observable boundary without preserving a second model, path, or correlation interpreter. Exact recovery identities and limits live in [`archived/VALIDATION-RAW-EVIDENCE.md`](VALIDATION-RAW-EVIDENCE.md).

## Decision 3 — archive opaque raw units outside `HEAD` (completed)

The current Lean code reads only three compact bundles: the 4,969-byte direct-cascade export, the 13,104-byte root-String bundle, and the 116,974-byte validation bundle. The direct-cascade archive migration recorded exact producer revisions, project recovery revision, Git tree objects, receipt and scenario SHA-256 identities, and claim limits in [`archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md`](STRING-DIRECT-CASCADE-RAW-EVIDENCE.md), then removed 31 raw/scenario files, 123,184 bytes, and 4,056 nonblank lines from `HEAD`. The root-String migration records its two raw capture identities, projection and model digests, case trees, dual-path agreement checkpoint, and claim limits in [`archived/STRING-COMPUTATION-RAW-EVIDENCE.md`](STRING-COMPUTATION-RAW-EVIDENCE.md), then removes 33 raw files and 80,490 bytes after exact 22/22 agreement. The validation archive records the five source projection digests, operator receipt, source trees, one-time checkpoint, fidelity reductions, and triangulation limits before removing the remaining raw estate.

The durable rule is now settled: compact observations stay checked out; complete raw audit material moves to a named immutable Git revision with exact identities in an archive record. Git history remains the recovery archive. A release asset may mirror that archive for convenience but is not the sole authority.

This reduces working trees, source archives, and ordinary release checkouts. It does not shrink existing full Git history; rewriting history for a repository of this size would add more risk than value and is not proposed.

## Assurance tradeoff

The project gives up immediate checkout-local inspection of every complete historical model and packet. It does not give up the executable semantic comparison, case identities, observed outputs, provenance, or recoverability of the raw material.

Do not delete an old family until:

1. Its compact input and observation shape closes the same claimed boundary.
2. Old and compact readers agree on every retained case at one committed revision.
3. A separating mutation proves that bypassing the semantic mechanism fails the compact replay.
4. The archive revision and raw digests are recorded before deletion.
5. `lake test` exercises the compact family offline without fetching external assets.
6. Current V2 suite evidence links remain exact.

If one of these conditions cannot be met without inventing a substantial framework, retain that family temporarily and continue semantic work. The simplification must remove more source than it adds.

## What remains

Keep the trusted semantics, elaboration, proofs, conformance, trust audit, current V2 manifest and suites, shared runnable fixtures, reference evaluator, generic candidate runner, bounded process boundary, compact observation reader, and the minimum typed projections needed by current external-correspondence claims.

Going materially below the target ranges would require a separate product decision to remove or split the reference CLI and candidate-conformance product. That is not an evidence cleanup and is outside this proposal.

## Target and gates

The realistic target is `A12Kernel/` at approximately 580–650 KiB and `evidence/` at approximately 50–150 KiB, excluding ignored files, without cutting the theory or current product boundary.

The completed working tree is 577,449 tracked bytes under `A12Kernel/` and 135,047 tracked bytes under `evidence/`; the small `A12Kernel/` underrun reflects deletion of obsolete support rather than lost theory. `lake test` owns 51 compact private replays—24 validation, 22 root-String, and five direct-cascade—while `checkReferenceProcess` owns 25 exact public normalized associations. These are separate gates and must not be summed into a claim that one runner replayed all 76 records; the validation bundle itself contains 49 records for 48 distinct observations.

Run after each independently committable stage:

```sh
lake build
lake test
lake exe checkReferenceProcess
lake exe checkBoundedProcess
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v2.conformance.json
lake exe checkCandidateConformance --self-test --suite reference/single-group-correlation-v2.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/flat-validation-empty-logic-v2.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/single-group-correlation-v2.conformance.json
./scripts/check-lean-trust.sh
git diff --check
git diff HEAD --exit-code -- spec/
```

Also require resolved Markdown links, no live reference to deleted Lake targets or V1 files, measured before/after tracked byte and nonblank-line totals, a clean worktree, and an independent deletion-boundary review. Do not push.

## Recommended order

The stale CI calls, local V1-to-V2 retirement, all three compact migrations, raw-estate deletion, driver reduction, measurements, and gates are complete. This proposal is archived with the delivery; subsequent work returns immediately to ordered computation connectives and first-match alternatives with the infrastructure settled.
