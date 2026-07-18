# External kernel evidence

This document owns the portable evidence boundary between the external A12 kernel harness and the Lean theory. It describes the three compact bundles retained in the current checkout, the two gates that consume them, and the correspondence claims those observations do and do not support.

## Current retained inventory

[`evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/) contains exactly three immutable compact bundles:

| Bundle | Exact identity | Current consumer | Retained cases |
|---|---|---|---|
| [Validation core](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json) | SHA-256 `bd8f9411cd479b009a71e7c5a93e0369815c0a0b4647f6eacb5a4b1957532db7` | [`ValidationProjection.lean`](../A12Kernel/Evidence/ValidationProjection.lean), `lake test`, and the public-suite evidence checks run by `checkReferenceProcess` | 49 records: 25 public associations and 24 private replays; 48 distinct external observations because one directional Number witness intentionally appears in both partitions |
| [Root String computation](../evidence/kernel-30.8.1/captures/string-computation-v1/semantic-observations.json) | SHA-256 `589ab2268c3347614b524a52a5667bfe5706e2a7a60f09d995da71068ea96d72` | [`StringComputationProjection.lean`](../A12Kernel/Evidence/StringComputationProjection.lean) and `lake test` | 22 project-reviewed cases: 13 final-delta observations and nine checked-outcome/delta/exact-application observations |
| [Direct String cascade](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/semantic-observations.json) | SHA-256 `1d8d253e553eba70fa990975666884833748bed9d9b2b6483f472767a9837c7a` | [`StringCascadeProjection.lean`](../A12Kernel/Evidence/StringCascadeProjection.lean) and `lake test` | Five producer-certified clean/error/delta/value-only application observations |

[`ObservationBundle.lean`](../A12Kernel/Evidence/ObservationBundle.lean) is the shared operation-neutral bounded reader. Each typed projection pins its bundle's exact bytes, closed family and case shape, provenance references, typed input, observation fidelity, and semantic comparison. Raw models, case files, diagnostic drafts, runner tables, packets, receipts, and one-time binders are deliberately absent from the current checkout; their exact identities and recovery revisions live in the [validation](archived/VALIDATION-RAW-EVIDENCE.md), [root-String](archived/STRING-COMPUTATION-RAW-EVIDENCE.md), and [direct-cascade](archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md) archives.

This is a deliberate assurance trade. The migrations ran the complete historical binders and compact lanes together before deleting the raw estates. Routine tests now check the accepted semantic meaning and exact compact bytes instead of repeatedly re-proving filesystem, model, runner, packet, qualification, or receipt relations. Git history is the audit archive; restoring that machinery to current `main` is not part of ordinary replay.

## Validation bundle and gate ownership

The validation bundle has seven ordered families. Four public families hold the current flat V2 cases, one directional Number witness, 12 captured-outer runtime cases, and four static one-star authoring cases. Three private families hold 11 path/required cases, six operator-sensitive empty-value cases, and seven uncorrelated iteration cases.

`lake test` replays the 24 private validation cases through the live checked semantics. Path cases use the normalized reference evaluator, absolute-required cases use the staged required evaluator, operator cases use the shared checked flat route, and iteration cases use the one-star selector and sum observer. The compact account retains the required-empty message code `mandatoryField` and pointer `/Order[1]/Quantity`; the other compact path and iteration records retain only the observation fields modeled by their current semantic comparison.

`lake exe checkReferenceProcess` owns the 25 public evidence associations. Through the candidate-conformance control it loads the same SHA-pinned bundle, requires the selected case ID and exact normalized request to match the suite case, validates the externally supported observation shape, and compares the suite's expected response only at that fidelity. A changed request, changed projected response, or alias to another existing evidence case is rejected. The public cases therefore do not need a separate protocol bridge or a second evidence manifest.

For public flat validation, an observed firing retains VALUE/OMISSION polarity, while authored silence is recorded only as suppression. Kernel output cannot generally distinguish hidden `NotFired` from `Unknown`, so the compact evidence does not pretend otherwise. The eight familiar empty/formal-error cases preserve their case-level external-support classification: four establish an exact firing and polarity, while four establish only authored silence. The directional witness establishes the externally visible VALUE firing for an empty unsigned Number under `!= -1`.

For public captured-outer runtime cases, the retained observation establishes the exact firing-row membership for the focused authored message. It does not claim kernel emission order, expose all formal-error channels, or turn the normalized request into a general concrete-DSL parser. For public static cases, each rejection requires both the observed kernel code and the mapped rejection class. The accepted mixed-scale ordering case records static acceptance only; its public empty firing-row answer is a Lean-account runtime projection and is not established by that authoring observation.

The private operator cases preserve the complete focused authored message list with rule code, VALUE/OMISSION polarity, and pointer for direct String equality, String `Length`, and directional signed/unsigned Number comparisons. Direct empty-String silence still cannot externally distinguish `NotFired` from `Unknown`, and the retained ASCII cases do not establish astral UTF-16 length behavior.

Both kernel routes agreed on all seven private iteration observations. The historical a12-dmkits interpreter disagreed on `having-malformed-filter-drops`: the kernel routes and Lean drop the malformed local filter row, while that historical interpreter result did not. This remains an explicit triangulation disagreement, not flattened agreement and not a kernel-strategy divergence. [`LF7`](LEAN-FINDINGS.md#lf7--a-malformed-having-filter-drops-its-row-before-consumption) records the semantic scope; the [validation archive](archived/VALIDATION-RAW-EVIDENCE.md) retains the exact raw and triangulation identities.

Both kernel routes and the a12-dmkits interpreter agreed on all 12 captured-outer runtime observations at capture time. The historical raw models preserved the executed `$` condition and complete signatures because a formatter or conversion path can otherwise lose an outer-bearing conjunct. The compact public account intentionally retains only the normalized input and externally supported firing rows; the richer raw material remains recoverable from the archive.

The four static observations establish three focused rejection code/class pairs and one acceptance:

- all-outer `Having` is rejected as `MVK_NO_ITERATION_FOR_WILDCARD` / `missingInner`;
- unequal-scale numeric equality is rejected as `MVK_INVALID_COMPARE_DEC_PLACES` / `equalityScaleMismatch`;
- an inner reference from a sibling repeatable group is rejected as `MVK_INVALID_ITERATION_IN_FILTER_CONDITION` / `fieldOutsideGroup`;
- unequal-scale numeric ordering is accepted by the static checker.

These observations are not a general authoring-diagnostic matrix. In particular, the accepted case establishes no runtime firing result, outer-origin `fieldOutsideGroup` and every unlisted Lean elaboration error fail closed rather than being assigned a kernel code, and all-inner `Having` belongs to the uncorrelated route rather than this rejection mapping.

## String computation and cascade bundles

The 13 clean root-String delta cases separate direct copy, suffix concatenation, and two-field concatenation while varying source emptiness, prior target state, and row content. They directly establish changed value, unchanged silence, stale-target clearing, absent-target silence, empty String contribution inside concatenation, final-empty no-value storage, and evaluation on an independently empty row for the retained inputs. Both kernel routes agreed. The historical a12-dmkits interpreter disagreed on three all-empty concatenation cases before a12-dmkits confirmed and fixed the mechanism as IF123; the archive retains that triangulation.

The nine String target-validation cases establish positive single-bound acceptance and rejection, retained attempted text and `stringZuKurz`/`stringZuLang` causes, change-sensitive accepted deltas, unconditional errored reporting across absent/stale/equal priors, and exact absent/present-empty/present-value application for their conservative ASCII inputs. They do not establish zero or negative bounds, combined constraints, patterns, enumerations, line-break permission and ordering, `noValueValidation`, initially present-empty targets, poison application, astral UTF-16 behavior, repeatable targets, or general target checking.

The direct-cascade compact bundle was certified by clean a12-dmkits exporter revision `1b5f463b89adc6cfb81b41121cd6c97855e8cbe3` after complete packet and qualification verification. Its five cases establish accepted-changed and accepted-equal propagation, clean no-value over stale and absent producer targets, and target rejection retaining the attempted producer value and cause while clearing the stale dependent target. Its compact value-only application projection deliberately omits exact no-value placement; those richer states remain recoverable in the archived raw unit.

Neither String bundle directly observes Lean's internal `StringTerm`, `StringStore`, dependency poison tag, graph construction, or scheduler. The cascade cases cover one authored non-repeatable edge, not transitive chains, preconditions, alternatives, aggregates, repeats, or general document mutation.

## Authority and claim boundary

The real kernel remains the behavioral authority. The Lean theory is the executable semantics-of-record for the chosen account. Retained observations establish finite empirical correspondence only for their admitted projections; proofs establish universal consequences inside the Lean account and do not prove universal equivalence with the kernel.

The compact validation bundle is project-reviewed rather than producer-certified. Its whole-file digest binds four embedded historical source-projection digests and the operator receipt; the separate operator-projection digest is preserved by the archive and dual-path checkpoint. That checkpoint established exact old/new agreement, but routine replay does not re-audit the deleted raw inputs. The direct-cascade bundle has the stronger producer-certified provenance described above. These assurance classes remain explicit rather than being normalized into one claim.

The evidence transport and IO drivers stay outside [`A12Kernel.lean`](../A12Kernel.lean), [`A12Kernel/Conformance.lean`](../A12Kernel/Conformance.lean), and [`A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean). Evidence replay is an empirical adequacy check over retained observations, not part of the trusted semantic theorem root. This repository contains no kernel binary, binding, linked type, or runtime dependency.

The current V2 suites are language-neutral consumer indices over retained evidence and Lean projections, not new observations. Candidate agreement with a suite establishes only the selected finite observable cases and does not transfer Lean's theorems. The historical Rust result and reference-semantics 0.2.0 artifacts remain in the [archived record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md), not current evidence inputs.

## Running the gates

```sh
lake test
lake exe checkReferenceProcess
```

`lake test` reports 51 compact non-public replays: 24 validation, 22 root String computation, and five direct String cascade cases. `checkReferenceProcess` separately owns the 25 public validation/correlation evidence associations while also checking the compiled CLI, manifest, fixtures, and V2 suite controls. Together the bundles retain 75 distinct external observations; the apparent 76 paths include the one directional Number observation intentionally shared between the public and private validation partitions.

Each gate is non-writing. Exact bundle binding uses `sha256sum` with a `shasum -a 256` fallback; at least one must be available for evidence replay. The shared reader rejects an unsafe path, oversized or non-regular input, malformed closed objects, duplicate identities, and incompatible bundle metadata. Family projections additionally reject digest, kernel version, family/order/count, case-shape, typed-input, observation-fidelity, or semantic-result drift.

`lake build` remains the pure internal build and executable-example gate. `lake test` checks the compact non-public correspondence cases; `checkReferenceProcess` checks public evidence associations and the reference process; [`scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh) audits the trusted theorem closure. None substitutes for the others.

## Evolution

A new semantic capsule may land as `external evidence pending`. Before claiming kernel correspondence, obtain the smallest portable observation family through an unchanged source-maintained a12-dmkits corpus/differential route or an accepted purpose-specific upstream handback, then project it through the existing compact reader when that observation shape fits. Do not resurrect capture V1, patch a copied harness, add a parallel evaluator, or build a universal packet layer in anticipation.

A pure Lean refactor or protocol-layout change must not alter retained observation bytes. A semantic disagreement is investigated at the definition or projection boundary; expected evidence is never refreshed merely to make a test green. A correction carries explicit provenance, and a new kernel version receives a new versioned bundle rather than rewriting `kernel-30.8.1`.

The exact historical validation estate, receipt and model identities, triangulation detail, dual-path checkpoint, deletion inventory, and recovery commands are in the [validation archive](archived/VALIDATION-RAW-EVIDENCE.md). Use Git to inspect those bytes when an audit needs them; do not restore the retired schema/replay stack to routine source.
