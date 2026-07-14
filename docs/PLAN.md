# Active implementation plan

This is the volatile checkpoint for resuming the current delivery unit. Stable purpose and milestones belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), proposed product progression in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md), production engineering in [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md), and durable implementation decisions in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Git and the owning documents retain completed history; this file records only the verified baseline, active objective, immediate order, and stop conditions.

## Verified baseline

The repository has an executable Lean semantics for the currently admitted flat-validation and one-group captured-outer fragments, with checked lowering, internal laws and counterexamples, retained kernel observations, a normalized reference process, and independent-candidate conformance surfaces. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns exact clause, proof, and support status; [`EVIDENCE.md`](EVIDENCE.md) owns the retained-observation inventory and correspondence limits; [`PROTOCOL.md`](PROTOCOL.md) owns the public process contract and samples.

Two development evaluator shipments exercise the knowledge-transport model. [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) owns the completed cold implementation outcome and the generated flat capability, fixtures, conformance suite, and mutation plan. [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) owns the separate captured-outer handover and its remaining release boundary. Neither shipment is a complete A12 interpreter or a release-readiness claim.

The flat cold experiment established finite implementation and mutation sensitivity, but its historical mutation execution was not retained as a digest-bound, independently replayable qualification record. The generated [mutation qualification plan](../reference/flat-validation-empty-logic-v1.mutation-plan.json) therefore remains source-maintainer test planning until the strict packet and result-checking path below is complete.

## Current objective

Complete a source-side, digest-pinned mutation qualification packet and strict result checker for the flat development shipment. The packet must let a separate session run the declared exercises against the pinned Rust baseline and return a closed machine-readable record that this repository can validate without trusting a narrative report or requiring new A12 research.

The current worktree contains an incomplete draft of this target: reusable digest support, a closed qualification-result model and parser, metadata validation, and a Lake executable declaration have begun. The executable entry point, complete packet export and index binding, referenced-file and digest verification, adversarial tests, end-to-end workflow, documentation updates, and final verification have not been completed. Treat none of that draft as landed until the whole delivery passes its gates and is committed.

## Immediate continuation order

1. State the complete packet and result invariants as red tests before extending the draft. Cover closed JSON shapes, compatibility identity, pinned baseline revision and source inventory, exact mutation order, natural and final gates, complete case observations, complete connective-algebra observations where required, patch and raw-log digests, restoration inventories, toolchain identity, and rejection of every unexpected or missing result.
2. Finish the source-side packet exporter in an ignored workspace. Its index must bind the generated mutation plan, the frozen candidate baseline, source files, observation harness, semantic patches, expected observations, commands, and every shipped file by digest. Packet generation is a maintainer action and must not write the sibling Rust repository.
3. Finish the checker executable so it parses the packet and returned record strictly, recomputes every referenced digest, validates every observation against the typed qualification plan, checks restoration to the pinned natural source inventory, and fails closed on missing, additional, reordered, reused, unsafe, or inconsistent artifacts.
4. Add positive and adversarial executable checks for packet generation and result validation, then connect the standalone checker to the documented verification workflow without adding it to the trusted semantics or external-evidence roots. A passing qualification remains finite candidate evidence, not a Lean proof or kernel observation.
5. Run the project gates in [`TESTING.md`](TESTING.md), the flat artifact drift check, the strict checker controls, trust and hygiene checks, and confirm that `spec/` and sibling tracked or visible worktrees remain unchanged. Update only the owning documentation and commit the completed source-side delivery separately.
6. Stop at the source-side handoff boundary and give the user one exact prompt for a separate session rooted in the Rust project. That session imports the packet, runs every declared exercise without semantic coaching or new kernel research, restores the natural implementation after each mutation, commits its qualification record, and returns the candidate revision.
7. Consume the committed downstream record read-only, validate it with the strict checker, classify any mismatch at its owning semantic, transport, harness, or candidate layer, and update the flat kit's experiment outcome without rewriting the historical cold bundle.
8. After strict mutation qualification closes, continue with the planned generated differential phase: define a pinned valid-input profile, add a dependency-free dual-process driver, compare non-fixture requests through Lean and the frozen candidate, minimize and classify disagreements, and record only Lean-account conformance rather than new kernel evidence.

## Guardrails and stop conditions

- Work only in this repository. Sibling repositories remain read-only and visibly clean; the separate Rust session owns its implementation and returned record.
- Keep temporary packet assembly, copied candidates, logs, and test output in ignored or temporary storage. Do not leave visible untracked operational artifacts.
- Do not edit [`../spec/`](../spec/). New findings, implementation state, and experiment results belong under `docs/` according to [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md).
- Do not change dependencies, hashing strategy, linkage, or distribution policy without explicit user approval. Reuse the existing external SHA-256 command boundary.
- Preserve the existing flat protocol bytes, compatibility identity, evidence classifications, and correlation firing-only boundary unless a discovered defect requires an explicit versioned correction.
- A green generated suite or mutation record does not transfer Lean proofs to Rust, add kernel evidence, close the wider flat operation, qualify the correlation shipment, or authorize a production release.
- Stop and report a serious blocker if the packet cannot bind the candidate baseline without sibling writes, the checker would have to trust rather than verify a claimed artifact, the typed plan does not determine an expected observation, or completing the route would broaden the supported semantics.

## Resume procedure

Read [`../CLAUDE.md`](../CLAUDE.md), this file, the flat kit's [cold-test outcome](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-outcome-2026-07-14) and [open boundary](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#open-boundary), and [`TESTING.md`](TESTING.md). Inspect `git status --short` and the complete diff before changing anything; the active qualification draft may be incomplete and must not be mistaken for a verified baseline. Resume from the first unfinished numbered step, use red/green development, and finish with the full relevant gate set from [`TESTING.md`](TESTING.md), artifact drift checks, `git diff --check`, no `spec/` diff, and unchanged sibling status.
