# Active implementation plan

This is the volatile checkpoint for resuming the current delivery unit. Stable purpose and milestones belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), proposed product progression in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md), production engineering in [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md), and durable implementation decisions in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Git and the owning documents retain completed history; this file records only the verified baseline, active objective, immediate order, and stop conditions.

## Verified baseline

The repository has an executable Lean semantics for the currently admitted flat-validation and one-group captured-outer fragments, with checked lowering, internal laws and counterexamples, retained kernel observations, a normalized reference process, and independent-candidate conformance surfaces. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns exact clause, proof, and support status; [`EVIDENCE.md`](EVIDENCE.md) owns the retained-observation inventory and correspondence limits; [`PROTOCOL.md`](PROTOCOL.md) owns the public process contract and samples.

Two development evaluator shipments exercise the knowledge-transport model. [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) owns the completed cold implementation outcome and the generated flat capability, fixtures, conformance suite, and mutation plan. [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) owns the separate captured-outer handover and its remaining release boundary. Neither shipment is a complete A12 interpreter or a release-readiness claim.

The flat cold experiment established finite implementation and representative mutation sensitivity, but its historical mutation execution did not retain exact patches and raw logs. The source-side post-cold qualification implementation now closes that tooling gap without rewriting the historical record: packet schema 2 binds the frozen Rust build/test-input closure, typed mutation plan, canonical fixture-driven observer, source-owned patches, expected observations, execution profile, commands, and payload bytes; result schema 2 binds actual parsed observations to raw logs and distinguishes `sourceExecutedReplay` from `isolatedSessionAttestation`. The complete natural-plus-seven-mutation source replay and the adversarial checker set are green in the containing revision. The isolated downstream schema-2 record is still pending.

## Current objective

Export a packet whose source revision names this completed source-side qualification delivery, then run it in a separate Rust session without semantic coaching or new A12 research. Consume the committed downstream record read-only and validate it as a digest-bound, internally consistent `isolatedSessionAttestation`, without claiming that the source checker independently witnessed its execution.

After that isolated record closes, define and execute the first bounded generated Rust-versus-Lean differential profile for this exact capability. It must expand beyond the eight retained fixtures while staying inside the admitted normalized positive-input fragment and must remain Lean-account conformance rather than new kernel evidence.

## Immediate continuation order

1. From this clean committed revision, export the packet into ignored `.lake/qualification/`, verify it against the frozen Rust candidate, run its packet-local payload verifier, and retain the `PACKET.json` SHA-256 out of band. Packet generation remains a source-maintainer action and must not write the sibling Rust repository.
2. Stop at the source-side handoff boundary and give the user one exact prompt for a separate session rooted in the Rust project. That session verifies the out-of-band packet digest, runs the natural gate and all seven declared exercises from the packet without semantic coaching or new kernel research, restores the natural build-input closure after every mutation, commits only its qualification result, and returns the candidate revision.
3. Consume the committed downstream record read-only, validate it with `checkMutationQualification --check`, and classify any mismatch at its owning semantic, transport, harness, candidate, or attestation layer. Acceptance means a digest-bound, internally consistent isolated-session attestation; update the flat kit's experiment outcome without rewriting the historical cold bundle or claiming independently witnessed execution.
4. Define a machine-readable bounded differential profile for `flat-validation-empty-logic-v1`: pin both revisions and the compatibility tuple, admit only supported positive normalized inputs, define deterministic enumeration or a recorded seed, cap the case count and request size, name the exact response projection, and preserve minimized disagreements. Rejected inputs remain excluded until their compared diagnostic projection is normative.
5. Add the smallest dependency-free dual-process driver needed for that profile, compare non-fixture requests through Lean and the frozen candidate, and classify results only as finite Lean-account conformance. Keep the first run deliberately small and pinned; do not turn this development driver into an untrusted-execution service.
6. Before high-volume generation or any untrusted candidate, add Cedar-informed explicit process resource controls at the execution boundary: a per-process wall-clock timeout, stdout and stderr caps enforced while capturing rather than after allocation, and aggregate case, byte, and elapsed-time budgets with deterministic failure records. The current stored-artifact size and tree limits do not provide those runtime guarantees, so scale-up remains deferred until this step is complete.

## Guardrails and stop conditions

- Work only in this repository. Sibling repositories remain read-only and visibly clean; the separate Rust session owns its implementation and returned record.
- Keep temporary packet assembly, copied candidates, logs, and test output in ignored or temporary storage. Do not leave visible untracked operational artifacts.
- Do not edit [`../spec/`](../spec/). New findings, implementation state, and experiment results belong under `docs/` according to [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md).
- Do not change dependencies, hashing strategy, linkage, or distribution policy without explicit user approval. Reuse the existing external SHA-256 command boundary.
- Preserve the existing flat protocol bytes, compatibility identity, evidence classifications, and correlation firing-only boundary unless a discovered defect requires an explicit versioned correction.
- A green generated suite or mutation record does not transfer Lean proofs to Rust, add kernel evidence, close the wider flat operation, qualify the correlation shipment, or authorize a production release.
- Do not describe acceptance of an external record as source-witnessed execution. The checker verifies its closed bytes and consistency; `isolatedSessionAttestation` records the remaining trust boundary.
- Stop and report a serious blocker if the packet cannot bind the candidate baseline without sibling writes, a recorded observation cannot be bound to its actual raw output, the typed plan does not determine an expected observation, or completing the route would broaden the supported semantics.

## Resume procedure

Read [`../CLAUDE.md`](../CLAUDE.md), this file, the flat kit's [post-cold qualification packet](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#post-cold-mutation-qualification-packet), [cold-test outcome](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-outcome-2026-07-14), and [open boundary](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#open-boundary), plus [`TESTING.md`](TESTING.md). Inspect `git status --short` and the complete diff before changing anything. Resume from the first unfinished numbered step, use red/green development, and finish with the full relevant gate set from [`TESTING.md`](TESTING.md), artifact drift checks, `git diff --check`, no `spec/` diff, and unchanged sibling status.
