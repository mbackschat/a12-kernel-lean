# Active implementation plan

This is the volatile checkpoint for resuming the current delivery unit. Stable purpose and milestones belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), proposed product progression in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md), production engineering in [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md), and durable implementation decisions in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Git and the owning documents retain completed history; this file records only the verified baseline, active objective, immediate order, and stop conditions.

## Verified baseline

The repository has an executable Lean semantics for the currently admitted flat-validation and one-group captured-outer fragments, with checked lowering, internal laws and counterexamples, retained kernel observations, a normalized reference process, and independent-candidate conformance surfaces. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns exact clause, proof, and support status; [`EVIDENCE.md`](EVIDENCE.md) owns the retained-observation inventory and correspondence limits; [`PROTOCOL.md`](PROTOCOL.md) owns the public process contract and samples.

Two development evaluator shipments exercise the knowledge-transport model. [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) owns the completed cold implementation outcome and the generated flat capability, fixtures, conformance suite, and mutation plan. [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) owns the separate captured-outer handover and its remaining release boundary. Neither shipment is a complete A12 interpreter or a release-readiness claim.

The flat cold experiment established finite implementation and representative mutation sensitivity, but its historical mutation execution did not retain exact patches and raw logs. The source-side post-cold qualification implementation closes that tooling gap without rewriting the historical record: packet schema 2 binds the frozen Rust build/test-input closure, typed mutation plan, canonical fixture-driven observer, source-owned patches, expected observations, execution profile, commands, and payload bytes; result schema 2 binds actual parsed observations to raw logs and distinguishes `sourceExecutedReplay` from `isolatedSessionAttestation`. The complete natural-plus-seven-mutation source replay and adversarial checker set are green. A separate isolated session committed the complete schema-2 record at Rust revision `d213005b3972c2acd8f67e87f523a923d69f6a54`, and the strict checker at the packet-pinned source revision accepted its packet identity, complete raw-log tree, actual observations, commands, statuses, and restoration inventories. [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-and-qualification-outcome-2026-07-1415) owns the exact result and assurance boundary.

## Current objective

Define and execute the first bounded generated Rust-versus-Lean differential profile for this exact capability. It must expand beyond the eight retained fixtures while staying inside the admitted normalized positive-input fragment, pin both revisions and the compatibility tuple, preserve minimized disagreements, and remain Lean-account conformance rather than new kernel evidence. Add explicit dependency-free process resource bounds before the new driver invokes the independent candidate so the known unbounded-output and no-timeout limitation is not copied into a new testing lane.

## Immediate continuation order

1. Define a machine-readable bounded differential profile for `flat-validation-empty-logic-v1`: pin both revisions and the compatibility tuple, admit only supported positive normalized inputs, define deterministic enumeration or a recorded seed, cap case count and request size, name the exact response projection, and require minimized disagreement retention. Rejected inputs remain excluded until their compared diagnostic projection is normative.
2. Establish the smallest dependency-free process boundary with a per-process wall-clock timeout, stdout and stderr caps enforced while capturing, and aggregate case, byte, and elapsed-time budgets with deterministic failure records. Inspect Cedar's actual bounded differential and fuzz drivers again before fixing the limits, while preserving the subprocess and clean-room boundary.
3. Add the dual-process driver, generate non-fixture requests through the profile, execute the Lean reference and frozen Rust candidate, and compare only the declared observable response projection. Keep the first run deliberately small and pinned; the Rust sibling remains read-only except for already-ignored build output.
4. Preserve and minimize every disagreement before classification. A green run records only finite Lean-account conformance for the generated profile; it adds no kernel evidence, transfers no proof, and does not expand the supported capability.
5. Update the flat kit, testing methodology, artifact lifecycle, and implementation map only where their owned facts change, then decide from the observed coverage whether to deepen this flat capsule or resume the next semantic capsule.

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

Read [`../AGENTS.md`](../AGENTS.md), this file, the flat kit's [post-cold qualification packet](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#post-cold-mutation-qualification-packet), [qualification outcome](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#cold-test-and-qualification-outcome-2026-07-1415), and [open boundary](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#open-boundary), plus [`TESTING.md`](TESTING.md). Inspect `git status --short` and the complete diff before changing anything. Resume from the first unfinished numbered step, use red/green development, and finish with the full relevant gate set from [`TESTING.md`](TESTING.md), artifact drift checks, `git diff --check`, no `spec/` diff, and unchanged sibling status.
