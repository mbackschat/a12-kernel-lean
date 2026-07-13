# Active implementation plan

This is the resumable plan for the next concrete delivery unit. Stable purpose and long-term potential belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md); the proposed release shape belongs in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md); durable implementation decisions belong in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).

## Landed verification boundary

The checked one-star correlation capsule is complete. It adds explicit repeatable-group declarations, path-derived outer-to-inner repeatable ancestry, shared repeatable-aware path resolution, a parser-independent single-star correlated surface, proof-bearing lowering, exact group/scope/kind/operator/scale checks, model-derived raw-cell checking, fail-closed unknown/cross-group/wrong-scope runtime references, and candidate-row validation before firing evaluation. Nested false-singleton scope metadata is rejected while sibling repeatable groups remain valid. All twelve retained captured-outer runtime cases now pass through checked lowering and model-derived formal checking instead of constructing the core directly.

The fourth closed evidence lane retains four kernel 30.8.1 authoring observations and their exact seeded models: all-outer rejection, unequal-scale `==` rejection, acceptance of the same operands under `<`, and one sibling-repeatable-group inner-reference rejection. Its exact binding and fail-closed projection rules remain owned by [`EVIDENCE.md`](EVIDENCE.md). The full gate reports `42/42`: 36 runtime observations and six static authoring observations.

The theorem boundary is intentionally precise. Selector/relation, observation-footprint, declaration/policy coherence, fail-closed routing, scale-law, and raw-candidate-validation-to-semantic-`WellFormed` results are proved. The checked-wrapper lemmas expose structural certificates carried by successful lowering; they are not a surface-to-core semantic-preservation proof because the surface does not yet have an independent dynamic semantics.

The first product-shaped process boundary is also complete. `a12-kernel-reference` reads at most the protocol byte limit plus one detection byte, safely preflights JSON depth and canonical structural integers before ordinary parsing, decodes exact decimal strings, validates the expanded model and sparse cells, and routes the condition through the existing checked elaborator and evaluator. It emits deterministic verdicts or finite fail-closed category/code diagnostics, and `--manifest` is generated from the same typed classifiers used by the decoder and checked against [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json). [`PROTOCOL.md`](PROTOCOL.md) owns the exact contract and the runnable samples under [`examples/reference-cli/`](../examples/reference-cli/); `lake exe checkReferenceProcess` exercises the compiled binary independently of `lake test`.

## Natural verification checkpoint

This is the intended stop for user verification: the first usable Lean reference CLI exists without broadening semantic support or changing the retained kernel-evidence claim. From the repository root, run:

```sh
lake build
lake test
lake exe checkReferenceProcess
./scripts/check-lean-trust.sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
lake exe a12-kernel-reference --manifest
```

The expected first sample result is `fired` with `omission` polarity. Other accepted and rejected inputs, with adjacent expected responses, are listed in [`PROTOCOL.md`](PROTOCOL.md#regression-checked-sample-data).

Known non-blocking process-hardening work remains before packaging a public release: add exact maximum/maximum-plus-one black-box probes for every manifest limit not already covered at the process boundary, exercise every rejected-cause tag and the remaining accepted Number-`notEqual` matrix cell, and decide whether a future manifest schema should expose the documented preclassified-scalar trust boundary directly. The decoder is already bounded, finite classifiers generate the manifest, and focused unit/process checks cover the mechanisms; these are coverage and machine-discoverability gaps, not known runtime/manifest disagreements, so they do not block this first interpreter checkpoint.

A resumed session must distinguish three states. If this CLI capsule is still an uncommitted diff, it is only a release candidate: finish the independent reviews, correct every blocker, run the complete gates, and commit it separately before starting new semantics. If the commit exists but the user has not yet accepted the checkpoint, remain here and answer verification questions without modifying files unless explicitly asked. Only after the committed checkpoint is accepted should work proceed to the next delivery unit below.

## Next delivery unit: expose the checked one-star correlation slice

After this checkpoint is accepted, the next recommended product increment is a row-addressed normalized operation for the already implemented and evidenced one-star captured-outer validation slice. This is preferable to adding a new semantic family immediately because it makes the project's most difficult existing mechanism—the `$`-outer distinction—available to independent consumers while reusing its checked lowering, candidate validation, retained kernel observations, and proofs.

The design must stop and be reassessed if exposing that exact slice would require pretending to have a general `Document` adapter, complete repeatable semantics, or filtered-result polarity. In that case, record the missing abstraction in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and choose the smallest semantic capsule that closes it; do not widen protocol v1 around an invented approximation.

Success criteria:

1. The existing `flatValidation.evaluateFull` request and response remain byte-stable; a new named operation has its own closed row-addressed input and output shapes.
2. The request represents only the current one-group, one-star, direct-child Number/repetition comparison slice: explicit ordered 1-based unique candidates, checked inner/outer origins, model-derived raw cells, outer guard, and selected-presence consumer.
3. The response exposes only observations the current semantics and retained evidence justify, principally firing rows and the documented polarity boundary; it does not manufacture kernel emission order or unimplemented filtered-result polarity.
4. Every accepted request routes through the existing checked correlation lowering and model-derived candidate validator. There is no second repeatable evaluator and no general DM-JSON or concrete DSL parser.
5. Process-level red/green tests cover an accepted `$` case, self-exclusion, malformed selected versus dropped consumers, row-zero/duplicate-candidate rejection, a static elaboration rejection, deterministic output, and unchanged flat fixtures.
6. The generated support manifest distinguishes the two operations and their disjoint supported fragments. The implementation map preserves the exact external-evidence projection and marks any transport-only behavior separately.

## Implementation sequence

1. Read [`PROTOCOL.md`](PROTOCOL.md), [`ARCHITECTURE.md`](ARCHITECTURE.md), the §9 row in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), and the public checked API in [`../A12Kernel/Elaboration/Correlation.lean`](../A12Kernel/Elaboration/Correlation.lean). Write the smallest operation-specific contract and nearest exclusions before code.
2. Add independent process-level red tests that leave the existing flat fixtures unchanged and demonstrate the exact firing-row boundary.
3. Add only the transport structures and pure adapter required to call the checked correlation route; keep JSON/IO outside the library, conformance, and trusted theorem roots.
4. Extend the finite support declarations and shipped manifest mirror, then add runnable correlation samples that are the same files exercised by the black-box gate.
5. Update the ownership-triggered documents, run independent code/protocol/proof-claim/documentation reviews, run every final gate, and commit the correlation process capsule separately.

## Deliberate exclusions from the next delivery unit

The next operation does not add concrete EN/DE condition parsing, general DM-JSON loading, arbitrary repeatable execution, nested or multiple stars, general cross-group references, general consumers, message interpolation, filtered-result polarity, computation, partial validation, a long-running service, FFI, or packaged release binaries. Those remain later capsules.

## Resume procedure

Read [`../CLAUDE.md`](../CLAUDE.md), this file, [`PROTOCOL.md`](PROTOCOL.md), and [`ARCHITECTURE.md`](ARCHITECTURE.md); inspect `git status --short` and the current diff; verify `lake build`, `lake test`, `lake exe checkReferenceProcess`, `./scripts/check-lean-trust.sh`, `git diff --check`, no `spec/` diff, and both sibling statuses against their recorded baseline. Follow the three-state rule above. If the flat CLI checkpoint is committed and accepted, begin at the implementation sequence; preserve the existing flat protocol bytes and do not broaden either semantic fragment merely to make a transport test convenient.
