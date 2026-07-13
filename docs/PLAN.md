# Active implementation plan

This is the resumable plan for the next concrete delivery unit. Stable purpose and long-term potential belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md); the proposed release shape belongs in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md); durable implementation decisions belong in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).

## Landed verification boundary

The checked one-star correlation capsule is complete. It adds explicit repeatable-group declarations, path-derived outer-to-inner repeatable ancestry, shared repeatable-aware path resolution, a parser-independent single-star correlated surface, proof-bearing lowering, exact group/scope/kind/operator/scale checks, model-derived raw-cell checking, fail-closed unknown/cross-group/wrong-scope runtime references, and candidate-row validation before firing evaluation. Nested false-singleton scope metadata is rejected while sibling repeatable groups remain valid. All twelve retained captured-outer runtime cases now pass through checked lowering and model-derived formal checking instead of constructing the core directly.

The fourth closed evidence lane retains four kernel 30.8.1 authoring observations and their exact seeded models: all-outer rejection, unequal-scale `==` rejection, acceptance of the same operands under `<`, and one sibling-repeatable-group inner-reference rejection. The projection contains no expected diagnostic code, pins each complete model file by SHA-256, requires the retained `en_US` condition language, rejects every English lexer keyword in its unquoted identifier subset and any projected group with a repeatable proper ancestor, and binds the retained model hierarchy, seed rule, complete candidate draft, capture provenance, and diagnostic routing. It maps only the three externally established rejection shapes, including only inner-origin `fieldOutsideGroup`, and fails closed on outer-origin `fieldOutsideGroup`, `missingOuter`, and every other unclassified result. Generic binding guards cover structural mutations, while focused mutations of one real retained diagnostic fixture exercise the digest, language, ancestry, draft/seed, provenance, and diagnostic-routing rejection paths; all retained cases cross the positive binding gate. The full gate reports `42/42`: 36 runtime observations and six static authoring observations.

The theorem boundary is intentionally precise. Selector/relation, observation-footprint, declaration/policy coherence, fail-closed routing, scale-law, and raw-candidate-validation-to-semantic-`WellFormed` results are proved. The checked-wrapper lemmas expose structural certificates carried by successful lowering; they are not a surface-to-core semantic-preservation proof because the surface does not yet have an independent dynamic semantics.

## Next milestone: first product-shaped Lean reference interpreter

The project already has a small executable interpreter internally: supported conditions lower and evaluate in Lean, conformance examples elaborate, and retained observations replay through `lake test`. The immediate next milestone is to make the flat fragment usable by non-Lean software through a stable process boundary. This is one focused capsule away, not a later computation-stage dependency.

The first interpreter slice should accept a versioned normalized JSON request containing the existing expanded flat model, declaring group, supported structured condition, raw scalar cells, and row-content flag. It should return a deterministic JSON response containing either the normalized `Verdict` or a structured unsupported/elaboration/input diagnostic. It must use the existing public checked route—`FlatModel`, `elaborate`, model-derived `checkContext`, and evaluation—rather than introduce a parallel evaluator or parse the bilingual A12 DSL.

Success criteria:

1. A protocol-v1 schema represents exactly the currently supported non-repeatable flat fragment: Number/Boolean/Confirm equality and inequality, filled/not-filled, `And`/`Or`, structured absolute/parent-relative/bare paths, declared field policy, raw scalar state, and row-content eligibility.
2. A Lean executable reads one request or a deterministic stream from standard input, writes one machine-readable response to standard output, uses standard error only for process/infrastructure failures, and has documented exit behavior.
3. Unsupported operators, kinds, paths, malformed protocol data, ambiguous models, and repeatable references fail closed with stable structured diagnostics; no nearby implemented clause is used as permission to guess.
4. Process-level black-box tests lock JSON bytes or canonical semantic equality, exit status, output-channel discipline, malformed input, and at least one accepted and one unsupported request. The ordinary `lake build`, `lake test`, and trust audit remain separate gates.
5. A machine-readable supported-fragment manifest is generated from or mechanically cross-checked with the protocol constructors and names kernel behavior version `30.8.1`; it must not claim the one-star runtime fragment until that fragment has a deliberate protocol shape.
6. A concise user-facing example invokes the real executable and is regression-checked. Plain Markdown plus shared fixtures is the default; Verso is considered only if Lean-aware checked exposition materially improves the explanation.

## Implementation sequence

1. Specify the smallest protocol and response algebra in an architecture decision, including exact Number encoding, missing versus rejected raw cells, stable diagnostic tags, protocol/kernel-version mismatch, and whether the first executable processes one request or newline-delimited requests. State the nearest unsupported inputs before coding.
2. Write process-level red tests for one successful flat evaluation, one elaboration rejection, malformed JSON, unsupported protocol version, and deterministic output. Keep the tests independent of the retained-kernel evidence driver.
3. Add the closed JSON transport and pure request-to-response adapter over the existing checked evaluator. Do not add the bilingual parser, `Document` adaptation, a service, FFI, or a second semantic implementation.
4. Add the executable target and make the red process tests green. Keep IO and JSON parsing outside the trusted semantics and theorem roots, following the Cedar-style separation already used by `EvidenceMain`.
5. Add and mechanically check the supported-fragment manifest, then add the smallest checked user example. Update only the documents whose ownership triggers fire: [`ARCHITECTURE.md`](ARCHITECTURE.md), [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), [`TESTING.md`](TESTING.md), the root status/orientation surfaces, and [`EVIDENCE.md`](EVIDENCE.md) only if the external claim changes.
6. Run independent code/API, protocol/fail-closed, proof-claim, documentation, and clean-room reviews. Correct mechanism-level findings, run the full gates, commit the interpreter capsule separately, and then reassess whether the next priority is one-star protocol exposure or the next semantic mechanism.

## Deliberate exclusions from this milestone

The first process API does not add concrete EN/DE condition parsing, general DM-JSON loading, repeatable execution, `$`, `CurrentRepetition`, message interpolation, filtered-result polarity, computation, partial validation, a long-running service, FFI, or packaged release binaries. Those remain later capsules. Exposing the flat fragment first gives Kotlin, TypeScript, and CI consumers a real Lean oracle without pretending the broader semantics are ready.

## Resume procedure

Read [`../CLAUDE.md`](../CLAUDE.md), this file, and [`ARCHITECTURE.md`](ARCHITECTURE.md); inspect `git status --short` and the current diff; verify `lake build`, `lake test`, `./scripts/check-lean-trust.sh`, `git diff --check`, no `spec/` diff, and a clean visible sibling status. If the checked correlation capsule is already committed and green, begin at implementation sequence step 1. Do not reopen it or broaden the interpreter protocol to make an unsupported test convenient.
