# Fresh Rust correlation consumer probe

**Status:** prepared in `a12-kernel-lean`; awaiting an owner-started or owner-authorized external repository and session. Nothing in this document authorizes changes outside this repository.

## Purpose and recommended boundary

This experiment tests whether the current language-neutral handover transports a non-trivial A12 decision procedure into an independent implementation without renewed kernel or a12-dmkits research. It deliberately starts from a fresh Rust repository; the retired 0.2.0/V1 Rust source, fixtures, reports, and architecture are historical controls and are not implementation inputs.

The recommended capability is the resolved runtime core of `single-group-correlation-v2`. It is a better executable transport test than the current Date/DateTime checkpoint because it already has a maintained language-neutral kit, twelve retained kernel runtime observations, separating fixtures, proved laws and checked non-laws, and an existing optional candidate runner. No new Lean protocol, fixture format, evidence route, or harness is needed.

The natural phase stops before JSON decoding, model/path elaboration, public diagnostics, process integration, and the four static-authoring cases. Its numeric profile is exactly the integer-valued retained runtime fixtures; broader exact-decimal support is not inferred. A successful result is a finite correlation-runtime consumer probe, not a general A12 interpreter or current-suite qualification.

Semantic source baseline: `2bb2d232cd62367d6aa92f64b6b0c1dfc591a830`. Later documentation-only descendants may be used only if the allowed semantic material below is unchanged from that baseline.

## Allowed source material

The external implementer may read only these files from this repository during the natural phase:

- [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md);
- [`single-group-correlation-v2.conformance.json`](../reference/single-group-correlation-v2.conformance.json);
- the request and expected-response files referenced by the first twelve runtime cases in that suite, from `correlation-direction` through `correlation-repetition-less-than`.

The implementer may also read the new repository's own `AGENTS.md`, `README.md`, source, tests, and reports. It must not inspect:

- the A12 kernel or a12-dmkits;
- any sibling repository other than the allowlisted files above;
- Lean source, the Lean executable, or unlisted project documentation during the natural phase;
- the historical Rust repository or its Git objects;
- web sources, private conversation history, or Git history as semantic input.

If the allowed material does not decide a required behavior, record the exact question and stop rather than researching or guessing.

## Paste-ready prompt for the external session

```text
You are implementing a cold consumer probe in a brand-new Rust repository. The purpose is to test knowledge transport from a12-kernel-lean, not to rediscover A12 behavior.

Use the existing Homebrew Rust toolchain. Do not install or add dependencies. Use Rust's standard library only. Work only in this new repository; treat every other repository as read-only.

The only semantic material you may consult is in the sibling a12-kernel-lean checkout:

- docs/IMPLEMENTER-KIT-CORRELATION.md
- reference/single-group-correlation-v2.conformance.json
- the request and expected-response files referenced by its first twelve cases, correlation-direction through correlation-repetition-less-than

The semantic source baseline is 2bb2d232cd62367d6aa92f64b6b0c1dfc591a830. Do not inspect the A12 kernel, a12-dmkits, Lean source or executable, unlisted a12-kernel-lean files, the historical Rust experiment, web sources, Git history, or prior conversation. If the allowlist does not decide something required, record the exact gap and stop. Do not infer nearby behavior.

Phase 1 is the already-resolved runtime core only. Exclude JSON decoding, model/path validation and lowering, public diagnostics, CLI/process behavior, the suite's four static-authoring cases, general exact decimals, and every A12 feature outside the named correlation runtime. The admitted numeric inputs are the integer-valued cells exercised by the twelve retained runtime cases. State this restriction in code and reports.

First create reports/COLD-READBACK.md before implementation. It must state:

1. the capability and assurance boundary;
2. the recovered types and decision procedure;
3. evaluation order and failure/unknown propagation;
4. the distinctions that the Rust representation must preserve;
5. the twelve case predictions;
6. laws, checked non-laws, and exclusions;
7. ambiguities or missing rules;
8. every consulted file;
9. whether implementation is possible without additional A12 research.

Commit that readback separately.

Then implement an idiomatic pure Rust library with closed enums or equivalent sum types for raw cell state, reference origin, numeric/repetition comparisons, strong-Kleene truth, `Having`, the captured inner/outer frame, and the resolved runtime rule/context. Keep selection separate from consumer observation. Preserve candidate order, explicit self-inclusion, local malformed filter behavior, filter-before-consumer observation, empty Number substitution as comparison zero, and definitely-true-only selection/firing.

Encode all twelve retained runtime fixtures as native Rust tests against one generic evaluator; do not write one function per fixture or embed expected results in production code. Add focused property-style tests, over finite generated inputs where useful, for outer-reference stability, inner-reference locality, candidate-order preservation, definitely-true-only selection, and no implicit self-exclusion.

Run cargo fmt --check and cargo test until green, then commit the naturally green implementation and tests before any mutation exercise. Write reports/NATURAL-IMPLEMENTATION-REPORT.md with that commit identity, the exact commands, tool versions, result, consulted-file inventory, supported profile, explicit exclusions, and unresolved questions; commit the report separately.

After the natural commit is frozen, predict and apply these defects one at a time:

1. resolve `Outer` Number references from the current inner row;
2. let an unselected malformed consumer poison the whole consumer scan;
3. exclude the outer row implicitly from every inner scan.

For each mutation, record the predicted failing cases before running tests, make the smallest change, run the complete test gate, record the actual failures, restore the exact natural implementation, and rerun green. Do not commit mutated production code. Write reports/MUTATION-SENSITIVITY.md and commit only that restored-state report.

Stop after mutation sensitivity. Do not add JSON, Serde, a CLI, a protocol adapter, a Lean differential, a candidate-runner connection, a new harness, or qualification machinery. Return the cold-readback, natural-implementation, natural-report, and mutation-report commit identities, repository status, test results, mutation outcomes, unresolved questions, and whether any prohibited A12 research was needed.
```

## Acceptance and stop conditions

The natural phase succeeds only if one generic evaluator reproduces the twelve runtime cases, the focused laws hold over its declared finite domains, every mutation is detected in the predicted semantic neighborhood, the final worktree is clean, and the report confirms that no external A12 research was needed.

The phase fails usefully if the implementer needs an unlisted semantic source, cannot distinguish a required state, or finds that the kit and fixtures disagree. That result comes back here as a handover defect; it does not authorize kernel archaeology downstream.

After the natural result is frozen and ferried back, the owner decides whether to start phase 2. Phase 2 would add the existing normalized JSON/process contract, checked authoring boundary, all sixteen suite cases, and the already-present `checkCandidateConformance` runner. It must reuse those current mechanisms and may require an explicitly approved Rust JSON dependency; it must not create another protocol or qualification harness.
