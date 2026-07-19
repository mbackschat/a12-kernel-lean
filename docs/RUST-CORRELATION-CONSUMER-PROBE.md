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

The phase-specific allowlist overrides the broader handover list, links, Rust playbook, Lean commands, and candidate-runner instructions inside the correlation kit. The cold implementer reads the kit as semantic material but does not follow a link or command that leaves this allowlist.

## Operator preflight

Immediately before starting the external session, the owner runs the following from `a12-kernel-lean`. Exit status zero confirms that every allowed input still has exactly its baseline bytes; a nonzero result blocks the probe until this work order is deliberately repinned.

```sh
baseline=2bb2d232cd62367d6aa92f64b6b0c1dfc591a830
git diff --quiet "$baseline" -- \
  docs/IMPLEMENTER-KIT-CORRELATION.md \
  reference/single-group-correlation-v2.conformance.json \
  examples/reference-cli/correlation-direction.{request,response}.json \
  examples/reference-cli/correlation-self-included.{request,response}.json \
  examples/reference-cli/correlation-self-excluded-distinct.{request,response}.json \
  examples/reference-cli/correlation-self-excluded-duplicate.{request,response}.json \
  examples/reference-cli/correlation-consumer-all-valid.{request,response}.json \
  examples/reference-cli/correlation-consumer-first-malformed.{request,response}.json \
  examples/reference-cli/correlation-consumer-second-malformed.{request,response}.json \
  examples/reference-cli/correlation-filter-empty-equals-zero.{request,response}.json \
  examples/reference-cli/correlation-filter-malformed-local.{request,response}.json \
  examples/reference-cli/correlation-number-not-equal.{request,response}.json \
  examples/reference-cli/correlation-repetition-equal.{request,response}.json \
  examples/reference-cli/correlation-repetition-less-than.{request,response}.json
```

The owner also confirms that the Lean worktree is clean, records the successful preflight in the external repository's initial README or agent instructions, and delivers only Prompt 1. The implementer does not use Git history to repeat this operator check.

## Prompt 1 — cold readback only

Deliver this prompt first. Do not reveal either later prompt before the readback commit is frozen.

```text
You are performing the cold-readback phase of a consumer probe in a brand-new Rust repository. The purpose is to test knowledge transport from a12-kernel-lean, not to rediscover A12 behavior. The owner has already verified that the allowed source bytes match baseline 2bb2d232cd62367d6aa92f64b6b0c1dfc591a830.

Use the existing Homebrew Rust toolchain. Do not install or add dependencies. Use Rust's standard library only. Work only in this new repository; treat every other repository as read-only.

The only semantic material you may consult is in the sibling a12-kernel-lean checkout:

- docs/IMPLEMENTER-KIT-CORRELATION.md
- reference/single-group-correlation-v2.conformance.json
- the request and expected-response files referenced by its first twelve cases, correlation-direction through correlation-repetition-less-than

This phase-specific allowlist overrides the kit's broader handover list, links, playbook, commands, and runner instructions. Do not follow its links or run its Lean/reference commands. Do not inspect the A12 kernel, a12-dmkits, Lean source or executable, unlisted a12-kernel-lean files, the historical Rust experiment, web sources, Git history, or prior conversation. If the allowlist does not decide something required, record the exact gap and stop. Do not infer nearby behavior.

Phase 1 is the already-resolved runtime core only. Exclude JSON decoding, model/path validation and lowering, public diagnostics, CLI/process behavior, the suite's four static-authoring cases, general exact decimals, and every A12 feature outside the named correlation runtime. The admitted numeric inputs are the integer-valued cells exercised by the twelve retained runtime cases. State this restriction in code and reports.

Create reports/COLD-READBACK.md without writing implementation source. It must state:

1. the capability and assurance boundary;
2. the recovered types and decision procedure;
3. evaluation order and failure/unknown propagation;
4. the distinctions that the Rust representation must preserve;
5. the twelve case predictions;
6. laws, checked non-laws, and exclusions;
7. ambiguities or missing rules;
8. every consulted file;
9. whether implementation is possible without additional A12 research.

Commit the readback separately, leave the worktree clean, report the commit identity and any blocker, and stop. Do not begin implementation.
```

The owner ferries the readback here for assessment. Prompt 2 is delivered only if the report demonstrates the intended scope, contains no prohibited research, and identifies no blocking ambiguity.

## Prompt 2 — natural implementation

```text
Proceed from the accepted cold-readback commit. The source allowlist, isolation rules, runtime-only scope, integer fixture profile, and no-dependency rule from Prompt 1 remain unchanged. Do not consult any new source.

Implement an idiomatic pure Rust library for the resolved runtime described by your committed readback. Use closed enums and exhaustive matches for semantic alternatives. Implement one generic evaluator; production code must not branch on fixture IDs, expected firing rows, or case-specific constants.

Manually project the first twelve JSON fixtures into native Rust test builders. Copy only their already-resolved candidate list, cell states, lowered runtime condition, guard/consumer field identities, and expected firing rows. Do not implement or silently exercise JSON decoding, response envelopes, model/path validation, or lowering. Make the manual projection visible in test setup and keep it outside production evaluation.

Encode all twelve projections as tests against the same evaluator. Add finite property-style tests for the applicable laws listed by the kit and regressions for its runtime checked non-laws, within the declared integer profile.

Run cargo fmt --check and cargo test until green, then commit the naturally green implementation and tests before any mutation exercise. Write reports/NATURAL-IMPLEMENTATION-REPORT.md with that commit identity, the exact commands, tool versions, result, consulted-file inventory, supported profile, explicit exclusions, and unresolved questions; commit the report separately.

Leave the worktree clean and stop. Return the cold-readback, natural-implementation, and natural-report commit identities. Do not perform mutations, add JSON or a CLI, consult Lean, or run the candidate runner.
```

The owner ferries the exact natural repository state here. Project-side review must inspect the natural commit and tests—not only the report—and confirm generic evaluation, absence of fixture-ID branching, correct manual projection boundaries, isolation compliance, and a clean worktree before Prompt 3 is delivered.

## Prompt 3 — mutation sensitivity

```text
Proceed from the reviewed and frozen natural implementation. Consult no new semantic source and change no scope. Before editing production code, record your predicted failing cases for each of the following defects:

1. resolve `Outer` Number references from the current inner row;
2. let an unselected malformed consumer poison the whole consumer scan;
3. exclude the outer row implicitly from every inner scan.

For each mutation, record the predicted failing cases before running tests, make the smallest change, run the complete test gate, record the actual failures, restore the exact natural implementation, and rerun green. Do not commit mutated production code. Write reports/MUTATION-SENSITIVITY.md and commit only that restored-state report.

Stop after mutation sensitivity. Do not add JSON, Serde, a CLI, a protocol adapter, a Lean differential, a candidate-runner connection, a new harness, or qualification machinery. Return the cold-readback, natural-implementation, natural-report, and mutation-report commit identities, repository status, test results, mutation outcomes, unresolved questions, and whether any prohibited A12 research was needed.
```

## Acceptance and stop conditions

The probe is accepted only after project-side inspection confirms that one generic evaluator reproduces the twelve native projections without fixture-ID branching, the focused laws hold over its declared finite domains, every mutation is detected in the predicted semantic neighborhood, manual test projection did not become hidden decoding or lowering, the final worktree is clean, and the exact source plus reports confirm that no external A12 research was needed. Reports alone are not acceptance evidence.

The phase fails usefully if the implementer needs an unlisted semantic source, cannot distinguish a required state, or finds that the kit and fixtures disagree. That result comes back here as a handover defect; it does not authorize kernel archaeology downstream.

After the complete runtime probe is accepted, the owner decides whether to start phase 2. Phase 2 would add the existing normalized JSON/process contract, checked authoring boundary, all sixteen suite cases, and the already-present `checkCandidateConformance` runner. It must reuse those current mechanisms and may require an explicitly approved Rust JSON dependency; it must not create another protocol or qualification harness.
