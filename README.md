# a12-kernel-lean

**Executable, proof-bearing semantics for A12 validation and computation in Lean 4.**

`a12-kernel-lean` is a clean-room mechanized theory of the A12 Kernel's observable validation-and-computation semantics. It turns behavior that is otherwise scattered across runtime rules, edge cases, and experiments into a language-neutral specification, executable Lean definitions, checked examples, and selected proofs.

> **Not an official A12 artifact.** This is a personal exploration, built with LLM assistance and not affiliated with or endorsed by mgm technology partners. It ships no kernel code and never links, calls, or transcribes the kernel.

## Why this project exists

The A12 Kernel evaluates business rules over complex form documents. Its semantics include more than ordinary true and false: empty values, invalid values, omission polarity, partial validation, repeatable addressing, filtered operands, ordered computations, temporal behavior, and message construction can all change observable results.

Those distinctions matter to anyone building an independent evaluator, importer, compiler, analyzer, rule-refactoring tool, verifier, or explanation system. Without a shared semantics, every consumer must rediscover the same behavior and can easily preserve the wrong thing.

The primary target is eventual **100% semantic conformance with A12 Kernel 30.8.1** for its complete observable validation-and-computation language and required static legality. The project pursues that target through:

- a canonical, language-neutral semantic account under [`spec/`](spec/);
- executable Lean definitions that serve as a precise reference;
- useful laws and explicit counterexamples with exact assumptions;
- retained differential observations that calibrate selected families against the real kernel;
- concrete consumer probes that test whether the representation preserves the information downstream tools actually need.

Lean does not make a semantic clause correct merely because it typechecks, and a proof about the Lean theory is not a universal proof about the external kernel. Internal proof, empirical kernel correspondence, and consumer adequacy are tracked as separate claims.

## What is in this repository

| Path | Purpose |
|---|---|
| [`spec/`](spec/) | Canonical prose semantics and the language-neutral bridge to a12-dmkits |
| [`A12Kernel/Semantics/`](A12Kernel/Semantics/) | Executable semantic mechanisms |
| [`A12Kernel/Elaboration/`](A12Kernel/Elaboration/) | Checked model and rule construction |
| [`A12Kernel/Proofs/`](A12Kernel/Proofs/) | Laws, preservation results, and checked non-laws |
| [`A12Kernel/Conformance/`](A12Kernel/Conformance/) | Focused executable separating cases |
| [`A12Kernel/Evidence/`](A12Kernel/Evidence/) and [`evidence/`](evidence/) | Typed projections and compact retained kernel observations |
| [`A12Kernel/Reference/`](A12Kernel/Reference/) and [`reference/`](reference/) | Normalized reference process, manifest, and conformance suites |
| [`examples/reference-cli/`](examples/reference-cli/) | Runnable requests for the reference CLI |
| [`docs/`](docs/) | Architecture, provenance, coverage, testing, consumer guidance, and active planning |

The theory covers substantially more than the public reference process. Public support remains deliberately fail-closed: an internal semantic capsule is not advertised as an integration capability until its protocol, evidence, and consumer boundary are explicit.

## How assurance works

```text
kernel behavior and source knowledge
                 │
                 ▼
       language-neutral spec
                 │
                 ▼
      executable Lean semantics
          │              │
          ▼              ▼
   proofs and non-laws   retained observations
          │              │
          └──────┬───────┘
                 ▼
     capability-level consumer probe
                 │
                 ▼
   optional purpose-specific shipment
```

The kernel remains the behavioral oracle. The specification and Lean theory state the project's chosen account, proofs establish consequences of that account, and retained observations provide finite empirical correspondence. Consumer probes then check that a closed capability transports enough knowledge for a named task without growing a second implementation inside this repository.

The project considers ten consumer tasks: **Execute, Translate, Transform, Compile, Analyze, Verify, Synthesize, Qualify, Explain, and Govern**. The [`use-case guide`](docs/USE-CASES.md) explains each task and the role Lean can—and cannot—play.

## Current status

This is an active formal-semantics project, not a complete A12 interpreter or a qualified production release.

<!-- github-publish-stats:start -->
**Verified at publication:** **1,314 trusted theorem roots**, **27,184 audited declarations**, and **250 trusted modules** in the mechanized theory.
<!-- github-publish-stats:end -->

- The internal theory already covers substantial validation, computation, numeric, String, Enumeration, Date/DateTime, repeatable, addressing, message, checked-document, and dependency behavior, with coverage varying independently across execution, proof, kernel evidence, public exposure, and consumer qualification.
- One immutable, model-certified checked document now owns declared topology and address resolution. A shared addressed core resolves checked Number, String, and stored/category Enumeration operands across independent and nested repeatable groups, preserves hierarchical extent and positional relevance, and keeps structural addressing failures distinct from semantic `UNKNOWN`; typed wrappers retain their exact declaration and projection certificates.
- Ordered checked Number and token value-list evaluation plus Number aggregates, token distinct count, and projection-bearing token value count consume that same resolved representation with their distinct stopping and fold rules; stored access and multiple named categories on one Enumeration remain distinct exact references rather than a flattened display value.
- Large semantic families are decomposed into import-only compatibility roots and focused elaboration, evaluation, proof, and conformance modules. This keeps ordinary source below the project’s 1,000-nonblank-line ceiling and lets red/green work rebuild only the affected family.
- The public reference process advertises reference semantics **0.3.0** over protocol **1**. It currently exposes checked flat validation and one single-group correlation capability and rejects unsupported constructs explicitly.
- Compact retained observations calibrate selected semantic families; other internally closed families remain honestly marked `external evidence pending`.
- The immediate hard frontier is completing that canonical addressed operand stream across cross-level, RNU, group, and whole-rule repeatable routes. Whole-document computation scheduling remains gated behind this boundary and its source audit.

[`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) is the exact coverage index. [`docs/PLAN.md`](docs/PLAN.md) records the active capsule and next frontier, while [`docs/SEMANTICS-GAPS.md`](docs/SEMANTICS-GAPS.md) owns unresolved semantic obligations.

## Quick start

The project is pinned to **Lean 4.31.0** in [`lean-toolchain`](lean-toolchain) and uses Lake 5.0. Install Lean through [`elan`](https://github.com/leanprover/elan); there are no external Lake package dependencies.

Build the theory, run the retained evidence replay, and audit the proof/runtime trust boundary:

```sh
lake build
lake test
./scripts/check-lean-trust.sh
```

During development, build the narrowest owning module—for example `lake build A12Kernel.Conformance.NumericValidation.Comparison`—before paying for the integrated gate.

Run the complete reference-process checks:

```sh
lake exe checkReferenceProcess
lake exe checkBoundedProcess
```

[`docs/TESTING.md`](docs/TESTING.md) defines the red/green capsule workflow, focused commands, proportional gates, and final verification ladder.

## Try the reference CLI

This request demonstrates comparison-local empty-Number substitution: omitting the declared Number cell makes equality with zero fire with omission polarity.

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

The semantic response is:

```json
{
  "kernelBehaviorVersion": "30.8.1",
  "outcome": "ok",
  "protocolVersion": 1,
  "verdict": {
    "polarity": "omission",
    "tag": "fired"
  }
}
```

Inspect the exact supported boundary of the executable you are running:

```sh
lake exe a12-kernel-reference --manifest
```

See [`docs/PROTOCOL.md`](docs/PROTOCOL.md) for the normalized request/response contract and deliberate exclusions. The [flat-validation](docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [single-group correlation](docs/IMPLEMENTER-KIT-CORRELATION.md) kits provide language-neutral algorithms, worked traces, evidence limits, and independent-consumer guidance for the two public capabilities.

## Documentation

| If you want to… | Start here |
|---|---|
| Read the semantic account | [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md) |
| Understand the project charter and proof boundaries | [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md) and [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md) |
| See exact implementation and evidence coverage | [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) |
| Explore consumer tasks and potential | [`docs/USE-CASES.md`](docs/USE-CASES.md) |
| Integrate an independent evaluator | [`docs/IMPLEMENTER-GUIDE.md`](docs/IMPLEMENTER-GUIDE.md) |
| Trace a clause back to its evidence | [`docs/SOURCES.md`](docs/SOURCES.md) |
| Resume current semantic work | [`docs/PLAN.md`](docs/PLAN.md) |
| Find any other project document | [`docs/README.md`](docs/README.md) |

## Development

Semantic changes use red/green TDD and close as small executable capsules with focused conformance cases, payoff-selected proofs, honest evidence status, and minimum documentation updates. Read [`CLAUDE.md`](CLAUDE.md) for the project rules and [`docs/TESTING.md`](docs/TESTING.md) for the workflow before contributing.

The clean-room boundary is a licensing constraint: learn behavior from the kernel, then write original Lean and independent semantic prose. Never link, call, ship, or transcribe kernel implementation code. Every behavioral change to [`spec/`](spec/) must be reconciled through the [`a12-dmkits spec-sync ledger`](docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).

Immediately before publishing committed source to GitHub, refresh the README's verified theory statistics:

```sh
./scripts/prepare-github-publish.sh --update
```

Review and commit any resulting README change, then push explicitly. The script runs the trust audit and updates only the marked statistics line; it never commits, tags, pushes, publishes a release, or distributes binaries. GitHub CI runs its `--check` mode so published statistics cannot silently drift from the trusted Lean closure.

## License

The project-authored source and documentation are MIT-licensed — see [`LICENSE`](LICENSE).

Native executables also incorporate separately licensed Lean toolchain and runtime components, including GMP in the current official toolchain. Those dependencies do not change the project's MIT source license, but distributing binaries requires their license obligations to be satisfied; [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md#dependency-approval-and-bundled-runtime-licensing) owns that release gate.
