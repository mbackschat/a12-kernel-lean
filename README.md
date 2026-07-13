# a12-kernel-lean

A clean-room **Lean 4 mechanized theory and executable specification** of the [A12 Kernel](../a12-kernel)'s validation & computation semantics.

> **Not an official A12 artifact.** A personal exploration, not affiliated with or endorsed by mgm — currently a private project, built with LLM assistance. This is a **clean-room** formal spec: it ships no kernel code and never links, calls, or transcribes the kernel (see [`CLAUDE.md`](CLAUDE.md)).

The A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: analysts declare validation rules (each phrased as the *error* condition) and computations (derived fields), which the engine evaluates against form documents. This project preserves that observed **evaluation semantics** as a versioned [mechanized theory](docs/LEAN-FORMALIZATION.md): executable as a reference oracle, empirically anchored to kernel 30.8.1, and equipped with a required proof spine plus selectively proved higher-level properties.

## Why Lean

Lean makes every captured semantic clause explicit and executable, then lets selected consequences be stated with exact hypotheses and proved for all modeled inputs. It can also preserve checked counterexamples, prove elaborations and optimizations semantics-preserving, and eventually verify real rule models against independently stated business invariants. It does **not** make a chosen clause correct merely by typechecking it or prove the real kernel universally equivalent; corpus and differential evidence remain the empirical bridge. The project charter is [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the case studies, potential, proof boundaries, and working practices are in [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).

## Status

An internal Lean reference evaluator now exists for the implemented fragments: formal checking and phase observation; typed flat Number/Boolean/Confirm equality, inequality, and presence; verdict-aware `And`/`Or`; staged absolute requiredness; checked flat model/path resolution and model-derived cell checking; ordered one-group iteration with row-local `Having`; and one captured-outer `$` correlation shape with selected presence and a separate outer guard. A checked parser-independent lowering route now resolves one group-qualified direct-child star, correlated Number or `CurrentRepetition` comparisons, explicit repeatable-group paths, field group/scope, operator-specific equality scale legality, and raw runtime cells. Its public firing route rejects row zero and duplicate candidates before evaluation. The accompanying theorems cover algebra, selector/relation agreement, filter-before-consumer footprints, declaration/policy coherence, fail-closed runtime routing, and carried structural certificates; they do not yet prove surface-to-core semantic preservation.

`lake test` replays 42 retained kernel 30.8.1 observations: 36 runtime cases and six static authoring observations. The twelve captured-outer runtime witnesses retain exact firing rows and stored `$` conditions; four new static witnesses pin all-outer rejection, unequal-scale `==` rejection, acceptance of the same unequal-scale operands under `<`, and one sibling-repeatable-group inner-reference rejection. The fourth evidence projection carries no expected codes, pins each complete seeded model file by SHA-256, binds its structured model and rule to the complete captured draft identity, and fails closed on every unmapped elaboration result, including `missingOuter`. Earlier evidence corrected bare-name resolution and exposed one a12-dmkits interpreter disagreement on a malformed uncorrelated filter. [`docs/EVIDENCE.md`](docs/EVIDENCE.md) owns the exact claim boundary.

The first product-shaped Lean interpreter boundary is now available as the `a12-kernel-reference` executable. Its versioned normalized [JSON protocol](docs/PROTOCOL.md) exposes exactly the checked non-repeatable flat slice: Number/Boolean/Confirm equality, inequality, and presence; `And`/`Or`; structured absolute, parent-relative, and bare paths; model-derived raw checking; the row-content gate; stable fail-closed diagnostics; and a generated [support manifest](reference/supported-fragment-v1.json). It accepts neither the bilingual concrete DSL nor general DM-JSON, and it does not yet expose the internally implemented iteration/correlation fragments, `Document` adaptation, computation, partial validation, or messages.

## Build

Needs **Lean 4.31.0** (via [`elan`](https://github.com/leanprover/elan); pinned in [`lean-toolchain`](lean-toolchain)). There are no external Lake package dependencies; native executables still include pinned Lean toolchain/runtime components, whose release implications are tracked in [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md).

```sh
lake build
lake test
lake exe checkReferenceProcess
./scripts/check-lean-trust.sh
```

## Try the reference CLI

The committed files under [`examples/reference-cli/`](examples/reference-cli/) are runnable sample data and regression fixtures. This example demonstrates the kernel's comparison-local empty-Number substitution: omitting the declared Number cell makes the equality with zero fire with omission polarity.

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

Inspect the exact supported boundary with:

```sh
lake exe a12-kernel-reference --manifest
```

See [`docs/PROTOCOL.md`](docs/PROTOCOL.md) for the request/response contract, exit behavior, all sample scenarios, and deliberate exclusions.

## Design and sources

- [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md) — the project charter: purpose, ecosystem role, deliverables, non-goals, and success criteria.
- [`docs/PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md) — the proposed compatibility-kit product boundary, public claim, and staged progression.
- [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md) — production artifact qualification, reproducibility, packaging, signing, measured size work, and release blockers.
- [`docs/README.md`](docs/README.md) — the documentation index and ownership map.
- [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) — live clause-level Lean coverage, proof, boundary, and external-evidence state.
- [`docs/LEAN-FINDINGS.md`](docs/LEAN-FINDINGS.md) — durable numbered formalization and research findings, including the `$` correlation treatment.
- [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md) — Lean's role and potential, audited project studies, proof/trust boundaries, theorem opportunities, and best practices.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — the concrete Lean encoding decisions and rejected alternatives.
- [`docs/PROTOCOL.md`](docs/PROTOCOL.md) — the normalized reference process, JSON schema, diagnostics, support manifest, and checked sample data.
- [`docs/TESTING.md`](docs/TESTING.md) — the Lean red/green method, concrete conformance harness, trusted-proof audit, kernel replay, and final verification gate.
- [`docs/DOC-DISCIPLINE.md`](docs/DOC-DISCIPLINE.md) — where findings, structure, status, and plans belong.
- [`spec/`](spec/) — the distilled, language-neutral specification; start at [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md).
- [`docs/SOURCES.md`](docs/SOURCES.md) — the drill chain from each semantic clause to its evidence.
- [`../a12-kernel`](../a12-kernel) — the real engine, the behavioural **source of truth** (EUPL-1.2 / commercial).
- [a12-dmkits (local `a12-rulekit/` checkout)](../a12-rulekit) — a peer clean-room reimplementation, reusable conformance corpus, semantics docs, and the dmtool-release public distribution.

This is a **clean-room** reimplementation: it never links, calls, or transcribes the kernel; it reproduces observed behaviour in original code and locks it with tests. See [`CLAUDE.md`](CLAUDE.md) for the full source-of-truth hierarchy and the licensing boundary.

## License

MIT © 2026 mbackschat — see [`LICENSE`](LICENSE). This project's source ships no kernel code, so it carries no copyleft entanglement (the same basis as [a12-dmkits](../a12-rulekit)' MIT source).
