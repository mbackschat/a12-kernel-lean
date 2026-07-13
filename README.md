# a12-kernel-lean

A clean-room **Lean 4 mechanized theory and executable specification** of the [A12 Kernel](../a12-kernel)'s validation & computation semantics.

> **Not an official A12 artifact.** A personal exploration, not affiliated with or endorsed by mgm — currently a private project, built with LLM assistance. This is a **clean-room** formal spec: it ships no kernel code and never links, calls, or transcribes the kernel (see [`CLAUDE.md`](CLAUDE.md)).

The A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: analysts declare validation rules (each phrased as the *error* condition) and computations (derived fields), which the engine evaluates against form documents. This project preserves that observed **evaluation semantics** as a versioned [mechanized theory](docs/LEAN-FORMALIZATION.md): executable as a reference oracle, empirically anchored to kernel 30.8.1, and equipped with a required proof spine plus selectively proved higher-level properties.

## Why Lean

Lean makes every captured semantic clause explicit and executable, then lets selected consequences be stated with exact hypotheses and proved for all modeled inputs. It can also preserve checked counterexamples, prove elaborations and optimizations semantics-preserving, and eventually verify real rule models against independently stated business invariants. It does **not** make a chosen clause correct merely by typechecking it or prove the real kernel universally equivalent; corpus and differential evidence remain the empirical bridge. The project charter is [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the case studies, potential, proof boundaries, and working practices are in [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).

## Status

The first proof-bearing semantic capsule and the first checked-elaboration slice are implemented internally. They cover base formal checking and phase observation; typed flat equality/inequality for Number, Boolean, and Confirm; presence predicates; the full-validation row gate; verdict-aware `And`/`Or`; scale-19 `HALF_UP`; the staged absolute/non-repeatable required-field transformation; checked model/path resolution for a deliberately small non-repeatable path subset; and model-derived formal checking. The default build includes executable conformance locks and the trusted proof root. A separate `lake test` driver replays 11 retained kernel 30.8.1 observations through a focused typed projection; [`docs/EVIDENCE.md`](docs/EVIDENCE.md) states exactly what this establishes and which required/path witnesses remain open. Coverage is deliberately partial and recorded clause by clause in [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md); the full path language, repetition, ordering/arithmetic, computation, and partial validation have not landed.

## Build

Needs **Lean 4.31.0** (via [`elan`](https://github.com/leanprover/elan); pinned in [`lean-toolchain`](lean-toolchain)). No external dependencies.

```sh
lake build
lake test
./scripts/check-lean-trust.sh
```

## Design and sources

- [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md) — the project charter: purpose, ecosystem role, deliverables, non-goals, and success criteria.
- [`docs/README.md`](docs/README.md) — the documentation index and ownership map.
- [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) — live clause-level Lean coverage, proof, boundary, and external-evidence state.
- [`docs/LEAN-FINDINGS.md`](docs/LEAN-FINDINGS.md) — durable numbered formalization and research findings, including the `$` correlation treatment.
- [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md) — Lean's role and potential, audited project studies, proof/trust boundaries, theorem opportunities, and best practices.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — the concrete Lean encoding decisions and rejected alternatives.
- [`docs/DOC-DISCIPLINE.md`](docs/DOC-DISCIPLINE.md) — where findings, structure, status, and plans belong.
- [`spec/`](spec/) — the distilled, language-neutral specification; start at [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md).
- [`docs/SOURCES.md`](docs/SOURCES.md) — the drill chain from each semantic clause to its evidence.
- [`../a12-kernel`](../a12-kernel) — the real engine, the behavioural **source of truth** (EUPL-1.2 / commercial).
- [a12-dmkits (local `a12-rulekit/` checkout)](../a12-rulekit) — a peer clean-room reimplementation, reusable conformance corpus, semantics docs, and the dmtool-release public distribution.

This is a **clean-room** reimplementation: it never links, calls, or transcribes the kernel; it reproduces observed behaviour in original code and locks it with tests. See [`CLAUDE.md`](CLAUDE.md) for the full source-of-truth hierarchy and the licensing boundary.

## License

MIT © 2026 mbackschat — see [`LICENSE`](LICENSE). This project's source ships no kernel code, so it carries no copyleft entanglement (the same basis as [a12-dmkits](../a12-rulekit)' MIT source).
