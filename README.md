# a12-kernel-lean

A clean-room **Lean 4 executable specification** of the [A12 Kernel](../a12-kernel)'s validation & computation semantics.

The A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: analysts declare validation rules (each phrased as the *error* condition) and computations (derived fields), which the engine evaluates against form documents. This project reimplements that **evaluation semantics** in Lean 4 as a faithful, `#eval`-able, property-testable specification — behaviour first, proofs a later optional layer.

## Why Lean

Two things Lean gives that more tests cannot: an **executable specification** you can `#eval` (documentation that cannot drift), and **machine-checked proofs** of universal properties — monotonicity of suppression, determinism, partial validation's one-directional guarantee — that hold for *all* inputs, not the finitely many a test samples. It also serves as an independent **differential oracle** against the engine and the Kotlin interpreter. It does *not* prove the real kernel correct; equivalence to kernel 30.8.1 stays empirical. The full argument is in [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md).

## Status

Kickstart skeleton. The language-neutral semantics are fully written under [`spec/`](spec/); the Lean encoding has its core types in place ([`A12Kernel/Core.lean`](A12Kernel/Core.lean)) and builds green. Operator clauses are filled in stage by stage per [`spec/13-lean-encoding-guide.md`](spec/13-lean-encoding-guide.md) §3.

## Build

Needs **Lean 4.31.0** (via [`elan`](https://github.com/leanprover/elan); pinned in [`lean-toolchain`](lean-toolchain)). No external dependencies.

```sh
lake build
```

## Where the semantics come from

- [`spec/`](spec/) — the distilled, language-neutral specification (start at [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md)).
- [`../a12-kernel`](../a12-kernel) — the real engine, the behavioural **source of truth** (EUPL-1.2 / commercial).
- [`../a12-rulekit`](../a12-rulekit) — a peer clean-room reimplementation, a reusable conformance corpus, and semantics docs.

This is a **clean-room** reimplementation: it never links, calls, or transcribes the kernel; it reproduces observed behaviour in original code and locks it with tests. See [`CLAUDE.md`](CLAUDE.md) for the full source-of-truth hierarchy and the licensing boundary.
