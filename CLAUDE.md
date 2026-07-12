# CLAUDE.md

Guidance for working in **a12-kernel-lean** — a clean-room **Lean 4 executable specification** of the A12 kernel's validation & computation semantics.

## What this is

A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: business analysts declare **validation rules** (each states the *error* condition — true ⇒ the data is invalid) and **computations** (derived fields) in a bilingual EN/DE DSL, and the engine evaluates them against form *Documents*. This project reimplements that **evaluation semantics** in Lean 4 as a faithful, `#eval`-able, property-testable specification. The stance is *semantics-first*: an executable spec whose behaviour matches the engine, with proofs a later, optional layer this design tries not to obstruct.

The language-neutral semantics live in [`spec/`](spec/) — start at [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md) (the map: taxonomy, invariants, core types, glossary) and follow the numbered deep-dives; the concrete Lean plan is [`spec/13-lean-encoding-guide.md`](spec/13-lean-encoding-guide.md). The `spec/` is self-contained by design — the sibling repos below are the **authority and knowledge layer** beneath it, not a substitute for reading it.

## ⚠️ HARD RULE — clean-room reimplementation; never link, call, or transcribe the kernel

This is a **licensing boundary, not a preference**, and it is the same rule a12-rulekit's interpreter already operates under. The A12 kernel is **EUPL-1.2 (copyleft) OR commercial**. A work that *links, ships, or calls* the kernel is a combined work the EUPL copyleft reaches; a **line-by-line transliteration of its source** is a copyright derivative that re-attracts the EUPL. Therefore:

- **Never** link, call, or ship the kernel (or a JS-kernel binding) from this project, and **never** transcribe a kernel *source expression* into Lean.
- **Do** read the kernel — and a12-rulekit's interpreter — to *learn the exact behaviour*, then write **original** Lean and lock it against that behaviour with property/differential tests. Reading the source to *understand* (and to find surprising special cases) is encouraged; the *fix* is never a transliteration. **Copy the mechanism, never the expression.**

Because this project's source ships no kernel code, it can carry a permissive license of the owner's choice — a12-rulekit's source is MIT for exactly this reason (see [`../a12-rulekit/docs/LICENSING.md`](../a12-rulekit/docs/LICENSING.md)). No `LICENSE` is committed yet: that is the owner's call; MIT would match the A12 OSS family.

## ⚠️ HARD RULE — no machine-specific data in committed files

No absolute home paths, usernames, hostnames, emails, or credentials in source, docs, or commit messages. Reference the sibling repos by **relative path** (`../a12-kernel`, `../a12-rulekit`); this project assumes they are checked out as adjacent directories under a shared parent, as the rest of the A12 OSS family does.

## The source-of-truth hierarchy

Three layers, in order of authority for a semantic question:

1. **`spec/` (this repo) — the primary working reference.** The distilled, language-neutral semantics with Lean modelling notes. Its `§n` taxonomy mirrors a12-rulekit's (below), so section numbers line up across repos.
2. **`../a12-kernel` — the ultimate source of truth (the behavioural oracle).** The real engine. When `spec/` and the engine disagree, **the engine wins and the spec is corrected**. Use it to *learn* and to *differentially test* — always under the clean-room rule above.
3. **`../a12-rulekit` (a12-dmkits) — the knowledge source.** A peer **clean-room** reimplementation of the same semantics (in Kotlin), a reusable test corpus, semantics ledgers, and an evaluation harness.

### Entry points in `../a12-kernel` (the oracle)

- [`../a12-kernel/documentation/_merged/kernel-ba.md`](../a12-kernel/documentation/_merged/kernel-ba.md) — the **canonical validation-language guide** (operators, predicates, arithmetic, dates, iteration, computations). The single best behaviour reference; worked examples throughout.
- [`../a12-kernel/documentation/_merged/kernel-dev.md`](../a12-kernel/documentation/_merged/kernel-dev.md) — developer docs: custom conditions, custom field types, the public-API contract.
- [`../a12-kernel/KERNEL-GRAMMAR.md`](../a12-kernel/KERNEL-GRAMMAR.md) and [`../a12-kernel/KERNEL-USE.md`](../a12-kernel/KERNEL-USE.md) — DSL grammar gotchas and the consumer call sequence.
- Source, for *understanding* behaviour only (never to transcribe): `kernel-tool/*` (parse → codegen), `kernel-md/*` (model/document API), `kernel-rt/*` (runtime).

### Entry points in `../a12-rulekit` (the knowledge source)

- [`../a12-rulekit/docs/KERNEL-SEMANTICS.md`](../a12-rulekit/docs/KERNEL-SEMANTICS.md) — the canonical kernel-truth prose in the **same 14-section `§n` taxonomy** `spec/` uses, and [`../a12-rulekit/docs/KERNEL-FINDINGS.md`](../a12-rulekit/docs/KERNEL-FINDINGS.md) — experiment-verified behaviours, each test-locked.
- [`../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md`](../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md) + [`../a12-rulekit/corpus/`](../a12-rulekit/corpus/) — **portable, engine-verified JSON test cases** (a shared model + placements + one op + kernel-verified `code|type|pointer` expectations, no message text) designed so that *any* engine — including a third-party reimplementation — can replay them to prove kernel-compatibility. **This is our ready-made differential oracle**; the schema is [`../a12-rulekit/corpus/case.schema.json`](../a12-rulekit/corpus/case.schema.json).
- [`../a12-rulekit/interpreter/`](../a12-rulekit/interpreter/) with [`../a12-rulekit/interpreter/CLAUDE.md`](../a12-rulekit/interpreter/CLAUDE.md), [`../a12-rulekit/docs/INTERPRETER-ARCHITECTURE.md`](../a12-rulekit/docs/INTERPRETER-ARCHITECTURE.md), and [`../a12-rulekit/docs/INTERPRETER-FINDINGS.md`](../a12-rulekit/docs/INTERPRETER-FINDINGS.md) — how a peer clean-room engine models Kleene 3VL, operator dispatch, star aggregation, iteration, polarity, and the compute poison. Read for *approach*, not to copy.
- [`../a12-rulekit/docs/RT-SEMANTICS-LEDGER.md`](../a12-rulekit/docs/RT-SEMANTICS-LEDGER.md), [`../a12-rulekit/docs/SEMANTICS-MAP.md`](../a12-rulekit/docs/SEMANTICS-MAP.md), and the full index [`../a12-rulekit/docs/README.md`](../a12-rulekit/docs/README.md).

## Building & running

Toolchain: **Lean 4.31.0**, pinned in [`lean-toolchain`](lean-toolchain); Lake 5.0. No external dependencies — the skeleton is self-contained.

```sh
lake build                          # elaborate & build the A12Kernel library (runs the #eval / example smoke checks)
lake env lean A12Kernel/Core.lean   # elaborate a single module with imports available
```

## Layout & the staged build order

- [`A12Kernel.lean`](A12Kernel.lean) — library root (imports the modules below).
- [`A12Kernel/Core.lean`](A12Kernel/Core.lean) — the core types from the encoding guide: `CellState` (three states — empty ≠ invalid), `Value`, `K` (strong-Kleene, no negation), `Polarity`/`Outcome`, `NumField`, `Env`.
- [`A12Kernel/Basic.lean`](A12Kernel/Basic.lean) — smoke module.

Build the executable spec **bottom-up** in the order of [`spec/13-lean-encoding-guide.md`](spec/13-lean-encoding-guide.md) §3 — scalars & literals → `CellState`/`formalCheck` → flat Kleene eval → required/index desugaring → the iteration environment → paths → polarity → computation → partial validation → interpolation/custom. Lock each stage against the engine before the next; the **ten encoding traps** (encoding guide §2) are where naive attempts silently diverge, and the properties in §4 are the strong regression guards.

## Conventions

- **English is canonical** — code, identifiers, comments, docs — matching the A12 OSS family.
- **Commits:** Conventional Commits (`type(scope): subject`, imperative, lowercase type); subject-only by default, a 1–2 sentence body only for a non-obvious *why*.
- Keep this file tool-neutral; [`AGENTS.md`](AGENTS.md) is a symlink to it so Codex and other AGENTS.md-reading agents get the same guidance.
