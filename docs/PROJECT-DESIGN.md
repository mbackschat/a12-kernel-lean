# a12-kernel-lean — project design: why Lean, and what it buys us

The argument for using Lean 4 here: the role it plays, what it uniquely provides over the existing Kotlin interpreter + tests + corpus, and — honestly — what it does not. The *how* (encoding decisions, the honest theorem chain, proof discipline) lives in [`ARCHITECTURE.md`](ARCHITECTURE.md); this doc is the *why / what-for*.

## The one argument

Lean plays three roles — a **functional language** (`#eval`-able, compilable), a **specification language**, and a **proof assistant** (kernel-checked proofs) — and this project uses all three, in that priority order. The chosen posture is *proved reference oracle, executable-first, proofs where they pay* (see [`ARCHITECTURE.md`](ARCHITECTURE.md), "Goal & role"). The deliverable is the ecosystem's **formal semantics-of-record and differential oracle** — not a replacement for the shipped Kotlin evaluator in [`../../a12-rulekit`](../../a12-rulekit).

The reason to reach for Lean rather than "just write more tests": **tests sample finitely many inputs; a Lean theorem quantifies over all of them.** The A12 semantics is full of subtle *universal* invariants — three-valued suppression, message polarity (VALUE/OMISSION), the order-dependent compute poison, partial validation's one-directional guarantee — that are easy to believe and hard to be sure of. That is exactly what machine-checked proof is for.

## What Lean buys us

### 1. An executable specification (near-term)

`eval` / `compute` become **total functions** — a precise, runnable definition you can interrogate with `#eval`, and *documentation that cannot drift* (if the semantics is ambiguous, the function will not typecheck, so the gap surfaces immediately). This is distinct from the Kotlin interpreter, which is optimized production code entangled with performance and platform targets; the Lean version is the clean *statement* of the intended answer.

### 2. Machine-checked proofs (the unique payoff)

Universal guarantees the test suite cannot give. The high-value A12 targets:

- **Monotonicity** — replacing an UNKNOWN operand with any definite value never flips a *fired* result to *not-fired* against the fire direction (the precise meaning of "formal errors only suppress, never invent, errors").
- **Determinism** — `eval` / `compute` are pure functions of `(model, document, clock, custom oracles)`; no hidden reads.
- **Partial-validation soundness** — if `validatePart` fires, every full document agreeing on the relevant set does not come back clean — the kernel's one-directional guarantee, *proven* rather than trusted.
- **Polarity one-sided soundness** — `VALUE ⇒ not repairable by any fill`; worth proving precisely because the prose "VALUE iff not-repairable" is suspected *not* to be an iff (`Having` escalates conservatively — see [`ARCHITECTURE.md`](ARCHITECTURE.md), "verify, don't assume the iff").
- **Verdict-algebra laws** — the `And` / `Or` tables behave (seeded by the `rfl` checks already in [`../A12Kernel/Core.lean`](../A12Kernel/Core.lean)).
- **Termination** — Lean *forces* every evaluation to terminate (no `partial` in the trusted core). For a language with iteration, quantifiers, and computation cascades, "this always terminates" is a guarantee by construction.
- **Refinement** — prove an *optimized* evaluator equals the simple reference one, justifying a fast path without re-risking correctness.

(The canonical target-theorem list and the proof discipline — no `partial`/`unsafe`, `IO` out of the semantics, `#print axioms` as a CI gate, `native_decide` kept out of the trusted chain — are in [`ARCHITECTURE.md`](ARCHITECTURE.md).)

### 3. A differential oracle / conformance engine

The Lean spec is an **independent third clean-room implementation**, which makes it a good arbiter. Replay [`../../a12-rulekit/corpus`](../../a12-rulekit/corpus) (portable, engine-verified JSON cases) through Lean `eval` and check against the recorded `code|type|pointer` expectations; do the three-way cross-check **kernel ↔ Kotlin interpreter ↔ Lean**. Where two disagree, one has a bug — and the engine backed by proven properties is the trustworthy tiebreaker.

### 4. Certificate checking and extraction (later / optional)

A small **trusted Lean checker** could validate evaluation *certificates* (traces) emitted by a fast Java/Kotlin/TS engine — proof-level trust in a result without proving the fast engine itself. And compiled Lean can be called from a JVM adapter if the proven core should ever run in the loop. Both are heaviest-effort and not near-term.

### 5. A design tool that surfaces underspecification

Formalizing forces precision. The genuinely fuzzy corners — DST / timezone handling, string length (Java UTF-16 code units vs Lean scalar values) — either get pinned or the function will not typecheck / the proof will not close. Lean turns "we're not sure" into a concrete, visible obligation.

## What Lean does not buy us

- It does **not prove the real kernel correct** — only our chosen formal semantics, and our interpreter relative to it. Equivalence to kernel 30.8.1 stays **empirical** (the differential corpus), because we have no formal model of the kernel's source. The honest theorem chain and the version-namespace discipline are in [`ARCHITECTURE.md`](ARCHITECTURE.md).
- If compiled Lean is *run*, the trusted base includes Lean's compiler and runtime; the proofs are checked against the logical definitions, not the compiled code.
- Proof effort is real — which is why the posture is *executable-first, proofs where they pay*, not "prove everything."

## Relationship to the a12 ecosystem

- **[`../../a12-kernel`](../../a12-kernel)** — the real engine; the behavioural **source of truth** / oracle.
- **[`../../a12-rulekit`](../../a12-rulekit)** — the **shipped** clean-room evaluator (Kotlin, native + JS) plus the conformance corpus.
- **a12-kernel-lean** (this) — the **formal semantics-of-record**: executable, proven where it pays, a differential oracle. It does not ship in the product.

The full source-of-truth hierarchy and the clean-room / EUPL boundary are in [`../CLAUDE.md`](../CLAUDE.md).

## Success criteria

What "working" means here, in the order to reach it:

- The **reference evaluator** reproduces the engine on every replayable case in [`../../a12-rulekit/corpus`](../../a12-rulekit/corpus) (100% PASS on the families it covers); any divergence is documented, never silent.
- The **core theorems** — verdict-algebra laws, monotonicity, determinism, partial-validation soundness — are proven, each with a clean `#print axioms` (no `sorry`, no `native_decide` in the trusted chain; discipline in [`ARCHITECTURE.md`](ARCHITECTURE.md)).
- Each staged layer ([`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md) §3) is locked against the engine before the next is built.
- The trusted core stays `partial`/`unsafe`-free and `IO`-free.

## Where we are, and the first Lean-specific wins

The executable-spec skeleton is in place ([`../A12Kernel/Core.lean`](../A12Kernel/Core.lean), [`../A12Kernel/Cell.lean`](../A12Kernel/Cell.lean), [`../A12Kernel/Document.lean`](../A12Kernel/Document.lean)) and the verdict algebra is locked by `rfl`. In order, the first wins that are genuinely Lean's: implement `eval` returning `Verdict` and `#eval` it → replay the corpus → prove the verdict-algebra laws and monotonicity (small, high-value, and they guard every later stage). The staged build order is [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md) §3; the first conformance targets are listed in [`ARCHITECTURE.md`](ARCHITECTURE.md).
