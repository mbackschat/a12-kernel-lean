# Documentation index

This index routes readers to the document that owns each kind of knowledge. The documentation workflow is specified in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md); repository rules that must stop an unsafe action before it happens remain in [`../CLAUDE.md`](../CLAUDE.md).

## Start here

- [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) — the project constitution: goal, users, evidence doctrine, semantic-capsule definition, milestones, success criteria, and outlook.
- [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) — the live `§n`-to-Lean map: implemented fragments, theorems/counterexamples, external kernel evidence, exact boundaries, and open evidence gates.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) — the current Lean encoding and module structure, including adopted and rejected representation choices.
- [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) — durable numbered findings and rationale from formalization and local evidence research.
- [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) — why Lean, what it can and cannot establish, audited project studies, proof opportunities, trust rules, and the later Verso strategy.
- [`SOURCES.md`](SOURCES.md) — the drill chain from each semantic topic to the read-only kernel and a12-rulekit sources, findings, corpus, and differential locks.

## Semantic input

The language-neutral semantic body lives under [`../spec/`](../spec/) and is treated as read-only. Start with [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md), then follow the numbered deep-dives. New Lean findings, implementation progress, evidence state, and planning belong in this `docs/` directory instead.

## Ownership rule

Use one owning surface per fact: semantic meaning in the read-only `spec/`; settled Lean treatment in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md); current structure in [`ARCHITECTURE.md`](ARCHITECTURE.md); live coverage/evidence state in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); future intent in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md). Cross-link instead of copying.
