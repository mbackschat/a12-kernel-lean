# Documentation discipline

This project adopts the useful documentation principles of [`../../a12-rulekit/docs/DOC-DISCIPLINE.md`](../../a12-rulekit/docs/DOC-DISCIPLINE.md), adapted to a Lean formalization and the repository's stricter write boundary. The purpose is to keep semantic truth, settled knowledge, current structure, live status, and future intent from collapsing into one document that inevitably drifts.

## Document roles

- [`../spec/`](../spec/) is read-only language-neutral semantic input. It plays the same consulted-upstream role for this repository that a12-kernel's merged BA/dev documentation plays for a12-rulekit; it is not a work log, findings ledger, implementation map, or roadmap.
- [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) owns the project argument, goals, evidence doctrine, success gates, roadmap, and outlook.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) owns the current Lean structure, representations, dependency boundaries, and adopted/rejected encoding decisions. It describes what exists, not a feature-status board.
- [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) owns Lean's role, theorem and trust contract, external case studies, and publication strategy.
- [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) owns durable, numbered findings about this project's formalization treatment and research conclusions. A finding is settled knowledge and rationale, not an open task.
- [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) is the live join from the read-only `§n` taxonomy to Lean definitions, proofs/counterexamples, kernel evidence, status, and exact support boundaries.
- [`SOURCES.md`](SOURCES.md) owns the drill path into the read-only kernel and rulekit evidence layers.
- [`README.md`](README.md) indexes the documentation set and its ownership rules; the top-level [`../README.md`](../README.md) remains the concise project front door.

## Finding lifecycle

Record a non-obvious formalization or research conclusion in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) before relying on it across several changes. Give it a stable `LF<n>` identifier, the date, its semantic section(s), its evidence basis, the claim, its Lean treatment, and its limits. Findings are not deleted or renumbered; if later evidence corrects one, amend it visibly and link the correcting finding.

Kernel-behavior discoveries are not invented or canonized here. They remain grounded in the read-only `spec/`, kernel documentation/source, and a12-rulekit's findings and real-kernel differentials. `LEAN-FINDINGS.md` records what this project learned from those sources and how the Lean theory should represent or bound it.

Open work does not belong in the findings ledger. Until a separate gaps ledger is justified by volume, current open obligations and `external evidence pending` states live in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), while sequencing and re-open criteria live in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md).

## Same-change update triggers

- A new or changed Lean module, representation, or dependency boundary updates [`ARCHITECTURE.md`](ARCHITECTURE.md).
- A new supported semantic clause updates [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) with its exact fragment, proof/counterexample state, kernel version, and external evidence status.
- A non-obvious mechanism, research conclusion, or rejected alternative updates [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).
- A changed goal, evidence rule, milestone, or next-capsule decision updates [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md).
- A changed theorem/trust discipline or external-study conclusion updates [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md).
- A new, renamed, or removed document updates [`README.md`](README.md) in the same change.
- A user-visible status change updates the top-level [`../README.md`](../README.md) without turning it into a detailed status table.

## Evidence discipline

Kernel differential testing is the empirical backbone. Internal examples are executable semantic locks, and proofs establish universal consequences of the Lean definitions, but neither is portable evidence of correspondence with the real kernel. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) must mark a fragment `external evidence pending` until retained, versioned kernel observations for that fragment are replayable in this repository.

The a12-rulekit interpreter is a clean-room peer used for triangulation and finding disagreements. It is never the oracle. A kernel mismatch changes the Lean definition or opens an explicit divergence; it is never hidden by relaxing an expected result.

## Markdown and links

Write one Markdown paragraph per line and do not hard-wrap prose. Link every referenced Markdown document with a regular relative Markdown link. Prefer stable document anchors and theorem names over copied prose, and avoid duplicating a detailed inventory that already has one owning surface.
