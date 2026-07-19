# Active implementation plan

This is the volatile checkpoint for resuming current work. Stable purpose and milestones belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md); exact implementation and proof coverage in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); retained correspondence in [`EVIDENCE.md`](EVIDENCE.md); and durable design conclusions in [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). Git and those owners retain completed history.

## Verified checkpoint

The repository has executable Lean semantics for admitted flat validation, one-group captured-outer correlation, and a narrow non-repeatable String-computation family, with checked lowering, payoff-selected laws and counterexamples, compact retained kernel observations, and versioned public/candidate process surfaces. Reference semantics 0.3.0 and the V2 suites are current; 0.2.0/V1 and the Rust experiment are archived.

The infrastructure simplification is complete and settled. Three compact evidence bundles remain; retired raw readers, packet binders, generators, qualification campaigns, and capture V1 machinery stay retired. [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) owns the scaling boundary, and the [simplification archive](archived/REFERENCE-AND-EVIDENCE-SIMPLIFICATION-PROPOSAL.md) owns measurements and recovery history.

Direct computation presence plus ordered left-to-right `And`/`Or` are internally complete over the admitted direct-presence leaves in one resolved checked context. The branch laws and operand-order counterexamples preserve clean not-true versus poison; local portable computation-control evidence remains pending and should be batched at the next meaningful family milestone.

The project now owns [`../spec/`](../spec/) as its language-neutral semantic bridge. [`A12-DMKITS-SPEC-SYNC.md`](A12-DMKITS-SPEC-SYNC.md) is the compact reconciliation ledger; its current pending entries cover the audited spec corrections and additions that a12-dmkits must review.

## Immediate order

1. Add first-matching computation alternatives: clean no-match falls through, the first holding alternative supplies the operation, and poison aborts without examining remaining alternatives. Keep selection separate from producer outcome, exact target application, dependency observation, and delta reporting.
2. At that computation-control milestone, decide whether the completed family needs one compact external calibration request. Do not build a new local harness; if no maintained upstream route exposes the required observations, keep the clauses `external evidence pending` and prepare the smallest a12-dmkits request.
3. Begin the first narrow partial-validation capsule after computation control.

## Guardrails and stop conditions

- Work only in this repository. Sibling repositories remain read-only and visibly unchanged.
- Put verified language-neutral behavior in [`../spec/`](../spec/) and update [`A12-DMKITS-SPEC-SYNC.md`](A12-DMKITS-SPEC-SYNC.md) in the same change. Keep Lean design, implementation status, evidence status, and plans in their `docs/` owners.
- Use red/green TDD, the Tier 1 gate in [`TESTING.md`](TESTING.md), payoff-selected laws/non-laws, and honest external-evidence status for each capsule.
- Add no dependency and change no linkage, hashing, or distribution policy without explicit approval.
- Do not restore retired V1, raw-packet, generator, registry, qualification, or universal-capture machinery. Reopen infrastructure only for a reproduced retained-mechanism defect, a concrete adopted semantic observation shape, or an actual consumer/release gate.
- Stop only for a serious blocker requiring new authority, an unavailable observation that changes the intended claim, an irreconcilable compatibility choice, or a dependency/licensing decision.

## Resume procedure

Read [`../AGENTS.md`](../AGENTS.md), this file, [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), [`EVIDENCE.md`](EVIDENCE.md), and [`TESTING.md`](TESTING.md). Inspect `git status --short`, recent commits, and the complete diff. Resume from the first unfinished step above. Finish each delivery with the relevant gates, measured theory/support/evidence ratios, `git diff --check`, a matching ledger entry for every behavioral `spec/` change, no machine-specific data, clean project-local temporary state, and no sibling worktree changes.
