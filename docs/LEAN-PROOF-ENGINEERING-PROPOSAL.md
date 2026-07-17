# Lean proof-engineering study proposal

> Status: active staged research proposal, created 2026-07-17. Audience: proof contributors and maintainers. Lifecycle: accepted results migrate to their canonical owners; this proposal and its registry entry are deleted when the study closes.

## Purpose

Establish a small, explicit, Cedar-led proof-engineering discipline for this project and validate it on real A12 proofs before treating it as guidance. The immediate proving ground is the direct String-cascade capsule; a second, independent existing proof family must confirm that any adopted technique is not a one-off repair.

This is not a general Lean tutorial. It is an engineering study of how this repository should shape semantic definitions, equation lemmas, theorem statements, simplification sets, and case proofs so trusted proofs remain readable, stable under unrelated changes, and faithful to the complete result domain.

## Trigger

The direct-cascade executable locks reached green before the first proof attempt. The focused `lake build A12Kernel.Proofs.StringCascade` command still reproduces the initial proof failure: `withDependencyOutcome` elaborates through `Except.map`, producing a nested `Except` result that the attempted `change` steps do not match definitionally. Broad `simp` calls also did not reduce the intended layer predictably, and theorem statements that combined outcome conversion, context overlay, observation, and term refinement made failures difficult to localize.

That does not establish a semantic defect, nor does it justify changing a theorem until it becomes easy to prove. It does establish a useful research question: which definition and lemma boundaries let Lean express the intended phase structure directly, and which tactic discipline makes those proofs robust without hiding case distinctions?

The study begins from the current semantic claims. A proposed refactor may change an implementation shape only when it exposes a genuine semantic phase that already exists in the domain—for example, separating a checked computation outcome from prior-state delta projection. “It makes `simp` close the goal” is not sufficient architectural rationale.

## Non-goals and constraints

- Do not add, remove, upgrade, vendor, or replace a dependency, toolchain, tactic package, or documentation generator. A dependency proposal requires separate user approval.
- Do not weaken, strengthen, reorder, or silently restate a theorem to make its proof easier.
- Do not change executable A12 behavior merely to accommodate automation.
- Do not turn all project definitions into `[simp]` rules or make recursive evaluators globally unfoldable.
- Do not use `native_decide`, `sorry`, a new axiom, an opaque escape hatch, compiler substitution, or foreign execution in the trusted proof lane.
- Do not measure assurance by proof-line count, theorem count, tactic cleverness, or absence of `sorry` alone.
- Do not rewrite the whole proof tree. The cascade pilot and one independent second instance can justify a named scoped practice or reject a candidate; they do not by themselves justify a universal contributor rule.
- Do not copy Cedar or Radix proof expressions mechanically. Transfer the mechanism and rationale into original A12 definitions and proofs.
- Do not push any result to a remote unless the user explicitly requests that push.

## Research questions

1. Which semantic phases should be separate definitions because they carry different domain meanings, and which proposed helpers would exist only to appease tactics?
2. When should a proof use definitional reduction or `rfl`, an explicit equation lemma plus `rw`, `simp only` with a reviewed rewrite set, or direct `cases` on the semantic enum?
3. Which equations, if any, are safe global `[simp]` rules because they are unconditional, canonical, terminating reductions?
4. How should `Except`, nested result domains, and short-circuiting evaluators be stated so failure branches remain visible rather than erased by success-only helper lemmas?
5. Where should projection lemmas separate a rich semantic result from delta, application, or transport views?
6. What local theorem and comment structure makes hypotheses, direction, residual errors, and unsupported cases reviewable without reading tactic traces?
7. Which current A12 proof family supplies a genuine second instance of the same mechanism?

## Source corpus and authority

The study uses three source classes in this order:

1. The Lean 4.31.0 behavior actually pinned by [`lean-toolchain`](../lean-toolchain), together with the matching official Lean reference material, is authoritative for tactic and elaborator behavior.
2. Cedar is the primary project precedent because its executable specification, validation, theorem, test, differential, and integration roots resemble this project's assurance problem. Audit revision [`3977eb4`](https://github.com/cedar-policy/cedar-spec/tree/3977eb4f017b421b7ac0b31ea4635e1dd36ce3ef).
3. Radix is the compact secondary precedent for evaluator/relation and transformation bridges. Audit revision [`617b67e`](https://github.com/leodemoura/RadixExperiment/tree/617b67eb09681ca98e19759b48978866dcafeb17).

Every source audit starts by verifying a fresh or intact read-only local clone at the named revision. A partial or damaged scratch clone is not evidence. Research notes may cite source paths and declarations, but this repository does not vendor those projects or commit machine-specific clone paths.

## Work plan

### PE0 — Capture the A12 baseline

Actions:

- Preserve the direct-cascade theorem statements being attempted, the exact semantic definitions they mention, their minimal imports, and the focused failing build command.
- Classify each failure by mechanism: hidden `Except.map`/`bind`, unresolved definitional reduction, dependent proof field, unhelpful theorem shape, missing equation lemma, or genuinely false claim.
- Inventory every `[simp]`, `simp`, `simp only`, `rw`, explicit enum case split, `decide`, and `native_decide` use under [`A12Kernel/Proofs/`](../A12Kernel/Proofs/) without treating raw counts as quality metrics.
- Select an existing positive control that already uses narrow rewriting well, such as the correlation or elaboration proof families.

Deliverable: a compact baseline and candidate-pattern table in this proposal while the study is active.

Gate: every failure has a named mechanism; “Lean could not prove it” is not an acceptable classification.

### PE1 — Audit Cedar’s proof discipline

Read and inspect:

- `cedar-lean/GUIDE.md`, especially import, theorem-docstring, and `simp only` guidance;
- Cedar’s theorem root and its proof-import linter;
- representative specification/evaluator definitions under `cedar-lean/Cedar/Spec/`;
- representative validation and error-domain definitions under `cedar-lean/Cedar/Validation/`;
- `cedar-lean/Cedar/Thm/Data/Control.lean` for `Except.bind_ok_T`, `Except.bind_ok`, `Except.bind_err`, `do_eq_ok`, and related bridges over elaborated `do` notation;
- `cedar-lean/Cedar/Thm/Tactics.lean` for `simp_do_let`, which exposes a subcomputation by case analysis before applying a small explicit simplification set;
- `cedar-lean/Cedar/Thm/Validation/Typechecker/Basic.lean` for the owning `EvaluatesTo` and `TypeOfIsSound` abstractions and `split_type_of`;
- `cedar-lean/Cedar/Thm/Validation/Typechecker/And.lean` for the inversion-lemma-then-soundness pattern;
- `cedar-lean/Cedar/Thm/WellTyped/Expr/Typechecking.lean` for explicit `Except.bind_ok`/`Except.bind_err`, constructor injection, and controlled simplification;
- `cedar-lean/Cedar/Thm/Validation/Typechecker/Call.lean` as a large operator-specific application of the residual-error vocabulary owned by `Basic.lean`;
- `cedar-lean/Cedar/Thm/Authorization/Evaluator.lean` for `ways_and_can_error`, `and_produces_bool_or_error`, record-evaluation lemmas, and domain-facing result statements rather than tactic style alone.

For each representative proof, record:

- the theorem statement and result domain;
- whether recursive evaluator equations are global simp rules or are opened locally;
- the exact role of `simp only`, `rw`, `cases`, helper equalities, and injection lemmas;
- how error and unsupported branches remain visible;
- how imports and theorem aggregation are controlled;
- the failure mode the practice is intended to prevent.

Record Cedar’s actual simplification rule accurately: its guide prefers `simp only` over `simp`, while explicitly allowing plain `simp` to close a goal, and the theorem sources use both. At the pinned revision, the specification and validation roots do not carry domain `[simp]` declarations; most custom simplification infrastructure lives in theorem utility modules. Measure that source/proof separation instead of treating Cedar as uniformly `simp only`.

Treat Cedar’s `checkThmFile` as an import-shape check only: it checks literal imports against corresponding file/directory aggregators, can omit proof directories without a matching aggregator, and does not inspect elaborated axiom dependencies. It may inform A12’s source organization, but it cannot replace this project’s stronger environment and trust audit.

Deliverable: transfer-candidate table with columns `Cedar mechanism`, `source declaration`, `A12 analogue`, `benefit`, `risk`, and `trial`.

Gate: no Cedar practice becomes a recommendation until an A12 experiment exercises it.

### PE2 — Audit Radix as a secondary check

Inspect:

- `Radix/Eval/Expr.lean`, `Radix/Eval/Stmt.lean`, and `Radix/Eval/Interp.lean` for the evaluator/bridge ladder, including `evalExpr_ok/ok'`, `evalArgs_ok/ok'`, `mkFrame_ok/ok'`, the `andThen` result equations, and fuel monotonicity;
- `Radix/Proofs/InterpCorrectness.lean` for the successful `interp_complete` and `interp_sound` directions;
- `Radix/Proofs/Determinism.lean` for relation-oriented case proofs;
- `Radix/Opt/ConstFold.lean` for partiality-sensitive transformation laws where an algebraic identity may need a success/type hypothesis and an apparently obvious absorbing law may be false;
- representative optimization modules under `Radix/Opt/` for forward-preservation structure;
- `Radix/Linear.lean` and state/agreement lemmas where primitive state projections are lifted into `BigStep` preservation and strengthened induction invariants.

Check explicitly that recursive evaluators are not made broad global simp rules merely for proof convenience, while small closed reducers and projection equations may be. Record Radix’s success-only and one-way theorem boundaries accurately; do not promote them to total error equivalence. Its Lean version differs from this project’s pinned 4.31.0, so every candidate technique must be re-elaborated locally rather than adopted from appearance.

Also inspect repeated effect lemmas. At the audited revision, `BigStep.funs_preserved` and similar get/set interaction results occur in more than one optimization/state module. Treat that as a warning: a reusable A12 outcome/overlay/projection law belongs in one semantic proof owner, not copied into every future computation capsule.

Deliverable: secondary comparison table identifying where Radix confirms Cedar, where it is merely a compact convenience, and where A12’s richer no-value/poison/error domain requires a stronger boundary.

Gate: Cedar remains the default when the projects suggest different proof practices unless A12’s semantics provides a written reason. Each A12 pilot test asserts an exact result or error constructor and includes a separating negative case; an `.isOk`-only check is insufficient.

### PE3 — Design the controlled experiment

For the same small cascade theorem family, trial these proof shapes without changing the claim:

| Trial | Technique | Required observation |
|---|---|---|
| A | Definitional reduction and `rfl` | Accept only where the semantic definition intentionally exposes the equation |
| B | Named equation/helper lemma followed by `rw` | Determine whether the helper captures a reusable domain boundary rather than tactic scaffolding |
| C | `simp only` with an explicit local rewrite set | Record every required equation and whether the proof remains readable |
| D | Explicit `cases` on `StringTargetOutcome`, `FormalCause`, `Except`, or the target-check result | Confirm that all non-success branches remain visible and correctly discharged |
| E | A candidate `[simp]` equation | Document its normal-form orientation; prove it is unconditional and canonical, terminates on nested representative terms, preserves every success/error branch, needs no reverse rewrite, helps the second instance, and leaves unrelated proofs unchanged |

The pilot theorem set must cover:

- dependency-cell well-formedness;
- target shadowing and preservation of unrelated reads;
- accepted, no-value, target-error, and inherited-poison transport;
- rejection of validation-scoped required poison;
- non-exposure of the attempted invalid payload;
- separation of checked outcome from prior-state delta;
- the nearest non-laws showing that delta and applied-value views do not determine a dependency read.

Deliverable: one decision row per trial with the exact theorem, proof shape, required helper equations, readability assessment, fragility or failure mode, and accept/reject outcome.

Gate: a winning proof must preserve the original theorem’s hypotheses, direction, and result domain and must not add trust.

### PE4 — Apply the winning pattern to the cascade

Actions:

- Review and stabilize the currently failing proofs in [`A12Kernel/Proofs/StringCascade.lean`](../A12Kernel/Proofs/StringCascade.lean) with the smallest accepted proof vocabulary.
- Keep the semantic source in [`A12Kernel/Semantics/StringCascade.lean`](../A12Kernel/Semantics/StringCascade.lean) focused on actual outcome, overlay, step, and cascade phases.
- If a new definition or equation lemma is introduced, state why it is a domain boundary and add a nearest misuse or non-law when appropriate.
- Keep recursive evaluation closed by default; expose only the equations deliberately needed by callers.
- Put any reusable `Except`, outcome, overlay, or projection proof lemmas in one deliberately imported owner under `A12Kernel/Proofs/`; semantic modules must not import proof modules merely to obtain a simplification set.
- Add the completed proof module to the trusted root and verify its exact axiom dependencies.

Deliverable: green cascade proof module with reviewed theorem statements and local documentation.

Gate: focused conformance remains unchanged and green; the proof root contains no `native_decide`, new axiom, or hidden compiler/IO dependency.

### PE5 — Prove a second instance

Select one existing theorem family outside the new cascade module that exhibits the same mechanism. Preferred candidates are the `Except`-carrying checked-context coherence theorems in [`A12Kernel/Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean), with [`A12Kernel/Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean) as a positive-control comparison.

Actions:

- Apply the accepted pattern to one real theorem or small family without changing its public statement.
- If the existing proof is already clearer than the candidate practice, retain it and reject the proposed general rule.
- Centralize any genuinely shared projection or effect lemma rather than duplicating it in cascade and elaboration modules.
- Run the existing conformance and trust gates to prove that the experiment did not change executable semantics or the imported trust boundary.

Deliverable: second-instance result and an explicit verdict on whether the practice is local, reusable, or rejected.

Gate: no project-wide guidance is accepted from the cascade result alone.

### PE6 — Adopt only the validated guidance

For every candidate practice, record:

- decision: accept, accept in a named scope, or reject;
- exact scope and exceptions;
- rationale from Cedar, Radix, Lean behavior, and both A12 instances;
- nearest failure mode or counterexample;
- migration destination from the ownership table below.

Potential outcomes include, but are not assumed in advance:

- important trusted proofs use `simp only` with reviewed rewrite sets;
- recursive semantic evaluators are not global simp rules;
- small constructor/projection equations may be `[simp]` when canonical and terminating;
- enum/result case analysis remains explicit when it communicates the complete semantic domain;
- named equation lemmas are preferred when they express a stable domain phase;
- `native_decide` remains confined to nontrusted executable conformance and qualification locks.

Gate: the resulting guidance is short enough to follow during ordinary proof work and precise enough for review to reject a violation.

### PE7 — Verification and independent review

Run:

```sh
lake build A12Kernel.Proofs.StringCascade
lake build A12Kernel.Conformance.StringCascade
lake build
lake test
./scripts/check-lean-trust.sh
git diff --check
```

Also run the reference and qualification gates affected by any shared definition refactor. No external candidate or sibling command is required unless the semantic behavior itself changes; tactic research alone must not manufacture new kernel evidence.

Commission independent reviews for:

- theorem statement and semantic-domain fidelity;
- tactic stability and `[simp]` safety;
- proof-root imports, axioms, and trust classification;
- documentation ownership and closure.

Gate: all focused and full gates pass, no `spec/` file changes, no machine-specific paths enter the repository, sibling visible status is unchanged, and each accepted practice has survived both A12 instances. Every adopted `[simp]` rule has a reviewed normal-form orientation, terminates on nested representative terms, preserves all result branches, requires no reverse rewrite, and causes no unintended change outside the targeted proof families.

### PE8 — Close the study

Move every accepted durable result into its canonical owner, update [`PLAN.md`](PLAN.md) to the next semantic task, delete this proposal, and remove its registry entry and active-plan link in the same change. Git history is the archive.

If an unresolved proof-engineering question remains, retain only a narrowly restated proposal for that question. Do not preserve the whole completed work plan for one pending paragraph.

Commit completed work locally using Conventional Commits. Do not push unless the user explicitly asks.

## Finding and decision destinations

| Result | Canonical destination | What belongs there |
|---|---|---|
| Pending questions, source-audit matrix, experiment matrix, task order, and provisional decisions | This proposal | Active study material only; deleted on closure |
| Current study position and next action | [`PLAN.md`](PLAN.md) | One concise checkpoint, not the research diary |
| Accepted general proof/tactic discipline and durable Cedar/Radix study conclusions | [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) | The short project-level practice, source basis, scope, and limitations |
| A non-obvious durable mechanism or rejected alternative with semantic/formalization consequences | [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) | A numbered `LF<n>` finding with basis, Lean treatment, and limits; not routine tactic notes |
| An adopted semantic phase, equation API, module boundary, or dependency direction | [`ARCHITECTURE.md`](ARCHITECTURE.md) | Current-state design and rationale |
| Repeatable focused proof workflow, diagnostics, or final gate change | [`TESTING.md`](TESTING.md) | Commands, red/green method, gate meaning, and failure interpretation |
| Actual theorem, counterexample, and adequacy coverage | [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) | Live support/proof/evidence status |
| The exact local claim, hypotheses, rationale, or warning needed to read one definition/theorem | Lean module docstrings and comments | Local explanation near the declaration; no project-wide policy duplication |
| Reusable `Except`, outcome, overlay, or projection proof machinery | A deliberately imported utility module under [`A12Kernel/Proofs/`](../A12Kernel/Proofs/) | Proof-only equations and tactics with one owner; semantic modules never depend on this layer |
| A concise universal contributor rule that must be enforced on every future change | [`CLAUDE.md`](../CLAUDE.md) | Only if the study establishes such a rule; link to the detailed owner rather than copying it |
| External study revisions and durable source interpretation | [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) | Audited revision and conclusions; no machine-specific clone paths |

Tactic research alone does not update [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), [`EVIDENCE.md`](EVIDENCE.md), [`PROTOCOL.md`](PROTOCOL.md), [`ARTIFACTS.md`](ARTIFACTS.md), or the read-only [`spec/`](../spec/). Those documents change only if the experiment independently changes the fact set they own.

The prohibition on `native_decide` in the trusted proof lane is this project’s own trust policy. Cedar uses `native_decide` in some trusted SymCC arithmetic proofs, so that prohibition must not be presented as a Cedar-derived convention.

## Stop and escalation conditions

Stop and report rather than improvising when:

- the pinned Cedar or Radix source cannot be reconstructed and verified;
- a desired tactic or proof method requires a dependency or toolchain change;
- the theorem appears false or needs a material hypothesis/result-domain change;
- a definition would be changed only to make automation succeed;
- the proof exposes a semantic ambiguity that requires new kernel evidence;
- a proposed `[simp]` rule loops, expands recursive evaluation, hides a failure branch, or changes an unrelated proof;
- the second instance contradicts the cascade-derived recommendation;
- completing the work would require a remote push that the user has not explicitly requested.

In those cases, preserve the executable counterexample or focused failure, classify the issue in [`PLAN.md`](PLAN.md), and route any durable finding to the appropriate owner above.
