# Testing methodology

This document owns the test harness and working method for `a12-kernel-lean`. The project tests three different claims—execution of the Lean theory, universal consequences inside that theory, and empirical correspondence with kernel 30.8.1—and deliberately does not collapse them into one green check.

## The four harness layers

| Layer | Repository surface | What a pass establishes | What it does not establish |
|---|---|---|---|
| Focused executable locks | [`../A12Kernel/Conformance/`](../A12Kernel/Conformance/) imported by [`../A12Kernel/Conformance.lean`](../A12Kernel/Conformance.lean) | Concrete inputs execute through the Lean definitions and produce the stated values, truth states, verdicts, or rejections | Universal correctness or agreement with the external kernel |
| Trusted proofs and checked non-laws | [`../A12Kernel/Proofs/`](../A12Kernel/Proofs/), [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean), and [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean) | Named theorems hold for every modeled input satisfying their hypotheses; counterexamples prevent a plausible stronger claim from being mistaken for a law | Correctness of the chosen primitive semantics or universal correspondence with kernel code |
| Retained external evidence replay | [`../evidence/`](../evidence/), [`../A12Kernel/Evidence/`](../A12Kernel/Evidence/), and [`../A12Kernel/EvidenceMain.lean`](../A12Kernel/EvidenceMain.lean) | The focused Lean projection agrees with retained portable observations produced by the real pinned kernel on those cases | Exhaustive agreement, hidden kernel intermediate states, or correctness outside the projected fragment |
| Structural and hygiene gates | [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), `git diff --check`, and worktree checks | Trusted roots contain no banned proof escape hatch, every exported theorem is audited, axiom dependencies are classified, patches are clean, and sibling worktrees remain untouched | Any new semantic fact by itself |

`lake build` runs the first two layers because the library root imports both the conformance root and the trusted proof root. `lake test` runs the retained-evidence executable separately. The trust script inspects the proof closure separately again because successful elaboration alone does not reveal an accidental axiom or omitted theorem-root import.

## Red/green semantic development

Every new semantic capsule uses red/green TDD.

1. State the exact supported fragment, its observable result domain, its evidence source, the useful law, and the nearest false generalization before adding a general abstraction.
2. Add concrete separating examples under `A12Kernel/Conformance/` against the intended public API.
3. Run the focused module and confirm a meaningful red result: the module, definition, constructor, or behavior is absent or wrong for the expected semantic reason.
4. Implement the smallest total pure definition that makes those examples green.
5. Add an independent declarative relation or judgment only when it exposes a useful boundary, then prove its connection to the executable definition in `A12Kernel/Proofs/`.
6. Capture and retain focused kernel observations through the external a12-dmkits adapter, extend the narrow replay projection, and make `lake test` green.
7. Update architecture, findings, implementation coverage, and evidence documentation, then run every final gate.

A red run is part of the evidence for the workflow, not a file committed to the repository. A test that was green before the semantic implementation is either not testing the requested behavior or is accidentally passing through an older path.

## Executable Lean examples

A conformance lock is an `example` whose proof evaluates a decidable proposition. For example:

```lean
example : (filteredCounts 1).sumSelected source = .value 7 := by
  native_decide
```

The left side executes the pure Lean function on the concrete fixture. Equality for the result type is decidable, so `native_decide` compiles and evaluates the decision procedure; if it produces `false`, elaboration fails and therefore `lake build` fails. Use `decide` for small structural propositions that reduce economically in the kernel, and `native_decide` for concrete executable fixtures where compiled evaluation materially reduces cost.

Lean tests do not require a JUnit-style runtime runner. The conformance modules are ordinary Lean modules imported by the conformance root: a false `example`, an ill-typed fixture, or an unprovable expected equality prevents elaboration and fails the build. `#eval` remains useful while exploring a new definition and for deliberate smoke output, but printed output alone is not an assertion; once behavior matters, move it behind an `example`, theorem, or retained-evidence comparison that can fail automatically.

`native_decide` is permitted only in conformance examples and other explicitly untrusted executable test surfaces. It is forbidden from the trusted semantics/proof closure by [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), because a general theorem should be supported by an inspectable proof term rather than trusted native execution.

Concrete cases should be separating, not merely numerous. Hold the model, kind, document, and condition fixed while varying one semantic axis. For filtered iteration, pair an invalid consumed cell in a filter-dropped row with the same cell in a kept row; this distinguishes filter-before-consumer semantics from an eager whole-column scan. For captured-outer correlation, pair equality with and without explicit repetition self-exclusion, then add an asymmetric inner-less-than-outer case so reversed or collapsed origins cannot pass accidentally. Keep guard, filter key, and starred consumer in distinct fields: `Count` is the filled outer guard and error target, `StockQty` is the numeric key when the filter needs one, and `UnitWeight` is the selected presence consumer. This separation prevents guard suppression, key classification, and consumer observation from masking one another. For the selected-consumer footprint, use two duplicate-key rows: malformed consumer row 1 must fire only on outer row 1 because it self-drops there and is kept from row 2; moving the malformed consumer to row 2 must mirror the firing row. For filter-state evidence, hold guards and consumers valid while comparing explicit empty with zero, then use a three-row malformed-local witness in which the malformed row is observably not kept while two healthy equal-key siblings still select each other. For operator evidence, place consumer values asymmetrically so the selected relation is recoverable from firing rows: numeric inequality uses keys `5, 5, 9` with only row 3's consumer filled, repetition equality fills only row 2, and repetition less-than fills all consumers to expose predecessors. Include the all-valid control and ordinary, boundary, empty, malformed, and order-sensitive cases whenever that axis is observable.

Run a focused executable file after its imports have been built:

```sh
lake build A12Kernel.Semantics.Iteration
lake env lean A12Kernel/Conformance/Iteration.lean
lake build A12Kernel.Semantics.Correlation
lake env lean A12Kernel/Conformance/Correlation.lean
```

Run `lake build` before handoff so the same examples also pass through the actual library import graph.

## Universal proofs and counterexamples

Proof modules quantify over arbitrary inputs and use induction, case analysis, rewriting, or previously proved laws to construct proof terms. Lean's kernel checks those terms. The theorem statement—especially its hypotheses, direction, and result domain—is the claim; theorem counts and proof-line counts are not quality measures.

When an executable enumerator has meaningful independent content, follow the audited Cedar pattern: define an ordered declarative relation separately, prove execution-to-relation soundness and relation-to-execution completeness, and package them as an exact bridge. Preserve ordered-list equality when order or multiplicity can become observable; a membership equivalence is too weak for an ordered A12 document.

Read-footprint theorems should be stated at the semantic observation boundary. The correlated `evalGuardedAnyFilledOn_filter_before_consumer` theorem assumes equal selection, equal validation observation of the outer guard, and equal validation observations of consumer cells in selected rows; it deliberately does not require equality of raw checked cells or any dropped consumer. This makes the proved noninterference exactly as strong as the evaluator's read surface and no stronger.

Each useful law should be paired with the nearest plausible false generalization as a concrete checked non-law. For example, a same-group star reopens the group and spans all candidate rows; the proposition that it collapses to the current row must have an explicit counterexample before `$` correlation is introduced.

Every exported theorem under `A12Kernel/Proofs/` must be imported by [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean) and registered with `#print axioms` in [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean). The trust script fails if a proof file is missing from the root, a theorem is missing from the audit, a trusted source contains `sorry`, `admit`, a project axiom, `unsafe`, `partial`, or `native_decide`, or the audited closure depends on an unexpected axiom.

## Kernel evidence and differential replay

Kernel differential testing is the empirical backbone, but the kernel never becomes a dependency of this repository. Focused scenarios run externally through the a12-dmkits adapter in the local `../a12-rulekit/` checkout. The Groovy-dynamic kernel result is the observation anchor, the static-Java kernel strategy detects a strategy split, and the a12-dmkits interpreter is a clean-room triangulation peer that may reveal a disagreement but is never the oracle.

Only portable own-domain artifacts—standalone model, placements, operation, complete observed signatures, kernel version, and any divergence record—are retained under `evidence/`. A narrow typed projection contains the input needed by the current Lean fragment but never a separately hand-authored expected Lean result. The replay driver derives the focused expectation from the complete external observation, executes the public Lean semantics, and exits nonzero on mismatch. The current driver keeps flat/path/required, uncorrelated iteration, and captured-outer correlation in three separate closed projections. Correlation replay validates 1-based unique rows, declared guard and consumer references, a complete ordered outer-row pointer map, and both inner and outer origins. It derives firing membership from the retained canonically sorted focused signatures, restores those firings to the projection's document-row order, and compares the result with Lean; the external evidence therefore establishes firing membership, not kernel emission order. The replay also binds the typed filter to the retained model without a general parser: unique group and Number-field paths and configurations, a unique focused rule, authored absolute-or-relative condition group/field paths resolving to the projected absolute entities, the error entity resolving to the guard field, and a canonical rendering of the admitted condition subset must all match exactly. Classified projected cells and row IDs remain a review-trusted transcription of the retained placements until a general instance decoder exists.

For `$` evidence, retain the actual executed stored condition in the standalone DM-JSON model. A typed origin projection is useful for Lean replay but cannot replace the raw condition because a formatter or conversion path may silently lose a `$`-bearing conjunct. Preserve full VALUE/OMISSION signatures even while the current truth-only replay deliberately compares only firing rows and pointers.

Observable boundaries must stay explicit. Validation output can establish that an authored message fired or was silent and can preserve its observed VALUE/OMISSION signature; it cannot generally distinguish the kernel's hidden `unknown` from `false`. When the Lean capsule deliberately defers a dimension such as filtered-result polarity, replay compares only the admitted truth/firing projection while retaining the full external signature for the later capsule.

The current retained gate reports `38/38`: 36 runtime observations and two static diagnostics. Twelve correlation observations across seven models agree in Groovy-dynamic, static-Java, and the a12-dmkits interpreter. They cover every currently admitted correlation comparison constructor plus the admitted empty and malformed filter-operand observations. The malformed-local witness establishes the observable claims that the malformed row is not kept and healthy equal-key siblings still select one another; it does not establish that a hidden kernel intermediate is Lean's `unknown`. Broader repeatable path elaboration, `$` authoring diagnostics, field/path/equality-scale legality, filtered-result polarity, nested or multi-star and cross-group binding, and general consumers remain deferred. The exact retained cases and limits are indexed in [`EVIDENCE.md`](EVIDENCE.md).

External capture may write only under paths already ignored by the sibling repository. Before capture, record the sibling's visible status and verify the disposable path with `git check-ignore`. Create an ignored disposable adapter copy under `../a12-rulekit/build/`, invoke the existing [`CorpusEngines`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusEngines.kt) or [`CorpusCapture`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusCapture.kt) patterns there, and collect Groovy-dynamic, static-Java, and interpreter results without modifying live tracked sources. Do not run the live [`CorpusGenerator`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusGenerator.kt), because its normal job rewrites tracked corpus output. Copy only the portable own-domain model and observation artifacts into this repository, remove the disposable source and output, and confirm afterward that the sibling's tracked and visible-untracked status is exactly unchanged. Never leave a temporary source, model, projection, or generated corpus case visible in a sibling worktree.

## Final gate

Run the complete gate from the repository root:

```sh
lake build
lake test
./scripts/check-lean-trust.sh
git diff --check
git status --short
git -C ../a12-rulekit status --short
```

Interpret failures by layer. A conformance failure means a concrete Lean behavior changed. A proof failure means the definition no longer supports the stated universal law or the proof needs legitimate repair. An evidence mismatch means the Lean projection and retained kernel observation disagree and must be investigated at the semantic definition or projection boundary; never relax the expected result merely to make it green. A trust failure means the theorem closure or audit is incomplete even if ordinary compilation passed.

## Capsule test checklist

- The red run failed for the intended missing or incorrect behavior.
- Concrete cases separate ordinary, boundary, empty, malformed, selection, and ordering behavior as applicable.
- Unsupported syntax or semantic axes fail closed or are unrepresentable.
- The useful theorem states the smallest defensible law with exact hypotheses.
- The nearest stronger false claim has a checked counterexample.
- Every exported theorem is in the trusted root and axiom audit.
- Focused portable kernel observations exist, or the implementation map says `external evidence pending`.
- The replay derives expectations from retained external output rather than duplicating them in Lean-shaped data.
- `lake build`, `lake test`, the trust audit, and patch/worktree hygiene gates all pass.
