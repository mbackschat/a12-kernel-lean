# Lean formalization findings

This is the durable findings ledger for `a12-kernel-lean`, adapted from a12-rulekit's separation between kernel truth, implementation treatment, and live gaps. It records settled conclusions about how this project should formalize, prove, and empirically anchor the read-only semantics. It does not redefine kernel behavior and it is not a backlog.

Each finding has a stable `LF<n>` identifier, date, semantic section, evidence basis, Lean treatment, and explicit limit. Findings are not deleted or renumbered; later corrections amend the record visibly.

## LF1 — differential evidence and proofs answer different questions

> Date: 2026-07-13. Sections: cross-cutting. Basis: project decision; Cedar-style executable-spec/production-engine separation; local a12-rulekit corpus and differential architecture.

Kernel differential testing is the empirical backbone. Each executable Lean capsule must ultimately be checked against retained portable observations from the real kernel. Proofs establish universal consequences of the chosen Lean definitions; they do not establish that the external kernel implements those definitions. Fuzzing broadens the empirical search but proves neither internal laws nor universal correspondence.

The evidence topology has four distinct roles: the real kernel is behavioral authority; the external a12-rulekit adapter is the kernel-facing probe/export harness; the portable corpus or another explicitly versioned artifact is the repository boundary; the a12-rulekit interpreter is a clean-room peer for triangulation and divergence discovery, never the oracle. Contrary kernel evidence overrides agreement between Lean and the interpreter.

Lean treatment: every live fragment in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) separates internal assurance from external adequacy. A capsule without retained kernel observations is marked `external evidence pending`, even when it builds, executes, and has trusted proofs.

Limit: finite retained observations cannot prove universal kernel equivalence. A wrong Lean primitive can support flawless theorems, and a finite differential suite can miss a divergence; confidence comes from keeping both forms of evidence connected without collapsing them.

## LF2 — checked elaboration must own model and runtime-policy coherence

> Date: 2026-07-13. Sections: §2, §10. Basis: [`../spec/08-paths-and-references.md`](../spec/08-paths-and-references.md), read-only path differentials, Lean/Lean4Lean parser–elaborator separation, and `do` Unchained's explicit surface-to-core transformation pattern.

The flat evaluator originally accepted resolved IDs, typed field metadata, and already checked cells independently. That was a real semantic admission: a caller could pair one identifier with inconsistent kind/scale metadata or check its raw cell under a different policy.

Lean treatment: [`A12Kernel/Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean) introduces a parser-independent surface subset and an expanded `FlatModel`. Resolution validates the model first, never uses first-match ambiguity, rejects repeatable scope, and lowers only legal scalar conditions into `CheckedFlatCondition`. The wrapper carries both model-validity and core-field well-formedness proofs. `FlatModel.checkContext` applies the same unique declaration policy to raw cells; unresolved or ambiguous IDs fail closed as malformed.

[`A12Kernel/Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean) proves that an admitted field has one matching non-repeatable declaration, that raw-to-checked context construction uses exactly its `formalCheck` policy, and that lookup failure observes as validation `unknown .malformed`. This closes policy coherence for the checked surface route. The low-level core evaluator remains intentionally usable with an arbitrary `FlatContext` for isolated semantic laws, so the stronger claim does not apply to arbitrary direct calls.

Supported path treatment: structured absolute paths, plain parent-relative paths, and bare lookup in the kernel order declaring group → nearest ancestors → flag-gated model-wide unique name. Excluded: concrete parsing/quoting, named turning-point labels, `RuleGroup`, stars, `$`, semantic indices, and repeatable evaluation.

External limit: [`ShortNameRefDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ShortNameRefDiffTest.kt) and [`NamedAncestorPathDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NamedAncestorPathDiffTest.kt) establish kernel-backed provenance, but no retained portable kernel artifact currently covers this exact Lean projection. Its status is therefore internal-only, external evidence pending.

## LF3 — `$` correlation requires two explicit environments

> Date: 2026-07-13. Sections: §9, §10, §12. Basis: [`../spec/07-repetition-and-iteration.md`](../spec/07-repetition-and-iteration.md), [`../spec/01-data-model.md`](../spec/01-data-model.md), read-only a12-rulekit findings, interpreter treatment, and kernel differentials.

The semantic mechanism is an explicit two-environment filter. A rule begins with a captured repetition environment `outerEnv`. A starred operand enumerates candidate rows and constructs an `innerEnv` for each candidate. Inside `Having`, ordinary references resolve against `innerEnv`, while `$`-marked references resolve against `outerEnv`; correspondingly, `CurrentRepetition(G)` reads the candidate row and `CurrentRepetition($G)` reads the captured outer row. `$` is correlation, not positional selection.

Star binding is inseparable from this mechanism. Bindings are retained only above the first star; a same-group star reopens that group and spans all its instantiated rows rather than silently collapsing to the current row; a multi-star path binds at the first star. The initial Lean reference meaning must be a straightforward candidate-row filter, not the interpreter's equality-bucket/hash-join optimization.

The most important edge cases are already exposed by the read-only evidence estate:

- Self-match is real. `[inner] == [$outer]` includes the outer row unless the authored filter explicitly adds `CurrentRepetition(G) != CurrentRepetition($G)`; the evaluator must not infer self-exclusion. See [`CorrelationLawsTest`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/CorrelationLawsTest.java) and [`OuterCorrelationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/OuterCorrelationDiffTest.kt).
- Filtering precedes consumed-cell classification. A malformed consumed cell in a dropped row is not read; one in a kept row may make the consumer unknown. See [`SelfCorrelatedOverlapQuantifierDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SelfCorrelatedOverlapQuantifierDiffTest.kt) and [`MultiStarFilteredCountDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/MultiStarFilteredCountDiffTest.kt).
- Validation and computation have different consequences inside the filter. Validation unknown drops a candidate because the filter is not true; computation reads contribute to dependency and poison behavior. See [`HavingOverComputedDependencyDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/HavingOverComputedDependencyDiffTest.kt).
- Polarity is not a simple consequence of selected values: filtered quantifiers/comparisons conservatively escalate, while filtered counts have an operand-dependent exception. See [`HavingQuantifierPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/HavingQuantifierPolarityDiffTest.kt), [`HavingStarComparisonPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/HavingStarComparisonPolarityDiffTest.kt), and [`FilteredCountPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FilteredCountPolarityDiffTest.kt).
- Evidence transport must preserve the raw stored condition because formatter/conversion paths are known to lose a `$`-bearing conjunct. A normalized observation artifact must record the actual executed condition rather than trusting display output.

Investigation sequence:

1. **Single-level star and uncorrelated `Having`:** one repeatable group, validation only, explicit candidate-row set, executable enumerator, and filter-before-consumer selection. Prove enumerator/declarative-set agreement and preserve “same-group star means current row” as a checked non-law. Anchor it to [`HavingDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/HavingDiffTest.kt) plus retained portable observations.
2. **Captured-outer `$`:** add reference origin (`inner` or `outer`), field-to-field equality, `CurrentRepetition` comparison, and naive correlated filtering. Prove outer stability, inner locality, selection agreement, and explicit self-exclusion. Reject `$` outside `Having` and a filter with no inner iteration source.
3. **Kept-row observation ordering:** connect phase-aware document reads and prove that a filtered-out consumed cell is outside the consumer's validation read footprint. Lock malformed-kept versus malformed-dropped cases.

Deliberate deferrals: multi-star/cross-subtree generality waits for access plans carrying first-star depth and shared ancestry; hash join waits for a measured optimized consumer and a refinement proof; polarity waits for `FillExtends`; computation overlays/poison wait for computation/read-footprint semantics; partial relevance remains a separate stage. These are different mechanisms, not one `$` feature batch.

## LF4 — Cedar is the primary Lean engineering precedent; Radix is a scoped secondary check

> Date: 2026-07-13. Sections: cross-cutting. Basis: filesystem audit of Cedar specification revision `3977eb4f017b421b7ac0b31ea4635e1dd36ce3ef` and Radix revision `617b67eb09681ca98e19759b48978866dcafeb17`.

Cedar's actual source tree, not merely its project description, is the best default for this repository's Lean engineering shape. `Cedar/Spec` contains ordinary executable semantic definitions with explicit result/error domains and observable short-circuit order; `Cedar/Validation` is separate from execution; `Cedar/Thm` is a recursively aggregated theorem hierarchy; unit tests, symbolic tests, differential interfaces, CLI/FFI, and protobuf transport are separate libraries or executables. Its Lake linter recursively checks that the theorem root imports every proof file. The differential/FFI boundary may use `unsafe` and timing/IO, while the semantics and theorem layers remain pure. Its style guide favors minimal sorted imports, theorem docstrings, explicit types, `simp only` for stable rewrites, and explicit proof steps.

Lean treatment adopted here: keep `Semantics`, `Elaboration`, `Proofs`, and `Conformance` distinct; maintain one mechanically complete proof root; state residual non-success outcomes rather than claiming accepted input cannot fail; keep portable differential transport outside the trusted semantics; and scan the complete transitive theorem dependency closure for trust escapes. This repository's explicit axiom inventory is intentionally stronger than Cedar's import-completeness linter alone.

Radix is useful when a compact technique needs confirmation. Its `BigStep` relation is genuinely independent from its fuel-based interpreter, and it proves fuel monotonicity plus soundness/completeness for successful terminating runs. Its optimization passes pair transformations with forward semantic-preservation theorems. Its top-level `Slides.lean` imports the real Radix library through Verso, so presentation examples elaborate against live code. These are valuable patterns only with their exact limits: the relation omits failure/divergence outcomes, the optimization results are forward preservation rather than unrestricted equivalence, and the slides dependency tracks an unpinned branch in the audited project.

Decision rule: inspect Cedar first for a new Lean architectural or proof-engineering choice. Use Radix to validate a small relational/evaluator/transformation or checked-exposition pattern when Cedar does not provide a compact example. Do not adopt either project's headline theorem counts, dependency choices, or theorem wording without reading the exact source, result domain, and hypotheses.
