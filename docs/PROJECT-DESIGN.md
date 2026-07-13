# a12-kernel-lean — project design

The overall goal is to build `a12-kernel-lean` into a self-contained, executable, proof-bearing semantics-of-record and body of knowledge for A12 validation and computation: capture observed behavior precisely, make it a practical reference for independent interpreter implementations and semantic reviews, prove the universal consequences and semantic-preservation results that provide real value beyond testing, keep correspondence with the external kernel empirical and explicitly bounded, preserve the provenance and limits of every claim, reuse established formal-language architectures where they fit, and advance one complete semantic capsule at a time without altering tracked or visible files outside this repository.

This document is the project constitution: the decision being made, who the work serves, its semantic boundary, the artifacts and evidence it produces, and the gates by which progress is judged. [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) owns the detailed theorem contract, case studies, trust discipline, and later publication strategy; [`ARCHITECTURE.md`](ARCHITECTURE.md) owns concrete Lean representations; [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns live clause-level status and evidence gates; read-only [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md) supplies consulted staged guidance rather than a writable project plan.

## Decision

> Preserve the observed A12 30.8.1 validation and computation semantics as a versioned, self-contained mechanized theory: prose explains behavior and provenance; Lean definitions state and execute it; named theorems and counterexamples capture universal consequences and limits; corpus and differential evidence connect that theory empirically to the real kernel.

The project follows the broad operating pattern demonstrated by [Cedar](https://github.com/cedar-policy/cedar-spec): an executable Lean semantic model and proved properties coexist with a separately shipped production engine, while differential evidence checks their correspondence. A12 requires a stricter clean-room adaptation: this repository may replay portable evidence but must never link, call, ship, or transcribe the kernel.

The strategy is **executable-first but not evaluator-only**. A reference evaluator makes each semantic clause concrete; the required proof spine, checked non-laws, provenance, and conformance status are part of completion. This is not “Kotlin again in Lean,” and Lean is not an authority over contrary kernel observations merely because internal theorems have been proved.

The project follows a **reuse-before-invention** discipline. Architecture and proof boundaries should be selected from the audited lessons in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#10-cross-study-findings): Cedar for the separate production-engine/executable-spec/differential shape, `do` Unchained for explicit surface-to-core transformations and preservation, Lean/Lean4Lean for parser–elaborator–theory separation, Verity for visible trust and supported-fragment boundaries, and Radix for compact relational/evaluator/optimization structure and checked exposition. A new mechanism is justified only when these patterns do not fit A12’s semantics or clean-room constraints, and that deviation must be recorded with its reason.

## Users and value

| User | Question this project should answer |
|---|---|
| Semantics maintainer | What exactly does this condition or computation mean, where did that claim come from, and what interactions follow from it? |
| Interpreter implementer | What is the small reference behavior, which edge cases must conform, and which optimizations preserve it? |
| Rule author or domain expert | Are two rules equivalent, does one imply another, can a computation violate a business invariant, and which assumptions bound the answer? |
| Formalization contributor | What is trusted, what is proved, which fragment is supported, and what obligation closes the next semantic slice? |
| Reviewer or auditor | Does a headline such as “sound,” “complete,” or “equivalent” match the exact theorem, result domain, evidence, and external boundary? |

## Scope boundary

The semantic center starts from an expanded model and resolved surface rule, then includes the static legality needed to elaborate that rule into a well-formed core.

| In scope | Initially outside scope |
|---|---|
| Validation conditions and computations | Correctness of the complete bilingual text parser |
| Documents, instantiated rows, formal checking, and phase-sensitive observations | The full structural/MVK diagnostic universe |
| Paths, semantic indices, iteration, correlation, and ordering | Editors, form rendering, workflow, persistence, and wire protocols |
| Kleene truth, directional fillability, verdict polarity, and partial validation | Proving the proprietary kernel implementation correct |
| Computation outcomes, application staging, and read-driven poison | Replacing the shipped Kotlin interpreter or generating a new production runtime |
| Real elaborations and semantics-preserving plans or optimizations | Generic compiler infrastructure without an A12 consumer and proof obligation |

Custom conditions, calendars/timezones, Unicode/regex behavior, and other external facilities remain explicit oracle or host boundaries until their contracts are modeled. The semantic theory is versioned as A12 30.8.1 from its first clause; a later kernel version must not silently change an unqualified meaning.

## Artifact and authority model

Four artifacts answer different questions and must not be collapsed:

| Artifact | Responsibility | What keeps it honest |
|---|---|---|
| [`../spec/`](../spec/) and evidence provenance | Human-readable meaning, rationale, taxonomy, and source trail | Review, kernel findings, and focused probes |
| Lean definitions, judgments, theorems, and counterexamples | Exact executable meaning and universal internal consequences | Elaboration, totality, proof checking, and root-axiom audit |
| Portable corpus replay and externally exported differential evidence | Empirical correspondence to kernel 30.8.1 | Pinned cases, independent kernel observations, and explicit divergence records |
| Kernel and Kotlin ecosystem | Behavioral authority, external probe harness, portable evidence, peer implementation, and production execution | Existing release, integration, fuzz, and operational processes |

The resulting claim classes are deliberately separate:

1. **Semantic coverage:** every in-scope clause has a Lean home or an explicit open/external/unsupported status.
2. **Internal correctness:** the claimed laws and semantic-preservation bridges follow from the chosen Lean theory over their declared fragments.
3. **Kernel correspondence:** primitive choices agree with the observed external engine on retained evidence; this is empirical rather than a universal theorem.

A wrong Lean clause can support flawless proofs, and finite differential testing can miss an input. Confidence comes from connecting the artifacts without claiming that one subsumes the others.

> **Differential doctrine:** Kernel differential testing remains the empirical backbone. Each executable Lean capsule must be checked against retained portable observations from the real kernel; proofs establish internal laws; a12-dmkits contributes knowledge, evidence transport, and clean-room triangulation, but its interpreter is never the oracle.

The recommended differential topology has four roles. [`../../a12-kernel`](../../a12-kernel) is the authoritative behavior. The external a12-dmkits [`adapter/`](../../a12-rulekit/adapter) harness runs focused kernel probes and exports normalized results without becoming a Lean dependency. Its [`corpus/`](../../a12-rulekit/corpus) is the portable replay boundary for this repository. Its [`interpreter/`](../../a12-rulekit/interpreter) is a secondary clean-room peer for triangulation and divergence discovery, not an oracle; agreement with it cannot override contrary kernel evidence. All three paths are under the local `a12-rulekit/` checkout.

This differential topology is the required way to anchor primitive semantic choices. For each new clause, prefer a small own-domain witness executed by a kernel-facing harness outside this repository, compare the kernel result independently with the clean-room interpreter where useful, retain the observable result and kernel version as portable evidence, and replay the supported projection against Lean. A mismatch is a finding to resolve at the semantic definition, never a tolerance to hide. Proofs establish universal consequences of the chosen Lean definitions; differentials establish empirical correspondence on retained observations; fuzzing broadens the search for missed observations. None substitutes for the others. Codex may run the sibling harness and write its already-ignored build/cache outputs, but never alter or leave visible files in the sibling worktree; tracked corpus generation must be redirected to an ignored disposable workspace before portable evidence is copied here.

## Delivery unit: the semantic capsule

The unit of progress is a **semantic capsule**, not a batch of evaluator branches. Every completed capsule contains:

1. the owning `§n` clause, kernel version, provenance, and support boundary;
2. the smallest necessary core representation and static legality rule;
3. a total pure executable definition with read order preserved where the phase semantics and evidence make it observable;
4. ordinary, boundary, empty, malformed, and order-sensitive examples as applicable;
5. every matching portable conformance case and retained external evidence;
6. a useful general theorem when one exists, with exact hypotheses and result domain;
7. the nearest plausible false generalization as a checked counterexample;
8. updated clause coverage, trusted-root audit, focused elaboration, and a green build.

A slice that misses an applicable obligation is `partial` and records the missing work. In particular, an implemented and proved capsule without retained portable kernel observations is internally closed but remains `external evidence pending`; it must not be described as kernel-correspondence complete. The full definition of done and proof spine live in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md).

Capsule 5a and the externally observed 5b/5c core demonstrate this distinction. Capsule 5a has closed both sides for its narrow one-group validation truth fragment: ordered candidates, uncorrelated row-local `Having`, selected numeric sum, an exact relation bridge, filter-before-consumer theorem, checked current-row-collapse non-law, and seven retained kernel observations. Capsules 5b/5c contribute explicit captured outer and candidate environments, filter-only inner/outer origins, origin-presence checking, naive correlated selection, a separately supplied guard and starred consumer, and a proof of their validation-observation footprint. Twelve retained correlation observations across seven models cover direction `[2,3]`, self-match `[1,2,3]`, excluded distinct `[]`, excluded duplicates `[1,2]`, all-valid consumers `[1,2]`, first malformed consumer `[1]`, second malformed consumer `[2]`, `empty=zero` `[1,2]`, malformed-local `[2,3]`, numeric `!=` `[1,2]`, repetition `==` `[2]`, and repetition `<` `[2,3]`; all three engines agree. The observations preserve OMISSION but replay only firing membership, restored to the projection's document-row order, because filtered-result polarity and external kernel emission ordering remain outside the claim. The focused witness set closes the five previously named correlation evidence gaps at that projection; it is not a Cartesian operator/state matrix and says nothing yet about the repeatable authoring or general execution surface.

## Planning high-complexity operator families

The operator surface is planned as a matrix of consuming clauses, not as a checklist of operator names and not as a global type-dispatch table. [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function) demonstrates why: even empty-input behavior varies by kind baseline, operator and operand position, enclosing consumer, field role, phase, row eligibility, and result polarity.

Before implementing an operator family, create a compact evidence inventory with these dimensions:

| Dimension | Question that must be answered |
|---|---|
| Input state | Clean empty, filled valid, formally invalid, contextual finding, missing row, or unresolved lookup? |
| Kind and role | What is the field/value kind, and is the field ordinary, required, index, computed, or otherwise model-derived? |
| Operator slot | Which operator consumes the value, and does subject/entry/left/right/starred position change treatment? |
| Selection | Is the operand scalar, repeated, filtered, skipped, or part of an all-empty selection with its own identity? |
| Consumer and phase | Is the result used by validation comparison, concatenation, aggregation, computation, or the store boundary, under validation or computation reads? |
| Observable result | Does it produce a value with fillability provenance, not-evaluated, false, unknown, poison, VALUE/OMISSION, CLEARED, or ERRORED? |

Preparation follows six rules. First, cluster operators by shared semantic mechanism confirmed in source and probes—comparison, conversion, fold, predicate, lookup, or store—not by surface naming alone. Second, mark every matrix cell as verified, inferred, contradictory, or unknown; unknown never silently inherits a convenient default. Third, design paired separating witnesses that hold the kind and document fixed while varying exactly one axis, such as String comparison versus `Length`, or `FieldValueAsString` in comparison versus concatenation versus assignment. Fourth, choose an intermediate result domain that preserves the distinction the next consumer observes, including no-value, not-check-relevant/poison, and given-versus-substituted provenance. Fifth, state the smallest useful law and the nearest false generalization before broadening the evaluator. Sixth, finish the capsule vertically—legality, execution, differential replay, theorem/counterexample, coverage, and trust audit—before opening the next mechanism.

This method deliberately avoids a speculative universal operator framework. Repeated structure may be factored only after at least two completed capsules expose the same law and result domain. The first implementation stays direct and named; an optimized table, generic fold, or compiled evaluator becomes a separate refinement target only when a real consumer and preservation theorem justify it. Cedar's executable-spec/validation/theorem separation is the default project shape, while Radix's evaluator/relation and transformation-preservation patterns are used only where their narrower proof form fits.

The planning artifact is [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md): it records the live supported cells and evidence gaps. The durable reason for a distinction belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), the current representation in [`ARCHITECTURE.md`](ARCHITECTURE.md), and kernel behavior remains grounded in the read-only sources indexed by [`SOURCES.md`](SOURCES.md). This prevents the matrix from becoming a second semantics specification or an unreviewed backlog.

## Milestones and gates

Development proceeds in vertical slices, using the baseline order and traps in read-only [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md), with current dispositions recorded in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and durable changes of treatment in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).

1. **Foundations:** align values, verdict algebra, checked cells, documents, environment, world, and theorem vocabulary.
2. **First proof-bearing capsule:** flat conditions and phase-aware invalid-cell suppression, including engine-backed examples, algebra/information-order laws, an evaluator/judgment or trace bridge where useful, and one generated-rule desugaring proof.
3. **Elaboration, paths, and iteration:** well-formed core rules, explicit rejection, required/index expansion, path resolution, semantic indices, star binding, and declarative context sets.
4. **Computation:** outcomes, precondition cascade, poison-on-read, stored-form application, implicit validation, and read-footprint noninterference.
5. **Whole-rule guarantees:** directional polarity, partial-validation soundness, supported-fragment relations, and reference/optimized refinement where an optimized consumer exists.
6. **Analyses and real models:** rule equivalence, implication, redundancy, overlap, dependency, version deltas, and model-specific business invariants.

Breadth does not advance a milestone while the current slice lacks its evidence, theorem/counterexample obligation, coverage entry, or trust gate. A relation or trace semantics is added when it exposes meaningful steps or provides an independent refinement target, not as ceremonial duplication of the evaluator.

## Trust, dependency, and publication policy

- Maintain one trusted theorem root importing every trusted proof module; mechanically check its coverage and transitive axioms.
- Reject active `sorry`, unclassified project axioms, `unsafe`, `partial`, and `native_decide` from the trusted closure. Experimental work stays outside that import graph.
- Distinguish successful-run soundness, failure behavior, termination, completeness, forward preservation, and equivalence in theorem names and coverage records.
- Keep the executable core dependency-free while that remains economical. Add a separate version-pinned Mathlib proof target when mature theory is cheaper and safer than rebuilding it.
- Keep external clocks, custom hooks, regex/Unicode facilities, and host failures explicit; purity alone does not imply locality or monotonicity.
- Keep Markdown canonical for charter, architecture, semantics, and provenance. The deferred, version-pinned Verso handbook, Radix-style checked slides, API documentation, and eventual Blueprint projection are described in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md); none is a current core dependency or a new source of truth.

## Success and reevaluation criteria

The project succeeds only when all three claim classes are visible:

- **Coverage:** every in-scope taxonomy/operator clause is implemented or explicitly classified; no silent semantic fallthrough exists.
- **Internal correctness:** the required proof spine is complete for its named fragments, theorem roots have clean reviewed dependencies, and exclusions are documented beside the claim.
- **Kernel correspondence:** the reference evaluator agrees with the pinned replayable corpus and focused kernel evidence exported through the external adapter harness, with every divergence explicit.
- **Operational discipline:** each semantic capsule closes its evidence, theorem/counterexample, coverage, trust, and build gates before the next layer expands.

The first proof-bearing capsule is also the project's reevaluation point. Continue the full program only if it demonstrates material value beyond the Kotlin interpreter plus tests—such as a useful universal law, a clarified false generalization, a semantics-preserving transformation, or a reusable model-level proof boundary. If it produces only another evaluator and ceremonial `rfl` facts, redesign or stop before reproducing the entire operator surface.

Theorem counts, proof-line counts, zero `sorry`, corpus counts, or evaluator breadth are navigation metrics rather than success criteria. Each can be high while the theorem is weak, the definition is wrong, or the external correspondence is untested.

## Ecosystem role and non-goals

- **[`../../a12-kernel`](../../a12-kernel)** is the behavioral source of truth. This repository reads and probes it under the clean-room boundary but never links, calls, ships, or transliterates it.
- **[a12-dmkits (local `a12-rulekit/` checkout)](../../a12-rulekit)** supplies three non-authoritative facilities with separate jobs: the adapter is the external kernel probe/export boundary, the corpus is portable replay evidence, and the interpreter is a peer clean-room implementation for triangulation. Its public release is dmtool-release.
- **a12-kernel-lean** is the versioned mechanized theory: precise definitions, theorems and counterexamples, a reference evaluator, and an empirical conformance projection.

This project does not claim to verify the external kernel, eliminate empirical testing, make ambiguous clauses correct by typechecking them, prove arbitrary custom oracles well behaved, or justify speculative compilers, extraction, certificates, and production deployment before a consumer requires them.

## Outlook

Once the semantic center and proof spine are credible, the highest-value later uses are:

- checked explanation traces whose acceptance implies a named evaluation judgment;
- proof-producing rule simplification and compilation;
- equivalence outside explicit deltas between versioned kernel-semantics theories;
- domain proofs that validation implies business invariants or computations preserve ranges and conservation laws;
- rule implication, redundancy, overlap, dependency, and repair analyses;
- the continuing `$` correlation program: single-level star/uncorrelated `Having`, captured-outer correlation, kept-row observation ordering, and the focused firing-membership witness set have landed; repeatable checked elaboration and diagnostics come next, before `Document` adaptation, broader repetition generalization, and later optimized-refinement work; [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md#lf3--correlation-requires-two-explicit-environments) records the prerequisites, differentials, proof obligations, checked non-laws, and deliberate deferrals;
- a checked Verso semantics handbook, presentation decks importing the live theory, and a Blueprint view of provenance, theorem dependencies, and progress.

## Reevaluation and immediate next step

The first capsule demonstrates value beyond a second evaluator: it has an exact information order replacing a false monotonicity slogan, a closed base-finding type that prevents requiredness from entering the wrong stage, a non-circular two-pass required transformation, universal computation-preservation and algebra laws, and checked counterexamples. Its primitive clauses are supported by focused kernel-backed law and differential tests in a12-dmkits. The external harness may be run from the local `a12-rulekit/` checkout with outputs redirected entirely into already-ignored paths; portable correspondence remains scoped to the retained and replayed own-domain observation bundle.

The smallest checked elaboration and normalized path-resolution slice is now internally closed: explicit model validation and order-independent lookup, fail-closed scalar/path rejection, a proof-bearing `CheckedFlatCondition`, model-derived formal checking, context-coherence theorems, rejected cases, scope documentation, trusted-root coverage, and internal conformance locks are present. It deliberately covers only structured absolute, plain parent-relative, and bare non-repeatable references; it does not claim complete §10 syntax.

The retained external-evidence gate now replays 38 focused kernel 30.8.1 observations through three closed typed projections with `lake test`: 36 runtime cases and two diagnostics, comprising 19 flat/path/required runtime-or-diagnostic cases, seven uncorrelated-iteration cases, and twelve captured-outer correlation cases. The path probes falsified the earlier ancestor-tier assumption and drove the root correction recorded in [`LF6`](LEAN-FINDINGS.md#lf6--bare-name-resolution-is-local-or-global-not-an-ancestor-walk). Across seven models, the correlation cases preserve their actual executed stored `$` conditions and separate direction `[2,3]`, self-match `[1,2,3]`, excluded distinct `[]`, excluded duplicates `[1,2]`, all-valid consumers `[1,2]`, first malformed consumer `[1]`, second malformed consumer `[2]`, `empty=zero` `[1,2]`, malformed-local `[2,3]`, numeric `!=` `[1,2]`, repetition `==` `[2]`, and repetition `<` `[2,3]`. Groovy-dynamic, static-Java, and the a12-dmkits interpreter agree on all twelve. The driver also resolves each authored absolute-or-relative condition path and the error field against the retained model before requiring exact condition equality; this strengthens evidence binding without claiming general repeatable elaboration.

Iteration capsule 5a remains closed for its narrow truth fragment: it models ordered explicit instantiated rows for one repeatable group, optional uncorrelated row-local `Having`, keep-iff-fired filtering, and validation-only numeric `Sum` as a truth-`K` selection observer. Its exact ordered `SelectRows` bridge and filter-before-consumer theorem apply Cedar's executable-slice/reachability pattern without introducing a speculative general framework; the checked neighboring non-law rejects current-row collapse. Seven retained observations cover unfiltered and filtered sums, firing and silent boundaries, empty selection, invalid-filter drop, and invalid-consumer drop/keep.

Correlation capsules 5b and 5c are internally implemented at their deliberately narrow boundary. `CapturedSingleGroupContext` holds the explicit outer row; each candidate supplies the inner row; `HavingOrigin` exists only inside `CorrelatedHaving`; and `OriginCheckedCorrelatedHaving` proves only that both origins occur. Number equality, inequality, and less-than plus structural repetition comparison execute as a naive ordered nested loop. Numeric empty comparison uses zero, invalid filter operands are unknown and drop, and `CurrentRepetition` reads the 1-based structural row. `evalSelectedAnyFilled` applies the starred-presence consumer only after selection; `evalGuardedAnyFilledOn` takes a separately supplied outer guard without requiring it to differ from the consumer; `firingRowsOn` retains ordered outer results. The retained 5c fixtures deliberately use a distinct valid guard to isolate consumer behavior. The footprint theorem states equality at the validation-observation boundary, not raw-cell identity or polarity. Twelve retained cases close the external gate for the admitted direction, self-match/self-exclusion, selected-consumer, empty/malformed filter, numeric comparison, and repetition comparison shapes at firing membership.

The next step is repeatable checked elaboration and diagnostics for the admitted single-group fragment, including field/path/equality-scale legality. This stage must land before `Document` adaptation or broader repetition generalization. Filtered-result polarity, `Document` adaptation, nested/multi-star and cross-group behavior, hash-join optimization/refinement, computation, partial validation, and general consumers remain deliberately deferred. The legal kernel precision witness also remains open because it reaches scale 20 through arithmetic; the direct rescaling examples are internal helper laws, not external whole-rule evidence.
