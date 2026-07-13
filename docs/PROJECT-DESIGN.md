# a12-kernel-lean — project design

The overall goal is to build `a12-kernel-lean` into the versioned, self-contained mechanized semantics-of-record, executable reference semantics, and navigable body of knowledge for A12's typed validation-and-computation language over hierarchical documents. It should capture conditions and computations—including formal checking, operator- and context-sensitive absence, iteration and correlation, ordered state change, partial validation, and message polarity—with explicit provenance and supported-fragment boundaries; empirically anchor each primitive semantic choice to kernel 30.8.1 through retained differential evidence; prove checked surface-to-core elaboration, evaluator correctness against independently meaningful judgments or traces, and semantics-preserving transformations or optimized implementations; serve as a precise oracle and design reference for independent interpreters; and enable later checked explanations or certificates, rule equivalence, implication, redundancy and overlap analysis, kernel-version delta analysis, and proofs that real rule models establish business invariants—without claiming that finite evidence universally verifies the external kernel or that Lean replaces the shipped implementation.

This document is the project constitution: the decision being made, who the work serves, its semantic boundary, the artifacts and evidence it produces, and the gates by which progress is judged. [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) owns the proposed releasable compatibility-kit boundary and product progression; [`PLAN.md`](PLAN.md) owns the current resumable checkpoint and immediate sequence; [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) owns the detailed theorem contract, case studies, trust discipline, and later publication strategy; [`ARCHITECTURE.md`](ARCHITECTURE.md) owns concrete Lean representations; [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns live clause-level status and evidence gates; read-only [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md) supplies consulted staged guidance rather than a writable project plan.

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
| Retained portable evidence replay and externally exported differentials | Empirical correspondence to kernel 30.8.1 | Pinned own-repository cases, independent kernel observations, and explicit divergence records |
| Kernel and Kotlin ecosystem | Behavioral authority, external probe harness, portable evidence, peer implementation, and production execution | Existing release, integration, fuzz, and operational processes |

The resulting claim classes are deliberately separate:

1. **Semantic coverage:** every in-scope clause has a Lean home or an explicit open/external/unsupported status.
2. **Internal correctness:** the claimed laws and semantic-preservation bridges follow from the chosen Lean theory over their declared fragments.
3. **Kernel correspondence:** primitive choices agree with the observed external engine on retained evidence; this is empirical rather than a universal theorem.

A wrong Lean clause can support flawless proofs, and finite differential testing can miss an input. Confidence comes from connecting the artifacts without claiming that one subsumes the others.

> **Differential doctrine:** Kernel differential testing remains the empirical backbone. Each executable Lean capsule must be checked against retained portable observations from the real kernel; proofs establish internal laws; a12-dmkits contributes knowledge, evidence transport, and clean-room triangulation, but its interpreter is never the oracle.

The recommended differential topology has four roles. [`../../a12-kernel`](../../a12-kernel) is the authoritative behavior. The external a12-dmkits [`adapter/`](../../a12-rulekit/adapter) harness runs focused kernel probes and exports normalized results without becoming a Lean dependency. This repository retains and replays its own typed projections of those portable observations; the sibling [`corpus/`](../../a12-rulekit/corpus) is knowledge and reusable source material, not a live runtime dependency. The a12-dmkits [`interpreter/`](../../a12-rulekit/interpreter) is a secondary clean-room peer for triangulation and divergence discovery, not an oracle; agreement with it cannot override contrary kernel evidence. All three external paths are under the local `a12-rulekit/` checkout.

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

Completed and partial capsule instances are reported in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), with their immediate continuation state in [`PLAN.md`](PLAN.md). They are not repeated here because their evidence counts and exact support boundaries change while this delivery contract should remain stable.

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

The live coverage and adequacy artifact is [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md): it records the supported cells and evidence gaps, while [`PLAN.md`](PLAN.md) orders the immediate work. The durable reason for a distinction belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), the current representation in [`ARCHITECTURE.md`](ARCHITECTURE.md), and kernel behavior remains grounded in the read-only sources indexed by [`SOURCES.md`](SOURCES.md). This prevents the matrix from becoming a second semantics specification or an unreviewed backlog.

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
- Keep Markdown canonical for charter, architecture, semantics, and provenance. User-facing documentation should reuse executable examples and maintained semantic artifacts where that materially prevents drift; [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#128-use-markdown-docstrings-and-verso-for-different-jobs) compares Markdown, docstrings, generated API documentation, Verso, and Blueprint by their natural jobs. No publication tool is a core-library dependency or a new source of truth.

## Success and reevaluation criteria

The project succeeds only when all three claim classes are visible:

- **Coverage:** every in-scope taxonomy/operator clause is implemented or explicitly classified; no silent semantic fallthrough exists.
- **Internal correctness:** the required proof spine is complete for its named fragments, theorem roots have clean reviewed dependencies, and exclusions are documented beside the claim.
- **Kernel correspondence:** the reference evaluator agrees with the pinned retained projections of focused kernel evidence exported through the external adapter harness, with every divergence explicit.
- **Operational discipline:** each semantic capsule closes its evidence, theorem/counterexample, coverage, trust, and build gates before the next layer expands.

The first proof-bearing capsule is also the project's reevaluation point. Continue the full program only if it demonstrates material value beyond the Kotlin interpreter plus tests—such as a useful universal law, a clarified false generalization, a semantics-preserving transformation, or a reusable model-level proof boundary. If it produces only another evaluator and ceremonial `rfl` facts, redesign or stop before reproducing the entire operator surface.

Theorem counts, proof-line counts, zero `sorry`, corpus counts, or evaluator breadth are navigation metrics rather than success criteria. Each can be high while the theorem is weak, the definition is wrong, or the external correspondence is untested.

## Ecosystem role and non-goals

- **[`../../a12-kernel`](../../a12-kernel)** is the behavioral source of truth. This repository reads and probes it under the clean-room boundary but never links, calls, ships, or transliterates it.
- **[a12-dmkits (local `a12-rulekit/` checkout)](../../a12-rulekit)** supplies three non-authoritative facilities with separate jobs: the adapter is the external kernel probe/export boundary, the corpus supplies knowledge and reusable source cases, and the interpreter is a peer clean-room implementation for triangulation. This repository commits its own portable evidence projections for replay. The public a12-dmkits release is dmtool-release.
- **a12-kernel-lean** is the versioned mechanized theory: precise definitions, theorems and counterexamples, a reference evaluator, and an empirical conformance projection.

This project does not claim to verify the external kernel, eliminate empirical testing, make ambiguous clauses correct by typechecking them, prove arbitrary custom oracles well behaved, or justify speculative compilers, extraction, certificates, and production deployment before a consumer requires them.

## Outlook

Once the semantic center and proof spine are credible, the highest-value later uses are:

- checked explanation traces whose acceptance implies a named evaluation judgment;
- proof-producing rule simplification and compilation;
- equivalence outside explicit deltas between versioned kernel-semantics theories;
- domain proofs that validation implies business invariants or computations preserve ranges and conservation laws;
- rule implication, redundancy, overlap, dependency, and repair analyses;
- deeper `$`-correlation semantics and proofs: explicit outer and inner environments, nested or multi-star scope, order-sensitive observation, and refinement from a naive relational account to justified execution plans; [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md#lf3---correlation-requires-two-explicit-environments) records the durable prerequisites and non-laws;
- user-facing explanations that double as regression consumers by reusing executable examples, theorem references, support data, and retained evidence, with the publication mechanism selected for the material rather than prescribed in advance, as described in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#user-facing-documentation-as-a-regression-consumer).

Current evidence counts, supported fragments, and remaining adequacy obligations live in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md). The accepted review checkpoint and exact continuation order live in [`PLAN.md`](PLAN.md). A durable conclusion from completing or failing a capsule belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) or this constitution only when it changes the project method, authority model, success criteria, or long-term decision.
