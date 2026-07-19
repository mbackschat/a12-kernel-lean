# a12-kernel-lean — project design

The overall goal is to build `a12-kernel-lean` into the versioned, self-contained mechanized semantics-of-record, executable reference semantics, and navigable body of knowledge for A12's typed validation-and-computation language over hierarchical documents. It should capture conditions and computations—including formal checking, operator- and context-sensitive absence, iteration and correlation, ordered state change, partial validation, and message polarity—with explicit provenance and supported-fragment boundaries; empirically anchor each primitive semantic choice to kernel 30.8.1 through retained differential evidence; prove checked surface-to-core elaboration, evaluator correctness against independently meaningful judgments or traces, and semantics-preserving transformations or optimized implementations; and act as a semantics factory that turns this knowledge into purpose-specific, versioned, research-closed shipments across execution, translation, transformation, compilation, analysis, verification, synthesis, qualification, explanation, and governance. Concrete consumers include independent evaluators in any implementation language, importers from explicitly versioned external subsets such as JSON Schema, A12 rule-analysis and rule-refactoring tools, checked explanations and certificates, kernel-version delta and migration tools, and proofs that real rule models establish business invariants. Every downstream capability must declare its source and target fragments, observable projection, unsupported cases, and exact claimed relation; none is implied by the current implementation, creates kernel evidence by itself, or may bypass or weaken closure of the semantic clauses on which it depends.

This document is the project constitution: it owns the durable decision, users, semantic boundary, artifact and evidence doctrine, delivery model, coverage horizons, and success criteria. The canonical documentation registry is [`README.md`](README.md). In particular, proposed product scope belongs in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md), live coverage and sequencing in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and [`PLAN.md`](PLAN.md), and concrete proof and encoding practice in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) and [`ARCHITECTURE.md`](ARCHITECTURE.md). Project-owned [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md) remains consulted staged guidance rather than a plan or implementation-status surface.

## Decision

> Preserve the observed A12 30.8.1 validation and computation semantics as a versioned, self-contained mechanized theory: prose explains behavior and provenance; Lean definitions state and execute it; named theorems and counterexamples capture universal consequences and limits; corpus and differential evidence connect that theory empirically to the real kernel.

The project follows the broad operating pattern demonstrated by [Cedar](https://github.com/cedar-policy/cedar-spec): an executable Lean semantic model and proved properties coexist with a separately shipped production engine, while differential evidence checks their correspondence. A12 requires a stricter clean-room adaptation: this repository may replay portable evidence but must never link, call, ship, or transcribe the kernel.

The strategy is **executable-first but not evaluator-only**. A reference evaluator makes each semantic clause concrete; the required proof spine, checked non-laws, provenance, and conformance status are part of completion. This is not “Kotlin again in Lean,” and Lean is not an authority over contrary kernel observations merely because internal theorems have been proved.

Independent evaluators are the first product-shaped consumer profile of the theory, not its exclusive purpose. The reusable asset is the versioned semantics, evidence account, theorem vocabulary, and checked boundary. An importer, analyzer, refactoring tool, optimizer, or certificate checker becomes a project capability only over named closed fragments and with a concrete consumer contract and proof obligation; being written in Lean or calling the reference evaluator is not itself a correctness argument.

The project follows a **reuse-before-invention** discipline. Architecture and proof boundaries should be selected from the audited lessons in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#10-cross-study-findings): Cedar for the separate production-engine/executable-spec/differential shape, `do` Unchained for explicit surface-to-core transformations and preservation, Lean/Lean4Lean for parser–elaborator–theory separation, Verity for visible trust and supported-fragment boundaries, and Radix for compact relational/evaluator/optimization structure and checked exposition. A new mechanism is justified only when these patterns do not fit A12’s semantics or clean-room constraints, and that deviation must be recorded with its reason.

## Users and value

| User | Question this project should answer |
|---|---|
| Semantics maintainer | What exactly does this condition or computation mean, where did that claim come from, and what interactions follow from it? |
| Interpreter implementer | What is the language-neutral decision procedure, which edge cases and non-laws must conform, which optimizations preserve it, and can I implement it without repeating kernel research? |
| Importer or rule-tool implementer | Which source and A12 fragments are supported, what mapping or transformation relation is guaranteed, what is rejected or approximated, and what checker or certificate establishes the result? |
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

The semantic center remains the expanded A12 model, resolved rule, document, and world. An external format such as JSON Schema is not silently promoted to A12 core syntax: a future importer is a separately versioned transformation from a named source dialect and subset into an already supported A12 fragment. Likewise, rule refactoring operates over checked A12 artifacts unless concrete parsing and rendering preservation are modeled separately. General JSON Schema validation, remote reference acquisition, arbitrary dialect support, editor integration, and full-fidelity concrete-syntax round trips remain outside scope unless a concrete consumer and theorem explicitly bring them in.

## Artifact and authority model

Four artifacts answer different questions and must not be collapsed:

| Artifact | Responsibility | What keeps it honest |
|---|---|---|
| [`../spec/`](../spec/) | Human-readable meaning, rationale, taxonomy, and cross-project semantic bridge | Review, kernel findings, and focused probes |
| Lean definitions, judgments, theorems, and counterexamples | Exact executable meaning and universal internal consequences | Elaboration, totality, proof checking, and root-axiom audit |
| Retained portable evidence replay and externally exported differentials | Empirical correspondence to kernel 30.8.1 | Pinned own-repository cases, externally captured cross-route kernel observations, and explicit divergence records |
| Kernel and Kotlin ecosystem | Behavioral authority, external probe harness, portable evidence, peer implementation, and production execution | Existing release, integration, fuzz, and operational processes |

[`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md) records reconciliation of spec changes into a12-dmkits. It transports reviewed semantic changes and retains their revision receipts; it is not evidence that keeps a semantic claim honest.

[`ARTIFACTS.md`](ARTIFACTS.md) projects this authority model onto the repository's concrete scenario-question, `evidence/`, `reference/`, `examples/`, and `qualification/` trees and defines how each is authored, retained, generated, checked, versioned, or kept transient.

The resulting claim classes are deliberately separate:

1. **Semantic coverage:** every in-scope clause has a Lean home or an explicit open/external/unsupported status.
2. **Internal correctness:** the claimed laws and semantic-preservation bridges follow from the chosen Lean theory over their declared fragments.
3. **Kernel correspondence:** primitive choices agree with the observed external engine on retained evidence; this is empirical rather than a universal theorem.

A wrong Lean clause can support flawless proofs, and finite differential testing can miss an input. Confidence comes from connecting the artifacts without claiming that one subsumes the others.

> **Differential doctrine:** Kernel differential testing remains the empirical backbone. Related executable Lean clauses are calibrated against retained portable observations from the real kernel; proofs establish internal laws; a12-dmkits contributes knowledge, current corpus/differential facilities, historical certified evidence, and clean-room triangulation, but its interpreter is never the oracle. A capsule may land internally with `external evidence pending`; that status must be closed before a kernel-correspondence or shipment-ready claim.

The differential topology has four roles. [`../../a12-kernel`](../../a12-kernel) is the authoritative behavior. Current a12-dmkits `main` supplies source-maintained ordinary kernel probes, corpus capture/replay, differential tests, knowledge, and clean-room triangulation; it no longer contains the retired portable capture V1 producer. This repository retains three compact observation bundles behind one operation-neutral reader and small typed family projections. The direct-cascade bundle is producer-certified by historical exporter revision `1b5f463b89adc6cfb81b41121cd6c97855e8cbe3`; the root-String and validation bundles are project-reviewed migrations whose complete old/new agreement and raw recovery identities live in their named archives. Ordinary Lean replay checks the compact semantic claims and does not re-audit the historical raw units. This repository never implements missing instrumentation in a copied a12-dmkits tree or re-implements a producer's packet audit for a new capsule. The sibling [`corpus/`](../../a12-rulekit/corpus) is knowledge and reusable source material, not a live runtime dependency. The a12-dmkits [`interpreter/`](../../a12-rulekit/interpreter) is a secondary clean-room peer for triangulation and divergence discovery, not an oracle; agreement with it cannot override contrary kernel evidence. All three external paths are under the local `a12-rulekit/` checkout.

This differential topology is the required way to anchor primitive semantic choices. For each calibrated family, prefer a small own-domain witness executed by a fit-for-purpose source-maintained kernel-facing command outside this repository, compare the kernel result independently with the clean-room interpreter where useful, retain the observable result and kernel version as portable evidence, and replay the supported typed projection against Lean. A mismatch is a finding to resolve at the semantic definition, never a tolerance to hide. Proofs establish universal consequences of the chosen Lean definitions; differentials establish empirical correspondence on retained observations; fuzzing broadens the search for missed observations. None substitutes for the others. Codex may run an unchanged sibling command and write only its caller-selected ignored outputs, but never alter or leave visible files in the sibling worktree. Use a12-dmkits' current corpus/differential facilities when the required observation shape fits. If it does not, send a specific demand-driven upstream improvement request and mark the capsule `external evidence pending`; never resurrect portable capture V1, patch a disposable source copy, or assume that a generic successor exists. The accepted historical first-client instance remains active only as a compact [`string-direct-cascade-v1` observation bundle](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/semantic-observations.json); its complete raw answer is recoverable from the [project archive](archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md), its producer history is archived in a12-dmkits' [`capture proposal`](../../a12-rulekit/docs/archived/A12-DMKITS-CAPTURE-PROPOSAL.md), and the accepted [`compact semantic-evidence plan`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) owns the settled three-bundle boundary and future scaling limits.

The assurance cadence has three tiers. Ordinary semantic development closes the executable clause, proof spine, counterexample, assumptions, and status without waiting for a new producer facility. Family calibration later closes `external evidence pending` through compact retained observations from an existing suitable route or an accepted purpose-specific handback. Full protocol, candidate, mutation, packaging, and release qualification runs only for a real shipment or consumer. This keeps the empirical backbone while preventing evidence infrastructure from dominating semantic work.

Infrastructure is retained by current responsibility, not by sunk cost. A process or evidence component remains live only when a current semantic family or consumer depends on it, when it uniquely guards a still-relevant failure class, or when accepted current state cannot otherwise be reproduced. Exact retained artifacts plus a pinned last reproducing revision are sufficient history for a completed one-off experiment; its generator, campaign runner, and qualification machinery need not remain on `main`. Shared infrastructure must amortize across semantic families, stay smaller than the semantic work it enables, and have an explicit retirement path when superseded. A capsule that starts growing a new packet vocabulary, registry, receipt audit, compatibility adapter, or qualification framework fails this design test and must return to the settled compact observation boundary.

## Delivery unit: the semantic capsule

The unit of progress is a **semantic capsule**, not a batch of evaluator branches. Every completed capsule contains:

1. the owning `§n` clause, kernel version, provenance, and support boundary;
2. the smallest necessary core representation and static legality rule;
3. a total pure executable definition with read order preserved where the phase semantics and evidence make it observable;
4. ordinary, boundary, empty, malformed, and order-sensitive examples as applicable;
5. every currently available matching portable conformance case, with missing external observation stated explicitly as `external evidence pending`;
6. a useful general theorem when one exists, with exact hypotheses and result domain;
7. the nearest plausible false generalization as a checked counterexample;
8. updated clause coverage, trusted-root audit, focused elaboration, and a green build.

A slice that misses an applicable obligation is `partial` and records the missing work. In particular, an implemented and proved capsule without retained portable kernel observations is internally closed but remains `external evidence pending`; it must not be described as kernel-correspondence complete. [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#12-required-proof-spine) supplies the formal proof spine, and [`TESTING.md`](TESTING.md#capsule-test-checklist) turns this delivery contract into the operational checklist.

Completed and partial capsule instances are reported in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), with their immediate continuation state in [`PLAN.md`](PLAN.md). They are not repeated here because their evidence counts and exact support boundaries change while this delivery contract should remain stable.

## Consumer shipments and research closure

A **semantic capsule** is the internal unit that closes one part of the theory and its evidence. A **semantic shipment** is a versioned, purpose-specific projection of one or more closed capsules for an independent consumer. The shipment carries a closed capability identity, language-neutral model, task contract, examples, evidence limits, laws and non-laws, and qualification surface. It is not a generated downstream implementation and it is not automatically a public release.

A **consumer probe** is the earlier, deliberately bounded use of current semantic material against one concrete task. It asks whether the definitions, examples, laws/non-laws, evidence limits, and exclusions are understandable and sufficient for that task; it may be an artifact-only isolated readback or, with separate approval, a small external prototype. A probe is allowed to fail by returning a missing distinction, unusable boundary, new use case, or evidence need. It is not a shipment, qualification, support claim, roadmap commitment, or product.

```text
semantic capsules → consumer probe → research-closed shipment → cold qualification → optional product
        ↑                |
        +-- gaps, corrections, and newly discovered potential
```

The factory centralizes reusable A12 research, retains portable kernel evidence, states the chosen account in Lean, proves internal consequences, and generates checked consumer artifacts. A probe tests usefulness before the project commits to productionizing that path. A later shipment lets an independent consumer implement or apply a research-closed capability without repeating kernel archaeology. A discovered semantic gap returns to this repository; its resolution changes the owning semantics and any affected shipment identity rather than becoming undocumented private behavior in one downstream tool.

The portable shipment contains the common semantic foundation, the exact capability projection, and a task profile naming the operation, source and target fragments, observable relation, exclusions, evidence limits, and applicable task interface. Language/runtime integration is a separate implementation profile, and the exact revision, commands, mutations, logs, and results form a separate candidate qualification record. Moving an evaluator from Rust to Python does not change its normative task, although each host boundary still needs explicit treatment; moving from evaluation to import or refactoring changes the task profile itself. Consumer-specific qualification can test a shipment but must never redefine its portable semantics.

The proposal organizes the broader potential into **Execute, Translate, Transform, Compile, Analyze, Verify, Synthesize, Qualify, Explain, and Govern**; [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#general-consumer-task-categories) owns that product taxonomy and [`USE-CASES.md`](USE-CASES.md) explains it for users. Evaluators are the first concrete profile. JSON Schema import and rule refactoring are important future examples, but their detailed source/target, preservation, and qualification obligations belong in [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) and do not constitute current support.

The shipment-readiness gate is **research closure**: every observable branch required by the task profile is either determined with provenance or rejected explicitly; its decision procedure or transformation relation, checked examples, evidence limits, theorem/non-law boundary, applicable task interface, and support declaration agree; and no downstream step delegates semantic archaeology to the consumer. Internal Lean work may be partial before that shipment exists, but an unresearchable gap keeps it out of the shipment-ready set. Product and production-release gates remain additional decisions owned by [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) and [`PRODUCTION-RELEASE.md`](PRODUCTION-RELEASE.md).

Shipment adequacy is tested with a **cold consumer exercise**: an isolated developer receives only the shipment and a normal toolchain and must complete and qualify its named task without kernel, a12-dmkits, or undocumented conversation context. Needing fresh A12 research, guessing an undocumented branch, or merely translating Lean syntax is a shipment failure; success validates knowledge transport only for the pinned shipment and executed checks and creates no new kernel evidence. [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#cold-consumer-gate) owns the exact task-specific procedure, candidate qualification record, learning feedback, and attestation limits.

[`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) owns the detailed shipment contents, implementation/qualification split, research-closure checklist, cold-consumer gate, downstream playbooks, and disagreement protocol. [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) is the first high-complexity evaluator-shipment design spike, while [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) owns the first executed isolated evaluator experiment. Both keep their remaining evidence, differential, and cold-qualification gaps explicit rather than treating runnable tooling as automatic release closure. Importer and refactoring profiles remain future capabilities until a concrete selected fragment, consumer, evidence plan, and preservation obligation are adopted.

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

Preparation follows six rules. First, cluster operators by shared semantic mechanism confirmed in source and probes—comparison, conversion, fold, predicate, lookup, or store—not by surface naming alone. Second, mark every matrix cell as verified, inferred, contradictory, or unknown; unknown never silently inherits a convenient default. Third, design paired separating witnesses that hold the kind and document fixed while varying exactly one axis, such as String comparison versus `Length`, or `FieldValueAsString` in comparison versus concatenation versus assignment. Fourth, choose an intermediate result domain that preserves the distinction the next consumer observes, including no-value, not-check-relevant/poison, and the exact provenance required downstream: symmetric given-versus-substituted flags where sufficient, but directional `canGrow`/`canShrink` whenever polarity depends on which fill could falsify a firing. Fifth, state the smallest useful law and the nearest false generalization before broadening the evaluator. Sixth, finish the capsule vertically—legality, execution, theorem/counterexample, coverage, trust audit, available differential replay, and honest evidence status—or cleanly exit a bounded risk spike under the contract below before opening the next mechanism. The next completed capsule may deliberately cross to another semantic family when that supplies the most informative second consumer.

This method deliberately avoids a speculative universal operator framework. Repeated structure may be factored only after at least two completed capsules expose the same law and result domain. The first implementation stays direct and named; an optimized table, generic fold, or compiled evaluator becomes a separate refinement target only when a real consumer and preservation theorem justify it. Cedar's executable-spec/validation/theorem separation is the default project shape, while Radix's evaluator/relation and transformation-preservation patterns are used only where their narrower proof form fits.

The live coverage and adequacy artifact is [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md): it records the supported cells and evidence gaps, while [`PLAN.md`](PLAN.md) owns the current spiral. Language-neutral kernel behavior belongs in the project-owned [`../spec/`](../spec/) body and remains grounded in the sources indexed by [`SOURCES.md`](SOURCES.md); every outbound semantic change is tracked in [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md). The durable reason for a Lean distinction belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and the current representation in [`ARCHITECTURE.md`](ARCHITECTURE.md). This prevents the implementation matrix from becoming a second semantics specification or an unreviewed backlog.

## Controlled interleaving and coverage horizons

Development uses a controlled spiral across semantic frontiers rather than completing one entire domain before touching the next. A12's difficult behavior is cross-cutting: absence, formal invalidity, polarity, paths, repetition, computation poison, application, and messages meet at consuming clauses. A long numeric-only or validation-only tunnel can therefore produce locally elegant definitions that overfit one consumer and fail late when computation, repetition, or another value kind needs a different distinction.

Interleaving reduces three risks. It tests an abstraction early through a materially different second consumer, reveals integration gaps while the first mechanism is still cheap to change, and makes duplicated concepts visible before they become separate frameworks. It also has costs: context switching, many superficially partial surfaces, premature reuse of a wrong abstraction, and pressure to publish unstable fragments. The controls are therefore part of the method, not optional scheduling advice.

Once a frontier has a minimum ordinary baseline—a named value, context, consuming clause, and result path whose internal gates are closed—the next unit of work should normally attack that frontier's highest semantic risk before routine breadth accumulates. The baseline is deliberately small: “basics first” does not mean completing every easy operator in the topic. A completed capsule may already supply it and must be reused rather than recreated to satisfy the schedule. The default rhythm is **minimum baseline → separating risk spike → representation review → routine breadth or next frontier**, but this is a selection heuristic rather than a quota that every frontier must mechanically repeat.

Risk is assessed qualitatively from three factors: **uncertainty**, meaning that multiple plausible semantic accounts remain; **downstream impact**, meaning that the choice affects several consumers, proofs, or transformations; and **representation pressure**, meaning that the answer could change a core result, context, provenance, or state-transition type rather than merely add another case. Prerequisite and evidence readiness are hard constraints rather than a fourth score: a difficult topic is not yet a ready spike if its separating witness cannot be interpreted from already closed foundations. This is a judgment rule, not a numeric score, backlog taxonomy, or new governance artifact.

A risk spike is a bounded semantic investigation, not a partially implemented feature. It starts by naming the competing accounts and the smallest witness that separates them. Lean implementation begins only when the existing source or retained-observation basis is sufficient to choose an account; otherwise the spike ends as a read-only analysis recorded once, with no experimental code. A spike has exactly three acceptable exits: close the result as an ordinary proof-bearing capsule; record the exact unresolved alternatives and required discriminator while removing experimental code; or correct the underlying representation and re-close every affected gate before continuing. Re-closing after a representation change includes auditing theorem statements, hypotheses, directions, result domains, and nearest non-laws rather than relying on a green build. Difficulty, novelty, and implementation size alone do not justify a spike.

Evidence status is transitive but not all uncertainty is equal. A source-grounded semantic choice that lacks portable replay may support later internal work, whose correspondence status remains `external evidence pending`. An unresolved choice that could change a result or representation may not be inherited at all; dependent work on that branch remains blocked until the discriminator closes it.

1. Only one capsule or risk spike is active at a time; finish or cleanly exit it before switching frontiers.
2. Reuse an existing completed baseline whenever one exists, then prefer the highest-ready semantic risk before adding routine breadth. If the risk is not ready, record why once and rotate rather than guess or repeat the investigation.
3. Introduce at most one major unknown semantic axis. Combine a new consumer or value family with an already closed context rather than widening type, repetition, orchestration, and protocol simultaneously.
4. Begin from competing semantic accounts and a separating witness, not framework code. A spike inherits the ordinary capsule scope and Tier 1 gates. Authorization to perform it does not authorize a new evidence harness, protocol, qualification path, or governance mechanism; those remain subject to the explicit approval rule.
5. Implement the first settled instance directly and visibly. Generalize only when a second completed consumer demonstrates the same meaning, result domain, and law; apparent syntactic similarity is insufficient.
6. Reuse stable semantic boundaries such as phase observation, checked expressions, verdicts, poison, outcomes, and application when their meanings fit exactly. Before adding another bespoke representation, check whether the current work is already the second consumer that justifies extracting a shared mechanism; do not force unlike operators or field kinds through one.
7. Keep a selected baseline→risk pair together by default and reassess the next frontier after the pair. A blocked spike may be parked only at a clean documented checkpoint with no partially integrated code; its unknown behavior may not be inherited by later work.
8. Run bounded consumer probes after high-leverage pairs and roughly every two rotations. Select a named task profile from [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md), map its required clauses and observable relation to existing specifications, executable cases, theorem/non-law links, support boundaries, and evidence status, then classify semantic dependency closure, shipment research closure, and cold-consumer qualification separately. An evaluator profile is language-neutral—Rust and Python need different implementation profiles, not different A12 semantics—while importers and refactoring tools require their own mapping or preservation relations. Use artifact-only readback by default; an external prototype, protocol, runner, dependency, or qualification path needs its own approval.

The ten categories in [`USE-CASES.md`](USE-CASES.md) are a discovery vocabulary, not an exhaustive backlog. A probe may expose another application or a genuinely different task relation. Classify it under an existing category when that contract fits; propose a new category only when it does not. Either way, the finding remains potential until a later decision adopts a research-closed shipment or product.

The durable coverage horizons remain:

1. **Foundations:** values, verdict algebra, checked cells, documents, environment, world, and theorem vocabulary.
2. **Scalar and nonrepeatable validation:** operator semantics, expressions, phase-sensitive reads, polarity, partial relevance, whole rules, and messages.
3. **Elaboration, paths, repetition, and correlation:** well-formed core rules, explicit rejection, required/index expansion, resolution, semantic indices, star binding, and declarative contexts.
4. **Computation and state transition:** outcomes, preconditions and alternatives, poison-on-read, scheduling, stored-form application, implicit validation, and read-footprint laws.
5. **Language and transformation boundaries:** concrete lowering, interpolation, custom-oracle boundaries, supported-fragment relations, and semantics-preserving transformations.
6. **Consumers, analyses, and real models:** independent evaluators, selected import/refactoring profiles, equivalence, implication, redundancy, overlap, dependency, version deltas, and business invariants.

These horizons express prerequisite and coverage direction, not a total phase-completion schedule. Project-owned [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md) supplies the bottom-up dependency spine and traps inside each capsule; [`PLAN.md`](PLAN.md) owns the current spiral and may cross horizons only when the selected capsule's exact prerequisites are internally closed for the claim being reused. Breadth does not count as progress while an active capsule lacks its theorem/counterexample obligation, coverage entry, trust gate, or honest evidence status. A relation or trace semantics is added only when it exposes meaningful steps or supplies an independent refinement target, not as ceremonial duplication.

A bounded importer, refactoring, explanation, or evaluator probe may begin over a fully closed named fragment to test knowledge transport and expose missing semantics. A shipment or release claim remains stricter: every clause required by its task profile must be research-closed, and consumer feedback cannot redefine the theory or fill an unknown branch.

## Trust, dependency, and publication policy

- Maintain one trusted theorem root importing every trusted proof module; mechanically check its coverage and transitive axioms.
- Reject active `sorry`, unclassified project axioms, `unsafe`, `partial`, and `native_decide` from the trusted closure. Experimental work stays outside that import graph.
- Distinguish successful-run soundness, failure behavior, termination, completeness, forward preservation, and equivalence in theorem names and coverage records.
- Keep the executable core dependency-free while that remains economical. Add a separate version-pinned Mathlib proof target when mature theory is cheaper and safer than rebuilding it.
- Keep external clocks, custom hooks, regex/Unicode facilities, and host failures explicit; purity alone does not imply locality or monotonicity.
- Keep Markdown canonical for charter, architecture, semantics, and provenance. User-facing documentation should reuse executable examples and maintained semantic artifacts where that materially prevents drift; [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md#128-use-markdown-docstrings-and-verso-for-different-jobs) compares Markdown, docstrings, generated API documentation, Verso, and Blueprint by their natural jobs. No publication tool is a core-library dependency or a new source of truth.

## Success and reevaluation criteria

The project succeeds only when its claim classes, independent-consumer boundary, and delivery discipline are visible:

- **Coverage:** every in-scope taxonomy/operator clause is implemented or explicitly classified; no silent semantic fallthrough exists.
- **Internal correctness:** the required proof spine is complete for its named fragments, theorem roots have clean reviewed dependencies, and exclusions are documented beside the claim.
- **Kernel correspondence:** the reference evaluator agrees with pinned retained projections of focused kernel evidence produced through named historical or current fit-for-purpose external routes, with every divergence explicit.
- **Independent reusability:** every release-supported consumer capability is research-closed and has passed its task-appropriate cold-consumer gate without kernel, sibling-source, or undocumented-context access; changing implementation language does not require renewed A12 research.
- **Transformation accountability:** every released importer or refactoring capability pins its source and target fragments, names the exact claimed relation and its assurance class, fails closed outside it, and retains a checked counterexample at the nearest tempting overgeneralization. Universal preservation is claimed only for a theorem-covered transformation or for outputs accepted by a proved certificate checker; an independent implementation without that bridge is reported as empirically qualified over executed cases.
- **Operational discipline:** each semantic capsule closes its theorem/counterexample, coverage, trust, build, assumptions, and evidence-status gates before the next capsule begins; that next capsule may deepen the same family or deliberately cross to another frontier. External evidence must close before a kernel-correspondence or shipment-ready claim, while related pending clauses may be calibrated together.

The first proof-bearing capsule is also the project's reevaluation point. Continue the full program only if it demonstrates material value beyond the Kotlin interpreter plus tests—such as a useful universal law, a clarified false generalization, a semantics-preserving transformation, or a reusable model-level proof boundary. If it produces only another evaluator and ceremonial `rfl` facts, redesign or stop before reproducing the entire operator surface.

Theorem counts, proof-line counts, zero `sorry`, corpus counts, or evaluator breadth are navigation metrics rather than success criteria. Each can be high while the theorem is weak, the definition is wrong, or the external correspondence is untested.

## Ecosystem role and non-goals

- **[`../../a12-kernel`](../../a12-kernel)** is the behavioral source of truth. This repository reads and probes it under the clean-room boundary but never links, calls, ships, or transliterates it.
- **[a12-dmkits (local `a12-rulekit/` checkout)](../../a12-rulekit)** supplies live ordinary kernel probes and differentials, a corpus with reusable cases and replay, and a peer clean-room interpreter for triangulation. It also historically produced the retained direct-cascade raw and compact evidence before retiring that portable producer estate. This repository retains accepted observations under their pinned provenance, keeps historical raw audit material opaque to ordinary Lean replay, and owns only each typed family meaning and replay against Lean. A future richer producer capability is a new demand-driven engagement, not a standing adapter service. The public a12-dmkits release is dmtool-release.
- **a12-kernel-lean** is the versioned mechanized theory: precise definitions, theorems and counterexamples, a reference evaluator, and an empirical conformance projection.

This project does not claim to verify the external kernel, eliminate empirical testing, make ambiguous clauses correct by typechecking them, prove arbitrary custom oracles well behaved, or justify speculative compilers, extraction, certificates, and production deployment before a consumer requires them.

It also does not currently claim general JSON Schema support, a JSON-Schema-to-A12 equivalence, a complete rule-refactoring engine, or a generic verified intermediate representation. Those become bounded capabilities only when a selected source profile, supported A12 target, concrete consumer, evidence plan, and exact preservation obligation have been adopted.

## Outlook

Once a named semantic fragment and its proof spine are credible, bounded probes can test these uses; scaling or releasing them requires the stronger consumer gates above:

- checked explanation traces whose acceptance implies a named evaluation judgment;
- selected JSON Schema import into supported normalized A12 models, with explicit dialect, mapping, lossiness, well-formedness, and satisfaction-preservation boundaries;
- proof-producing or certificate-checkable rule refactoring, simplification, and compilation with exact preconditions and observation-preservation claims;
- equivalence outside explicit deltas between versioned kernel-semantics theories;
- domain proofs that validation implies business invariants or computations preserve ranges and conservation laws;
- rule implication, redundancy, overlap, dependency, and repair analyses;
- deeper `$`-correlation semantics and proofs: explicit outer and inner environments, nested or multi-star scope, order-sensitive observation, and refinement from a naive relational account to justified execution plans; [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md#lf3---correlation-requires-two-explicit-environments) records the durable prerequisites and non-laws;
- user-facing explanations that double as regression consumers by reusing executable examples, theorem references, support data, and retained evidence, with the publication mechanism selected for the material rather than prescribed in advance, as described in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#user-facing-documentation-as-a-regression-consumer).

Current evidence counts, supported fragments, and remaining adequacy obligations live in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md). The accepted review checkpoint, current spiral, and immediate work live in [`PLAN.md`](PLAN.md). A durable conclusion from completing or failing a capsule belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md) or this constitution only when it changes the project method, authority model, success criteria, or long-term decision.
