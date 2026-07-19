# Lean formalization — role, potential, case studies, and working discipline

This document is the project's durable study of what Lean can contribute to an A12 semantics-of-record, which claims it can and cannot justify, and what established Lean projects teach us about structuring the work. It complements the project argument in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), the concrete encoding decisions in [`ARCHITECTURE.md`](ARCHITECTURE.md), and the language-neutral semantics under [`../spec/`](../spec/).

The external-project review is a snapshot from 2026-07-12 and uses primary repositories, papers, and official documentation. Project metrics are context, not assurance claims: exact theorem statements, hypotheses, result domains, axiom dependencies, and trust boundaries matter more than counts.

## 1. Thesis

> Lean is where the observed behaviour of A12 validation rules and computations becomes a versioned, mechanized theory: executable definitions state the chosen semantics; named theorems and counterexamples capture its universal consequences and limits; and corpus plus differential evidence connects that theory empirically to the real kernel.

This is deliberately stronger than “another evaluator in Lean” and narrower than “prove the A12 kernel correct.” The existing Kotlin interpreter already supplies an excellent clean-room runtime implementation. Lean earns its place by turning selected behavioural knowledge into definitions that compose, propositions with explicit hypotheses, proofs that range over all modeled inputs, and checked witnesses for attractive claims that are false.

[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#artifact-and-authority-model) owns the three project claim classes—semantic coverage, internal correctness, and empirical kernel correspondence—and their evidence topology. The formalization consequence is that theorem statements justify only internal consequences of the chosen definitions: a proved evaluator may formalize the wrong behaviour, while any finite differential campaign remains empirical.

### 1.1 Scope and semantic boundary

The formalization covers runtime validation conditions and computations: normalized rules and models, static legality needed to evaluate them, documents and formal checking, iteration and paths, phase-sensitive cell observation, truth and polarity, partial validation, computation outcomes, and application staging. The recommended initial boundary begins after bilingual text parsing but includes an explicit checked elaboration from resolved surface syntax into a smaller well-formed core. Proving the English/German parser correct is a possible later transformation project, not a prerequisite for the semantic center.

This is not an attempt to formalize the entire model validator or all structural diagnostics. It targets the evaluation semantics represented by the fourteen-section taxonomy. Every claim is about kernel 30.8.1 unless another version is named; version scope exists from the first theorem, not only after a second kernel version appears.

### 1.2 Required proof spine

The reference evaluator is useful before the entire theorem program is complete, but the formalization is not complete with executable code alone. Its required spine is:

1. the full truth, verdict, and fillability algebra, including an explicit information order and checked non-laws;
2. phase-observation and formal-check laws that preserve empty, malformed, excluded, and poison distinctions;
3. executable-evaluator soundness and completeness relative to an independent judgment or read-trace presentation wherever that second presentation adds semantic information;
4. well-formed elaboration and preservation for real surface-to-core transformations, beginning with required/index and implicit-computation desugarings;
5. read-footprint noninterference and poison-on-read causality for the supported fragment;
6. partial-validation one-sided soundness under a precise relevance/agreement relation;
7. polarity one-sided soundness under a precise legal fill-extension relation.

The proof spine is a contract about theorem shape, not a promise that each theorem covers the entire DSL. A root theorem must name a machine-readable supported fragment or hypotheses whenever custom oracles, counting quantifiers, row creation, time behavior, or order-sensitive constructs are excluded.

## 2. Formal knowledge carried by the stack

[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#artifact-and-authority-model) owns the artifact stack and authority order; [`ARTIFACTS.md`](ARTIFACTS.md) explains its concrete repository trees. Lean's distinctive responsibility inside that stack is to make the chosen compositional meaning and its universal consequences checkable. It does not replace readable rationale, discovery history, provenance, or empirical observations, while prose and finite tests should not be asked to carry laws that can be stated and proved once.

### 2.1 Kinds of semantic knowledge

Every important claim should be classified as one of:

- **Primitive observed clause:** for example, an empty Number participates as a fillable zero in a comparison.
- **Derived law:** for example, a branch that is already true makes `Or` insensitive to an unknown sibling.
- **Scoped law:** for example, row permutation is valid only for order-insensitive constructs.
- **Non-law / counterexample:** for example, `Valid` and `Invalid` are not complements under malformed input.
- **Semantic transformation:** for example, required/index declarations elaborate into generated rules and validation-scoped formal checks.
- **Model-level property:** for example, successful validation of a particular rule model implies a separately stated business invariant.
- **Empirical correspondence claim:** for example, the scale-19 comparison normalization matches kernel 30.8.1 on the captured boundary cases.

A semantic clause is not fully captured merely because an evaluator has a branch for it. Its provenance, interaction laws, nearest false generalization, and theorem scope are part of the body of knowledge too.

### 2.2 The semantic capsule

[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#delivery-unit-the-semantic-capsule) owns the semantic capsule and its complete delivery obligations. The formalization-specific rule is that evaluator code alone never closes a capsule: the useful theorem must state its exact hypotheses and result domain, and the nearest plausible stronger false claim must remain checked.

### 2.3 Semantic-slice definition of done

The stable definition of done is the capsule contract in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#delivery-unit-the-semantic-capsule). [`TESTING.md`](TESTING.md#capsule-test-checklist) owns its operational red/green and final-gate checklist, while [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) records `partial` and `external evidence pending` states. This document contributes the required proof spine above and the proof-engineering rules below; it does not maintain a second completion checklist.

### 2.4 Coverage chain

The fourteen-section taxonomy in [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) is the stable join key. Eventually each in-scope clause should be auditable through:

```text
§n semantic clause
  → provenance / kernel evidence
  → human-readable spec
  → Lean definition or judgment
  → executable conformance witnesses
  → theorem, counterexample, or explicitly empirical-only status
  → assumptions, unsupported fragment, and version caveat
```

The existing a12-dmkits map verifies that prose, findings, catalog facets, corpus families, and test classes are present. This repository's live [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) adds Lean definitions, theorem scope, support boundaries, and external-evidence state rather than duplicating that inventory blindly.

## 3. Architectural pattern for A12

The useful pattern shared by the strongest case studies is a small semantic center surrounded by separately justified transformations and implementations.

```text
A12 text + expanded model
          │
          ▼  parse / resolve / type-and-scale check / desugar
   well-formed core rule
          │
          ├──────────────► declarative or trace semantics
          │                            ▲
          ▼                            │ soundness / completeness
   executable reference evaluator ────┘
          │
          ▼  optional compiled paths / joins / caches
     optimized evaluator
          │
          ▼  empirical only
  kernel 30.8.1 observations
```

The executable definitions may initially be the normative semantic definitions. A second relational presentation is worth its duplication only where it exposes meaningful steps, traces, nondeterministic-looking scheduling choices, or a stable specification against which an algorithm can be proved. A relation defined merely as `result = eval ...` adds no knowledge.

The high-value bridge statements are therefore selective:

- elaboration produces a well-formed core rule and preserves meaning;
- required/index and implicit-computation desugarings preserve meaning;
- the reference evaluator is sound, complete, and functional with respect to an independent judgment or trace model;
- path plans, joins, and caches refine the reference semantics;
- partial validation and polarity soundness hold for explicit supported fragments and completion relations.

## 4. Case study: Cedar — the closest operational precedent

[Cedar](https://github.com/cedar-policy/cedar-spec) is an authorization policy language with a production Rust engine and a separate executable Lean model. Of the projects studied, it is the closest architectural precedent for A12: a real rule language, an independently shipped evaluator, static validation, explicit evaluation errors, an executable semantic model, proved consequences of that model, and differential randomized testing across the implementation boundary.

The repository makes the responsibilities concrete:

- [`cedar-lean`](https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean) contains the definitional evaluator, authorizer, validator, symbolic compiler, and theorem hierarchy;
- [`cedar-drt`](https://github.com/cedar-policy/cedar-spec/tree/main/cedar-drt) connects the Lean definitions to generated Rust tests for evaluator, authorizer, validator, partial evaluation, entity/request validation, symbolic queries, and selected algorithms;
- the production [Cedar engine](https://github.com/cedar-policy/cedar) remains Rust rather than being replaced by the Lean artifact.

The core [expression evaluator](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/Spec/Evaluator.lean) is an ordinary total Lean definition over an explicit `Result Value`. It makes short-circuit order visible for `and`, `or`, and conditionals, and preserves error classes rather than reducing every failed policy to a Boolean. The [authorizer](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/Spec/Authorizer.lean) separately defines policy satisfaction, error collection, and the final allow/deny decision. This decomposition is directly relevant to A12's distinction between truth, verdict, formal invalidity, computation poison, and orchestration.

The root [authorization theorems](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/Thm/Authorization.lean) prove domain laws such as forbid-overrides-permit, default deny, and invariance under policy order and duplicates. The [typechecker soundness theorem](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/Thm/Typechecking.lean) is especially instructive because it does not claim “validated means evaluation cannot fail”: it states the remaining allowed error classes—missing entities, extension errors, and arithmetic bounds—under a well-formed environment. Cedar also has sound/complete symbolic compilation and verification layers for analyses such as equivalence and implication, as summarized by the [`cedar-lean` guide](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/README.md).

Its engineering discipline is as important as the theorem catalog. The Lake project has one theorem root and a linter that checks recursively that proof modules are imported; CI builds proofs, runs the linter, runs unit and symbolic tests, builds FFI artifacts, runs differential and integration suites, and generates API documentation. The current Lake file makes [`doc-gen4`](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/lakefile.lean) a development-only dependency pinned to the Lean release, so documentation tooling does not burden the ordinary formalization target. Its [proof-style guide](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/GUIDE.md) favors minimal imports, root theorem docstrings, `simp only`, and explicit proof steps to improve upgrade stability.

**Transfer to A12:** make Cedar, not a weekend experiment, the default comparison for the overall project shape. Keep the production Kotlin/kernel world separate from the Lean semantics; model every semantically visible non-success result; prove domain-facing rule laws and static-validation guarantees with residual cases stated exactly; make theorem-root coverage mechanically checkable; and retain aggressive differential testing after proofs exist. Cedar's in-process differential bridge cannot be copied blindly because A12's licensing boundary forbids linking or calling the kernel from this project; clean-room external capture plus retained portable own-repository evidence must provide that bridge instead.

## 5. Case study: Radix

[Radix](https://github.com/leodemoura/RadixExperiment) is a compact verified embedded DSL created by ten Claude agents over one weekend. The project and its [ETAPS 2026 presentation](https://leodemoura.github.io/static/etaps2026/) report 52 completed theorems, no `sorry`, five optimization passes, big-step semantics with determinism, a fuel-based interpreter proved sound and complete for its relational semantics, linear-ownership results, 27 modules, and roughly 7,400 lines of Lean.

Those are presentation metrics, not reproducible assurance measures. At the audited revision, the 27 library modules contain about 5,993 physical lines (about 6,330 across all 30 Lean files); the [`BigStep`](https://github.com/leodemoura/RadixExperiment/blob/main/Radix/Eval/Stmt.lean) relation has 17 constructors even though [`Slides.lean`](https://github.com/leodemoura/RadixExperiment/blob/main/Slides.lean) labels and lists them as 16; and a source count finds 51 non-private theorem declarations with 50 unique public theorem names rather than 52. These inconsistencies do not invalidate the checked proof terms, but they reinforce why this review audits statements and dependencies instead of treating counts as evidence.

Its architecture is directly instructive:

- an extrinsic expression/statement AST;
- macros for pleasant concrete syntax;
- a relational big-step semantics;
- an executable interpreter;
- soundness and completeness bridges;
- static analyses and preservation theorems;
- optimization passes with semantic-preservation proofs.

The headline labels require narrower reading, which is itself an important lesson:

- [Interpreter correctness](https://github.com/leodemoura/RadixExperiment/blob/main/Radix/Proofs/InterpCorrectness.lean) covers successful terminating executions: the relational semantics has no error or divergence judgment, and interpreter soundness begins from a successful result.
- The [optimization theorems](https://github.com/leodemoura/RadixExperiment/tree/main/Radix/Opt) are forward preservation results for successful source executions, not full bidirectional equivalence for failures, termination, and divergence.
- [TypeSafety.lean](https://github.com/leodemoura/RadixExperiment/blob/main/Radix/Proofs/TypeSafety.lean) proves a scoped expression-result preservation result under environment and heap hypotheses; statement progress is not the theorem.
- [MemorySafety.lean](https://github.com/leodemoura/RadixExperiment/blob/main/Radix/Proofs/MemorySafety.lean) primarily establishes heap-API properties, while the substantial ownership theorem in [Linear.lean](https://github.com/leodemoura/RadixExperiment/blob/main/Radix/Linear.lean) is invariant preservation under explicit assumptions and successful normal execution.
- The macros in [Syntax.lean](https://github.com/leodemoura/RadixExperiment/blob/main/Radix/Syntax.lean) construct an extrinsic AST. Lean typechecks the host expression constructing that AST; it does not automatically establish that the represented object-language program is well typed.

The exact headline counts are less useful than this architecture and these proof boundaries. Radix demonstrates that an extrinsic AST can support meaningful verification and that a relational semantics can anchor an executable interpreter and transformations. It does not establish long-term maintainability, production maturity, or fidelity to an independently existing language. A12 has the additional and harder empirical-correspondence problem.

Radix also demonstrates a documentation use that is easy to miss: its top-level [`Slides.lean`](https://github.com/leodemoura/RadixExperiment/blob/main/Slides.lean) imports both `VersoSlides` and the Radix library, and its embedded examples are elaborated while the presentation builds. The slides are therefore a checked consumer and explanation of the formal artifact, not a detached deck that can silently bit-rot. This is strong evidence for Verso as a publication layer for a formal project; it is not evidence that ordinary repository prose should all be moved out of Markdown. Its [`lakefile.lean`](https://github.com/leodemoura/RadixExperiment/blob/main/lakefile.lean) places the library and slides in one package and tracks `verso-slides` at `main`, so Radix is not the model for dependency isolation or version pinning; A12 should keep the checked publication in a separate pinned target.

### Proof engineering transferred from Cedar and Radix

The focused 2026-07-17 study re-audited Cedar revision `3977eb4f017b421b7ac0b31ea4635e1dd36ce3ef` and Radix revision `617b67eb09681ca98e19759b48978866dcafeb17`, then exercised the candidate practices on the String dependency bridge and the independent flat checked-context lookup family under Lean 4.31.0. The adopted practice is scoped: expose one `Except` or enum layer explicitly, use `simp only` with a reviewed local equation set for the constructor reduction, and then apply named domain laws. Use `rfl` only where a semantic constructor equation is intentionally transparent. Keep recursive evaluators closed and keep result-domain case splits explicit when they communicate residual errors.

Cedar supplies the primary rationale: its guide prefers `simp only` while allowing plain `simp` to close a goal; its `Data/Control` and `simp_do_let` utilities expose effect constructors before simplifying; and its typechecker theorems state the allowed residual error domain. Its `checkThmFile` checks source import aggregation, not elaborated axioms, and its SymCC use of `native_decide` does not alter A12's stricter trusted-proof policy. Radix confirms the value of small closed result equations and directional evaluator bridges, while its success-only interpreter and forward optimization theorems warn against silently promoting a success projection to total error equivalence. Neither precedent justifies broad global simplification.

No new A12 `[simp]` rule was adopted. The cascade pilot did not demonstrate a cross-instance need for one, and the rich outcome bridge has a semantically important rejected branch. Proof-only observation equations live in [`A12Kernel/Proofs/Observation.lean`](../A12Kernel/Proofs/Observation.lean); semantic modules do not import proof infrastructure. The independent elaboration instance confirmed the local `simp only` pattern, while the correlation proof family remains the positive control for explicit `Except` case analysis.

**Transfer to A12:** build one similarly complete but much smaller semantic capsule early; prove the evaluator/judgment bridge over the full A12 result domain being claimed, including `unknown`, empty, poison, and failure cases rather than silently proving successful cases only.

## 6. Case study: Verity

[Verity](https://github.com/lfglabs-dev/verity) is a research smart-contract DSL and compiler implemented in Lean. Its authoring model explicitly separates a contract specification, executable implementation, and proof, while its compiler pipeline lowers an EDSL through a compilation model and IR to Yul.

Its most transferable contribution is **proof-boundary hygiene**. The current [verification status](https://github.com/lfglabs-dev/verity/blob/main/docs/VERIFICATION_STATUS.md), [trust assumptions](https://github.com/lfglabs-dev/verity/blob/main/TRUST_ASSUMPTIONS.md), and [axiom registry](https://github.com/lfglabs-dev/verity/blob/main/AXIOMS.md) qualify the broad “three verified layers” summary:

- the frontend macro/elaborator remains part of the trusted boundary; its generated “semantic preservation” bridge facts are definitional body-alignment equalities, while executable-EDSL/compilation-model equivalence is a separate, currently contract-instantiated proof surface;
- the compilation-model-to-IR theorem covers an explicit supported fragment rather than every accepted program;
- the IR-to-Yul theorem surface carries explicit hypotheses and documented gaps;
- pinned `solc` performs Yul-to-bytecode compilation and is trusted rather than verified;
- gas and several low-level mechanics remain outside the modeled semantics;
- differential EVM tests remain an independent cross-check rather than being displaced by proofs.

The project makes assumptions and unsupported features visible through reports, direct rejection of unsupported interop, and opt-in strict `--deny-*` gates for other trust surfaces. Its [paper](https://lfglabs.dev/papers/verity.pdf) also distinguishes generic compiler preservation from contract-specific business theorems such as state-update, access-control, or conservation properties. For A12, the trusted conformance profile should be strict by default rather than relying on callers to remember an opt-in gate.

**Transfer to A12:** maintain three explicit claim classes—internal semantic theorems, empirical kernel correspondence, and properties of actual business rule models. Give each important theorem a named supported-fragment predicate or equally precise hypotheses. Track custom conditions, clock/timezone choices, regex/Unicode behavior, decimal approximations, and external-kernel correspondence as explicit boundaries. Do not manufacture compiler stages that A12 does not need; prove only real elaborations, desugarings, plans, and optimizations.

## 7. Case study: Lean 4 and Lean4Lean

Lean 4 is evidence that substantial language infrastructure can be implemented in Lean, but not that all such infrastructure is verified. The official [Lean 4 paper](https://lean-lang.org/papers/lean4.pdf) and [language-reference pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) separate parsing, macro expansion, elaboration, kernel checking, and compilation. Parser, elaborator, tactics, decision procedures, pretty-printer, and code generator are extensible. The trusted kernel still checks elaborated terms, and the reference kernel is implemented in C++.

This separation suggests an A12 design in which bilingual concrete syntax and model-dependent legality elaborate into a smaller semantic core. The core evaluator should not repeatedly rediscover path resolution, numeric scale legality, or generated-rule expansion at runtime. A successful elaboration can carry or establish `WellFormed`; a preservation theorem can connect surface and core meanings.

[Lean4Lean](https://github.com/digama0/lean4lean) is an even closer architectural reference. It separates:

- an executable Lean implementation of the checker;
- an abstract `Theory` containing the metatheory and typing relation;
- a `Verify` layer relating the implementation to that theory.

The [Lean4Lean paper](https://arxiv.org/abs/2403.14064) reports that the checker can validate Mathlib and runs roughly 20–50% slower than the C++ reference checker. The repository is also candid that its implementation was derived from the C++ checker and may share its bugs, so executable independence and formal relation are distinct concerns.

The architectural separation must not be mistaken for completed end-to-end verification. The current default `Theory` and `Verify` targets contain active `sorry`, including in [metatheory foundations](https://github.com/digama0/lean4lean/blob/master/Lean4Lean/Theory/Inductive.lean) and checker cases. The explicit [`Verify/Axioms.lean`](https://github.com/digama0/lean4lean/blob/master/Lean4Lean/Verify/Axioms.lean) bridge surrounds opaque or partial upstream implementation facts and includes declarations documented as currently false; additional [pointer-equality axioms](https://github.com/digama0/lean4lean/blob/master/Lean4Lean/PtrEq.lean) live outside that registry. The public checker `WF` results are shaped as [soundness for successful results](https://github.com/digama0/lean4lean/blob/master/Lean4Lean/Verify/TypeChecker/Basic.lean), with errors satisfying the postcondition vacuously, rather than termination, completeness, or guaranteed acceptance. Lean4Lean is valuable architectural evidence and a source of checker results, but its trusted boundary must be read theorem by theorem. For A12, no `sorry` or known-false axiom may be reachable from a trusted semantic root.

**Transfer to A12:** keep semantic theory, reference execution, verification/refinement, and external conformance as visible modules or dependency directions. This is more important than whether every construct receives two full definitions. The architecture must make it possible to state which layer a theorem talks about and which external facts remain empirical.

## 8. Case study: `do` Unchained

[`do` Unchained](https://lean-lang.org/papers/do.pdf) is the most focused translation case study. It adds local mutation, early return, iteration, `break`, and `continue` as convenient surface syntax, translates them into pure monadic Lean, specifies a simple static and dynamic semantics, and proves that the translation preserves typing and evaluation.

The formalization deliberately narrows its model where necessary—for example, the presented operational semantics focuses on the identity monad and list iteration—while the Lean development proves modular translation results under lawful-monad assumptions. It uses a mixed deep/shallow embedding: statements are deeply represented, while existing Lean terms and monadic infrastructure are reused.

Its important design move is not intrinsic typing by itself; it is making a user-facing lowering into a named semantic transformation and proving the transformation modularly before composing the passes.

**Transfer to A12:** treat required/index expansion, implicit computation validation, path elaboration, scale/type checks, and potentially English/German surface equivalence as explicit transformations. Prove that their accepted fragment preserves core meaning. This yields more value than making the parser or surface AST artificially dependent merely because Lean supports dependent types.

## 9. Additional projects found in the landscape search

The supplied case studies were treated as starting points, not the completed research set. A broader search found the following projects with distinct lessons. They are not all equally close to A12, so the table records both the transferable idea and why this project should not imitate the whole architecture.

| Project | Distinct finding | A12 consequence |
|---|---|---|
| [Strata](https://github.com/strata-org/Strata) | An extensible Lean environment for defining language dialects, generating generic and specialized ASTs, translating between dialects, giving an operational semantics, and producing verification conditions for SMT; its own [architecture](https://github.com/strata-org/Strata/blob/main/docs/Architecture.md) calls the platform actively evolving and partly aspirational | Reuse the separation of generic syntax, specialized semantic core, transformations, and analyses; do not turn A12 into a general language workbench before its one semantics is complete |
| [CvxLean](https://github.com/verified-optimization/CvxLean) | A proof-producing DSL distinguishes equivalence, reduction, and relaxation and has a verified canonization procedure rather than describing every useful transformation as “equivalent” | Give A12 transformations the weakest accurate relation and compose proof-producing passes; a one-way preservation theorem must not receive an equivalence label |
| [Veil](https://github.com/verse-lab/veil) | One framework combines specification, executable/model-checking feedback, SMT automation, interactive proof, and realistic case studies; its [`Action/Theory.lean`](https://github.com/verse-lab/veil/blob/main/Veil/DSL/Action/Theory.lean) explicitly documents an incomplete `Wp`-to-big-step conversion and the termination/success assumptions needed by soundness results | Make counterexample discovery and checked witnesses first-class beside proofs, and document incompleteness at the conversion site rather than only in project-level caveats |
| [KLR](https://github.com/leanprover/KLR) | A family of ML-kernel languages is translated into a common representation with a precise operational semantics and program logic, while the README openly calls its current CPython-based source-gathering path complex and brittle | Keep A12 surface ingestion and semantic core separate, but avoid a generic IR or foreign-parser bridge until a real consumer and preservation theorem justify it |
| [SampCert](https://github.com/leanprover/SampCert) | A substantial Mathlib-backed verified implementation is deployed in AWS Clean Rooms and separates executable sampler code, probability semantics, deep mathematical proofs, and extraction support | A separate Mathlib proof target can be pragmatic rather than architectural failure; deployment or extraction creates a new correspondence boundary that must be verified separately from the source theorem |

These projects sharpen the selection criterion: include a case as a primary precedent only when its trust and semantics problem resembles A12's; otherwise extract one technique and retain the mismatch. Cedar is therefore primary. CvxLean strengthens the transformation vocabulary, Veil the counterexample workflow, Strata and KLR the surface/core boundary, and SampCert the dependency/deployment strategy.

## 10. Cross-study findings

| Finding | Consequence for this project |
|---|---|
| An executable Lean model and a production engine can coexist productively | Follow Cedar: proofs establish properties of the model; differential evidence connects the separately shipped implementation |
| Static-validation soundness should retain residual failures | State exactly which A12 errors remain possible after `WellFormed` or formal checking rather than promising blanket safety |
| Exact theorem statements outrank labels and counts | Document hypotheses, direction, result domain, and excluded behavior next to every root theorem |
| A relational semantics can anchor multiple algorithms | Add one where it supports traces, evaluator correctness, or refinement—not as ceremonial duplication |
| Extrinsic syntax is compatible with serious verification | Keep the current extrinsic AST; establish legality through elaboration and `WellFormed` |
| Surface-to-core translation is a high-payoff proof boundary | Prove genuine A12 desugarings and path/type elaboration, following `do` Unchained |
| Trust boundaries are part of the deliverable | Maintain an explicit boundary/assumption inventory, following Verity's discipline |
| Tests remain necessary beside proofs | Use differentials to anchor primitive choices; use proofs for internal universal consequences |
| An implementation written in Lean is not automatically verified | Separate “implemented in Lean,” “proved internally,” and “matches the external system” |
| Zero `sorry` is necessary but insufficient | Check axioms and theorem strength; guard roots with `#print axioms` |
| Proof automation checks terms, not intent | Preserve human review, provenance, and counterexamples; a wrong definition can support flawless proofs |
| Domain-specific model verification is the long-term payoff | Eventually prove real A12 rule families against independently stated business invariants |
| Proof-producing tools should name the relation they establish | Distinguish equivalence, forward refinement, reduction, relaxation, and conservative approximation, following CvxLean |
| Checked exposition can itself consume the artifact | Make user-facing examples consume maintained executable artifacts; consider Verso when the exposition is Lean-aware, following Radix and Lean's own manuals, while keeping durable repository prose accessible |

## 11. Lean-specific opportunities for A12

### 11.1 Foundational theory

- Full algebraic characterization of `K`, `Verdict`, polarity combination, and any information order—not merely selected table entries.
- Checked witnesses for laws that fail, including non-complementary predicate families and order-sensitive operations.
- Phase laws for `CheckedCell` observations, including required-empty's validation/computation asymmetry.
- Exact aggregate identities and per-kind empty behavior.
- Static scale derivation and equality-gate soundness.

### 11.2 Whole-rule semantics

- A precisely scoped suppression/information-monotonicity theorem.
- Partial-validation soundness over an explicit `AgreesOn` or completion relation.
- The one-sided polarity theorem: a VALUE firing cannot be repaired by a legal fill-only extension, under the covered fragment's assumptions.
- Read-footprint noninterference: documents agreeing on everything actually read produce the same result.
- Poison noninterference: an invalid cell outside the dynamic read trace cannot poison a computation.
- Determinism or functionality of an independent evaluation judgment for a fixed model, ordered document, world, schedule, and oracle contract.

### 11.3 Transformations and implementations

- Required and index desugaring preservation.
- Implicit computation-validation rule preservation.
- Surface-to-core elaboration soundness for paths, types, scale, and scope.
- Reference path resolution versus compiled access-plan equivalence.
- Declarative joins versus hash joins and cache correctness.
- Reference versus optimized evaluator refinement.
- Checked import from a named JSON Schema dialect/subset into a supported A12 fragment: explicit source semantics; checked parsing and reference-resolution soundness, or an explicit pre-parsed source-AST trust boundary; target well-formedness; and precisely directed satisfaction preservation over an explicit JSON-instance-to-Document relation.
- Rule-refactoring preservation over the complete observation domain admitted by the fragment, with the weakest accurate relation—equivalence, forward/backward refinement, reduction, relaxation, or conservative approximation—and compositionality for multi-pass tools.
- Soundness of compact certificates emitted by untrusted importer, refactoring, analysis, or optimization frontends and checked by a smaller Lean-defined verifier.

### 11.4 Actual rule models

Once business intent is stated independently, Lean can ask questions that kernel conformance alone cannot answer:

- Does validation success imply the intended domain invariant?
- Are two rule versions equivalent for all well-formed documents?
- Is one rule redundant under the others?
- Can two computation alternatives overlap?
- Do computations preserve a range, conservation law, or cross-field consistency relation?
- Which semantic changes between kernel versions can affect this model?

These are longer-term goals, but they are the strongest reason to build a reusable formal semantics instead of stopping at a third evaluator.

## 12. Working best practices

### 12.1 State the theorem before celebrating the proof

For every root claim, record:

- the exact Lean statement;
- its quantifiers and hypotheses;
- its direction (`→`, `←`, or `↔`);
- the result domain it covers, including error/unknown/poison/divergence cases;
- excluded constructors or external oracles;
- the evidence that motivated it;
- `#print axioms` output in the trusted proof gate.

“Sound,” “complete,” “safe,” “equivalent,” and “verified” are summaries, never substitutes for these details.

### 12.2 Define relations before proving monotonicity

The important theorem vocabulary should be explicit data or propositions, not English hidden in comments. Likely foundations include:

- `InformationRefines` — one observation/document contains no more definite information than another;
- `FillExtends` — a legal fill-only change, with rows/world/entered values constrained precisely;
- `AgreesOn` — two documents agree on a relevant or read set;
- `WellFormed` — the elaborated model/rule satisfies static type, scale, path, and scope constraints;
- `Reads` / evaluation trace — the dynamic cells actually observed before short-circuiting.

Counting quantifiers, custom conditions, created rows, and order-sensitive computations will force these relations to be narrower than an intuitive slogan. That precision is a result, not an inconvenience.

### 12.3 Preserve the small executable core

- Keep semantic functions pure and accepted as total by Lean's kernel. Structural recursion is ideal when natural, but well-founded recursion and readable local `do`, `let mut`, `for`, `StateM`, or `Except` notation are legitimate when they elaborate to pure terms and keep the semantic order visible.
- Keep `IO`, ambient clocks, and host exceptions outside the semantics.
- Prefer small named operations to a monolithic evaluator so theorems can reuse exactly the clause they describe.
- If fuel is genuinely needed, expose exhaustion rather than mapping an arbitrary bound to an A12 result; prove fuel monotonicity and sufficient-fuel soundness/completeness for the claimed relation.
- Preserve the dependency-free executable target while it remains cheap. If serious proofs require mature results about finite maps, permutations, orders, rationals, or calendars, consider a separate Mathlib-backed proof target rather than rebuilding a theorem library or burdening `#eval`.

### 12.4 Make assumptions visible and fail closed

- A new `sorry`, project axiom, `unsafe`, source-partial or unclassified opaque declaration, compiled-body substitution, foreign entry point, or unclassified oracle boundary must fail the trusted proof gate through the elaborated environment rather than source spelling alone.
- Every project Lean source must have an explicit architectural zone, and each trusted or executable root must admit only its declared zones. A newly named evidence, registry, process, or other directory fails closed until classified; absence from a blacklist is never permission to enter the logical closure.
- Custom conditions should be excluded from locality/fill theorems unless supplied with explicit contracts.
- Timezone/DST, Unicode/regex, decimal approximation, and kernel-version assumptions should be named at the theorem or module boundary.
- An unsupported language fragment must produce an explicit elaboration/conformance status, never silently reuse a stronger theorem label.

### 12.5 Keep proofs and evidence independent

- Do not derive Lean clauses mechanically from the implementation being checked and then claim independence.
- Use a12-dmkits findings, catalog facts, and corpus cases as evidence inputs, not as runtime dependencies.
- Continue differential testing after a theorem is proved; the theorem validates consequences of the Lean definition, while the differential validates the primitive definition against the external engine.
- Seek a second predicted instance for every discovered semantic mechanism before encoding it, following the project's root-cause discipline.

### 12.6 Capture non-laws

For every attractive algebraic or semantic conjecture, either prove it under explicit assumptions or retain a small checked counterexample. Important A12 knowledge often consists precisely of failed equivalences:

- empty is not invalid;
- Boolean and Confirm emptiness differ;
- `Valid` and `Invalid` are not complements;
- field-presence predicate pairs are not all complements;
- row permutation is not valid for order-sensitive constructs;
- OMISSION is not necessarily an exact “there exists a repairing fill” classification;
- poison propagation is intentionally read- and order-sensitive.

### 12.7 Design for reviewability

- Mirror the stable `§n` taxonomy in module docs and theorem names where practical.
- Link each semantic module to its local spec section and evidence source.
- Keep the human-readable theorem index smaller than the implementation: list root claims and counterexamples, not every helper lemma.
- Treat generated theorem counts and coverage reports as navigation aids, not quality scores.
- Review external projects by reading theorem statements, proof dependencies, trust models, and unsupported fragments—not only READMEs.

### 12.8 Use Markdown, docstrings, and Verso for different jobs

Verso is an official, increasingly important Lean documentation system, but it is not a universal replacement for Markdown in Lean repositories. The useful distinction is by artifact and audience:

| Form | Best use here | Recommendation |
|---|---|---|
| Markdown | Project charter, architecture decisions, semantic prose, evidence and provenance, contributor orientation | Keep as the canonical format for the current `README`, `docs/`, and `spec/`; it is reviewable without a Lean build and works for A12 readers who are not Lean users |
| Lean module docs and declaration docstrings | Definitions, theorem statements, local rationale, and symbol-level API documentation | Add beside the implementation; treat these as the source for code API documentation |
| [`doc-gen4`](https://github.com/leanprover/doc-gen4) | Generated browsable API reference from compiled modules and docstrings | Add in a separate documentation build once the public Lean API is substantial; it is not the narrative semantics guide |
| [Verso](https://verso.lean-lang.org/) | A published handbook, tutorial, technical article, website, or slide deck whose Lean examples, theorem references, and proof states must stay checked | Consider it when a concrete user or maintenance need benefits from Lean-aware exposition; existing capsules make a pilot possible but do not by themselves justify one, and ordinary repository Markdown should not migrate merely for uniformity |
| [Verso Blueprint](https://github.com/leanprover/verso-blueprint) | A navigable claim/dependency plan that separates original provenance, informal statements, and associated Lean declarations, and derives progress from the formal artifact | Design the clause-level coverage data so it can feed a blueprint; adopt the rendered blueprint once theorem dependencies and contributor coordination outgrow the simpler map |

If Verso is adopted, its natural boundary is a nested or otherwise separate documentation target that imports `A12Kernel` and publishes selected semantic clauses, examples, counterexamples, theorem statements, and coverage views. The executable library should not acquire a documentation dependency. Pin Verso to the tag or commit compatible with the project's Lean version rather than tracking `main`; the [Verso package guidance](https://reservoir.lean-lang.org/@leanprover/verso) provides release-aligned tags and also notes that the project is changing rapidly.

This publication must not create a second hand-maintained semantics. Markdown remains the durable source for project intent, empirical provenance, and the full language-neutral specification; Lean definitions and theorem statements remain the mechanized source. Verso should import and render those checked artifacts, add a curated learning path, and link to the canonical prose. Radix's checked [`Slides.lean`](https://github.com/leodemoura/RadixExperiment/blob/main/Slides.lean) is the compact model for this role. The [Lean Reference Manual](https://github.com/leanprover/reference-manual/blob/main/Manual.lean) demonstrates the larger manual form. Verso Blueprint's explicit three-level split—source provenance, informal exposition, and associated Lean declarations—closely matches this project's knowledge stack and is the natural later projection for clause dependencies and proof progress.

### 12.9 Verso decision rule and outlook

**Status:** available option, not scheduled work and not a core dependency. The existing proof-bearing capsules make Lean-aware exposition technically possible, but they do not establish that Verso is the best response to a real reader or maintenance problem. Do not migrate existing Markdown.

The general goal is user-facing documentation that also serves as a regression consumer. Verso is one mechanism for that goal when the material being explained is Lean-native. A command guide should normally be checked by process-level integration tests; evidence summaries by schema validation and replay; support tables by the coverage source; ordinary rationale by reviewable Markdown. Any of those checked results may be rendered into a user guide without making the rendering tool responsible for the underlying test.

Verso is strongest here for a semantic handbook or presentation that imports `A12Kernel`, elaborates selected examples, resolves real declarations and theorem names, and gives readers a curated narrative through material that an API index cannot teach. Radix's `Slides.lean` demonstrates this narrow strength. Verso Blueprint may later help when the theorem and provenance dependency graph becomes difficult to navigate from [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), but graph size and contributor need—not availability of the tool—should trigger it.

The audiences impose different tests of value:

| Audience | Potential benefit | Warning sign |
|---|---|---|
| A12 rule authors and domain readers | Executable examples and plain-language explanations remain synchronized with the semantic theory | The page exposes Lean machinery without improving understanding of A12 behavior |
| Independent semantic-consumer authors | One path connects a supported scenario or transformation to its normalized result or relation, theorem/checker boundary, counterexample, and evidence status | The publication invents a second task interface, support list, expected-result store, or transformation contract |
| Lean contributors | Narrative navigation through related declarations and proofs, with examples checked during the documentation build | The handbook duplicates module docstrings or generated API documentation |
| LLM and coding agents | Stable anchors and checked exemplars reduce stale prose and make claim-to-code-to-proof-to-evidence traversal more reliable | Canonical knowledge becomes harder to read, search, or update than Markdown and ordinary Lean files |

For an agent specifically, Verso does not add semantic intelligence by itself. It helps only if its source or generated output exposes durable structure and its build catches a class of stale references or examples that otherwise reaches the agent as plausible but false context. A compact Markdown ownership map, well-named Lean declarations, executable fixture files, and explicit theorem/evidence indices remain more valuable baseline affordances.

Adopt Verso only when a named audience needs a curated Lean-aware artifact and a small experiment shows that it catches meaningful drift or improves navigation enough to justify another pinned build. The lowest-cost experiment is first a dedicated explanatory Lean module whose examples already compile; one end-to-end semantic capsule can cover observed clause and provenance → normalized input → executable result → exact theorem boundary → checked counterexample → retained evidence status. Render that module through Verso only if the publication layer adds visible reader or navigation value beyond the compiled module and its Markdown links.

### 12.10 Keep document ownership explicit

The canonical document ownership map is [`README.md`](README.md), and lifecycle/update triggers are defined in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md). This document owns the formalization contract, audited case-study knowledge, theorem and trust discipline, and publication strategy. Any future checked handbook, walkthrough, slide deck, or blueprint—whether built with Verso or another suitable mechanism—is a publication view over the maintained Markdown, Lean, protocol, and evidence surfaces, not an additional authority.

## 13. Anti-patterns

- **Kotlin again in Lean:** building the full evaluator before demonstrating a proof-bearing semantic capsule.
- **Evaluator defines correctness by itself:** adding a relation that is only equality with the evaluator.
- **Headline verification:** citing theorem counts, zero `sorry`, or a label such as “memory safe” without its statement and boundary.
- **Success-only theorem promoted to full correctness:** omitting unknown, poison, rejection, failure, or divergence from a relation while calling its bridge equivalence.
- **Forward preservation called equivalence:** proving only that a successful source execution is preserved and then claiming identical behavior in both directions.
- **Format-name verification:** claiming a “verified JSON Schema importer” without pinning a dialect/subset, modeling its source meaning, defining the JSON-instance-to-Document relation, and stating the exact preservation direction.
- **Boolean-only refactoring equivalence:** proving that condition truth agrees while omitting in-scope unknown/poison, polarity, messages, computation deltas, storage, or observable order.
- **Silent import approximation:** dropping or defaulting an unsupported source construct while returning an ordinary successful A12 model instead of an explicit rejection or declared approximation.
- **Host/object-language confusion:** assuming a syntax macro makes A12 programs well typed because Lean typechecks the macro expansion.
- **Hidden fuel semantics:** treating exhaustion at an arbitrary bound as though it were an A12 outcome.
- **Monadic order accident:** allowing a generic traversal to choose read order where short-circuiting or poison makes order observable.
- **Hidden theorem exclusions:** claiming monotonicity while silently skipping counting quantifiers or custom conditions.
- **Definitional self-proof:** using `rfl` between aliases of one implementation as evidence that it meets an independent specification.
- **Proof replaces conformance:** treating internal proof as evidence that kernel 30.8.1 has the same primitive behaviour.
- **Conformance replaces proof:** treating finite differential success as a universal guarantee.
- **Experimental leakage:** importing conjectures, unfinished verification, or axiomatic prototypes into trusted library roots.
- **Speculative compiler architecture:** adding IRs, certificate formats, code generation, or intrinsic typing without a theorem or consumer that needs them.
- **One giant semantic pass:** implementing many operator families before one slice has executable meaning, a proof obligation, a counterexample, and external evidence.
- **Rebuilding mathematics:** retaining “no dependencies” at the cost of writing inferior map, permutation, arithmetic, or calendar theory.
- **Prose erasure:** moving rationale and provenance into code comments until the semantics becomes formally checked but humanly unintelligible.

## 14. Proof-spine retrospective

The first thin slices validated the formalization strategy without making this document a second milestone plan. Finite truth and verdict algebras support quantified laws and checked non-laws; phase-aware observation makes empty, malformed, required, and poison distinctions explicit; required-property treatment supplies an independently meaningful transformation boundary; and iteration/correlation use declarative relations or observation-footprint theorems where they expose structure beyond execution.

A duplicate flat judgment was deliberately not added because it would restate the evaluator without an independently useful trace or refinement target. The same restraint applies to checked wrappers: their carried model/core certificates justify structural coherence, not source-to-core semantic preservation in the absence of an independent surface dynamics. Add another relational presentation only when observable reads, scheduling, access plans, or a real transformation make its steps semantically informative.

[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#controlled-interleaving-and-coverage-horizons) owns the durable development method and coverage horizons, [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and [`EVIDENCE.md`](EVIDENCE.md) own current closure, and [`PLAN.md`](PLAN.md) owns the current spiral. This section retains only the proof-engineering lesson: independent presentations earn their maintenance cost by exposing a theorem boundary that the executable definition alone does not.

## 15. Study sources

Repository claims in this review were checked against shallow local clones at the following revisions on 2026-07-12. Inline links favor readable default-branch locations; this table fixes the audited state when those branches later move.

| Repository | Audited revision |
|---|---|
| Cedar specification | [`3977eb4`](https://github.com/cedar-policy/cedar-spec/tree/3977eb4f017b421b7ac0b31ea4635e1dd36ce3ef) |
| Radix | [`617b67e`](https://github.com/leodemoura/RadixExperiment/tree/617b67eb09681ca98e19759b48978866dcafeb17) |
| Verity | [`e57064c`](https://github.com/lfglabs-dev/verity/tree/e57064c1db487da9e0f15adfdb616ff45025f451) |
| Lean4Lean | [`8865b15`](https://github.com/digama0/lean4lean/tree/8865b155abbf68d3a827fb3568bf6839780163c2) |
| `do` Unchained supplement | [`353fad8`](https://github.com/Kha/do-supplement/tree/353fad821a6bdfe2efb0762abdb0e4cee74ba9a2) |
| Strata | [`e912c9b`](https://github.com/strata-org/Strata/tree/e912c9bba0ad82244185e9c75b9535a6aedbd0f3) |
| CvxLean | [`c62c2f2`](https://github.com/verified-optimization/CvxLean/tree/c62c2f292c6420f31a12e738ebebdfed50f6f840) |
| Veil | [`6a12daa`](https://github.com/verse-lab/veil/tree/6a12daa8d3e0e8a9808a40ecab17ca030b557063) |
| KLR | [`7ccd18c`](https://github.com/leanprover/KLR/tree/7ccd18c174b2f4bd896bb6025eae7ded1386fa7d) |
| SampCert | [`6e2392c`](https://github.com/leanprover/SampCert/tree/6e2392c165652063fefc628d8f047b77ca393b0f) |
| Verso | [`8649419`](https://github.com/leanprover/verso/tree/86494197017df60fb4a30a6637294426e6d17a7f) |
| Verso Blueprint | [`dac5295`](https://github.com/leanprover/verso-blueprint/tree/dac52958052093bdf5013a3cf17b8fc7aed90694) |
| Lean Reference Manual | [`f447334`](https://github.com/leanprover/reference-manual/tree/f447334e7f0491de855df4218188481ed6023263) |

- [Cedar specification repository](https://github.com/cedar-policy/cedar-spec), [`cedar-lean` overview](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/README.md), and [Cedar security model](https://docs.cedarpolicy.com/other/security.html)
- [Radix repository](https://github.com/leodemoura/RadixExperiment) and [ETAPS 2026 presentation](https://leodemoura.github.io/static/etaps2026/)
- [Verity repository](https://github.com/lfglabs-dev/verity), [paper](https://lfglabs.dev/papers/verity.pdf), [verification status](https://github.com/lfglabs-dev/verity/blob/main/docs/VERIFICATION_STATUS.md), and [trust assumptions](https://github.com/lfglabs-dev/verity/blob/main/TRUST_ASSUMPTIONS.md)
- [The Lean 4 Theorem Prover and Programming Language](https://lean-lang.org/papers/lean4.pdf) and the [Lean processing pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean4Lean repository](https://github.com/digama0/lean4lean) and [paper](https://arxiv.org/abs/2403.14064)
- [`do` Unchained paper](https://lean-lang.org/papers/do.pdf) and [supplement](https://github.com/Kha/do-supplement)
- [Verso](https://verso.lean-lang.org/), its [package and versioning guidance](https://reservoir.lean-lang.org/@leanprover/verso), [Verso Blueprint](https://github.com/leanprover/verso-blueprint), the [Lean Reference Manual source](https://github.com/leanprover/reference-manual/blob/main/Manual.lean), and [`doc-gen4`](https://github.com/leanprover/doc-gen4)
- [Strata](https://github.com/strata-org/Strata), [CvxLean](https://github.com/verified-optimization/CvxLean), [Veil](https://github.com/verse-lab/veil), [KLR](https://github.com/leanprover/KLR), and [SampCert](https://github.com/leanprover/SampCert)
- The local A12 evidence inventory in [`SOURCES.md`](SOURCES.md) and a12-dmkits' [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md)
