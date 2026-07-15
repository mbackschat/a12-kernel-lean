# CLAUDE.md

Guidance for working in **a12-kernel-lean** — a clean-room, versioned **Lean 4 formal theory and executable specification** of the A12 kernel's validation & computation semantics.

## What this is

A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: business analysts declare **validation rules** (each states the *error* condition — true ⇒ the data is invalid) and **computations** (derived fields) in a bilingual EN/DE DSL, and the engine evaluates them against form *Documents*. This project preserves that observed **evaluation semantics** as a versioned mechanized theory: executable as a reference oracle, empirically anchored to kernel 30.8.1, equipped with a required proof spine plus selectively proved higher-level properties, and designed to produce purpose-specific semantic shipments for independent evaluators and later checked consumers such as importers and rule-refactoring tools.

The language-neutral semantics live in read-only [`spec/`](spec/) — start at [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md) and follow the numbered deep-dives. [`docs/README.md`](docs/README.md) is the sole registry and ownership map for the living project documentation; do not reproduce its complete catalog here.

- **Extend semantics:** use [`docs/SOURCES.md`](docs/SOURCES.md) for the writable drill path and post-spec deltas, inspect current clause/proof/evidence coverage in [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md), and follow the capsule workflow in [`docs/TESTING.md`](docs/TESTING.md). [`spec/13-lean-encoding-guide.md`](spec/13-lean-encoding-guide.md) remains consulted staged guidance, not a writable plan.
- **Resume current work:** read [`docs/PLAN.md`](docs/PLAN.md) for the verified baseline summary, active objective, immediate order, and stop conditions; follow its links to the owning evidence and capability records.
- **Work on the process or a consumer:** start with [`docs/PROTOCOL.md`](docs/PROTOCOL.md) for the normalized reference process and [`docs/IMPLEMENTER-GUIDE.md`](docs/IMPLEMENTER-GUIDE.md) for semantic shipments and independent consumers.

## Goal & role

**A versioned mechanized theory, executable-first, with a required proof spine and additional proofs selected by payoff** (decided 2026-07-12). Build small semantic capsules: each lands with its executable clause, evidence, useful law when one exists, nearest checked non-law, exact assumptions, and coverage entry. Project closed capsules into versioned, purpose-specific semantic shipments across the Execute/Translate/Transform/Compile/Analyze/Verify/Synthesize/Qualify/Explain/Govern taxonomy owned by [`docs/PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md#general-consumer-task-categories) and explained for users in [`docs/USE-CASES.md`](docs/USE-CASES.md): independent evaluators are the first consumer profile, while selected external-model importers and A12 rule-refactoring tools are later concrete examples with their own source/target fragments and preservation obligations. The reference evaluator is differentially checked against retained portable observations produced by the real engine and exported through the external a12-dmkits adapter; the sibling corpus is knowledge and source material, not a second live replay dependency. Proofs establish internal universal consequences and semantic-preservation bridges, never universal correspondence to the external kernel or automatic correctness of an independent consumer. Lean is the ecosystem's formal semantics-of-record for the chosen account of observed behaviour — *not* a replacement for the shipped Kotlin interpreter. Read [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md) for the charter and [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md) before extending the proof or semantics architecture; read [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) before extending the core types.

## ⚠️ HARD RULE — clean-room reimplementation; never link, call, or transcribe the kernel

This is a **licensing boundary, not a preference**, and it is the same rule the a12-dmkits interpreter already operates under. The A12 kernel is **EUPL-1.2 (copyleft) OR commercial**. A work that *links, ships, or calls* the kernel is a combined work the EUPL copyleft reaches; a **line-by-line transliteration of its source** is a copyright derivative that re-attracts the EUPL. Therefore:

- **Never** link, call, or ship the kernel (or a JS-kernel binding) from this project, and **never** transcribe a kernel *source expression* into Lean.
- **Do** read the kernel — and the a12-dmkits interpreter under `../a12-rulekit/interpreter/` — to *learn the exact behaviour*, then write **original** Lean and lock it against that behaviour with property/differential tests. Reading the source to *understand* (and to find surprising special cases) is encouraged; the *fix* is never a transliteration. **Copy the mechanism, never the expression.**

Because this project's source ships no kernel code, it is licensed **MIT** (see [`LICENSE`](LICENSE)) — matching the A12 OSS family (a12-dmkits source is MIT for the same reason; see [`../a12-rulekit/docs/LICENSING.md`](../a12-rulekit/docs/LICENSING.md)).

## ⚠️ HARD RULE — no machine-specific data in committed files

No absolute home paths, usernames, hostnames, emails, or credentials in source, docs, or commit messages. Reference the sibling repos by **relative path** (`../a12-kernel/`, `../a12-rulekit/`); this project assumes they are checked out as adjacent directories under a shared parent, as the rest of the A12 OSS family does.

## ⚠️ HARD RULE — dependency changes require user approval

Consult the user and obtain explicit approval before adding, removing, upgrading, vendoring, or replacing a Lake package, runtime library, build tool, or other dependency, and before changing static/shared linkage or the distribution strategy for a bundled component. Discovering an implicit toolchain dependency is not authorization to change it: report the dependency, its purpose, licensing/deployment consequence, and concrete options first. Read-only inspection and measurements of the existing dependency graph are allowed.

## Naming convention

- **a12-dmkits** is the project/repository name. Use it when referring to the software, semantics corpus, interpreter, adapter, catalog, documentation, or project as a whole.
- **dmtool-release** is a12-dmkits' public release/distribution. Use it when referring to the released CLI or public binary surface.
- **`a12-rulekit/`** is only the local checkout folder name. Use `../a12-rulekit/` or an explicitly labeled “a12-dmkits (`a12-rulekit/` checkout)” when a filesystem path matters; do not use “a12-rulekit” as the project name.

## ⚠️ HARD RULE — sibling tracked worktrees stay immutable and visibly clean

Treat every tracked or visible-untracked path outside the `a12-kernel-lean` repository root as **strictly read-only**, including all sibling repositories such as `../a12-kernel/` and `../a12-rulekit/`. The user permits build/test writes only under paths that the owning sibling repository already ignores.

- Never edit, create, generate, format, delete, restore, stage, or commit a tracked file outside this repository, and never create a visible untracked file there.
- Sibling builds, tests, and external kernel-harness runs are allowed only when every produced cache, build directory, report, lock, or temporary artifact is already ignored by that sibling repository. Check the intended path with `git check-ignore` when uncertain.
- Check the sibling's visible `git status --short` before and after the run. It must remain unchanged and clean; remove any visible temporary artifact created by the run without using broad destructive cleanup.
- A generator that normally rewrites tracked fixtures or corpus files must be redirected to an ignored workspace or run on an ignored disposable copy. Never let it touch the sibling's tracked outputs.
- Read-only source and documentation inspection remains allowed. Keep temporary artifacts in ignored locations only, and remove project-local temporary files before completing the task.

## ⚠️ HARD RULE — treat `spec/` as read-only

The language-neutral semantics in [`spec/`](spec/) are consulted upstream reference input, playing the same role for this repository that the merged BA/dev kernel documentation plays for a12-dmkits. They are not a working log or implementation-status surface. Do not edit files under `spec/` unless the user explicitly authorizes that exact change. Put new findings, Lean design decisions, implementation progress, evidence status, research notes, and plans under [`docs/`](docs/) instead.

## The source-of-truth hierarchy

Three layers, in authority order for a semantic question:

1. **`../a12-kernel` — the ultimate source of truth (the behavioural oracle).** The real engine. When the local theory and the engine disagree, **the engine wins and the theory is corrected**. Use it to learn and to differentially test — always under the clean-room rule above.
2. **`spec/` and the Lean theory (this repo) — the primary working reference.** The distilled, language-neutral semantics, executable definitions, and proved consequences of the chosen account. The `§n` taxonomy mirrors a12-dmkits, so section numbers line up across repos.
3. **a12-dmkits — the knowledge source, checked out locally as `../a12-rulekit/`.** A peer **clean-room** reimplementation of the same semantics (in Kotlin), a reusable test corpus, semantics ledgers, and an evaluation harness. Its public release is **dmtool-release**.

### Entry points

[`docs/SOURCES.md`](docs/SOURCES.md) inventories both sibling checkouts, defines the drill chain from `spec/` prose to ground truth, and records project-local post-spec deltas; a12-dmkits' guard-checked [`../a12-rulekit/docs/SEMANTICS-MAP.md`](../a12-rulekit/docs/SEMANTICS-MAP.md) owns the exhaustive per-`§n` peer-project index. Highest-signal starting points are [`../a12-kernel/documentation/_merged/kernel-ba.md`](../a12-kernel/documentation/_merged/kernel-ba.md) (the definitive behaviour spec), that a12-dmkits map, and [`../a12-rulekit/interpreter/`](../a12-rulekit/interpreter/) (the peer clean-room engine — read for approach, never to copy). The external Lean case studies and their primary-source links are curated in [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).

**Differential doctrine:** Kernel differential testing remains the empirical backbone. Each executable Lean capsule must be checked against retained portable observations from the real kernel; proofs establish internal laws; a12-dmkits contributes knowledge, evidence transport, and clean-room triangulation, but its interpreter is never the oracle. Kernel execution happens only through the external sibling harness, never as a dependency or shipped component of this repository. Codex may run that harness while preserving the sibling's tracked/visible worktree under the rule above, then bring only portable own-domain observations into this repository. A capsule without them remains marked `external evidence pending` rather than kernel-correspondence complete. The exact topology and evidence roles are fixed in [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md).

### Codebase orientation

For codebase warm-ups and explanations, work directly from this repository's source and documentation. Ignore Showboat and the dmtool-release CLI unless the user explicitly asks for either; they are not part of understanding or explaining this codebase.

## Building & running

Toolchain: **Lean 4.31.0**, pinned in [`lean-toolchain`](lean-toolchain); Lake 5.0. There are no external Lake package dependencies. Native executables still incorporate pinned toolchain/runtime components, including GMP; [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md) owns their release implications.

```sh
lake build                          # build definitions, proofs, and executable conformance locks
lake test                           # replay retained kernel 30.8.1 observations through the Lean projection
lake exe checkReferenceProcess      # run the black-box CLI/fixture/manifest and runner-integrity gate
lake exe syncFlatHandover --check   # verify frozen 0.2.0 handover artifacts; historical --write is rejected
lake exe checkBoundedProcess        # check timeout, streamed caps, exact bytes, and process-group cleanup
lake exe checkGeneratedDifferential --self-test # check the closed 52-case generator and runner guards without a candidate
lake exe checkGeneratedDifferential --check-profile reference/flat-validation-empty-logic-v1.generated-differential-v1.json # validate the pinned Rust campaign without executing it
lake exe checkGeneratedDifferential --check-result reference/flat-validation-empty-logic-v1.generated-differential-v1.json qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json # check the retained green receipt's exact profile identity and internal consistency
lake build checkMutationQualification # build the mutation packet/replay/checker executable
lake exe checkMutationQualification --self-test --candidate-repo ../a12-kernel-rust-spike # replay the baseline and mutations, then exercise checker guards
lake exe checkCandidateConformance --self-test --suite reference/single-group-correlation-v2.conformance.json
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v2.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/single-group-correlation-v2.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/flat-validation-empty-logic-v2.conformance.json
./scripts/check-lean-trust.sh       # reject proof/runtime escape hatches and audit theorem-root axioms
lake env lean A12Kernel/Core.lean   # elaborate a single module with imports available
```

The canonical red/green workflow, executable-example conventions, proof/trust boundary, external replay method, and final gate are documented in [`docs/TESTING.md`](docs/TESTING.md). Follow it for every semantic capsule.

## Layout & the staged build order

- [`A12Kernel.lean`](A12Kernel.lean) — library root for the trusted semantics, proofs, and in-library conformance modules identified below; process and evidence drivers remain separate.
- [`A12Kernel/Core.lean`](A12Kernel/Core.lean) — the truth/polarity algebra and value domain: `K` (strong-Kleene, no negation), `Polarity`, `Verdict` + `conj`/`disj`, `ScaleInfo`, `NumField`, `Value`.
- [`A12Kernel/Cell.lean`](A12Kernel/Cell.lean) — the phase-sensitive cell model: `FormalCause`, `Phase`, `CheckedCell`, `CellObservation` (empty ≠ invalid, refined into a phase-indexed read).
- [`A12Kernel/Document.lean`](A12Kernel/Document.lean) — addressing & instance: `RowAddr`/`CellAddr`, `Document` (instantiated rows kept separate from cell values), `Env`, `World` (injected clock).
- [`A12Kernel/Semantics/`](A12Kernel/Semantics/) — phase observation; shared scale-19 numeric truth and directional fillability; the flat Number/Boolean/Confirm core plus direct String equality and String `Length <`/`>=`; staged absolute-required semantics; narrow ordered single-group iteration; and captured-outer `$` correlation with filter-only origins, selected presence, a separate outer guard, and per-row firing.
- [`A12Kernel/Elaboration/`](A12Kernel/Elaboration/) — checked lowering from structured, parser-independent surface subsets: normalized flat path resolution, model-derived cell policies, and the narrow String/Length surface with String presence rejected, plus one exact group-qualified direct-child star with correlated Number/repetition comparisons, explicit group/scope binding, and operator-specific scale legality.
- [`A12Kernel/Reference/`](A12Kernel/Reference/) — the normalized protocol vocabulary, strict JSON and exact-decimal transport, explicit historical/current reference-semantics lineage, generated per-operation support metadata, closed decoder, and pure adapters to the existing checked flat and one-group correlation evaluators. The current executable advertises 0.3.0 through the v2 manifest; the 0.2.0 v1 shipment remains digest-frozen history. Requests have no per-request semantics selector, so consumers identify the account through the exact binary's `--manifest` output and pin those bytes. These process-boundary modules are outside the library, conformance, and trusted-proof roots.
- [`A12Kernel/Proofs.lean`](A12Kernel/Proofs.lean) — trusted theorem root importing algebra, information-order, observation, required-staging, directional numeric polarity, the direct-String-versus-`Length` distinction, flat and one-star declaration/context coherence, fail-closed repeatable routing, ordered-selection/filter-before-consumer, correlated origin/judgment/selection/self-match, and selected-consumer observation-footprint proofs. Checked-wrapper lemmas expose carried structural certificates; do not describe them as surface-to-core semantic preservation. [`A12Kernel/TrustAudit.lean`](A12Kernel/TrustAudit.lean) and [`A12Kernel/Trust/Environment.lean`](A12Kernel/Trust/Environment.lean) keep the human-readable theorem reports and the authoritative elaborated-declaration audit separate from the trusted roots they inspect.
- [`A12Kernel/Conformance.lean`](A12Kernel/Conformance.lean) — executable locks for the supported fragment, including directional unsigned/signed/fixed Number polarity, direct String equality versus grow-only `Length`, UTF-16 code-unit length, String rejection boundaries, one-group iteration/correlation separating cases, checked one-star lowering and rejection classes, candidate-row validation, `empty=zero` and malformed-local filters, admitted numeric and repetition comparisons, symmetric malformed dropped-versus-kept consumers, and checked non-laws; these are semantic examples, not a substitute for external differential evidence.
- [`A12Kernel/EvidenceMain.lean`](A12Kernel/EvidenceMain.lean) — IO-only `lake test` driver for retained runtime and static authoring observations, including the separate six-case operator-sensitive Number/String projection; it is outside the library, conformance, and proof roots. [`A12Kernel/Evidence/FlatProtocolBridge.lean`](A12Kernel/Evidence/FlatProtocolBridge.lean) owns the frozen typed eight-case capability descriptor, its non-writing projection-to-protocol artifact checker, and the source-maintainer mutation qualification plan; [`A12Kernel/FlatHandoverMain.lean`](A12Kernel/FlatHandoverMain.lean) exposes the check and deliberately rejects historical writes. [`A12Kernel/Evidence/OperatorProtocolBridge.lean`](A12Kernel/Evidence/OperatorProtocolBridge.lean) independently binds the current flat suite's directional witness to retained evidence and its normalized request/response. [`docs/EVIDENCE.md`](docs/EVIDENCE.md) owns the exact current evidence inventory and claim boundary; the mutation plan is testing metadata, not evidence. The internal String/Length capsule is not part of the normalized public protocol or frozen Rust capability.
- [`A12Kernel/ReferenceMain.lean`](A12Kernel/ReferenceMain.lean) and [`A12Kernel/ReferenceProcessTestMain.lean`](A12Kernel/ReferenceProcessTestMain.lean) — the one-request CLI and its independent process-level regression gate. [`A12Kernel/CandidateConformanceMain.lean`](A12Kernel/CandidateConformanceMain.lean) runs language-neutral capability suites against independent candidates without adding semantics. [`docs/PROTOCOL.md`](docs/PROTOCOL.md) owns the public contract; [`docs/IMPLEMENTER-KIT-CORRELATION.md`](docs/IMPLEMENTER-KIT-CORRELATION.md) and [`docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) own the frozen 0.2.0 handovers, while the v2 suites are the current candidate controls.
- [`A12Kernel/Qualification/`](A12Kernel/Qualification/), [`A12Kernel/MutationQualificationMain.lean`](A12Kernel/MutationQualificationMain.lean), [`A12Kernel/Differential/`](A12Kernel/Differential/), and [`A12Kernel/GeneratedDifferentialMain.lean`](A12Kernel/GeneratedDifferentialMain.lean) — separate nontrusted process lanes for source-side mutation packets/replay and bounded generated candidate differentials. [`A12Kernel/Process/`](A12Kernel/Process/) supplies their digest and bounded relay helpers. None is imported by the trusted library, conformance, proof, or evidence roots; they carry no semantic or kernel-evidence authority. [`docs/TESTING.md`](docs/TESTING.md) owns the methods and commands, while [`docs/ARTIFACTS.md`](docs/ARTIFACTS.md) owns profile, packet, and result lifecycles.
- [`A12Kernel/Basic.lean`](A12Kernel/Basic.lean) — smoke module.

The design decisions behind these types (extrinsic AST, `Rat` + rendered stored-form, the unified `Verdict`, the two-level cell model, the `Document` split, the injected `World`) are recorded with rationale in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

Build the executable theory **bottom-up** in the order of [`spec/13-lean-encoding-guide.md`](spec/13-lean-encoding-guide.md) §3 — scalars & literals → `CheckedCell`/`formalCheck`/phase observation → flat Kleene eval → required/index desugaring → the iteration environment → paths → polarity → computation → partial validation → interpolation/custom. Close each stage's evidence and required proof obligations before the next; the **ten encoding traps** (encoding guide §2) are where naive attempts silently diverge.

Every new semantic clause must link to its read-only `§n` spec and evidence, state whether it is empirically checked, formally proved, deliberately counterexampled, or still open, and update [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) once that surface exists. Record non-obvious settled treatment in [`docs/LEAN-FINDINGS.md`](docs/LEAN-FINDINGS.md). Never use theorem counts or `0 sorry` as a substitute for reviewing the exact statement, hypotheses, direction, result domain, and axiom dependencies.

For Lean-specific architecture and proof-engineering choices, inspect the audited cloned projects' actual sources before promoting a practice. Cedar is the primary precedent for executable specification, validation/theorem separation, proof-root coverage, residual error claims, tests, and differential boundaries; Radix is a compact secondary check for relational/evaluator bridges, transformation proofs, and checked exposition that consumes the live theory. If their patterns conflict, prefer Cedar unless A12's semantics or clean-room boundary supplies a documented reason otherwise. The audited revisions and transferred lessons live in [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md) and [`docs/LEAN-FINDINGS.md`](docs/LEAN-FINDINGS.md).

## Conventions

- **English is canonical** — code, identifiers, comments, docs — matching the A12 OSS family.
- **Lean comments:** Use `/-! ... -/` for a nontrivial module's purpose, semantic scope, and boundary; `/-- ... -/` for public semantic declarations and main theorems; and `--` only beside a non-obvious implementation or proof choice. Following a12-dmkits' intent, explain rationale, phase or context, an invariant or counterexample, and a short provenance pointer (`spec/` section, finding, or evidence ID) when those facts are not evident from the types or statements. Never narrate Lean syntax, restate an encoded definition or truth table, document routine proof steps, or let prose claim more than the formal statement. Keep durable analysis in [`docs/`](docs/); code comments stay concise, local, and synchronized with tests and proofs.
- **Commits:** Conventional Commits (`type(scope): subject`, imperative, lowercase type); subject-only by default, a 1–2 sentence body only for a non-obvious *why*.
- Keep this file tool-neutral; [`AGENTS.md`](AGENTS.md) is a symlink to it so Codex and other AGENTS.md-reading agents get the same guidance.
