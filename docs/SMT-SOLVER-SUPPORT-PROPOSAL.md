# SMT-backed analysis and accepted-document synthesis

> **Status:** proposal, pending adoption, 2026-07-18. This document owns the proposed satisfiability, contradiction-analysis, accepted-document synthesis, and SMT integration architecture. Current implementation state remains in [`PLAN.md`](PLAN.md), [`ARCHITECTURE.md`](ARCHITECTURE.md), and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md). No solver, package, runtime dependency, public command, or support claim is adopted by this proposal. Once adopted and implemented, durable contracts graduate to their owning documents and this proposal is retired or narrowed to unresolved work.

The [G40 contract](../../a12-rulekit/docs/FEATURE-GAPS.md#3-open-backlog) correction landed in a12-dmkits revision `93e2bd57fc53db49cd36b743d3912e2dc5088df2` across its current gap, seed, CLI, interpreter, and example owners. Seed-vocabulary and shipped-command follow-ups landed at revisions `71dd93df111c88eab701f9b6f94310c8e29eb825` and `68c9e9556dbe838dac662ce48d650f9d0adbcd91`; revision `bcd74cefc4db161e592edfd2dc7912b7f65d8a02` then aligned the documented focused run with its JVM-only command. Reconciliation against that clean sibling HEAD confirmed that G40 remains open, distinguishes condition reachability, model inhabitance, and computation-table partition analysis, preserves the SME/TDG evidence and two independent demand gates, and adds no analyzer, solver, dependency, command, or behavior. Every future upstream handoff must still re-audit the then-current revision.

## Decision

Use a hybrid architecture. Lean owns the precise analysis questions, the checked model fragment, the accepted-document relation, a solver-neutral constraint semantics, directional lowering theorems, strict result decoding, and mandatory replay of every SAT witness. An external SMT solver performs search over canonical SMT-LIB2 produced outside the trusted logical core.

Do not translate raw A12 syntax directly to SMT-LIB2 and treat solver output as semantic authority. The safe route is checked A12 model → query-specific semantic constraints → SMT-LIB2, with a proof or an explicit assurance limit at each arrow.

The long-term whole-model query is:

```text
∃ document. Accepted(profile, model, document)
```

`SAT` can yield a model-accepted sample only after the assignment is decoded and the resulting finite document passes Lean replay under the identical model, world, bounds, and acceptance profile. `UNSAT` means no accepted document only when the supported fragment is complete for that profile, every semantic witness can be represented by the SMT encoding, and the result's solver or certificate trust is stated.

This direction fits the existing Analyze and Synthesize categories in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#general-consumer-task-categories) and the witness-checking boundary in [`USE-CASES.md`](USE-CASES.md#7-synthesize). It does not authorize reordering the semantic closure owned by [`PLAN.md`](PLAN.md).

## The queries must stay distinct

An A12 authored rule states an error condition: `fired` means the input is invalid. This reverses the intuition behind the word “contradiction” and requires separate query names.

| Query | Exact question | Meaning of SAT | Meaning of UNSAT |
|---|---|---|---|
| `conditionTruthReachable` | `∃ admissible local context. target error condition is true` | The selected condition has a truth witness; outer rule gates may still prevent a message | The condition is dead and therefore its rule cannot fire within the stated fragment and bounds |
| `ruleFiringReachable` | `∃ admissible document/context. full target rule fires after its iteration/content/eligibility gates` | The target rule has an actual firing witness | The full rule is dead within the stated fragment and bounds |
| `modelInhabited` | `∃ document. Accepted(profile, model, document)` | At least one accepted document exists | No accepted document exists within the stated fragment and bounds |
| `rulesCanCoFire` | `∃ admissible context. left fires ∧ right fires` | The two rules can fire together | They cannot co-fire within the stated fragment and bounds |
| `alternativeOverlap` | `∃ admissible normally evaluated computation context. common guard = true ∧ preconditionᵢ = true ∧ preconditionⱼ = true` | Two ordered alternatives are simultaneously eligible under an enabled table | This pair does not overlap within the stated fragment and bounds |
| `alternativeGap` | `∃ admissible normally evaluated computation context. common guard = true ∧ every alternative precondition = false` | An enabled table has a missing-case witness | Enabled tables are covered within the stated fragment and bounds |
| `constrainedSample` | `∃ document. Accepted(profile, model, document) ∧ goal(document)` | An accepted sample satisfying an extra coverage goal exists | No such sample exists within the stated fragment and bounds |

For reachability and co-firing, “admissible context” means that model/document structure, scalar domains, formal checks, generated eligibility gates, world, and bounds satisfy the query profile. `conditionTruthReachable` deliberately observes the selected condition before the outer rule gate, while `ruleFiringReachable` includes the admitted full-rule iteration, content, relevance, and eligibility gates. Neither silently requires unrelated authored rules to pass unless the profile explicitly adds that constraint.

`[A] > 5 And [A] < 3` as one error condition is an unreachable rule: it never fires. It does not make the model uninhabitable. By contrast, two ERROR-severity rules `[A] <= 5` and `[A] > 5` over a required, formally valid `A` exhaust the domain and can make the model uninhabitable. The latter conclusion still depends on requiredness, field domain, row eligibility, and the selected acceptance profile.

“Contradiction checker” may remain reader-facing product language only when every result identifies its exact query. Internal APIs, support manifests, results, and proofs use the unambiguous names above.

## Accepted document is a named semantic contract

An accepted sample is not merely a document on which no authored rule returns `fired`. A malformed value can make a condition `unknown`, and a naive encoding could exploit that suppression to manufacture a false success. Acceptance must independently establish the preceding structural and formal obligations.

An eventual `Accepted profile model document` relation must compose, in the selected profile's exact order:

1. model-relative document topology and address well-formedness;
2. raw-to-scalar classification or an explicitly named pre-classified trust boundary;
3. declared field constraints and formal checking;
4. generated checks such as requiredness, index requirements, and repetition limits;
5. computation scheduling, root-store checks, application, and dependency propagation for the admitted computation fragment;
6. authored validation over the resulting state;
7. the profile's severity, suppression, and message policy.

The initial profiles should be closed data, not prose flags. Candidate meanings to research and then pin are:

- `kernelAccepted`: no finding or authored message whose severity makes the document invalid under the selected kernel account;
- `fullyDecided`: `kernelAccepted` plus no disallowed validation `unknown` or suppression;
- `strictNoMessages`: no formal, generated, or authored message at any severity.

These are proposal names, not current claims about SME TDG or the kernel. The exact severity and suppression behavior must be derived from the relevant semantic capsules and retained evidence before a profile is admitted.

`modelInhabited` means full validation. A partial-validation run over a relevant set can establish only a separately named page/subset claim, never whole-model acceptance; its relevant set, wildcard semantics, automatic global relevance, and one-directional guarantee would all be part of that separate query identity.

Test-data goals such as “instantiate at least one row,” “fill this optional field,” or “hit a numeric boundary” are separate query conjuncts. Firing an invalidating ERROR rule is incompatible with `Accepted` and belongs to `ruleFiringReachable`; a WARNING/INFO firing goal may be conjoined with `Accepted` only when the selected profile permits it. Goals must never be smuggled into the definition of model acceptance.

The world is also part of the query identity. `Today`, `Now`, base year, timezone rules, and custom oracles cannot read ambient state during translation or replay. A profile either fixes their versioned inputs through [`World`](../A12Kernel/Document.lean) or rejects the dependent construct.

## Architecture

The intended data flow is:

```text
a12-dmkits expanded model bytes
              |
              v
checked finite Lean model + query/profile
              |
              v
solver-neutral constraint relation ---> canonical SMT-LIB2 ---> bounded external solver
              |                                                        |
              |                                                        v
              +<--- mandatory Lean replay <--- decoded finite document assignment
```

The solver-neutral constraint relation is the semantic bridge. SMT-LIB2 is one serialization/backend projection of that relation, not the source of meaning.

Any implementation would need a separately adopted analysis task profile, compatibility identity, support manifest, and command surface. It must not be added as an incidental operation of the current reference evaluator: Execute and Analyze/Synthesize have different inputs, result algebras, resource limits, and assurance claims. The public profile and product progression remain owned by [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) and [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md).

### Ownership

| Concern | Owner |
|---|---|
| Rule, computation, formal-check, document, and orchestration semantics | Trusted Lean semantic modules and their existing owning documents |
| Surface-model resolution and proof-bearing admission | Lean checked elaboration |
| Finite expanded-model transport from a real A12 model | a12-dmkits, through a future versioned export handoff |
| Query/profile vocabulary and support predicate | Lean analysis shipment |
| Constraint AST, denotation, and lowering theorems | Lean logical zone |
| SMT-LIB2 rendering, solver invocation, output parsing, and resource limits | Nontrusted Lean analysis/process zone |
| SAT witness replay | Lean executable semantics under the pinned query/profile |
| Concrete A12 document rendering and re-import validation | a12-dmkits product integration unless a later proposal assigns it elsewhere |
| Kernel correspondence | Retained producer-certified observations plus explicit evidence status, never solver agreement alone |
| Product packaging, bundled solver choice, and dmtool UX | Separate adoption decisions in the repository that ships them |

## Versioned request and result contracts

Every request must pin:

- a schema and semantic-profile version;
- one closed query kind;
- a checked supported-fragment identifier;
- the complete finite model bytes and their digest;
- a fixed world;
- repetition, String-length, and other search bounds not already fixed by the model;
- the acceptance, full/partial-validation mode and relevant set, severity, suppression, computation, and application policy;
- optional query-specific goals;
- deterministic resource limits.

Support is a checked predicate over the actual model and query, not a caller assertion. Any unsupported field kind, operator, path shape, repetition shape, computation feature, custom hook, world dependency, or bound must fail closed and identify the rejected capability.

Every solver-invoked result binds the analysis-semantics and constraint-encoding versions, canonical SMT formula digest, query/model/profile/bounds identity, solver name and version, deterministic options and seed, source-map version, replay executable/manifest identity, and solver executable or package identity where portable identification is available.

Results use a closed algebra such as:

- `verifiedSat`, additionally carrying the decoded finite document and exact replay result;
- `solverReportedUnsatWithinBounds`, carrying exact bounds, solver identity, and optional nonminimal core;
- `certifiedUnsat`, reserved for a later checked certificate or complete finite proof path;
- `unknown`;
- `timeout`;
- `unsupported`;
- `solverProtocolError`;
- `replayRejected`.

Never collapse `unknown`, timeout, unsupported translation, protocol failure, and UNSAT into one “no sample” result. Never return a raw solver model as a verified sample.

Repetition bounds are part of result identity. A SAT witness found within a bound remains a genuine replayed witness. An UNSAT result is only bounded unless declared finite maxima or a proved cutoff theorem establishes that the search covers every semantic document.

## Constraint and SMT-LIB2 design rules

### Model and document structure

The future checked whole model uses finite ordered lists with stable field, group, rule, and computation identities; uniqueness checks; explicit authored order; and explicit computation schedule order. It should aggregate checked semantic components rather than stretch the current field-resolution-only `FlatModel` into a universal model.

A future finite `DocumentData` carries instantiated rows and sparse raw or classified cells as lists, validates duplicate addresses and model-relative scope/topology, and compiles to the existing functional semantic views. [`Document`](../A12Kernel/Document.lean) and evaluator contexts remain convenient pure lookup abstractions.

Row activation and cell presence are separate variables. A blank instantiated row remains observable. The existing narrow caller-supplied `hasContent` input must not become a free SMT variable; the whole-document adapter derives row eligibility and content gates from validated document topology and field presence.

Repeatable rows use bounded activation plus ordered, contiguous semantic indices where the selected profile establishes that representation. Zero rows, blank rows, omitted tails, nested scopes, and row-order effects receive separating cases. Set-based encodings are insufficient because iteration and computations observe order.

### Values and formal validity

Each future field constraint becomes first-class executable policy data in the model. Numeric bounds, enum domains, String constraints, date ranges, required/index roles, and repetition limits cannot exist only as a caller-supplied `.rejected .declaredConstraint`, because both translation and replay must derive the same formal result from the same model.

Keep operator configuration separate from formal-input constraints. In particular, [`NumField.signed`](../A12Kernel/Core.lean) drives directional fillability and is not a lower bound. Do not overload it with every authoring constraint merely to simplify the solver.

Preserve exact `Rat` semantics and every named normalization point. A closed numeric profile may lower values to scaled SMT integers, but only with an explicit bridge to A12 scale-19 `HALF_UP` comparison and stored-form constraints. Translating all Number values to unrestricted SMT `Real`, or inferring non-negativity from `signed = false`, would be unsound.

Boolean and Confirm must preserve absence and Confirm's stored-true restriction. Enum tokens require a first-class finite domain. Dates require a fixed world and an exact ordinal/calendar bridge. Strings require the already established one-pass CRLF ingestion, UTF-16 length, charset/newline policy, and a deliberately closed regex/string-theory subset before admission.

Formal-invalid values are not a shortcut to rule suppression. The accepted-document encoding asserts field and generated-check validity independently of authored rule truth.

### Rules and computations

Authored error rules are encoded as non-firing constraints according to the acceptance profile; they are not translated as business requirements with their surface polarity unchanged. `conditionTruthReachable` instead asserts that its selected error condition is true before the outer rule gate, while `ruleFiringReachable` asserts the complete admitted rule fires; neither requires the witness document to be accepted.

No generic A12 `Not` should be added to simplify analysis. Query-level complement and meta-negation belong to the constraint language, with proved connections to the specific A12 verdict and acceptance predicates.

Computations are ordered state transitions. Computed targets are derived states, not unconstrained SMT inputs, and alternatives preserve the optional common precondition, authored first-match order, evaluator truth, expression evaluation, root-store checks, application, poison, and subsequent reads. A clean false common precondition disables the table and is neither an alternative gap nor an overlap, while an absent common precondition behaves as enabled; an absent alternative precondition is the unconditional true alternative. Unknown or poison during the guard or alternative checks remains its own computation outcome, not a clean gap/overlap witness. The current expression, root-store check, target check, payloadful outcome, deliberately lossy value projection, delta, and exact one-address String target-application state are separate and should remain so. General finite-document mutation, repeatable target addressing, scheduling, raw-text preservation, and multi-target application remain later explicit transitions; simultaneous equations would admit states the evaluator cannot produce.

Custom validators, custom conditions, external labels, timezone behavior without pinned rules, unrestricted regex, and other oracles are unsupported until each receives a finite exact contract. An uninterpreted SMT function is not an acceptable substitute when its arbitrary interpretation could create or remove a witness.

### Rendering and explanations

Use tagged solver symbols derived from stable typed IDs, not raw path text or unqualified natural numbers. Maintain a versioned source map from every named assertion to its semantic origin.

Name field-domain, topology, generated-rule, computation, shape-goal, and authored-rule assertions separately. An unsat core may include any of them. It is an explanation aid, not a proof, a guaranteed minimum conflict, or necessarily a list of authored rules.

Prefer one-shot canonical solver interaction for the first profile: bounded SMT-LIB2 input, explicit requested values, bounded stdout/stderr, deterministic options, and strict parsing. Interactive incremental solving and solver-specific model syntax can wait for a measured need.

A solver assignment first decodes into typed finite document data. A concrete serialized A12 document additionally needs canonical value rendering and a checked re-import/evaluation path. Until that cross-project path exists, call the output a verified normalized semantic witness, not a ready-to-use model document.

## Assurance and trust

Two lowering directions have different payoffs and must be named theorem by theorem:

1. `assignment satisfies constraints → source query holds` supports semantic trust in a decoded SAT witness; mandatory Lean replay is still required at the process boundary.
2. `source query witness → some assignment satisfies constraints` is required before solver UNSAT can imply semantic UNSAT for the stated fragment and bounds.

SAT is the lower-risk first result class. Strict decoding plus Lean replay can reject errors in rendering, solver behavior, model parsing, and assignment decoding. The result is a checked witness, not a proof that the generator is complete.

UNSAT additionally trusts the query lowering, SMT renderer, and solver unless a certificate is checked. Initial negative results should therefore be labeled `solverReportedUnsatWithinBounds`, even when both lowering directions are proved. A later finite exhaustive checker or proof-certificate path may justify `certifiedUnsat`; Z3 proof parsing, unsat-core interpretation, and certificate portability are not first-slice requirements.

Lean proofs establish consequences of the chosen Lean semantics. Retained kernel observations are still required before the supported fragment is described as kernel-correspondence complete. Agreement between Lean, a12-dmkits, and a solver is valuable triangulation, not a universal kernel theorem.

Solver execution should reuse the settled bounded-process lane where compatible rather than introduce another runner: explicit input/output/time caps, candidate-status separation, streamed output, process-group cleanup, and independent lifecycle checks. That lane is currently a cooperative macOS/Linux resource boundary, not hostile-code containment or a cross-platform packaging decision. No solver executable, binding, Lake package, bundled native binary, or distribution change may be adopted without the repository's separate dependency approval and release-impact review.

## Architecture audit and preparation invariants

This source-audit snapshot was refreshed at a12-kernel-lean revision `d975cd89183a8094a0d41905b8afafb860ed2a57`, after exact one-target String application, the narrow clean-Boolean common-precondition seam, bounded candidate-process hardening, the semantic-first simplification decision, and retirement of completed one-off shipment machinery. The computation-condition row below was subsequently refreshed against the direct presence result that replaced that Boolean seam; the rest is not live implementation status. Exact current coverage remains owned by [`ARCHITECTURE.md`](ARCHITECTURE.md) and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); re-audit these seams if their source changes before implementation. The snapshot still found useful existing seams but no checked whole-model object or accepted-document relation sufficient for the proposed query.

| Audited source seam | Keep or prepare | Reason for SMT work |
|---|---|---|
| Extrinsic surface AST plus [`CheckedFlatCondition`](../A12Kernel/Elaboration/Flat.lean) | Keep; future lowering consumes only a checked whole model | Prevents raw paths, kinds, scales, and caller metadata from disagreeing |
| [`FieldPolicy`](../A12Kernel/Semantics/Observation.lean) currently contains only kind | Add first-class constraint policies one semantic capsule at a time | The solver and replay must derive bounds/domains instead of trusting preclassified rejection |
| `FlatModel` currently owns fields, repeatable groups, and reference policy | Keep narrow; add a separate finite checked whole-model aggregate when its first consumer lands | Rules, severity, computations, schedules, and generated checks need ordered model ownership |
| [`Document.rawCells`](../A12Kernel/Document.lean) and contexts are functions | Add a finite checked adapter; do not replace the functional semantic views | Transport, solver variables, uniqueness, and witness decoding require finite data |
| Instantiated rows are separate from cells | Preserve | Row activation, blank rows, cell presence, and content gates are different facts |
| Lists preserve row and computation order | Preserve | Set or simultaneous-equation encodings would change observable behavior |
| `K`, `Verdict`, formal findings, and phase-sensitive observation are explicit | Preserve | Acceptance cannot collapse empty, invalid, unknown, poison, and non-firing |
| `Rat` and declared scale are separated; general numeric stored-form semantics remains open | Preserve the separation; close rendering explicitly and prove any scaled-integer lowering | Avoids silent Number and representation drift |
| [`World`](../A12Kernel/Document.lean) is explicit | Require one fixed world per query | Makes date/time-dependent search deterministic |
| Computation expression, store, target check, outcome, value projection, delta, and exact one-address String application are separated | Preserve the distinctions; extend only through explicit finite-document state, repeatable addressing, and scheduling capsules | Prevents unconstrained or simultaneous computed targets without overstating the narrow application state as whole-document mutation |
| [`ComputationConditionResult`](../A12Kernel/Semantics/ComputationCondition.lean), direct presence, and ordered `And`/`Or` preserve clean not-true versus poison; [`evaluateOutcomeWhen`](../A12Kernel/Semantics/StringCascade.lean) consumes that result before the body | Reuse this result boundary and ordered connectives; add checked finite contexts and first-match alternatives explicitly | Supports poison-aware table analysis without pretending that direct presence already supplies condition partitions or whole-model checking |
| Support manifests use closed enumerations and fail closed | Reuse as a separate analysis profile | Makes every admitted model/query and every exclusion machine-readable |
| Logical and process zones are audited separately; the bounded relay remains while one-off artifact, differential, and qualification frameworks are retired | Make an explicit adopted source-zone decision when implementation begins; reuse only the settled subprocess mechanics | Constraint denotation/proofs belong to the logical zone; SMT rendering and solver IO do not, and retired shipment machinery is not a future analysis template |

The low-cost decisions to apply during nearby semantic work are:

- give new model declarations stable IDs and preserve their authored or scheduled order;
- represent field-domain constraints and generated roles as model data, not solver annotations;
- keep structural row existence separate from field presence and derive every content gate;
- expose finite checked adapters at transport boundaries while leaving semantic lookup APIs pure;
- state whole-model `WellFormedDocument` and `Accepted` relations when the necessary formal/generated validation and orchestration semantics land;
- keep canonical raw rendering and parse/re-import round trips separate from semantic values;
- keep query meta-negation out of the A12 condition AST;
- continue proving evaluator/relational bridges for ordered iteration and state transitions;
- avoid an empty generic SMT framework before the first closed profile supplies concrete types and separating tests.

No Lean source change is justified now solely for SMT, and this proposal does not authorize reordering semantic closure. [`PLAN.md`](PLAN.md) remains the sole owner of the current sequence. When nearby semantic work extends exact application, computation-condition evaluation, generated validation, domains, iteration, or scheduling, it should preserve the explicit distinctions above rather than add solver-specific shortcuts.

The stages below are semantic prerequisites, not permission to prebuild a generic analysis schema, registry, renderer, runner, or qualification framework. Land the required semantics as ordinary Tier 1 capsules first. Add solver IO and shipment qualification only for an explicitly adopted Analyze or Synthesize consumer, reuse the settled bounded-process lane where it fits, and do not restore retired one-off shipment machinery as anticipated infrastructure.

## Staged delivery

These stages state technical dependency order for a future experiment. They are not an adopted product/release progression and do not replace the active sequence in [`PLAN.md`](PLAN.md). A public task profile, CLI, release, or dmtool integration requires an explicit adoption change in its owning project documents.

### Stage 0 — fixed query contract

The query taxonomy, acceptance-profile requirements, trust directions, and early Lean invariants are fixed here and in LF17 in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md#lf17--dead-error-conditions-and-uninhabitable-models-are-different-queries). a12-dmkits [G40](../../a12-rulekit/docs/FEATURE-GAPS.md#3-open-backlog) independently adopted the same three-way distinction while keeping the analyses unimplemented and demand-gated. This prerequisite changes no solver behavior and adopts no dependency.

### Stage 1 — solver-free reachability

After checked flat numeric ordering and first-class numeric bounds exist, implement a small interval/domain analyzer for `conditionTruthReachable` over a closed single-field fragment. Prefer a proved decision procedure or a checker with exact false-negative boundaries. An UNSAT local result proves the full rule dead, but a SAT local result does not by itself establish that the outer full-rule gates can fire. Do not advertise the analyzer as whole-model contradiction detection.

The a12-dmkits solver-free lint can proceed independently when its demand trigger is met. Its typed authoring surface and actual reachable AST must determine the supported cases; an out-of-domain enum literal rejected before AST construction is not a useful lint case.

### Stage 2 — `flat-satisfiability-v1`

Admit only full validation over nonrepeatable Number, Boolean, and Confirm fields; first-class scalar domains; the existing narrow absolute-required staging represented as an explicit model role; a finite ordered list of ERROR rules; the checked flat comparison/presence fragment extended with the ordering operators the profile names; and a fixed world with no time-dependent constructs. No generated check is implicit: each field is either not required or carries exactly the admitted absolute-required role whose generated rule and staged finding are included by `Accepted`. Reject partial-validation relevant sets, index/global roles, other generated-validation shapes, computations, custom hooks, Strings, enums, dates, and repeatable groups.

The proposed initial query set is `conditionTruthReachable`, `ruleFiringReachable`, `modelInhabited`, and `constrainedSample`; co-firing and computation-partition queries remain unsupported. Deliver the finite checked model, finite document adapter, exact `Accepted` relation, support predicate, solver-neutral constraint semantics, canonical SMT-LIB2 projection, bounded external solver lane, strict SAT decoding, and mandatory replay. This profile explicitly begins at the pre-classified scalar boundary used by `RawCell`; its verified output is a normalized semantic witness, not proof of concrete raw-document parsing or serialization. Begin with `verifiedSat`; label negative results `solverReportedUnsatWithinBounds`.

Qualify the profile with a tiny exhaustive finite-domain oracle in addition to examples, property tests, focused lowering-mutation checks, replay-rejection tests, and retained kernel observations for every semantic clause claimed. Any shipment-level qualification lane must be justified for this consumer rather than restoring the retired generic campaign machinery.

### Stage 3 — scalar domains one capsule at a time

Expand the admitted model syntax, not the query algebra. Add enum, restricted String, and date fragments only after their formal constraints, raw/semantic rendering boundary, world inputs, SMT theory choice, lowering directions, and external evidence are explicit. A solver's native string or regex support is not evidence that the A12 construct has been encoded correctly.

### Stage 4 — bounded one-group repetition and correlation

Expand the admitted model syntax and list the exact repetition-aware query subset in the new profile. Add one declared bounded repeatable group with explicit row activation, contiguous indices, blank-row controls, candidate ordering, derived content gates, and the exact correlation observer needed by each admitted query. A `modelInhabited` profile at this stage must also enforce the admitted declared repetition maximum and over-repetition behavior; otherwise the stage exposes only bounded iteration/reachability queries, not accepted-document synthesis. Prove the bounded unrolling bridge and label UNSAT with the bound unless the model maximum or a cutoff theorem makes it complete.

### Stage 5 — whole validation

Expand the admitted model and acceptance-profile syntax, not the query set by default. Add the remaining generated-requiredness shapes, index requirements, repetition policies not admitted by Stage 4, severity policy, message/suppression handling, and every remaining validation construct needed by the selected whole-model profile. Only at this stage may a sufficiently covered fragment be described as whole validation rather than flat satisfiability.

### Stage 6 — ordered computations

Expand the model syntax with a complete admitted computation schedule and add the separate `alternativeOverlap`/`alternativeGap` query kinds. Preserve common-guard semantics, ordered alternatives, target checking, application state, dependency propagation, and subsequent validation. Computation overlap/gap remains query-specific even after the same constraint backend can answer it.

No stage may call itself “whole-model translation” while its manifest rejects a model feature present in the input. Unsupported models fail before solver invocation.

## a12-dmkits engagement plan

The sibling checkout stays read-only. The user carries each request upstream, and this project consumes only committed handback.

### First future handoff — versioned expanded analysis-model export

Mint `docs/A12-DMKITS-SMT-MODEL-EXPORT-PROPOSAL.md` only after the Lean consumer has fixed the first exact schema, checked support predicate, sample fixtures, and mutation predictions. Register that temporary handoff in [`README.md`](README.md), have the user carry it upstream, and delete it after accepted handback and migration of durable facts.

That proposal must pin:

- the audited a12-dmkits revision and exact expanded-model source mechanism;
- the versioned canonical bytes and digest rules required by the Lean consumer;
- stable typed IDs, ordered fields/groups/rules/computations, severity, first-class domains, generated and relevance/global roles, repetition declarations, world inputs, and source provenance admitted by the selected profile;
- producer validation and unsupported-feature behavior;
- a12-dmkits ownership of concrete model loading/expansion and Lean ownership of semantic admission;
- backward compatibility, schema evolution, retirement, and fixture lifecycle;
- separating fixtures for polarity, absent versus malformed, generated checks, row topology/order, computations when admitted, and source identity;
- predicted failures for dropped rules, reversed order, altered bounds, missing generated roles, duplicate IDs, changed severity, and unsupported constructs falsely admitted;
- maintained export commands, focused tests, documentation updates, and exact handback format.

Do not ask a12-dmkits to freeze an undifferentiated “whole model” before the first consumer profile can name the exact transported declarations and feature markers. The export must nevertheless carry a complete feature/declaration inventory for Lean support checking. A smaller semantic payload is permissible only when it also carries an explicit omitted-declaration inventory and a closure certificate accepted by a Lean checker; producer certification alone does not establish semantic irrelevance. Silently dropping unsupported fields, rules, computations, or generated roles would invalidate fail-closed admission. Do not reproduce its parser or expander in this repository merely to avoid the handoff.

### Second future handoff — concrete sample rendering and product integration

Mint a separate temporary cross-project proposal after `flat-satisfiability-v1` produces stable verified normalized witnesses. It must decide whether dmtool calls the Lean analysis executable, independently consumes a semantic shipment, or uses another explicitly qualified arrangement; the projects must not drift into two unnamed SMT semantics.

The proposal must cover:

- normalized witness to concrete A12 document rendering;
- canonical per-kind raw values and round-trip re-import;
- final a12-dmkits evaluation under the identical profile;
- CLI naming and the distinction between a field-aware candidate and a model-accepted sample;
- solver discovery or bundling, platform matrix, licensing, native-image and distribution impact, size, update policy, resource controls, and failure diagnostics;
- provenance tying model bytes, query/profile, solver, Lean shipment, normalized witness, concrete document, and replay/evaluation receipts;
- compatibility with the existing best-effort model-derived sample candidate from `model seed`, including whether it remains separate or gains an explicitly named solver-grade mode;
- product acceptance cases and mutation predictions.

Bundling Z3, selecting another solver, adding a runtime library, or changing distribution remains a separate explicit dependency decision even though this proposal recommends the subprocess + SMT-LIB2 shape.

### Engagement discipline

Once an upstream request is reported in progress, issue no parallel implementation request and infer no completion. Reconcile against the actual committed revision and disposition, verify maintained commands and portable artifacts, move durable facts to their owning documents, and delete the completed temporary handoff. Small compatible follow-up fields may use copy-ready prompts; a schema, lifecycle, packaging, or compatibility change requires a proposal.

## Acceptance gates

The first SMT-backed profile is not accepted until all of the following hold:

- each query kind admitted by the profile has one exact relation and separating polarity tests;
- the accepted-document relation independently excludes structural, formal, and generated-check invalidity;
- the checked support predicate fails closed over every model feature;
- finite model and document transports reject duplicates, incoherent scopes, unstable identity, and unsupported shapes;
- assignment decoding is strict and every SAT result passes Lean replay;
- both lowering directions are stated separately, with exact hypotheses and proof/evidence status;
- every UNSAT result names its bounds and assurance class;
- unknown, timeout, unsupported, protocol error, replay rejection, SAT, and UNSAT are distinguishable;
- resource caps and process cleanup are adversarially checked on every supported platform;
- named-assertion provenance includes generated and domain constraints as well as authored rules;
- tiny finite domains are differentially checked against exhaustive enumeration;
- focused lowering mutations fail for the predicted cases, with any shipment-level mutation gate newly justified for this profile rather than inherited from retired campaign machinery;
- external kernel evidence covers every clause claimed as kernel-correspondent;
- a cold consumer can identify the profile, implement or invoke it without hidden repository state, and reproduce a seeded disagreement;
- dependency, licensing, packaging, and release consequences have received separate approval.

## Stop and reevaluation conditions

Stop and narrow the profile if whole-model acceptance cannot be stated without unsupported semantic guesses, if solver encodings start defining A12 behavior instead of preserving it, if replay cannot consume the exact decoded witness, if a required upstream export lacks a maintained owner, or if the runtime/package cost is not justified by a concrete Analyze/Synthesize consumer.

Reevaluate the architecture if a checked portable proof format makes certified UNSAT materially cheaper, a proved cutoff removes important repetition bounds, the solver subprocess cannot meet the bounded-process contract, or a12-dmkits adopts a product constraint that changes the best integration owner. Those are proposal changes, not reasons to silently widen a shipped profile.
