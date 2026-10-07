# Testing methodology

This document is the entry point for the test harness and working method for `a12-kernel-lean`; the triggered guides below own specialized procedures. The project tests five live semantic and process claims—execution of the Lean theory, universal consequences inside that theory, empirical correspondence with kernel 30.8.1, compatibility of the public reference process, and finite retained-case conformance of an independent candidate—and deliberately does not collapse them or repository hygiene into one green check. The completed Rust generated-differential and mutation campaigns remain historical records, not live harness layers.

## Read only the sections your task triggers

Use the headings to select a bounded section; do not read this document or every linked guide wholesale on each task or sub-agent handoff. Reuse already-read instructions until the task or their contents change.

| Task or trigger | Required starting point |
|---|---|
| Starting a semantic capsule or new capability | [Consumer hypothesis](#pre-implementation-consumer-hypothesis) and, when triggered, [keystone pre-audit](#high-connectivity-keystone-pre-audit) |
| Ordinary semantic implementation | [Command ladder](#command-ladder), [red/green](#redgreen-semantic-development), [executable examples](#executable-lean-examples), and applicable [tier gates](#tier-gates) |
| Closure or a triggered review | [Same-context assessment](#same-context-capsule-closure-assessment) and [cold-review triggers](#trigger-based-cold-review) |
| Decide whether population replay is due | [Population-replay cadence](#population-replay-cadence) |
| Prepare or interpret a kernel measurement | [Kernel measurement procedures](TESTING-KERNEL-PROBES.md); select the relevant source, runtime, static or instrument section |
| An authorized peer handoff or returned result | [Peer-session coordination](TESTING-PEER-COORDINATION.md#peer-session-coordination) |
| Public-process, candidate, shipment or release work | [Public-process and candidate testing](TESTING-PROCESS.md) |

The compatibility headings below preserve existing links to specialized procedures. Their linked files own the full instructions.

## Command ladder

Pay only for the narrowest rung that can answer the current question:

1. **Red/green loop:** build the focused semantic-family Lake target, for example `lake build A12Kernel.Conformance.NumericValidation.Comparison`, not its import-only `A12Kernel.Conformance.NumericValidation` umbrella. This refreshes changed imported modules before checking the consumer; direct `lake env lean` elaboration may otherwise read an older built dependency. Stay on this rung while changing the capsule. If the smallest target is an umbrella or a legacy file containing unrelated families, extract the family being changed before extending it; focused compilation is part of the module-boundary acceptance criterion.
2. **Integrated semantic check:** run `lake build` once after the focused modules are green. This checks the complete library, proof root, conformance root, and default executable targets.
3. **Retained evidence:** run `lake test` once for a completed Tier 1 semantic capsule. Add a family-specific replay only when the capsule belongs to an active Tier 2 calibration batch.
4. **Pre-commit trust and hygiene:** run `./scripts/check-lean-trust.sh`, `git diff --check`, `./scripts/check-spec-sync.sh`, and the full status check once after the integrated diff is stable. The trust audit invokes both source and documentation hygiene guards. A successful trust audit emits one summary line; a failure preserves the underlying diagnostics.
5. **Public-process checks:** run `checkReferenceProcess`, `checkBoundedProcess`, and candidate self-tests only when the public process, shipment, or process machinery changed, or before a release.

Do not restart at a more expensive rung after a documentation-only edit unless that document is itself consumed by the corresponding gate.

Lean elaborates and caches one `.olean` per module, so semantic ownership and compilation ownership must agree. Keep import-only compatibility roots at the historical module path, place definitions/proofs/cases in focused child modules, and import the narrowest dependency stratum that actually owns the used declaration. The permanent size policy in [`CLAUDE.md`](../CLAUDE.md#semantic-first-simplification-rule) targets at most 800 nonblank lines and forbids ordinary source above 1,200. `TrustAudit.lean` is the sole current exception: its exhaustive theorem-root presentation intentionally remains one Lean session because splitting it would restore repeated process startup and duplicate environment loading; it contains registry commands only, not semantics or fixtures.

### Lean source-hygiene gate

[`check-lean-source-hygiene.sh`](../scripts/check-lean-source-hygiene.sh) enumerates tracked Lean source with Git, excludes generated/build output, counts nonblank lines, enforces the 800/1,200 thresholds, checks the exact umbrella-root inventory, and validates the exceptional registry structure. Run its dependency-free adversarial fixtures with [`test-check-lean-source-hygiene.sh`](../scripts/test-check-lean-source-hygiene.sh). The default trust gate invokes the source-hygiene guard, so local pre-commit verification and CI share one enforcement path.

The marked entries below are the exact machine-read reviewed-exception map. `review-threshold` may retain one cohesive 801–1,200-line file only with a nonempty reviewed rationale. `exceptional-ceiling` is restricted in the guard to the sole `TrustAudit.lean` registry; adding another path cannot authorize a second over-ceiling file. Remove an entry when its path disappears or its line count no longer needs that mode, because stale and duplicate entries fail the gate.

<!-- lean-source-hygiene-exceptions:start -->
<!-- lean-source-hygiene-exception: A12Kernel/Elaboration/Correlation.lean | review-threshold | The cohesive checked-filter elaborator retains private resolveHavingEntityRead and its typed leaf resolvers; splitting the named-type resolver would expose that private field-read construction without isolating an independently useful build target. -->
<!-- lean-source-hygiene-exception: A12Kernel/Conformance/DateRangeComparison.lean | review-threshold | The cohesive DateRange construction-equality family reuses private model and document fixtures across exact, fragment, yearless, and mixed cases; splitting it would duplicate or expose those fixtures without isolating a useful build target. -->
<!-- lean-source-hygiene-exception: A12Kernel/Conformance/ScalarComputationRun.lean | review-threshold | The cohesive finite scalar-run family reuses private model, checked-table, pattern, and document fixtures across execution, result, formal-input, and authored-order cases; splitting the calibration would duplicate or expose those fixtures without isolating a useful build target. -->
<!-- lean-source-hygiene-exception: A12Kernel/TrustAudit.lean | exceptional-ceiling | The exhaustive theorem-root presentation and environment audit remain one Lean session to avoid repeated process startup and duplicate environment loading; this file contains only audit-driver setup and registry commands, never semantics or conformance fixtures. -->
<!-- lean-source-hygiene-exceptions:end -->

### Documentation-hygiene gate

[`check-doc-hygiene.sh`](../scripts/check-doc-hygiene.sh) guards the implementation and source hubs, their bounded family shards, and the open gap index. It rejects physical claim lines above 1,000 characters, records above 80 physical lines, semicolon-packed omnibus claims, exact revisions or hashes copied into status owners, completed or correction chronology introduced as an open-gap bullet, generic hub links labelled as source checkpoints, files above 200,000 bytes, capability/source records above 24,000 bytes, SG blocks above 12,000 bytes, legacy wide capability tables, duplicate detailed anchors, and shard anchors missing or unlinked from their compatibility hub. The hard ceilings are failure boundaries, not writing targets; the 500-character soft claim ceiling and one-claim-per-bullet rule remain the authoring standard in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md#bounded-detailed-records).

The trust audit invokes this guard. The pre-push publication updater and CI both invoke that audit, so documentation hygiene is checked locally before publication and again remotely without a duplicate workflow step. Fix the owning record instead of adding path or line exceptions.

## Default assurance cadence

The accepted evidence consolidation divides work into three tiers. Tier 1 is the default for a semantic capsule: red/green executable examples, the smallest total definition, proof spine, nearest non-law, assumptions, trust audit, and an explicit evidence status. Tier 2 batches related clauses into one focused external calibration family and replays a compact retained semantic account from an existing suitable route or an accepted purpose-specific handback. Tier 3 runs protocol, independent-candidate, mutation, packaging, and release qualification only for a real shipment or consumer. [`SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) owns the exact trust split, budgets, migration, and stop conditions.

An unavailable external observation no longer blocks unrelated internal semantics or theorem work. Mark the capsule `external evidence pending`, keep the claim narrow, and schedule the smallest useful family calibration. It still blocks a kernel-correspondence-complete or shipment-ready claim.

## High-connectivity keystone pre-audit

Before opening a new capability boundary in SG1, SG2, SG4, SG6, SG9, SG10, or another high-connectivity owner, prepare a bounded source-audit packet in the working context. Name the exact supported family and observable result domain, the source owners, static admission gates, runtime precedence and read order, the common mechanism and true deviations in a compact decision matrix, at least two realistic wrong accounts with separating witnesses, and every unresolved fact with its reopening trigger. Run the highest-risk discriminator first. The packet and separating matrix are mandatory entry gates for the selected keystone, not optional planning aids. If the discriminator disproves the proposed representation, change the design before broadening the family.

The packet is capability-scoped. A subordinate capsule inside an already-audited mechanism consumes the existing packet and prepares no new one. Reopen it when the unit needs a source fact not already closed by that packet and its gap entry, crosses into another engine layer or runtime class, makes a new composition claim, changes the semantic result domain or a representation whose adequacy depends on new source behavior, or disproves a discriminator. A conservative wider finite bound over the same checked tables and behavior is not by itself a reopening trigger; a new Kernel behavior class is. Keep the gap's unresolved-fact and reopening account complete even when the rest of the entry is shortened.

Follow that packet with the consumer hypothesis below, then implement through the existing checked plan, runtime, and result owners without collapsing those phases or creating a parallel representation. Add temporary diagnostics only inside an existing conformance example and remove them before closure. A new runner, schema, trace format, or evidence framework remains prohibited unless the same unmet observation has blocked at least two real semantic families, the current mechanisms have been measured and shown insufficient, and the user explicitly approves the resulting infrastructure work. **Instrument-side throughput tooling is the standing exception** and needs no fresh ask, under the conditions the [owner authorization](../CLAUDE.md#%EF%B8%8F-hard-rule--semantics-first-harness-governance-and-redundant-work-require-explicit-approval) states: the mechanism must remove a *measured* repeated cost, and the commit body must name it.

This packet is working context, not another committed template, receipt, registry, or report. Record only its durable outcomes: implemented status in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), live gaps and reopening facts in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), cross-session sequencing in [`PLAN.md`](PLAN.md) when a handoff fact changes, and a genuinely non-obvious semantic lesson in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md). A cold artifact-only probe remains milestone-triggered rather than per-capsule.

## Pre-implementation consumer hypothesis

Before writing the first red case for a selected semantic capsule, state one compact consumer hypothesis in the working context. This is a design discriminator, not a new committed template or harness:

- name the consumer task, usually Execute plus one or more of Analyze, Transform, or Compile;
- state the exact decision that consumer must make;
- list the minimum semantic distinctions the representation must expose;
- name one realistic unsafe transformation or wrong account;
- predict one public query or result the finished API must support;
- name one explicit `insufficient information` outcome rather than guessing or collapsing it into a semantic result.

Use the hypothesis to choose the red separator and representation before implementation. At same-context closure, run the predicted query against the finished API and verify that the unsafe account remains distinguishable; if the representation cannot answer without renewed source archaeology or consumer-specific reconstruction, fix the semantic root or record the precise open gap. This check adds no runner, schema, registry, permanent report, or per-capsule cold review. Trigger-based artifact-only probes keep the milestone cadence below.

## Same-context capsule closure assessment

After the focused and integrated implementation is stable, the agent that performed the source audit and capsule work must assess the completed unit before the final trust/hygiene gate and commit. Apply the same rule proportionally to every approved substantive architecture, harness, process, or documentation unit. This is deliberately an in-context review: the agent must use its knowledge of rejected accounts, failed red cases, source discriminators, assumptions, measurements, and implementation tradeoffs rather than delegating the retrospective to a cold reviewer.

Every routine capsule always checks:

- **Semantic root and claim scope:** name the invariant and the representation that preserves it. Predict and reproduce a second instance outside the reported example before fixing the shared cause. For a position, phase or carrier distinction, test both sides of the boundary with admitted and refused controls; a one-direction refusal does not establish the boundary. Keep supported scope and kernel-correspondence claims exact.
- **Reuse:** the unit specializes or composes the owner named in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) instead of introducing a parallel representation, and every extracted abstraction has two real completed consumers.
- **Separator and law strength:** the red run failed for the intended reason, and each claimed invariant has a retained separator that would fail under a named realistic wrong account. After replacing an evaluator or carrier, trace the running call site to the law: prove the actual shared mechanism and specialize it, rather than leaving assurance on a legacy path. A law about empty operands does not establish a law about operands whose cells are empty. Keep exact hypotheses and a meaningful nearest false generalization where one exists.
- **Consumer decision:** run the predicted query through the API path whose behavior is claimed. A hand-built outcome or standalone projection proves only that local function; a claim about scheduling, dependent reads or emitted messages needs a lock that executes that path. The named unsafe account must remain distinguishable.
- **Evidence status:** the external status and claim limits are exact, and no internal proof, source reading, or peer agreement is labeled Kernel evidence. Inspect branches that choose an answer to a recorded uncertainty: a caveat cannot justify collapsing distinct runtime effects or exporting an assumed result. Apply the [claim-discharge rule](../CLAUDE.md#%EF%B8%8F-hard-rule--discharge-a-claim-before-stating-it-or-flag-it-and-surface-it) before dependent work proceeds.
- **Document trigger and ownership:** every touched document was actually triggered under [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md), each detailed fact has one owner, displaced copies were deleted or replaced by a local consequence and link, and no stale exclusion or completed narrative remains in an open-only owner. An untriggered document touch is a closure defect even when its prose is accurate.
- **Local consolidation and hygiene:** no obsolete parallel mechanism remains, the support-versus-theory estate ratio still holds, and sibling status is unchanged from the recorded baseline. Trust-root registration, per-file line limits, and leftover artifacts are already asserted by the tier gate and the source-hygiene guard, so do not re-check them here.

Run these checks only when the unit triggers them:

- **Architecture and ownership:** when the unit changes a semantic ownership boundary, representation contract, dependency direction, composition invariant, or adopted or rejected encoding alternative.
- **Composition-claim routing:** when the unit claims read order, precedence, reachability, short-circuiting, prefix termination, or interaction between runtime classes. Then name the engine layer that established it using the routing rule in [`SOURCES.md`](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit). Source reading of one runtime class leaves such a claim a hypothesis until a code-generation template, backing bean, generated program, or probe confirms it. This check is mandatory whenever such a claim is made.
- **Harness and executable cost:** when the unit touches a gate, driver, executable, fixture-loading path, or exhibits repeated or material diagnostic or latency friction.
- **Cross-project directionality:** when an inbound handback or outbound request is involved; verify exact revision provenance, owner overlap, and feedback-loop risk.
- **Documentation responsibility beyond routine status:** when a public contract, source route, stable architecture decision, evidence inventory, or resumption contract changes. Verify the exact owner and remove superseded detail elsewhere rather than appending another account.
- **Evidence and calibration batching:** when the unit joins or changes a Tier 2 calibration family.

At a reusable capability milestone or an explicit risk trigger, run the complete list above—routine core and every conditional item—together with the [trigger-based cold review](#trigger-based-cold-review).

Fix a same-capsule defect before committing. Record a genuinely open semantic obligation only in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md); route a durable formalization lesson to [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), implemented/evidence state to [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), and changed cross-session sequencing to [`PLAN.md`](PLAN.md). These are possible destinations, not a mandatory touch list: leave any owner whose facts did not change untouched. A routine assessment with no concrete finding creates no repository report. Infrastructure, protocol, dependency, shipment, or governance work found by the assessment remains a proposal subject to its existing approval rule.

If the assessment changes code, proofs, executable cases, or a gate-consumed artifact, rerun the affected focused check and every later applicable rung before commit. Documentation-only corrections do not restart unrelated semantic gates.

### Trigger-based cold review

A cold reviewer supplements rather than replaces the same-context assessment. Run a bounded artifact-only review after a reusable family closes, whenever SG1, SG2, or SG4 reaches a reusable capability boundary, after another major addressing/computation boundary changes, when a public protocol or shipment changes, when the change carries a behavioral `spec/` edit or the synchronization ledger entry for one, when it adds a module under `A12Kernel/Semantics/` or alters a type two or more families consume, when it records a Tier 1 line-budget exception, or before making a consumer-adequacy or compatibility claim. A new or materially changed clean-room mechanism or kernel-oracle/evidence route is also a trigger; the fact that ordinary semantic work is clean-room work is not. Do not pay for a cold review after every routine capsule.

For every agent, the [permanent family-batching rule](../CLAUDE.md#semantic-first-simplification-rule) defers these triggers to one review of the frozen family slice, including its local checkpoint commits. Focused red/green checks still run per implementation step; required integrated, retained-evidence and trust/hygiene checks run before family closure. An isolated change outside a declared family batch retains the per-change trigger. A checkpoint commit is not a completed coverage milestone.

Keep a review slice small enough that every acceptance row can be traced from its source distinction through the running implementation to its law or separating lock. Independent syntax, evaluation-effect and result-projection obligations need explicit partitions even when they share one family batch; file count and green gate totals do not substitute for that trace. Finish local red/green work, focused mechanical mutants, finite-denominator enumeration, API-diff inspection, and stale-surface searches before calling the reviewer. Freeze the reviewed slice as an exact baseline plus a stable working diff; when reviewing an already committed handback, name the exact revision or range instead. Give the reviewer the task, governing instructions, exact baseline and range, the implemented diff, a finite acceptance matrix with each claim's oracle and explicit non-goals, a factual list of already-closed findings and their guards, and authoritative verification output. **Capture that output against the reviewed state**: a gate that reads the *working tree* rather than a range — `check-spec-sync.sh` is one — reports "no change" on a committed slice and so proves nothing about it, which a reviewer will correctly report as vacuous. Run such a gate before the commit, or re-run it against a checkout of the range, and hand over that line instead. Do not provide the implementor's rationale or conclusions: the reviewer must recover the account from the artifacts rather than inherit its framing.

Use a fresh context with no conversation history and the same model and reasoning/effort tier as the implementing session. The prompt is review-only, the reviewer stays read-only, and the implementing session remains the sole writer. A reviewer may run read-only checks, but it must remain build-free while an isolated timing-sensitive gate is running. A warm reviewer with prior context may help with compilation fallout, regression inventory, and synchronized API, documentation, or golden surfaces, but it never substitutes for cold review on any adversarial axis below. Batch compatible axes into one information-dense review; use multiple cold reviewers only when distinct mechanisms require genuinely different source estates and the risk justifies rereading the diff.

Ask the cold reviewer to attack vacuity and missing positive controls; acceptance-denominator completeness; fidelity to the owning semantic, elaboration, proof, and public API shapes; source-versus-artifact oracle choice; and whether each observation supports the mechanism claimed for it. For Lean specifically, it must distinguish executable conformance from trusted proof, inspect hypotheses and theorem-root registration, check that Analyze/Transform or other named consumer decisions preserve the required identities and distinctions, challenge evidence classification and kernel-correspondence scope, and inspect the clean-room and spec/ledger directionality boundaries when triggered. Mechanical hygiene remains the implementing session's responsibility, so the reviewer need not hunt for it; it still reports any hygiene defect it happens to notice rather than filtering it out, because [`LF76`](LEAN-FINDINGS.md) was a citation with no referent that reads as mechanical hygiene and survived both a capsule review and an author-run closure assessment.

Request new findings only. Each finding must have the form `discriminator input → observed/expected output → exact source locus → oracle → execution status`. The implementing session reproduces every actionable finding and decides it against the correct oracle before editing anything. The reviewer reports every finding it holds, including ones it judges low-severity, out of scope, or merely mechanical, and does not filter for importance or confidence; scope decides the denominator, not whether a finding is reported. A finding enters the reviewed slice when its discriminator violates that slice's named invariant; an adjacent improvement or independently exposed defect is recorded in its owning gap or next task without enlarging the current acceptance denominator. The original in-context agent reconciles every accepted finding against the actual source evidence and documentation owners before changing the representation or opening a gap.

### Review convergence and landing gate

A review finding is evidence against a mechanism, not a patch prescription. Before disposition, name the violated invariant, its owner and the affected rows of the existing acceptance matrix. For behavioral defects, reproduce the reported discriminator and a second predicted instance, then fix their common cause and rerun those rows, including opposite-direction and positive controls. For proof or record findings, check the actual statement, call site or owning record against its oracle; do not invent executable work for a prose correction. Use the already-required focused mutant check where a missing refusal or skipped path could otherwise survive; do not add a mutation framework or another reviewer. Reconcile implementation claims and exclusions in their existing owners in the same change. These are applications of the mandatory closure core, not additional verification passes.

A review verdict covers its frozen revision only. Disposition edits invalidate the affected acceptance rows; an earlier clean review does not certify the correction. Recheck those rows in the implementing context and apply the existing convergence rule below, without automatically starting another cold round. Preserve demonstrated defects separately from concerns awaiting an oracle.

Stop patching a slice when two consecutive implementation/review rounds add net-new blockers to it, or when any round changes its acceptance denominator. Freeze the observations already established, name the coupled mechanisms, partition them into the smallest independently meaningful feature commits, and give each partition its own finite acceptance matrix, oracle, and explicit non-goals. Finish one partition before reopening another.

A cold-reviewed slice may land only when its reviewed range remains stable, its finite matrix is green, every actionable cold finding has been reproduced, every accepted in-slice finding is closed, every confirmed out-of-scope finding is routed to its owner, and the original in-context agent has completed the applicable final trust and hygiene gates. Once those conditions hold, do not redesign an already-satisfied mechanism merely to improve it; commit the bounded slice and start any independent improvement from that stable baseline.

## The six harness layers

- **Focused executable locks:** [`Conformance/`](../A12Kernel/Conformance/) checks concrete Lean results and rejections. It does not prove universal correctness or kernel agreement.
- **Trusted proofs and checked non-laws:** [`Proofs/`](../A12Kernel/Proofs/) proves named laws for modeled inputs and retains counterexamples to stronger claims. It does not validate the chosen primitive against the kernel.
- **Retained evidence:** [`evidence/`](../evidence/) and [`A12Kernel/Evidence/`](../A12Kernel/Evidence/) bind Lean projections to 51 private observations; public association checks bind 25 suite cases. Finite projections are not exhaustive correspondence.
- **Reference-process black box:** [`ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) checks JSON, exits, channels, determinism, strict input, fixtures, manifest, and V2 controls. It adds no semantic evidence.
- **Independent candidate conformance:** [`CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) checks selected finite JSON suites within per-invocation bounds. Passing does not inherit Lean proofs, establish release readiness, or cover omitted behavior.
- **Structural and hygiene gates:** [`check-lean-trust.sh`](../scripts/check-lean-trust.sh), `git diff --check`, and status checks enforce source zones, trusted closures, theorem registration, escape-hatch checks, patch hygiene, and sibling immutability. They establish no semantic fact by themselves.

`lake build` runs the first two layers because the library root imports both the conformance root and the trusted proof root, and it builds the reference executable because that executable is a default target. `lake test` separately replays the compact non-public evidence cases. `lake exe checkReferenceProcess` runs the compiled CLI through an independent process driver, verifies the current manifest, binds the 25 public suite cases to their exact compact evidence associations, invokes structural integrity self-tests for the current V2 suites, and runs those suites against the compiled Lean reference as controls. `lake exe checkCandidateConformance --candidate … --suite …` runs only the selected language-neutral suite against an independent process through the shared bounded relay; it does not query that process for a manifest. `lake exe checkBoundedProcess` exercises the bounded relay lifecycle and adversarial resource cases. The trust script enumerates every project Lean source, rejects an unclassified path, derives each positive source-zone closure from fail-closed canonical Lean import headers, refreshes the library root before inspecting its elaborated logical environment, and compares the theorem inventory with the human-readable axiom registry in one batch. Successful elaboration alone does not classify unused project axioms, opaque/partial stubs, compiler substitutions, foreign entry points, omitted theorem-root imports, or accidental process dependencies. The gate executes the adversarial declarations in one Lean session, captures the axiom registry internally, prints one compact inventory on success, and exposes the complete captured diagnostics when any audit fails.

## Red/green semantic development

Every new semantic capsule uses red/green TDD.

1. For a high-connectivity family, complete the [bounded pre-audit](#high-connectivity-keystone-pre-audit). Then state the exact supported fragment, its observable result domain, its evidence source, the useful law, the nearest false generalization, and the [consumer hypothesis](#pre-implementation-consumer-hypothesis) before adding a general abstraction.
2. Add concrete separating examples under `A12Kernel/Conformance/` against the intended public API.
3. Run the focused module and confirm a meaningful red result: the module, definition, constructor, or behavior is absent or wrong for the expected semantic reason.
4. Implement the smallest total pure definition that makes those examples green.
5. Add an independent declarative relation or judgment only when it exposes a useful boundary, then prove its connection to the executable definition in `A12Kernel/Proofs/`.
6. Replay any already available matching observation. Otherwise mark the capsule `external evidence pending` and add it to the smallest coherent Tier 2 calibration family; do not build packet machinery in the semantic change.
7. Apply the exclusive ownership triggers in [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md): update only owners whose facts changed, remove displaced detailed copies, and leave every untriggered document untouched. Then run the applicable tier gate below.

A red run is part of the evidence for the workflow, not a file committed to the repository. A test that was green before the semantic implementation is either not testing the requested behavior or is accidentally passing through an older path.

For a public process or protocol change, write the independent process expectation before adding the decoder or IO route, run `lake exe checkReferenceProcess`, and confirm that it fails for the missing or wrong public behavior. Make the existing checked semantic route satisfy the test; never make a protocol fixture green by introducing a second evaluator.

## Executable Lean examples

A conformance lock is an `example` whose proof evaluates a decidable proposition. For example:

```lean
example : (filteredCounts 1).sumSelected source = .value 7 := by
  native_decide
```

The left side executes the pure Lean function on the concrete fixture. Equality for the result type is decidable, so `native_decide` compiles and evaluates the decision procedure; if it produces `false`, elaboration fails and therefore `lake build` fails. Its successful proof is admitted through Lean's native-decision axiom rather than reconstructed by kernel reduction, so the native compiler and runtime join the trust base for that example. Use `decide` for small structural propositions whose proof reduces economically in the kernel, and reserve `native_decide` for concrete executable fixtures in explicitly nontrusted test lanes where compiled evaluation materially reduces cost.

Lean tests do not require a JUnit-style runtime runner. The conformance modules are ordinary Lean modules imported by the conformance root: a false `example`, an ill-typed fixture, or an unprovable expected equality prevents elaboration and fails the build. `#eval` remains useful while exploring a new definition and for deliberate smoke output, but printed output alone is not an assertion; once behavior matters, move it behind an `example`, theorem, or retained-evidence comparison that can fail automatically.

`native_decide` is permitted only in conformance examples and other explicitly nonlogical executable test surfaces. It is forbidden from the logical semantics/proof closure by [`../scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh), because an axiom-backed native result is suitable as a regression lock but not as evidence that the theorem root depends only on the audited logical axioms. Adding a new source directory is itself a red trust test until that directory receives an explicit zone; a name omitted from an old blacklist is never admitted by default.

Concrete cases should be separating, not merely numerous. Name the realistic wrong account—wrong order, empty substitution, polarity, unknown collapse, scope or row, or poison timing—hold unrelated inputs fixed, vary one semantic axis, and retain one case per independent branch. For repeated-operand admission, test truth and the full verdict/polarity independently: truth idempotence does not establish that VALUE versus OMISSION survives occurrence-preserving lowering. Exact matrices belong in their family conformance modules rather than this generic method; [`Correlation.lean`](../A12Kernel/Conformance/Correlation.lean), [`CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean), [`NumericTarget.lean`](../A12Kernel/Conformance/NumericTarget.lean), the String computation modules, and [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md) are worked examples.

**"Vary one axis" assumes you can. Before writing that a conjunctive claim's conjuncts are separated, attempt each variation and record which layer refused.** An axis you chose to hold is one you can name; an axis the surface forbids never presents itself as an axis at all, so it reads exactly like one nobody thought to vary. The two are not distinguishable from inside the resulting table, and a row failing several conjuncts at once feels like evidence for each and is evidence for none — count rows against conjuncts before writing the count. **This project is more exposed to that than the peer is, and the reason is structural rather than incidental:** the licensing boundary means the Kernel can never be linked or called here, so every observation is mediated by an instrument this project does not own, and a forced axis therefore has two possible owners — a Kernel gate or the instrument's authoring surface. Assuming the second is the default error, and it is wrong in the direction that matters, because a consumer bypassing the instrument still meets a Kernel gate. Attack the variation through the sanctioned hand-edit-a-copy route and let the refusing layer name itself; that turns an assumed constraint into a measured one, and the refusal class is itself the finding. The same boundary supplies the sharper form of the peer's own standing rule that a client-side refusal needs a measured Kernel basis: because a clause here is a total function rather than a narrowing, **a clause stricter than the measured Kernel is as defective as one more permissive**, and inventing a comparison the Kernel does not perform is the specific way that happens. [`LF161`](LEAN-FINDINGS.md) records the instance that produced this rule, and the fact that two prior findings stating the general form did not prevent it.

For checked lowering, distinguish static rejection from runtime routing. Reject unresolved, ambiguous, wrong-kind, wrong-scope, and invalid-topology inputs before lowering; prove only that successful checked wrappers carry their structural certificates; keep exact rejection matrices in the owning family module. Do not describe those certificates as surface-to-core semantic preservation.

Run a focused executable file after its imports have been built:

```sh
lake build A12Kernel.Semantics.Iteration
lake env lean A12Kernel/Conformance/Iteration.lean
lake build A12Kernel.Semantics.Correlation
lake env lean A12Kernel/Conformance/Correlation.lean
lake build A12Kernel.Elaboration.Correlation
lake env lean A12Kernel/Conformance/CorrelationElaboration.lean
```

Run `lake build` before handoff so the same examples also pass through the actual library import graph.

### Exploratory Lean probes

**Throwaway probes are piped, never written.** To check a constructor name, an operand's static legality, or one evaluation before committing to an expected value in a conformance case, stream the snippet in instead of creating a scratch file:

```sh
printf 'import A12Kernel.Semantics.NumericAggregate\nopen A12Kernel\n#eval repr (someQuery args)\n' \
  | lake env lean /dev/stdin
```

Run it from the repository root so Lake resolves the package; a path outside the package loses the build search path. This leaves nothing to clean up, so it never creates an untracked project file and never needs a deletion. Use it before writing expected values rather than inferring a fixture's legality from a failing case: probe first, then write the case. `#eval` needs a `Repr` instance and aborts on a term that depends on `sorry`, so project a decidable view when the type has none.

**When the probe's purpose is to produce a conformance case's expected values, put the `#eval` in that conformance module beside the fixture it will lock, then replace it with the `example`.** A piped probe is a *second* fixture, and a second fixture can differ from the one the case will use in a way neither file shows: a scratch projection that collapsed a row-level skip onto `notFired` produced expected values that the real module then rejected, costing a build round to attribute. Writing the probe where the case will live makes them the same definitions by construction. The piped form above stays right for the question it answers — a constructor name, an operand's legality, one evaluation — none of which is about a fixture you are also building.

## Reference-process harness and sample data

When a public process, candidate suite, shipment or release check is triggered, read [Reference-process harness and sample data](TESTING-PROCESS.md#reference-process-harness-and-sample-data).

### Independent candidate suites

When a public process, candidate suite, shipment or release check is triggered, read [Independent candidate suites](TESTING-PROCESS.md#independent-candidate-suites).

### Historical Rust qualification experiment

When a public process, candidate suite, shipment or release check is triggered, read [Historical Rust qualification experiment](TESTING-PROCESS.md#historical-rust-qualification-experiment).

## Universal proofs and counterexamples

Proof modules quantify over arbitrary inputs and use induction, case analysis, rewriting, or previously proved laws to construct proof terms. Lean's kernel checks those terms. The theorem statement—especially its hypotheses, direction, and result domain—is the claim; theorem counts and proof-line counts are not quality measures.

For effectful proof failures, first preserve the exact elaborated goal and classify every visible `Except` or enum layer. Trial definitional `rfl`, a named domain equation plus `rw`, a reviewed local `simp only` set, and explicit cases without changing the claim. Use `rfl` only for intentionally transparent constructor equations; prefer `simp only` after exposing one effect layer; retain explicit cases when they communicate the residual error domain. A helper belongs in a proof-only owner only when it states a reusable domain boundary, not merely because a tactic needs a different shape. Validate an adopted pattern on a second theorem family before documenting it as reusable. Do not add a global `[simp]` rule unless its normal form is canonical and terminating on nested representatives, preserves every success/error branch, needs no reverse rewrite, and leaves unrelated proofs unchanged.

When an executable enumerator has meaningful independent content, follow the audited Cedar pattern: define an ordered declarative relation separately, prove execution-to-relation soundness and relation-to-execution completeness, and package them as an exact bridge. Preserve ordered-list equality when order or multiplicity can become observable; a membership equivalence is too weak for an ordered A12 document.

Read-footprint theorems should be stated at the semantic observation boundary. The correlated `evalGuardedAnyFilledOn_filter_before_consumer` theorem assumes equal selection, equal validation observation of the outer guard, and equal validation observations of consumer cells in selected rows; it deliberately does not require equality of raw checked cells or any dropped consumer. This makes the proved noninterference exactly as strong as the evaluator's read surface and no stronger.

The checked-elaboration theorems in [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean) establish structural obligations: checked wrappers expose stored model/core certificates, admitted references have a unique matching declaration, the raw-to-checked route uses that declaration's policy, other IDs fail closed, and one-group well-formedness implies the operator-specific scale law. These are not source-to-core semantic-preservation theorems. Such a claim would require an independent dynamic semantics for the surface language, which this capsule deliberately does not yet define.

Each useful law should be paired with the nearest plausible false generalization as a concrete checked non-law. For example, a same-group star reopens the group and spans all candidate rows; the proposition that it collapses to the current row must have an explicit counterexample before `$` correlation is introduced.

Every manually authored exported theorem under `A12Kernel/Proofs/` must be imported by [`../A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean) and remain in the human-readable `#print axioms` registry in [`../A12Kernel/TrustAudit.lean`](../A12Kernel/TrustAudit.lean); duplicate basenames are rejected before that presentation check. Keep exported theorem-root identifiers free of `?` because the registry inventory tokenizes that character as a name boundary, even when the underlying definition conventionally ends in `?`. The authoritative gate does not depend on those source spellings. [`../A12Kernel/Trust/Environment.lean`](../A12Kernel/Trust/Environment.lean) inspects every elaborated constant owned by the imported trusted project modules and rejects project axioms whether used or unused, `unsafe`, unclassified opaque declarations, source-partial wrappers, nonstandard axiom dependencies, `implemented_by` substitutions, and `extern` entry points. Lean's generated `_unsafe_rec` helper is admitted only when its parent is a kernel-visible safe total definition with the same type. Conformance is intentionally outside this environment root because its executable examples may use `native_decide`.

**A backticked identifier must resolve to a declaration.** The same gate rejects any `` `name` `` in project Lean source that looks like a declaration citation — an identifier containing an underscore and not written in ALL-CAPS — when no `theorem`, `lemma`, `def`, `abbrev`, `inductive`, `structure`, `instance`, or `class` of that name exists anywhere in the project. Kernel diagnostic codes are ALL-CAPS and namespaced Lean core lemmas carry a dot, so both fall outside the pattern; Lean-provided bare names that are legitimately cited live in a small explicit allowlist in the script, currently just `native_decide`. The rule exists because a docstring naming a theorem that was never written is a claim with no referent, and it reads as settled to the next agent — one such citation survived an entire capsule review and an author-run closure assessment before an external reviewer found it ([`LF76`](LEAN-FINDINGS.md)). Update the allowlist rather than weakening the pattern, and delete or implement the citation rather than allowlisting a project name.

The shell gate retains source scanning as defense in depth, but environment inspection is the authority because modifiers, multiline or late attributes, and command macros can make spelling-based checks incomplete. The batched [`Trust/Adversarial.lean`](../A12Kernel/Trust/Adversarial.lean) guard elaborates attributed and macro-generated axioms, unsafe and partial definitions, late compiler/foreign attributes, `sorry`, `native_decide`, and a bodyless opaque; an accepted control contains the same words in an ordinary String and uses an ordinary attribute plus the reviewed logical axioms. The script separately computes the transitive project-source closure of the library, proof, and conformance roots and rejects current evidence, reference, process, trust, and IO-driver sources from the logical closure. Exact representative-path self-tests require known logical and process paths to retain their assigned zones and require an unknown future path to remain unclassified.

## Kernel evidence and differential replay

Kernel differential testing is the empirical backbone, but the kernel never becomes a dependency of this repository. Existing focused scenarios run externally through maintained a12-dmkits corpus or differential facilities in the local `../a12-rulekit/` checkout; a new scenario uses that route only when it exposes the required own-domain observation, otherwise it needs an accepted purpose-specific handback. The Groovy-dynamic kernel result is the observation anchor, the static-Java kernel strategy detects a strategy split, and the a12-dmkits interpreter is a clean-room triangulation peer that may reveal a disagreement but is never the oracle.

### Read the kernel source first, then measure only the residual

When preparing or interpreting a kernel measurement, read [Read the kernel source first, then measure only the residual](TESTING-KERNEL-PROBES.md#read-the-kernel-source-first-then-measure-only-the-residual).

### The kernel-runtime probe route

When preparing or interpreting a kernel measurement, read [The kernel-runtime probe route](TESTING-KERNEL-PROBES.md#the-kernel-runtime-probe-route).

### The population replay

<a id="population-replay-cadence"></a>
**Standing replay cadence — owner direction, 2026-10-05.** During implementation, use focused family checks. Before each family commit, run the applicable integrated build, compact evidence, trust and hygiene gate. Full population replay is separate from the routine Tier 1 gate:

- Run it once on the stable, reviewed family slice when the batch changes shared evaluation, scheduling, scope resolution or parsing. Apply review corrections before this run.
- Otherwise run it after three completed semantic family batches since the last full replay. Intermediate checkpoint commits do not count as separate batches; a triggered full replay resets the interval.
- Repeat immediately only when a failure or subsequent semantic fix invalidates the preceding replay result. Rerun only affected checks; prose edits and report requests do not invalidate replay.
- A coverage-report refresh alone must never trigger full replay. The current [report script](../scripts/report-conformance-coverage.sh) couples regeneration to replay, so run it only when replay is due and retain its dated snapshot between runs. Update changed cell classifications in [the construct inventory](CONFORMANCE-CONSTRUCTS.tsv) immediately; describe current totals from that inventory without presenting the older report as current.

Keep the interval in working context and carry it in [the handoff](PLAN.md) when needed. This cadence changes neither focused evidence obligations nor honest `external evidence pending` classifications, and requires no additional tracking machinery.

`lake exe a12-kernel-replay <request.json>…` reads each retained `kernelProbe` request with its DM-JSON model and documents. It parses every rule condition and computation operation, lowers each onto the existing checked carriers and runs it. Each rule and computation is compared, row by row, with the request's retained artifact (`artifact<suffix>.json` beside `req<suffix>.json` or `request<suffix>.json`). A rule is compared by the messages it fires and a computation by the Kernel's change projection for its target. An admitted computation sharing a refused computation's resolved target is unattributed, like a dependent of a refused computation: its alternative table is incomplete, whether its partial result agrees or differs. Each instance lands in one of the six tiers the [replay executable](../A12Kernel/ReplayMain.lean)'s module doc defines: `match`, `tier1`, `unattributed`, `tier2`, `fault` or `absent`. The [coverage report](../scripts/report-conformance-coverage.sh) runs it over every retained request and owns the clustered result in [Axis R](CONFORMANCE-COVERAGE.md#axis-r--population-replay).

The reader stands where the Kernel's document conversion stands, so it owns that conversion's choices: a Number text the conversion parses is decimal-valued (spec §4, storage regimes), a Boolean token is read regardless of case, and a JSON `null` is a field present without a value. Its locks are [`ReaderLocks.lean`](../A12Kernel/Reference/Dm/ReaderLocks.lean) and [`ParserLocks.lean`](../A12Kernel/Reference/Dm/ParserLocks.lean).

**A tier-1 line has three possible owners, and only a measurement tells them apart: a Lean defect, a replay defect, or a stale artifact.** The first replay found all three. Each is settled by re-running the request on the pinned measurement checkout before any record changes, and the Lean fix is red/green against a conformance case in the owning family module, never against the replay alone.

### Five measured throughput rules — apply all five to every sweep

When preparing or interpreting a kernel measurement, read [Five measured throughput rules — apply all five to every sweep](TESTING-KERNEL-PROBES.md#five-measured-throughput-rules--apply-all-five-to-every-sweep).

### Read the grammar or the checker first, then measure only the residual

When preparing or interpreting a kernel measurement, read [Read the grammar or the checker first, then measure only the residual](TESTING-KERNEL-PROBES.md#read-the-grammar-or-the-checker-first-then-measure-only-the-residual).

### Three batch preconditions, each paid for by a wasted round trip

When preparing or interpreting a kernel measurement, read [Three batch preconditions, each paid for by a wasted round trip](TESTING-KERNEL-PROBES.md#three-batch-preconditions-each-paid-for-by-a-wasted-round-trip).

### Measure a gap's premise before weighing its options

When preparing or interpreting a kernel measurement, read [Measure a gap's premise before weighing its options](TESTING-KERNEL-PROBES.md#measure-a-gaps-premise-before-weighing-its-options).

### Two static routes, not one: `rule check` and `computation add --dry-run`

When preparing or interpreting a kernel measurement, read [Two static routes, not one: rule check and computation add --dry-run](TESTING-KERNEL-PROBES.md#two-static-routes-not-one-rule-check-and-computation-add---dry-run).

### Structured `dmtool` probes and feedback

When preparing or interpreting a kernel measurement, read [Structured dmtool probes and feedback](TESTING-KERNEL-PROBES.md#structured-dmtool-probes-and-feedback).

### Peer-session coordination

When coordinating an authorized peer handoff or reconciling a returned result, read [Peer-session coordination](TESTING-PEER-COORDINATION.md#peer-session-coordination).

## Tier gates

**Iterate on the narrowest target and run the full gate once, before the commit.** `lake build A12Kernel.<Module>` while a capsule is still red is seconds; the whole Tier 1 sequence is minutes, and running it after every intermediate edit buys nothing a module build has not already told you. The full sequence is a landing gate, not a feedback loop. The one case that genuinely needs the umbrella build earlier is a change to a shared type or a diagnostic registry, where the fallout is precisely what you are trying to see.

Run this Tier 1 gate for an internal semantic capsule:

```sh
lake build
lake test
./scripts/check-lean-trust.sh
git diff --check
./scripts/check-spec-sync.sh
git status --short
```

Immediately before every explicit push, run the existing publication updater:

```sh
./scripts/prepare-github-publish.sh --update
```

Review and commit any resulting README statistics change before pushing. This push gate is mandatory even when every commit in the outgoing batch already passed its proportional Tier gate, because only the outgoing repository tip determines the published theorem, declaration, and module counts. The updater includes the trust audit, so do not rerun `check-lean-trust.sh` solely for this pre-push step. GitHub CI keeps `--check` as a fail-closed backstop rather than the first place stale publication statistics should be discovered.

Run `./scripts/check-spec-sync.sh` even when the change is documentation-only. It is git-only and cheap, so the expensive-rung exemption above never applies to it, and a behavioral `spec/` edit normally lands as a `docs(spec)` commit that skips every Lean rung. It replaces the former scoped status line: instead of printing the two paths for an author to compare, it fails when a `spec/*.md` change carries neither the synchronization ledger nor [`SOURCES.md`](SOURCES.md), and its message states the three classifications. Declare an exempt spelling, formatting, link, or navigation-only change with `A12_SPEC_CHANGE_IS_NONBEHAVIORAL=1`, which records the claim in the run rather than silencing the gate.

When `check-spec-sync.sh` reports a behavioral `spec/` change, classify its synchronization direction before committing. A locally originated delta that still needs a12-dmkits reconciliation must also list the synchronization ledger. An inbound correction already committed and reviewed in a12-dmkits must instead list [`SOURCES.md`](SOURCES.md) with the exact source revision and evidence routes and must not create an outbound ledger entry merely to echo the finding back to its origin. If an inbound result answers an existing pending or handed-off entry, update that same entry. Pure spelling, formatting, link, or navigation-only spec changes are exempt. A ledger-only status receipt may legitimately list only the ledger. A checkpoint's `sync: no clause` is the opposite case and is itself a claim, that no `spec/` sentence states something the checkpoint contradicts; before writing it, grep `spec/` for every diagnostic code its claim rows carry, as [`LF121`](LEAN-FINDINGS.md) requires of any negative claim. On 2026-09-24 a `no clause` row stood beside a `spec/02` sentence naming the very code it had just refuted for that carrier. Add only the focused replay or producer-bundle check owned by a Tier 2 calibration family. `lake test` already replays every retained non-public compact observation, while `checkReferenceProcess` owns the public evidence associations and current shipment process integrity; do not invent another family-independent gate.

Run the complete Tier 3 gate only when the change affects a public process, independent-consumer shipment, qualification mechanism, packaging, or release—or before an actual release:

```sh
lake build
lake test
lake exe checkReferenceProcess
lake exe checkBoundedProcess
lake exe checkCandidateConformance --self-test --suite reference/single-group-correlation-v2.conformance.json
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v2.conformance.json
./scripts/check-lean-trust.sh
git diff --check
./scripts/check-spec-sync.sh
git status --short
git -C ../a12-kernel status --short
git -C ../a12-rulekit status --short
```

Do not run a Tier 3 gate merely because it was needed by a historical experiment. Interpret failures by layer. A conformance failure means a concrete Lean behavior changed. A proof failure means the definition no longer supports the stated universal law or the proof needs legitimate repair. An evidence mismatch means the Lean projection and retained kernel observation disagree and must be investigated at the semantic definition or projection boundary; never relax the expected result merely to make it green. A reference-process failure means the public transport, executable wiring, fixture, current manifest, or current-suite control changed and must be reconciled with [`PROTOCOL.md`](PROTOCOL.md). A candidate-suite failure means the suite/evidence linkage, resource boundary, or candidate observable changed and must be classified using [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md); agreement with the reference is not allowed to overwrite external evidence. A bounded-process failure means the relay lifecycle, byte/deadline limit, status separation, or process-group cleanup invariant changed. A trust failure means the theorem closure or audit is incomplete even if ordinary compilation passed. Sibling status must be unchanged from the recorded pre-run baseline and should be clean; if a sibling was already visibly dirty, report that pre-existing state rather than touching or concealing it.

## Capsule test checklist

- The red run failed for the intended missing or incorrect behavior.
- Concrete cases separate ordinary, boundary, empty, malformed, selection, and ordering behavior as applicable.
- Unsupported syntax or semantic axes fail closed or are unrepresentable.
- The useful theorem states the smallest defensible law with exact hypotheses.
- The nearest stronger false claim has a checked counterexample.
- Every exported theorem is in the trusted root and axiom audit.
- Focused portable kernel observations exist, or the implementation map says `external evidence pending`.
- The replay derives expectations from retained external output rather than duplicating them in Lean-shaped data.
- Current 0.3.0/V2 shipment controls remain green. Historical 0.2.0/Rust identities and hashes remain immutable in the archive rather than current `checkReferenceProcess`; a successor campaign receives a new identity and uses only a newly justified, adopted Tier 3 qualification path.
- The applicable tier gate passes. A Tier 1 semantic capsule does not inherit unrelated historical shipment and qualification gates.
