# CLAUDE.md

Operating contract for **a12-kernel-lean**, a clean-room Lean 4 formal theory and executable specification of A12 Kernel validation and computation semantics. [`AGENTS.md`](AGENTS.md) is a symlink to this file; keep it tool-neutral. Read linked procedures when their stated trigger applies; links do not load their contents automatically.

## What this is

A12 Kernel evaluates bilingual EN/DE rules and derived fields against form Documents. Validation rules state the error condition: true means invalid. This project models observed behavior, with executable clauses, a required proof spine, selected higher-level laws, and purpose-specific semantic shipments. The target is kernel **31.3.1 (A12 2026.06-ext2)**; version transitions and frozen accounts belong to [the migration plan](docs/PLAN.md#kernel-313-migration).

Use these task routes; [`docs/README.md`](docs/README.md) is the full documentation registry.

| Before this task | Read |
|---|---|
| Resume work or choose the next unit | [`docs/PLAN.md`](docs/PLAN.md), then its selected gap in [`docs/SEMANTICS-GAPS.md`](docs/SEMANTICS-GAPS.md); preserve its sequence and stop conditions |
| Extend semantics | The clause in [`spec/SEMANTICS-MAP.md`](spec/SEMANTICS-MAP.md), its provenance in [`docs/SOURCES.md`](docs/SOURCES.md), existing coverage in [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md), and [family working method](docs/TESTING.md#family-batch-working-method) |
| Change semantic or proof architecture | [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md), and [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) |
| Implement a capsule | [Consumer hypothesis](docs/TESTING.md#pre-implementation-consumer-hypothesis), [applicable test procedures](docs/TESTING.md#read-only-the-sections-your-task-triggers), and [Tier 1 scope](docs/SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#tier-1--semantic-development) |
| Edit documentation | [`docs/DOC-DISCIPLINE.md`](docs/DOC-DISCIPLINE.md) and [canonical ownership](docs/README.md#canonical-ownership-registry) |
| Explore a consumer | [`docs/USE-CASES.md`](docs/USE-CASES.md), then [`docs/IMPLEMENTER-GUIDE.md`](docs/IMPLEMENTER-GUIDE.md); read [`docs/PROTOCOL.md`](docs/PROTOCOL.md) only if the task consumes the normalized process |

## Goal & role

The goal is eventual complete semantic conformance across the target kernel's observable validation/computation language and required static legality. Supported fragments are intermediate checkpoints, never a permanent ceiling. Lean is the versioned formal semantics-of-record, not a replacement for the shipped Kotlin interpreter. Kernel observations establish empirical correspondence; proofs establish internal consequences and preservation bridges, never universal kernel equivalence or automatic correctness of an independent consumer.

Keep five completion levels distinct: executable/tested; useful laws and non-laws proved; kernel correspondence retained; public protocol exposed; consumer-probe qualified. Ordinary capsules normally stop after the first two until a coherent milestone warrants calibration or shipment work. A source-grounded clause may remain `external evidence pending`; dependent correspondence claims inherit that limit. An unresolved alternative affecting the representation blocks dependent work.

## Permanent conformance-convergence rule

Infer mechanisms and close semantic families, rather than accumulating green examples. Follow the single-track sequence in [`docs/PLAN.md`](docs/PLAN.md); its adopted checklist and consumer transition supersede completed historical queues. Do not append an automatic conformance-tail programme.

Before each batch, reconcile current code, tests, evidence and construct coverage; inventory representations and state a causal model and finite acceptance matrix. Select by remaining construct/arm coverage, shared-mechanism reuse and total cost, not replay frequency alone. Use existing evidence first; measure only unresolved distinctions, including a second composition that could falsify the account. Keep one selected family and one writer active until closure or a concrete dependency, falsifying evidence or owner direction requires a change. Explain reprioritization.

Apply the [family-batch procedure](docs/TESTING.md#family-batch-working-method). Freeze the acceptance denominator, implement the common mechanism and all ready members, and require reader-to-evaluator coverage where available. Known in-scope omissions remain obligations. Report verified construct/family closures separately from prerequisites and replay gains; do not claim a measured conformance percentage or universal equivalence. If work repeatedly yields prerequisites without closure, stop that sequence and revise its decomposition.

## HIGH/MEDIUM/LOW task allocation

Standing owner authorization permits **sequential** bounded delegation when it is likely to save total effort. The main agent is always HIGH and owns decisions, contracts, semantic judgment and final acceptance. MEDIUM implements a settled contract; LOW performs exact mechanical work supported by raw output, never authors claims or commits. When judgment is required or classification is unclear, use HIGH.

Resolve tiers through the active CLI's global [model mappings](https://github.com/mbackschat/coding-setup/blob/main/CLAUDE.md#model-tier-mappings); keep selectors and effort values there. Report a coordinator mismatch or unsupported configuration rather than substituting silently. If no mapping exists, use the most capable model for HIGH, a faster cheaper model for MEDIUM and the cheapest for LOW, and state the choices.

**Before delegating, read [the delegation procedure](docs/TESTING.md#sequential-delegation).** Supply bounded ownership, settled mechanism, acceptance cases, controls, narrow targets and stop conditions. HIGH waits while the delegate works; no overlapping implementation, review or builds. MEDIUM and LOW may not delegate further. HIGH reviews actual diffs and raw check output before acceptance or commits. A warm implementer cannot replace a required cold reviewer. This authorization grants no parallel tracks and waives no approval boundary; do not delegate a check cheaper to perform directly.

## Semantic-first simplification rule

- Reuse existing ASTs, evaluators, result types, proofs and conformance cases. Generalize only after two completed semantic users share meaning, result domain and law; specialize generic laws rather than duplicating them. Remove a case only when another retained case demonstrably guards its branch. Consolidate locally, never through an unsolicited repository-wide cleanup.
- Design each representation for a concrete [consumer task](docs/USE-CASES.md), preserving the distinctions and decision or preservation relation it needs. Fix an inadequate semantic root rather than compensating in an adapter. Use the [consumer hypothesis and closure assessment](docs/TESTING.md#pre-implementation-consumer-hypothesis).
- Keep each semantic family independently buildable. Umbrella roots assemble imports only. Target at most **800 nonblank Lean lines** per file; review before exceeding that or acquiring a third independent responsibility. **1,200 is a hard ceiling** for ordinary source. A reviewed 801–1,200-line file may remain only for one cohesive responsibility when splitting would expose private internals without a useful build target; extract before adding another family. The registry-only `TrustAudit.lean` exception is governed by [source hygiene](docs/TESTING.md#lean-source-hygiene-gate). Split by ownership, retain family-local fixtures, and share helpers only after two completed users need the same invariant; create no universal fixture module, include-file chain or replacement harness.
- Prefer existing owners and small capsules. The [Tier 1 touch budget](docs/SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#tier-1--semantic-development) governs the semantic/proof/conformance trio, 250-line decomposition target and zero new process machinery. Explain an indivisible exception in the commit body, never a coverage row; it does not waive module, estate, approval or review limits.
- Keep documentation ownership exclusive: implemented/evidence state in [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md), open obligations in [`docs/SEMANTICS-GAPS.md`](docs/SEMANTICS-GAPS.md) and its shards, cross-session sequencing in [`docs/PLAN.md`](docs/PLAN.md). Leave untriggered owners untouched, delete completed gaps, and keep uninterrupted gate progress in working context. Follow [documentation discipline](docs/DOC-DISCIPLINE.md), including bounded operational records.
- Batch external evidence by family and follow [population-replay cadence](docs/TESTING.md#population-replay-cadence); a report refresh does not justify replay. Use bounded consumer probes at meaningful capability/addressing/computation milestones or before public compatibility claims, not after every capsule. Probe design, artifact-only readback and risk-spike exit rules are in [project design](docs/PROJECT-DESIGN.md#controlled-interleaving-and-coverage-horizons). Probes authorize no external prototype, product, dependency, runner, protocol or qualification campaign.
- At least **three substantial semantic units** must land between infrastructure or product-boundary units; this ratio grants no approval. Support must not exceed theory in tracked nonblank Lean lines, and evidence must remain below one third of theory unless the owner approves an exception. **Before adding support, read [estate definitions, live-value tests and stop conditions](docs/SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#support-estate-and-live-value-limits).** Stop at a threshold crossing and redesign or obtain approval; do not delete or migrate retired tooling without approval.

Before final trust/hygiene checks and commit, perform the [same-context assessment](docs/TESTING.md#same-context-capsule-closure-assessment). Run [cold review](docs/TESTING.md#trigger-based-cold-review) only at its named triggers, over the frozen family slice including checkpoints, with a fresh read-only context at the implementing session's tier and no implementor rationale. Ordinary clean-room work alone is not a trigger. Apply [review convergence and landing](docs/TESTING.md#review-convergence-and-landing-gate): stop and repartition after two consecutive rounds add net-new blockers or any round changes the denominator. Fix same-unit defects and rerun only invalidated gates. A clean assessment creates no report or extra verifier.

## ⚠️ HARD RULE — clean-room reimplementation; never link, call, or transcribe the kernel

Never link, call or ship the kernel or a JS-kernel binding from this project; never transcribe a kernel source expression into Lean. Read kernel and peer source to learn behavior, then write original Lean and focused cases/laws. **Copy the mechanism, never the expression.** This project's [MIT license](LICENSE) and the kernel's EUPL-1.2/commercial boundary require this separation; see the peer's [licensing rationale](../a12-rulekit/docs/LICENSING.md).

Message catalogs are protected expression: retain keys, codes and parameters, never rendered catalog sentences in Lean, spec, docs, evidence or archived receipts. Describe classes in original words. Run [`scripts/check-no-kernel-prose.sh`](scripts/check-no-kernel-prose.sh) before committing changes to spec, docs or Lean prose. Kernel binaries, linked objects, implementation code and volatile logs never cross into this repository.

## ⚠️ HARD RULE — no machine-specific data in committed files

No absolute home paths, usernames, hostnames, emails or credentials in source, docs or commit messages. Use relative sibling paths such as `../a12-kernel/` and `../a12-rulekit/`.

## ⚠️ HARD RULE — dependency changes require user approval

Obtain explicit approval before adding, removing, upgrading, vendoring or replacing any dependency, build tool or runtime library, or changing linkage or bundled-component distribution. An implicit toolchain dependency is not authorization: explain its purpose, licensing/deployment consequences, concrete options and your recommendation first. Read-only graph inspection and measurements are allowed.

## ⚠️ HARD RULE — semantics first; harness, governance, and redundant work require explicit approval

Default work is semantics and the minimum documentation needed to state its boundary honestly. “Continue” or “finish” does not authorize new or expanded harnesses, process/evidence frameworks, protocols, schemas, generators, registries, qualification campaigns, migrations, governance, trust mechanisms or infrastructure.

**Standing throughput-tooling exception:** instrument-side tooling is pre-approved only when it removes a measured repeated cost or prevents a demonstrated costly mistake. Name that cost in the commit body and stay within estate ratios. This does not authorize evidence frameworks, protocols, schemas, qualification, governance or semantic/shipment-boundary changes. Anticipated savings are insufficient.

For other infrastructure, explain the reproduced need, why existing mechanisms cannot serve it, semantic/consumer payoff, scope, lifecycle cost, alternatives and your recommendation, then wait for explicit approval. Do not hide it in a capsule.

Before implementing or proposing a capability, inspect its owner, code, tests, Git history, active plans and cross-project handoffs. If it is already satisfied, overlapping, obsolete or assigned elsewhere, surface the exact overlap and block that work until the user decides whether to no-op, consolidate, replace or proceed for a new reason. Reuse settled mechanisms; do not clone or reverify assigned work. Before an outbound semantic request, search the peer's [findings](../a12-rulekit/docs/KERNEL-FINDINGS.md) heading-first and read matching settling values.

Deliver the requested scope. Make routine decisions yourself; ask only when materially different interpretations change the work. Explain a mistaken premise or better alternative without silently widening or narrowing the task.

## ⚠️ HARD RULE — never push without an explicit current request

Commit every completed coherent unit before reporting completion unless the user explicitly says not to. Follow global Conventional Commit and rationale rules. Keep commits local: no push, remote branch/tag update, release or other publication without an explicit request for that remote action in the **current request**.

Immediately before an authorized push, run [`scripts/prepare-github-publish.sh --update`](scripts/prepare-github-publish.sh), review and commit any README statistics update, and check the remote-appropriate Git email under the global rule. The updater includes trust; do not add a redundant trust pass. Do not create or switch worktrees without explicit instructions.

## ⚠️ HARD RULE — discharge a claim before stating it, or flag it and surface it

Every claim in spec, ledger, docstring, finding, user reply or peer message must meet its discharge method or be visibly marked **unverified**. This includes accepting a handback, scheduling work from a premise, or reusing a mechanism on another arm, carrier, phase, depth or topology. Confidence, source proximity, matching outcomes and peer agreement alone do not settle a mechanism.

| Claim | Required discharge |
|---|---|
| Value: input yields output | Red-first executable case in the owning conformance module |
| Mechanism: output occurs because of a particular step | Independent re-derivation or a witness isolating that cause from its neighbours |
| Reachability/scope: what legal models express or a gate constrains | Measurement; reading alone never discharges reachability |
| Provenance: a source/revision established this case | Verify that exact revision measured this case, not an adjacent outcome |

**Before stating, consuming or accepting such claims, read [claim verification](docs/TESTING-KERNEL-PROBES.md#verify-claims-before-measurement-or-publication).** Search local spec, source checkpoints, evidence, findings and peer findings before negative or unmeasured-assumption claims; follow its heading-first and literal-value searches. Never invent a full revision from a short one. Keep total semantic clauses unconditional and authorability separate. Cross-carrier reuse needs covering evidence or an explicit assumption/evidence item in its owner, subject to the blocker rule below. Prefer a pointer to a gated record over fresh peer-message prose; [peer coordination](docs/TESTING-PEER-COORDINATION.md#peer-session-coordination) governs authorized communication.

If discharge is unavailable, explicitly choose:

1. **Drop the claim** when unnecessary; preferred.
2. **Record a gap** with its discriminator when the answer does not change dependent work; continue unrelated work.
3. **Block dependent work and ask the user** when the answer changes representation, proof or dependent work, or when that distinction is unclear. Recommend an account with reasons without adopting it. Persist an `EXP-` entry for an observation blocker or a [`docs/PLAN.md`](docs/PLAN.md) blocker for an owner decision, and set `Blocked on:` on the owning gap.

Do not substitute hedged prose for this decision. Flag unverified claims visibly in user-facing responses.

## Naming convention

Use **a12-dmkits** for the peer project, software, interpreter, corpus or documentation; **dmtool-release** for its public CLI/distribution. **`a12-rulekit/`** is only the local checkout directory name, never the project name.

## ⚠️ HARD RULE — sibling tracked worktrees stay immutable and visibly clean

Every tracked or visible-untracked path outside this repository is read-only. Never edit, create, generate, format, delete, restore, stage or commit sibling tracked files or create visible untracked files. Build/test writes are allowed only in paths the owning sibling already ignores; check `git check-ignore` when uncertain, including caches, reports, locks and temporary outputs.

Check the sibling's visible `git status --short` before and after any command; it must remain unchanged. Commands writing ignored outputs require a clean sibling baseline. A pre-existing dirty sibling permits read-only inspection only: report it and never clean or conceal it. The owner-approved existing untracked analysis/docs in `../a12-kernel/` do not block builds in a different clean sibling; record their exact baseline and never touch them or add more.

Redirect generators away from tracked fixtures into already ignored outputs. Never extend missing sibling functionality in a disposable copy. Keep temporary artifacts in ignored locations and remove project-local temporary files before completion.

## ⚠️ HARD RULE — request a12-dmkits improvements upstream; never patch a copied harness

Never clone, archive or copy a12-dmkits for capture/improvement work, or alter its `RuntimeLaws`, tests, projectors, exporters or other source, even in a disposable copy. Request changes upstream and consume their committed result.

The sole exception is the existing **read-only pinned measurement checkout** identified in [`docs/SOURCES.md`](docs/SOURCES.md): build its launcher and run existing observation commands only. Re-pin deliberately for an upstream instrument fix and record the pin there. Never edit/stage/commit its source, extend it or use it as the source of an upstream request. Sibling clean-baseline rules still apply.

Before requesting a missing capability, inspect live sibling source, record the gap, and read [upstream engagement](docs/SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule), [entry routing](docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#entry-kinds-and-routing), and [probe feedback](docs/TESTING-KERNEL-PROBES.md#structured-dmtool-probes-and-feedback). Instrument defects are not ledger entries; unreachable observations use `EXP-`, local behavioral corrections use `SPEC-`, and capabilities with their own architecture/lifecycle use a temporary proposal.

**The user carries requests.** Do not send them automatically, duplicate assigned work or infer completion. Verify the committed handback and maintained commands/artifacts, reconcile durable facts and delete completed handoffs. Run only unchanged source-owned commands with permitted outputs; otherwise retain `external evidence pending`. Never patch an adapter fork, resurrect capture V1 or infer a current command contract from historical tooling.

## ⚠️ HARD RULE — `spec/` is the project-owned semantic bridge

[`spec/`](spec/) owns the canonical language-neutral behavioral account. Verified corrections, narrowing and extensions update its clause. Keep implementation status, Lean design, evidence inventories, research and plans in [`docs/`](docs/).

Every locally originated behavioral change still requiring peer reconciliation must update the outbound [ledger entry](docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) in the same change, including removal of a distinction, trap, negative guard or confidence limit. On handback, verify the exact upstream revision and update that entry's disposition.

**No feedback loop:** incorporate an exact committed, reviewed inbound correction, record provenance in [`docs/SOURCES.md`](docs/SOURCES.md), and update implementation status as applicable. Do not create another outbound request or seek acknowledgement of that same correction. Update an existing answered entry if present; otherwise leave the ledger unchanged. This overrides a handoff template asking for a new outbound entry.

## The source-of-truth hierarchy

1. **Kernel behavior** in `../a12-kernel/` is the oracle. When the theory disagrees, correct the theory under the clean-room boundary.
2. **Project-owned spec and Lean theory** are the primary working reference.
3. **a12-dmkits** in `../a12-rulekit/` is a peer knowledge source and clean-room implementation, never the behavioral oracle.

### Entry points

[`docs/SOURCES.md`](docs/SOURCES.md) owns sibling inventories, pins and the drill route to ground truth. Before measurements, read its [engine-routing rule](docs/SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) and the [kernel probe procedure](docs/TESTING-KERNEL-PROBES.md#the-kernel-runtime-probe-route); use maintained external sibling commands only. [`docs/EVIDENCE.md`](docs/EVIDENCE.md) owns retained identities and replay scope. Evidence-boundary changes require the [compact pipeline contract](docs/SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md) and approval.

### Codebase orientation

Explain this codebase from its source and documentation. Ignore Showboat and dmtool-release unless explicitly requested.

## Building & running

Before builds/tests, read the [command ladder](docs/TESTING.md#command-ladder) and [applicable tier gates](docs/TESTING.md#tier-gates). Use narrow targets for red/green and one integrated gate on the stable family slice, with only affected reruns after corrections. Public-process/candidate/release checks are not ordinary capsule gates. Never edit compiler inputs while a build is live.

**Before planning or delegating edits to widely imported modules, read [build batching](docs/TESTING.md#batch-widely-imported-edits).** List planned edits and their import blast radius; collect shared-module edits before one full build, `lake test` and trust run. Do not alternate high-blast edits with full rebuilds. An exception requires the next design to depend on the preceding build's result and that reason in the handoff.

The toolchain is pinned in [lean-toolchain](lean-toolchain). Follow [exploratory Lean probes](docs/TESTING.md#exploratory-lean-probes) before throwaway queries or fixture expectations. Read [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md) before release/linkage work and obtain dependency/distribution approval. Save slow-command output once; inspect that log rather than rerunning for another view.

## Layout and dependency spine

Before module ownership/dependency changes, read [architecture layering](docs/ARCHITECTURE.md#layering-and-dependency-direction). Semantic/proof roots must not import evidence, reference, process or IO adapters. Keep these representation invariants:

- Preserve absence, present-empty placement, formal invalidity, arithmetic domain failure and computation poison until an intentional consuming projection.
- Preserve exact decimals and each rounding stage; never algebraically reassociate ordered evaluation.
- Separate instantiated rows from cell storage and captured outer environments from candidate inner environments.
- Separate validation's extensional unknown/polarity account from computation's ordered poison and short-circuit account.
- Preserve the versioned model-zone calendar split: proleptic ISO runtime with full zone history versus hybrid Julian/Gregorian static date-constant admission. Do not substitute either account for the other or the zone-free `CivilDate` predicate for either; [architecture](docs/ARCHITECTURE.md) owns the representation.

Consult [`docs/LEAN-ENCODING-GUIDE.md`](docs/LEAN-ENCODING-GUIDE.md) as staged guidance, never a writable plan: use its traps and bottom-up spine inside each capsule, not as a global domain-completion order. Follow the [risk-spike contract](docs/PROJECT-DESIGN.md#controlled-interleaving-and-coverage-horizons); do not write Lean for an unresolved representation choice.

Every new clause links to its canonical spec, source basis and exact assurance status, with its implemented surface recorded in [`docs/IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md). A Lean-only proof/representation finding does not trigger a behavioral spec/ledger change. Review theorem statements, hypotheses, direction, result domain and axiom dependencies; counts or `0 sorry` do not establish adequacy.

Before promoting Lean architecture/proof practices, inspect the audited projects' actual sources via [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md): Cedar is the primary precedent, Radix the secondary check. Prefer Cedar where they conflict unless A12 semantics or clean-room constraints supply a documented reason otherwise. Durable non-obvious lessons belong in [`docs/LEAN-FINDINGS.md`](docs/LEAN-FINDINGS.md).

## Conventions

English is canonical for code, identifiers, comments and docs. Follow global Markdown, comment and commit-message rules; operational records additionally follow [their exact contract](docs/DOC-DISCIPLINE.md#bounded-detailed-records).

### Comments — document semantic surplus

Use `/-! ... -/` for nontrivial Lean module boundaries, `/-- ... -/` for public contracts, and ordinary comments only for non-obvious constraints, oracle basis or construction choices. Explain why with a checkable basis, assumptions and failure limits, distinguishing structural failure from UNKNOWN and internal proof from kernel correspondence. Test names carry intent; comments explain separating witnesses or deliberate non-laws. Keep status/history in its document owner and remove invalidated comments in the same edit.
