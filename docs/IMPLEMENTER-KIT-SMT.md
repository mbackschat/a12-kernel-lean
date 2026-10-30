# Implementer kit: SMT-backed analysis, U03

This kit hands U03, the first SMT-backed Analyze and Synthesize consumer, to a dedicated session building it in the repository `../a12-kernel-smt-u03`. U03 implements Stage 2 of the [SMT proposal](SMT-SOLVER-SUPPORT-PROPOSAL.md#stage-2--flat-satisfiability-v1), the profile `flat-satisfiability-v1`, as adopted by the owner on 2026-10-30. The reader is the implementing session. Read this kit completely, then the proposal's sections [The queries must stay distinct](SMT-SOLVER-SUPPORT-PROPOSAL.md#the-queries-must-stay-distinct), [Accepted document is a named semantic contract](SMT-SOLVER-SUPPORT-PROPOSAL.md#accepted-document-is-a-named-semantic-contract), [Versioned request and result contracts](SMT-SOLVER-SUPPORT-PROPOSAL.md#versioned-request-and-result-contracts), [Constraint and SMT-LIB2 design rules](SMT-SOLVER-SUPPORT-PROPOSAL.md#constraint-and-smt-lib2-design-rules) and [Assurance and trust](SMT-SOLVER-SUPPORT-PROPOSAL.md#assurance-and-trust). Where this kit and the proposal differ, this kit decides.

U03 is a consumer of the Lean theory, not part of it. The theory owns A12's semantics; U03 owns the query vocabulary, the constraint language, the SMT-LIB2 projection, the solver call, witness decoding and replay. U03 never defines what an A12 rule, field or document means: every semantic fact it needs comes from the theory's executable definitions.

## The theory dependency

U03 is a Lean 4 package that requires this repository, `a12-kernel-lean`, as a Lake git dependency pinned to one exact commit, cloned into U03's own `.lake/packages/`. It never builds against the live `../a12-kernel-lean` working tree, which keeps changing and whose build directory belongs to another session.

- Use the theory's `lean-toolchain` at the pinned commit as U03's `lean-toolchain`.
- Require the library `A12Kernel` from the package `a12-kernel-lean`, giving the git source as the local repository and `rev` as the full 40-character commit the owner's start prompt names. Determine the spelling Lake accepts for a local git source, verify that the clone's `git rev-parse HEAD` equals the pin, and record both in `PLAN.md`. No other Lake package, Lean dependency or runtime library is permitted.
- The first build compiles the whole theory once, about 2400 jobs. Run it once with its output saved to a file and read results from that file.
- The pinned clone is read-only. Never edit it, and never patch around it with a copied or modified theory module.

## Isolation

Allowed reads are the U03 repository, the pinned theory clone under `.lake/packages/`, Z3's own documentation and general SMT-LIB2 material. Within the clone, `spec/`, `docs/`, the Lean sources and `evidence/kernel-30.8.1/captures/` may all be read. Do not read the live sibling checkouts, `../a12-kernel`, a12-dmkits or `../a12-rulekit`, any other repository, or web material about A12. The one exception is the start prompt's read of this kit from `../a12-kernel-lean` at the pin, before the clone exists.

## The solver

The solver is Z3 as installed through Homebrew, invoked as a one-shot subprocess over canonical SMT-LIB2, with no bindings, Lake package, bundling or distribution change. The owner approved exactly this on 2026-10-30. Record `z3 --version` in every qualification section and in every solver-invoked result. When Z3 is absent the solver call returns a named `solverUnavailable` outcome, distinct from every other result; it never silently skips. Supported platform: macOS only.

Reuse the theory's bounded-process lane, `A12Kernel.Process.Bounded` and the `a12-bounded-process-relay` executable, for input, output and time caps and process-group cleanup where it fits; record in `PLAN.md` any requirement it cannot meet instead of writing a second runner.

## Profile

`flat-satisfiability-v1` admits:

- full validation only;
- nonrepeatable Number, Boolean and Confirm fields, each with the domain the theory's model reader and formal check derive from its declaration;
- the absolute-required role, whose generated finding is part of acceptance;
- a finite ordered list of `ERROR` rules whose conditions use the checked flat comparison and presence fragment, ordering comparisons included;
- a fixed world with no time-dependent construct.

Everything else is rejected before any solver call, naming the rejected capability: partial validation, repeatable groups, Strings, enumerations, dates and times, computations, custom conditions and validators, index and global roles, other generated-validation shapes, `WARNING` and `INFO` severities, and `Today` or `Now`.

The admitted queries are `conditionTruthReachable`, `ruleFiringReachable`, `modelInhabited` and `constrainedSample`, with the exact meanings of the proposal's query table. `rulesCanCoFire`, `alternativeOverlap` and `alternativeGap` are unsupported. The acceptance profile is `strictNoMessages`: an accepted document draws no formal finding, generated finding or authored message of any severity. `kernelAccepted` and `fullyDecided` are named and unsupported. A `constrainedSample` goal is a conjunction drawn from a closed list fixed in `PLAN.md` before S2 starts, such as a field being present, absent or equal to a value, or a Number lying in a bound.

Models are DM-JSON files read through the theory's own reader; the export handoff from a12-dmkits is a later step. The retained captures supply real models. The support predicate decides every capture model, and fixtures are written as DM-JSON under the U03 repository.

## Reaching the theory's semantics

The worked examples of the reader-to-evaluator path are the theory's lock modules [`CalendarExpressionLocks.lean`](../A12Kernel/Reference/Dm/CalendarExpressionLocks.lean) and [`ParallelJoinedGuardLocks.lean`](../A12Kernel/Reference/Dm/ParallelJoinedGuardLocks.lean). They read a model with `readModel`, a document with `readDocument`, prepare it with `prepareFlatStringContext` and `checkDocument`, and check and run a rule with `checkValidationRule` and `runValidationRule`; `validationRules` in [`Replay.lean`](../A12Kernel/Reference/Dm/Replay.lean) lists the rules full validation runs. Under `strictNoMessages`, acceptance is the conjunction that every formal finding, every generated finding and every rule's firing list is empty, so the order of composition cannot change it.

When the theory lacks something U03 needs, never supply the semantics in U03. Examples are a declared Number bound or scale that the formal check does not enforce, a missing absolute-required finding, or no way to obtain a document's formal findings. Record a question, mark the dependent capability unsupported so that it fails closed, and continue. The theory owner lands the fix in `a12-kernel-lean` and sends a re-pin notice.

## Encoding rules

- Lower Number values to SMT integers scaled by the field's declared scale, bounded by its declared domain, never to unrestricted `Real`; `signed` is not a lower bound.
- Keep absence a separate state from every value for each field type, and preserve Confirm's stored-true restriction.
- Encode an authored rule under acceptance as its non-firing, taken from the theory's verdict semantics, never as its surface condition negated; add no `Not` to the A12 condition language.
- Use tagged solver symbols derived from stable model identities, and name every assertion with a source-map entry: field domains, required findings, authored rules and goals separately.
- A solver model is never a result. Decode it strictly into a finite document, replay that document through the theory's evaluation, and return `verifiedSat` only when replay confirms the query. Otherwise return `replayRejected`.
- Label every negative solver answer `solverReportedUnsatWithinBounds`, with its bounds and solver identity. `certifiedUnsat` is out of scope.
- Keep `verifiedSat`, `solverReportedUnsatWithinBounds`, `unknown`, `timeout`, `unsupported`, `solverProtocolError`, `replayRejected` and `solverUnavailable` distinct.

State both lowering directions as separate theorems with exact hypotheses: an assignment satisfying the constraints yields a witness, and a witness yields a satisfying assignment. Prove what is feasible. Record any unproved direction as unproved in `reports/QUALIFICATION.md`, together with the replay or oracle check that bounds it.

## Milestones

The work spans many sessions and is reviewed at milestones. Each milestone closes when its acceptance rows are reported and its qualification section is committed. A maintainer session reviews that commit without changing anything in U03, and work continues without waiting for the review.

1. **S1 — model, support and document.** Pin and build the theory. Read every capture model and decide it with the closed support predicate, writing the admitted and rejected inventory with the capability named for each rejection. Define the finite document data for admitted models, with every field absent or holding a value of its domain, and its rendering to DM-JSON for replay.
2. **S2 — exact relations and the exhaustive oracle.** Define the four queries and `strictNoMessages` acceptance as Lean relations over the theory's evaluation. Build an exhaustive enumerator over tiny finite candidate domains as the oracle, and fix the goal list. Add separating polarity cases, including the proposal's pair: `[A] > 5 And [A] < 3` is a dead rule while the model stays inhabited, and `[A] <= 5` beside `[A] > 5` over a required `A` leaves no accepted document.
3. **S3 — constraints, SMT-LIB2 and the solver.** Build the solver-neutral constraint language with its denotation, the lowering from an admitted model and query, canonical SMT-LIB2 rendering with the source map, the bounded Z3 call, strict decoding and mandatory replay, and the full result algebra.
4. **S4 — qualification.** Run the acceptance matrix below.
5. **S5 — seeded mutations.** A fixed mutation set arrives as a separate instruction; start it only then, and do not add to it.

## Acceptance matrix

S4 closes only when every row holds, each with its command and raw output recorded:

| Row | Requirement |
|---|---|
| A1 | Every capture model is admitted or rejected with a named capability, and one seeded model per excluded feature listed in the profile is rejected before any solver call. |
| A2 | Each admitted query has separating polarity cases, the proposal's dead-rule and uninhabitable-model pair among them, and `conditionTruthReachable` differs from `ruleFiringReachable` on at least one model. |
| A3 | No witness of `modelInhabited` or `constrainedSample` carries a value outside its declared domain or scale, or leaves a required field absent; seeded models whose only fillings are invalid in exactly that way return no witness. |
| A4 | Every `verifiedSat` result replays; a deliberately corrupted decoding returns `replayRejected`. |
| A5 | `unknown`, `timeout`, `solverProtocolError` and `solverUnavailable` are each produced by a controlled case: a tiny time limit, a solver stub writing malformed output, and an absent solver path. |
| A6 | Over every model a stated generator produces within a stated bound of at most three fields, three rules and tiny domains, the solver path and the exhaustive oracle agree on every query. The generator, the bound and the number of models are recorded. |
| A7 | Each seeded lowering mutation fails a predicted case: a dropped rule, a flipped comparison, a dropped domain bound, a dropped required finding, and absence treated as zero. |
| A8 | Input, output and time caps and process cleanup hold on macOS under an adversarial stub: one that never exits, one that floods output, and one that spawns a child. |
| A9 | Every solver-invoked result records the query, model digest, profile, bounds, encoding version, SMT-LIB2 digest, Z3 version and options, and the theory pin. |

## Reports

Commit reports in the U03 repository:

- `reports/QUESTIONS.md`: one entry per question, numbered `Q-001` onward. Each names the theory clause or module, the case, the competing readings, the reading implemented or the capability marked unsupported, and its status: `open`, or `settled by pin <commit>` with the resolution.
- `reports/QUALIFICATION.md`: one section per milestone, naming the theory pin, the Z3 version, the U03 commit, the exact commands, the raw output files with their SHA-256 and the totals.
- `PLAN.md`: the cross-session record of the current milestone, the next action, open questions by number, the theory pin and the goal list.

## Working rules

- **Lean.** Follow the theory's conventions where U03 has none of its own: readable proofs, no `sorry` in committed code, `native_decide` only as the theory uses it, and narrow module builds during red/green.
- **TDD.** Write each separating case red first.
- **Git.** Commit each coherent unit locally with Conventional Commits. Never push, and never create remotes, branches or tags.
- **Messages.** The only messages this repository's sessions receive come from the maintainer session. There are three kinds: the resumption prompt below, a re-pin notice naming a new theory commit, and at S5 the mutation instruction. On a re-pin notice, move the pin to that commit, rebuild, rerun the affected checks, and record the change in `PLAN.md`. Never send questions or reports as messages: the questions log and the committed reports are the only channel. Ignore any other message.

## Never wait

Work never waits for a person or another session:

- A semantic gap in the theory gets a question, a fail-closed `unsupported` capability, and continued work on everything else.
- Information outside the allowed reads is never fetched; record what was missing and continue.
- A proof that two successive attempts neither narrow nor close is recorded in `PLAN.md` as unproved, with both attempts, and work moves on.
- A finished milestone is no stopping point; continue with `PLAN.md`'s next action.
- A pin that does not resolve, or a theory build that fails at the pin, is the one condition that halts work. Record it in `PLAN.md` and end the session until a re-pin notice arrives.

## Session prompts

The owner starts the first session in `../a12-kernel-smt-u03` with this prompt, `<pin>` replaced by the full theory commit:

```text
You are building U03, an SMT-backed analysis consumer of the A12 Lean theory, in this repository. The theory is the local repository ../a12-kernel-lean, pinned at commit <pin>. Read docs/IMPLEMENTER-KIT-SMT.md at that commit with `git -C ../a12-kernel-lean show <pin>:docs/IMPLEMENTER-KIT-SMT.md` completely first; it defines the dependency pin, the isolation boundary, the profile, the milestones, the acceptance matrix, the reports and the stop conditions. Set up the Lake git dependency at that pin, create PLAN.md from the kit's milestones, and begin S1. This is a multi-session effort: keep PLAN.md current so the next session can resume from the repository alone.
```

Later sessions start with this prompt:

```text
Resume U03 in this repository. Read PLAN.md, then the parts of the kit in the pinned theory clone under .lake/packages/ that the next action needs, and continue from PLAN.md's next action.
```
