# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns current `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. The 164 terminal receipts through 2026-08-28 are preserved with their stable anchors in the [historical ledger](archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md).

## Ledger contract

Every commit that corrects, narrows, or extends kernel behavior in `spec/` and still needs a12-dmkits reconciliation must add or update an entry here in the same change. The spec clause owns the complete semantic account; an entry links to that clause and records only the transport facts needed by a12-dmkits.

An inbound correction whose exact source revision is already committed and reviewed in a12-dmkits does not create a new outbound entry. Record that revision and its evidence route in [`SOURCES.md`](SOURCES.md). If the inbound result answers an existing `pending` or `handed-off` entry, update that same entry instead.

Pure spelling, formatting, link, and non-semantic navigation edits do not enter the ledger. One entry may group several clauses only when they express one coherent behavioral correction with one upstream acceptance decision.

Each entry has a stable `SPEC-YYYY-MM-DD-NN` or `EXP-YYYY-MM-DD-NN` ID that is unique across both this file and the [historical ledger](archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md). IDs are never reused. An entry records its exact status, canonical clause or experiment question, concise delta, evidence basis and kernel version, expected reconciliation surfaces, acceptance condition, local introducing revision, and reviewed a12-dmkits revision and disposition when terminal. A later correction creates a new entry with `Supersedes`; it never rewrites a terminal receipt.

Statuses are exactly `pending`, `handed-off`, `accepted`, `resolved`, `rejected`, or `superseded`. `accepted` requires review of an exact a12-dmkits revision against the entry's acceptance condition. `resolved` is only for an `EXP-` closed locally without an upstream observation. An inconclusive handback remains `handed-off`. Contrary kernel evidence prevents acceptance and requires the local semantic account to be corrected before the entry is rejected or superseded.

The user transfers pending entries. Treat the entire `../a12-rulekit/` checkout as read-only. Reconciliation here means inspecting an exact committed a12-dmkits revision and recording the reviewed outcome in the existing entry. Do not create a second feedback ledger. A `dmtool-release` instrument defect belongs in a dated feedback note under the user's exchange directory, as defined by [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback), not in this ledger.

The introducing revision cannot name itself inside the same commit. Until handoff, `introducing commit` means the first commit containing the stable entry ID; resolve it with:

```sh
git log --reverse -S 'SPEC-YYYY-MM-DD-NN' --format='%H' -- docs/A12-DMKITS-SPEC-SYNC-LEDGER.md | head -n 1
```

An exact a12-dmkits revision must resolve when its handback is reviewed. If later upstream history rewriting makes it unreachable, retain the historical citation, do not invent a replacement mapping, and re-discharge any reused claim against the maintained owner at the then-current reviewed revision. The [archived receipt-continuity record](archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#receipt-continuity) documents the established boundary and claim limit.

## Entry kinds and routing

- **`SPEC-…`** records a locally originated semantic correction that still needs a12-dmkits reconciliation. A locally measured static-legality finding is a `SPEC-`, not an experiment request.
- **`EXP-…`** requests one specific kernel-runtime observation only after the available local source, static-check, retained-evidence, and runtime-probe routes have been checked and shown unable to settle it. State the exact input, competing accounts, prediction under each account, negative result, and route limit. If no input distinguishes the accounts, the entry is not ready.
- A `dmtool-release` command, schema, diagnostic, exit, or artifact defect is instrument feedback rather than kernel semantics. A cross-project capability or retirement request follows the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule).

[`SOURCES.md`](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) owns the current observation-route inventory and [`TESTING.md`](TESTING.md#the-kernel-runtime-probe-route) owns its method. Every claim leaving this repository must also satisfy the discharge rule in [`../CLAUDE.md`](../CLAUDE.md#%EF%B8%8F-hard-rule--discharge-a-claim-before-stating-it-or-flag-it-and-surface-it).

## Current queue

<a id="spec-2026-08-29-04"></a>
### `SPEC-2026-08-29-04` — the rule-message `$#…$` group position admits the rule's own group and its ancestors

- `status`: pending
- `clause`: [`11-messages-and-custom.md` the parameter-grammar clauses](../spec/11-messages-and-custom.md)
- `delta`: the clause covered the parameter **name** position, where `RootGroup`/`LfdNr` draws `INVALID_ENTITY`, and explicitly scoped that measured absence to the rule-owned carrier. It said nothing about the `$#…$` **group** position, which resolves the same words differently: `$#RootGroup$` and `$#RuleGroup$` are admitted there. The position takes an absolute group path, and the admitted set is the rule's own group plus its ancestors at any depth. A declared descendant, a sibling, and a group under a declared root that does not contain the rule all draw `INVALID_GROUP`, as does a relative spelling of a real group.
- `delta`: an absolute argument resolves in **two gates the Kernel reports apart**, which a first pass of this entry got wrong by claiming one code covered the whole refusal. An undeclared first segment draws `INVALID_ROOT_GROUP` whatever follows it, so `$#/Nope$` and `$#/Nope/Rows$` share that code and `$#/probe$` shows the match is case-sensitive; only under a declared root does containment decide and report `INVALID_GROUP`. Segments take the name grammar's single-quote escape, so `$#/'Probe'/'Rows'$` reaches the same group as its bare spelling, while a malformed spelling is refused earlier on its own lexical codes: `MVK_LEXER_STANDARD_ERROR` for an unbalanced quote or empty quoted segment, `MVK_INCOMPLETE_INPUT` for a trailing separator, `MVK_UNEXPECTED_TOKEN` for a doubled one.
- `delta`: `$#RootGroup$` names the root of the **rule's own** ancestor chain, not a model-wide root. A model with two root groups is authorable and kernel-valid, and it separates the readings: a rule under the second root admits the shorthand while the first root draws `INVALID_GROUP`. Admission cannot separate that reading from an unconditional admission, since the chain root always contains the rule's group; what it settles is that the primary root is not what the shorthand means.
- `mechanism`: containment, running opposite to the computation declaring-group gate. There the computed field must lie at or below the declaring group; here the *named* group must contain the rule's group, and `RootGroup`/`RuleGroup` are keyword shorthands for the two endpoints of that chain.
- `mechanism`: the **terminal match is on the raw argument**, so quoting removes a word's terminal reading rather than merely being stripped ahead of it. `$#'RootGroup'$` and `$#'RuleGroup'$` draw `INVALID_GROUP` naming a group of that name, and `$#'Zeile'$` draws `INVALID_GROUP` rather than the retired code its bare spelling draws. That is the separator between the two tempting accounts of the escape.
- `delta`: the clause's existing assertion that `Zeile` and `Usb` "are not permitted in an A12 model at all" gains its code. Both draw `PARAM_INVALID_IN_NEW_WORLD`, distinct from `INVALID_GROUP`, so the Kernel recognizes the terminals and refuses them on the modern route rather than failing to parse them. `Vordruckzeile`, `Vordruckname`, and `index(...)` draw plain `INVALID_GROUP` on this carrier and so are not terminals in this position.
- `evidence`: [group-parameter checkpoint](sources/temporal-and-message-probes.md#src-message-group-parameter) for the admitted set, and the [resolution checkpoint](sources/temporal-and-message-probes.md#src-message-group-parameter-resolution) for the two gates, the quoting rule, and the two-root separator. Both are `rule check --message` verdicts at a12-dmkits `4e78f8254bcf12f6d94fc23c5c3cd5e4906c8d04` (clean), `dmtool` 0.13.0, Kernel `30.8.1`, each batch carrying admitted and refused controls.
- `confound`: a first attempt used a negative condition and every row, controls included, refused `MVK_NEG_CONDITION_IN_ITERATION` before the error-text checker ran. Any peer reproduction needs a positive condition or it measures the condition gate instead.
- `surfaces`: any peer clause, test, or catalog note that treats `$#…$` as a second spelling of the name position, or that constrains the group parameter to the rule's own group alone.
- `local-scope`: closed for static admission. [§13](IMPLEMENTATION-MAP.md#13--message-interpolation) owns the implemented boundary; what the position renders is still unmeasured and stays with [SG10](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration).
- `acceptance`: a12-dmkits states the group position's admitted set and its two resolution gates, or supplies the contrary measurement.
- `introducing commit`: resolve with the ledger contract's `git log --reverse -S` recipe.
- `reviewed a12-dmkits revision`: none yet.

<a id="spec-2026-08-29-03"></a>
### `SPEC-2026-08-29-03` — an aggregate over a star derives no iteration, so a fixed computation target has no placement restriction at all

- `status`: pending
- `clause`: [`09-computations.md` the generated-rule anchoring paragraph](../spec/09-computations.md)
- `delta`: the reconciled account states that iteration is derived from the computed field's own repeatable scope *or* from a per-row operand of a repeatable declaring group. It does not say which operands count. Measured: a sibling-star `FirstFilledValue` is **not** a per-row operand. A star aggregate into a *fixed* target is admitted from the target's own group, from an ancestor, from an unrelated sibling group, and from the starred source's own repeatable group — the identical pattern a bare constant gives at the same four placements. So a fixed target carries no placement restriction until an operand actually reads per row.
- `delta`: the same clause's adjacent-gate sentence also gains a qualifier it was missing. An unstarred read of a repeatable field is refused `MVK_NO_WILDCARD` only **from a nonrepeatable declaring group**; from a repeatable one the identical read reaches the placement gate and refuses `MVK_ERROR_FIELD_NOT_IN_RULEGROUP` instead. Stated without that qualifier the sentence claims the wildcard gate always pre-empts placement, which the measurement contradicts.
- `mechanism`: the same model separates the two operand classes. The unstarred per-row read `[Marker]` declared at the repeatable `/Probe/Rows` refuses `MVK_ERROR_FIELD_NOT_IN_RULEGROUP` with the Kernel's own text naming iteration, while `FirstFilledValue(/Probe/Rows*/Marker)` at the same declaring group is admitted. The distinction is aggregation, not the presence of a repeatable group in the operand path. An unstarred read of a repeatable field from a nonrepeatable declaring group never reaches this gate: `MVK_NO_WILDCARD` refuses it earlier.
- `evidence`: [fixed-target star placement checkpoint](sources/cross-layer-routes.md#src-fixed-target-star-placement), 25 `KERNEL_CONFIRMED` `computation add --dry-run` verdicts over one model at a12-dmkits `4e78f8254bcf12f6d94fc23c5c3cd5e4906c8d04` (clean), `dmtool` 0.13.0, Kernel `30.8.1` built and runtime. The `matrix` and `carrier` keys carry the admissions, the `separator` key the per-row-operand refusal this entry's mechanism rests on, and the `control` key the negative control: a repeatable target declared at a non-containing group refuses `MVK_ERROR_FIELD_NOT_IN_RULEGROUP` in the same model, so the gate is reachable and the admissions are not an unreachable-gate artifact.
- `surfaces`: any peer clause, test, or catalog note that treats a starred operand of a repeatable group as deriving iteration, or that constrains where a fixed-target computation may be declared.
- `local-scope`: seven Lean gates refuse a fixed target outside its own declaring group and are therefore narrower than the Kernel on this shape. Closing them is not a widening to containment — containment also refuses the measured sibling admission — but the removal of a placement gate plus an iteration-derivation check. Open in [SG4](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).
- `acceptance`: a12-dmkits states which operand classes derive iteration, or supplies the contrary measurement showing a star aggregate into a fixed target refused on placement.
- `introducing commit`: resolve with the ledger contract's `git log --reverse -S` recipe.
- `reviewed a12-dmkits revision`: none yet.

<a id="spec-2026-08-29-02"></a>
### `SPEC-2026-08-29-02` — a sibling-star computation is admitted from any ancestor of its repeatable target, not only its own parent

- `status`: pending
- `supersedes`: the declaration-placement clause of [`SPEC-2026-08-27-01`](archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-27-01--a-sibling-star-computation-may-target-a-repeatable-group-and-stays-parent-local). That entry's sibling-star runtime account is untouched; only its placement sentence is corrected.
- `clause`: [`09-computations.md` the generated-rule anchoring paragraph](../spec/09-computations.md)
- `delta`: the accepted entry recorded that "the computation must be declared at its target's own parent; declaration elsewhere is refused `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`". Measured against the Kernel, declaration at *any* ancestor is admitted; only a group the target does not lie below is refused. This is the same containment rule as [`SPEC-2026-08-29-01`](#spec-2026-08-29-01), now shown to govern the operand-bearing route and not just constants.
- `mechanism`: the earlier reading is what a relative operand produces. Moving the declaration to an ancestor while leaving the operand spelled against the old base refuses with `MVK_INVALID_ENTITY`, an operand-resolution failure under a different code. Re-spelling the operand for the new base, or writing it absolute, admits the same placement.
- `evidence`: [declaring-group gate checkpoint](sources/cross-layer-routes.md#src-computation-declaring-group-gate), the operand-bearing and misattribution rows — four placements with an absolute operand, the same four with a bare-constant control, and the three relative-spelling rows, all `KERNEL_CONFIRMED` at a12-dmkits `4ad7cec69df28790cd47adae14f7ab18eca4733e`, Kernel `30.8.1`.
- `surfaces`: any peer clause, test, or catalog note stating that a sibling-star or exact-address computation must be declared at its target's own parent.
- `local-scope`: closed. Every repeatable-target gate now admits by containment, and parent-local correlation under an ancestor declaration was measured separately before the widening landed. Recorded at [`AddressedRepeatableTarget.lean`](../A12Kernel/Elaboration/AddressedRepeatableTarget.lean).
- `acceptance`: a12-dmkits restates the placement clause as containment, or supplies the contrary measurement showing the ancestor declaration refused with a correctly spelled operand.
- `introducing commit`: resolve with the ledger contract's `git log --reverse -S` recipe.
- `reviewed a12-dmkits revision`: none yet.

<a id="spec-2026-08-29-01"></a>
### `SPEC-2026-08-29-01` — `MVK_ERROR_FIELD_NOT_IN_RULEGROUP` is a containment gate under derived iteration, and the computed field's own repetition derives it

- `status`: accepted
- `clause`: [`09-computations.md` the generated-rule anchoring paragraph](../spec/09-computations.md) and its §1 declaration-group bullets
- `delta`: the gate fires exactly when iteration is derived **and** the computed field does not lie at or below the declaring group. Iteration has two independent sources: a per-row operand of a repeatable declaring group, and the computed field's own repeatable scope reaching the gate through the generated rule anchored at that field. Containment, not parenthood, is what admits: an ancestor declaring group including the root is accepted. A repeatable declaring group derives no iteration by itself.
- `delta`: separately, the declaring group contributes no repetition at runtime. A constant computation declared in a repeatable group whose fixed target sits elsewhere produces exactly one value whether that group has zero or three instantiated rows.
- `corrects`: this repository previously stated the placement-only reading — that declaration outside a repeatable target's own group is refused *and* that the operand is irrelevant. Both halves were wrong. a12-dmkits' handback of 2026-08-29 states the mirrored operand-only reading, that "placement alone never refuses", recorded there as `KERNEL-FINDINGS` `KF212`, locked by `validate.laws.ComputationDeclaringGroupLawsTest`, and published in the shipped `schema computation add` description of the new `group` key. A constant into a repeatable target declared elsewhere carries no operand and is still refused, so that universal negative is false. Every row of the handback's own four-row matrix reproduces; it held the computed field non-repeatable throughout and so could not reach this case.
- `evidence`: [declaring-group gate checkpoint](sources/cross-layer-routes.md#src-computation-declaring-group-gate) — seven `KERNEL_CONFIRMED` static rows and one `:adapter:kernelProbe` artifact at a12-dmkits `4ad7cec69df28790cd47adae14f7ab18eca4733e`, Kernel `30.8.1`, both codegen strategies agreeing.
- `surfaces`: `KF212` and its locking test, the `group` key's published schema description, and any interpreter or validator path that pre-checks placement independently of derived iteration.
- `acceptance`: a12-dmkits restates the gate as containment under derived iteration, its locking test gains the constant-into-repeatable-target row and the admitted ancestor-declaration row, and the shipped schema description drops "Placement alone never refuses".
- `introducing commit`: resolve with the ledger contract's `git log --reverse -S` recipe.
- `reviewed a12-dmkits revision`: `ab055329376fe89f6cdf9490bad0e9520e3a56f3`, reviewed clean at HEAD. Every acceptance condition is met: `KF212` is restated as containment under derived iteration with the parenthood reading corrected, the shipped schema description no longer claims placement never refuses, and `ComputationDeclaringGroupLawsTest` gains both required rows plus the two unrelated-subtree controls, with the retraction recorded in the class javadoc rather than left as a silent edit. The peer reproduced the counterexample on its own `/Depot` model instead of adopting the reported rows.
- `disposition`: accepted. The revision also supplies an inbound rule/computation asymmetry recorded at the [declaring-group gate checkpoint](sources/cross-layer-routes.md#src-computation-declaring-group-gate); under the no-feedback-loop rule it creates no new outbound entry, and it is held on reviewed peer provenance because this project's `rule check` route cannot reach that cell.
