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

<a id="spec-2026-08-29-02"></a>
### `SPEC-2026-08-29-02` — a sibling-star computation is admitted from any ancestor of its repeatable target, not only its own parent

- `status`: pending
- `supersedes`: the declaration-placement clause of [`SPEC-2026-08-27-01`](archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-27-01--a-sibling-star-computation-may-target-a-repeatable-group-and-stays-parent-local). That entry's sibling-star runtime account is untouched; only its placement sentence is corrected.
- `clause`: [`09-computations.md` the generated-rule anchoring paragraph](../spec/09-computations.md)
- `delta`: the accepted entry recorded that "the computation must be declared at its target's own parent; declaration elsewhere is refused `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`". Measured against the Kernel, declaration at *any* ancestor is admitted; only a group the target does not lie below is refused. This is the same containment rule as [`SPEC-2026-08-29-01`](#spec-2026-08-29-01), now shown to govern the operand-bearing route and not just constants.
- `mechanism`: the earlier reading is what a relative operand produces. Moving the declaration to an ancestor while leaving the operand spelled against the old base refuses with `MVK_INVALID_ENTITY`, an operand-resolution failure under a different code. Re-spelling the operand for the new base, or writing it absolute, admits the same placement.
- `evidence`: [declaring-group gate checkpoint](sources/cross-layer-routes.md#src-computation-declaring-group-gate), the operand-bearing and misattribution rows — four placements with an absolute operand, the same four with a bare-constant control, and the three relative-spelling rows, all `KERNEL_CONFIRMED` at a12-dmkits `4ad7cec69df28790cd47adae14f7ab18eca4733e`, Kernel `30.8.1`.
- `surfaces`: any peer clause, test, or catalog note stating that a sibling-star or exact-address computation must be declared at its target's own parent.
- `local-scope`: this project's shared repeatable-target certificate keeps the narrower equality on purpose. Admission is measured; parent-local correlation *runtime* under an ancestor declaration is not, and every consuming family applies that correlation clause. Recorded at [`AddressedRepeatableTarget.lean`](../A12Kernel/Elaboration/AddressedRepeatableTarget.lean) and open in [SG4](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).
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
