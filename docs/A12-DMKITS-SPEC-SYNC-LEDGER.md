# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns open `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. Terminal receipts leave this queue after their useful live facts are preserved in the canonical spec, source or gap owner.

The terminal receipts retired on 2026-10-10 remain in [the ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), under their stable entry anchors. Earlier deleted receipts remain in [the historical ledger](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md) and [the accepted receipts through 2026-09-24](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md) at `a050f150`. Recover any exact receipt with `git show <revision>:<path>` and find its stable ID; retired IDs are never reused.

## Ledger contract

Every commit that corrects, narrows, or extends kernel behavior in `spec/` and still needs a12-dmkits reconciliation must add or update an entry here in the same change. The spec clause owns the complete semantic account; an entry links to that clause and records only the transport facts needed by a12-dmkits.

An inbound correction whose exact source revision is already committed and reviewed in a12-dmkits does not create a new outbound entry. Record that revision and its evidence route in [`SOURCES.md`](SOURCES.md). If the inbound result answers an existing `pending` or `handed-off` entry, update that same entry instead.

Pure spelling, formatting, link, and non-semantic navigation edits do not enter the ledger. One entry may group several clauses only when they express one coherent behavioral correction with one upstream acceptance decision.

Each entry has a stable `SPEC-YYYY-MM-DD-NN` or `EXP-YYYY-MM-DD-NN` ID that is unique across the live queue and its retired Git history. IDs are never reused. An entry records its exact status, canonical clause or experiment question, concise delta, evidence basis and kernel version, expected reconciliation surfaces, acceptance condition, local introducing revision, and reviewed a12-dmkits revision and disposition when terminal. A later correction creates a new entry with `Supersedes`; it never rewrites a terminal receipt.

Statuses are exactly `pending`, `handed-off`, `accepted`, `answered`, `resolved`, `rejected`, or `superseded`. `accepted` requires review of an exact a12-dmkits revision against the entry's acceptance condition. `resolved` is only for an `EXP-` closed locally without an upstream observation. **`answered` is for an entry the peer engaged whose outcome is neither acceptance nor refutation**, and it exists because four entries reached exactly that state and the six-status list could not express any of them: an `EXP-` closed *by* an upstream observation rather than locally, and a `SPEC-` where the peer could not corroborate in the way its own acceptance condition anticipated, or found reconciliation unnecessary, or stated a free choice not to carry it. An `answered` entry owes nothing in either direction and carries a `disposition` or `answered` row saying which of those it was; do not relabel one as `accepted`, which asserts an acceptance review that never happened. An inconclusive handback remains `handed-off`. Contrary kernel evidence prevents acceptance and requires the local semantic account to be corrected before the entry is rejected or superseded.

The user transfers pending entries. Treat the entire `../a12-rulekit/` checkout as read-only. Reconciliation here means inspecting an exact committed a12-dmkits revision and recording the reviewed outcome in the existing entry. Do not create a second feedback ledger. A `dmtool-release` instrument defect goes to the a12-dmkits session directly, or to a dated feedback note under the user's exchange directory when no such session is reachable, as defined by [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback); neither belongs in this ledger.

The introducing revision cannot name itself inside the same commit. Until handoff, `introducing commit` means the first commit containing the stable entry ID; resolve it with:

```sh
git log --reverse -S 'SPEC-YYYY-MM-DD-NN' --format='%H' -- docs/A12-DMKITS-SPEC-SYNC-LEDGER.md | head -n 1
```

An exact a12-dmkits revision must resolve when its handback is reviewed. If later upstream history rewriting makes it unreachable, retain the historical citation, do not invent a replacement mapping, and re-discharge any reused claim against the maintained owner at the then-current reviewed revision. The measured boundary and claim limit are the older receipt file's `#receipt-continuity` section at that revision.

## Entry kinds and routing

- **`SPEC-…`** records a locally originated semantic correction that still needs a12-dmkits reconciliation. A locally measured static-legality finding is a `SPEC-`, not an experiment request.
- **`EXP-…`** requests one specific kernel-runtime observation only after the available local source, static-check, retained-evidence, and runtime-probe routes have been checked and shown unable to settle it. State the exact input, competing accounts, prediction under each account, negative result, and route limit. If no input distinguishes the accounts, the entry is not ready.
- **The user carries pending entries to a12-dmkits.** Prepare the stable ID and its checkpoint anchor in the same change. Do not send entries to peer sessions automatically; reconcile the exact committed handback when the user supplies it, following [the repository authority](../CLAUDE.md#%EF%B8%8F-hard-rule--request-a12-dmkits-improvements-upstream-never-patch-a-copied-harness).
- **The routing test is one question: is kernel behavior in question, or only this project's ability to observe it?** A `dmtool-release` command, schema, diagnostic, exit, or artifact defect is instrument feedback rather than kernel semantics: it goes to the a12-dmkits session directly or, when none is reachable, to a dated feedback note in the user's `~/Downloads` exchange directory per [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback), and **never to this ledger**, because a note has no acceptance condition or reviewed-revision receipt. A missing tool capability that blocks a measurement is such a note, while the semantic question it blocks is an entry. A cross-project capability or retirement request follows the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule).

[`SOURCES.md`](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) owns the current observation-route inventory and [`TESTING.md`](TESTING.md#the-kernel-runtime-probe-route) owns its method. Every claim leaving this repository must also satisfy the discharge rule in [`../CLAUDE.md`](../CLAUDE.md#%EF%B8%8F-hard-rule--discharge-a-claim-before-stating-it-or-flag-it-and-surface-it).

## Current queue

Eight entries are `accepted`, reconciled by the [October 23 handback](sources/inbound-handbacks.md#src-inbound-2026-10-23), and four are `pending`. The 16 terminal receipts closed at the [October 18 response](sources/inbound-handbacks.md#src-inbound-2026-10-18), fourteen `accepted` and two `answered`, remain in [the ledger at `bf2216b6`](https://github.com/mbackschat/a12-kernel-lean/blob/bf2216b69d5a3bbaefe182b76271ddf8d6b27ecf/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).

<a id="spec-2026-10-22-01"></a>
### SPEC-2026-10-22-01 — a bracketed read inside `Length` or a day difference is a token defect

- `status`: accepted
- `canonical`: [spec/12 §3](../spec/12-concrete-syntax.md#3-the-condition-and-operation-grammar-sketch).
- `delta`: `Length` names its field as an entity, and `DifferenceInDays` takes a bare path, so a bracketed read in either slot draws `MVK_UNEXPECTED_TOKEN` rather than being read as the field's value; `Length(/Order/Note)` is the admitted String control. Other entity-typed slots, the other differences included, are unmeasured.
- `basis`: [condition-class checkpoint](sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection), rows `O08` (`Length([/Order/Qty])`), `O09` (`Length([/Order/Note])`) and `O09b`, measured locally 2026-10-01, Kernel 30.8.1, replayed by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean); the [yearless-anchor checkpoint](sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year)'s `instrument` row `DifferenceInDays([/G/F], …)`, measured locally 2026-09-04.
- `acceptance`: Reconcile the class of the three bracketed rows, and the `Length([F]) > 5` spelling of [KF34](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf34) whose rule read it names. Do not claim a class for a relative bracketed read or for another entity-typed slot.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles; the peer corrected its KF34 spelling to the bare `Length(F)`, and its rows extend the class to a relative bracketed read and both `DifferenceInDays` slots, re-measured locally. `CheckerBracketedEntitySlotAgreementTest`, KF600; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-22-02"></a>
### SPEC-2026-10-22-02 — the document conversion drops a member the model does not declare

- `status`: accepted
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands).
- `delta`: Kernel Document JSON conversion drops an undeclared string or object member of a fixed group and an undeclared string key inside a repeatable row, so the document validates exactly as the one without them. Other JSON kinds, an object inside a row, a member at the document root and the conversion's notifications for a dropped member are unmeasured.
- `basis`: [undeclared-member checkpoint](sources/domain-ingestion-probes.md#src-undeclared-document-members), rows `f-extra` against `f-full`, measured locally 2026-10-22, Kernel 30.8.1, both strategies, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile the interpreter's document reader with the three dropped shapes. Do not claim an outcome for an undeclared array, a scalar of another JSON kind, an object inside a row, a member at the document root or the deserializer's notification channel.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles; the peer reader already conformed, and its rows extend the drop to every JSON kind measured and to a string beside the root group, now adopted by the Lean document reader. `A12JsonIngressDiffTest`, KF1; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-22-03"></a>
### SPEC-2026-10-22-03 — a repeatable or parallel rule reports a reached unregistered name at its first error address

- `status`: accepted
- `canonical`: [spec/11 §14](../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).
- `delta`: The VALUE report of a reached unregistered custom condition ([KF52](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf52)) stands once, at the iterator's first error address, on a repeatable, root-iterated and parallel rule, even when a later row reached the name. On a repeatable rule earlier firing rows keep their messages and later rows are not evaluated. A partial call's iterator starts where its relevant set's error-field selectors, compressed into one, start it: at their one row, or at the first row when they name different rows. A parallel rule's first address is the join's first row, an unmatched one with its `UNKNOWN` coordinate included; its later rows and earlier firings are unmeasured.
- `basis`: [call checkpoint](sources/model-structure-and-declaration-probes.md#src-custom-condition-calls), rules `M01`–`M04` and `E01` of `request-missing`, rows `m-claim`, `m-row3` and `m-keep`, and of `request-review`, rows `r1-rows23`, `r2-order` and `r3-supply-first`, measured locally 2026-10-22, Kernel 30.8.1, both strategies, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile the address, the single report per rule, the compressed partial start and the retained earlier firing for the five rules. Do not claim an outcome under a repeatable outer row of a parallel rule, for its later joined rows or for a parallel rule with an earlier firing row.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles on the Kernel's side; the peer interpreter keeps refusing an unregistered custom condition when it prepares the model, as declared policy, so it never reproduces the report. `CustomConditionUnregisteredReportLawsTest`, KF52; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-22-04"></a>
### SPEC-2026-10-22-04 — a custom-condition name is reached by the rule's two evaluation passes

- `status`: accepted
- `canonical`: [spec/11 §14](../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).
- `delta`: Replaces "a guard that decides the condition first leaves the lookup unreached". A false conjunct ahead of the name in an `And` leaves it unreached, and so does a disjunct already true when the tree needs no classification pass; a holding tree that needs one evaluates again past that disjunct, so `FieldNotFilled(Stage) Or CustomCondition X` reaches the name with `Stage` empty or filled. In a parallel rule a field pair whose fill quantifier does not fire on a joined row ends the `And` there.
- `basis`: [call checkpoint](sources/model-structure-and-declaration-probes.md#src-custom-condition-calls), rule `M06` in rows `r1-rows23` and `r2-order`, `E01` in `m-claim` and `M04` in `r1-rows23`, measured locally 2026-10-22, Kernel 30.8.1, both strategies, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile reach of the unregistered name for the three rules on both channels. Do not claim an outcome for a classification pass of a parallel rule or for a callback that throws.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles on the Kernel's side, with `-03`'s policy note; the same probe measured a registered callback's call counts (KF604), which the classification pass already gives. `CustomConditionUnregisteredReportLawsTest`, KF52; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-22-05"></a>
### SPEC-2026-10-22-05 — the iteration guard skips a level and judges comparisons by three constant rules

- `status`: accepted
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands).
- `delta`: The twice-repeating keyed licence exempts the group's level from the guard rather than licensing one negative, so it covers every leaf there and a negative inside such a group is still judged at an enclosing level. A comparison is refused by a count below a positive constant on either side, a value operation equal to a constant converting to zero, or a mix of iterating and fixed reads against any constant, with brackets transparent. `CurrentRepetition` is an unguarded leaf, the three value-list quantifiers have their own rules, a `$` read inside a filter references no level, and an unreferenced error field answers ahead of the guard.
- `basis`: [K04 checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04), rows `e01`–`e11`, `u01`–`u30`, `a01`–`a06` and `o01`–`o03`, measured locally 2026-10-22, Kernel 30.8.1, at the measurement pin `09f1352e5`; the constant and operator rows of the [October 22b peer rows](sources/inbound-handbacks.md#src-inbound-2026-10-22b).
- `acceptance`: Reconcile the guard's outcome on those rows. The clause's source-read extensions, the nested `CurrentRepetition` and filter-read rules, a non-constant side and an H model's exemption are unmeasured; do not claim them as measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles; the peer's portable checker names the Kernel's class on every row, as peer-reported. `CheckerIterationK04AgreementTest`, KF601; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-23-01"></a>
### SPEC-2026-10-23-01 — selections bind and weigh alike for fields and groups, and only a join's own group joins its error field

- `status`: accepted
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) and its parallel-iteration constraints.
- `delta`: Beyond the [October 22c rows](sources/inbound-handbacks.md#src-inbound-2026-10-22c): the error-field iteration class follows the parallel iteration, so beside an unkeyed group a starred-only error field draws `MVK_NO_WILDCARD`; a presence of a group above the joined one does not join the error field, one of the joined group does; a field-keyed field or group selection is admitted with its key read from the iterated row and guards that row as a positive, while `NoFieldFilled` beside a field-keyed selection refuses; a negative field or group selection alone fails its parent's level; a constant group selection binds below an unkeyed iterated row; and a constant selection of the iterated group's own field is one independent slot in the field-fill quantifiers and `FieldValuesNotUnique`.
- `basis`: [Binding checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04), discriminator rows `d1`, `d2`, `d5`, `d6` and the `review` rows `v1`–`v18`, measured locally 2026-10-23, Kernel 30.8.1, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile the class and admission of those rows. The runtime of a selection read at the rule's row is unmeasured; do not claim it as measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles, with the peer's checker agreeing on every row, as peer-reported. `CheckerIterationK04AgreementTest`, KF601; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-23-02"></a>
### SPEC-2026-10-23-02 — a rule may report on a group, whose own level is unindexed, and a blank root runs a negative over the exempt keyed level

- `status`: accepted
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands).
- `delta`: A non-root group error entity fires at its own pointer once per iterated row above it; a repeating group's own level is pinned to its first row, where field reads and fixed subgroup presence read that row while the group's own presence reads every row. Its own and a containing group's presence reference it while a field inside or above it does not, only the levels above it need a binding reference, the guard still judges its own level, and the message type, fill-to-fix entries and references follow the condition's leaves. Beside a joined side, the measured group target fires once per joined row whose partner meets the condition. Separately, a blank nonrepeatable root runs a negative over a twice-repeating keyed group at every declared row, for field and group targets alike.
- `basis`: [Group-target checkpoint](sources/model-structure-and-declaration-probes.md#src-group-target-nested-join), rows `E1`–`E6`, `t0`–`t8`, `v1`–`v5`, and the [K04 checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04) rows `g01`–`g06`, measured locally 2026-10-22 and 2026-10-23, Kernel 30.8.1, replayed by the [group-target locks](../A12Kernel/Reference/Dm/GroupTargetLocks.lean), the [guard locks](../A12Kernel/Reference/Dm/IterationGuardLocks.lean) and `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the pointer, message type, references and admission of those rows, and the blank-root firings of `E3`, `v1` and `v2`. Do not claim the blank-root dispatch for other conditions or roots, partial validation of a group target, the reference of leaves other than field and group presence, or the firing of a rule reporting on the root.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles; the peer interpreter's agreement on the five runtime channels is peer-reported. Its extension, that a partial call reports no group-target rule, is adopted locally. `CheckerIterationK04AgreementTest`, `GroupTargetRuntimeDiffTest`, `GroupTargetCarrierDiffTest`, KF601, KF603; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-23-03"></a>
### SPEC-2026-10-23-03 — an error field below a joined side iterates its own levels within each joined row

- `status`: accepted
- `canonical`: [spec/07 §2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key).
- `delta`: A rule whose error field sits one unkeyed level below a joined group visits that level's rows inside each joined row, firing at the nested row's pointer, on an unmatched partner too, with both index fields and the partner row among its references. The pair over the nested field is judged as the direct pair; an unguarded nested level draws the negative-iteration class and a guarded one admits the rule. A computation into that field computes every instantiated nested row whose precondition holds, on matched and unmatched rows, and clears a seeded nested row of a matched row whose precondition fails.
- `basis`: The [K04 checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04) rows `a10`, `a11`, the [binding checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04) rows `s9`, `k08`, and the [runtime checkpoint](sources/model-structure-and-declaration-probes.md#src-group-target-nested-join) rows `C0`–`C2`, `k00`, `k08`, measured locally 2026-10-22 and 2026-10-23, Kernel 30.8.1, replayed by the [guard](../A12Kernel/Reference/Dm/IterationGuardLocks.lean) and [binding](../A12Kernel/Reference/Dm/IterationBindingLocks.lean) locks and `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the classes and admission of those rows, and the pointers, references, computed values and clears of the runtime rows. Do not claim the nested rows a rule visits beyond the instantiated ones, nested levels without a reference or unclassified, value leaves over the nested field, clears on an unmatched row, non-Number targets, an error field below the partner's side, or partial validation.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`.
- `disposition`: Reconciles; its extension, the capacity rule for nested rows beyond the instantiated ones, was re-measured and adopted locally. `GroupTargetRuntimeDiffTest`, `GroupTargetCarrierDiffTest`, KF603; [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-23).

<a id="spec-2026-10-23-04"></a>
### SPEC-2026-10-23-04 — a count below one is drawn at the groups and fields beneath it, not at its rules or computations

- `status`: pending
- `canonical`: [spec/01 §1](../spec/01-data-model.md#1-model--a-typed-tree), the names, groups and texts paragraph.
- `delta`: The [October 21 letter](sources/inbound-handbacks.md#src-inbound-2026-10-21) §2.17 states `MVK_MAX_VALUES_INVALID` at every element beneath a group whose count is below one; this account draws it at every group and field beneath it, because the Kernel's entity walk (`NoMetaModelChecks.checkEntity`, kernel-core-codegen) visits groups and fields only, so a rule or computation beneath draws none.
- `basis`: The letter's §2.17 rows, whose hosts hold groups and fields only, and the source read of that walk, 2026-10-23; replayed for groups and fields by the [declaration-walk locks](../A12Kernel/Reference/Dm/DeclarationWalkLocks.lean).
- `acceptance`: Reconcile the wording to groups and fields. A rule or computation beneath such a group is source-read only and unmeasured; do not claim it as measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-23-05"></a>
### SPEC-2026-10-23-05 — an ungated rule runs under a blank root, and a group target beside a join draws its field twin's class

- `status`: pending
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) and [§2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key).
- `delta`: Beyond [SPEC-2026-10-23-02](#spec-2026-10-23-02) and [-03](#spec-2026-10-23-03): a rule evaluated without admitted content, by a negative, a small-side count, an `Or` beside a negative or a second root's read, runs under a blank nonrepeatable root at every declared row of a keyed level, the second-root read alone included (`r1`), while a condition gated on a value waits for it. Beside a join a group target's reads are checked in order as its field twin's, its own level unindexed: a field or group read reaching the join draws `MVK_ERROR_FIELD_NO_INDEX` below no keyed group, a keyed target included, and `MVK_MULTIPLE_INDEX_FIELDS` below two, and an earlier read its own class first, the twin's `MVK_NO_WILDCARD` and `MVK_PARALLEL_ITERATION_NOT_ALLOWED` included; a field-fill list across the join and a group holding no field of its own are admitted. Below a joined side, a condition not reading the nested level draws `MVK_ERROR_FIELD_NOT_REFERENCED`, and a comparison over the nested field is admitted.
- `basis`: The [blank-root checkpoint](sources/model-structure-and-declaration-probes.md#src-blank-root-dispatch-k06), rows `d1`–`d13`, `p1`–`p11`, `q1`–`q5f`, `m1`–`m5f` and `r1`, measured locally 2026-10-23, Kernel 30.8.1, at the measurement pin `09f1352e5`, replayed by the [group-target locks](../A12Kernel/Reference/Dm/GroupTargetLocks.lean) and `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the classes, admissions and firings of those rows. Every negative or small-side count measured over a repeatable root, a nested keyed level or an unkeyed level is refused, and the second-root rule over a repeatable root needs content beside it, so the dispatch of a repeatable root is not observed; do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-23-06"></a>
### SPEC-2026-10-23-06 — value slots refuse a bare name, completed productions bind first, and a joined side's nested rows follow capacity

- `status`: pending
- `canonical`: [spec/12 §3](../spec/12-concrete-syntax.md#3-the-condition-and-operation-grammar-sketch), [spec/05](../spec/05-dates-and-time.md), [spec/08](../spec/08-paths-and-references.md) and [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) and [§2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key).
- `delta`: Beyond the [October 23 handback](sources/inbound-handbacks.md#src-inbound-2026-10-23): a bare name in a value slot of `Abs`, `Min`, `Max` and the three roundings draws `MVK_UNEXPECTED_TOKEN`, outside a filter body and, bare or `$`-marked, inside one, as does any read in a rounding's digits slot, while a production completed before it meets its gates at the rule's binding first; a standalone `ValueAsDate` meets the gates it meets in a filter body; a raw-type key draws `MVK_INVALID_RAW_TYPE` in a bracketed read, a group presence and a field absence; a field-keyed group list is admitted under `And`, beside a constant selection, and `NoGroupFilled` over it is admitted under `And` and draws the negative-iteration class under `Or`; a filled count over one field per joined side meets the count's own guard, refused against `< 1` only among the eight thresholds measured, and against `> 0` and `>= 2` runs as its fill quantifier; below a joined side, other groups' rows at the nested depth, an unjoined group's included, count toward the occupancy that sets the visited rows, and a `Picks` row without a line reads its parts empty; a keyed group target beside a join fired on no measured document while its twins without the join fire.
- `basis`: The [handback-rows checkpoint](sources/model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23), rows `sa1`–`sa4`, `sv1`–`sv9`, `sb1`–`sb6`, `sh1`–`sh10`, `sd1`, `sd2`, `sc1`–`sc6`, `se1`–`se4`, `sf1`–`sf3`, `sg1`–`sg13`, `pd1`–`pd4` and the `k0607f` run, and the [nested capacity checkpoint](sources/model-structure-and-declaration-probes.md#src-nested-join-capacity), the `c5`, `c6` and `g` runs, measured locally 2026-10-23, Kernel 30.8.1, at the measurement pin `09f1352e5`, replayed by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean) and the [group-target locks](../A12Kernel/Reference/Dm/GroupTargetLocks.lean).
- `acceptance`: Reconcile the classes of those rows, the `c5` and `c6` firings with their unmatched side's references, the `twoSlots` and `wraps` occupancy, the `f1`–`f4` firings, and the silence of `g1` beside the firings of `g2`–`g5`. The runtime of value slots, standalone `ValueAsDate`, keyed group lists and filled-count pairs other than `> 0` and `>= 2`, other constants and why the keyed target beside a join never fires are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-24-01"></a>
### SPEC-2026-10-24-01 — built-in findings report their own cell, an operand-poisoned instance reports nothing, and admission does not decide satisfiability

- `status`: pending
- `canonical`: [spec/02 §B.1](../spec/02-logic-and-formal-errors.md#b1-what-a-formal-error-is) and [spec/09 §3](../spec/09-computations.md).
- `delta`: A formal finding, `mandatoryField` and `uniqueIndex` each report one message at the finding's pointer, `referenced` exactly that pointer, VALUE with an empty `fillToFix` except `mandatoryField`, which is OMISSION with its own pointer there, in validation and in computation's formal-operand channel; a computation instance aborted by a formally invalid stored operand, and its poisoned dependents, emit no message and are no erroneous instances, the operand's finding being the only report; and a self-contradictory condition is admitted without a diagnostic. The K21 consumer readbacks found these three outputs unstated.
- `basis`: The [K21 checkpoint](sources/consumer-readiness-probes.md#src-consumer-readiness-k21): its `builtin-channels` survey of every retained artifact on 2026-10-24, its `computation` row `badSrc` and its `candidates` rows `a1` and `a5`, measured locally 2026-10-23, Kernel 30.8.1, at the measurement pin `09f1352e5`, the candidates replayed by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean).
- `acceptance`: Reconcile the channel shape of those messages, the empty erroneous-instance channel and single operand finding of `badSrc`, and the admission of `a1` and `a5`. Target failures other than a formally invalid stored operand, such as division by zero, keep their existing account; do not extend the poison sentence to them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
