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

Six entries are `handed-off`, carried to a12-dmkits by the owner on 2026-10-23, and one is `pending`. The 16 terminal receipts closed at the [October 18 response](sources/inbound-handbacks.md#src-inbound-2026-10-18), fourteen `accepted` and two `answered`, remain in [the ledger at `bf2216b6`](https://github.com/mbackschat/a12-kernel-lean/blob/bf2216b69d5a3bbaefe182b76271ddf8d6b27ecf/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).

<a id="spec-2026-10-22-01"></a>
### SPEC-2026-10-22-01 — a bracketed read inside `Length` or a day difference is a token defect

- `status`: handed-off
- `canonical`: [spec/12 §3](../spec/12-concrete-syntax.md#3-the-condition-and-operation-grammar-sketch).
- `delta`: `Length` names its field as an entity, and `DifferenceInDays` takes a bare path, so a bracketed read in either slot draws `MVK_UNEXPECTED_TOKEN` rather than being read as the field's value; `Length(/Order/Note)` is the admitted String control. Other entity-typed slots, the other differences included, are unmeasured.
- `basis`: [condition-class checkpoint](sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection), rows `O08` (`Length([/Order/Qty])`), `O09` (`Length([/Order/Note])`) and `O09b`, measured locally 2026-10-01, Kernel 30.8.1, replayed by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean); the [yearless-anchor checkpoint](sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year)'s `instrument` row `DifferenceInDays([/G/F], …)`, measured locally 2026-09-04.
- `acceptance`: Reconcile the class of the three bracketed rows, and the `Length([F]) > 5` spelling of [KF34](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf34) whose rule read it names. Do not claim a class for a relative bracketed read or for another entity-typed slot.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-22-02"></a>
### SPEC-2026-10-22-02 — the document conversion drops a member the model does not declare

- `status`: handed-off
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands).
- `delta`: Kernel Document JSON conversion drops an undeclared string or object member of a fixed group and an undeclared string key inside a repeatable row, so the document validates exactly as the one without them. Other JSON kinds, an object inside a row, a member at the document root and the conversion's notifications for a dropped member are unmeasured.
- `basis`: [undeclared-member checkpoint](sources/domain-ingestion-probes.md#src-undeclared-document-members), rows `f-extra` against `f-full`, measured locally 2026-10-22, Kernel 30.8.1, both strategies, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile the interpreter's document reader with the three dropped shapes. Do not claim an outcome for an undeclared array, a scalar of another JSON kind, an object inside a row, a member at the document root or the deserializer's notification channel.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-22-03"></a>
### SPEC-2026-10-22-03 — a repeatable or parallel rule reports a reached unregistered name at its first error address

- `status`: handed-off
- `canonical`: [spec/11 §14](../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).
- `delta`: The VALUE report of a reached unregistered custom condition ([KF52](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf52)) stands once, at the iterator's first error address, on a repeatable, root-iterated and parallel rule, even when a later row reached the name. On a repeatable rule earlier firing rows keep their messages and later rows are not evaluated. A partial call's iterator starts where its relevant set's error-field selectors, compressed into one, start it: at their one row, or at the first row when they name different rows. A parallel rule's first address is the join's first row, an unmatched one with its `UNKNOWN` coordinate included; its later rows and earlier firings are unmeasured.
- `basis`: [call checkpoint](sources/model-structure-and-declaration-probes.md#src-custom-condition-calls), rules `M01`–`M04` and `E01` of `request-missing`, rows `m-claim`, `m-row3` and `m-keep`, and of `request-review`, rows `r1-rows23`, `r2-order` and `r3-supply-first`, measured locally 2026-10-22, Kernel 30.8.1, both strategies, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile the address, the single report per rule, the compressed partial start and the retained earlier firing for the five rules. Do not claim an outcome under a repeatable outer row of a parallel rule, for its later joined rows or for a parallel rule with an earlier firing row.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-22-04"></a>
### SPEC-2026-10-22-04 — a custom-condition name is reached by the rule's two evaluation passes

- `status`: handed-off
- `canonical`: [spec/11 §14](../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).
- `delta`: Replaces "a guard that decides the condition first leaves the lookup unreached". A false conjunct ahead of the name in an `And` leaves it unreached, and so does a disjunct already true when the tree needs no classification pass; a holding tree that needs one evaluates again past that disjunct, so `FieldNotFilled(Stage) Or CustomCondition X` reaches the name with `Stage` empty or filled. In a parallel rule a field pair whose fill quantifier does not fire on a joined row ends the `And` there.
- `basis`: [call checkpoint](sources/model-structure-and-declaration-probes.md#src-custom-condition-calls), rule `M06` in rows `r1-rows23` and `r2-order`, `E01` in `m-claim` and `M04` in `r1-rows23`, measured locally 2026-10-22, Kernel 30.8.1, both strategies, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile reach of the unregistered name for the three rules on both channels. Do not claim an outcome for a classification pass of a parallel rule or for a callback that throws.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-22-05"></a>
### SPEC-2026-10-22-05 — the iteration guard skips a level and judges comparisons by three constant rules

- `status`: handed-off
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands).
- `delta`: The twice-repeating keyed licence exempts the group's level from the guard rather than licensing one negative, so it covers every leaf there and a negative inside such a group is still judged at an enclosing level. A comparison is refused by a count below a positive constant on either side, a value operation equal to a constant converting to zero, or a mix of iterating and fixed reads against any constant, with brackets transparent. `CurrentRepetition` is an unguarded leaf, the three value-list quantifiers have their own rules, a `$` read inside a filter references no level, and an unreferenced error field answers ahead of the guard.
- `basis`: [K04 checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04), rows `e01`–`e11`, `u01`–`u30`, `a01`–`a06` and `o01`–`o03`, measured locally 2026-10-22, Kernel 30.8.1, at the measurement pin `09f1352e5`; the constant and operator rows of the [October 22b peer rows](sources/inbound-handbacks.md#src-inbound-2026-10-22b).
- `acceptance`: Reconcile the guard's outcome on those rows. The clause's source-read extensions, the nested `CurrentRepetition` and filter-read rules, a non-constant side and an H model's exemption are unmeasured; do not claim them as measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

### SPEC-2026-10-23-01 — selections bind and weigh alike for fields and groups, and only a join's own group joins its error field

- `status`: handed-off
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) and its parallel-iteration constraints.
- `delta`: Beyond the [October 22c rows](sources/inbound-handbacks.md#src-inbound-2026-10-22c): the error-field iteration class follows the parallel iteration, so beside an unkeyed group a starred-only error field draws `MVK_NO_WILDCARD`; a presence of a group above the joined one does not join the error field, one of the joined group does; a field-keyed field or group selection is admitted with its key read from the iterated row and guards that row as a positive, while `NoFieldFilled` beside a field-keyed selection refuses; a negative field or group selection alone fails its parent's level; a constant group selection binds below an unkeyed iterated row; and a constant selection of the iterated group's own field is one independent slot in the field-fill quantifiers and `FieldValuesNotUnique`.
- `basis`: [Binding checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04), discriminator rows `d1`, `d2`, `d5`, `d6` and the `review` rows `v1`–`v18`, measured locally 2026-10-23, Kernel 30.8.1, at the measurement pin `09f1352e5`.
- `acceptance`: Reconcile the class and admission of those rows. The runtime of a selection read at the rule's row is unmeasured; do not claim it as measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-23-02"></a>
### SPEC-2026-10-23-02 — a rule may report on a group, whose own level is unindexed, and a blank root runs a negative over the exempt keyed level

- `status`: pending
- `canonical`: [spec/07 §1](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands).
- `delta`: A non-root group error entity fires at its own pointer once per iterated row above it; a repeating group's own level is pinned to its first row, where field reads and fixed subgroup presence read that row while the group's own presence reads every row. The group is referenced only by its own or a containing group's presence, only the levels above it need a binding reference, and the guard still judges its own level. Separately, a blank nonrepeatable root runs a negative over a twice-repeating keyed group at every declared row, for field and group targets alike.
- `basis`: [Group-target checkpoint](sources/model-structure-and-declaration-probes.md#src-group-target-nested-join), rows `E1`–`E6`, `t0`–`t8`, `v1`–`v5`, and the [K04 checkpoint](sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04) rows `g01`–`g06`, measured locally 2026-10-22 and 2026-10-23, Kernel 30.8.1, replayed by the [group-target locks](../A12Kernel/Reference/Dm/GroupTargetLocks.lean), the [guard locks](../A12Kernel/Reference/Dm/IterationGuardLocks.lean) and `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the pointer, message type, references and admission of those rows, and the blank-root firings of `E3`, `v1` and `v2`. Do not claim the blank-root dispatch for other conditions or roots, partial validation of a group target, or a root group target.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
