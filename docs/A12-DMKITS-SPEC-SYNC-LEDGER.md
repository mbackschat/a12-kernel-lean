# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns open `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. Terminal receipts leave this queue after their useful live facts are preserved in the canonical spec, source or gap owner.

The terminal receipts retired on 2026-10-10 remain in [the ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), the accepted receipts retired on 2026-10-28 remain in [the ledger at `0a56df16`](https://github.com/mbackschat/a12-kernel-lean/blob/0a56df1698fe9a9f2d64bad3c9ed22a728c9121c/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), and the answered, rejected and superseded receipts retired later that day remain in [the ledger at `5868c3d2`](https://github.com/mbackschat/a12-kernel-lean/blob/5868c3d270f6b4c87c5a8f98ba51d07adcbd0a7c/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), all under their stable entry anchors. Earlier deleted receipts remain in [the historical ledger](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md) and [the accepted receipts through 2026-09-24](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md) at `a050f150`. Recover any exact receipt with `git show <revision>:<path>` and find its stable ID; retired IDs are never reused.

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

<a id="spec-2026-10-28-01"></a>
### SPEC-2026-10-28-01 — A `−1` maximum leaves the static scale unknown on every carrier measured

- `status`: accepted
- `canonical`: [spec/04 §1.1](../spec/04-numbers-and-decimals.md#11-static-scale-and-the-multiplicative-constant-capability).
- `delta`: Extends the measured refusal of a `−1`-maximum field at `==` and as a computation source or target from fixed-group rules to minimum 0, `BaseYear`, repeatable rows, `Having`, `$`-correlated and key-joined reads, `MaxValue`, `Sum`, `Min`, `FirstFilledValue` and repeatable targets fed a copy, a constant, `Length` or `NumberOfFilledGroups`, with ordering admitted and the waiver admitting a row copy. `Sum` and one-operand `MaxValue` over a scale-2 field are admitted against `1.00`.
- `basis`: the [unknown-scale and root-index batch](sources/static-admission-and-class-probes.md#src-unknown-scale-and-root-index), 91 rows measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`, each family with a known-scale control.
- `acceptance`: Reconcile the carrier list; a `−1` maximum with no declared minimum stays unmeasured, so do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa2677f7dbc20f198f3b063947fb2da3d4f5cc04`.
- `disposition`: Reconciles the carrier list: the 91 static rows rerun unchanged with identical input hashes and every verdict reproduced, and the peer checker now names A12's class on `ue7` and `ue9`, where it had typed no `$`-marked comparison side (KF625, KF487). A `−1` maximum with no declared minimum stays unclaimed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28).

<a id="spec-2026-10-28-02"></a>
### SPEC-2026-10-28-02 — A key over an index nominated on the root or a fixed group is admitted and selects that group's one instance

- `status`: accepted
- `canonical`: [spec/08 §4](../spec/08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-), the key-and-index-group paragraph.
- `delta`: Replaces "a root- or fixed-indexed chain that crosses no repetition is unmeasured" with its admission on a direct read, a presence read, a starred `Sum` and a row-bound read, and with the runtime selection: an equal stored index reads as unkeyed, a different one reads empty, an empty one fires neither the condition nor its negation and draws `mandatoryField`.
- `basis`: the [unknown-scale and root-index batch](sources/static-admission-and-class-probes.md#src-unknown-scale-and-root-index) (`ug` rows) and the [runtime open-cells probe](sources/model-structure-and-declaration-probes.md#src-runtime-open-cells) (`ixroot-*`, `ixfix-*`), measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`, both engines agreeing.
- `acceptance`: Reconcile the static and runtime rows; reads through a further keyed level and message parameters over such an index are unmeasured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa2677f7dbc20f198f3b063947fb2da3d4f5cc04`.
- `disposition`: Reconciles the `ug`, `ixroot-*` and `ixfix-*` rows statically and three-engine at runtime (KF478). The peer also measured that a level below the key which the rule's iteration binds names the firing row in `referenced`, on a root, fixed-group and repeatable-group index (KF522, IF445); Lean refuses that read below the key, recorded at [SG9](gaps/paths-and-groups.md#gap-sg9). [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28).

<a id="spec-2026-10-28-03"></a>
### SPEC-2026-10-28-03 — A nominated non-repeatable index field reaches the computation prepass and draws nothing without content

- `status`: accepted
- `canonical`: [spec/03 B.4](../spec/03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique).
- `delta`: Adds that a present group holding nothing, or only the nominated field as `null`, draws no `mandatoryField`, and that a computation reading the empty nominated field of a group holding other content reports `mandatoryField` among its operand errors and stores nothing.
- `basis`: the [runtime open-cells probe](sources/model-structure-and-declaration-probes.md#src-runtime-open-cells) (`hold-*` rows), measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`.
- `acceptance`: Reconcile the `hold-*` rows; the third state the finding then puts the cell in is SPEC-2026-10-28-06's.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa2677f7dbc20f198f3b063947fb2da3d4f5cc04`.
- `disposition`: Reconciles the `hold-*` rows three-engine; the peer interpreter's prepass now treats the empty nominated key as required only while its group holds content (KF638, IF446). Its lock pins stored values and fired sets, not the operand-error report, which the rerun reproduced. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28).

<a id="spec-2026-10-28-04"></a>
### SPEC-2026-10-28-04 — An arithmetic dependent of an instance skipped at its own row's key is cleared

- `status`: accepted
- `canonical`: [spec/09 §5.4](../spec/09-computations.md#54-parallel-joins).
- `delta`: Moves the dependents of an instance skipped at its own row's duplicated key from unmeasured to cleared on an arithmetic dependent, and records that String and Enumeration copies and a Date shift of a skipped target clear without separating poison from emptiness.
- `basis`: the [runtime open-cells probe](sources/model-structure-and-declaration-probes.md#src-runtime-open-cells) (`join-*` rows), measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`.
- `acceptance`: Reconcile the `join-own-duplicate` row; dependents of an over-capacity skip stay unmeasured, since the probe's over-capacity row also duplicates keys.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa2677f7dbc20f198f3b063947fb2da3d4f5cc04`.
- `disposition`: Reconciles the `join-own-duplicate` and `join-own-unmatched` rows three-engine (KF630). The String, Enumeration and Date-shift dependents are reproduced by the rerun but not locked upstream; the over-capacity skip stays unclaimed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28).

<a id="spec-2026-10-28-05"></a>
### SPEC-2026-10-28-05 — Operand-list `Min`/`Max`, `Abs`, the value field forms, `Length` and a filtered count are typed as their polarity rows state

- `status`: accepted
- `canonical`: [spec/10 §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing).
- `delta`: Moves the operand-list `Min`/`Max` and `Abs` rows, the `AbsValue` and `RoundAccountingValue` field forms, the `Length` seed and the headroom arm of `filled shrink` from unmeasured to measured, with the separating `Max` row firing VALUE where an either-operand shrink would fire OMISSION.
- `basis`: the [runtime open-cells probe](sources/model-structure-and-declaration-probes.md#src-runtime-open-cells) (`fill-*` rows), measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`.
- `acceptance`: Reconcile the `fill-*` rows against the table; more than two operand-list operands stay unmeasured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa2677f7dbc20f198f3b063947fb2da3d4f5cc04`.
- `disposition`: Reconciles every `fill-*` row three-engine, including the separating `Max` row (KF639). More than two operand-list operands stay unclaimed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28).

<a id="spec-2026-10-28-06"></a>
### SPEC-2026-10-28-06 — An empty or duplicated index cell is unknown to authored rules and poisons computation

- `status`: accepted
- `canonical`: [spec/03 B.4](../spec/03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique), with its consequences in [spec/02 B.3](../spec/02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state), the [spec/03 B.2](../spec/03-empty-and-required.md#b2-required-manifests-as-a-formal-error) asymmetry and the prepass clause of [spec/09 §3.3](../spec/09-computations.md#33-what-compute-reports).
- `delta`: Adds the index field's generated mandatory finding as a third-state producer that, unlike the required checkbox's, is not validation-scoped: an authored rule reads an empty nominated or repeatable key and both participants of a duplicated key as unknown, and a computation reading the empty key clears its target while its generated rule stays silent.
- `basis`: the [runtime open-cells probe](sources/model-structure-and-declaration-probes.md#src-runtime-open-cells) (`q-*` rows of `request-rules.json`, `hold-key-empty-seeded` of `request-prepass.json`), measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`.
- `acceptance`: Reconcile the `q-*` and `hold-key-empty-seeded` rows; partial validation's reads of these cells are not covered.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa2677f7dbc20f198f3b063947fb2da3d4f5cc04`.
- `disposition`: Reconciles the `q-*` rows and `hold-key-empty-seeded` three-engine; the peer interpreter already agreed (KF638). Partial validation of these cells stays unclaimed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28).

<a id="spec-2026-10-28-07"></a>
### SPEC-2026-10-28-07 — A key over a repeatable index reads and references a lower level the rule iterates at the rule's own row

- `status`: accepted
- `canonical`: [spec/08 §4.1](../spec/08-paths-and-references.md#41-what-a-semantic-index-read-yields), the paragraph on a repeatable level below the index group, and [spec/07 §1.8](../spec/07-repetition-and-iteration.md#18-the-negative-condition-guard), the paragraph on a selection read below the selected row.
- `delta`: Adds the value and static scope to KF522's references and KF475's starred-level class: from `Slots` below the repeatable `Bins` index, `[Qty For "b"]` reads the selected bin at the firing slot, from `Cells` at its slot and cell rows, a slot the selected bin lacks yields a clean no-match's values and verdicts on every route measured while its references keep the matched bin, a keyed group at a bound lower level is admitted, an unstarred unbound lower level draws `MVK_NO_WILDCARD` in rules and computations, and the read guards and references the error field at the rule's lower rows but never at the selected level. A level the error field reaches only through its key and no other read iterates is not iterated, so such a rule runs inside the selected row alone and a key selecting no row fires nothing, while an unkeyed read of the error field beside it iterates every row again.
- `basis`: the [below-key selection](sources/model-structure-and-declaration-probes.md#src-below-key-selection), [below-key routes](sources/model-structure-and-declaration-probes.md#src-below-key-routes) and [below-key error scope](sources/model-structure-and-declaration-probes.md#src-below-key-error-scope) probes, 20 runtime documents and 60 static rows measured locally 2026-10-28, Kernel 30.8.1, at the measurement pin `08b0d6499`, both strategies agreeing.
- `acceptance`: Reconcile the `bk-*` and `p3-*` runtime rows, the error-scope capture's `N2`, `N2T`, `E2`, `E2T`, `E5` and `E5T` firings, and the `t`, `g`, `m`, `n`, `e` and `q` static rows; a missing lower row under a compromised column, partial calls leaving it outside relevance, Time and DateTime targets, a dynamic key beside a rule whose key fixes its level, differently keyed selections of the error field and a runtime failure's address in such a rule are unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `61378d4563b260b8152a39203bfe04e633d66995`.
- `disposition`: Reconciles the `bk-*` and `p3-*` runtime rows, the error-scope firings and the `t`, `g`, `m`, `n`, `e` and `q` static rows: the 60 static rows rerun with the same verdict and the five runtime requests with no difference. The peer checker now runs every single-value operand gate on a keyed star below the index group (KF476, `q4`), and its interpreter reads that star at the firing row's lower coordinates and compares a keyed field's selected cell in `FieldValuesNotUnique` (KF475, IF449, IF450). The listed unmeasured cases stay unclaimed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28b).

<a id="spec-2026-10-28-08"></a>
### SPEC-2026-10-28-08 — A key over a root or fixed-group index selects that group's one instance in every phase and carrier

- `status`: accepted
- `canonical`: [spec/08 §4](../spec/08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-), the index-group sentence and the runtime paragraph on a key over a root or fixed-group index with its four bullets, and [spec/11 A.7](../spec/11-messages-and-custom.md#a7-semantic-index-keys), the paragraph on an index on the root or a fixed group.
- `delta`: The index group is the one indexed group on the chain of either kind, a second one drawing `MVK_MULTIPLE_INDEX_FIELDS` ahead of `MVK_NO_WILDCARD`. At runtime the one instance is selected in validation, partial validation and computation, a key field reading as a literal does. Every keyed carrier measured reads a no-match as an absent payload, a fixed indexed group below a repeatable row selects per row, and a no-match's references write `-5` at the index group and `[1]` elsewhere. `GroupFilled(/Root For "X")` references only the error field and the index field, and a keyed name parameter beside the same keyed read is admitted and renders the field's name, the unkeyed one drawing `INVALID_FIELD`.
- `basis`: the [single-instance key probe](sources/model-structure-and-declaration-probes.md#src-single-instance-key), 10 runtime documents over two models and 15 static rows measured locally 2026-10-28, and the `ix*` rows of the [runtime open-cells probe](sources/model-structure-and-declaration-probes.md#src-runtime-open-cells), Kernel 30.8.1, at the measurement pin `08b0d6499`, both strategies agreeing.
- `acceptance`: Reconcile the `a-*` documents of both requests, rows `t1`–`t6`, `m1`–`m4` and `x1`–`x5`, and the `ix*` references. Such a key inside a filter, with a value or category message suffix, and below a repeatable row over its capacity, is unmeasured, so do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `61378d4563b260b8152a39203bfe04e633d66995`.
- `disposition`: Reconciles the `a-*` documents, rows `t1`–`t6`, `m1`–`m4` and `x1`–`x5`, and the `ix*` references: the 15 static rows rerun with the same verdict, and both runtime requests and the open-cells `ix*` rows with no difference. The peer interpreter now references only the index field for a keyed root and lists an empty single-instance index field among a computation's operand errors (KF478, IF447, IF448). The listed unmeasured cases stay unclaimed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-28b).

<a id="spec-2026-10-29-01"></a>
### SPEC-2026-10-29-01 — Type definitions are walked in case-sensitive id order, repeated Enumeration values follow no stated order, and the locale grammar has two quirks

- `status`: accepted
- `canonical`: [spec/01 §1.1](../spec/01-data-model.md#member-binding), the locale-parser bullets, [spec/01 §1.2](../spec/01-data-model.md#the-six-rules), the sentence on the walk's id order, and [spec/01 §1.3](../spec/01-data-model.md#enumeration-declarations), the bullet on block 6's order.
- `delta`: Refines KF647's id order as case-sensitive, `Beta`, `Zeta`, `alpha`. Records that block 6's repeated values follow neither declaration nor second-occurrence order on five rows, and alphabetical order on one, so no order is stated. States the locale grammar beyond KF290's spellings: `-` separating only without `_`, a variant after a second separator with the country optional, a spelling opening with its separator, a three-digit area after any first segment of a two-segment spelling, a bare uppercase pair parsing only when the JDK lists it as a country, and `zh_Hans_CN` and a padded spelling refused.
- `basis`: the [basic sentence order](sources/model-structure-and-declaration-probes.md#src-basic-sentence-order) probe, two `model check` runs measured locally 2026-10-29, Kernel 30.8.1, at the measurement pin `08b0d6499`, and the [locale grammar](sources/model-structure-and-declaration-probes.md#src-locale-spelling-grammar), the commons-lang3 3.20.0 jar the measurement launcher ships, run on 2,410 spellings under JDK 21 and 25 the same day.
- `acceptance`: Reconcile the `order_DM` and `order2_DM` rows and the locale grammar; ids beyond ASCII and the country table of another JDK are unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `3dd931e4db5b63ac08c1a0a927989bb3b6b4b21e`.
- `disposition`: Reconciles both parts: `order_DM` and `order2_DM` rerun through the Kernel's own reader and builder give the type-definition order and all four repeated-value orders unchanged, and all 2,410 spellings as a label entry build a model exactly where the jar parses. Two inbound extensions, a Latin-1 id row and the header locale code's tag demands and locale identity, enter spec/01 without a new entry. The mechanism wording is corrected to a fill at every occurrence after the first (KF647, KF649, KF290). [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-29a).

<a id="spec-2026-10-29-02"></a>
### SPEC-2026-10-29-02 — A header locale code needs no well-formed language tag; an empty language and a repeated locale fail the build

- `status`: accepted
- `canonical`: [spec/01 §1.1](../spec/01-data-model.md#member-binding), the header locale code paragraph and its six bullets, and the two header rows of [spec/01 §1.2](../spec/01-data-model.md#defects-that-leave-no-model)'s no-model table.
- `delta`: Corrects the header part `SPEC-2026-10-29-01`'s disposition took from KF649, its demand of a well-formed language tag: beside `fr_CH` the Kernel admits all 21 tag-refused codes of the October 29a letter, beside `en_US` the 20 other than `en_US_abcdefghi`, which it admits beside `de_DE` too, and the refusal those rows record is thrown by dmtool's own model index after the Kernel's gate has passed. An empty language and two codes naming one locale fail the build, two distinct locales with one JDK language tag draw `MVK_SUPP_LANGUAGES_DUPLICATE`, as `und` beside `ée` and `en_US` beside `en_US_abcdefghi` do where `en_US` beside `en_US_abcd` does not, and a bare-text `locales` entry is judged as an object entry is.
- `basis`: the [header locale codes](sources/model-structure-and-declaration-probes.md#src-header-locale-codes) probe, 109 `model check` runs measured locally 2026-10-29, Kernel 30.8.1, at the measurement pin `08b0d6499`, each thrown exception classified by its stack.
- `acceptance`: Reconcile every row of the projection through a route whose Kernel verdict no tool reader after the gate can replace. The rule stating `MVK_SUPP_LANGUAGES_DUPLICATE`, the order of two such tags and the locales the JDK tags specially are unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `22c198c3a4186486446acbeea0eade6c7fdb3c07`.
- `disposition`: Reconciled through the Kernel gate alone, with no dmtool reader after it: the letter reports all 109 projection rows unchanged, and its committed lock's 38 header rows and duplicate-tag row agree with the retained projection. The header half of the October 29a letter is withdrawn, and the peer's checker stays silent on `MVK_SUPP_LANGUAGES_DUPLICATE` (DG163). [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-29b).

<a id="spec-2026-10-29-03"></a>
### SPEC-2026-10-29-03 — A non-repeatable group context beneath a starred group's star carries 1, not the wildcard

- `status`: accepted
- `canonical`: [spec/01 §3.1](../spec/01-data-model.md#address-coordinates), the paragraph on one rule deciding a level's coordinate.
- `delta`: Removes the exception, adopted 2026-08-04 from a12-dmkits `b5aba1ec`, that beneath a starred group's star every reopened group-context part is wildcarded including a non-repeatable descendant group context. Over a repeatable `Left` holding the fixed group `Seal`, `NoGroupFilled(Left*/Seal)` and `NoGroupFilled(Left*, Left*)` reference `/Form[1]/Left[0]/Seal[1]/M`, so such a part follows the general rule and carries `1`; measured on both presence predicates one fixed level beneath the star, deeper nesting and other operators unmeasured.
- `basis`: the retained [mixed group predicates](sources/group-count-topology.md#src-mixed-group-predicates) capture, Kernel 30.8.1, measured locally 2026-10-10 and read for this coordinate 2026-10-29, with no `Seal[0]` among its pointers; the Lean replay agrees on all 2,178 of its reference comparisons. The disagreement was found as question Q-003 of the U02 cold evaluator, in `reports/QUESTIONS.md` of `../a12-rust-interpreter-u02` at its commit `0cb1469`. a12-dmkits' `GroupStarValueAggregateDiffTest` at `f73341971` expands a starred group over `Extras`, a repeatable descendant, which does not separate the non-repeatable case.
- `acceptance`: Reconcile the `LNone` and `TNone` rows of that capture and any statement of the exception in a12-dmkits' own record; `b5aba1ec` no longer resolves there, so a witness for the exception on another operand form, if one exists, is the evidence that would reopen it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `eaa6faf0c6619e8aa61b2de16cb4c5af6648b42d`.
- `disposition`: Reconciled: the peer's Kernel gate reproduces the capture's 99 rows on both strategies with no `Seal[0]`, its interpreter differential agrees on all 198 calls, and its own domain, a fixed `Adjuster` beneath a repeatable `Claims`, gives `Claims[0]` beside `Adjuster[1]` under both presence predicates. KF183 is amended to keep the wildcard at the starred level. No statement of the exception was found in its record, and `b5aba1ec` does not resolve there either. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-29c).

<a id="spec-2026-10-29-04"></a>
### SPEC-2026-10-29-04 — A computation's implicit message lists fillToFix by the ordinary omission projection, withholding positive presence

- `status`: accepted
- `canonical`: [spec/09 §6](../spec/09-computations.md#6-the-implicit-validation-rule-precisely), the `fillToFix` bullet of the message's type and channels.
- `delta`: Replaces the rule that an implicit message's `fillToFix` is all of `referenced` or none of it with the ordinary rule arm's omission projection of the generated condition: empty on VALUE, and on OMISSION the pointers its ordinary operands contribute, the computed target always among them. A field read only through positive presence is referenced but not listed: a common precondition `FieldFilled(Gate)`, a positive field-fill quantifier's field operands and a `GroupFilled` precondition's group fields are withheld, while a field the condition also reads ordinarily, such as a `Having` filter's field, an operation operand or a parallel index key, stays listed, so the set is a proper subset of `referenced`.
- `basis`: the retained [empty pattern execution](sources/computation-scheduling-probes.md#src-empty-pattern-execution) (`FilteredComp`, row `reached-filled`), [field-fill computation guards](sources/computation-scheduling-probes.md#src-field-fill-computation-guards) extension capture `field-fill-family-2026-10-04` (`AF2Comp`) and [parallel instance leaves](sources/key-join-and-parallel-probes.md#src-parallel-instance-leaves) (`Cg02`) captures, Kernel 30.8.1, each OMISSION message's `fillToFix` a proper subset of its `referenced` set as read 2026-10-29; the Lean replay, which lowers the computation to its generated rule, matches them. The U02 cold evaluator's question Q-004, in `reports/QUESTIONS.md` of `../a12-rust-interpreter-u02` at its commit `d2dbe1a`, found the disagreement; it was introduced at `774f375` and is present at `d2dbe1a`.
- `acceptance`: Reconcile those three messages and any all-or-nothing statement of the projection in a12-dmkits' own record. Whether the generated condition's upward count pruning matches an authored rule's is not separately measured, so do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `510e60321018c917bb4b507d0ca5dd23b937991e`.
- `disposition`: Reconciled: the peer's Kernel gate equals the four retained artifacts on all 2,732 messages, `fillToFix` included, and its interpreter differential passes on all four requests. Its record's all-or-nothing statement is corrected in place, and it measured the count pruning the acceptance left unclaimed: on one fixed group of Number fields an upward `NumberOfFilledFields(…) > 0` precondition withholds its operands as an authored rule's does. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-29e).

<a id="spec-2026-10-29-05"></a>
### SPEC-2026-10-29-05 — The message cache's population, identifier hash, bucket and capacity decide a duplicated key's winner

- `status`: accepted
- `canonical`: [spec/08 §4.3](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages), the population and hash paragraph after the OpenJDK 21 profile.
- `delta`: States the derivation the clause left to its source account: which group rows and cells enter the temporary cache, the model-wide internal names with their numeric suffixes, the coordinate vector, the identifier hash as a 31-polynomial over the coordinates and the name's UTF-16 units, the bucket `(h xor (h >>> 16)) mod capacity`, the load capacity with its early collision growth, and the winner rule that leaves a query undecided unless every possible capacity agrees.
- `basis`: the [cache population order](sources/message-and-pointer-probes.md#src-message-cache-population-order) checkpoint's identifier and host source reading with its independent prediction of four observed winners, and the Lean replay of the retained `message-cache-topology-2026-10-10` capture, matching all 1,122 comparisons, and of `message-cache-collision-2026-10-10`, matching 60, leaving 54 host-order comparisons undecided and 10 rows with no single Kernel observation, 2026-10-29. The U02 cold evaluator's question Q-005, at its commit `73d8b84`, found the gap.
- `acceptance`: Reconcile the derivation against both captures. The runtime vendor, other capacities and tree histories remain unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `510e60321018c917bb4b507d0ca5dd23b937991e`.
- `disposition`: Reconciled: the peer's Kernel gate equals both topology artifacts on all 554 messages, and the collision capture differs only on 16 messages of 14 identical-input rows, which select either row on its host too. A replay written from the clause's prose alone agrees on all 96 full-validation `Ref*` messages it ran, while dropping the hash's trailing term, the load's plus one or the spread each loses agreement. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-29e).

<a id="spec-2026-10-29-06"></a>
### SPEC-2026-10-29-06 — A model written with a check-only frame shape is not evaluated on the runtime route, so an evaluator refuses it

- `status`: accepted
- `canonical`: [spec/01 §1.1](../spec/01-data-model.md#member-binding), the frame-binding paragraph's evaluation bullet.
- `delta`: Adds that a model lacking `header.modelVersion` or `content.modelInfo`, with `header.locales` absent or `null`, or with a `null` supported character, which builds and fails its consistency check without a class, is not evaluated on the measured runtime route, because that route checks a model before evaluating it; an evaluator refuses such a model rather than evaluating the built one. The spec states the Kernel's validation entry points as unmeasured.
- `basis`: the retained [model frame check route](sources/model-structure-and-declaration-probes.md#src-model-frame-check-route) capture, Kernel 30.8.1, measured locally 2026-10-29: each of the four shapes exits before any engine evaluates, at the probe's consistency gate, while the unchanged control evaluates. The frame table itself is a12-dmkits' KF650, adopted as [inbound provenance](sources/inbound-handbacks.md#src-inbound-2026-10-29d).
- `acceptance`: Reconcile how the a12-dmkits interpreter treats those four shapes. Whether the Kernel's validation entry points evaluate such a model when called without the check is unobservable on the retained route, so do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `7b6623d6898ea5e4fb8830eec8414510d96a367d`.
- `disposition`: Reconciled on the checked route, with a divergence of the peer's recorded: its interpreter evaluates all four shapes, an open decision on its side. Its runtime measured with no check in front evaluates only the model lacking its version and throws before any rule on the other three, which spec/01 now states as inbound provenance. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-30).

<a id="spec-2026-10-30-01"></a>
### SPEC-2026-10-30-01 — An unsupported condition-language code is refused with no class

- `status`: accepted
- `canonical`: [concrete syntax §12](../spec/12-concrete-syntax.md), the bullet on a model's `conditionLanguage`.
- `delta`: Replaces the statement that a model declaring a code other than `en_US` or `de_DE` is refused by a class no chapter states with its refusal drawing no class for the two measured codes, the class of every other code left unmeasured. Whether the refusal leaves no model or builds and fails the check is not separated by the capture.
- `basis`: the retained [model frame members](sources/model-structure-and-declaration-probes.md#src-model-frame-members) capture, Kernel 30.8.1, measured locally 2026-10-29: `{"code":"zz"}` and `{"code":""}` each draw one codeless error and no class, while `de_DE` and `en_US` parse their own rules. The other unsupported spellings of that grid stop at `dmtool`'s precheck and measure nothing of the Kernel.
- `acceptance`: Reconcile the refusal's class in a12-dmkits' own record. Codes other than the two measured are unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f22972e27b7f376b450ed8b50ea527d05611f525`.
- `disposition`: Reconciled: both codes draw no class, and the peer separated the stage the capture could not, each read and expanded before the check refuses it, both engines refusing it too with no check in front. Its code table shows the language read as a locale, so concrete syntax §12 and the readers now compare locale keys, `de-DE` selecting German, and the member-binding table in [spec/01 §1.1](../spec/01-data-model.md#member-binding) leaves no model on a code the parser refuses, as the peer's KF650 row now states. The precheck row for `{"code":"en_us"}` is the Kernel deserializer's refusal, as the corrected checkpoint records. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-30a).

<a id="spec-2026-10-30-02"></a>
### SPEC-2026-10-30-02 — A yearless field copied into a year-bearing Date target takes the declared Base Year, a month alone completing to the first

- `status`: accepted
- `canonical`: [spec/09 §4](../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape), the bullet on a field source's static component compatibility, with the year-carrier row in [spec/05](../spec/05-dates-and-time.md#where-a-yearless-value-gets-its-year) and the constant scope of the §4.1 Base Year sentence.
- `delta`: Adds the copy direction the clause did not state: a yearless field into a year-bearing Date target is refused `MVK_INVALID_COMPARE_TO_DATE` without a Base Year and admitted with one, whatever the two component sets, and stores the source in the declared Base Year rendered in the target's format, a month-only source completing its day to the first. An absent or malformed source clears the target, a day the Base Year makes unreal included. The §4.1 statement that a Base Year adds nothing to the stored text is narrowed to a constant's store, which it always described.
- `basis`: the retained [yearless direct copy](sources/temporal-constant-and-base-year-probes.md#src-yearless-direct-copy-base-year) capture, Kernel 30.8.1, measured locally 2026-10-30 on both codegen strategies: all twenty pairs of five yearless sources and four year-bearing targets under Base Year 2023, refused without one, where `06-11` stores `2023-06-11`, `11.06.2023`, `2023-06` and `2023`, `06` stores `2023-06-01` and `02-29` clears, and nine of those pairs under Base Year 2024. The `MM-dd` admission confirms the peer's `kf483` row; `kf550` measures the same completion on `FirstFilledValue`.
- `acceptance`: Reconcile the bare-copy store, the month-only completion to the first and the clears in a12-dmkits' own record. DATE_FRAGMENT declarations, partial precision, repeatable carriers and a DateTime target are unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `48ec4bcc5a4117600070be144704869cfc9d5b95`.
- `disposition`: Reconciled with no correction: the peer re-measured all twenty pairs under both Base Years on both strategies and its checker names the refusal on all twenty, agreeing on every row. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-30b).

<a id="spec-2026-10-30-03"></a>
### SPEC-2026-10-30-03 — Two component-omitting Dates of different component sets compare as their own earliest completions

- `status`: pending
- `canonical`: [spec/05 §1](../spec/05-dates-and-time.md#the-temporal-pair-gate), the paragraph after the pair gate on how an admitted pair compares.
- `delta`: Adds the evaluation the pair gate left unstated: each operand completes on its own, a missing month or day to `01` and a missing year from the declared Base Year, an `MM` operand's included, and the completed dates compare; neither operand's component set narrows the other's.
- `basis`: the retained [fragment pair comparison](sources/temporal-constant-and-base-year-probes.md#src-fragment-pair-comparison) capture, Kernel 30.8.1, measured locally 2026-10-30 on both codegen strategies under Base Year 2023: `yyyy-MM` `2023-06` before `MM-dd` `06-11`, `yyyy` `2023` before `2023-06`, `MM` `06` before `06-11` and `07` after it, `2024-06` after `06-11`, and `2023-01`, `01-01`, `01` and `2023` equal. The shared-component reading predicts equality on the first four and is refuted. `kf176` measures the decode against a full-format sibling.
- `acceptance`: Reconcile the clause in a12-dmkits' own record. DATE_FRAGMENT declarations, partial precision, yearless pairs without a Base Year and compact or dotted spellings are unmeasured, so do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.
