# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns open `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. Terminal receipts leave this queue after their useful live facts are preserved in the canonical spec, source or gap owner.

The terminal receipts retired on 2026-10-10 remain in [the ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), the accepted receipts retired on 2026-10-28 remain in [the ledger at `0a56df16`](https://github.com/mbackschat/a12-kernel-lean/blob/0a56df1698fe9a9f2d64bad3c9ed22a728c9121c/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), the answered, rejected and superseded receipts retired later that day remain in [the ledger at `5868c3d2`](https://github.com/mbackschat/a12-kernel-lean/blob/5868c3d270f6b4c87c5a8f98ba51d07adcbd0a7c/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), and the accepted receipts `SPEC-2026-10-28-01` to `SPEC-2026-10-30-10` retired on 2026-10-31 remain in [the ledger at `1f755d54`](https://github.com/mbackschat/a12-kernel-lean/blob/1f755d54874701c9056ef7be93a6ba6005779ad5/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), all under their stable entry anchors. Earlier deleted receipts remain in [the historical ledger](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md) and [the accepted receipts through 2026-09-24](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md) at `a050f150`. Recover any exact receipt with `git show <revision>:<path>` and find its stable ID; retired IDs are never reused.

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

<a id="spec-2026-11-05-03"></a>
### SPEC-2026-11-05-03 — An unmatched parallel side renders as an absent cell in every form, the join's index fields are members, and a joined group's row index is refused beside a condition that fires unmatched

- `status`: accepted
- `canonical`: [spec/11 A.11](../spec/11-messages-and-custom.md#a11-rendering-a-rule-owned-message), the unmatched-side bullet; the membership list's parallel-join bullet; the `$#RootGroup$` paragraph's parallel row.
- `delta`: Beside KF672's value rows: an unmatched side's String index field renders empty, an Enumeration's value and category render empty and a name renders the name. Both sides' index fields are members although the condition text names neither. Beside `FieldsNotCollectivelyFilled` over a field of each joined side, the absolute spelling of either joined group draws `INVALID_USE_OF_ITERATION_PARAM`; the earlier admission beside `FieldFilled` of a field of each side, on another route and model, does not isolate the gate, and which further conditions draw it is stated unmeasured.
- `basis`: the [unmatched-side checkpoint](sources/message-parameter-rendering-probes.md#src-unmatched-parallel-side), `:adapter:kernelProbe` at a12-dmkits `e62c2059d78f896a0b6304891c76c113966cd069`, both strategies agreeing, kernel 31.1.1.
- `acceptance`: a12-dmkits' interpreter renders the checkpoint's `pg` and `pk` rows and its checker admits the `Dept` parameters and gives the two row-index parameters the class, or records why its account differs.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `c7afca597e812de26b0f758653643107b1e072f8`.
- `disposition`: Reconciled in substance on the peer's own carriers: the peer reports reproducing the capture's rows and classes on its kernel probe and its interpreter and checker on `P31_DM`, while its committed locks render the analogues of `pg` and `pk` on a staffing carrier (`UnmatchedParallelValueMessageDiffTest`) and admit the join's index fields and refuse the unproved row tokens on a shop carrier (`CheckerParallelJoinMessageAgreementTest`), its checker reporting no finding on an admitted row with its verdict inconclusive. Its KF675 rows measure the further conditions this entry left unmeasured, and spec/11's [joined-row proof](../spec/11-messages-and-custom.md#the-joined-row-proof) now states them, Lean's template check agreeing on each row it reads. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-11-05c).

<a id="spec-2026-11-05-02"></a>
### SPEC-2026-11-05-02 — A parallel join over an index nomination naming no field of its group draws the index-name class

- `status`: accepted
- `canonical`: [spec/07 §2.2](../spec/07-repetition-and-iteration.md#22-static-gates), the gate table and the paragraph after it.
- `delta`: Adds the level gate `MVK_INDEX_FIELD_INVALID` for an index nomination naming none of its group's children, on either side of the join and on a presence or a value read, where the same rule with the name resolved is admitted; kernel 31.1.1 builds such a model, drawing the nomination's `MVK_INVALID_INDEX_FIELD` beside it. The nomination's effect on the table's other rows and the class's order against the other gates are stated unmeasured.
- `basis`: the [verdict-file pass](sources/kernel-31-calibration-probes.md#src-kernel-31-recapture-verdicts), rows `u1`–`u5`, at a12-dmkits `e62c2059d78f896a0b6304891c76c113966cd069`, kernel 31.1.1.
- `acceptance`: a12-dmkits' checker gives `u1`, `u4` and `u5` the class and admits `u2`, or records why its account differs.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `3f7f6887830a08665e12895db2fb268e96420e80`.
- `disposition`: Reconciled: the peer reports reproducing `u1`–`u5` on its kernel probe from this project's capture, and `CheckerUnresolvedParallelIndexAgreementTest` locks the law in its own domain, its checker now giving the class on the join rows. Two new rows, both groups nominating one undeclared name, on a join and on `RepetitionNotUnique`, separate the name's existence from a disagreement between the names; spec/07 §2.2 states them and Lean's rule check gives both. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-11-05b).

<a id="spec-2026-11-05-01"></a>
### SPEC-2026-11-05-01 — Kernel 31.1.1 settles the rows still derived for it: month and year shifts refuse a clock, gap and overlap landings, the no-instant constant in validation, the version law, null header members, temporal members a body does not declare, empty-pair rendering and further partial skips

- `status`: accepted
- `canonical`: [spec/05](../spec/05-dates-and-time.md) §2.3, §2.4, §2.7, §4.1, §4.2 and §5; [spec/01](../spec/01-data-model.md) §1.1, §1.2 (the version law, the three check-only shapes, the computation target on a rule), §1.3 (the token-less entry) and the no-model table; [spec/07 §3.10](../spec/07-repetition-and-iteration.md#310-sumofterms) and the `Having` failure paragraph; [spec/09](../spec/09-computations.md) the DateTime-constant paragraph; [spec/10 §5.2](../spec/10-validation-and-polarity.md#5-full-vs-partial-validation) step 2; [spec/11](../spec/11-messages-and-custom.md) the empty category name and both empty-pair rules.
- `delta`: Replaces "unmeasured on 31.1.1" with measured rows: `AddMonths` and `AddYears` over `Now` or a DateTime draw `MVK_WRONG_DATE_FORMAT_FOR_OP`; a month or year landing and a stored Date in a gap move forward by the gap; the 1947 overlap takes the earlier offset; a gap date-time constant in validation is the instant one gap later; a no-instant Date or date-time constant fails the rule with VALUE whatever the other operand holds, and clears a seeded computation target; a completed-period count across Berlin's repeated 1916 midnight counts instants (`DifferenceInYears` 0, `DifferenceInMonths` 5 and 1); the DM version law is major 29 with bound `4.0`; the header's `id`, `modelVersion` or `locales`, absent or `null`, fails the build; a computation target on a rule draws the unresolved-target sentence; a root-climbing or `/`-leading target, an `errorMessage` or `modelInfo.name` written as an object, `errorMessage` written `null` and an unreadable error code leave no model on 31.1.1; `datePrecision` and `youngerThan1900Check` beside a kind that does not declare them are passed over; an empty `format` read through the expand route is the default; an empty pair inside a field-owned text renders verbatim; spec/11's rule-group paragraph now records that `$RuleGroup.Vordruckname$` drew `MVK_INTERNAL_ERROR` on 30.8.1 too; an empty category name on a group draws `NO_CATEGORY`; a filtered `MaxValue` and `FieldValuesNotUnique` are skipped in partial validation; a two-star `SumOfTerms` entity and a non-repeatable divisor; a single unlabelled token-less Enumeration entry adds no stored value. Moves the Date message-key, header-locale, group-target and error-target rows of spec/01 and spec/05 to 31.1.1 and deletes the `datePrecision` no-model row.
- `basis`: the [derived-row capture](sources/kernel-31-calibration-probes.md#src-kernel-31-derived-rows) at a12-dmkits `e62c2059d78f896a0b6304891c76c113966cd069`, kernel 31.1.1, and the [31.1.1 re-capture](sources/kernel-31-calibration-probes.md#src-kernel-31-recapture) for the message keys and the temporal members of the declaration batch.
- `acceptance`: a12-dmkits' corpus or checker gives each listed row, `MVK_ERROR_FIELD_NOT_REFERENCED` beside two duplicate ids included, or records why its account differs.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `35a09951fcb0812e7dbfac2292f915e51ad2674e`.
- `disposition`: Reconciled: the peer reports reproducing every row on kernel 31.1.1 from this project's capture, the six runtime artifacts equal with message texts masked, `probeDifferential` `ok` on all 22 comparisons and every rule, model and header-slot row giving the stated class. Its checker now gives `am-now`, `ay-now`, `mc-ct-rule` and `mc-code-bind`, and declines the identity rows as inconclusive by design (its KF654); on the other rows its checker agrees on the verdict only, refusing where A12 refuses and leaving an admitted model inconclusive, so the listed classes, `MVK_ERROR_FIELD_NOT_REFERENCED` beside two duplicate ids included, are met by the peer's kernel reproduction. The `mc-ct-rule` row opened its KF674, and `mc-code-bind` its KF304's `errorCode` row, both adopted inbound. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-11-05b).

<a id="spec-2026-11-04-03"></a>
### SPEC-2026-11-04-03 — The rule-group terminal takes no dotted continuation and is refused as a group in the form-pointer position, and a DateFragment without its format leaves no model

- `status`: accepted
- `canonical`: [spec/11 §A.8](../spec/11-messages-and-custom.md#a8-form-pointers-the-rule-group-terminal-and-the-base-year), the rule-group terminal paragraph; [spec/01 §1.2](../spec/01-data-model.md#defects-that-leave-no-model), the DateFragment row.
- `delta`: Replaces "unmeasured on kernel 31.1.1" with `INVALID_FIELD_IN_PARAMETER` for `$RuleGroup.Vordruckzeile$`, from a root-group rule and two levels down; adds `MVK_UNEXPECTED_TOKEN` for `$RuleGroup.Vordruckname$`, as for `$RuleGroup/Anchor$`; widens the fragment row from an empty `formatOfFragment` to an absent one, a bodiless `DateFragmentType` included.
- `basis`: the re-capture of the retained rule-check and declaration batches at a12-dmkits `e62c2059d78f896a0b6304891c76c113966cd069`, kernel 31.1.1 ([checkpoint](sources/kernel-31-calibration-probes.md#src-kernel-31-recapture)), rows `I01`, `P01`, `P00` and `tb-frag-nobody`.
- `acceptance`: a12-dmkits' checker gives the three message classes and refuses to build the bodiless fragment model, or records why its account differs.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `3f7f6887830a08665e12895db2fb268e96420e80`.
- `disposition`: Reconciled: `CheckerRuleGroupFormLineAgreementTest` and two rows of `CheckerBasicSentenceAgreementTest` reproduce every row on kernel 31.1.1, the peer's checker correcting `$RuleGroup.Vordruckzeile$` from `INVALID_PARAMETER` to `INVALID_FIELD_IN_PARAMETER`; the other rows already agreed. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-11-05b).

<a id="spec-2026-11-04-02"></a>
### SPEC-2026-11-04-02 — A `SumOfTerms` computation's row that divides by zero adds nothing and does not poison the sum

- `status`: accepted
- `canonical`: [spec/07 §3.10](../spec/07-repetition-and-iteration.md#310-sumofterms), the evaluation paragraph.
- `delta`: Replaces "unmeasured" with the rule: in a computation, as in validation, a row whose term divides by zero, including by an empty divisor, adds nothing, and a sum whose only row divides by zero is 0; no outcome is cleared or errored. The same change records three measured scopes that change no rule: spec/10 §5.2 step 2's skip of a filtered `Sum`, `NumberOfFilledFields` and value-list subject, spec/07's `$` read inside a filter that references no leaf, and the `CurrentRepetition` guard row's refusal at an inner level under a skipped keyed outer level.
- `basis`: `:adapter:kernelProbe` at a12-dmkits `e62c2059d78f896a0b6304891c76c113966cd069`, both strategies agreeing, kernel 31.1.1 ([checkpoint](sources/kernel-31-calibration-probes.md#src-first-kernel-31-capture)).
- `acceptance`: a12-dmkits reconciles its account of a `SumOfTerms` computation over a dividing row with the rule, its interpreter computing the checkpoint's four `Total` rows as stated.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `da388eeac1f26c954947c8d9639b78104276e925`.
- `disposition`: Reconciled with no correction: the peer reports re-running this project's capture at a12-dmkits `c8b1ff5ef` to the same four values with `probeDifferential` `ok`, and `SumOfTermsDivisionComputationLawsTest` locks the law in its own domain (`VALUE` 5, 7, 0 and 5, no outcome cleared or errored) on both strategies and its interpreter; its KF670 gains the computed row. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-11-05).

<a id="spec-2026-11-04-01"></a>
### SPEC-2026-11-04-01 — The wholly relevant group extent never folds a capacity-one level, and a declared empty sub-group keeps its parent from being wholly relevant

- `status`: accepted
- `canonical`: [spec/10 §5.6](../spec/10-validation-and-polarity.md#56-group-presence-and-group-counts), step 1 of `NumberOfFilledGroups`.
- `delta`: Narrows KF667's fold to repeatable levels of capacity at least two, so every field named at the only row of a capacity-one group leaves a count over it UNKNOWN; and counts a declared fixed sub-group with no field below it as a member that is never wholly relevant, so its parent never is.
- `basis`: kernel source read at `a12-kernel` `eec9134` (`ValidationCommand.compress` returns a capacity-one set unchanged; the contained elements a group must cover include its sub-groups), kernel 31.1.1; no runtime measurement.
- `acceptance`: Reconcile a12-dmkits' fully-relevant account with both boundaries, or measure either one on kernel 31.1.1 against the stated outcome. Whether a starred capacity-one operand can be authored has no witness known as of `1124b523f`; the rule is stated whatever the answer.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `6fcdbfcdffd0f80787a0109c3b13d29396811da0`.
- `disposition`: Accepted on the second boundary and settled on the first. `PartialWhollyRelevantBoundaryDiffTest` measures on both strategies, beside full validation, that a field-less fixed sub-group leaves both a starred and a fixed count undecided while `GroupFilled` over that group stays decided (KF667, extended 2026-11-04); the peer's interpreter, which had decided both counts, is corrected in that revision (IF459). The first boundary has no repeatable carrier: repeatability `1` declares a fixed group and a star over it is refused `MVK_INVALID_WILDCARD`, so the one-slot level is a fixed group, whose non-folding is KF667's `Seal` row. spec/10 §5.6 is restated so, and [the partial group-count locks](../A12Kernel/Conformance/PartialGroupCount.lean) hold the table.

<a id="spec-2026-10-31-01"></a>
### SPEC-2026-10-31-01 — A String and a Custom join key of one text match, while two temporal keys of different kinds under the measured formats never matched

- `status`: accepted
- `canonical`: [spec/07 §2.2](../spec/07-repetition-and-iteration.md#22-static-gates), the paragraph after the index-kind table.
- `delta`: Replaces "how two keys of different kinds match at runtime is unmeasured". A String key and a Custom key of one text match; under the measured formats a Date beside a DateTime at midnight, a Date beside a Time, a Date inside a `yyyy-MM` fragment's month and a DateTime beside its own clock time never matched, so each such row's join found no partner row. Two kinds declaring one format stay unmeasured, and whether an index field takes such a format is unmeasured too.
- `basis`: the [cross-kind join checkpoint](sources/key-join-and-parallel-probes.md#src-cross-kind-join-keys), `validateFull` on both strategies at a12-dmkits `08b0d6499`, Kernel 30.8.1, measured 2026-10-31.
- `acceptance`: Reconcile a12-dmkits' account of joining keys of different kinds. Text equality and "never across kinds" coincide on every measured temporal row, since its formats give different kinds different texts, so do not claim either as the temporal mechanism.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa66320b6ab32b1ac664e908a40484f9a33e18ec`.
- `disposition`: Reconciled with no correction: on both strategies and the peer's interpreter, String with Custom joins on equal text and fires on unequal text, and every cross-kind temporal pair under the measured formats finds no partner, with Date beside Date as the control. Its KF353 leaves text equality and "never across kinds" unseparated for the temporal rows, as required. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-31a).

<a id="spec-2026-10-31-02"></a>
### SPEC-2026-10-31-02 — A predefined type is a Custom declaration, so `+`'s string-like operands are String and Custom

- `status`: accepted
- `canonical`: [spec/04 §4.1](../spec/04-numbers-and-decimals.md#41-arithmetic-operand-kinds), the `+` paragraph.
- `delta`: Removes the predefined type as a third string-like operand kind: the only predefined-type declaration is a Custom field type, and `+` over one is admitted and concatenates.
- `basis`: the [predefined-type checkpoint](sources/static-admission-and-class-probes.md#src-plus-over-predefined-type), `rule check`, `model check` and `compute` at a12-dmkits `08b0d6499`, Kernel 30.8.1, measured 2026-10-31.
- `acceptance`: Reconcile a12-dmkits' operand-kind account of `+`. The search covered the field schema, `dmtool manifest` and the model JSON; another declaration route is not excluded.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `aa66320b6ab32b1ac664e908a40484f9a33e18ec`.
- `disposition`: Reconciled with no correction: its KF396 and the operand-kind lock now treat the predefined type as Custom's own kernel type, not a third kind, and `[Code] + "x"` computes `abx` on both strategies and the interpreter. The peer bases "exactly String and Custom" on a read of the model mapper. That is a source read, not a measurement, so the canonical clause keeps its own search limit. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-31a).
