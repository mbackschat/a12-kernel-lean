# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns open `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. Terminal receipts leave this queue after their useful live facts are preserved in the canonical spec, source or gap owner.

The terminal receipts retired on 2026-10-10 remain in [the ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), and the accepted receipts retired on 2026-10-28 remain in [the ledger at `0a56df16`](https://github.com/mbackschat/a12-kernel-lean/blob/0a56df1698fe9a9f2d64bad3c9ed22a728c9121c/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), both under their stable entry anchors. Earlier deleted receipts remain in [the historical ledger](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md) and [the accepted receipts through 2026-09-24](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md) at `a050f150`. Recover any exact receipt with `git show <revision>:<path>` and find its stable ID; retired IDs are never reused.

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

<a id="spec-2026-10-26-08"></a>
### SPEC-2026-10-26-08 — A count types VALUE once its headroom is exhausted, and four carriers gain polarity rules

- `status`: answered
- `canonical`: [spec/10 §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing).
- `delta`: A fired `count < n` is OMISSION only while the count has headroom and VALUE once it is fixed, with headroom per count operator. Added rules: a filtered `NumberOfFilledFields` moves both ways when a filtered operand contributes a filled cell, a temporal `MinValue`/`MaxValue` is not-given under an empty selected operand, an open tail or a reached filter, operand-list `Min`/`Max` and `Abs` propagate by table, and `NumberOfDifferentValues` grows from an empty selected cell.
- `basis`: this project's executable account. Headroom at the exhausted extent and the distinct count's open tail are Kernel-measured as the chapter's `Sources:` lines name; the four added carrier rules are external evidence pending and marked unmeasured.
- `acceptance`: One fired comparison per added carrier with a fillable operand settles it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: The peer reports confirmation but supplies rows for two carriers only: `NumberOfDifferentValues` over an empty selected cell and a reached `Having` filter on a temporal `MaxValue` (KF639), now stated in spec/10 §4. The filtered `NumberOfFilledFields` movement, operand-list `Min`/`Max` and `Abs` received no row and stay unmeasured. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-26-10"></a>
### SPEC-2026-10-26-10 — An operator reference assigns every operator its class, deciding six cells the chapters left open

- `status`: answered
- `canonical`: [spec/14](../spec/14-operator-reference.md), with the classes defined in [spec/02 B.2](../spec/02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) and [spec/10](../spec/10-validation-and-polarity.md).
- `delta`: Moves the per-operator membership tables of spec/02 and spec/10 into one table without changing a class. Adds six cells: a `Length` polarity seed, arithmetic propagation for the field-form `AbsValue`/`Round*Value`, the symmetric not-given rule on Boolean, Confirm, Enumeration and DateRange comparisons, classification by Boolean/Confirm comparisons, and keyed group operands enabling classification on the group-list quantifiers. 51 cells read `not stated`, 4 of them for one operand kind only.
- `basis`: this project's executable account for the six added cells, external evidence pending; the moved cells keep their chapter's measured scope.
- `acceptance`: A fired comparison per added polarity cell and a classification grid row per added enablement cell settle them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: The peer measures the classification of Boolean and Confirm comparisons and keyed group operands (KF631), the Confirm not-given row and the unfired Boolean and Enumeration comparisons (KF639), now stated in spec/10 and spec/14. The `Length` seed and the field-form propagation received no row and keep citing no measurement. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-26-12"></a>
### SPEC-2026-10-26-12 — Computation runtime results settle four conflicting or silent clauses

- `status`: rejected
- `canonical`: [spec/09 §2](../spec/09-computations.md#2-separate-operations-and-the-three-outcomes), [§3.2](../spec/09-computations.md#32-an-invalidity-clear-poisons) and [§5.4](../spec/09-computations.md#54-parallel-joins).
- `delta`: An invalid joined index cell skips the target instances under the common repeatable prefix of the target and the malformed group's parent, and every instance only when no repeatable level is shared. A skipped instance stores no value and a dependent reads it as empty. A filtered count or `Sum` over zero survivors is an ordinary `0`, with no value only where the aggregate identity has none. An empty Date operand of a Date-to-Number operation reads as fillable `0`, so only Date-valued operations clear.
- `basis`: the prefix rule follows the chapter's measured sibling case; the survivor and Date-operand sides follow spec/07 and spec/03/spec/05; the dependent read of a skipped instance is this project's executable account, external evidence pending.
- `acceptance`: A dependent of a joined instance skipped for an off-path invalid key settles the empty read: EMPTY computes `0`, poison clears it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: Contrary on the acceptance cell: a dependent of a joined instance skipped at an invalid off-path key is cleared, not an empty `0`, and a starred `Sum` over the skipped targets clears too (`JoinedInstanceSkipDependentDiffTest`). spec/09 §2 and §5.4 and the Lean parallel run now poison the skip. The prefix rule and the zero-survivor clause are confirmed, and the Date-to-Number empty read is measured in rules only (KF78). [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-26-18"></a>
### SPEC-2026-10-26-18 — Message-parameter admission states its stage order, with unmeasured stages marked

- `status`: answered
- `canonical`: [spec/11 A.6](../spec/11-messages-and-custom.md#a6-name-position-field-references), [A.7](../spec/11-messages-and-custom.md#a7-semantic-index-keys), [A.9](../spec/11-messages-and-custom.md#a9-the-index-terminal), [A.10](../spec/11-messages-and-custom.md#a10-the-group-position) and the [spec/14 keyed message guard column](../spec/14-operator-reference.md#keyed-message-guard).
- `delta`: Group-parameter and index-terminal admission are ordered stage tables. Leaves outside the three guard classes supply no keyed presence guard; a name-position keyed parameter needs no guard; the value suffix's star gate answers first; a keyed or starred index read draws the repetition class even beside a plain read; a key's group is the nearest enclosing indexed repeatable group. Each order or member not measured is marked source reading.
- `basis`: the measured rows the chapter cites, and this project's message-authoring checker for the orders and members marked unmeasured, external evidence pending for those.
- `acceptance`: A value-list leaf beside a keyed group parameter, a keyed index terminal beside a plain read of the same index, and a deeper field keyed past an unindexed intermediate group settle the three widest unmeasured stages.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: Two of the three stages are measured: a value-list leaf supplies no keyed presence guard, and a key past an unindexed intermediate group binds the nearest indexed repeatable group (KF637). The index-terminal stage received no row and stays on source reading. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-26-24"></a>
### SPEC-2026-10-26-24 — Required gates use the field's direct parent, and a non-repeatable index field arms no generated check

- `status`: rejected
- `canonical`: [spec/03 B.1](../spec/03-empty-and-required.md#b1-the-generated-rule-precisely) and [B.4](../spec/03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique).
- `delta`: The parent-option fixture now places `F5` in group `K` nested in the repeatable `C`, so both columns follow the chapter's own rule that the gate is the field's direct parent and the iteration its nearest repeatable group. An index field nominated in a non-repeatable group is admitted and read by `index(...)`, and neither generated arm checks it, unmeasured.
- `basis`: the generated-requiredness checkpoint for the parent shape; this project's requiredness scope and index preliminary for the non-repeatable case, external evidence pending.
- `acceptance`: An empty or duplicated index field nominated in a non-repeatable group draws no generated finding.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: Contrary: an index field nominated in a non-repeatable group arms the generated mandatory check, OMISSION at the empty key while the group instance holds content, and draws no uniqueness finding (`NonRepeatableIndexFieldGeneratedChecksDiffTest`). spec/03 B.4 and the Lean index preliminary now arm it. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-26-25"></a>
### SPEC-2026-10-26-25 — Static scale and its capability become per-operator classes

- `status`: rejected
- `canonical`: [spec/04 §1.1](../spec/04-numbers-and-decimals.md#11-static-scale-and-the-multiplicative-constant-capability), [§1.3](../spec/04-numbers-and-decimals.md#13-power-scale-and-the-exponent-gate), [§4.8](../spec/04-numbers-and-decimals.md#48-the-formal-check-of-a-stored-value) and the [spec/14 static scale column](../spec/14-operator-reference.md#static-scale).
- `delta`: Every Number-valued operator takes a static-scale class and a multiplicative-constant capability. A `−1` maximum fixes the static scale at the declared minimum; `+` and `-` keep the capability only when every operand has it, and rounding removes it. The exponent gate admits a scale-0 aggregate exponent, while an aggregate over a field of nonzero scale takes the largest declared scale and is refused. A grouped power exponent meets the exponent gate, so `[A] ^ {[B] ^ [C]}` over fields is refused while `[N] ^ {2 ^ 2}` is admitted. The formal-read grammar for stored Number text is stated whole, and the constant-pair gate merges into this chapter. Each class not measured is marked.
- `basis`: the arithmetic-shape and number-operation-node checkpoints for the power cases, the addressed-numeric checkpoints for the measured scales, and this project's scale summary and formal-read parser for the unmeasured classes, external evidence pending for those.
- `acceptance`: `[F] ^ Sum(G*/D2)` with `D2` at scale 2, a rounded operand inside a `==` against a wider field, and a stored `-1`-maximum Number settle the widest unmeasured classes.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: Contrary on one clause: a `-1` maximum is an unknown static scale, not the declared minimum, so equality, inequality, a computation to or from it and its use as an exponent are refused (`CheckerUnknownMaximumScaleAgreementTest`). spec/04 §1.1 and §4.7 and the Lean static scale summary now say so. The three acceptance cells are measured (KF625, KF628). [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-26-28"></a>
### SPEC-2026-10-26-28 — Semantic-index reads state their column state, index group and star classes

- `status`: rejected
- `canonical`: [spec/08 §4](../spec/08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-), [§4.1](../spec/08-paths-and-references.md#41-what-a-semantic-index-read-yields), [§1](../spec/08-paths-and-references.md#1-absolute-relative-and-short-name-references) and the [spec/14 keyed and category operand column](../spec/14-operator-reference.md#keyed-and-category-operands).
- `delta`: A column is compromised by any in-capacity index cell that is empty, duplicated or formally invalid; rows beyond capacity are excluded. In validation a no-match over a clean column reads empty and over a compromised column UNKNOWN, which suppresses only through the branch-scoped rule rather than the whole rule; computation poisons over a compromised column. A key addresses the nearest repeatable group declaring an index field, so a chain with no repeatable index group draws `MVK_NO_INDEX_FIELD`, measured on an unindexed chain and unmeasured where the only index is the root's or a fixed group's. The star-position classes apply to every keyed operand, not only `NumberOfFilledGroups` and `RepetitionNotUnique`. In a condition a turning point naming another group than the one reached draws `MVK_INVALID_ENTITY`. Each operator's keyed and category operand handling becomes a spec/14 column, and the unmeasured items are marked.
- `basis`: the semantic-index read, runtime-fill and K22 static checkpoints for the measured parts, and this project's semantic-index evaluation, index preliminary and reference resolution for the unmeasured ones, external evidence pending for those.
- `acceptance`: A no-match over a column holding one empty index cell, in a branch beside an independent firing part, and a keyed `Sum` with a star at the index level settle the widest unmeasured items.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `fecf855251c1245fd7048b2a509ddbb2b72989dd`.
- `disposition`: Contrary on one clause: where the only index is the root's or a fixed group's above an unbound repetition, the class is `MVK_NO_WILDCARD`, not `MVK_NO_INDEX_FIELD` (`SemanticIndexPinnedLevelLawsTest`). spec/08 §4 and the Lean admission walk now say so. The branch clause and the star cell are confirmed, and Lean now classes the star at the index level. The turning-point clause stays unmeasured. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-27).

<a id="spec-2026-10-24-09"></a>
### SPEC-2026-10-24-09 — Separate declarations into a key-joined target, ordinary parallel leaves on an unmatched side, and partial calls over them

- `status`: superseded
- `canonical`: [spec/09](../spec/09-computations.md), the alternatives bullet and the joined-precondition bullet; [spec/07](../spec/07-repetition-and-iteration.md), the unmatched-side bullet and the partial-validation note.
- `delta`: Adds that into a key-joined target a separate declaration reading no partner field ends the combined table's scan with the target cleared wherever it is reached, whatever its preconditions, leaving later alternatives unreached and poisoning no dependent, while one declaration mixing joined and ordinary alternatives and two joined declarations select normally; that `GroupFilled` of an enclosing group holds at a key-only target row without a partner; that `Length`, text comparison, value-list membership, a filled-field count and the side's own key read an unmatched side as empty, an unmatched error side firing at `-5` when its group has no free row; and that a partial call fires an ordinary parallel leaf only for joined rows it covers on both sides.
- `basis`: The [cross-declaration checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-cross-declaration), two runs over eleven rows measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the [partial leaf locks](../A12Kernel/Reference/Dm/ParallelLeafPartialLocks.lean).
- `acceptance`: Reconcile the `k22x` and `k22y` outcomes and the five partial scopes. The mechanism ending the scan and a partial call over a joined computation's generated rule are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Superseded by [SPEC-2026-10-25-03](https://github.com/mbackschat/a12-kernel-lean/blob/0a56df1698fe9a9f2d64bad3c9ed22a728c9121c/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-10-25-03). The peer reconciles the `k22x` and `k22y` outcomes and the five partial scopes, but its `Skipped` row (KF619) contradicts the delta's clause that the scan ends wherever a declaration reading no partner field is reached; the local [declaration-order checkpoint](sources/group-count-topology.md#src-k22-joined-declaration-order) measured the corrected account. The entry's other clauses stand reconciled. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).
