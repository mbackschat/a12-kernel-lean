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

<a id="spec-2026-10-26-01"></a>
### SPEC-2026-10-26-01 — An unavailable cell makes its consuming operand UNKNOWN by consumer class and stays in its operand list

- `status`: pending
- `canonical`: [spec/02 B.2](../spec/02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) and [A.4.3](../spec/02-logic-and-formal-errors.md#a43-classifying-a-slot).
- `delta`: Replaces the single row "an aggregate or count containing an invalid cell is non-evaluable and suppresses the rule wherever the cell sits" with consumer classes: all-cells consumers such as `NumberOfFilledFields` and `NumberOfDifferentValues` are UNKNOWN, `FirstFilledValue` is decided by the first non-empty cell, `FieldValuesNotUnique` skips the cell, and group presence follows A.4.8. The operand, not the rule, becomes UNKNOWN, and `And`/`Or` decide the rest. Replaces "an invalid cell drops out" with: the member stays in its list and settles nothing.
- `basis`: the clause's existing cases (`FirstFilledValue` after the first filled row, the [erroneous-member checkpoint](sources/inbound-group-operand-batches.md#src-erroneous-member-quantifier-undecidable)), consistent with this project's executable account. Kernel 30.8.1.
- `acceptance`: Reconcile each consumer class against a12-dmkits' interpreter, notably an invalid member beside a duplicate among the other members under `FieldValuesNotUnique`, which fires. `MinValue`/`MaxValue` as all-cells consumers over a malformed cell in validation are not separately measured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-02"></a>
### SPEC-2026-10-26-02 — In computation a field presence read poisons and group presence never does

- `status`: pending
- `canonical`: [spec/02 A.4.8](../spec/02-logic-and-formal-errors.md#a48-numberoffilledgroups) and [B.6](../spec/02-logic-and-formal-errors.md#b6-validation-excludes-computation-poisons).
- `delta`: Replaces the rationale "a presence test is not a read" with the line Kernel behaviour draws: a field-cell presence read (`FieldFilled`, the field-fill scans) poisons on a reached invalid cell like a value read, while `GroupFilled`, `GroupNotFilled`, `NumberOfFilledGroups` and the group-list quantifiers never poison. A formally invalid stored descendant counts as group content, and a descendant invalid only because its computed dependency failed supplies none.
- `basis`: the [group-presence computation checkpoint](sources/computation-scheduling-probes.md#src-group-presence-computation-guards), Kernel 30.8.1, measured 2026-10-03 on Number inputs at depth two with one repeatable level.
- `acceptance`: Reconcile the field/group split in a12-dmkits' computation arm and its spec/09 cross-reference. Deeper nesting and other kinds are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-03"></a>
### SPEC-2026-10-26-03 — A group operand of the value and filled-field counts expands recursively

- `status`: pending
- `canonical`: [spec/02 A.4.1](../spec/02-logic-and-formal-errors.md#a41-operand-expansion); spec/03's contrary "direct fields" sentence is corrected when spec/03 is rewritten.
- `delta`: States that a group operand of `NumberOfFilledFields` and `NumberOfValueInFields` expands to every field in its subtree, as for the fill quantifiers, where spec/03 said direct fields only. Nested non-repeatable subgroups under these counts are marked unmeasured.
- `basis`: this project's executable account, which expands the counts' group operands over the whole subtree; no Kernel row separates direct from recursive expansion for these counts.
- `acceptance`: Confirm the expansion against a12-dmkits; a row with a field only in a nested non-repeatable subgroup separates the accounts and is unmeasured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-04"></a>
### SPEC-2026-10-26-04 — An instantiated-range filtered predicate never tallies a missing coordinate

- `status`: pending
- `canonical`: [spec/02 A.4.5](../spec/02-logic-and-formal-errors.md#a45-validation-filtered-field-fill-lists).
- `delta`: States that under an instantiated-range field-fill predicate a missing coordinate never enters the tally, whatever the filter would answer there. Whether the filter executes at such a coordinate stays with spec/07 §3.
- `basis`: this project's executable account. Kernel 30.8.1 correspondence for this shape is external evidence pending.
- `acceptance`: Reconcile against a12-dmkits; a filter that would keep a missing coordinate under an instantiated-range predicate separates the accounts.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-05"></a>
### SPEC-2026-10-26-05 — A starred computation count operand counts in-capacity rows on its two unmeasured shapes

- `status`: pending
- `canonical`: [spec/02 A.4.8](../spec/02-logic-and-formal-errors.md#a48-numberoffilledgroups).
- `delta`: Extends the computation rule "a starred operand takes its group's instantiated in-capacity row count" from "not established" to two shapes, each marked unmeasured: a row holding only formally invalid content counts, and a repeatable descendant does not multiply the count.
- `basis`: this project's executable account, which reads no cell for a starred count operand. Kernel 30.8.1 correspondence is external evidence pending.
- `acceptance`: Both shapes are unmeasured on either side; a computation over a malformed-only starred row, and one over a group with a repeatable descendant, settle them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-06"></a>
### SPEC-2026-10-26-06 — Partial validation decides a multi-cell operand's extent by one declared-slot rule and a missing keyed row by one wildcard rule

- `status`: pending
- `canonical`: [spec/10 §5.4](../spec/10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) and [§5.5](../spec/10-validation-and-polarity.md#55-a-selection-that-resolves-to-no-row).
- `delta`: Value-list quantifiers and value counts are decided when the union of relevant patterns covers every declared slot, replacing the one-covering-pattern wording. The terminal field coordinate covers as `0` or `1`, compares literally in wildcard dominance and is ignored by group-absence coverage. A matched key needs its row's index cell and target covered. A no-match is definite absence only when index column and target both wildcard the selected level. `FieldValuesNotUnique` takes no extent judgment. Group-operand `MinValue`/`NumberOfDifferentValues` default to the field-by-field rule.
- `basis`: this project's executable account. The value-list union, the measured keyed coverages and the dominance rows are Kernel-measured as the chapter's `Sources:` lines name; the terminal coordinate in cell cover, the index-cell requirement, the wildcard-only no-match case, `FieldValuesNotUnique` and the group-operand defaults are external evidence pending.
- `acceptance`: Each unmeasured part is marked in the clause; a partial call per part settles it, starting with a matched key whose index cell is uncovered.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-07"></a>
### SPEC-2026-10-26-07 — Message classification enablement is a closed per-leaf table

- `status`: pending
- `canonical`: [spec/10 §3.1](../spec/10-validation-and-polarity.md#31-truth-testing-and-message-classification).
- `delta`: Replaces the three enabling examples with a closed table over every condition leaf, including the root-group arm: root `GroupFilled` and root-operand group lists other than `NoGroupFilled` do not enable, root `GroupNotFilled` and `NoGroupFilled` do; `CustomCondition`, custom-type validity and unfiltered `AllFieldsFilled`/`MoreThanOneFieldFilled`/plural `AtLeastOne`/`FieldValuesNotUnique` do not.
- `basis`: this project's executable account. The rows named as measured members in the clause are Kernel-measured; the root arm and the membership forms are source-read; the other rows are external evidence pending.
- `acceptance`: The clause names its measured rows; a classification grid crossing the unmeasured leaves with a reached runtime failure settles the rest.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-08"></a>
### SPEC-2026-10-26-08 — A count types VALUE once its headroom is exhausted, and four carriers gain polarity rules

- `status`: pending
- `canonical`: [spec/10 §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing).
- `delta`: A fired `count < n` is OMISSION only while the count has headroom and VALUE once it is fixed, with headroom per count operator. Added rules: a filtered `NumberOfFilledFields` moves both ways when a filtered operand contributes a filled cell, a temporal `MinValue`/`MaxValue` is not-given under an empty selected operand, an open tail or a reached filter, operand-list `Min`/`Max` and `Abs` propagate by table, and `NumberOfDifferentValues` grows from an empty selected cell.
- `basis`: this project's executable account. Headroom at the exhausted extent and the distinct count's open tail are Kernel-measured as the chapter's `Sources:` lines name; the four added carrier rules are external evidence pending and marked unmeasured.
- `acceptance`: One fired comparison per added carrier with a fillable operand settles it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-09"></a>
### SPEC-2026-10-26-09 — Relevance is a property of the call and formal invalidity of the cell

- `status`: pending
- `canonical`: [spec/10 §5.1](../spec/10-validation-and-polarity.md#51-the-relevant-set) and [§5.3](../spec/10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set).
- `delta`: Replaces "a field whose value leads to a formal error is not relevant": a formally invalid cell stays relevant for dispatch and is read as unavailable per consumer class. The formal-finding channel under a relevant set now carries [spec/02 B.3](../spec/02-logic-and-formal-errors.md#over-repetition)'s over-repetition exception.
- `basis`: this project's executable account and the three-document `validatePart`/`validateFull` measurement the clause cites; the over-repetition exception is spec/02's existing rule.
- `acceptance`: Already measured on the cited documents; no further row is needed unless a consumer observes the dispatch of a malformed relevant cell.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-10"></a>
### SPEC-2026-10-26-10 — An operator reference assigns every operator its class, deciding six cells the chapters left open

- `status`: pending
- `canonical`: [spec/14](../spec/14-operator-reference.md), with the classes defined in [spec/02 B.2](../spec/02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) and [spec/10](../spec/10-validation-and-polarity.md).
- `delta`: Moves the per-operator membership tables of spec/02 and spec/10 into one table without changing a class. Adds six cells: a `Length` polarity seed, arithmetic propagation for the field-form `AbsValue`/`Round*Value`, the symmetric not-given rule on Boolean, Confirm, Enumeration and DateRange comparisons, classification by Boolean/Confirm comparisons, and keyed group operands enabling classification on the group-list quantifiers. 51 cells read `not stated`, 4 of them for one operand kind only.
- `basis`: this project's executable account for the six added cells, external evidence pending; the moved cells keep their chapter's measured scope.
- `acceptance`: A fired comparison per added polarity cell and a classification grid row per added enablement cell settle them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-11"></a>
### SPEC-2026-10-26-11 — Computation static admission settles five conflicting or silent clauses

- `status`: pending
- `canonical`: [spec/09 §1](../spec/09-computations.md#1-the-ground-rules), [§1.3](../spec/09-computations.md#13-the-scale-gate), [§4](../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape), [§5.1](../spec/09-computations.md#51-operand-reach-scope-the-level-walk-and-placement) and [§5.3](../spec/09-computations.md#53-selection-across-alternatives-and-declarations).
- `delta`: The scale agreement gate applies per alternative, and an alternative with a tolerance band meets none. `MVK_ERROR_FIELD_NO_INDEX` is drawn only by a keyed level beside the target's group whose written path is unkeyed. The empty-precondition gate is per declaration, so a combined first-match table may hold unguarded rows. `RepetitionNotUnique` in the common precondition draws `MVK_ERROR_INVALID_LANGUAGE_FEATURE`. The full-Date-to-yearless copy refusal is scoped as measured, with the declared-Base-Year case unmeasured.
- `basis`: the band, gate-per-declaration and `FIELD_NO_INDEX` sides follow spec/04, spec/01 and the chapter's own measured rows; the common-precondition refusal is this project's executable account, external evidence pending.
- `acceptance`: A computation with `RepetitionNotUnique` in its common precondition, a full-Date field copied into a yearless target under a declared Base Year, and a tolerance-banded Number alternative that fits no target scale settle the three unmeasured parts.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-12"></a>
### SPEC-2026-10-26-12 — Computation runtime results settle four conflicting or silent clauses

- `status`: pending
- `canonical`: [spec/09 §2](../spec/09-computations.md#2-separate-operations-and-the-three-outcomes), [§3.2](../spec/09-computations.md#32-an-invalidity-clear-poisons) and [§5.4](../spec/09-computations.md#54-parallel-joins).
- `delta`: An invalid joined index cell skips the target instances under the common repeatable prefix of the target and the malformed group's parent, and every instance only when no repeatable level is shared. A skipped instance stores no value and a dependent reads it as empty. A filtered count or `Sum` over zero survivors is an ordinary `0`, with no value only where the aggregate identity has none. An empty Date operand of a Date-to-Number operation reads as fillable `0`, so only Date-valued operations clear.
- `basis`: the prefix rule follows the chapter's measured sibling case; the survivor and Date-operand sides follow spec/07 and spec/03/spec/05; the dependent read of a skipped instance is this project's executable account, external evidence pending.
- `acceptance`: A dependent of a joined instance skipped for an off-path invalid key settles the empty read: EMPTY computes `0`, poison clears it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-13"></a>
### SPEC-2026-10-26-13 — Parallel join frames split into common and one-sided classes

- `status`: pending
- `canonical`: [spec/07 §2.1](../spec/07-repetition-and-iteration.md#21-frames).
- `delta`: The join's outer scopes form two classes. A common frame binds both sides at each common outer row before the key union, so equal keys in different outer rows do not join; a one-sided frame is a repeatable non-indexed level above exactly one joined group, iterating ordinarily with the join inside each frame row. Frames diverging on both sides are not stated, and that a common frame's outer rows follow the rule iteration domain is unmeasured.
- `basis`: the one-sided frame is measured at the partial parallel checkpoint's frames row; the common-frame binding keeps the chapter's earlier sentence; this project's executable account admits both classes and plans no diverging frame, external evidence pending for the common frame.
- `acceptance`: A common-frame join whose outer rows differ from the rule iteration domain settles the outer-row clause; a diverging-frame model settles admission.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-14"></a>
### SPEC-2026-10-26-14 — A group operand's compared set is bounded by its own depth

- `status`: pending
- `canonical`: [spec/07 §5.3](../spec/07-repetition-and-iteration.md#53-fieldvaluesnotunique).
- `delta`: The chapter stated a bare repeatable group operand as a per-row anchor judging the current row's cells, and separately that an ancestor operand compares the ancestor's whole extent. Both now follow one rule: repeatable levels above the operand stay bound at the rule's binding and every level below it is reopened. An ancestor operand therefore compares its whole subtree, the rule's sibling rows included, while an unstarred repeatable operand stays bound at the rule's row of its own level, which is unmeasured.
- `basis`: the ancestor-extent case keeps the chapter's measured sentence; the unstarred repeatable case is this project's executable account, which bounds the compared set by the operand's own scope length or first star, external evidence pending.
- `acceptance`: An unstarred repeatable group operand admitted with the error field inside it, with a duplicate only between its current row and a sibling row, stays silent under this account.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-15"></a>
### SPEC-2026-10-26-15 — Concrete syntax adopts the literal and arithmetic-shape rules of spec/04

- `status`: pending
- `canonical`: [concrete syntax §2](../spec/12-concrete-syntax.md#2-literals) and [§3](../spec/12-concrete-syntax.md#3-the-condition-and-operation-grammar-sketch).
- `delta`: A number literal's total digit count is ungated, replacing the fifteen-digit bound. A power chains left-associatively in the grammar, and only an ungrouped power as the direct left operand of another power is refused, `MVK_TOO_MANY_POW_FOR_CALC`; a grouped power exponent still meets the exponent-scale check. At most one division stands in each plain-arithmetic region, `MVK_TOO_MANY_DIV_FOR_CALC`, so `[a]/[b] + [c]/[d]` is admitted. Literal scale, date classification and omitted-year completion now point to their owners in spec/04, spec/05 and spec/09.
- `basis`: spec/04 and spec/09 already stated each rule; 16- and 19-digit literals are measured admitted; this project's lexer and arithmetic-shape checks agree.
- `acceptance`: A 16-digit literal is admitted, `a ^ b ^ c` draws the power code while `a ^ {b ^ c}` passes it, and two divisions in separate addends are admitted. A grouped power exponent then meets the exponent-scale check: `[N] ^ {2 ^ 2}` is admitted and `[A] ^ {[B] ^ [C]}` over scale-0 fields draws `MVK_INVALID_NUMBER_FOR_EXP`.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-16"></a>
### SPEC-2026-10-26-16 — Value lists take no parentheses, and the singular forms take no `In`

- `status`: pending
- `canonical`: [concrete syntax §3](../spec/12-concrete-syntax.md#3-the-condition-and-operation-grammar-sketch) and [§3.2](../spec/12-concrete-syntax.md#32-argument-slots).
- `delta`: The parenthesised value-list form is withdrawn: a parenthesised argument is refused `MVK_UNEXPECTED_TOKEN` in general, and a parenthesised list after `In` is unmeasured. The singular value-list operators take their members after the subject's comma, as spec/06 lowers them; the `In` form of those operators is unmeasured.
- `basis`: the chapter's own measured refusal of a parenthesised argument and spec/06's lowering; this project's reader refuses a parenthesis in any argument and matches the singular forms only without an `In` list, external evidence pending for both unmeasured forms.
- `acceptance`: `FieldValueIncludedInValueList(f In "A", "B")` and a parenthesised list after `In` settle the two unmeasured forms.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-17"></a>
### SPEC-2026-10-26-17 — Argument-slot classes and keyword categories

- `status`: pending
- `canonical`: [concrete syntax §3.2](../spec/12-concrete-syntax.md#32-argument-slots), [§5](../spec/12-concrete-syntax.md#5-keyword-catalog-english--german-verified-pairs) and the [spec/14 argument-slot column](../spec/14-operator-reference.md#argument-slots).
- `delta`: Each operator's argument slots take a named slot class, whether entity, value, literal-or-bracket or another, and spec/14 assigns them per operator; slots no chapter states follow this project's reader and are marked unmeasured. The keyword catalog gains a category column; a condition-call keyword standing where an operation is expected is refused at that keyword, measured on `FieldFilled` only. One name alphabet serves every name, with path segments unmeasured.
- `basis`: the measured slot rows of spec/04, spec/05 and spec/06, and this project's reader for the rest, external evidence pending.
- `acceptance`: A bracketed read in an unmeasured `entity` slot, and a condition call other than `FieldFilled` where an operation is expected, settle the two largest unmeasured classes.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-18"></a>
### SPEC-2026-10-26-18 — Message-parameter admission states its stage order, with unmeasured stages marked

- `status`: pending
- `canonical`: [spec/11 A.6](../spec/11-messages-and-custom.md#a6-name-position-field-references), [A.7](../spec/11-messages-and-custom.md#a7-semantic-index-keys), [A.9](../spec/11-messages-and-custom.md#a9-the-index-terminal), [A.10](../spec/11-messages-and-custom.md#a10-the-group-position) and the [spec/14 keyed message guard column](../spec/14-operator-reference.md#keyed-message-guard).
- `delta`: Group-parameter and index-terminal admission are ordered stage tables. Leaves outside the three guard classes supply no keyed presence guard; a name-position keyed parameter needs no guard; the value suffix's star gate answers first; a keyed or starred index read draws the repetition class even beside a plain read; a key's group is the nearest enclosing indexed repeatable group. Each order or member not measured is marked source reading.
- `basis`: the measured rows the chapter cites, and this project's message-authoring checker for the orders and members marked unmeasured, external evidence pending for those.
- `acceptance`: A value-list leaf beside a keyed group parameter, a keyed index terminal beside a plain read of the same index, and a deeper field keyed past an unindexed intermediate group settle the three widest unmeasured stages.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-19"></a>
### SPEC-2026-10-26-19 — Message rendering names its one fault and treats quoted group segments as the bare group

- `status`: pending
- `canonical`: [spec/11 A.11](../spec/11-messages-and-custom.md#a11-rendering-a-rule-owned-message), [A.3](../spec/11-messages-and-custom.md#a3-the-parameter-grammar), [A.9](../spec/11-messages-and-custom.md#a9-the-index-terminal) and [A.13](../spec/11-messages-and-custom.md#a13-field-owned-producers), with [A.14](../spec/11-messages-and-custom.md#a14-parameter-tokens-and-declared-names) and [B.6](../spec/11-messages-and-custom.md#b6-the-extensibility-surface) for the three negative existentials.
- `delta`: Interpolation is a render step over a fired message except that a key selecting no row faults a value parameter, failing the rule as a runtime failure does. A quoted group segment names the same group as its bare spelling, dropping the earlier admission-only caveat. The index terminal's two readings agree on a non-member S-value, while a blank S-value is unmeasured, replacing a claim that the distinction cannot arise. Only the String-pattern and Enumeration producers insert text opaquely in one pass; requiredness re-reads the running text. Three negative existentials become evidence statements: no admitted use of `Zeile` or `Usb` is known, digit-initial and `:`-bearing declared names are refused on every measured carrier with no resolving witness known, and custom conditions and custom field types are the known hooks, with no custom computation or function known.
- `basis`: the chapter's measured keyed-row fault, quoted-segment render and producer rows; the blank S-value case is external evidence pending.
- `acceptance`: An index terminal over a blank S-value settles whether the two readings agree.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-20"></a>
### SPEC-2026-10-26-20 — A partially known Date meets its omission check before its calendar reality

- `status`: pending
- `canonical`: [spec/05 §6.2](../spec/05-dates-and-time.md#62-partially-known-dates).
- `delta`: The chapter stated both that a partial Date first meets its omission check and that reality is tested before position and precision. The omission pattern now runs first, so a year-optional `yyyy-MM-dd` field holding `0000-13-00` draws `datumFalsch` with the year-optional omission key rather than a format failure.
- `basis`: the K22 message-key capture's row `d5-3`, where both engines agree; this project's stored classifier still runs reality first, recorded under SG6.
- `acceptance`: Row `d5-3` replays with `datumFalsch` and the year-optional omission key.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-21"></a>
### SPEC-2026-10-26-21 — Temporal operands pass one ordered gate per operator

- `status`: pending
- `canonical`: [spec/05 §9.2](../spec/05-dates-and-time.md#92-the-component-classes), [§3.3](../spec/05-dates-and-time.md#33-datetimedate-time-and-the-datetime-projections), [§1](../spec/05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-) and the [spec/14 temporal operand gate column](../spec/14-operator-reference.md#temporal-operand-gate).
- `delta`: Each shift, difference and extractor checks its operand through one ladder: precision, then non-temporal kind, then the unit's component, with a Base Year supplying the year, then the date half, then the time half for month and year steps, then year agreement for a difference. Shifts and differences refuse a partial field before their component gates, while `DateTime`'s Date argument checks components and year first. A shift's result carries its source's component set, all six difference units are non-expandable scale 0, ordering comparisons check orderability before kind, and an odd-length empty-separator range token draws `datumBereichFormatFalsch`. A clock-only DATE_TIME (`HH:mm:ss`) is admitted by the `part H`, `part m` and `part s` extractors, measured for `HoursFromTime`, where a blanket sentence had refused every component extractor on it. Rungs and orders not measured are marked.
- `basis`: the measured rows the chapter cites, including the yearless-anchor and composition-locus checkpoints, and this project's admission checks for the unmeasured rungs, external evidence pending for those.
- `acceptance`: A partial field as `DateTime`'s Date argument beside a missing time half, a non-default-format shift source, and an odd-length range token settle the widest unmeasured cases.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-22"></a>
### SPEC-2026-10-26-22 — `Valid` over an unregistered named type is a runtime failure

- `status`: pending
- `canonical`: [spec/05 §3.7](../spec/05-dates-and-time.md#37-valid-and-invalid-over-a-named-type).
- `delta`: spec/05 said both predicates fire as an ordinary rule message for a filled field when the named type is unregistered; it now follows spec/06 A.3, where the registry lookup failure is a runtime failure of the rule.
- `basis`: spec/06 A.3 already decided it; this project's custom-field validity agrees.
- `acceptance`: A filled field of an unregistered named type under `Valid` separates a runtime failure from an ordinary VALUE firing.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-23"></a>
### SPEC-2026-10-26-23 — Empty reads and the content gate become per-operator classes

- `status`: pending
- `canonical`: [spec/03 A.1](../spec/03-empty-and-required.md#a1-the-per-kind-default), [A.2](../spec/03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default), [A.4](../spec/03-empty-and-required.md#a4-the-row-gate--where-the-substitutions-stop) and the spec/14 [empty read](../spec/14-operator-reference.md#empty-read) and [content gate](../spec/14-operator-reference.md#content-gate) columns.
- `delta`: Every operator takes an empty-read class and a content-gate class. The content-gate leaf inventory is closed, and composition follows the connective: `And` fires on empty only when both parts can, `Or` when either can, with `Or` measured and both `And` forms unmeasured. A tolerance comparison lifts on either side, unmeasured. An all-empty concatenation is the empty String, so its comparison is not evaluated, resolving the chapter's two statements. An empty Confirm reads false with not-given provenance and a fired comparison over it types OMISSION, now measured. Count typing, fixed-group count expansion and the empty value-list subject adopt spec/10 §4, spec/02 A.4.1 and spec/06 B.4.
- `basis`: the measured rows the chapter cites, including the negation pair grid; this project's condition and empty-read evaluation for the leaf inventory and the unmeasured compositions, external evidence pending for those.
- `acceptance`: An `And` of a content-only part and a fires-on-empty part over an empty instance, and a tolerance comparison with an empty right side, settle the two widest unmeasured cases.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-24"></a>
### SPEC-2026-10-26-24 — Required gates use the field's direct parent, and a non-repeatable index field arms no generated check

- `status`: pending
- `canonical`: [spec/03 B.1](../spec/03-empty-and-required.md#b1-the-generated-rule-precisely) and [B.4](../spec/03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique).
- `delta`: The parent-option fixture now places `F5` in group `K` nested in the repeatable `C`, so both columns follow the chapter's own rule that the gate is the field's direct parent and the iteration its nearest repeatable group. An index field nominated in a non-repeatable group is admitted and read by `index(...)`, and neither generated arm checks it, unmeasured.
- `basis`: the generated-requiredness checkpoint for the parent shape; this project's requiredness scope and index preliminary for the non-repeatable case, external evidence pending.
- `acceptance`: An empty or duplicated index field nominated in a non-repeatable group draws no generated finding.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-25"></a>
### SPEC-2026-10-26-25 — Static scale and its capability become per-operator classes

- `status`: pending
- `canonical`: [spec/04 §1.1](../spec/04-numbers-and-decimals.md#11-static-scale-and-the-multiplicative-constant-capability), [§1.3](../spec/04-numbers-and-decimals.md#13-power-scale-and-the-exponent-gate), [§4.8](../spec/04-numbers-and-decimals.md#48-the-formal-check-of-a-stored-value) and the [spec/14 static scale column](../spec/14-operator-reference.md#static-scale).
- `delta`: Every Number-valued operator takes a static-scale class and a multiplicative-constant capability. A `−1` maximum fixes the static scale at the declared minimum; `+` and `-` keep the capability only when every operand has it, and rounding removes it. The exponent gate admits a scale-0 aggregate exponent, while an aggregate over a field of nonzero scale takes the largest declared scale and is refused. A grouped power exponent meets the exponent gate, so `[A] ^ {[B] ^ [C]}` over fields is refused while `[N] ^ {2 ^ 2}` is admitted. The formal-read grammar for stored Number text is stated whole, and the constant-pair gate merges into this chapter. Each class not measured is marked.
- `basis`: the arithmetic-shape and number-operation-node checkpoints for the power cases, the addressed-numeric checkpoints for the measured scales, and this project's scale summary and formal-read parser for the unmeasured classes, external evidence pending for those.
- `acceptance`: `[F] ^ Sum(G*/D2)` with `D2` at scale 2, a rounded operand inside a `==` against a wider field, and a stored `-1`-maximum Number settle the widest unmeasured classes.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-26"></a>
### SPEC-2026-10-26-26 — A raw String's treatment becomes a per-operator class

- `status`: pending
- `canonical`: [spec/06 A.1](../spec/06-strings-and-enumerations.md#a1-raw-type-strings-novaluevalidation) and the [spec/14 raw String operand column](../spec/14-operator-reference.md#raw-string-operand).
- `delta`: Each operator takes a class for a String declared without value validation: refused as a raw read, refused by its own class, read for presence only, or read through its own placeholder or length shape. The earlier blanket refusal of every other value operation is withdrawn for entity-slot operators no chapter decides, whose cells are not stated. Group predicates, `NumberOfFilledGroups` and `CurrentRepetition` refuse a field operand by their own class, and `ValueNotConsistent` refuses a non-table subject, a raw String included.
- `basis`: the measured rows A.1 names (`==`, `+`, `*`, computation `Abs`, the value-list quantifiers, the coercions, named-type validity, `Length`, `FirstFilledValue`, two presence counts), spec/08 §3 for bracketed reads, and this project's reader for the rest, external evidence pending.
- `acceptance`: A raw String under `<`, `-` and `Sum` settles the three widest unmeasured classes.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-27"></a>
### SPEC-2026-10-26-27 — String findings name their codes, and value-list admission states one gate order

- `status`: pending
- `canonical`: [spec/06 stored-value checking](../spec/06-strings-and-enumerations.md#stored-value-checking-and-normalization), [B.3](../spec/06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-) and [B.4](../spec/06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-).
- `delta`: The String findings name their codes: a character outside the charset draws `ZeichenNichtImZeichensatz`, and the length, line-break and pattern findings their measured codes; a trailing blank draws `nachfolgendesBlank`, unmeasured. Value-list admission runs repeat, scope, base type, kind, value validation, then the values side. A Custom field counts as String in scalar membership and takes a literal values side, unmeasured. A formally unavailable member makes scalar `NotIncluded` UNKNOWN in validation while it still poisons in computation, and the pattern blacklist is stated as a character-level predicate.
- `basis`: the string-expression, ingestion and K22 message-key captures for the measured codes, and this project's formal refusal, value-list and pattern checks for the unmeasured items, external evidence pending for those.
- `acceptance`: A trailing blank in a String cell, a Custom field in `FieldValueIncludedInValueList` with a literal list, and a pattern containing an escaped backslash before `p` settle the unmeasured items.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-28"></a>
### SPEC-2026-10-26-28 — Semantic-index reads state their column state, index group and star classes

- `status`: pending
- `canonical`: [spec/08 §4](../spec/08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-), [§4.1](../spec/08-paths-and-references.md#41-what-a-semantic-index-read-yields), [§1](../spec/08-paths-and-references.md#1-absolute-relative-and-short-name-references) and the [spec/14 keyed and category operand column](../spec/14-operator-reference.md#keyed-and-category-operands).
- `delta`: A column is compromised by any in-capacity index cell that is empty, duplicated or formally invalid; rows beyond capacity are excluded. In validation a no-match over a clean column reads empty and over a compromised column UNKNOWN, which suppresses only through the branch-scoped rule rather than the whole rule; computation poisons over a compromised column. A key addresses the nearest repeatable group declaring an index field, so a chain with no repeatable index group draws `MVK_NO_INDEX_FIELD`, measured on an unindexed chain and unmeasured where the only index is the root's or a fixed group's. The star-position classes apply to every keyed operand, not only `NumberOfFilledGroups` and `RepetitionNotUnique`. In a condition a turning point naming another group than the one reached draws `MVK_INVALID_ENTITY`. Each operator's keyed and category operand handling becomes a spec/14 column, and the unmeasured items are marked.
- `basis`: the semantic-index read, runtime-fill and K22 static checkpoints for the measured parts, and this project's semantic-index evaluation, index preliminary and reference resolution for the unmeasured ones, external evidence pending for those.
- `acceptance`: A no-match over a column holding one empty index cell, in a branch beside an independent firing part, and a keyed `Sum` with a star at the index level settle the widest unmeasured items.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-29"></a>
### SPEC-2026-10-26-29 — The data model gathers declaration rules and states each operator's fill-to-fix entry

- `status`: pending
- `canonical`: [spec/01 §1.2](../spec/01-data-model.md#12-model-consistency-rules), [§1.3](../spec/01-data-model.md#13-declaration-generation-classes), [§1.4](../spec/01-data-model.md#14-variant-filters-and-where-a-filtered-declaration-is-seen), [§3.1](../spec/01-data-model.md#31-rules-validation) and the [spec/14 fill-to-fix column](../spec/14-operator-reference.md#fill-to-fix-contribution).
- `delta`: Each operator states how its operands enter the fill-to-fix set: the measured presence-withheld and upward-count members as before, an own projection for `RepetitionNotUnique`, and every other operator ordinary, with a connective taking the union of its branches, unmeasured. A field reports its printed maximum bound before its minimum, and no other order among declaration notifications is claimed. A filtered declaration is still present where the Kernel reads the model as authored. Imported Enumeration block 6 compares its values as written, while the other blocks trim. Index nomination, Enumeration declaration checks, the declared-name table and document JSON reading now live here; the cross-reference, partial-dispatch, target self-read and no-match clauses adopt spec/07, spec/09 and spec/10.
- `basis`: the K17 declaration checkpoint for the bound order, the inbound 2026-10-21 letter for block 6, and this project's omission inventory for the ordinary class and the connective union, external evidence pending for those.
- `acceptance`: A firing rule `A Or B` whose two ordinary leaves read different fields shows whether fill-to-fix holds both fields, and a value comparison over a filled field shows whether the ordinary class lists it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-27-01"></a>
### SPEC-2026-10-27-01 — Five unconditional build failures are not stated under a deleting variant filter

- `status`: pending
- `canonical`: the build table of [spec/01 §1.2](../spec/01-data-model.md#12-model-consistency-rules), its filtered `ONLY` column.
- `delta`: An empty type-reference id, an empty computation target path, two categories of one name, two hint-list entries for one locale and an empty DateFragment `formatOfFragment` still fail the build. Where a variant filter `ONLY` deletes the declaration, their outcome is now not stated, where the old text failed the build unconditionally.
- `basis`: no filtered case was measured for these five, and filters are measured to lift other build refusals, such as an Enumeration without values.
- `acceptance`: each of the five on a field that an `ONLY` filter deletes shows whether the build still fails.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-27-02"></a>
### SPEC-2026-10-27-02 — Two polarity rules are narrowed to their evidence: filtered value-count shrink and `CurrentRepetition`

- `status`: pending
- `canonical`: [spec/10 §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) for the filtered value counts and [spec/10 §4.1](../spec/10-validation-and-polarity.md#41-the-same-rule-fires-either-type) for `CurrentRepetition`.
- `delta`: A filtered value count still shrinks only through a counted match, but that condition now rests on source reading, and a filtered count whose filter counted no match is unmeasured on a comparison only a shrink would falsify. A fired comparison against `CurrentRepetition` is VALUE beside a partner no fill can change. The former "always VALUE" no longer covers a fillable partner, which is unmeasured, while the general dispatch would type it OMISSION.
- `basis`: the measured filtered and unfiltered value-count rows of spec/10 §4, and the general fill-direction dispatch for the fillable partner, external evidence pending.
- `acceptance`: a filtered `NumberOfValueInFields` whose filter counts no match, under a comparison only a shrink would falsify, and `CurrentRepetition` compared with an empty Number field, show each typing.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-27-03"></a>
### SPEC-2026-10-27-03 — Two spec/07 reachability claims become no-witness statements

- `status`: pending
- `canonical`: [spec/07 §3.1](../spec/07-repetition-and-iteration.md#31-the-filter-condition-and-its-static-gates) for the filter gate's discriminating shape and [spec/07 §6.1](../spec/07-repetition-and-iteration.md#61-admission) for the containment gate.
- `delta`: The model that would separate the two filter-gate accounts was called unauthorable, and the containment check was called unreachable without index-keying. Both now say only that no witness is known. The measured `MVK_NO_WILDCARD` refusal of the operand and the index-keying selection stay unconditional.
- `basis`: no measurement settles either negative existential, and the spec rule against unmeasured negative existentials requires the weaker statement.
- `acceptance`: a model reaching the containment gate without index-keying, or a filter-gate model whose operand is admitted, would each be a defeating witness.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-26-30"></a>
### SPEC-2026-10-26-30 — The semantics map becomes a non-normative summary, and empty DateFragment, DateRange and Custom reads move to spec/03

- `status`: pending
- `canonical`: [spec/SEMANTICS-MAP](../spec/SEMANTICS-MAP.md) and [spec/03 A.1](../spec/03-empty-and-required.md#a1-the-per-kind-default).
- `delta`: The map no longer defines rules or terms: every rule it mentions is owned by the linked chapter, which wins on a difference. Its four map-only rules found owners: an empty DateFragment or DateRange operand leaves a comparison not evaluated and an empty Custom field reads as the String kind, so its comparison is not evaluated, all now in spec/03 A.1 and unmeasured; the host pointer API is in scope as data model §2.1 states it, not out of scope as the map said.
- `basis`: this project's DateFragment, DateRange and String comparison operand reads for the three empty reads, external evidence pending, and data model §2.1 for the host pointer API.
- `acceptance`: `[DF] == [DF2]`, `[DR] == [DR2]` and `[C] == "x"` over an empty DateFragment, DateRange and Custom field show whether each comparison is not evaluated.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: none yet.
- `disposition`: none yet.

<a id="spec-2026-10-25-03"></a>
### SPEC-2026-10-25-03 — Behind a joined lead, a declaration reading no partner field is passed over unread

- `status`: accepted
- `canonical`: [spec/09](../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join), the key-joined sentence of the alternatives bullet.
- `supersedes`: [SPEC-2026-10-24-09](#spec-2026-10-24-09)'s clause on a separate declaration reading no partner field; its other clauses stand reconciled.
- `delta`: Replaces "the scan ends with the target cleared wherever it reaches such a declaration" with a position rule: leading the table, such a declaration clears the target at every row whatever any precondition says; behind a joined lead the scan passes over it without reading it, so a holding guard selects nothing, a malformed read in it poisons nothing, and a later joined declaration computes. This also corrects the peer's KF619, which has such a declaration store nothing where its guard selects it.
- `basis`: The [declaration-order checkpoint](sources/group-count-topology.md#src-k22-joined-declaration-order), measured locally 2026-10-25, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the [mixed-plan locks](../A12Kernel/Reference/Dm/ParallelComputationLocks.lean).
- `acceptance`: Reconcile `W01`–`W07`, `WS1`, `WS2`, `WD1` and `WD2` in both documents, notably `W02`, `WS2` and `WD2` at row `B`, where the passed-over guard holds, and `W06` in `w1`, where it reads a malformed cell. Enumeration targets behind a joined lead are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `95b57fb4a3fb40cc7c605d9e3251e5ff35e60cc6`.
- `disposition`: Reconciles all eleven targets at all four rows of both documents, the probe re-run identical to the capture; the peer corrected KF619 to the passing-over rule and its interpreter after `50aeb5b45`, adding its own `Passed`, `PassedConstant` and `PassedBad` rows. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25a).

<a id="spec-2026-10-25-02"></a>
### SPEC-2026-10-25-02 — A group-target CustomCondition's name lookup is left unmeasured

- `status`: accepted
- `canonical`: [spec/11](../spec/11-messages-and-custom.md), the group-target CustomCondition bullet.
- `delta`: Withdraws the claim that the rule fails before the condition's name is looked up and states the outcome only: the rule fails whatever the name answers, the callback is never invoked, and whether a call-specific factory is consulted first is unmeasured. The chosen account resolves no name for such a leaf.
- `basis`: The [group-target abort checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-group-target-custom-abort), measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, whose rows measure the outcome; the lookup timing came from the peer's source reading at [KF615](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf615) and is not adopted.
- `acceptance`: Reconcile the clause's outcome. A factory-consultation discriminator, such as a call-specific factory recording its name queries on a group-target rule, would settle the timing; none is retained, so do not claim either order.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the clause's outcome. The peer's `CustomConditionGroupTargetLookupLawsTest` measures that the group-target rule's name is never looked up, which [spec/11](../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch) now states. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-25-01"></a>
### SPEC-2026-10-25-01 — Count shift amounts take their comparison gate under partial validation, and value counts accept complete concrete coverage

- `status`: accepted
- `canonical`: [spec/10](../spec/10-validation-and-polarity.md), the shift-amount bullet and the value-count sentence after the partial count table.
- `delta`: Adds that a shift amount answers a partial call as the same count or aggregate does as a comparison operand: aggregates, distinct counts and `NumberOfFilledFields` keep the all-rows gate, a value count takes its declared-slot extent, which concrete group rows beside the column wildcard still pass, and `NumberOfFilledGroups` takes its four-step walk. Also adds that concrete group rows covering the whole declared capacity make a String or Boolean value-count column relevant without its wildcard.
- `basis`: The [count shift-amount checkpoint](sources/group-count-topology.md#src-k22-runtime-r9) and the [count-amount twin checkpoint](sources/group-count-topology.md#src-k22-runtime-r11), measured locally 2026-10-25, Kernel 30.8.1, at the measurement pin `08b0d6499`, compared by the runtime replay's full and partial channels.
- `acceptance`: Reconcile r11's `counts` rows, notably `NWild-g12` firing `SV1` but not `SC5`, `NWild-g123` firing `CV2`, `CB7` and `SG3`, `allButItemsD` leaving `SG3` silent and `bad1-gWild` leaving `SG3`, `SC5` and `SV1` silent while `bad2-gWild` fires `SG3`. DateTime distinct counts, Date and Enumeration value counts, fixed or mixed group-count amounts and the Number value count under complete concrete coverage without a wildcard are not separately measured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles `r9` and `r11`, full and partial. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-20"></a>
### SPEC-2026-10-24-20 — A reached unresolvable DateTime literal ends Number arithmetic before a later malformed operand

- `status`: accepted
- `canonical`: [spec/09](../spec/09-computations.md), the sentence after the temporal operand-list extrema paragraph.
- `delta`: Adds that Number arithmetic over temporal extractions reaches its operands in order like the extrema: an extraction reaching the unresolvable literal on the left of `+` reports `berechnungsWertFehler` at the target although the right operand reads a malformed field, the reversed sum aborts silently, and unlike a division domain failure the reached literal is not replaced by a later reached poison. A precondition comparison reaching the literal reports at its target in the same order and poisons the target's readers.
- `basis`: The effects batch of the [recursive temporal checkpoint](sources/temporal-and-message-probes.md#src-recursive-temporal-numeric-expression) (`leftGap`, `rightGap` on `badClock`), measured locally 2026-10-04, Kernel 30.8.1, at the measurement pin `6bc5e753`, whose operand-error channel the runtime replay now compares on every computation row ([operand-channel checkpoint](sources/group-count-topology.md#src-k22-operands-channel)). It instantiates the runtime-failure account the peer's KF513 measures on `Min`/`Max`. The guard carrier and the division contrast are measured on both strategies by the [ordering batch](sources/group-count-topology.md#src-k22-runtime-r8), 2026-10-24, at the measurement pin `08b0d6499`.
- `acceptance`: Reconcile the two `badClock` targets' operand-error channel and the ordering batch's `gG`, `gD`, `gL`, `gR`, `dL`, `dR` and `dA` rows. An unconvertible String component left of a malformed operand is unmeasured: no DM-JSON witness is known as of the measurement pin, since a digit-pattern component always converts and the alternative admitting other text has no DM-JSON carrier by source reading; do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the `badClock` operand-error channel and the `r8` ordering rows. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-19"></a>
### SPEC-2026-10-24-19 — Partial validation's row domain, root coordinates and aggregate shift amounts, and the callback's whole-document view

- `status`: accepted
- `canonical`: [spec/10](../spec/10-validation-and-polarity.md), the root-coordinate sentence after the partial count table, the phantom-row bullet and the aggregate-shift-amount bullet; [spec/11](../spec/11-messages-and-custom.md), the CustomCondition data-view bullet.
- `delta`: Adds that a partial call walks full validation's declared-capacity rows with the content gate overridden, that relevance root coordinates compare literally with `0` encompassing `1`, and that an aggregate shift amount takes the all-rows aggregate gate while a filtered one skips. Also adds that the callback's data view is the whole document, a nonrelevant or over-capacity repeatable cell included.
- `basis`: The [K22 runtime checkpoint](sources/group-count-topology.md#src-k22-runtime-r7) (`rA`–`rC`) and the [partial-channel checkpoint](sources/group-count-topology.md#src-k22-partial-channel), measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, compared by the runtime replay's full and partial channels.
- `acceptance`: Reconcile `rA`'s `c1`/`c2` rows, `rB`'s relevance and over-capacity rows, `rC`'s `KS3` rows and the generated-requiredness capture's partial rows. The `KX5`–`KX8` rows extend the aggregate gate to `MaxValue`, `MinValue`, `NumberOfDifferentValues` and `NumberOfFilledFields` amounts; value-count and group-count shift amounts are settled under [SPEC-2026-10-25-01](#spec-2026-10-25-01).
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5` and `95b57fb4a3fb40cc7c605d9e3251e5ff35e60cc6`.
- `disposition`: `rA`–`rF` reconcile, full and partial, at `f3c2578194b7e2293707fe33980f31920b3983d5` ([reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25)); the generated-requiredness capture's seventeen rows reconcile, full and partial, at `95b57fb4a3fb40cc7c605d9e3251e5ff35e60cc6` [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25a).

<a id="spec-2026-10-24-18"></a>
### SPEC-2026-10-24-18 — On-demand lexing ahead of a later lexer defect, ASCII index-key digits and the callback's view of an empty String

- `status`: accepted
- `canonical`: [spec/12](../spec/12-concrete-syntax.md), the token-demand paragraph; [spec/08](../spec/08-paths-and-references.md), the index-key literal paragraph; [spec/11](../spec/11-messages-and-custom.md), the CustomCondition data-view bullet.
- `delta`: Adds that a parse failure at a real token before a lexer defect keeps its own class, that a `For` literal's digits are ASCII on every index kind, and that the callback's data view hands over a placed empty or blank String as a value, only an absent cell reading as none.
- `basis`: The [K22 S6 checkpoint](sources/group-count-topology.md#src-k22-static-s6), eleven static rows and one runtime probe measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, compared by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean) and the runtime replay.
- `acceptance`: Reconcile the `z` rows and the `when-filled` artifact. A non-ASCII digit stored in a temporal index field and the data view of a repeatable cell are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the `z` rows and the `when-filled` artifact after `e708cf447` and `8536a638c`. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-17"></a>
### SPEC-2026-10-24-17 — A name before `(` resolves first in an entity slot, and difference operands admit shifts but not extrema

- `status`: accepted
- `canonical`: [spec/12](../spec/12-concrete-syntax.md), the bare-entity paragraph; [spec/05](../spec/05-dates-and-time.md), the paragraph after the difference evaluation order.
- `delta`: Narrows the token class of a name that is no keyword before `(` to value positions: in an entity-typed argument slot or inside a bracket the name is resolved first, so an undeclared one draws `MVK_INVALID_ENTITY`. Adds that shifted and `Today` difference operands are admitted, while an extremum in a difference or extractor operand draws `MVK_UNEXPECTED_TOKEN` and a starred operand `MVK_NO_WILDCARDS_ALLOWED`.
- `basis`: The [K22 S5 checkpoint](sources/group-count-topology.md#src-k22-static-s5), two static batches of 17 and 22 rows measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, compared by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean).
- `acceptance`: Reconcile the `w`, `wc`, `y` and `yc` rows. Keyed temporal sources and partial validation of recursive operands are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the `w`, `wc`, `y` and `yc` rows. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-16"></a>
### SPEC-2026-10-24-16 — Raw first-filled members, string-like Custom lists, repeatable category and display sources, key pairing by base type and empty-group `RuleGroup`

- `status`: accepted
- `canonical`: [spec/06](../spec/06-strings-and-enumerations.md), the raw String bullets; [spec/09](../spec/09-computations.md), the ENUMERATION and CUSTOM target paragraphs and the category self-read sentence; [spec/08](../spec/08-paths-and-references.md), the empty-group and defective-key bullets.
- `delta`: Adds that a raw String member of a `FirstFilledValue` list is admitted and reads as the token `X` when filled; that a Custom target's first-filled list admits any string-like source; that a repeatable Enumeration target meets category sources, category self-reads and labelled display classes as measured; that semantic-index keys pair by base type; and that `RuleGroup` naming an empty group draws `MVK_GROUP_IS_EMPTY`.
- `basis`: The [K22 S4 checkpoint](sources/group-count-topology.md#src-k22-static-s4), three static batches, ten `model check` verdicts and two runtime probes measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, compared by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean), the [empty-group locks](../A12Kernel/Reference/Dm/EmptyRuleGroupLocks.lean) and the runtime replay.
- `acceptance`: Reconcile the `va`, `vb`, `vd`–`vf`, `c`, `rw`, `rk` and `rg` rows and both runtime artifacts. Incompatible categories on a fixed target, rendered operand messages and `RuleGroup` over an empty repeatable group are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the S4 rows and both runtime artifacts after `e0b47ee25` and `4a5eb8732`; the peer's KF620 confirms the raw-member reading. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-15"></a>
### SPEC-2026-10-24-15 — Repeatable Enumeration targets: calculation class and the incompatible-pair self-read

- `status`: accepted
- `canonical`: [spec/09](../spec/09-computations.md), the ENUMERATION target paragraph and the target self-read bullet.
- `delta`: Adds that a plain String source and an unlabelled Enumeration source of another domain draw `MVK_ERROR_INVALID_ENUM_CALCULATION` into a repeatable Enumeration target as into a fixed one, and that a repeatable target's plain self-read in a two-entry `FirstFilledValue` of stored reads draws `MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD` even where the other entry's domain leaves the target's.
- `basis`: The [K22 S3 checkpoint](sources/group-count-topology.md#src-k22-static-s3), one 176-row batch measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, rows `ud5`–`ud7` and `uf13`–`uf15`, compared by the [rule-check projection](../A12Kernel/Evidence/RuleCheckProjection.lean).
- `acceptance`: Reconcile those six rows. A labelled repeatable target's display refusal, a category source or category self-read into a repeatable target, and the incompatible pair on a fixed target are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the six rows among 176 after the peer's checker fix `605580381`. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-14"></a>
### SPEC-2026-10-24-14 — Date message keys of the component-omitting, clock and DateTime formats

- `status`: accepted
- `canonical`: [spec/05](../spec/05-dates-and-time.md), the stored Date message-key paragraph.
- `delta`: Adds that one component reading of the completed text serves every date-bearing format: a format without a day selects the format key for every refusal, a day-bearing component-omitting format is completed with the Base Year before the reading, a well-shaped DateTime label is read by its date half whatever its clock holds, and with the 1900 check a malformed date below 1900 selects the check's key ahead of every component.
- `basis`: The [wider key checkpoint](sources/domain-ingestion-probes.md#src-k22-formal-keys-wider), three runs over 123 single-field documents measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, each key identified by rendered text and checked by the [key locks](../A12Kernel/Conformance/FormalMessageKeys.lean).
- `acceptance`: Reconcile the date rows of `keys.json` in the capture. A Base Year below 1900 and the pre-1900 check on a day-bearing component-omitting format are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles all 128 rows of `keys.json` on both strategies, each key recovered from the peer's own rendered text, the shared-text rows up to their `sameText` alternatives. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-13"></a>
### SPEC-2026-10-24-13 — Ordinary partial dispatch compresses the error field's selectors

- `status`: accepted
- `canonical`: [spec/10](../spec/10-validation-and-polarity.md), the rule-gating bullet and the `validatePart` checklist item.
- `delta`: Replaces the exact per-selector match of bound levels with one compressed selector: the relevant identifiers reaching the error path merge, each differing coordinate becoming a wildcard, before the bound levels are matched, so two parts of different lines admit every part of every line. States that parallel dispatch compresses the same way.
- `basis`: The [ordinary partial dispatch checkpoint](sources/group-count-topology.md#src-k22-ordinary-partial-dispatch), nine scopes over one document measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, checked by the [compression locks](../A12Kernel/Reference/Dm/OrdinaryPartialCompressionLocks.lean) and replayed for full validation by `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the `O1` and `O4` firings on unnamed parts under `twoParts`, `threeParts`, `threeNoEmail` and `sameLine`. A group selector compressed with a field selector in one call, and compression for the generated checks, are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles `O1` and `O4` under the four scopes after `84d9cc314`. The generated mandatory check under compression, left unmeasured here, is settled by KF621 and the [dispatch-merge checkpoint](sources/group-count-topology.md#src-k22-partial-dispatch-merge). [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-12"></a>
### SPEC-2026-10-24-12 — Partial dispatch of a parallel rule whose error field lies below its joined group

- `status`: accepted
- `canonical`: [spec/10](../spec/10-validation-and-polarity.md), the parallel-dispatch bullet; [spec/07](../spec/07-repetition-and-iteration.md), the nested-error-field paragraph's unmeasured list.
- `delta`: Adds that a level the error field reopens below its joined group bounds partial dispatch as an ordinary outer level does: a concrete selector of the joined line suppresses the rule, also with concrete parts and for two parts of one line, while parts of two different lines compress to a wildcard line and dispatch, leaf relevance then limiting the firing parts. Removes partial validation from the nested paragraph's unmeasured list.
- `basis`: The [nested-join partial checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-nested-join-partial), eleven partial scopes over one document measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, checked by the [nested partial locks](../A12Kernel/Reference/Dm/ParallelNestedPartialLocks.lean).
- `acceptance`: Reconcile the eleven `C1` outcomes and the `C0` control under `line3`. Whether a concrete part coordinate restricts dispatch or only leaf relevance is not separated by this capture; do not claim either.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the eleven `C1` outcomes and the `C0` control after `84d9cc314`. The part-coordinate question left open here is settled by the peer's KF621 and the local [dispatch-merge checkpoint](sources/group-count-topology.md#src-k22-partial-dispatch-merge): the coordinate narrows dispatch. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-11"></a>
### SPEC-2026-10-24-11 — A parallel rule reaching an unregistered custom condition keeps no earlier joined-row firing and ends

- `status`: accepted
- `canonical`: [spec/11](../spec/11-messages-and-custom.md), the parallel-leaf and registration-lookup bullets.
- `delta`: Replaces the unmeasured note: a parallel rule that reaches an unregistered name keeps no message of a joined row that fired before the reaching row, evaluates no later joined row, and below a repeatable outer row no later outer row. Adds that an `Or` arm reading no joined field is refused beside the pair whatever it holds, while an arm pairing a joined read with the custom condition is admitted.
- `basis`: The [parallel reach checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-parallel-custom-reach), seven documents and six static rows, measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the rule-check projection.
- `acceptance`: Reconcile the `keep`, `reg2` and `mid` outcomes of `P4`, `P7`, `Q1` and `Q7` and the six static verdicts. The partial rows are retained uncompared; do not claim partial behavior from them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: A12 reconciles the `keep`, `reg2` and `mid` outcomes and the six static verdicts; the peer interpreter declines a rule reaching an unregistered name by design and reproduces the other rules. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-10"></a>
### SPEC-2026-10-24-10 — Uniqueness, count and custom-condition leaves beside a joined group target, and joined declarations over different partner groups

- `status`: accepted
- `canonical`: [spec/07](../spec/07-repetition-and-iteration.md), the group error-entity bullet; [spec/09](../spec/09-computations.md), the alternatives bullet.
- `delta`: Adds that beside a join a group target admits `FieldValuesNotUnique` over the pair, a starred partner group or two error-side fields, `NumberOfDifferentValues` over the pair and a custom condition, the uniqueness leaves firing at the line's first part where their field forms fire; that two joined declarations into one target over different partner groups concatenate; and that the ended scan holds for Date and Enumeration joined targets.
- `basis`: The [joined group-target checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-joined-group-target-leaves), nine rules over four documents and ten computations over one, measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the `k22g` firings and the `k22z` outcomes. `g4` and `g5` follow the group-target abort the peer's KF615 at `3be383e24` already states ([inbound](sources/inbound-handbacks.md#src-inbound-2026-10-24b)), so they need no separate reconciliation.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles the `k22g` firings and the `k22z` outcomes after `1533efa45`. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-09"></a>
### SPEC-2026-10-24-09 — Separate declarations into a key-joined target, ordinary parallel leaves on an unmatched side, and partial calls over them

- `status`: superseded
- `canonical`: [spec/09](../spec/09-computations.md), the alternatives bullet and the joined-precondition bullet; [spec/07](../spec/07-repetition-and-iteration.md), the unmatched-side bullet and the partial-validation note.
- `delta`: Adds that into a key-joined target a separate declaration reading no partner field ends the combined table's scan with the target cleared wherever it is reached, whatever its preconditions, leaving later alternatives unreached and poisoning no dependent, while one declaration mixing joined and ordinary alternatives and two joined declarations select normally; that `GroupFilled` of an enclosing group holds at a key-only target row without a partner; that `Length`, text comparison, value-list membership, a filled-field count and the side's own key read an unmatched side as empty, an unmatched error side firing at `-5` when its group has no free row; and that a partial call fires an ordinary parallel leaf only for joined rows it covers on both sides.
- `basis`: The [cross-declaration checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-cross-declaration), two runs over eleven rows measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the [partial leaf locks](../A12Kernel/Reference/Dm/ParallelLeafPartialLocks.lean).
- `acceptance`: Reconcile the `k22x` and `k22y` outcomes and the five partial scopes. The mechanism ending the scan and a partial call over a joined computation's generated rule are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Superseded by [SPEC-2026-10-25-03](#spec-2026-10-25-03). The peer reconciles the `k22x` and `k22y` outcomes and the five partial scopes, but its `Skipped` row (KF619) contradicts the delta's clause that the scan ends wherever a declaration reading no partner field is reached; the local [declaration-order checkpoint](sources/group-count-topology.md#src-k22-joined-declaration-order) measured the corrected account. The entry's other clauses stand reconciled. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

<a id="spec-2026-10-24-08"></a>
### SPEC-2026-10-24-08 — Enumeration and invalid-row joined targets, atoms without a joined form, a guard-only join and Number keys in a joined computation

- `status`: accepted
- `canonical`: [spec/09](../spec/09-computations.md), the String or Date joined-target bullet and the bullet after it.
- `delta`: Adds that a joined Enumeration target copies the partner's token; that String, Date and Enumeration targets clear every instance at a repeated or empty key and clear a target row beyond capacity alone; that a literal-keyed read, a filtered starred `Sum`, `DayFromDate(Today)` and a target-row `NumberOfFilledFields` keep their target-row value inside a joined operation beside an unmatched partner reading empty; that a precondition keyed by a partner field joins by itself; and that Number keys of differing maximum fractional digits join a computation numerically.
- `basis`: The [joined-computation checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-joined-computations), ten computations over three documents measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the 90 computation and generated-rule instances of the `k22j` run. A Number-keyed computation with differing minimum fractional digits, a Boolean or DateRange joined target and a guard keyed by a partner field beside a joined operation are unmeasured here; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Reconciles all three `k22j` rows, the 90 computation and generated-rule instances included, after the peer's interpreter fix `1533efa45`. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

The [October 25 handback](sources/inbound-handbacks.md#src-inbound-2026-10-25) answered the fifteen entries handed off on 2026-10-25: thirteen are `accepted` and `SPEC-2026-10-24-09` is `superseded` by `SPEC-2026-10-25-03`. The [October 25a handback](sources/inbound-handbacks.md#src-inbound-2026-10-25a) accepted `SPEC-2026-10-25-03` and `SPEC-2026-10-24-19`, so no entry is open. The ten terminal receipts accepted at the [October 24a handback](sources/inbound-handbacks.md#src-inbound-2026-10-24a) remain in [the ledger at `255d971f`](https://github.com/mbackschat/a12-kernel-lean/blob/255d971f369efe847a4b39d5127b8a290e4f37ff/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The eight terminal receipts accepted at the [October 23 handback](sources/inbound-handbacks.md#src-inbound-2026-10-23) remain in [the ledger at `e48204df`](https://github.com/mbackschat/a12-kernel-lean/blob/e48204df08f6dd823c28011f520672cfefe0fd60/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 16 terminal receipts closed at the [October 18 response](sources/inbound-handbacks.md#src-inbound-2026-10-18), fourteen `accepted` and two `answered`, remain in [the ledger at `bf2216b6`](https://github.com/mbackschat/a12-kernel-lean/blob/bf2216b69d5a3bbaefe182b76271ddf8d6b27ecf/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).
