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

Sixteen corrections are `pending` below and have not been handed off. The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).

<a id="spec-2026-10-14-12"></a>
### SPEC-2026-10-14-12 — a parallel rule's read below a joined group binds that side's joined row

- `status`: pending
- `canonical`: [spec/07 §2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key).
- `delta`: Beside a key join, starred children at one or two starred levels and a fixed subgroup of either side are admitted, read at that side's joined row, and alone anchor the join. An unmatched side's children read empty, also when its key-only row lies beyond capacity, and are referenced at its `-5` row with starred levels at `[0]` and a fixed subgroup at `[1]`; a read below a side's row adds that side's index field to the fill-to-fix set. A filtered star below either joined group draws `MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED` after `RepetitionNotUnique` beside the join, one in an unjoined group is admitted, and an unstarred child read draws `MVK_NO_WILDCARD`.
- `basis`: [parallel child-read checkpoint](sources/model-structure-and-declaration-probes.md#src-parallel-child-reads), 24 static rules and two runtime rounds over the `free` and `full` documents, at a12-dmkits `a4091041`, Kernel 30.8.1, both strategies agreeing.
- `acceptance`: Reconcile the static verdicts of `q00`–`q12`, `r01`–`r05`, `y1`, `y2`, `x1`, `x2` and the messages with their references on both documents of both rounds. Do not claim partial calls over these reads, a runtime row for a rule declared inside a joined group, a keyed read into a child group, a filtered star in a frame enclosing a joined group, or a keyed read on a key-only row beyond capacity, which this entry does not cover.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-11"></a>
### SPEC-2026-10-14-11 — the scale-warning waiver reaches every filter comparison of its text

- `status`: pending
- `canonical`: [spec/04 §1](../spec/04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time).
- `delta`: `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` and a computation's `errorCodesToSuppress` waive the `==`/`!=` scale gate inside the text's `Having` filters as well, on literal, field-pair and arithmetic sides under every measured aggregate; unwaived, each such filter draws the class. Evaluation stays exact. Tolerance comparisons draw no scale class inside or outside a filter.
- `basis`: [filter suppression checkpoint](sources/having-filter-probes.md#src-having-scale-warning-suppression), 22 rule checks, two computations and two runtime documents per model, and the [carrier checkpoint](sources/having-filter-probes.md#src-having-waiver-carriers), 12 rule checks and six computations, at a12-dmkits `a4091041`, Kernel 30.8.1, both strategies agreeing.
- `acceptance`: Reconcile the static verdicts of `w01`–`w08`, `s01`–`s14`, `m01`–`m04`, `t01`–`t04`, `v01`/`v02` and the six carrier computations, `c01` admitted and `c02` refused, and the runtime messages and `Tot2` values of both documents. A nested filter draws `MVK_NO_WILDCARD` waived or not, so it witnesses nothing about the waiver. Do not claim a German-condition model.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-10"></a>
### SPEC-2026-10-14-10 — the requiredness text substitutes four tokens in succession and checks nothing; an Enumeration text renders its stored value

- `status`: pending
- `canonical`: [spec/11 Part A](../spec/11-messages-and-custom.md#part-a--13-error-message-interpolation).
- `delta`: A required field's own text is never checked. Rendering replaces `$Feld$`, `$field$`, `$Feld.Wert$` and `$field.value$` in that order over the whole text, the names by the label or short name and the values by the empty text, every other dollar sequence staying verbatim. An Enumeration's invalid-value text renders the label and the stored value and refuses `$BaseYear$`, another field, a category and an inner `$$` with `INVALID_PARAMETER`.
- `basis`: [field-owned producer checkpoint](sources/message-parameter-rendering-probes.md#src-field-owned-message-producers), 23 requiredness and seven Enumeration templates at a12-dmkits `a4091041`, Kernel 30.8.1, both strategies agreeing.
- `acceptance`: Reconcile the rendered texts of `q01`–`q23`, `rq`, `n01` and `n02` and the static classes of `n03`–`n07`. Do not claim re-substitution inside a label, a German-condition model or the catalog default text.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-09"></a>
### SPEC-2026-10-14-09 — `RepetitionNotUnique` keys in sibling fixed groups of one row

- `status`: pending
- `canonical`: [spec/07 §6](../spec/07-repetition-and-iteration.md#6-repetitionnotunique-precisely-).
- `delta`: Key components in sibling fixed groups of one repeatable row are admitted and compare per that row; a component whose group repeats nowhere draws `MVK_REPEATABLE_GROUP_MISSING` whether it is written first or second.
- `basis`: [entity-list and group checkpoint](sources/group-count-topology.md#src-row-bound-group-and-key-gates), rules `d01`–`d05` at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile `d01`–`d03` on the filled and malformed documents and the two static refusals. Do not claim sibling groups below different repeatable levels, which no row measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-08"></a>
### SPEC-2026-10-14-08 — an unstarred own-row operand beside a star in `SumOfProducts` draws the lowest-level class

- `status`: pending
- `canonical`: [spec/07 §3](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation).
- `delta`: The filtered operand is not the only shape reaching `MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED`: an unstarred operand on the level the rule iterates beside a starred one draws it too, while `Sum` and `MaxValue` admit the same pair and evaluate it per row.
- `basis`: [entity-list and group checkpoint](sources/group-count-topology.md#src-row-bound-group-and-key-gates), rules `b01`–`b05` at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile `b02`'s class and the admitted `b01`/`b05` runtime. Do not claim which gate reaches the class first.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-07"></a>
### SPEC-2026-10-14-07 — an undecided keyed selection leaves `NotAllFieldsFilled` silent

- `status`: pending
- `canonical`: [spec/08 §4](../spec/08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-).
- `delta`: Over a keyed lower star or a keyed fixed group, a duplicated key leaves `NotAllFieldsFilled` silent, as it leaves `NoFieldFilled`: the undecided selection has no declared slot left to count as missing, so beside it only an empty sibling operand fires the rule. A key naming no row fires it with OMISSION.
- `basis`: [semantic-index checkpoint](sources/model-structure-and-declaration-probes.md#src-semantic-index-reads), rule `q04` over a keyed star and `v05` over a keyed fixed group, each on its duplicate, unmatched and matched documents, and `w02`–`w05` beside a filled or empty fixed operand, at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile the documents of both carriers and the fixed-operand compositions. Do not claim whether the silent verdict is UNKNOWN or not-fired, which no row separates, or the remaining fill quantifiers, which no row measured under a duplicate key.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-06"></a>
### SPEC-2026-10-14-06 — leaves beside a key join keep their ordinary meaning at the row that binds them, and String and Date targets join

- `status`: pending
- `canonical`: [spec/09 §5](../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join) and [spec/07 §2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key).
- `delta`: A joined computation's precondition admits `Today`, starred aggregates and field-fill lists, a filtered starred `Sum`, literal-keyed reads of a third or the partner group and `PatternMatched`; a parallel rule admits literal-keyed field reads of a third group, literal-keyed reads into the partner group and error-side key fields. Values and messages agree with each leaf keeping its ordinary meaning at the common row, or at the error side's row where it reads that row; an omission against an error-side key that names no row includes that side's index field in its fill-to-fix set. A key read off the partner row selects per joined row, in a precondition and beside a pair. An unmatched side, the error side included, reads its non-key fields as empty, so a read keyed by one of them names no row and negative leaves fire as omissions at its `-5` address. `NumberOfDifferentValues` and `FieldValuesNotUnique` over one field of each side count the two joined values; alone, `> 1` is admitted and `< 2` draws `MVK_PARALLEL_ITERATION_INVALID`. A starred aggregate inside a joined Number operation, and in its generated rule's compared operation, keeps its ordinary meaning at the target row. A String or Date target copies a partner field by key, an empty partner field or a missing partner clearing it.
- `basis`: [joined-carrier checkpoint](sources/model-structure-and-declaration-probes.md#src-joined-carrier-admission), rows `j01`–`j08`, `j10`, `j11`, `t01`–`t03`, `k01`–`k09` and the `matched` and `sparse` documents, and the [joined-carrier-limits checkpoint](sources/model-structure-and-declaration-probes.md#src-joined-carrier-limits), rows `p01`–`p04`, `u01b`–`u04b`, `d01b`, `d02b`, `d03`, `d04` and the `staff` and `noledger` documents, at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile admission, the per-row values and the messages with their references. Do not claim the ordinary-meaning account as a measured mechanism, the reading of an unmatched side's own key field or of a group with no free row, the empty-field reading for an unmatched error side's other leaf kinds, the runtime reading of a starred uniqueness test beside a join, a joined target of a kind other than Number, String and Date, or an invalid-index or over-limit row of a String or Date target, which this entry does not cover.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-05"></a>
### SPEC-2026-10-14-05 — a condition call in an operation position fails at its keyword

- `status`: pending
- `canonical`: [spec/12 §12.3](../spec/12-concrete-syntax.md).
- `delta`: A condition call where an operation stands draws `MVK_UNEXPECTED_TOKEN` at its keyword, before its own reads are checked, after the gates of productions completed before it.
- `basis`: [predicate-operand checkpoint](sources/model-structure-and-declaration-probes.md#src-predicate-operand-classes), 30 static rows at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile the operand, arithmetic and comparison-side rows and the completed rounding and date gates. Do not claim a completed call inside a filter body, which no row measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-04"></a>
### SPEC-2026-10-14-04 — an empty Enumeration token is legal, admitted as a literal, and never a cell value

- `status`: pending
- `canonical`: [spec/06 value lists](../spec/06-strings-and-enumerations.md).
- `delta`: An Enumeration declaring `""` loads; `""` is a value-list literal exactly where it is a selected token; a stored `""` cell stays present-empty, so the token never matches and draws no formal finding; `== ""` and `!= ""` never fire on an Enumeration, as on a String.
- `basis`: [empty-token checkpoint](sources/model-structure-and-declaration-probes.md#src-empty-enumeration-token), seven static rows and one runtime request over four documents at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile declaration loading, the literal gate and the four documents. Do not claim an empty category token, a labelled empty token or an empty index value, which no row measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-03"></a>
### SPEC-2026-10-14-03 — a keyed group read beside a key join selects one row for every joined row

- `status`: pending
- `canonical`: [spec/07 §2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key).
- `delta`: A literal-keyed `GroupFilled` of a group outside both joined groups is admitted beside a joined pair, licenses keyed message parameters under its key, and selects the same row, rendered and referenced, at every joined row.
- `basis`: [keyed membership](sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15) rows `p00`–`p02` and [message rows](sources/message-parameter-rendering-probes.md#src-message-parameter-rows-k15) rule `RPk` over two documents, a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile admission, rendering and references with these rows. Do not claim a field-valued key, a keyed field read or a keyed group enclosing a joined group beside the join, which no row measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-02"></a>
### SPEC-2026-10-14-02 — ordinary leaves and computation guards of a key join read one joined row

- `status`: pending
- `canonical`: [spec/07 §2](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key) and [spec/09 §5](../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join).
- `delta`: Validation leaves without a pair form and the preconditions of a joined computation are admitted and read each field from its side's joined row; an unmatched partner's fields read empty, as a key-only row's other fields do, while `GroupFilled` of the partner group fails without a partner and holds for a key-only one; `GroupFilled` of the target's own group is admitted in a joined guard and `GroupNotFilled` of it draws `MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD`.
- `basis`: [parallel instance checkpoint](sources/model-structure-and-declaration-probes.md#src-parallel-instance-leaves), 39 static rows and two runtime requests at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile the admission and runtime rows. Do not claim the enclosing-group account, which no row separates, or the reading of an unmatched partner's own key field, which no row reads.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-14-01"></a>
### SPEC-2026-10-14-01 — a CustomCondition leaf in a parallel rule guards no iteration

- `status`: pending
- `canonical`: [spec/11 §14](../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).
- `delta`: Beside a parallel field pair a `CustomCondition` leaf is admitted under `And` in either order and refused under `Or` with `MVK_PARALLEL_ITERATION_INVALID`; its callback receives the joined row's error pointer, `UNKNOWN` where unbound.
- `basis`: [parallel custom checkpoint](sources/model-structure-and-declaration-probes.md#src-parallel-custom-condition), six rows at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile the static admission with these rows. Do not claim the callback's runtime inputs in a parallel row, which no route measured.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-13"></a>
### SPEC-2026-10-13-13 — quoted Number conversion, kept leading-zero text and the full formal cascade with its message keys

- `status`: pending
- `canonical`: [storage regimes](../spec/04-numbers-and-decimals.md#stored-decimal-identity-and-runtime-read-text-depend-on-the-storage-regime) and [other numeric constraints](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints).
- `delta`: Quoted Number text converts by the host decimal grammar (sign, BMP decimal digits, fraction, exponent); unconvertible text and, on a `leadingZerosAllowed` field, text with an ASCII leading zero stay verbatim. A scale outside 32 bits keeps the text; an extreme in-range scale can fault validation. The cascade gains a leading plus first, signed zero, missing separator and leading zero at their positions, and a negative zero on an unsigned zero-forbidding amount field reports `zahlIstNull`. The lexical checks are reached by kept text, not only by display conversion, which this replaces. Message keys additionally read sign and plain fractional shape.
- `basis`: [ingress checkpoint](sources/domain-ingestion-probes.md#src-number-ingress-k16), four runtime requests over fourteen documents at a12-dmkits `a4091041`, Kernel 30.8.1, plus the retained `FormalNum` captures; peer kf276 for the money exception.
- `acceptance`: Reconcile conversion, retention and cascade order with these rows. Do not claim a measured grouping-separator route, a separated sign variant of any message key, or a conversion outcome for a scale magnitude between 100,000 and the faulting `2147483648`.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-14"></a>

### SPEC-2026-10-13-14 — the model consistency rule set, its order and the authored versus filtered model it reads

- `status`: pending
- `canonical`: [model consistency rules](../spec/01-data-model.md#12-model-consistency-rules).
- `delta`: A built model meets identifier uniqueness, Number value limits, attachment and multi-select group shapes, the generation of the declaration with the printed-bound formal check, and basic member checks, in that order, each notification reported in walk order except the generation rule's, which form an unordered set ([SPEC-2026-10-13-16](#spec-2026-10-13-16)); a model drawing any is refused. Every rule but the bound check reads the authored model, variant-filtered fields included. Duplicated identifiers report every occurrence; the value limit compares doubles at the raw declared maximum fraction digits; a field's bound check reports the maximum before the minimum and an identical class once. Six empty or repeated members fail the build with no class.
- `basis`: [consistency checkpoint](sources/model-structure-and-declaration-probes.md#src-model-consistency-k17), 89 rows at a12-dmkits `a4091041`, Kernel 30.8.1, with source reading at Kernel `cb66e51`.
- `acceptance`: Reconcile rule order, multiplicity and the authored/filtered split with these rows. Do not claim an order across distinct duplicated identifiers, attachment texts under another condition language, or two build failures in one model.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-15"></a>

### SPEC-2026-10-13-15 — runtime Number bounds as printed double text and the runtime account of the fractional sentinel

- `status`: pending
- `canonical`: [other numeric constraints](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints).
- `delta`: A declared `minValue`/`maxValue` is compared at runtime as the text printed from its nearest double, with fixed places rounding half up when both fractional members equal `n ≥ 0` and the plain shortest decimal otherwise. The `-1` sentinel resolves into an ordinary pair (`-1` minimum to zero, `-1` maximum to the minimum), except that a `-1` minimum beside a zero maximum arms neither the separator nor the fractional-count test.
- `basis`: [bounds checkpoint](sources/domain-ingestion-probes.md#src-number-declaration-bounds-k17), two requests at a12-dmkits `a4091041`, Kernel 30.8.1, both strategies agreeing.
- `acceptance`: Reconcile the printed bound and sentinel resolution with these rows. Do not claim a measured computed fractional result into a `(-1, 0)` field.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-16"></a>
### SPEC-2026-10-13-16 — the declaration-generation classes of field types, element names, groups and element texts, reported as one unordered set

- `status`: pending
- `canonical`: [declaration generation classes](../spec/01-data-model.md#13-declaration-generation-classes), with the carrier alphabets in [spec/11](../spec/11-messages-and-custom.md).
- `delta`: The generation rule's notifications form an unordered set, identical ones on one element collapsing, over the variant-filtered model, a type definition judged once per referencing field. New or sharpened: member ranges draw five codeless classes; `lineBreaksPermitted` coerces like `noValueValidation`, a fractional number or other text being unreadable; Number bounds may be written as decimal text; an empty pattern and a `-1` minimum are undeclared; a field-locus Java compile failure is `MVK_PATTERN_INVALID`; hint lists judge declared locales only, fail the build on a repeated locale and exempt supplementary values; the Number length budget, arity on the minimum count and value bounds compared as printed; Custom names ASCII letters, digits and `_`; Enumeration label counts once per declared locale, blank and duplicate labels, tab/pipe/line-break texts and the case-sensitive default value; a refused group's path class only at the group, its group-path notification on every element beneath, which keep their own classes; the root's own shape and length notifications; the exact `__meta` reservation; element annotations as repertoire carriers; a computation name under the error-code alphabet; `WRONG_ENCODING` on a lone surrogate, and no repertoire notification for a message character that draws `INVALID_CHARACTERS`; the temporal format and DateRange pair notifications; `MVK_MAX_TOO_BIG` and `MVK_INVALID_SORTINFO`, an empty group drawing nothing; `MVK_UNSPECIFIED_TYPE_NO_CODEGEN`; a temporal kind without its body and an undeclared member such as `datePrecision` off a Date being unreadable.
- `basis`: [declaration checkpoint](sources/model-structure-and-declaration-probes.md#src-field-declaration-notifications-k17), 355 rows at a12-dmkits `a4091041`, Kernel 30.8.1.
- `acceptance`: Reconcile the class laws, multiplicities and withholding with these rows. Do not claim a notification order, or the listed unmeasured choices.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
