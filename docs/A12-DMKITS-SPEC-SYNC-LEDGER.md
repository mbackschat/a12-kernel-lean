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

<a id="spec-2026-10-25-03"></a>
### SPEC-2026-10-25-03 — Behind a joined lead, a declaration reading no partner field is passed over unread

- `status`: handed-off
- `canonical`: [spec/09](../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join), the key-joined sentence of the alternatives bullet.
- `supersedes`: [SPEC-2026-10-24-09](#spec-2026-10-24-09)'s clause on a separate declaration reading no partner field; its other clauses stand reconciled.
- `delta`: Replaces "the scan ends with the target cleared wherever it reaches such a declaration" with a position rule: leading the table, such a declaration clears the target at every row whatever any precondition says; behind a joined lead the scan passes over it without reading it, so a holding guard selects nothing, a malformed read in it poisons nothing, and a later joined declaration computes. This also corrects the peer's KF619, which has such a declaration store nothing where its guard selects it.
- `basis`: The [declaration-order checkpoint](sources/group-count-topology.md#src-k22-joined-declaration-order), measured locally 2026-10-25, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the [mixed-plan locks](../A12Kernel/Reference/Dm/ParallelComputationLocks.lean).
- `acceptance`: Reconcile `W01`–`W07`, `WS1`, `WS2`, `WD1` and `WD2` in both documents, notably `W02`, `WS2` and `WD2` at row `B`, where the passed-over guard holds, and `W06` in `w1`, where it reads a malformed cell. Enumeration targets behind a joined lead are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

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

- `status`: handed-off
- `canonical`: [spec/10](../spec/10-validation-and-polarity.md), the root-coordinate sentence after the partial count table, the phantom-row bullet and the aggregate-shift-amount bullet; [spec/11](../spec/11-messages-and-custom.md), the CustomCondition data-view bullet.
- `delta`: Adds that a partial call walks full validation's declared-capacity rows with the content gate overridden, that relevance root coordinates compare literally with `0` encompassing `1`, and that an aggregate shift amount takes the all-rows aggregate gate while a filtered one skips. Also adds that the callback's data view is the whole document, a nonrelevant or over-capacity repeatable cell included.
- `basis`: The [K22 runtime checkpoint](sources/group-count-topology.md#src-k22-runtime-r7) (`rA`–`rC`) and the [partial-channel checkpoint](sources/group-count-topology.md#src-k22-partial-channel), measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, compared by the runtime replay's full and partial channels.
- `acceptance`: Reconcile `rA`'s `c1`/`c2` rows, `rB`'s relevance and over-capacity rows, `rC`'s `KS3` rows and the generated-requiredness capture's partial rows. The `KX5`–`KX8` rows extend the aggregate gate to `MaxValue`, `MinValue`, `NumberOfDifferentValues` and `NumberOfFilledFields` amounts; value-count and group-count shift amounts are settled under [SPEC-2026-10-25-01](#spec-2026-10-25-01).
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: `f3c2578194b7e2293707fe33980f31920b3983d5`.
- `disposition`: Partly answered: `rA`–`rF` reconcile, full and partial, but the letter does not name the generated-requiredness capture's partial rows this acceptance also lists, so the entry stays open for them. [reviewed evidence](sources/inbound-handbacks.md#src-inbound-2026-10-25).

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

The [October 25 handback](sources/inbound-handbacks.md#src-inbound-2026-10-25) answered the fifteen entries handed off on 2026-10-25: thirteen are `accepted`, `SPEC-2026-10-24-09` is `superseded` by `SPEC-2026-10-25-03`, and `SPEC-2026-10-24-19` stays `handed-off` for its generated-requiredness rows. `SPEC-2026-10-25-03` was handed off to a12-dmkits on 2026-10-25 and awaits its handback. The ten terminal receipts accepted at the [October 24a handback](sources/inbound-handbacks.md#src-inbound-2026-10-24a) remain in [the ledger at `255d971f`](https://github.com/mbackschat/a12-kernel-lean/blob/255d971f369efe847a4b39d5127b8a290e4f37ff/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The eight terminal receipts accepted at the [October 23 handback](sources/inbound-handbacks.md#src-inbound-2026-10-23) remain in [the ledger at `e48204df`](https://github.com/mbackschat/a12-kernel-lean/blob/e48204df08f6dd823c28011f520672cfefe0fd60/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 16 terminal receipts closed at the [October 18 response](sources/inbound-handbacks.md#src-inbound-2026-10-18), fourteen `accepted` and two `answered`, remain in [the ledger at `bf2216b6`](https://github.com/mbackschat/a12-kernel-lean/blob/bf2216b69d5a3bbaefe182b76271ddf8d6b27ecf/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).
