# Archived inbound handback checkpoints of 2026-09-26o through 2026-09-27

This immutable archive contains the 5 terminal inbound handback receipts reviewed from the peer's `-2026-09-26o`, `-2026-09-26p` and `-2026-09-27` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 195,000-byte archiving threshold. Every obligation they recorded already lives in its gap or implementation owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation keeps resolving through the hub's anchor stubs.

### Inbound 2026-09-27 handback

<a id="inbound-2026-09-27-completed-steps"></a>
#### Reviewed 2026-09-27 walked-step, comment and count handback — a walked path checks only the steps whose production completed, a comment is a token the grammar places, and the peer confirms `SPEC-2026-09-26-05` on its own fixture

a12-dmkits revision `936bf2c427213122299e7ebbc79cfb49563e579d` on `main`, read on 2026-09-27; the peer reports every row green at its ancestor `45168bd8f340a2aa279c38f544fbe12d1725fb17`, and only two documentation files differ between the two. The letter is the peer's `-2026-09-27`, frozen as sent in the user's exchange directory with SHA-256 `3afdf3bb1b8b37e71d9657e3c57423431a6940508317dd1e0c529369e503248f`. The locks were read at that revision, not run here. Its §1 replaces one sentence of [`-26p`](#inbound-2026-09-26p-walked-path) §1, and its §3 answers [`SPEC-2026-09-26-05`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-26-05). Its §4 offers hypotheses and its §5 the peer's own records, recorded as no claim.

**Claim.** Its §1 (`EntityProductionCloseLawsTest.aWalkedPathChecksEachStepItCompletesEvenWhenItNeverCloses`, the `-26p` fixture), each condition `FieldFilled(Code) And` an operand from `/Policy`. `FieldFilled(Items*/NoSuch.)` draws `MVK_UNEXPECTED_TOKEN` beside `FieldFilled(Items*/NoSuch/)`'s `MVK_INVALID_ENTITY`, `FieldFilled(NoSuch.*/Items/)` and `FieldFilled(NoSuch.*/Items)` draw `MVK_INVALID_ENTITY`, and `FieldFilled(Items.*/Count)` `MVK_POINT_IN_A12_MODEL`. The method is the one `-26p` cited under another name, which stated the broader reading.

<a id="inbound-2026-09-27-comment-placement"></a>
Its §2 (`ConditionCommentPlacementLawsTest`), `/Policy` with the String `Code` and the Number `Premium`, a comment `;;c` ending at a line feed. It is admitted before a branch after `And`, after a branch before `And`, and before an arithmetic operand after `+`, and draws `MVK_UNEXPECTED_TOKEN` inside `FieldFilled(…)` and before `RoundUpValue`'s place count. The letter calls the grammar sketch consistent with the admitted rows; its `branch` production does not spell the arithmetic-operand position, which `spec/12` now names.

<a id="inbound-2026-09-27-count-and-list"></a>
Its §3, the peer's own fixtures with every class predicted from the entry's delta before the run. `SoleGroupCountPlacementLawsTest`: an error field outside the counted group draws `MVK_NO_WILDCARD`, and seven placements with the error field in the counted group or a child of it, from the group, the root, a fixed group between, an enclosing repeatable group, the second level and a repeatable root, draw `MVK_PARAMSIZE_INVALIDGN`.

`DateRangeOverlapListGateOrderLawsTest`: over a repeatable root `/Contract`, `Term In` `Grace` is admitted, `Term` draws `MVK_DUPLICATE_PARAM1`, `/Contract` `MVK_ROOT_GROUP_REFERENCED`, `Term, /Contract*` `MVK_DUPLICATE_PARAM2`, `Term, Serial` and `Serial` `MVK_VARYING_TYPES_NOT_ALLOWED`, and `Serial, Serial` `MVK_DUPLICATE_PARAM1`. `FieldTypeMessageTextLawsTest`: a non-ASCII letter in a String pattern message's parameter draws `INVALID_PARAMETER`. No row places the error field outside the rule's group or pairs the list with an interpreted scalar, so those two parts of the entry rest on this project's grids alone.

**Lean.** No change. This project models no parser, so §1's and §2's texts have no spelling, and §3's classes are already locked beside this project's own rows.

### Inbound 2026-09-26p handback

<a id="inbound-2026-09-26p-walked-path"></a>
#### Reviewed 2026-09-26p walked-path and field-copy handback — a `$`-marked, up-run-led or starred path raises its class as it is read even when it never closes, and the peer confirms `SPEC-2026-09-26-04` on its own fixture

a12-dmkits revision `4e1a49baf49fa2215c2ec98c7141edd0200d6ab8` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26p`, frozen as sent in the user's exchange directory with SHA-256 `1ced5086aadeddfa217137f139a04845427c9e0ac127cb7b9cbf0a6d80ee5d8f`. The locks were read at that revision, not run here. Its §1 replaces one sentence of `-26o` §1, and its §2 answers [`SPEC-2026-09-26-04`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-26-04). Its §3 reports the peer's own records and is recorded as no claim.

**Claim.** Its §1 (`EntityProductionCloseLawsTest.aWalkedPathIsResolvedAsItIsReadEvenWhenItNeverCloses`), rule group `/Policy` with the String `Code`, the Number `Premium` and the repeatable `Items` holding the Number `Count`, each condition `FieldFilled(Code) And` an operand. `FieldFilled(Items*/NoSuch/)` and `FieldFilled(NoSuch/Items*/)` draw `MVK_INVALID_ENTITY`, `FieldFilled(/NoRoot/Items*/)` `MVK_INVALID_ROOT_GROUP`, and `FieldFilled(Items/NoSuch/)`, `FieldFilled(/NoRoot/)` and `FieldFilled(Items*/Count/)` `MVK_UNEXPECTED_TOKEN`.

In a `Having` body of `AtLeastOneFieldFilled(Items*/Count Having [Items/Count] == …)`, `[$NoSuch/]` draws `MVK_INVALID_ENTITY`, and `[NoSuch/]` and `[$Items/]` `MVK_UNEXPECTED_TOKEN`. From `/Policy/Claim/Cover`, `FieldFilled(Limit) And FieldFilled(../NoSuch/)` draws `MVK_INVALID_ENTITY`.

Its §2 (`CheckerFieldCopyCrossAgreementTest`), the peer's own eleven declarations and twins, 121 cross cells and six further rows, predicted from the arm order and drawn by the Kernel on all 127. It confirms the arm order and both Enumeration rows of `SPEC-2026-09-26-04`, and adds a limit: the three temporal kinds carry three different formats, so its rows do not separate the kind question from the format question.

**Lean.** No change. For §1 this project models no parser, so no text has a spelling. For §2 the [field-copy locks](../../A12Kernel/Conformance/FieldCopyComparison.lean) already hold the confirmed order and rows.

### Inbound 2026-09-26o handback

<a id="inbound-2026-09-26o-production-close"></a>
#### Reviewed 2026-09-26o production-close handback — a reference or an arithmetic chain is checked where its production closes, a star after a bare name is that name's, up-steps chain only through `/`, and only `Time()` takes an empty argument list

a12-dmkits revision `2aa289fb803747f75aaa7c3c35f57ba89d846375` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26o`, frozen as sent in the user's exchange directory with SHA-256 `284007dd908c41aff8ced5c21f909470fbdc940cabebac5af7d93f06a0ac1922`. The locks were read at that revision, not run here. It answers no ledger entry and creates none. Its §1 sentence that an open production raises no reference class holds only for an unwalked path; [`-26p`](#inbound-2026-09-26p-walked-path) replaces it. Its §6 names the grammar's closing actions and non-recovering error strategy as source-read and is recorded as no claim.

**Claim.** Its §1 and §4 (`EntityProductionCloseLawsTest`), each condition `FieldFilled(Limit) And` an operand from `/Policy/Claim/Cover`. `FieldFilled(../../Code)` and `FieldFilled(.. / .. / Code)` are admitted, `FieldFilled(NoSuch Code)` draws `MVK_INVALID_ENTITY`, and `FieldFilled(NoSuch/)` and `FieldFilled(NoSuch/And)` `MVK_UNEXPECTED_TOKEN`. `FieldFilled(..)` draws `MVK_NO_GROUPS_ALLOWED`, and `FieldFilled(.. ..)`, `FieldFilled(.. .. / Code)` and `FieldFilled(..../Code)` `MVK_UNEXPECTED_TOKEN`.

Its §2 and §5 (same lock), each condition `FieldFilled(Code) And` a text from `/Policy`. `[Code] * 2 == "ABC"` draws `MVK_NO_NUMBER_FOR_CALC`. `[Code] * == "ABC"`, `[Code] + * "x" == "ABC"`, `[Premium] - == 1`, `[Code] - PatternViolated "[0-9]{5}"`, `MinValue(Items**Count) > 1`, `MinValue(Items*/Count - 1) > 1` and `MinValue(Items*/Count ^ 2) > 1` draw `MVK_UNEXPECTED_TOKEN`, while `[Premium] * Abs([Premium]) > 1` and `MinValue(Items*/Count) > 1` are admitted.

`FieldFilled(Premium * 2)` draws `MVK_INVALID_WILDCARD` and `FieldFilled(NoSuch * 2)` `MVK_INVALID_ENTITY`. `FieldFilled()`, `Abs() > 1`, `MinValue() > 1`, `Today() > 1`, `[Code -> ] == "x"` and `[Code -> And X] == "x"` draw `MVK_UNEXPECTED_TOKEN`, and `Time() == Time()` is admitted.

Its §3 (`ValueListInfixLanguageLawsTest`), `/Policy` with the Strings `Tier` and `Premium`. `ValueNotConsistent(Tier To Premium, "gold")` in English and `WertNichtKonsistent(Tier Zu Premium, "gold")` in German draw `MVK_TABLE_ENUM_EXPECTED` in all three casings, the other language's spelling `MVK_UNEXPECTED_TOKEN`, and `In` is admitted in both.

**Lean.** No change. This project models no parser, so none of these texts has a spelling, and `SurfaceFieldPath` carries no starred single field.
