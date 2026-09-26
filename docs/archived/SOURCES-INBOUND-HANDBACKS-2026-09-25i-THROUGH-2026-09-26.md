# Archived inbound handback checkpoints of 2026-09-25i and 2026-09-26

This immutable archive contains the 7 terminal inbound handback receipts reviewed from the peer's `-2026-09-25i` and `-2026-09-26` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 195,000-byte archiving threshold. Every obligation they recorded already lives in its gap owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation still resolves through the anchor the hub keeps.

<a id="inbound-2026-09-25i-key-addressing"></a>
### Reviewed 2026-09-25i key-addressing handback — a key addresses only its index group's level, a defective key answers first, and the key's own crossing draws the semantic-index class

a12-dmkits revision `16dca38ac1616e43554d2ca063946e21ef9f37ae` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-25i`, frozen as sent in the user's exchange directory with SHA-256 `07e45d5039c9b0bdd6f33a1c62429a0e568632784736f2d8fa448fa281215a0d`. Every lock the records below cite was read at that revision, not run here. It answers no ledger entry and creates none, and the `-2026-09-25i` records below share this provenance. Its §7 reports the peer's own checker and its §8 source hypotheses, neither recorded as a claim.

**Claim.** Its §1 and §2, static verdicts (`KeyedOperandFamilyGateLawsTest`, `SemanticIndexPinnedLevelLawsTest`, `kf476`, `kf478`). Over a repeatable `Claims` keyed by a String and `Endorsements` by an Enumeration, 26 operand gates and the field-operand kind gate, each probed on an operand it refuses, draw their own class on a keyed read from the root, on an unkeyed read from a rule declared inside `Claims` and inside a `Having` body, where the unkeyed read from the root draws `MVK_NO_WILDCARD`. A defective key or keyed path answers first: `MVK_NO_INDEX_FIELD`, `MVK_INDEX_TYPE_INCONSISTENT` for a Number field key, `MVK_INDEX_VALUE_INVALID` for a refused Enumeration constant even ahead of the operand's filter, `MVK_SEMANTIC_INDEX_INVALID_ITER` for a key crossing an unkeyed repetition, `MVK_SEMANTIC_INDEX_AND_WILDCARD` for a starred keyed level and `MVK_MULTIPLE_INDEX_FIELDS` for a second indexed ancestor. Of two reads the first in the text answers.

From the root `Riders/Legs/Amount For "X"` over an unindexed `Riders` draws `MVK_NO_WILDCARD`, as does a key indexed on the root or a fixed group above an unindexed repetition, while from a rule declared inside `Riders` the read reaches `Sum`'s arity class.

**Lean.** [`IterationLegality`](../../A12Kernel/Elaboration/IterationLegality.lean) had glossed its class selector as whether a reference carries a semantic index, which this project's own [iteration capture](#src-iteration-and-semantic-index-legality) already refuted (`SIwild3` against `SIkeySI`) and `Riders/Legs/Amount For "X"` beside `Claims/Amount For Riders/RiderRef` repeats. The Kernel's iteration check asks whether the reference stands inside the key's production, read in its entity checker, so the selector is now `insideSemanticIndexKey` and [its conformance module](../../A12Kernel/Conformance/IterationLegality.lean) locks the local pair. [`SemanticIndexAdmission`](../../A12Kernel/Elaboration/SemanticIndexAdmission.lean) agrees with each class it owns. The validation spine carries no keyed leaf, so no row is replayed on a carrier.

<a id="inbound-2026-09-25i-literal-key"></a>
### Reviewed 2026-09-25i literal-key handback — a quoted key is judged by the index field, and an unquoted digit sequence is an entity name

**Claim.** Its §3 (`LiteralIndexKeyLawsTest`, `kf479`). Over an Enumeration index, `For "OPEN"` is admitted while an undeclared value, the token in another case and the token's label draw `MVK_INDEX_VALUE_INVALID`, and over a whole-number Number index `For "5"` is admitted. An unquoted digit sequence draws `MVK_INVALID_ENTITY` over a String, an Enumeration and a Number index alike, a leading zero included, and `For 5.5` draws `MVK_UNEXPECTED_TOKEN`. Under `Fuer` on a `de_DE` model four of those keys read the same.

**Lean.** No change. [`SemanticIndexAdmission`](../../A12Kernel/Elaboration/SemanticIndexAdmission.lean) takes a constant key's fit as an input, and an entity key resolving to nothing is outside its inputs.

<a id="inbound-2026-09-25i-rule-iteration"></a>
### Reviewed 2026-09-25i rule-iteration handback — the level a rule iterates addresses a scalar slot's read, from the declaring group or the error field's

**Claim.** Its §4 (`RuleIterationAddressesScalarSlotLawsTest`, `kf477`). Of a repeatable, keyed `Claims`, `FieldFilled` of a fixed subgroup, `FieldValueIncludedInValueList` over a Boolean, `AddDays` and `ValueAsDate` over a String and `RangeAsString` over a Number draw their own classes from a rule declared inside `Claims` and from a root rule whose error field lies there, and `MVK_NO_WILDCARD` from a root rule reporting at the root. A string key inside `Claims` draws the gate's class, `For 5` draws `MVK_INVALID_ENTITY`, and from inside an unindexed twin the string key draws `MVK_NO_INDEX_FIELD`.

**Lean.** [`ReadingScope`](../../A12Kernel/Conformance/ReadingScope.lean) locks the field slot's three rows, which settles the [SG9](../gaps/paths-and-groups.md#gap-sg9) assumption that a level the error field binds reaches the slot's kind gate. The membership's Boolean subject has no Lean class at either bound locus: from inside `Claims` the flat route refuses it as a bound repeatable read, and from a root rule reporting into `Claims` as a level holding the error field, the flat-carrier limit [SG9](../gaps/paths-and-groups.md#gap-sg9) records; at the root its kind refusal projects no class, which [SG8](../gaps/strings-and-messages.md#gap-sg8) records. `ValueAsDate`'s scoped comparison refuses a String source without a class, which the [temporal gaps](../gaps/numeric-and-temporal.md) record, and `AddDays` and `RangeAsString` have no flat surface.

<a id="inbound-2026-09-25i-keyed-duplicate"></a>
### Reviewed 2026-09-25i keyed-duplicate handback — a keyed group and a keyed field of it repeat only under one key

**Claim.** Its §5 (`CheckerKeyedOperandAgreementTest.theCheckerReadsAKeyedGroupOperandAsA12Does`, `kf475`). `Sum(Claims For "X", Claims/Amount For "X") > 0` draws `MVK_DUPLICATE_PARAM2`, and with the field keyed `"Y"` it draws `MVK_NO_NUMBER`, the group holding String fields.

**Lean.** No change: no entity list carries a keyed operand.

<a id="inbound-2026-09-25i-enum-source"></a>
### Reviewed 2026-09-25i enumeration-source handback — a starred source meets the star gate after its category and before the target's source gate, and a climbing source is judged as a local one

**Claim.** Its §6 and the keyed rows of §1 (`CheckerKeyedOperandAgreementTest.theCheckerReadsAnEnumComputationSourceAsA12Does`, `KeyedOperandFamilyGateLawsTest.anEnumComputationSourceReadThroughAKey`). Into a root Enumeration, `[Claims*/Banded -> Band]`, `-> Wide` and the stored `[Claims*/Banded]` draw `MVK_NO_WILDCARDS_ALLOWED`, where the local `[Banded -> Wide]` draws `MVK_ERROR_INVALID_ENUM_CALCULATION`, and `-> Nope`, which the Enumeration does not declare, draws `MVK_CATEGORY_UNKOWN`. From `Claims/Review` into its `Outcome`, `[../Banded -> Band]` is admitted while `-> Wide` and the stored read draw `MVK_ERROR_INVALID_ENUM_CALCULATION`. `[Claims/Memo For "X"]` into an Enumeration draws that class too, unkeyed it draws `MVK_NO_WILDCARD`, and `For 5` draws `MVK_INVALID_ENTITY`.

**Lean.** No change. A piped probe of the addressed Enumeration computation admits the climbing covering category and refuses the other two climbing rows, but its refusal projects no class, which [SG8](../gaps/strings-and-messages.md#gap-sg8) records. No surface spells a starred or keyed source.

<a id="inbound-2026-09-26-climbing-read"></a>
### Reviewed 2026-09-26 climbing-read handback — a climbing read is judged at the level it lands on

a12-dmkits revision `c823c798fac47359aa4e49f960e4c23310f8a37f` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26`, frozen as sent in the user's exchange directory with SHA-256 `7824dd20ed05a83033f530d5a016aefa00bcd3f12c9a99ca9e5d0e195fc5fdc3`. Every lock the records below cite was read at that revision, not run here. It answers no ledger entry and creates none. Its §2 and §4 report the peer's own checker and its §5 a source hypothesis, none recorded as a claim.

**Claim.** Its §1 (`KeyedOperandFamilyGateLawsTest.aClimbingReadIsJudgedAtTheLevelItReaches`, `kf480`). From a rule declared in the fixed `Review` inside the keyed `Claims`, `../<x>`, `../<x> For "X"` and `../../Claims/<x>` draw each of the 27 gates' own class, and `../../Riders/<x>` into an unindexed repetition draws `MVK_NO_WILDCARD`.

**Lean.** [`ReadingScope`](../../A12Kernel/Conformance/ReadingScope.lean) locks the field slot's unkeyed rows.

<a id="inbound-2026-09-26-index-key-shape"></a>
### Reviewed 2026-09-26 index-key handback — a constant key meets its index field's value validation as a shape test, one rule per kind

**Claim.** Its §3 (`CheckerIndexKeyConstantAgreementTest`, `kf481`), 48 rows over 17 index fields, each `Sum(<group>/Amount For "<constant>") > 0` from the root. A String key is refused empty, outside declared length bounds, and against a declared pattern unless the whole key matches. A Number key admits an optional minus, digits and a fraction after `.` or `,` within the declared fraction bounds, admitting `05` on a whole-number field and `12345` on a two-integer-digit one, and refusing `+5`. A temporal key matches its format one digit per component letter, admitting `2020-13-45`, and a date range is two dates around its separator. A Boolean admits exactly `true` and `false`, refusing its custom `J` and `N`, and a Confirm only `true`.

**Lean.** No change. [`SemanticIndexAdmission`](../../A12Kernel/Elaboration/SemanticIndexAdmission.lean) takes a constant key's fit as an input; deriving it from the declaration is recorded in [SG9](../gaps/paths-and-groups.md#gap-sg9).
