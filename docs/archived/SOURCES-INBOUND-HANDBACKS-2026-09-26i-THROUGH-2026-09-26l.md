# Archived inbound handback checkpoints of 2026-09-26i through 2026-09-26l

This immutable archive contains the 5 terminal inbound handback receipts reviewed from the peer's `-2026-09-26i`, `-2026-09-26j`, `-2026-09-26k` and `-2026-09-26l` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 195,000-byte archiving threshold. Every obligation they recorded already lives in its gap or implementation owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation still resolves through the anchor the hub keeps.

### Inbound 2026-09-26l handback

<a id="inbound-2026-09-26l-repeatable-root"></a>
#### Reviewed 2026-09-26l repeatable-root handback — a `RepetitionNotUnique` rule at a repeatable root holding every key compares the root's own rows across the document

a12-dmkits revision `70e16c71258092b66e50760dee742b092080f6d5` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26l`, frozen as sent in the user's exchange directory with SHA-256 `435f245eb4619abba545f80ff425e5c726544dab5807712798445a9e4756e7ef`. The lock was read at that revision, not run here. It answers no ledger entry and creates none. Its §2 reports the peer's own records, not recorded as a claim.

**Claim.** Its §1 (`RepetitionNotUniqueRepeatableRootDiffTest`, runtime, both Kernel strategies agreeing), each rule declared in the repeatable root `Fleet`. With `(Plate, Vin)` at `(A, 1)`, `(A, 1)`, `(B, 2)`, `RepetitionNotUnique(Plate, Vin)`, `RepetitionNotUnique(Plate)` and `RepetitionNotUnique(Plate @From /Fleet)`, reporting at `Plate`, fire `VALUE` at the first two vehicles; with `Vin` empty on those two the pair fires `OMISSION` and the sole key `VALUE`, scoped or not; with distinct plates none fires. `RepetitionNotUnique(Drivers/License)`, reporting at `License`, fires `VALUE` at both drivers of the vehicle listing `L-1` twice and not at the other vehicle's `L-1`.

**Lean.** Corrected. [`elaborateRepetitionNotUniqueSource`](../../A12Kernel/Elaboration/RepetitionNotUnique.lean) had refused the root rule without a class; it now takes the root as the reference group, and [`RepetitionNotUniqueValidationRule`](../../A12Kernel/Conformance/RepetitionNotUniqueValidationRule.lean) locks every row.

### Inbound 2026-09-26k handback

<a id="inbound-2026-09-26k-paired-gates"></a>
#### Reviewed 2026-09-26k paired-gate handback — `RepetitionNotUnique` reads every key and its scope before any gate, orders its key-list and placement gates pair by pair, and admits keys at a repeatable root

a12-dmkits revision `4c04bb1abd4b5e72b8bb2b4689b0bb578d57a076` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26k`, frozen as sent in the user's exchange directory with SHA-256 `d0f09b99cbd268f9b90dce27ffb2a046bf9346d233c388c0bb6bd452b3966ecc`. The locks were read at that revision, not run here. It answers no ledger entry and creates none. Its §7 and §9 report the peer's own records and its §8 asks which shape [SG9](../gaps/paths-and-groups.md#gap-sg9)'s last unattributed source meant, answered in this project's receipt as its own §1 row reporting at `Reference`; none is recorded as a claim.

**Claim.** Its §1 to §5 (`RepetitionNotUniquePairedGateLawsTest`, the index-selected `Payments` scope row in `CheckerRepetitionNotUniquePairedGateAgreementTest` alone), on a root `Policy` holding a keyed repeatable `Claims`, a `Payments` keyed on the same field, an index-free `Batches` holding `Items` and `Parts` keyed on one `LineRef`, an index-free `Riders`, an empty repeatable `Vacant` and an empty fixed `Dormant`, beside a repeatable root `Fleet`; unless placed otherwise each rule is in `/Policy` reporting at `Claims/ClaimRef`.

A key that cannot be read answers ahead of each key-list gate in either position, and reporting at the root's `Reference`, `Reference, Claims/ClaimRef` draws `MVK_NO_WILDCARD`, and so it does with a category, a group, a star, a semantic-index key, the raw `Memo` or `Insured, Insured` added before or after `Claims/ClaimRef`. The scope is read with the keys: `@From Vacant` draws `MVK_NO_WILDCARD` over a sole raw key and over a duplicate pair, `@From Dormant` `MVK_GROUP_IS_EMPTY`, and reporting at `Reference` a keyed, an index-free and the empty scope draw `MVK_NO_WILDCARD`.

Each adjacent pair of the category, group, star, semantic-index and raw gates answers with the earlier gate's class in both orders, as does the group gate beside the raw one. `Insured, Insured` draws `MVK_DUPLICATE_PARAM1`, and `Insured, Insured/InsuredName` and `/Policy` beside `Claims/ClaimRef` in both orders `MVK_DUPLICATE_PARAM2`.

From a rule in `Claims`, `ClaimRef` beside `/Policy/Payments/PayRef` draws `MVK_NOT_IN_SAME_PATH` in both orders. Keys in the sibling fixed `Claims/Adjuster` and `Claims/Assessor` are admitted with and without `@From Claims`, while `Batches/Items/ItemRef, Batches/Parts/PartRef` draws `MVK_NOT_IN_SAME_PATH` and with `@From Batches` `MVK_PARALLEL_ITERATION_NOT_ALLOWED`. At `/Fleet`, `Plate` and `Plate, Vin` are admitted, `Registration/RegNo` alone and beside `Plate` draw `MVK_REPEATABLE_GROUP_MISSING`, and `Drivers/License` is admitted.

`@From Insured For "k"` draws `MVK_NO_INDEX_FIELD`, `@From Claims For ""` `MVK_INDEX_VALUE_INVALID`, `@From Claims For "C-1"`, beside `Claims/ClaimRef` or `Payments/PayRef`, `MVK_SEMANTIC_INDEX_NOT_ALLOWED`, `@From Claims*` `MVK_NO_WILDCARDS_ALLOWED`, `@From Vacant*` `MVK_GROUP_IS_EMPTY`, `@From Insured*` `MVK_INVALID_WILDCARD` and `@From Claims* For "C-1"` `MVK_SEMANTIC_INDEX_AND_WILDCARD`. From a rule in `Claims` reporting at `Reference`, `ClaimRef` and `/Policy/Reference @From /Policy/Claims` draw `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`.

**Lean.** Corrected. [`elaborateRepetitionNotUniqueSource`](../../A12Kernel/Elaboration/RepetitionNotUnique.lean) read the scope after the key list's gates and asked an empty scope before its walk; it now reads the scope with the keys, walk first, and projects `MVK_PARALLEL_ITERATION_NOT_ALLOWED` for keys in parallel repeatable groups under a scope. [`RepetitionNotUniqueDiagnostic`](../../A12Kernel/Conformance/RepetitionNotUniqueDiagnostic.lean) locks every row a plain field path can spell, the index-free `Notes` standing for `Riders`. Keys in sibling fixed groups reach this theory's topology limit, and an empty fixed group and a category, starred, index-selected or `$` key or scope have no spelling, which [SG9](../gaps/paths-and-groups.md#gap-sg9) records.

<a id="inbound-2026-09-26k-empty-star"></a>
#### Reviewed 2026-09-26k empty-star handback — an empty group's missing star answers ahead of its emptiness on every group carrier, and an empty repeatable root starred draws the root class

It shares the provenance of the paired-gate record above and takes the letter's §6.

**Claim.** Its §6 (`CheckerRepetitionNotUniquePairedGateAgreementTest.aGroupsStarClassAnswersAheadOfItsEmptinessOnEveryCarrier`), each rule in `/Policy` reporting at `Reference` behind `FieldFilled(Reference)`. `GroupFilled(/Policy/Vacant)` and `NumberOfFilledGroups`, `AtLeastOneGroupFilled` and `NumberOfFilledFields` over `/Policy/Vacant, /Policy/Insured` draw `MVK_NO_WILDCARD`, `NumberOfFilledGroups(/Policy/Vacant*) > 0` `MVK_GROUP_IS_EMPTY` and `NumberOfFilledGroups(/Policy/Dormant*) > 0` `MVK_INVALID_WILDCARD`. On the empty repeatable root `Archive`, `GroupFilled(/Archive)` draws `MVK_NO_WILDCARD` and `NumberOfFilledGroups(/Archive*) > 0` `MVK_ROOT_GROUP_IS_EMPTY`, and on the empty fixed root `Attic`, `GroupFilled(/Attic*)` draws `MVK_INVALID_WILDCARD`.

**Lean.** Corrected once. The unstarred rows already drew the missing star on every carrier Lean holds for them; `NumberOfFilledFields` over two groups has none. A starred empty root had claimed no class; [`StarredGroupElabError.emptyGroupDiagnostic?`](../../A12Kernel/Elaboration/StarGroup.lean) now projects `MVK_ROOT_GROUP_IS_EMPTY`, measured on the count and carried to the other carriers sharing that read as an assumption [SG9](../gaps/paths-and-groups.md#gap-sg9) records, locked in [`GroupListDiagnostic`](../../A12Kernel/Conformance/GroupListDiagnostic.lean). An empty fixed group has no representation.

### Inbound 2026-09-26j handback

<a id="inbound-2026-09-26j-count-star"></a>
#### Reviewed 2026-09-26j count-star handback — a lone unstarred repeatable group draws the missing star ahead of the count's arity, and a rule declared in the group binds it

a12-dmkits revision `7129827809d14f28af455eb3235cd471d537d735` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26j`, frozen as sent in the user's exchange directory with SHA-256 `5bfa9b7d952589d88d413b98aa9fd625c2ff1185bd798c009f5f6180b63f85fc`. The lock was read at that revision, not run here. It answers no ledger entry and creates none. Its §3 corrects the peer's own `-26d`, whose account `spec/05` already carries, its §4 reports the peer's own records, and its note that `KF242` agrees with `spec/07`'s filter scope-gate paragraph changes nothing here; none is recorded as a claim.

**Claim.** Its §1 and §2 (`GroupCountScopeOperandLawsTest`), on a root `Item` holding a fixed `Grading` and a repeatable `Keyed` indexed by its `Key`, beside a repeatable root `Lot`. At `/Item` reporting at `Title` behind `FieldFilled(Title)`, `NumberOfFilledGroups(…) > 0` over `Keyed`, `Grading, Keyed` and `/Lot` draws `MVK_NO_WILDCARD`, over `/Item` and `Grading` `MVK_PARAMSIZE_INVALIDGN`, and over `Keyed*` is admitted. In `/Item/Keyed` reporting at `Amount` behind `FieldFilled(/Item/Keyed/Amount)`, the count over `/Item/Grading, /Item/Keyed` and over `/Item/Keyed*` is admitted and over `/Item/Keyed` alone draws `MVK_PARAMSIZE_INVALIDGN`.

**Lean.** Corrected. The fixed-list count refused a lone group counted from inside it without a class; from the measured placement, a rule declared in the group with its error field there and the group its outermost repeatable level, it now meets the count's arity, every other placement claiming no class, a repeatable root read through the rule's row included, and [`GroupListDiagnostic`](../../A12Kernel/Conformance/GroupListDiagnostic.lean) locks the lone rows from both placements. The paired count from inside the group refuses without a class, since the comparison route sees no guard.

### Inbound 2026-09-26i handback

<a id="inbound-2026-09-26i-expansion-order"></a>
#### Reviewed 2026-09-26i expansion-order handback — a group operand is read depth-first in declaration order, its index field in place, and its first field sets the list's family

a12-dmkits revision `2c2640e731377818a06a59446f315e6cef410d6f` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26i`, frozen as sent in the user's exchange directory with SHA-256 `166fc249834fc5accc1acd36cec8508adba21f92b6970566056718a1484efa4f`. The lock was read at that revision, not run here. It answers no ledger entry and creates none. Its §5 reports the peer's own records, not recorded as a claim.

**Claim.** Its §1 to §3 (`EntityListGroupExpansionKindLawsTest`), each rule at `/Item` behind `FieldFilled(Title)`. `NumberOfDifferentValues` over `Specs, Weight` draws `MVK_STRING_ENUM_AND_NON_STRING_ENUM`, over `Rekeyed*, Title` `MVK_NUMBER_AND_NON_NUMBER` although `Rekeyed`'s String index field follows its Number, over `Layered, Weight`, whose subgroup of a String precedes its Number, the String class, and over `Annotated, Weight`, whose Number precedes its subgroup of a String, the Number class, against `Grading, Weight` admitted.

`Sum` over `Keyed*`, whose index field is a String, over `Nested`, holding a String only in a subgroup, and over `Specs` alone draws `MVK_NO_NUMBER`, and `NumberOfDifferentValues(Keyed*, Title)` the String class, against `Sum(NumNested, Weight)` and `Sum(Grading)` admitted. `MaxValue(Released, Keyed*)` draws `MVK_DATE_AND_NONDATE` and `MaxValue(Released, Monthly*)` over a `yyyy-MM` group `MVK_DATEFORMATS_NOT_COMPATIBLE`, against `MaxValue(Dated*, Released)` admitted. Its §4: `NumberOfDifferentValues(Title, Keyed For "k")` draws the String class, the valid key reading cleanly.

**Lean.** No behaviour change. A group's expansion is the model's field list filtered to its subtree, which [`FlatModel.fields`](../../A12Kernel/Elaboration/Flat/Types.lean) now states is the depth-first declaration order, and every row but the index-selected one agrees in [`GroupExpansionOrder`](../../A12Kernel/Conformance/GroupExpansionOrder.lean). An index-selected group has no spelling on these carriers.
