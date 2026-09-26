# Archived inbound handback checkpoints of 2026-09-25g and 2026-09-25h

This immutable archive contains the 7 terminal inbound handback receipts reviewed from the peer's `-2026-09-25g` and `-2026-09-25h` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 200,000-byte hub ceiling. Every obligation they recorded already lives in its gap owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation still resolves through the compatibility entry the hub keeps.

<a id="inbound-2026-09-25g-value-list-order"></a>
### Reviewed 2026-09-25g value-list handback — `SPEC-2026-09-25-08` confirmed, and the construct's five gate positions measured

a12-dmkits revision `389920a922fdfc372875a328a2ca26626b6807fa` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-25. The letter is the peer's `-2026-09-25g`, frozen as sent in the user's exchange directory with SHA-256 `cdea0f22449ba14aceffe638e95e6f9616f5369c786ce87fbd257db4a5e8fe8e`. Every lock the records below cite was read at that revision, not run here. The letter answers [`SPEC-2026-09-25-06`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-25-06), `-07` and `-08`, whose entries record the dispositions; its other facts create no outbound entry, and the `-2026-09-25g` records below share this provenance.

**Claim.** Its §1, source-read in the Kernel's field-and-value-list check and then measured at each position (`ValueListQuantifierOperandKindLawsTest.whatTheValueListMayCarryAndWhereARepeatIsAsked`). The field list refuses its own repeat as it is built, then asks its root, base-type, kind and value-validation gates. A field value list refuses its own repeat, and either spelling then asks its root and base-type gates. A repeat across the two lists comes next, an exact one drawing `MVK_DUPLICATE_PARAM1` and a group beside its own member `MVK_DUPLICATE_PARAM2`, and the value list's value validation last. A raw String on either list, or against a literal, draws `MVK_INVALID_RAW_TYPE`. The peer corrected its `kf380` in place.

**Lean.** [`TokenEntityValueList`](../../A12Kernel/Elaboration/TokenEntityValueList.lean)'s stored form now asks the repeat across the lists, containment included, after the value list's base type and ahead of its certification, where it had certified the value list first and asked only an exact repeat, and it projects the raw refusal of either list. The projected form certifies both sides first, so its raw refusal claims no class. [`ValueListQuantifierKindGate`](../../A12Kernel/Conformance/ValueListQuantifierKindGate.lean) locks the discriminating rows.

<a id="inbound-2026-09-25g-date-class"></a>
### Reviewed 2026-09-25g ordering handback — `SPEC-2026-09-25-07` confirmed with the Date on either side

**Claim.** Its §2 (`TemporalComparisonAgreementLawsTest.whatADatePartnerOfAnotherKindDraws`). `[Premium] < [Start]`, `1 < [Start]` and `[Start] < 1` over a Number and a Date draw `MVK_INVALID_COMPARE_TO_DATE`, and `[Start] < [Reference]` against a String draws `MVK_INVALID_TYPE_FOR_COMPARISON`.

**Lean.** No change: the rows confirm this project's own [measurement](../SOURCES.md#src-ordering-date-class-reads-the-pair).

<a id="inbound-2026-09-25g-field-value-read"></a>
### Reviewed 2026-09-25g field-value read handback — `SPEC-2026-09-25-06` confirmed, and a filter's body refuses a repeatable group it does not iterate

**Claim.** Its §3 (`FieldValueReadOperandLawsTest.theGatesReachEveryCarrierOfTheRead`). Every row of `SPEC-2026-09-25-06` holds on a fulfilment sheet. `Sum(/Fulfilment/Shipments*/Parcels*/Weight Having [/Fulfilment/Returns] > 0) > 0`, whose body reads a repeatable group the filter does not iterate, draws `MVK_NO_GROUPS_ALLOWED`.

**Lean.** No change: the star route's body already asked the gates of every read. [`StarNumberElaboration`](../../A12Kernel/Conformance/StarNumberElaboration.lean) now locks a repeatable group the filter does not iterate.

<a id="inbound-2026-09-25g-rounding-mode"></a>
### Reviewed 2026-09-25g rounding-mode handback — `RoundDown` beside `!=` is refused

**Claim.** Its §4 (`ComputationRoundingModeLawsTest.aRoundingModeIsOnlyWrongAgainstAStrictInequality`). On one computation model, `RoundDown` and `RoundUp` beside a band-less alternative draw `MVK_ERROR_WRONG_ROUNDING_MODE`, while `Exact` beside it and every mode beside a tolerance range are admitted.

**Lean.** No change: [`ComputationNormalForm`](../../A12Kernel/Elaboration/ComputationNormalForm.lean) already refused the cell on the peer's earlier reading, and [its conformance module](../../A12Kernel/Conformance/ComputationNormalForm.lean) now locks it as measured.

<a id="inbound-2026-09-25g-banded-rounding"></a>
### Reviewed 2026-09-25g banded-rounding handback — a banded computation's mode rounds to zero places, `Exact` floors to the target's digits, and the validation compares the operation as authored

**Claim.** Its §5, runtime, on the adapter differential with both Kernel strategies agreeing (`ComputationRoundingModeDiffTest`). Beside a tolerance band, into a two-digit target, `RoundUp` writes 1.25 as 2 and −1.25 as −1, and `RoundDown` writes 1.75 as 1 and −1.25 as −2. `Exact` writes a finer operand floored to the target's two digits, 1.255 as 1.25 and −1.255 as −1.26, where the same model without its band errors. An empty operand writes 0 under `Exact` and `RoundUp`. The implicit validation compares the entered value with the unrounded operation. The letter's §7 source hypotheses about where the rounding happens are not recorded as claims.

**Lean.** No change. No Lean computation applies a rounding mode at runtime; [SG5](../gaps/numeric-and-temporal.md#gap-sg5) records the gap.

<a id="inbound-2026-09-25g-keyed-group"></a>
### Reviewed 2026-09-25g keyed-group handback — a keyed group's operand reads the selected row's cells, a lower repeatable level included

**Claim.** Its §6, runtime, with both Kernel strategies agreeing (`KeyedGroupFieldListDiffTest`). `NumberOfFilledFields(Packages For "P1")` counts both filled rows of the repeatable `Items` below the key, 8 where collapsing that level to its first row gives 6, and `AllFieldsFilled` reads that level's declared tail. A key no row carries reads every cell empty, and a key two rows carry is undecided. A malformed cell in the selected row keeps `NumberOfFilledFields` and `NoFieldFilled` silent, poisons `NoFieldFilled` in a computation, and lets `AtLeastOneFieldFilled` stop at the filled key. Statically, `Sum(Packages/Items For "P1")` draws `MVK_NO_WILDCARD`, `Sum(Packages/Items* For "P1")` draws `MVK_NO_NUMBER`, and `Sum(Packages/Items*/Weight For "P1")` is admitted.

**Lean.** No change. The validation spine carries no keyed leaf; [SG9](../gaps/paths-and-groups.md#gap-sg9) records the rows.

<a id="inbound-2026-09-25h-category-index-relevance"></a>
### Reviewed 2026-09-25h category handback — a category read over an index cell the document makes unavailable tracks the value read

a12-dmkits revision `b9e30dc72883608ac761cd946bc5fa0b2ba72b89` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-25. The letter is the peer's `-2026-09-25h`, frozen as sent in the user's exchange directory with SHA-256 `5e9f6889975d4fd70d0471e1d7c01fb12a9cfca740473d05d4c3bb2babb4a7a0`. Its lock `EnumCategoryIndexRelevanceDiffTest` was read at that revision, not run here. It answers no ledger entry and creates none.

**Claim.** Runtime, with both Kernel strategies agreeing. Over a repeatable group keyed by an Enumeration `Plan` with a category `Tier`, `[Plan -> Tier] == HIGH` and `[Plan] == PREMIUM` fire on no row when two rows carry the same key, and neither read's tautology fires there either. On a row above capacity the reads fire nowhere while the tautology fires on the two rows within capacity. A computation guarded by either read clears its target on every row of a duplicated key and on the one row of a missing key. The rows are a second basis for the category bullet in [`06`](../../spec/06-strings-and-enumerations.md) and the category read in [`09`](../../spec/09-computations.md), on a well-formed cell.

**Lean.** No change was made, and the rows were not replayed against a Lean case.
