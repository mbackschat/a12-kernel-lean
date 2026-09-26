# Archived inbound handback checkpoints of 2026-09-26b and 2026-09-26c

This immutable archive contains the 5 terminal inbound handback receipts reviewed from the peer's `-2026-09-26b` and `-2026-09-26c` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 200,000-byte hub ceiling. Every obligation they recorded already lives in its gap owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation still resolves through the compatibility entry the hub keeps.

### Inbound 2026-09-26c handback

<a id="inbound-2026-09-26c-joined-comparison"></a>
#### Reviewed 2026-09-26c joined-comparison handback — a field copied into a field draws the class its kind pair draws in a comparison, and a Boolean field source leaves the constant ladder

a12-dmkits revision `2a55a3d0ce925cff1771da985681ce88fb6802f2` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26c`, frozen as sent in the user's exchange directory with SHA-256 `e1f975f4378a17d656bc8a8e07ab3118f131bf88ce94790a0ad6c8e47e8599f4`. Every lock the records below cite was read at that revision, not run here. It answers no ledger entry and creates none, and the `-2026-09-26c` records below share this provenance. Its §4 reports the peer's own checker and its §5 a source hypothesis, neither recorded as a claim.

**Claim.** Its §1 (`CheckerComputationJoinedConditionAgreementTest`, `kf483`), every computation writing a field of `/Order` from the root unless named. A Number into a String or Enumeration, a String or a written-out text into a Number, and `1` into a String draw `MVK_INVALID_COMPARE_TO_ENUM_OR_STRING`. A Number, String or Time into a Date and a Date into a Number or DateRange draw `MVK_INVALID_COMPARE_TO_DATE`, and a String into a DateRange `MVK_INVALID_COMPARE_TO_DATE_RANGE`. A Number into a Boolean and a Boolean into a String draw `MVK_INVALID_COMPARE_TO_YESNO`, a Boolean into a Confirm `MVK_INVALID_COMPARE_TO_YES`, and `True` into a Number `MVK_INCONSISTENT_TYPES_COMPARED`.

A Number of the other scale in either direction and `1.50` into a scale-0 Number draw `MVK_INVALID_COMPARE_DEC_PLACES`, `"PLATINUM"` into an Enumeration `MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON`, and a labelled Enumeration into an unlabelled one declaring the same values `MVK_INVALID_COMPARE_ENUM_TO_STRING`. A field of the target's own kind and scale, on each of String, Enumeration, Number, Date, Time, DateRange, Boolean and Confirm, a declared token, `True` into a Boolean or Confirm, `1` into a scale-2 Number and a Number copy under a tolerance band are admitted, while a String copy under `DiffersWithToleranceRange1` draws `MVK_INVALID_TYPE_FOR_TOLERANCE_OP`.

`[Total] + 1` and `[Total] [Note]` into a String draw the text class, the second not `MVK_UNEXPECTED_TOKEN`. The four target spellings, relative below the declaring group and absolute outside it, declared in `Billing`, at the root and in `Lines`, draw the text class alike.

**Lean.** [`LiteralComparisonDiagnostic`](../../A12Kernel/Elaboration/LiteralComparisonDiagnostic.lean) now names the generated comparison as the route and the two Boolean field cells as where a field source leaves the ladder. Lean's String and Number expression computations refuse a field source of another kind without a class, which [SG15](../gaps/targets-and-derivation.md#gap-sg15) records.

<a id="inbound-2026-09-26c-target-read"></a>
#### Reviewed 2026-09-26c target-read and member-order handback — a partially known Date or raw String read draws its read class alone, and a computation's members answer in the order A12 joins them

**Claim.** Its §2 and §3 (same lock). `[ShippedCopy]` into a `DAY_OPTIONAL` Date and `[Promised]` into a Number draw `MVK_INVALID_DATE_TYPE`, and `[Note]` into a raw String and `[Remark]` into a Number `MVK_INVALID_RAW_TYPE`, each alone. Into `Total`, with `[Shipped] > [Billing/Net]` drawing `MVK_INVALID_COMPARE_TO_DATE` and a read of the group `Billing` `MVK_NO_GROUPS_ALLOWED`, the class first in joined order answers: a precondition's date class ahead of its operation's group read and of an unresolved name there, the common precondition's ahead of an alternative precondition's group read, the first alternative's operation's group read ahead of the second alternative's precondition's date class, and an unresolved name in a precondition, `MVK_INVALID_ENTITY`, ahead of its operation's group read. Every member readable is admitted, and a refused precondition's date class answers alone ahead of a Number-into-String copy's comparison class.

**Lean.** [`StringComputation`](../../A12Kernel/Elaboration/StringComputation.lean) projects its raw-target refusal, asked ahead of the operation, to `MVK_INVALID_RAW_TYPE`, a literal source taking it by that read as an assumption. The repeatable String constant carrier's error does not separate a raw target from a custom one, and Lean's Number and String tables assemble already-checked operations, so no class is ordered across members, both recorded in [SG15](../gaps/targets-and-derivation.md#gap-sg15).

<a id="inbound-2026-09-26c-star-above-index"></a>
#### Reviewed 2026-09-26c star-above-index handback — a star on an unindexed repetition above the index group is refused even from a rule that iterates that level

**Claim.** Its §6 (`SemanticIndexWildcardPlacementLawsTest`, `kf351`, and `kf478` corrected in place). Over a repeatable `Regions` declaring no index field above a repeatable `Stores` indexed by `StoreCode`, `FirstFilledValue(Regions*/Stores For "S1") == [Title]` and `NoGroupFilled(Regions*/Stores For "S1")` declared in `/Order`, and `NoGroupFilled(/Order/Regions*/Stores For "S1")` declared in `/Order/Regions`, draw `MVK_SEMANTIC_INDEX_BELOW_WILDCARD`, while `NoGroupFilled(/Order/Regions/Stores For "S1")` declared in `/Order/Regions` is admitted. It corrects the peer's `-2026-09-25i` §2, whose star half [`spec/08`](../../spec/08-paths-and-references.md) §4 took at `f8b480ac` and dropped at `e384adb5` against `kf351`.

**Lean.** No behaviour change: [`IterationLegality`](../../A12Kernel/Conformance/IterationLegality.lean) already refused the starred read and now locks the admitted one.

### Inbound 2026-09-26b handback

<a id="inbound-2026-09-26b-dispositions"></a>
#### Reviewed 2026-09-26b field-value read handback — `SPEC-2026-09-25-09`, `-25-10` and `-26-01` confirmed on the peer's carrier

a12-dmkits revision `8f088ca71f8b82ef8d78cdd4d31c50f6c1548bae` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26b`, frozen as sent in the user's exchange directory with SHA-256 `cb140d914367e8a2a86fdeca34aa309fe1583ed9f17cf0eee6b78390da06b259`. Every lock the records below cite was read at that revision, not run here. It answers the three entries, whose ledger entries record the dispositions, and its other facts create no outbound entry. Its §4 reports the peer's own checker and its §5 a source hypothesis, neither recorded as a claim.

**Claim.** Its §1 (`CheckerFieldValueReadCarrierAgreementTest`, `kf473`). On an `/Order` carrier the Kernel answers every re-measured row of the three entries as each states it, the parallel-iteration rows not re-measured. A Number copied into an Enumeration draws `MVK_INVALID_COMPARE_TO_ENUM_OR_STRING`, from a root computation and from one declared in `Billing` reading that group's Number `Grade`.

**Lean.** No change. The confirmation adds no shape the entries' own grids lacked except the Number-into-Enumeration class, whose Lean refusal projects no class, which [SG8](../gaps/strings-and-messages.md#gap-sg8) records.

<a id="inbound-2026-09-26b-entity-list-category"></a>
#### Reviewed 2026-09-26b entity-list category handback — an Enumeration's category is refused by every entity list whose carrier refuses one, and a category behind a group draws the group class

**Claim.** Its §2 and §3 (`CheckerEntityListCategoryAgreementTest`, `kf482`), every rule at the root of `/Order` with an Enumeration `Tier` carrying the category `Level`. `Tier -> Level` draws `MVK_CATEGORY_NOT_ALLOWED` in the nine field-fill predicates, `DateRangesOverlap`, `FieldValuesNotUnique`, the three counts, the five group-list quantifiers, `GroupFilled`, `GroupNotFilled` and `RepetitionNotUnique`. Beside a repeated operand the counts still draw it while `AllFieldsFilled`, `FieldValuesNotUnique`, `AtLeastOneGroupFilled` and `RepetitionNotUnique` draw `MVK_DUPLICATE_PARAM1`, and `AllFieldsFilled(Tier -> Level, Tier)` draws the category class. `GroupFilled(Tier)` draws `MVK_NO_FIELDS_ALLOWED` and `RepetitionNotUnique(Tier, Label)` `MVK_REPEATABLE_GROUP_MISSING`. `Billing -> Level` draws `MVK_NO_GROUPS_ALLOWED` in seven entity lists, ahead of a repeat in `AtLeastOneGroupFilled`. The peer's source reading names four carriers that call the gate.

**Lean.** The shared entity-list shape takes the gate as a per-carrier position: the token `NumberOfDifferentValues` asks it ahead of the repeat, and the three routes of `FieldValuesNotUnique` and both `DateRangesOverlap` routes behind the root gate, with the measured rows and the source-read positions each locked in [`EntityListCategoryGate`](../../A12Kernel/Conformance/EntityListCategoryGate.lean). A category behind a group draws `MVK_INVALID_ENTITY` there instead of its §3 class. The carriers outside the gate and that divergence are recorded in [SG8](../gaps/strings-and-messages.md#gap-sg8).
