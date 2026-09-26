# Archived inbound handback checkpoints of 2026-09-26d and 2026-09-26e

This immutable archive contains the 5 terminal inbound handback receipts reviewed from the peer's `-2026-09-26d` and `-2026-09-26e` letters, frozen when [`../SOURCES.md`](../SOURCES.md) neared its 195,000-byte archiving threshold. Every obligation they recorded already lives in its gap owner. Stable `inbound-` anchors remain authoritative here, and every original `SOURCES.md#inbound-…` citation still resolves through the anchor the hub keeps.

### Inbound 2026-09-26e handback

<a id="inbound-2026-09-26e-labelled-target"></a>
#### Reviewed 2026-09-26e labelled-target handback — a String copied into an Enumeration draws the comparison class at a labelled target and the calculation's class at an unlabelled one

a12-dmkits revision `58a09fcdd6736770013e1e7ccca9da5fe3b47ede` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26e`, frozen as sent in the user's exchange directory with SHA-256 `3d9c9496d554dbe4f024cfc0d231c7f1b3df8a2aa7ef6e2f391eaef7bfb7b2cc`. The lock it cites was read at that revision, not run here. It answers [`SPEC-2026-09-26-03`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-26-03) and creates no entry. Its §2 reports the peer's own checker, not recorded as a claim.

**Claim.** Its §1 (`CheckerComputationJoinedConditionAgreementTest`, `kf483`). On the `/Order` carrier a root computation copying `[Label]` into `TierCopy`, an Enumeration declaring `GOLD` and `SILVER` unlabelled, draws `MVK_ERROR_INVALID_ENUM_CALCULATION`, and into `Plan`, declaring the same values labelled, `MVK_INVALID_COMPARE_ENUM_TO_STRING`. The `-25i` record's control row, a root String `[Reference]` copied into the unlabelled `Outcome`, draws the calculation class too (`KeyedOperandFamilyGateLawsTest`), which refutes the entry's `limit` that no unkeyed row existed. A keyed String source has no row into a labelled target.

**Lean.** No change: Lean's Enumeration computation refuses a String source at its operand elaboration without a class, which [SG8](../gaps/strings-and-messages.md#gap-sg8) records beside its other refused sources.

### Inbound 2026-09-26d handback

<a id="inbound-2026-09-26d-constant-typing"></a>
#### Reviewed 2026-09-26d constant-typing handback — a written-out constant is typed by its shape and the calendar before the comparison walk

a12-dmkits revision `caccdf539913bf6c77160a5e8fa0520027019ed8` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26d`, frozen as sent in the user's exchange directory with SHA-256 `931bc1cecbcd9091fdf9d218de55d6b3df92645da0bf5b5d1ae2f20355ea048e`. Every lock the records below cite was read at that revision, not run here, and the `-2026-09-26d` records below share this provenance. Its §1 answers [`SPEC-2026-09-26-02`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-26-02), accepted at `c808de4fa2540b64d57a8e4cf74545657d303270` with `kf483` corrected in place. Its §7 reports the peer's own checker and its §8 source hypotheses, none recorded as a claim.

**Claim.** Its §2 (`CheckerComparisonConstantAgreementTest`, `kf484`), each rule at the root of `/Order` behind `FieldFilled(Label)`. `[Label] == "29.02.2023"` is admitted, and opposite the Date `Shipped` that literal draws `MVK_INVALID_COMPARE_TO_DATE` under `==` and `MVK_INVALID_TYPE_FOR_COMPARISON` under `>`. `[Label] == "05.03.2024"` and `== "12:30:00"`, `[Tier] == "05.03.2024"` and `== Now`, and `[Total] > "05.03.2024"` and `> Today` draw `MVK_INVALID_COMPARE_TO_DATE`, and `[Paid] == "05.03.2024"` draws `MVK_INVALID_COMPARE_TO_YESNO`.

`[Shipped] == "05.03."` draws the date class without a Base Year and is admitted with one, as is `[Birthday] == "05.03.2024"`. `[Shipped] == "05.03.2024T12:30:00"`, `[Shipped] == Now`, `[Stamped] == Today` and `[Cutoff] == Now` draw `MVK_INVALID_COMPARE_TO_DATE`, while `[Shipped] > "05.03.2024T12:30:00"` is admitted. `[FiscalYear] == "05.03.2024"` and `[Season] == "05.03."` are admitted and `[FiscalYear] == 2024` draws the date class. `kf484` also holds `[Cutoff] > "12:30:00"` admitted and `[Cutoff] == "05.03.2024"` drawing the date class.

`[Window] == 5`, `== True` and `== "abc"` draw `MVK_INVALID_COMPARE_TO_DATE_RANGE`, and `== "05.03.2024"` and `== Today` `MVK_INVALID_COMPARE_TO_DATE`. `[Label] PatternMatched` a date or clock literal, `True` or `Today` draws `MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON`, and `PatternMatched "12:30"` is admitted. A computation copying `"05.03.2024"` into `Label`, `5` or `True` into `Shipped`, `Now` into `Cutoff` or `Today` into `Total` draws the date class, `5` into `Window` the range class, and `"05.03.2024"` into `Shipped` and `Now` into `Stamped` are admitted.

**Lean.** No behaviour change. Lean's flat surface takes a literal already typed, so the typing lives upstream of it, and its wrong-kind literal comparisons claim no class. Its flat temporal comparison admits a literal only as a Date constant, so a Time literal or a DateTime stamp is refused where the Kernel admits one, which [SG6](../gaps/numeric-and-temporal.md#gap-sg6) records.

<a id="inbound-2026-09-26d-filter-walk"></a>
#### Reviewed 2026-09-26d filter-walk handback — a key-owned filter is walked against the key, and the walk reads every spec in the body

**Claim.** Its §3 and §4 (`CheckerFilterBodyAgreementTest`, `kf485`, `kf486`) on `/Policy`, rules at the root reporting on `Reference`. After `Sum(Orders*/Units For Parties*/Name Having …) > 0` a body read of `Orders/Note`, `Claims/Notes` or `Orders/Lines/Memo` draws `MVK_INVALID_ITERATION_IN_FILTER_CONDITION`, beside `[Parties/Name]` too, `[Parties/Name]` alone draws `MVK_SEMANTIC_INDEX_WITH_WILDCARD`, `[Reference]` `MVK_NO_ITERATION_FOR_WILDCARD`, `[Orders/Note For "A"]` `MVK_SEMANTIC_INDEX_WITH_SEMANTIC_INDEX`, and `[Orders/Note] < [Orders/Units]` `MVK_INVALID_TYPE_FOR_COMPARISON`. `For Claims*/ClaimNo` answers alike, `For Parties/Name` draws `MVK_SEMANTIC_INDEX_INVALID_ITER` and `For Reference` `MVK_WILDCARDS_REQUIRED`.

Over `Claims*/Paid`, `Having Sum(Claims*/Units) > 0` draws `MVK_NO_ITERATION_FOR_WILDCARD`, and it beside `[Claims/Units] > 1`, the same beside a `Parties` star, and `Sum(Claims/Units, Claims/Paid) > 0` are admitted, while `Sum(Parties/Count, Claims/Units) > 0` draws the iteration class. `Orders*/Units Having Sum(Orders*/Lines/Qty) > 0 And [Orders/Units] > 1` draws the iteration class, `Orders*/Lines*/Qty Having Sum(Orders*/Lines/Qty) > 0 And [Orders/Lines/Qty] > 1` `MVK_NO_WILDCARD`, and `Orders*/Units Having Sum(Orders*/Lines*/Qty) > 0 And [Orders/Units] > 1`, starred at every level, is admitted.

A nested filter over `Claims*` draws `MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION`, one over `Parties*` reading `Parties/Name` or `Claims/Units` the iteration class, and one reading `Reference` `MVK_NO_ITERATION_FOR_WILDCARD`. The unstarred nested base `Claims/Units`, and `[Claims/Units] > 1` after a nested filter, draw `MVK_NO_WILDCARD`, and `[$Reference]` there `MVK_INVALID_OUTER_ITERATION`.

**Lean.** No change. Lean's `Having` surface spells no entity key, nested aggregate, nested filter or index, so none of these rows reaches it, which [SG17](../gaps/paths-and-groups.md#gap-sg17) records.

<a id="inbound-2026-09-26d-marked-read"></a>
#### Reviewed 2026-09-26d marked-read handback — a `$`-marked read in a body is judged as the rule's own read

**Claim.** Its §5 (same lock, `kf487`). From the root reporting on `Reference`, `Sum(Claims*/Paid Having [Claims/Units] > [$Claims/Units]) > 0` draws `MVK_NO_WILDCARD`, inside a nested filter too, `[$Reference] == "x" And` a nested filter draws the construct class, and `[$Claims*/Units] > 1` in a body `MVK_NO_WILDCARDS_ALLOWED`. Outside any filter `[$Claims*/Units] > 1` and `[$Orders/Note For "A"] == "x"` draw `MVK_INVALID_OUTER_ITERATION`.

From the root reporting on `Claims/Notes`, `Sum(Parties*/Count Having [Parties/Name] == [$Claims/Notes]) > 0` is admitted, `[$Parties/Name]` draws `MVK_NO_WILDCARD`, `[$Orders/Note]` `MVK_ERROR_FIELD_NO_INDEX`, `[$Claims/Notes] == "x"` alone `MVK_NO_ITERATION_FOR_WILDCARD`, and the unmarked `[Claims/Notes] == "x"` the iteration class. That marked read inside a nested filter draws the construct class, `[Parties/Name] == [$Orders/Note For "A"]` `MVK_SEMANTIC_INDEX_NOT_ALLOWED`, `[$Orders/Note For "A"] == "x"` alone `MVK_NO_ITERATION_FOR_WILDCARD`, and beside an unmarked `[Orders/Note]` the iteration class.

From `Parties` reporting on the root's `Reference`, `Sum(Claims*/Paid Having [Claims/Units] > [$Parties/Count]) > 0` draws `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`, the unmarked read the iteration class, and `[Parties/Name]` after a nested filter and the unstarred nested base `Parties/Count` the containment class.

**Lean.** No change. The rows Lean spells agree with existing locks: a marked read alone draws the no-iteration class, an unmarked one to another repetition the iteration class, and a marked read no host binds `MVK_NO_WILDCARD`, in [`FilledFieldStarCountHaving`](../../A12Kernel/Conformance/FilledFieldStarCountHaving.lean). No Lean lock places a marked read against a rule declared in a repeatable group reporting outside it.

<a id="inbound-2026-09-26d-reference-set"></a>
#### Reviewed 2026-09-26d reference-set handback — the post-parse error-field gates count only references outside every filter body and marked ones inside

**Claim.** Its §6 (`CheckerRuleReferenceSetAgreementTest`, `kf488`) on `/Shipment` with `Received` and `Expected` indexed by `LineNo` and an unkeyed `Returns`, the rule declared in `Received` reporting on `Note`. Behind `GroupFilled(/Shipment)`, nothing is admitted, `[Quantity] > 0` draws `MVK_ERROR_FIELDGROUP_ITERATION4_INVALID` and `[/Shipment/Expected/Quantity] > 0` `MVK_ERROR_FIELDGROUP_ITERATION5_INVALID`. A starred `Sum` over each of the three groups, a keyed read of `Received` or `Expected`, and an unmarked body read of `Received/Quantity` are admitted, while a body reading `[$Quantity]` draws `ITERATION4`.

`Sum(/Shipment/Received*/Quantity Having [/Shipment/Received/Note] == "x") > 0` draws `MVK_ERROR_FIELD_NOT_REFERENCED`, the same body with `[/Shipment/Received/Quantity] > 1 And [$Note] == "x"` is admitted, as is `FieldFilled(Note) And` the first body. `[Quantity] > 0 And` a body reading `GroupFilled(/Shipment)` draws `MVK_ERROR_FIELD_NOT_REFERENCED`.

**Lean.** Corrected. Lean's rule assembly counted an aggregate's or value count's filter-body unmarked read as a reference to the error field and admitted the refused row's shape, while the DateRange overlap leaves dropped a marked filter read. [`ValidationCondition.referencesErrorField`](../../A12Kernel/Elaboration/ValidationCondition/Core.lean) now counts a filter's marked reads alone on every filtered validation carrier, measured on the numeric aggregate and carried to the other filters on the assumption that a filter body is one production whatever its carrier, locked on the numeric aggregate in [`OrdinaryAdmission`](../../A12Kernel/Conformance/ValidationRule/OrdinaryAdmission.lean), on the token and Boolean value counts in [`OrdinaryReference`](../../A12Kernel/Conformance/ValidationRule/OrdinaryReference.lean) and on a DateRange overlap in [`IteratedDateRangeCondition`](../../A12Kernel/Conformance/IteratedDateRangeCondition.lean).
