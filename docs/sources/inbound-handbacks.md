# Inbound handback provenance

[Source registry](../SOURCES.md) owns authority and drill routing. The retained handbacks and historical Git stubs below preserve their original receipts and claim limits.

<a id="inbound-2026-10-09-reconciliation"></a>
## 2026-10-09 ledger reconciliation

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-09.md`, SHA-256 `523c6de0964ca3b76fc358bfd4f6f5fa45a4da7f3b638a3b4f3f86b235cdec52`; peer baseline last read by its author was local `f0e75563`. The handback covers 23 entries through SPEC-2026-10-09-08, not the later SPEC-2026-10-09-09.
- `route`: Kernel 30.8.1 through peer static `RuleValidator`/checkConsistency and runtime differentials. Dynamic Groovy is the runtime anchor; static Java and the peer interpreter are co-evidence. Exact committed findings and test assertions were inspected locally; no peer test or Kernel process was run here.
- `disposition`: The [ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) retains 21 accepted receipts and two answered receipts from this handback. These receipts do not claim complete interpreter parity or a new Lean population replay.
- `limit`: Client-SPI extensible-String constructor conversion and host bounds remain source-derived. Custom-condition factory shadowing and first-match fallback have no peer harness counterpart; interpreter preparation refusal remains declared policy.

| Entry suffix (`SPEC-2026-`) | Reviewed peer revision | Finding / executable lock |
|---|---|---|
| 10-05-01 | `f641cc24f` | KF526; KF515; `ConstructionArgumentPhaseDiffTest` |
| 10-06-01 | `f641cc24f` | KF52; `CustomConditionRegistrationReachLawsTest` |
| 10-06-02 | `f641cc24f` | KF209; `PartialBooleanValueCountDiffTest` |
| 10-06-03 | `f641cc24f` | KF527; `PartialProductCapacityDiffTest`, `PartialFillWalkRelevanceDiffTest` |
| 10-06-04 | `a1b2f45cb` | KF523; `DateComponentRelevanceDiffTest` |
| 10-06-05 | `a1b2f45cb` | KF402; KF523; `CheckerSelectedDateValidityAgreementTest`, `DateComponentRelevanceDiffTest` |
| 10-07-01 | `dce1d1bc6` | KF20; `ParentScopedIndexColumnDiffTest` |
| 10-07-02 | `dce1d1bc6` | KF522; IF376; `SelectedMessageReferenceDiffTest` |
| 10-07-03 | `dce1d1bc6` | KF64; `SelectedIterationGuardLawsTest` |
| 10-07-04 | `a1b2f45cb` | KF525; `FilterTemporalLiteralFailureDiffTest` |
| 10-07-05 | `323f53439` | KF325; `CheckerOverlapIdentityAgreementTest`, `CapturedGroupListDuplicateTest` |
| 10-08-01 | `a1b2f45cb` | KF261; `BaseYearExtractorAdmissionDiffTest`, `TemporalExtractorBaseYearGateLawsTest` |
| 10-08-02 | `a1b2f45cb` | KF524; `DifferenceOperandFailureOrderDiffTest` |
| 10-08-03 | `323f53439` | KF388; `CheckerOverlapIdentityAgreementTest` |
| 10-08-04 | `62a2b930a` | KF396; `CheckerEnumerationAdditionAgreementTest` |
| 10-09-01 | `62a2b930a` | KF390; KF401; `CheckerListAdmissionOrderAgreementTest`, `ValueListGateOrderTest` |
| 10-09-02 | `323f53439` | KF407; `CheckerComparisonOperandShapeAgreementTest` |
| 10-09-03 | `b455738d8` | KF375; KF353; `CheckerPostParseOrderAgreementTest` |
| 10-09-04 | `d81792669` | KF51; `UnregisteredPredefinedTypeAbortDiffTest` |
| 10-09-05 | `d132307f7` | KF533; `IterationBindingLawsTest`, `CheckerIterationBindingAgreementTest` |
| 10-09-06 | `d132307f7` | KF417; KF348; `CheckerIterationBindingAgreementTest`, `IterationBindingLawsTest` |
| 10-09-07 | `31d74336c` | KF535; `FirstFilledIndexNoMatchPolarityDiffTest` |
| 10-09-08 | `31d74336c` | KF536; `DeeperErrorFieldIterationDiffTest` |

- `drill`: Revisions resolve in the read-only [peer checkout](../../../a12-rulekit). Findings are in [KERNEL-FINDINGS](../../../a12-rulekit/docs/KERNEL-FINDINGS.md); test class names above locate the committed adapter, rulekit or DSL owners with `git ls-tree` at the named revision. The receipt's revision is authoritative if a current file changes.

<a id="inbound-2026-10-09-extensions"></a>
## 2026-10-09 additional observation boundaries

| Family | Reviewed peer revisions and locks | Adopted result and limit |
|---|---|---|
| Enumeration concatenation, KF530/KF396 | `797f0855b`, `8701f31d5`, `cd1de7570`, `29b665a47`; `EnumConcatenationDiffTest`, `KeyedEnumerationConcatenationLawsTest` | Stored values, not labels, contribute to admitted direct/keyed/first-filled concatenations; empty contributes no text, wholly empty clears. Categories contribute their projected values. |
| Temporal extraction, KF529/KF261 | `6ccb833b8`, `82943e3e8`, `a1b2f45cb`; `CheckerTemporalExtractorAgreementTest`, `BaseYearExtractorAdmissionDiffTest` | Partial precision precedes numeric component-format admission; projections have their separate format gate. Clock fields share the 1970 anchor. Yearless range interpretation FROM permits Year extraction without Base Year; TO was not measured. |
| Filter traversal, KF528 | `40a510808`; `FilterMissingSlotDiffTest` | Small finite-capacity filters can evaluate unstored coordinates; extent follows per-depth maxima across stored parents/groups, with a minimum of one. The original read-only scope interpretation is superseded by the [programme/target-subtree observations](#src-inbound-2026-10-09a); [H10-R6](../gaps/paths-and-groups.md#gap-sg17-closure-matrix) owns reconciliation. |
| Partial field/group traversal, KF527 | `f641cc24f`; `PartialProductCapacityDiffTest`, `PartialFillWalkRelevanceDiffTest` | Declared missing slots retain coverage obligations. First-filled, fill quantifiers, wildcard-only aggregates and products keep distinct gates. No Having traversal claim follows from this matrix. |
| Keyed temporal fields, KF531 | `daf2b8d4c`, `a57343dc7`; `KeyedTemporalOperandDiffTest`, `KeyedTemporalOperandLawsTest` | Selected partial-Date interpretation and text constructor components preserve selection, empty, poison and phase rules; Number keys and partial validation were not measured. |
| Captured operand slots, KF534 | `d00e02415`, `3e8f5a366`, `24157369b`; `CorrelatedFieldOperandDiffTest`, `CorrelatedTypedRefSlotDiffTest` | Captures retain the rule row through coercions, range operations, presence, memberships, patterns, concatenation, arithmetic, groups and constructor components. Named Valid is admission-only; keyed filter reads remain forbidden. |
| Constructor grammar, KF532/KF423 | `6979aa829`, `907c082b9`; `CheckerConstructorComponentAgreementTest`, `TemporalComponentGrammarTest` | Entity/quoted-constant/extractor grammar, parse-before-slot precedence, both conflicting orders and split-year widths/bounds are corroborated. No claim that an arbitrary numeric expression is a component. |
| Peer model readback | `d00e02415`, `9b771e466`, `3e8f5a366`, `29b665a47`, `b8954e248`, `006172739`; aggregate-pair, comparison-left and selected-Boolean read tests | Previously Opaque author/readback shapes now convert upstream. Historical captures remain unchanged; no Kernel verdict or Lean conformance gain is implied. |

- `filter-cache-source`: [CalculationCommand](../../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/core/CalculationCommand.java), `getEntityFullNamesNotRemovedFromData` / `getFieldFullNamesRelevantForCalculation`, retains ancestor groups of all expanded operand and target fields before evaluation. [GroupFillCache](../../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/core/GroupFillCache.java), `propagateEntityFilled` / `updateHighestRepetition`, supplies shared maxima by full group depth, defaulting to one.
- `filter-iterator-source`: [RuntimeController](../../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/core/RuntimeController.java), `setzeEndIndicesAufMaxGesetzt` / `combineFeldListe`, chooses bounds and consumer policy. [EbenenIterator](../../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/util/EbenenIterator.java) owns the threshold of 100, one-kept-successor prefetch and sparse reset behavior; a physical-row list is not an implementation of that sparse iterator.
- `filter-calibration-limit`: These loci use the [pinned Kernel revision](../SOURCES.md). KF528 establishes the original small-profile outcomes; the [follow-up](#src-inbound-2026-10-09a) calibrates target-only, unreached-operand and fixed-depth extensions and adds target-subtree influence. Large sparse traversal and partial relevance remain separate from that empirical matrix.

- `implementation-boundary`: These are reviewed upstream observations, not newly retained Lean replay rows. Existing implementation owners keep their finite carriers. [Temporal residuals](../gaps/numeric-and-temporal.md#gap-sg6) and [Having residuals](../gaps/paths-and-groups.md#gap-sg17-closure-matrix) retain the newly actionable checks; outbound receipts do not close them implicitly.

### Reviewed inbound batches through 2026-09-08

Deleted from this hub; the records' full text is `docs/archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing citation resolving.

<a id="reviewed-numeric-scale-continuity"></a>
- Reviewed numeric-scale continuity
<a id="reviewed-pointer-and-operator-domain-batch"></a>
- Reviewed pointer and operator-domain batch
<a id="inbound-2026-09-06-ladder-handback-detail"></a>
<a id="reviewed-group-count-multiplicity-batch"></a>
- Reviewed group-count multiplicity batch
<a id="reviewed-group-operand-extent-and-coverage-batch"></a>
- Reviewed group-operand extent and coverage batch
<a id="reviewed-compute-result-granularity-and-cascade-clear-kinds--the-axis-the-computation-rows-were-queuing-measurements-for"></a>
- Reviewed compute result-granularity and cascade clear-kinds — the axis the computation rows were queuing measurements for
<a id="inbound-2026-09-07-extremum-and-orderability-handback"></a>
<a id="reviewed-2026-09-07-handback--the-extremum-leader-set-and-the-powers-derived-scale"></a>
- Reviewed 2026-09-07 handback — the extremum leader set and the power's derived scale
<a id="reviewed-per-carrier-group-operand-admission--the-extrema-row-this-project-had-queued-was-already-held"></a>
- Reviewed per-carrier group-operand admission — the extrema row this project had queued was already held
<a id="reviewed-custom-field-type-leaf-observability-and-filtered-carrier-batch"></a>
- Reviewed custom-field-type, leaf-observability, and filtered-carrier batch

### Inbound 2026-09-05 and 2026-09-06 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-05b"></a>
- Inbound 2026 09 05b
<a id="inbound-2026-09-05c"></a>
- Inbound 2026 09 05c
<a id="inbound-2026-09-05d"></a>
- Inbound 2026 09 05d
<a id="inbound-2026-09-05e"></a>
- Inbound 2026 09 05e
<a id="inbound-2026-09-05f"></a>
- Inbound 2026 09 05f
<a id="inbound-2026-09-06b"></a>
- Inbound 2026 09 06b
<a id="inbound-2026-09-06a"></a>
- Inbound 2026 09 06a

<a id="inbound-2026-10-03"></a>
#### Reviewed 2026-10-03 peer handback

- `revision`: a12-dmkits `35ad604468360640f9f5bd9fcdc2cc6922b0b685`, verified as the clean peer HEAD on 2026-10-03. The received letter has SHA-256 `e0f175e2c9d1e43baae3c7aa56e1cd52bde5961b407585ab2af30bdbe2bc6ecc`.
- `verification`: inspected the pinned implementations, differential tests and fixtures against this project’s retained grids. Peer suites were not rerun here; executed gates are the letter’s report.
- `numeric`: KF510 / `FilterNumberComparisonAgreementTest` cover the 59 scale/direction rows; KF509 / `NumericComputationGuardDiffTest` cover 128 producer/dependent results. These reconcile SPEC-08 and SPEC-01.
- `dependencies`: KF511’s dependency implementations and tests pin 21 static cases and 14 root observations in [the fixture](../../../a12-rulekit/adapter/src/test/resources/checker-near-miss/containing-group-profiles.json). SPEC-02 acceptance covers singular GroupFilled, not ordinary lists.
- `filtered-fill`: KF512’s fill implementations and differential/replay tests check [the eighteen document/arm rows](../../../a12-rulekit/adapter/src/test/resources/filtered-fill-decisions.json), 441 full plus 441 whole-root partial signatures. These reconcile SPEC-03.
- `limits`: finite single-level Number fields and fixed-root runtime scheduling; no new CLI or protocol. Wider scopes/kinds remain outside. SPEC-04 was excluded and remains pending.

### Inbound 2026-10-02c handback

<a id="inbound-2026-10-02c"></a>
#### Reviewed pending-queue dispositions

- `revision`: a12-dmkits `5ca76014c9bdcf8b9445b84e7343ea510ae91de8`; the cited count tests and common-read correction resolve and are ancestors of this tip.
- `receipt`: the received `2026-10-02c` letter has SHA-256 `8e0773c3b83ba1657ab3dbb2bf701a33383d7ebfe64800320af6d23dac228611`. Reconciliation uses the committed tests and replay, not the letter's prose.
- `count-route`: [count-side checkpoint](../sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate) and [connective checkpoint](../sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and); SPEC-06 is accepted for firing on the fixed full-validation carrier, without transferring polarity or attachment claims.
- `self-read-route`: [alternative-walk checkpoint](../sources/computation-scheduling-probes.md#src-self-read-alternative-walk); SPEC-07 is accepted for ordered report placement and multiplicity on the three measured Number target topologies. This supersedes the earlier letter's common-first reading, not its rows.
- `scope`: SPEC-08 has no disposition in this handback. The peer's wider qualification summary is not a new local conformance claim.

### Inbound 2026-10-02a handback

<a id="inbound-2026-10-02a-provenance"></a>
#### Reviewed 2026-10-02a supplement — from two alternatives on an unguarded alternative's target reads go unjudged whatever its neighbours, each judged read reports its class in walk order, the projected class answers alone, and four division-walk controls pass or refuse as the walk predicts

The letter is the peer's `-2026-10-02a`, delivered by its session and frozen at SHA-256 `b4f98c0f12a3f470243aa75449d86a00b68e12ab03e7973fdfe41854cc680397`; it supplements the `-2026-10-02` letter. Its rows are `checkConsistency` verdicts at a12-dmkits `fb9f2720ed8d7ccd769c6566d7a8bcb4d07c3c82`, locked in adapter tests at three commits, each read here and holding the test file it names: `d56e5725afb8482de26a9dbcb737b6aa43143f6e` (`UnguardedAlternativeSelfReadAgreementTest`), `9c6e84d654062047d7b706921012b3d67acbfc90` (`SelfReadMultiplicityAgreementTest`) and `97cfb199a9d0844aa488e2ec7628b927b8750a8a` (`DivisionWalkAgreementTest`). Its carriers are root nonrepeatable targets only.

<a id="inbound-2026-10-02a-alternative-walk"></a>
**Claim.** Its §1 has two unconditional alternatives draw `MVK_ERROR_EMPTY_PRECONDITION` alone with no preconditioned neighbour, either one reading the target or both, while a sole unconditional alternative draws the target-read class; the projected class is reported in every arrangement, with no empty class beside it. Its §2 reports the plain target-read class once per judged read, a precondition's reads included, and the empty class once, at the first unconditional alternative. Its §3 has `[Amount] / [Rate] + [Rate] / [Amount]`, the same with `-`, and `[Amount] / {[Rate] / [Amount]}` reach the scale class and `{[Amount] / [Rate] / [Amount]}` draw `MVK_TOO_MANY_DIV_FOR_CALC`. Its §4 is a source reading of the division walk and a single-walk reading of §1 and §2, both offered as hypotheses.

**Classification.** Inbound from committed revisions; [`spec/09`](../../spec/09-computations.md)'s stages bullet drops its "beside a preconditioned alternative" condition and places the projected class. The letter's reading that the common precondition is judged first does not hold: this project's [alternative-walk grid](../sources/computation-scheduling-probes.md#src-self-read-alternative-walk) places it at the first judged alternative, now reconciled by the [2026-10-02c disposition](#inbound-2026-10-02c). §4 is not adopted: the spec's division-walk clause already states the cut the reading describes, and no row here separates the reading from it.

**Lean.** The Number table already left an unguarded alternative's own reads unjudged from two alternatives on, without needing a guarded neighbour. The String table now projects the empty class, and §3's four rows are locked in [`OperationNodeGates`](../../A12Kernel/Conformance/NumericComputation/OperationNodeGates.lean). The projected class against the empty class has no Lean carrier, and a String operation reading its target is refused before the table can leave it unjudged ([SG29](../gaps/paths-and-groups.md#gap-sg29), [SG7](../gaps/strings-and-messages.md#gap-sg7)).

### Inbound 2026-10-02 handback

<a id="inbound-2026-10-02-provenance"></a>
#### Reviewed 2026-10-02 handback — every pending entry from `SPEC-2026-10-01-02` to `SPEC-2026-10-02-05` holds on the peer's own carriers, a day landing's re-fit is judged against the expected date, a partially known Date is selected as its earliest day, and two more rule shapes are evaluated without content

The letter is the peer's `-2026-10-02`, delivered by its session and frozen at SHA-256 `01501b22aa9b3783e42298cfb64a344dd45712289074470da742c8e736322594`; it replaces the `-2026-10-01a` letter. Its rows are the peer's adapter tests at six a12-dmkits commits, each read here and holding the test file it names: `cd37d3ccb6df7e7094cdc1b7d77f970f50199de9` (message parameters), `d3cb6f74f66a18c7be36e5c2e1dbdc87e89006b4` (static operand gates), `b88dc54ff62cc38c72e0d04d7de213fe1a93ca25` (runtime), `3bab32bccfb30681d7c86f44c4e40b4d82a6765a` (rule buckets), `a7ed04ad35925cd2fe459965db7e9c0fafce5100` (partial-Date selection) and `ed58c5139655fe34e3d4a3305ed34a3180f10829` (day-step rows). Static rows are the Kernel's consistency check; runtime rows are dynamic Groovy, static Java and the peer's interpreter agreeing on one document. Its §12 states mechanisms its rows do not separate and is recorded as no claim.

<a id="inbound-2026-10-02-dispositions"></a>
**Claim.** Its §1 to §11 confirm the delta rows of all eleven pending entries, each on the commit its ledger entry names, and the entries are accepted on them. Beyond those rows, their additions are recorded on the entries themselves.

<a id="inbound-2026-10-02-day-landing"></a>
**Claim.** Its §7 (`ComputedDateTimeJoinDiffTest` at `b88dc54f`, `DayStepLandingDiffTest` at `ed58c513`) separates two readings of the day landing's re-fit. `AddDays(2024-10-27T00:30, 1)` gives `2024-10-28T00:30` and the peer's own `AddDays(2024-03-30T23:30, 1)` gives `2024-03-31T23:30` on both strategies, where keeping a re-fit only when it preserves the raw landing's own date gives `2024-10-27T23:30` and `2024-04-01T00:30`. `DifferenceInDays(2024-10-26T00:30, 2024-10-28T00:00)` is `1` and `(2024-03-29T23:30, 2024-03-31T23:45)` is `2`, against `2` and `1` on that reading; the peer reports the JDK's `GregorianCalendar` agreeing.

**Classification.** Inbound from committed, reviewed revisions; [`spec/05`](../../spec/05-dates-and-time.md) §5's landing bullet now names the expected date and these rows.

**Lean.** Already this account: the re-fit is compared with the expected date, and the four values are locked in [`BerlinLegacyCalendarArithmetic`](../../A12Kernel/Conformance/BerlinLegacyCalendarArithmetic.lean) and [`DateTimeDayDifference`](../../A12Kernel/Conformance/DateTimeDayDifference.lean). Its Date-source rows are not locked.

<a id="inbound-2026-10-02-partial-date-readers"></a>
**Claim.** Its §10 (`FirstFilledValuePartialDateDiffTest` at `a7ed04ad`) has `FirstFilledValue` select a partially known Date as its earliest day, `2024-06-00` as `2024-06-01` and `2024-00-00` as `2024-01-01`, directly, starred, over a group and keyed, while `0000-00-00` and a malformed value leave the selection unknown and end the walk. A copy of the selection into a full Date takes the first day, and a malformed or unknown-year value clears it. `PartialDatePresenceDiffTest` at `ed58c513` adds stored-text uniqueness at `MONTH_OPTIONAL` and `YEAR_OPTIONAL` and down a starred column.

**Classification.** Inbound; [`spec/05`](../../spec/05-dates-and-time.md)'s partial-Date paragraph takes the selection.

**Lean.** Direct-list and one-star validation/computation now re-derive the earliest-day and stopping distinctions; [the capability record](../implementation/strings-and-enumerations.md#cap-partial-date-first-filled) owns the exact matrix and remaining evidence boundary. No new kernel capture.

<a id="inbound-2026-10-02-rule-buckets"></a>
**Claim.** Its §11 (`RuleBucketGateDiffTest` at `3bab32bc`) narrows which comparisons are evaluated on an instance without content: `2 > NumberOfFilledGroups(…)`, `Abs(NumberOfFilledGroups(…)) < 2`, `NumberOfFilledFields(…) < 1` and `NumberOfDifferentValues(…) < 1` fire over the three blank documents, while `NumberOfFilledGroups(…) > 5 Or [W] < 5` stays silent. A rule naming a second root fires there too, and a rule on a repeatable root whose error field it does not iterate fires once, at the root's first row.

**Classification.** Inbound and narrowing: [`spec/03`](../../spec/03-empty-and-required.md) §2's "anywhere in either operation" no longer holds. This project's [rule-bucket grid](../sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate) measures the remaining arms before the clause is restated.

**Lean.** Diverged on the large-side row and did not count `NumberOfDifferentValues`, and its once plan gated a repeatable-root rule on the root's content; all three are corrected with that grid. The [ordinary execution owner](../implementation/validation-messages-and-custom.md#cap-ordinary-once-repeatable-execution) now records fixed cross-root numeric admission and its static content-gate projection. The same-root qualification in `spec/03` A.4 reconciles its field-only sentence with this already accepted second-root clause.

### Inbound 2026-10-01a handback

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `cdb479d937968be6e4a839191fe6cd9dd7c86fbd`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-10-01a-provenance"></a>
- Inbound 2026 10 01a provenance
<a id="inbound-2026-10-01a-event-order"></a>
- Inbound 2026 10 01a event order — [`SPEC-2026-10-01-01`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-10-01-01)
<a id="inbound-2026-10-01a-parent-walk-and-dotted-names"></a>
- Inbound 2026 10 01a parent walk and dotted names

### Inbound 2026-10-01 handback

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `cdb479d937968be6e4a839191fe6cd9dd7c86fbd`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-10-01-provenance"></a>
- Inbound 2026 10 01 provenance
<a id="inbound-2026-10-01-group-arguments"></a>
- Inbound 2026 10 01 group arguments — [`SPEC-2026-09-30-01`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-30-01)
<a id="inbound-2026-10-01-mixed-absent-product"></a>
- Inbound 2026 10 01 mixed absent product

### Inbound 2026-09-30a handback

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `a5aac437de724678adf5e96bb9681892abdb0a9d`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-30a-provenance"></a>
- Inbound 2026 09 30a provenance
<a id="inbound-2026-09-30a-message-reference-admission"></a>
- Inbound 2026 09 30a message reference admission
<a id="inbound-2026-09-30a-relative-render"></a>
- Inbound 2026 09 30a relative render
<a id="inbound-2026-09-30a-keyed-products"></a>
- Inbound 2026 09 30a keyed products
<a id="inbound-2026-09-30a-regex-operands"></a>
- Inbound 2026 09 30a regex operands

### Inbound 2026-09-28 parse-event account

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `a5aac437de724678adf5e96bb9681892abdb0a9d`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-28-parse-events"></a>
- Inbound 2026 09 28 parse events

### Inbound 2026-09-27a handback

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `a5aac437de724678adf5e96bb9681892abdb0a9d`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-27a-provenance"></a>
- Inbound 2026 09 27a provenance
<a id="inbound-2026-09-27a-variant-filter-stages"></a>
- Inbound 2026 09 27a variant filter stages
<a id="inbound-2026-09-27a-index-and-sort-lookup"></a>
- Inbound 2026 09 27a index and sort lookup
<a id="inbound-2026-09-27a-token-demand"></a>
- Inbound 2026 09 27a token demand
<a id="inbound-2026-09-27a-number-literal-whitespace"></a>
- Inbound 2026 09 27a number literal whitespace
<a id="inbound-2026-09-27a-field-message-render"></a>
- Inbound 2026 09 27a field message render
<a id="inbound-2026-09-27a-element-paths"></a>
- Inbound 2026 09 27a element paths
<a id="inbound-2026-09-27a-current-repetition"></a>
- Inbound 2026 09 27a current repetition
<a id="inbound-2026-09-27a-keyed-lower-lists"></a>
- Inbound 2026 09 27a keyed lower lists
<a id="inbound-2026-09-27a-index-key-dialect"></a>
- Inbound 2026 09 27a index key dialect
<a id="inbound-2026-09-27a-keyed-parent-stars"></a>
- Inbound 2026 09 27a keyed parent stars
<a id="inbound-2026-09-27a-consistent"></a>
- Inbound 2026 09 27a consistent

### Inbound 2026-09-26o through 2026-09-27 handbacks

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `73595edc0671fd49e6fac7ba192c5b22d0010f7f`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-27-completed-steps"></a>
- Inbound 2026 09 27 completed steps
<a id="inbound-2026-09-27-comment-placement"></a>
- Inbound 2026 09 27 comment placement
<a id="inbound-2026-09-27-count-and-list"></a>
- Inbound 2026 09 27 count and list
<a id="inbound-2026-09-26p-walked-path"></a>
- Inbound 2026 09 26p walked path
<a id="inbound-2026-09-26o-production-close"></a>
- Inbound 2026 09 26o production close

### Inbound 2026-09-26m and 2026-09-26n handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-26m-THROUGH-2026-09-26n.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26n-field-message-gates"></a>
- Inbound 2026 09 26n field message gates
<a id="inbound-2026-09-26m-message-characters"></a>
- Inbound 2026 09 26m message characters
<a id="inbound-2026-09-26m-model-texts"></a>
- Inbound 2026 09 26m model texts
<a id="inbound-2026-09-26m-error-target-paths"></a>
- Inbound 2026 09 26m error target paths
<a id="inbound-2026-09-26m-index-key-pattern"></a>
- Inbound 2026 09 26m index key pattern
<a id="inbound-2026-09-26m-marked-keyed-read"></a>
- Inbound 2026 09 26m marked keyed read

### Inbound 2026-09-26i through 2026-09-26l handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-26i-THROUGH-2026-09-26l.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26l-repeatable-root"></a>
- Inbound 2026 09 26l repeatable root
<a id="inbound-2026-09-26k-paired-gates"></a>
- Inbound 2026 09 26k paired gates
<a id="inbound-2026-09-26k-empty-star"></a>
- Inbound 2026 09 26k empty star
<a id="inbound-2026-09-26j-count-star"></a>
- Inbound 2026 09 26j count star
<a id="inbound-2026-09-26i-expansion-order"></a>
- Inbound 2026 09 26i expansion order

### Inbound 2026-09-26f through 2026-09-26h handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26h-empty-scope"></a>
- Inbound 2026 09 26h empty scope
<a id="inbound-2026-09-26h-list-reads"></a>
- Inbound 2026 09 26h list reads
<a id="inbound-2026-09-26g-type-match"></a>
- Inbound 2026 09 26g type match
<a id="inbound-2026-09-26f-gate-order"></a>
- Inbound 2026 09 26f gate order

### Inbound 2026-09-26d and 2026-09-26e handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26e-labelled-target"></a>
- Inbound 2026 09 26e labelled target
<a id="inbound-2026-09-26d-constant-typing"></a>
- Inbound 2026 09 26d constant typing
<a id="inbound-2026-09-26d-filter-walk"></a>
- Inbound 2026 09 26d filter walk
<a id="inbound-2026-09-26d-marked-read"></a>
- Inbound 2026 09 26d marked read
<a id="inbound-2026-09-26d-reference-set"></a>
- Inbound 2026 09 26d reference set

### Inbound 2026-09-26b and 2026-09-26c handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26c-joined-comparison"></a>
- Inbound 2026 09 26c joined comparison
<a id="inbound-2026-09-26c-target-read"></a>
- Inbound 2026 09 26c target read
<a id="inbound-2026-09-26c-star-above-index"></a>
- Inbound 2026 09 26c star above index
<a id="inbound-2026-09-26b-dispositions"></a>
- Inbound 2026 09 26b dispositions
<a id="inbound-2026-09-26b-entity-list-category"></a>
- Inbound 2026 09 26b entity list category

### Inbound 2026-09-25i and 2026-09-26 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25i-key-addressing"></a>
- Inbound 2026 09 25i key addressing
<a id="inbound-2026-09-25i-literal-key"></a>
- Inbound 2026 09 25i literal key
<a id="inbound-2026-09-25i-rule-iteration"></a>
- Inbound 2026 09 25i rule iteration
<a id="inbound-2026-09-25i-keyed-duplicate"></a>
- Inbound 2026 09 25i keyed duplicate
<a id="inbound-2026-09-25i-enum-source"></a>
- Inbound 2026 09 25i enum source
<a id="inbound-2026-09-26-climbing-read"></a>
- Inbound 2026 09 26 climbing read
<a id="inbound-2026-09-26-index-key-shape"></a>
- Inbound 2026 09 26 index key shape

### Inbound 2026-09-25g and 2026-09-25h handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25g-value-list-order"></a>
- Inbound 2026 09 25g value list order
<a id="inbound-2026-09-25g-date-class"></a>
- Inbound 2026 09 25g date class
<a id="inbound-2026-09-25g-field-value-read"></a>
- Inbound 2026 09 25g field value read
<a id="inbound-2026-09-25g-rounding-mode"></a>
- Inbound 2026 09 25g rounding mode
<a id="inbound-2026-09-25g-banded-rounding"></a>
- Inbound 2026 09 25g banded rounding
<a id="inbound-2026-09-25g-keyed-group"></a>
- Inbound 2026 09 25g keyed group
<a id="inbound-2026-09-25h-category-index-relevance"></a>
- Inbound 2026 09 25h category index relevance

### Inbound 2026-09-25e and 2026-09-25f handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25f-value-list-base-type"></a>
- Inbound 2026 09 25f value list base type
<a id="inbound-2026-09-25f-field-value-read"></a>
- Inbound 2026 09 25f field value read
<a id="inbound-2026-09-25f-generated-text"></a>
- Inbound 2026 09 25f generated text
<a id="inbound-2026-09-25f-bare-entity"></a>
- Inbound 2026 09 25f bare entity
<a id="inbound-2026-09-25e-below-star-placement"></a>
- Inbound 2026 09 25e below star placement
<a id="inbound-2026-09-25e-sum-of-products-reach"></a>
- Inbound 2026 09 25e sum of products reach
<a id="inbound-2026-09-25e-value-list-base-type"></a>
- Inbound 2026 09 25e value list base type
<a id="inbound-2026-09-25e-comparison-arm-order"></a>
- Inbound 2026 09 25e comparison arm order

### Inbound 2026-09-25b and 2026-09-25c handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25b-index-type-table"></a>
- Inbound 2026 09 25b index type table
<a id="inbound-2026-09-25b-condition-class-order"></a>
- Inbound 2026 09 25b condition class order
<a id="inbound-2026-09-25b-condition-positions"></a>
- Inbound 2026 09 25b condition positions
<a id="inbound-2026-09-25b-computation-texts"></a>
- Inbound 2026 09 25b computation texts
<a id="inbound-2026-09-25b-message"></a>
- Inbound 2026 09 25b message
<a id="inbound-2026-09-25b-joint-level-slots"></a>
- Inbound 2026 09 25b joint level slots
<a id="inbound-2026-09-25c-gate-raise-points"></a>
- Inbound 2026 09 25c gate raise points
<a id="inbound-2026-09-25c-form-keyword"></a>
- Inbound 2026 09 25c form keyword
<a id="inbound-2026-09-25c-key-filter"></a>
- Inbound 2026 09 25c key filter
<a id="inbound-2026-09-25c-filter-body"></a>
- Inbound 2026 09 25c filter body
<a id="inbound-2026-09-25c-calculation-stages"></a>
- Inbound 2026 09 25c calculation stages

### Inbound 2026-09-24c through 2026-09-25 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25-fixed-group-star"></a>
- Inbound 2026 09 25 fixed group star
<a id="inbound-2026-09-25-message-withheld"></a>
- Inbound 2026 09 25 message withheld
<a id="inbound-2026-09-25-keyed-group-walk"></a>
- Inbound 2026 09 25 keyed group walk
<a id="inbound-2026-09-25-bare-group-placement"></a>
- Inbound 2026 09 25 bare group placement
<a id="inbound-2026-09-25-comment-terminators"></a>
- Inbound 2026 09 25 comment terminators
<a id="inbound-2026-09-25-operator-gates-wait"></a>
- Inbound 2026 09 25 operator gates wait
<a id="inbound-2026-09-25-parallel-index-gates"></a>
- Inbound 2026 09 25 parallel index gates
<a id="inbound-2026-09-24e-misplaced-star"></a>
- Inbound 2026 09 24e misplaced star
<a id="inbound-2026-09-24e-nested-partial-star"></a>
- Inbound 2026 09 24e nested partial star
<a id="inbound-2026-09-24e-message-withheld"></a>
- Inbound 2026 09 24e message withheld
<a id="inbound-2026-09-24e-filter-leaf"></a>
- Inbound 2026 09 24e filter leaf
<a id="inbound-2026-09-24d-star-containment"></a>
- Inbound 2026 09 24d star containment
<a id="inbound-2026-09-24d-mixed-group-count"></a>
- Inbound 2026 09 24d mixed group count
<a id="inbound-2026-09-24c-path-walk"></a>
- Inbound 2026 09 24c path walk
<a id="inbound-2026-09-24c-field-slot"></a>
- Inbound 2026 09 24c field slot
<a id="inbound-2026-09-24c-group-operand-walk"></a>
- Inbound 2026 09 24c group operand walk

### Inbound 2026-09-24 and 2026-09-24b handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-24b-keyed-partial-read"></a>
- Inbound 2026 09 24b keyed partial read
<a id="inbound-2026-09-24b-lexer-and-blank-text"></a>
- Inbound 2026 09 24b lexer and blank text
<a id="inbound-2026-09-24b-category-read-poison"></a>
- Inbound 2026 09 24b category read poison
<a id="inbound-2026-09-24b-kf463-validation"></a>
- Inbound 2026 09 24b kf463 validation
<a id="inbound-2026-09-24b-kf464-partial-group-extent"></a>
- Inbound 2026 09 24b kf464 partial group extent
<a id="inbound-2026-09-24b-kf464-partial-group-count"></a>
- Inbound 2026 09 24b kf464 partial group count
<a id="inbound-2026-09-24b-dispositions"></a>
- Inbound 2026 09 24b dispositions
<a id="inbound-2026-09-24-ancestor-starred-group-count"></a>
- Inbound 2026 09 24 ancestor starred group count

### Inbound 2026-09-23 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-23d-grandparent-fill-and-malformed-key"></a>
- Inbound 2026 09 23d grandparent fill and malformed key
<a id="inbound-2026-09-23c-computation-cascade-reads"></a>
- Inbound 2026 09 23c computation cascade reads
<a id="inbound-2026-09-23b-entity-list-operand-reads"></a>
- Inbound 2026 09 23b entity list operand reads
<a id="inbound-2026-09-23-first-filled-gate-positions"></a>
- Inbound 2026 09 23 first filled gate positions
<a id="inbound-2026-09-23-entity-list-root-group-gate"></a>
- Inbound 2026 09 23 entity list root group gate
<a id="inbound-2026-09-22e-first-filled-gate-order"></a>
- Inbound 2026 09 22e first filled gate order

### Inbound 2026-09-22 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-22.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-22d-first-filled-cross-kind"></a>
- Inbound 2026 09 22d first filled cross kind
<a id="inbound-2026-09-22-temporal-category"></a>
- Inbound 2026 09 22 temporal category
<a id="inbound-2026-09-22-dispositions"></a>
- Inbound 2026 09 22 dispositions

### Inbound 2026-09-21 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-21.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-21b-corrections"></a>
- Inbound 2026 09 21b corrections
<a id="inbound-2026-09-21-corrections"></a>
- Inbound 2026 09 21 corrections

### Inbound 2026-09-07 and 2026-09-08 handbacks

Deleted from this hub; the records' full text is `docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-08-corrections"></a>
- Inbound 2026 09 08 corrections
<a id="inbound-2026-09-08-instrument"></a>
- Inbound 2026 09 08 instrument
<a id="inbound-2026-09-08"></a>
- Inbound 2026 09 08
<a id="inbound-2026-09-07-dispositions"></a>
- Inbound 2026 09 07 dispositions

- `stored-gap`: Reviewed a12-dmkits `a56a825941c1ce393ae2deaf8b604f5023f39f44`: a stored `2024-03-31T02:30:00` on Europe/Berlin suppresses its referencing rule rather than normalizing forward. `DstTimeZoneDiffTest.gapWallTimeIsAFormalError` and KF6 supply the retained corroboration.
- `limit`: The differential's code assertion is on the peer interpreter; the every-era generalization rests on a `SimpleDateFormat` parser probe, not a Kernel differential. [Terminal disposition](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-07-08).

<a id="src-inbound-2026-10-09a"></a>
## October 9 follow-up: guards, programme scope and stored reads

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-09a.md`, SHA-256 `09abbc5db52f605770f39a8d4392253a8e2677e6cecaa29ef81e351ae9130398`. Exact reviewed peer revision: `59b94e1e5f0801af264ce8df8afbb76aae91250a`; local baseline `11493f71`.
- `route`: Kernel 30.8.1; committed static and runtime test assertions inspected, not rerun here. Runtime tests compare dynamic Groovy, static Java and the peer interpreter. No new local capture, replay or implementation closure follows from this receipt.
- `guards`: KF537 and corrected KF435: `ParallelGuardConnectiveLawsTest`, `IterationGuardNestedCompositionLawsTest` and `ParallelGuardConnectiveDiffTest` corroborate recursive And/Or guards on parallel and ordinary levels. Every disjunct must guard the level; off-level positives do not. The unfiltered Sum control separates filter-combination precedence.
- `messages`: KF539: `ParallelGuardConnectiveDiffTest` compares reference and fill-to-fix pointers through `DocumentDifferential`. A joined group's referenced payload brings its index field into the corresponding list; the single-group control does not. [SG10](../gaps/strings-and-messages.md#gap-sg10) owns executable reconciliation.
- `extent`: KF528: `FilterCacheScopeDiffTest` corroborates target-only and unreached static reads, full path depth including fixed groups, and whole-programme scope for a subplan. Its capacity-150 control does not establish arbitrary sparse traversal or partial validation.
- `target-subtree`: KF538: `ComputeTargetSubgroupScopeDiffTest` distinguishes a target's innermost repeatable group's descendants from only its ancestors. Nested repeatable groups contribute to filter extents even when no computation names them. Declaring the target's computation in its parent does not change the selected subtree.
- `formal`: KF538: `ComputeFormalScopeDiffTest` and the subgroup test include uncomputed descendants in formal and over-limit findings. An inner target excludes an invalid field in its outer repeatable parent; root-only targets add no subtree. The internal Kernel mechanism responsible for target-derived inclusion remains unidentified.
- `decimal`: KF1: `A12JsonIngressKernelTest` pins native/quoted Number and String inputs, signed zero, scientific thresholds and a native `1e999999999` String value. Numeric document-id conversion is source-read only; assertions prevented measurement. [Wire provenance](cross-layer-routes.md#src-number-wire-ingestion) owns the probe revision boundary.
- `ranges`: KF540: `DateRangeSharedRuntimeDiffTest` and `DateRangeSharedFormatOrderDiffTest` corroborate all eight source profiles, both interpretations, default/configured year and the additional-check partition. Measured first profiles remain dotted and month-only, in UTC on direct nonrepeatable sources, without pre-1900 values.
- `readback`: `ComputedDateStoredReadDiffTest` pins yearless Date rollover back to Base Year on dependent read. The range matrix compares dependent reads of cross-interpretation targets. Readback consumes target storage rather than preserving discarded expression components; [SG6](../gaps/numeric-and-temporal.md#gap-sg6) owns the executable audit.
- `earlier-receipts`: No new executable receipt is issued for KF184 fill-to-fix scope, KF410 root spellings, KF522 fill-to-fix, KF416, KF109, KF527 or KF529. The earlier letter's acceptance of outbound entries does not establish these distinct obligations; keep the peer's reopened rows open pending exact guards.
- `sync`: The [ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) retains dispositions for SPEC-2026-10-09-09 through -12. These inbound additions create no outbound request. Canonical corrections are in [iteration](../../spec/07-repetition-and-iteration.md) and [computation](../../spec/09-computations.md).

<a id="src-inbound-2026-10-12"></a>
## Reviewed October 12 consolidated peer response

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-11a.md`, SHA-256 `df4973bc98f3032b6e914bdd7e71405d0b08ab60387541a531a94748837578b0`; the consolidated letter is dated 2026-10-12 and answers the 24 ledger entries below.
- `revision`: Reviewed a12-dmkits `c0a564ad30ab0baf41c4b4cac33e5452b39993a4`; every principal checkpoint below resolves and is its ancestor. Committed files were read with `git show` at this revision rather than from the sibling working tree.
- `review`: Source-reading review inspected named peer clean-room test assertions and findings against each existing acceptance condition. No peer suites, Kernel calls or local replay were run for this receipt.
- `receipt`: [The reconciliation ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue) owns current dispositions, including the subsequent [profile clarification](custom-field-probes.md#src-custom-legacy-profile). Acceptance does not certify universal peer compatibility or widen the original finite profiles.
- `if376`: [The peer policy](../../../a12-rulekit/docs/INTERPRETER-FINDINGS.md#if376) retains first-admitted duplicate selected/parallel pointers. Reviewed tests pin Kernel winners separately or project only a coherent concrete duplicate association; this is a compatibility difference, not contrary Kernel evidence.
- `comparator`: `DocumentDifferential.MessageSignature` retains full error/reference/fill pointer coordinates, including group terminals. It does not compare severity or localized text; separate `assertMessageTexts` controls compare exact text and address. Reported retained replay totals were not independently checked here.
- `reserved-limit`: [The legacy profile checkpoint](custom-field-probes.md#src-custom-legacy-profile) owns the unmeasured true-arm continuation limit and reopening trigger. The modern observations remain evidence for K01, not proof of local implementation.
- `canonical-limit`: [KF541](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf541) retains its canonical fold as pending. [The peer API contract](../../../a12-rulekit/docs/INTERPRETER-API-SPEC.md) carries raw callback input, one-pass evaluated normalization and the exact reserved result; the canonical kernel-truth prose has not explicitly folded `testIDNummer`.
- `follow-on`: Enclosing-row Having and fixed-suffix relevance are reviewed candidate evidence routes for [path/group obligations](../gaps/paths-and-groups.md). Their local coverage remains to be checked under K03/K06; the receipt does not establish local conformance.
- `computation-assembly`: [The duplicate-diagnostic checkpoint](#src-computation-diagnostic-assembly) owns the committed controls and source mechanism, outside the 24 receipt decisions.
- `qualification`: Integration, JVM/Node, performance and mutant outcomes remain peer-reported. They were not rerun or certified by this source-reading review.

| SPEC-2026 suffix | Checkpoint | Committed test class | Status |
|---|---|---|---|
| 10-10-01 | `282bb9c52` | `ComputeAuthoredGuardScopeDiffTest` | accepted |
| 10-10-02 | `28749bce0` | `SparseFilteredAggregateDiffTest` | accepted |
| 10-10-03 | `8299a1760` | `SelectedAuthoredScopeDiffTest` | accepted |
| 10-10-04 | `d90ef09a8` | `NumericIndexKeyDiffTest` | accepted |
| 10-10-05 | `1dc5d5dca` | `ParallelValidationDispatchDiffTest` | answered |
| 10-10-06 | `1dc5d5dca` | `SelectedMessageReferenceDiffTest` | answered |
| 10-10-07 | `38cdc9839` | `A12JsonIngressDiffTest` | accepted |
| 10-10-08 | `1dc5d5dca` | `SelectedMessageReferenceDiffTest` | answered |
| 10-10-09 | `1dc5d5dca` | `SelectedMessageReferenceDiffTest` | answered |
| 10-10-10 | `1dc5d5dca` | `ParallelValidationDispatchDiffTest` | answered |
| 10-10-11 | `0047d5e0c` | `CustomTestRangeLawsTest` | accepted |
| 10-10-12 | `0047d5e0c` | `CustomTestRangeLawsTest` | [answered](custom-field-probes.md#src-custom-legacy-profile) |
| 10-10-13 | `a4c920ca4` | `EmptyAuthoredPatternDiffTest` | accepted |
| 10-10-14 | `67c7f0957` | `FirstFilledNestedPrefixDiffTest` | accepted |
| 10-10-15 | `9da38987d` | `PartialDeclaredListExtentDiffTest` | accepted |
| 10-10-16 | `717568297` | `SelectedGroupValueListDiffTest` | accepted |
| 10-10-17 | `e72f3145a` | `MultiLevelStarredGroupCountDiffTest` | accepted |
| 10-10-18 | `7511f051a` | `OverRepetitionOccurrenceDiffTest` | accepted |
| 10-10-19 | `e72f3145a` | `PartialGroupCountRelevanceDiffTest` | accepted |
| 10-10-20 | `28135b68b` | `PartialStarredGroupCoverageDiffTest` | accepted |
| 10-10-21 | `28135b68b` | `PartialStarredGroupCoverageDiffTest` | accepted |
| 10-10-22 | `a33993cce` | `PartialParentGroupCoverageDiffTest` | accepted |
| 10-11-01 | `5d6900c42` | `SelectedMessageReferenceDiffTest` | accepted |
| 10-11-02 | `2242a6141` | `InvalidModelLoadDiagnosticTest` | accepted |

- `drill`: Runtime classes above are under `adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/` in the read-only [peer checkout](../../../a12-rulekit). `InvalidModelLoadDiagnosticTest` is under `cli/src/test/java/io/github/mbackschat/a12/dm/cli/`. The reviewed revision is authoritative when current files change.
- `additional-locks`: SPEC-02 also uses `SparseFilteredFillDiffTest`, `SparseMembershipTraversalDiffTest`, `DenseUniquenessPrefixDiffTest` and `SparseOverlapPolicyDiffTest`.
- `additional-locks`: SPEC-03 uses `SemanticKeyAddressAgreementTest`, `SelectedParallelUniquenessAgreementTest` and `SelectedContainmentAgreementTest`.
- `additional-locks`: SPEC-17 includes `AncestorStarredGroupCountComputationDiffTest`.
- `additional-locks`: SPEC-18 includes `OverRepetitionAncestorCacheDiffTest`.
- `additional-locks`: SPEC-11-01 includes `RuleMessageParameterRenderingDiffTest` and `ParallelValidationDispatchDiffTest`.
- `additional-locks`: SPEC-11-02 includes `RuleSlotLawsTest` and `ComputationSlotLawsTest`.

<a id="src-computation-clear-observability"></a>
#### Public result projection erases clear validity, audited October 12

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-12.md`, 407a87084bb8843fb494bfe92679a96cf1c716ff0cca90dd3b84bd868b0786a0-256 `407a87084bb8843fb494bfe92679a96cf1c716ff0cca90dd3b84bd868b0786a0`; exact peer revision `20a5f36b1e325ab597ad2349c840707a8a8d97ba`. This instrument response is separate from [the consolidated ledger response](#src-inbound-2026-10-12).
- `review`: Inspected the committed KF240 correction, existing `DependencyClearKindDiffTest` and `ComputedDependencyCauseErasureDiffTest` routes, and the source-owned [CLI reproduction](../../../a12-rulekit/docs/KERNEL-PROBE-SPEC.md#distinguishing-cleared-targets). Existing Lean [dependency controls](../../A12Kernel/Conformance/NumericDependency.lean) already distinguish clean empty from poisoned reads.
- `reported-observation`: The four-row Number source/guard batch retains seeded Target/Reader. A malformed source with an absent guard clears Target and yields Reader=0; an enabled guard clears both. Target flags and the source-error inventory agree between those rows. Valid source/guard is the positive control. The peer ran both strategies; this receipt adds no locally replayed artifact.
- `mechanism`: At Kernel `cb66e51fa7ab90b650698f861bf670754e2e1e66`, `CalculationCache.getBerechneteFelder` exports values and clears without private invalid-field membership. `DocumentComputationResultImpl.init` synthesizes remaining clears as empty instances. Both loci and the public `IDocumentComputationResult` / `IComputedFieldInstance` interfaces were read locally.
- `denominator`: The audited public computation-result and computed-instance APIs, their result assembly, and the existing validateFull/compute/computeResults probe projections. Internal cache instrumentation and hypothetical future API additions are outside this claim.
- `claim`: These public result channels expose neither per-clear validity nor causal attribution. Error messages cover actual errored results; they do not restore silent poison. Formal operand errors are an inventory, not a cause graph.
- `method`: Seed the target and a numeric-copy dependent in the same call. The dependent distinguishes clean emptiness from poison; it does not uniquely identify an originating cause. An unseeded aborted target can be absent from the change projection.
- `disposition`: Instrument inquiry answered with an API boundary, not a missing adapter field. No inference field, new harness or outbound ledger entry is warranted. Reopen direct exposure only if the public API gains the information.

<a id="src-computation-diagnostic-assembly"></a>
#### Computation diagnostic assembly — Kernel source and peer law tests, 2026-10-12

- `source`: Inbound a12-dmkits `6b919e0870e36b9da7f33e6735ea7821474e68a0`, retained in reviewed `c0a564ad30ab0baf41c4b4cac33e5452b39993a4`; [ComputationDiagnosticAssemblyLawsTest](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ComputationDiagnosticAssemblyLawsTest.kt).
- `oracle`: Seven witnesses on both Kernel strategies cover reserved duplicate, accepted duplicate, reserved distinct, rejected distinct, unused collision, separate target errors and collision after an independent callback. Public compute/apply calls and original-document preservation are asserted separately.
- `mechanism`: Kernel `cb66e51fa7ab90b650698f861bf670754e2e1e66`, `kernel-md/kernel-md-runtime-service/src/main/java/com/mgmtp/a12/kernel/md/rt/a12internal/service/DocumentComputationResultImpl.java`, `init`: the complete result-message stream is keyed by full error pointer before target classification, with duplicate keys rejected.
- `claim`: Computation completes before duplicate report assembly fails. Distinct physical rows remain distinct; reserved Custom reports do not override index unavailability. Root-only computation ignores an unused custom index. No result or applied snapshot exists on the assembly-failure arm.
- `limit`: The tests establish duplicate-key failure, not a portable choice of which collision wins when several pointers repeat. Exact exception text beyond the asserted prefix is not a language-neutral contract. The peer's separate first-admitted pointer policy does not replace this Kernel result-assembly oracle.
- `local`: [The implementation owner](../implementation/validation-messages-and-custom.md#cap-computation-message-partition) separates raw execution, checked assembly and projection. The ordinary malformed-source twin is an internal composition control, not a newly measured Kernel witness.
- `sync`: Inbound correction to [computation §3.3](../../spec/09-computations.md#33-what-compute-reports); no outbound acknowledgement request is created.

<a id="src-inbound-kf558-multiplicity"></a>
#### Model-check class multiplicity, peer KF558 at a12-dmkits `18dd8a23dedbdfc96bc62a6b0832c8aea4645430`, reconciled 2026-10-13

- `source`: [KF558](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf558), committed at the revision above, which also corrects the peer's distinct-only laws instrument.
- `local-confirmation`: rows `m-two-locales-no-text`, `m-three-locales-one-text` and `m-two-locales-two-empty` of the [R1 supplement](model-structure-and-declaration-probes.md#src-sort-list-capacity) reproduce the per-locale `RULE_HAS_NO_ERRORTEXT` at the measurement pin; [report locks](../../A12Kernel/Conformance/DeclarationReport.lean) assert them.
- `routing`: inbound, so no outbound ledger entry. The xml-prefix, value-validation-off String and unspecified-type multiplicities have no local implementation and join [K17](../PLAN.md#k17--model-declarations-and-static-denominator)'s matrix.

<a id="src-inbound-2026-10-18"></a>
## Reviewed October 18 peer response

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-18.md`, SHA-256 `b026cbcfb6d313f796f2838dfc1f1f3b289f21c32c48e88b10be58b4e7396528`. It answers the sixteen pending entries `SPEC-2026-10-13-13` to `-16` and `SPEC-2026-10-14-01` to `-12` as committed at `84f50280`.
- `revision`: Reviewed a12-dmkits `d26873580`. Every checkpoint the letter names resolves, and every named lock class exists there; files were read with `git show` at this revision.
- `review`: A read-only HIGH review of the named Kernel-differential, `checkConsistency` and `rule check` assertions against each acceptance condition. No peer suite, Kernel call or replay of ours was run; the peer's replays of our captures through its interpreter and checker, and its lane counts, are peer-reported.
- `receipt`: [The reconciliation ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue) owns the per-entry dispositions.

| SPEC-2026 suffix | Committed lock class | Status |
|---|---|---|
| 10-13-13 | `NumberDeclarationIngressDiffTest` | accepted, extended |
| 10-13-14 | none | answered |
| 10-13-15 | `NumberDeclarationIngressDiffTest` | accepted |
| 10-13-16 | `CheckerDeclarationAdmissionAgreementTest`, `ShortNameFlagSpellingLawsTest`, `BooleanMemberBindingDiffTest`, `IndexDefaultStagingDiffTest` | accepted, corrected |
| 10-14-01 | none | answered |
| 10-14-02 | `ValidityConditionOperandLawsTest` | accepted, extended |
| 10-14-03 | `JoinedRowAggregateDiffTest` | accepted, extended |
| 10-14-04 | `EmptyEnumerationTokenDiffTest` | accepted, extended |
| 10-14-05 | `CheckerConditionCallOperandAgreementTest` | accepted |
| 10-14-06 | `CheckerKeyedReadErrorReferenceAgreementTest`, `JoinedRowAggregateDiffTest` | accepted |
| 10-14-07 | `KeyedNotAllFieldsFilledDiffTest` | accepted, extended |
| 10-14-08 | `CheckerSumOfProductsBoundOperandAgreementTest`, `SumOfProductsLawsTest` | accepted, extended |
| 10-14-09 | `RepetitionNotUniqueSiblingGroupKeyDiffTest` | accepted, extended |
| 10-14-10 | `RequirednessTextSubstitutionDiffTest` | accepted, corrected |
| 10-14-11 | `RuleConditionPreambleDiffTest`, `ScaleWaiverLanguageLawsTest`, `CheckerScaleWaiverAgreementTest` | accepted, extended |
| 10-14-12 | `JoinedSideChildReadDiffTest` | accepted, extended |

- `correction-a`: A boolean member binds by Java's `trim` and six exact spellings, the empty text and the text `null` being the default; our account read the text `true` in any letter case as set and every padded text as unreadable. The law binds every primitive boolean member, before the variant filter ([spec/01 §1.1](../../spec/01-data-model.md#member-binding), [locks](../../A12Kernel/Reference/Dm/MemberBindingLocks.lean)). The spellings `1e0` and `-0` are Kernel rows since the [October 22 answers](#src-inbound-2026-10-22).
- `correction-b`: An `sValue` is judged after `trim` against trimmed tokens, so `" BASIC"` names `BASIC` ([spec/01 §1.3](../../spec/01-data-model.md#13-declaration-generation-classes), [conformance](../../A12Kernel/Conformance/FieldTypeDeclarationNotification.lean)). The runtime stages a padded default as written, which the [written-member locks](../../A12Kernel/Reference/Dm/WrittenMemberLocks.lean) hold with peer KF574's rows.
- `correction-c`: The requiredness text replaces a fifth literal token, `$<fieldName>.Value$`, before the other four, and each pass reads the running text, so a token a label carries in meets every later pass; a German-condition model replaces both languages' tokens (rows `r10`–`r14`, `d01`; [spec/11](../../spec/11-messages-and-custom.md#part-a--13-error-message-interpolation), [locks](../../A12Kernel/Reference/Dm/FieldMessageTextLocks.lean)).
- `extension`: `Valid` and `Invalid` parse only `Date(...)` or a field and a type name ([spec/05 §3](../../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity)); `SumOfProducts`' lowest-level class needs no star once the level is bound, and its filter and star gates run operand by operand from the left ([spec/07](../../spec/07-repetition-and-iteration.md)). The [refusal-class locks](../../A12Kernel/Reference/Dm/RefusalClassLocks.lean) draw each family's class through the reader.
- `replay-only`: These acceptance rows rest on the peer's replay of our captures rather than a committed Kernel lock: `-13-13`'s cascade order, `-14-02`'s `v01`–`v16` and `g01`–`g20` with its runtime rows, `-14-06`'s values and references, `-14-09`'s static refusals, `-14-10`'s `q01`–`q23`, `rq` and `n01`–`n07`, `-14-11`'s static verdicts, on which the checker answers inconclusive, and `-14-12`'s filtered-star classes. Our own captures remain their Kernel evidence.
- `answered`: `-13-14` found no contradiction and claims no notification order; `-14-01`'s parallel refusals fell under a peer scoping decision, which the peer withdrew on 2026-10-22 ([October 22 answers](#src-inbound-2026-10-22)) before sending Kernel rows for both classes ([October 22b rows](#src-inbound-2026-10-22b)). Neither reconciles its acceptance rows.
- `instrument`: The kernel-probe request now carries a `customConditions` key (`bf56df1cd`, `14818d417`, lock `KernelProbeCustomConditionTest`), the capability [K18](../PLAN.md#k18--customcondition-callback-contract-and-calibration) waits on; the measurement checkout was [re-pinned](cross-layer-routes.md#src-measurement-checkout-route) to carry it on 2026-10-22.
- `sync`: Inbound corrections to clauses this project owns; no outbound ledger entry is created.

<a id="src-inbound-2026-10-21"></a>
## Reviewed October 21 peer measurements

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-21.md`, SHA-256 `f3b764cfdfaf0ee0c2d495b445ed0d2e8a8d1ce98df63e4348051827de0574f0`, at a12-dmkits `dbbbdb5d8`. It answers no entry: every row is a Kernel fact the peer measured on its own models.
- `review`: A read-only HIGH triage of every row against `spec/` and the Lean theory at `63813608`, classifying agreement, contradiction and new behaviour. The rows' own revisions and locks were not reread; they are peer-reported Kernel outcomes. The letter's source readings and Section 4 hypotheses are not adopted as mechanisms.
- `implemented`: the boolean and `int` binding laws, with the base year, the bound text `null` and a count below one (§1.3, §2.17–§2.22); the document Boolean cell's `equalsIgnoreCase` fold (§1.13); date constants typed on the hybrid calendar (§2.15, §1.12). [Locks](../../A12Kernel/Reference/Dm/MemberBindingLocks.lean). Rule readers judging an out-of-range length (§2.2), stated in [spec/01 §1](../../spec/01-data-model.md#1-model--a-typed-tree) and [spec/04](../../spec/04-numbers-and-decimals.md); [locks](../../A12Kernel/Reference/Dm/WrittenMemberLocks.lean).
- `implemented`: the declaration rows of §2.1, §2.3–§2.8, §2.11, §2.12, §2.16 and §2.17 on the letter's hosts: the inversion withheld beside a refused printed bound, trimmed Enumeration texts and the supplementary withholding, trimmed executable alphabets and the deleted rule's empty-code notification, the group-path law over each element's trimmed path, the composed range format, a blank date format, blank names, the computed-path class with the operation and index classes before it beneath a refused group name, the ordering member and its gates, and the count class beneath a group. [Walk locks](../../A12Kernel/Reference/Dm/DeclarationWalkLocks.lean), [admission locks](../../A12Kernel/Reference/Dm/DeclarationAdmissionLocks.lean), [element-name locks](../../A12Kernel/Conformance/ElementNameNotification.lean).
- `implemented`: `Today`, `Now`, a pre-cutover Date or DateTime constant and a Base Year before the cutover valued on the hybrid calendar (§1.2, §1.12, §2.15), through the [model-zone label](../implementation/temporal.md#cap-model-zone-profile). [Locks](../../A12Kernel/Reference/Dm/HybridCalendarLocks.lean).
- `correction`: spec/01 had read §2.8 as an absent separator composing blank; peer [KF581](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf581) composes it as `/`, so only an empty or blank separator beside a blank format draws the missing class.
- `agrees`: §1.1 and §2.14 (ASCII digits, stated in [spec/12 §1](../../spec/12-concrete-syntax.md#1-lexical-structure)), §1.4–§1.11 (two message-key rows added to [spec/11](../../spec/11-messages-and-custom.md)), stored-date reality on the hybrid calendar (§1.12, stated in [spec/05 §4](../../spec/05-dates-and-time.md#4-the-gregorian-floor)), §2.9, §2.10, §2.20, and the time-zone and type-definition rows of §2.21. Report order (§1.6) matches `SPEC-2026-10-13-06`.
- `unmodeled`: Includes, model references and type-definition libraries (§2.21–§2.23); the reader reads no included model.
- `sync`: Inbound facts about clauses this project owns; no outbound ledger entry is created.

<a id="src-inbound-2026-10-22"></a>
## Reviewed October 22 peer answers

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-22.md`, SHA-256 `be5dcbbadf716c690248623fa4c257049f76c3fbc6fd6d31f26291f836976c89`, at a12-dmkits `09f1352e5`. It answers our receipt at `bf2216b6` and no ledger entry.
- `revision`: `a50e0c86b`, `ede16bfa2` and `d8e0ba8d0` resolve as ancestors of `09f1352e5`, and every lock class and method the letter names exists there; read with `git` only.
- `review`: A HIGH reconciliation of every row against `spec/` and the Lean readers on 2026-10-22. The rows are peer-reported Kernel outcomes; no peer suite or Kernel run of ours was made.
- `implemented`: §1.2, a boolean member reads a number token by its kind, an integer set unless zero, `-0` clearing, and a fraction or an exponent refused whatever its value. Lean's JSON parser folded `1e0` into `1`, so every model file is now parsed through the exponent-respelling pass ([spec/01 §1.1](../../spec/01-data-model.md#member-binding), [locks](../../A12Kernel/Reference/Dm/MemberBindingLocks.lean)).
- `implemented`: §1.3, an `int` member reads a number alike in both spellings; every relabelled row is locked as written.
- `implemented`: §1.1, a lone U+0130 or U+212A draws what a lone long s draws ([spec/02](../../spec/02-logic-and-formal-errors.md)); that no other character outside ASCII completes either word is the letter's JDK 21 enumeration, recorded as a JDK row.
- `correction`: §2 relabels the October 18 `fieldRefByShortNameAllowed` row `1e0` as `1.0`; both tokens are now locked on that member.
- `withdrawn`: §3 offered to close `SPEC-2026-10-14-01` on the peer's scope of 2026-09-15, which declined to reproduce `MVK_PARALLEL_ITERATION_INVALID` and `MVK_NEG_CONDITION_IN_ITERATION` in its portable checker. The peer's follow-up letter `a12-kernel-lean-spec-corrections-2026-10-22a.md`, SHA-256 `d4f33f6145bc85bd030daab7f4fc63871f0211a0072321487cacf33a54ebca41`, replaces only that section: its owner reversed the scope on 2026-10-22, both codes are re-opened together, and a later letter is to bring Kernel rows for both. `-14-01` therefore stays answered but not closed, and nothing is asked of us; our captures remain the Kernel evidence for both classes. The follow-up carries a decision and no Kernel rows; that a portable report names both codes as unchecked since a12-dmkits `309ba4fd8` is peer-reported.
- `agrees`: §6's open rows of the October 21 letter. In §1.13 an empty, space or U+2003 label draws `MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES` and a U+00A0 label is admitted, as the blank predicate of [spec/01](../../spec/01-data-model.md) reads them ([cases](../../A12Kernel/Conformance/FieldTypeDeclarationNotification.lean)); the U+00A0 label's rendering is not locked here. §1.14's literals and year digits agree and are stated in [spec/04](../../spec/04-numbers-and-decimals.md) and [spec/05](../../spec/05-dates-and-time.md), locked in the [document-number locks](../../A12Kernel/Reference/Dm/DocumentNumberLocks.lean) and the [binding locks](../../A12Kernel/Reference/Dm/MemberBindingLocks.lean).
- `disclosure`: §4's two peer defects touched no row sent here. The hazard it names, a writer re-serializing a model through a numeric tree, does not reach the Lean readers, which write no model.
- `sync`: Inbound facts about clauses this project owns; no outbound ledger entry is created.

<a id="src-inbound-2026-10-22b"></a>
## Reviewed October 22b iteration-guard rows

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-22b.md`, SHA-256 `5026b4e22f46360f34275a09855deac94bd8aa16553a70797316ef88c5912a23`, at a12-dmkits `532cd2b28`, which corrects `74115d16a`; both resolve as ancestors of the peer's head, read with `git` only. It answers `SPEC-2026-10-14-01` with Kernel rows for `MVK_NEG_CONDITION_IN_ITERATION` and `MVK_PARALLEL_ITERATION_INVALID`, as the [October 22a follow-up](#src-inbound-2026-10-22) promised.
- `rows`: The peer locks `CheckerIterationGuardAgreementTest` and `CheckerUniquenessGuardAgreementTest` pin the Kernel's classes per rule through the peer's `RuleValidator`. The order model repeats `Lines` 50 times and `Picks` 10 times, both keyed by `LineNo`, `Lines/Parts` 5 times, `Gifts` twice keyed by `GiftNo` and `Wraps` twice without an index field. These are peer-reported Kernel outcomes; every divergent row was re-measured on our own model in the [K04 capture](model-structure-and-declaration-probes.md#src-iteration-guard-k04), and each agrees.
- `review`: A HIGH replay on 2026-10-22 of every row of both locks through our reader and checker at `219a12b7`, by a piped probe that rebuilt the order model. About 45 rows agree, among them the three computation rows, the shallowest refused level, and the group operands of `FieldValuesNotUnique`, which the [uniqueness guard locks](../../A12Kernel/Reference/Dm/UniquenessIterationGuardLocks.lean) already hold against our own capture.
- `diverges`: Lean exempts no level, admits about fifteen shapes its classifier leaves unjudged, answers the guard ahead of `MVK_ERROR_FIELD_NOT_REFERENCED`, and refuses four admitted shapes with no class or another one. The [K04 checkpoint](model-structure-and-declaration-probes.md#src-iteration-guard-k04)'s `implementation` record names the closed rows; the rest were returned omissions under K04 or K07, which closed with that checkpoint and the [K06 and K07 batch](model-structure-and-declaration-probes.md#src-blank-root-dispatch-k06).
- `source-reading`: Kernel `IterationNotValidVisitor` leaves out of the guard an iteration level whose group repeats exactly twice and, on an A12 model, declares an index field; the lock's two keyed `Gifts` rows show it. The flat model does not distinguish H models, whose exemption needs no index field.
- `ledger`: Neither lock holds a CustomCondition row, so `-14-01`'s six `pc-*` rows stay unreconciled and the entry stays `answered` in [the ledger at `bf2216b6`](https://github.com/mbackschat/a12-kernel-lean/blob/bf2216b69d5a3bbaefe182b76271ddf8d6b27ecf/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-10-14-01).
- `redaction`: The letter and the lock quote a rendered Kernel message for the nested-level row; it is not retained. The refusal names the `Lines` level.
- `sync`: Inbound facts about clauses this project owns; no outbound ledger entry is created.

<a id="src-inbound-2026-10-22c"></a>
## Reviewed October 22c selection, computation and parallel-binding rows

- `source`: Peer-session letter of 2026-10-22, its frozen copy `a12-kernel-lean-spec-corrections-2026-10-22c.md`, SHA-256 `8d916ab14963980d56c2e0165b12aac8bc02fdb2d286b03beee4ac3390af9fb1`. Its rows hold at a12-dmkits `e9747abbf`, with the selection and computation rows from `15e567b27` and the binding rows from `51304fc29`; all three resolve as ancestors of the peer's head, read with `git` only. It extends the [October 22b](#src-inbound-2026-10-22b) answer to `SPEC-2026-10-14-01` and replaces nothing.
- `rows`: The peer locks `CheckerIterationGuardAgreementTest` and `CheckerIterationBindingAgreementTest` pin the Kernel's classes through the peer's `RuleValidator`: nine rules on the 22b order model with `Wraps` holding `Bows` (three rows keyed by `BowNo`), selecting with a constant or a field key; five computation preconditions; six rules on a staffing plan whose `Demand` and `Supply` repeat six times keyed by `Shift`; and two on a rota nesting them in an unkeyed `Weeks` of four. Every row was re-measured at our pin in the [binding capture](model-structure-and-declaration-probes.md#src-iteration-binding-k04), and each agrees.
- `review`: A HIGH replay on 2026-10-22 of the 17 rule rows through our reader at `6e6ad094`, on DM-JSON models built to the letter's shapes. Seven agree. Ten diverge: two field-fill rules beside a constant selection that the Kernel refuses are admitted; two selections below the unkeyed `Wraps` and one field-keyed selection are refused with no class; a guarded nested pair beside a join is refused with no class; and four rules a parallel iteration binds only through a starred or nested reference of the error field are admitted or draw no class or another one where the Kernel draws `MVK_ERROR_FIELD_AND_ITERATION_INVALID`. The [binding capture](model-structure-and-declaration-probes.md#src-iteration-binding-k04) replays the computation rows too.
- `diverges`: Each divergence was a returned omission under K04 or K07, closed by the [K04 checkpoint](model-structure-and-declaration-probes.md#src-iteration-guard-k04) and the [K06 and K07 batch](model-structure-and-declaration-probes.md#src-blank-root-dispatch-k06). The binding rows share the mechanism of row `a09` of the [K04 capture](model-structure-and-declaration-probes.md#src-iteration-guard-k04), whose sides are both keyed by `LineNo`.
- `source-reading`: The letter's account, a constant selection fixing only its own level and the parallel binding asked after the per-level loop, is the peer's hypothesis with source pointers; it is not adopted here until measured.
- `sync`: Inbound facts about clauses this project owns; no outbound ledger entry is created.

<a id="src-inbound-2026-10-24"></a>
## Reviewed October 24 instrument handback

- `source`: Peer-session letter of 2026-10-24, delivered to this session and placed by the peer as `a12-kernel-lean-spec-corrections-2026-10-24.md`, SHA-256 `94f6ac4fcd9837875e92fd92f7c113e607b23dc8f48492b0e49227bee01489b0`. It answers this project's instrument note of the same day on the probe's `-6` fault and disposes of no ledger entry.
- `revision`: a12-dmkits `08b0d6499c98b132257ec961eb214de73fa223e3`; the fix `082ea50ee` and its review commits `61fb70c5f` and `08b0d6499` resolve, read with `git` only. The [measurement checkout](cross-layer-routes.md#src-measurement-checkout-route) was fast-forwarded to it for this fix.
- `review`: A HIGH reconciliation on 2026-10-24. The letter's `k8` table was not adopted from the letter: `request-k22kk8.json` was rerun unchanged at the new pin as `k22kk8b`, which reproduces every row's count, target, type, references and fill-to-fix the table states, and Lean's replay matches it ([checkpoint](model-structure-and-declaration-probes.md#src-keyed-group-beside-join), `runtime-keyed`).
- `adopted`: The letter's scope limit, measured where the group's key differs from the join key, the error entity is a group and the condition a presence form, bounds the [spec clause](../../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands). That a harness reading Kernel messages with Java assertions enabled cannot observe these messages concerns the peer's harness, which this project runs only through the unchanged probe task.
- `instrument-limit`: The probe's slash-led address omits a group target's own-level coordinate on every artifact (the peer's CG24), as Lean's [renderer](../../A12Kernel/Reference/Dm/Validate.lean) already reproduces; the peer asked whether this project wants an opt-in lossless coordinate vector. The owner accepted it on 2026-10-24 in the peer's recommended shape, leaving existing artifact bytes unchanged, and the request went to the peer session that day; this project's replay does not consume it.
- `hypotheses`: None offered; why `k8`'s target stays at `Lines[1]` while its references name the joined line is not settled by either side.
- `sync`: Instrument facts and inbound rows about clauses this project owns; no outbound ledger entry is created. Our measurement extends the pending `SPEC-2026-10-24-03`.

<a id="src-inbound-2026-10-23"></a>
## Reviewed October 23 handback of the October 22 and 23 entries

- `source`: Peer-session letter of 2026-10-23, delivered by the owner as `a12-kernel-lean-spec-corrections-2026-10-23.md`, SHA-256 `2cc08d1a9592d8dedba37408dfb85308e17fe8f33bc7ef77b6c82a7a9fd12c28`. Its rows hold at a12-dmkits `e6850d0b9984d7df3f8eae3baa3639f4a7d25084`, which resolves as an ancestor of the peer's head; read with `git` only. It follows the [October 22c letter](#src-inbound-2026-10-22c) and replaces nothing.
- `revision`: Every lock class the letter names exists at `e6850d0b9`; the `slotkeys` document of `GroupTargetCarrierDiffTest` was read at its last change `4abbdd35d`, an ancestor.
- `review`: A HIGH reconciliation on 2026-10-23 of every entry disposition and every row against `spec/` and the Lean readers. The static rows of the letter's [KF598](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf598)–[KF606](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf606) tables were re-measured at our pin and replayed through `lake exe checkKernelEvidence` ([checkpoint](model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23)); the runtime rows of [KF603](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf603) were re-measured and replayed through the parallel evaluator ([checkpoint](model-structure-and-declaration-probes.md#src-nested-join-capacity)). The interpreter-side agreements are peer-reported.
- `agrees`: `SPEC-2026-10-22-01` to `-05` and `SPEC-2026-10-23-01` to `-03` are reconciled, none contradicted; the [ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue) owns the per-entry dispositions. For `-22-01` the peer corrected its own KF34 spelling to the bare `Length(F)`. For `-22-03` and `-22-04` the peer interpreter keeps its preparation-time refusal of an unregistered custom condition as declared policy, so it never reproduces the Kernel's report.
- `implemented`: A partial call reports no rule whose error entity is a group ([KF603](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf603)), so the [rule executor](../../A12Kernel/Elaboration/ValidationRule/Execution.lean) skips one there ([spec/07](../../spec/07-repetition-and-iteration.md)).
- `implemented`: The nested rows a parallel rule visits below a joined side follow the capacity rule with the joined level counted once and occupancy merged at the joined coordinate ([KF603](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf603)), an unmatched side included; the letter's two capacities agree with ours and our rows extend them.
- `implemented`: `-22-02`'s extension: an undeclared member of any JSON kind drops, a boolean, `null`, number or array member of a fixed group, an object in a nested fixed group or a row, and a string beside the root group ([KF1](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf1)); the [document reader](../../A12Kernel/Reference/Dm/Document.lean) previously refused the non-string, non-object kinds.
- `implemented`: A group operand of a field-form slot, a raw-type key in every selection carrier, a field-keyed group list and a filled-count pair now answer as [KF599](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf599), [KF601](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf601), [KF602](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf602) and [KF605](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf605) measure; the [handback checkpoint](model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23)'s `lean` record names the readers.
- `agrees`: [KF604](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf604)'s call counts follow the classification pass Lean already runs; a [lock](../../A12Kernel/Reference/Dm/CustomConditionCaptureLocks.lean) pins both `Or` orderings beside a negative.
- `deferred`: The `SlotNo`-keyed `Lines/Slots` target beside the `Picks` join is admitted and fired on none of six peer documents and three of ours; its mechanism is measured, and `okt002` agrees, at the [keyed-group checkpoint](model-structure-and-declaration-probes.md#src-keyed-group-beside-join).
- `hypotheses`: Section 4's source readings, that a field-keyed selection iterates where its key does, that a group target iterates the levels above it, the partial filter's locus, and the optimization flag behind the nested-row choice, are the peer's accounts. Only their measured rows were adopted.
- `sync`: Inbound facts about clauses this project owns; no outbound ledger entry is created for them. Our local supplements beyond the letter go out as `SPEC-2026-10-23-06`.

<a id="src-inbound-2026-10-13"></a>
## Reviewed October 13 peer response

- `source`: Owner-delivered `a12-kernel-lean-spec-corrections-2026-10-13.md`, SHA-256 `5005f7da4fffc207bb251398e7c7a507f388ce39c5109aa29b63d9d59520f5a8`. It answers `SPEC-2026-10-12-01` and `SPEC-2026-10-13-01` to `-12` as committed at `a4f769ba`; `SPEC-2026-10-13-13` postdates it.
- `revision`: Reviewed a12-dmkits `8addfd0bf5e1e6f1c21d20d49c1eb0acaac85358`; every checkpoint the table names resolves and is its ancestor, and every named lock class exists there. Files were read with `git show` at this revision.
- `review`: Source-reading review of the named Kernel-differential and `checkConsistency` assertions against each acceptance condition, plus local reader probes for the rendering rows. No peer suites, Kernel calls or local replay were run for this receipt; peer lane and performance figures are peer-reported.
- `receipt`: [The reconciliation ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue) owns the per-entry dispositions.

| SPEC-2026 suffix | Checkpoint | Committed lock class | Status |
|---|---|---|---|
| 10-12-01 | `43c4b1302` | `SelectedErrorReanchorEligibilityDiffTest` | accepted |
| 10-13-01 | `609eb41c3` | `FirstFilledDateTargetRenderingDiffTest` | accepted |
| 10-13-02 | `4b5e73812` | `CheckedInputOrderDiffTest` | accepted, corrected |
| 10-13-03 | `82bb2d977` | `CheckerMembershipReadOrderAgreementTest` | accepted |
| 10-13-04 | `09acf9995` | `CheckerEnumDeclarationStreamAgreementTest` | accepted |
| 10-13-05 | `796e060e4` | `OverRepetitionOccurrenceScopeDiffTest` | accepted |
| 10-13-06 | `c223b0f4c` | `RequiredEmptyReadDiffTest` | accepted |
| 10-13-07 | `399c728ef` | `UnmatchedKeyAggregatePolarityDiffTest` | accepted |
| 10-13-08 | `f3677bea0` | `CheckerDeclarationWithholdingAgreementTest` | accepted |
| 10-13-09 | `83d726617` | `RepetitionNotUniqueSiblingReferenceDiffTest` | accepted |
| 10-13-10 | `f01f1fc58` | `UniquenessGuardSlotLawsTest` | accepted |
| 10-13-11 | `058750e73` | `CheckerEnumDeclarationStreamAgreementTest` | accepted, corrected |
| 10-13-12 | `7b98fae62` | `MessageParameterRowDiffTest` | accepted, extended |

- `correction-a`: A computed String target meets its type's maximum, 99,999 units when none is declared, so 100,000 computed units are ERRORED while a Custom target stores them ([KF547](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf547), `CheckedInputOrderDiffTest`). Our entry's claim that the technical guard is absent stands; the default maximum was missing. Lean now checks computed String targets under it ([conformance](../../A12Kernel/Conformance/StringComputation.lean)); [spec/09 §4](../../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape).
- `correction-b`: Every sort entry beyond the third draws its own capacity notification; the peer's five-entry row draws two, which our four-entry rows could not separate ([conformance](../../A12Kernel/Conformance/IndexAndSortDeclaration.lean)); [spec/01](../../spec/01-data-model.md#index-and-sort-nomination-admission).
- `correction-c`: Enumeration charset notifications collapse per value and unit, so two values sharing a high surrogate draw two. The Lean notification already carried the value; only the spec prose generalized our one-value row ([lock](../../A12Kernel/Reference/Dm/EnumerationDeclarationNotificationLocks.lean)); [spec/01](../../spec/01-data-model.md#enumeration-declarations).
- `extension-d`: Any `supportedCharacters` entry holding a surrogate unit leaves the model unbuilt, a supplementary singleton included; [spec/06](../../spec/06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching) already states it and the charset elaborator refuses it.
- `extension-g-h`: An unmatched key faults a value parameter only, which [spec/11](../../spec/11-messages-and-custom.md#part-a--13-error-message-interpolation) already stated at `4097253d`. In a rule iterating the keyed group the fault reports once, at the first row (`KEYED_MISS_ROW`, a12-dmkits `7b98fae62`); the replay now ends the row loop at the fault through the existing runtime-failure handler ([lock](../../A12Kernel/Reference/Dm/MessageRowRenderingLocks.lean)). A fault first reached at a later row follows that handler's account and is not separately measured. The whitespace-spelling rows render tight through the local reader.
- `selected-key`: A formally invalid or partially irrelevant field-valued key selects no row ([KF549](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf549)); the local selected-error lookup already reads the authored-validation cell. [spec/08 §4.3](../../spec/08-paths-and-references.md#43-selected-references-in-validation-messages).
- `member-ranges`: [KF556](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf556) and [KF559](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf559) (`CheckerLengthLimitAgreementTest`, `CheckerDigitMemberRangeAgreementTest`, a12-dmkits `b20417768`, `97bbeaaf4`) give length and digit-count ranges, a fractional count below `-1` as signed, and an integer count above 15 as a codeless verdict rather than a build failure, correcting [spec/04](../../spec/04-numbers-and-decimals.md#4-other-numeric-constraints)'s earlier tier. [spec/01 §1](../../spec/01-data-model.md#1-model--a-typed-tree) owns the account. The model reader does not judge these ranges; [K17](../PLAN.md#k17--model-declarations-and-static-denominator) carries them.
- `corroborating`: [KF553](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf553) (partial validation runs a per-row rule on every covered declared slot, the content gate overridden) and [KF555](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf555) (a value outside `supportedCharacters` is formally invalid on every read) agree with [spec/10 §5](../../spec/10-validation-and-polarity.md#5-full-vs-partial-validation) and [spec/06](../../spec/06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching); no local replay was run for them. The peer's TIME-kind first-filled rows extend [KF211](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf211)'s declared-format rule.
- `name-length`: A 61-character nested group name draws the path-shape notification at the group and its field, with no separate length notification; no local clause states otherwise, and K17 carries it.
- `peer-residuals`: The peer reports Enumeration block 2 under its own code after block 5, omits block 7, declines a doubly declared index name for the display-label class, and keeps the [IF376](../../../a12-rulekit/docs/INTERPRETER-FINDINGS.md#if376) first-admitted pointer policy. These are compatibility choices of the peer, not contrary Kernel evidence.
- `hypotheses`: The letter's mechanism accounts (high-unit refusal, metamodel judging of out-of-range members, the unmatched-key throw, index-scan order) are unmeasured and were not adopted.
- `sync`: Inbound corrections to clauses this project owns; no outbound ledger entry is created.

<a id="src-inbound-2026-10-24a"></a>
## Reviewed October 24a handback of the ten open entries

- `source`: Peer-session letter of 2026-10-24, `a12-kernel-lean-spec-corrections-2026-10-24a.md`, SHA-256 `0a475a44422e350669775082c6a59b2fa3f85f3f60370c3c3d1393b23c49b442`, delivered by the a12-dmkits session. It answers the ledger as of `b5035bba` plus the then uncommitted `SPEC-2026-10-24-07`, which landed at `69faa20b`, and replaces nothing.
- `revision`: a12-dmkits `2539feea3b679bebb1c1dd9c2b346bc436311a0d`, committed on the peer's local `main` and unpushed, read with `git` only; it carries the fixes the letter names, `CheckerRepeatabilityCascadeAgreementTest` with the `AmountSet` rule and `NoteFromAmount` computation it injects, and `RuleGroupErrorEntityTest`.
- `review`: A HIGH reconciliation on 2026-10-24 of every disposition against the entries' acceptance conditions and `spec/`. The letter's rows re-run our own requests and captures through `checkConsistency` and the probe; none contradicts an entry, and every entry is `accepted` in the [ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue).
- `adopted`: Under a group whose count is below one, a rule and a computation declared there draw no `MVK_MAX_VALUES_INVALID` (13 rows, the peer's measurement), which [spec/01](../../spec/01-data-model.md#repeatability) now states beside the groups and fields.
- `instrument`: `td29`'s retained `RK_REDUNDANT_OPERAND` and `ogt008`/`ogt009`'s `RK_ERROR_FIELD_OUTSIDE_GROUP` are the instrument's own findings; A12 admits `td29` and cannot build the injected `ogt` model. No local claim names either as a Kernel class.
- `limits`: The 45 message keys of `SPEC-2026-10-24-06` were reconciled by the same rendered-text method as ours, not by an independent observation of the selected key. The peer interpreter declines `g1`, `k1`, `k5` and `k8` (IG180); `k8`'s error pointer at `Lines[1]` beside references at `Lines[2]` and `Lines[-5]` stays unexplained on both sides.
- `sync`: Inbound facts about clauses this project owns; no outbound ledger entry is created for them.

<a id="src-inbound-2026-10-24b"></a>
## Reviewed October 24b instrument handback

- `source`: Peer-session letter of 2026-10-24, `a12-kernel-lean-spec-corrections-2026-10-24b.md`, SHA-256 `2027e0dbac4bc1522a30d04c4c4297a967f16f49bda7b62279c822d13ca989b9`, delivered by the a12-dmkits session. It answers this project's instrument note `A12-DMTOOL-FEEDBACK-2026-10-24-02` and disposes of no ledger entry.
- `revision`: a12-dmkits instrument `d2dd5453b`, adding the probe's `evaluationRaises` channel, and interpreter correction `3be383e24`, which records [KF615](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf615); both resolve, read with `git` only. The [measurement checkout](cross-layer-routes.md#src-measurement-checkout-route) stays at `08b0d6499`, since no local replay consumes the new channel.
- `review`: A HIGH reconciliation on 2026-10-24. KF615's outcome was re-measured on a local model of its shapes, adding a false and an unregistered name, the leaf first and an `Or` ([checkpoint](model-structure-and-declaration-probes.md#src-k22-group-target-custom-abort)); every row agrees with the letter, and the retained `k22g` artifact's `g4` and `g5` show the same outcome.
- `adopted`: A reached custom condition on a group-target rule fails the rule before its name is looked up ([spec/11](../../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)). The letter's `Kernel` origin for `g4` and `g5` is the peer's measurement at `d2dd5453b`, not repeated here.
- `source-reading`: The letter's account of why the name is empty, read from the Kernel's code generator and one observed stack, is the peer's hypothesis; this project adopts only the measured outcome.
- `instrument-limit`: `evaluationRaises` entries are not keyed to messages, and an artifact holding a raise-born message changes bytes when rerun at `d2dd5453b`; the retained `artifact-k22g.json` was produced at `08b0d6499` and is not rerun.
- `sync`: Inbound facts about clauses this project owns. The answer settles the `g4`/`g5` exclusion of the pending `SPEC-2026-10-24-10`, whose acceptance now points here; no new outbound entry is created.

<a id="src-inbound-2026-10-25"></a>
## Reviewed October 25 handback of the fifteen entries handed off at `e9c7259f`

- `source`: Peer-session letter of 2026-10-25, `a12-kernel-lean-spec-corrections-2026-10-25.md`, SHA-256 `ab8c5b3d8b8b777f0bf65e57a3fbc37279d0f69a040392cd0a80196fdc41c48b`, delivered by the a12-dmkits session. It answers `SPEC-2026-10-24-08` to `-20` and `SPEC-2026-10-25-01` and `-02` as handed off at `e9c7259f`, and replaces nothing.
- `revision`: a12-dmkits `f3c2578194b7e2293707fe33980f31920b3983d5`, read with `git` only. Every fix the letter names resolves as its ancestor, the one commit after its replay revision `e6e01a01d` touches only tests and docs, and the lock tests it names exist there.
- `review`: A HIGH reconciliation on 2026-10-25 against each entry's acceptance condition. Two of the letter's corrections were re-measured locally before adoption ([declaration order](group-count-topology.md#src-k22-joined-declaration-order), [dispatch merge](group-count-topology.md#src-k22-partial-dispatch-merge)). Thirteen entries are `accepted`, `SPEC-2026-10-24-09` is `superseded` and `SPEC-2026-10-24-19` stays `handed-off`, since the letter does not name its generated-requiredness rows, as the [ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue) records.
- `adopted`: KF619's distinction between a leading declaration reading no partner field and one behind a joined lead, in [spec/09](../../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join); KF621's part-coordinate narrowing, its invalid-cell merge and the mandatory check reading only its own cell, in [spec/10](../../spec/10-validation-and-polarity.md); KF615's lookup order, from the peer's `CustomConditionGroupTargetLookupLawsTest`, in [spec/11](../../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch). The lookup order is the peer's measurement at that revision, not repeated here.
- `corrected`: KF619 states that a declaration behind a joined lead stores nothing where its guard selects it. The local `W02`, `WS2` and `WD2` rows contradict that clause, since the scan passes over such a declaration even where its guard holds. `SPEC-2026-10-25-03` carries the measured account outbound.
- `not-adopted`: §3.3 confirms spec/06 A.1 unchanged. §3.4's core `IData` view is a host API no clause here models. §3.6's keyed-category roles (extending KF568) and Enumeration-into-text rows (extending KF610) extend clauses spec/08 and spec/09 own but are not yet checked against Lean, as the [SG8 gap](../gaps/strings-and-messages.md#gap-sg8) records.
- `instrument`: The peer's probe and `rule check` now pin the JVM default zone to UTC (`d0a357ea8`, `b6fe8a2f8`), because by its KF231 a DateTime constant is judged against that default; the [measurement checkout](cross-layer-routes.md#src-measurement-checkout-route) stays at `08b0d6499`. Equal messages now order numerically by `repetitionIndexes` (`9bf922e33`), which no retained request observes.
- `sync`: Inbound facts about clauses this project owns create no outbound entry. `SPEC-2026-10-25-03` exists because the local measurement corrects the peer's account.

<a id="src-inbound-2026-10-25a"></a>
## Reviewed October 25a handback of the two entries left open at `1ac375a6`

- `source`: Peer-session letter of 2026-10-25, `a12-kernel-lean-spec-corrections-2026-10-25a.md`, SHA-256 `7331db2ddca69ef4f564f5d577499367e41db0b9bfa85e9a86e3a5bfbb52213f`, delivered by the a12-dmkits session. It answers `SPEC-2026-10-25-03` and `SPEC-2026-10-24-19` as handed off at `1ac375a6`, and replaces nothing.
- `revision`: a12-dmkits `95b57fb4a3fb40cc7c605d9e3251e5ff35e60cc6`, read with `git` only. Its interpreter fix `50aeb5b45` and the [October 25](#src-inbound-2026-10-25) revision are its ancestors, the commits between the fix and it touch only test sources and docs, and KF619 there states the passing-over rule with its `JoinedTargetDeclarationTableDiffTest` and `JoinedTargetDeclarationTableTest` locks.
- `review`: A HIGH reconciliation on 2026-10-25 against both acceptance conditions; both entries are `accepted` in the [ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue). The peer's probe re-runs reproduce the [declaration-order capture](group-count-topology.md#src-k22-joined-declaration-order) and the generated-requiredness capture's seventeen rows, full and partial.
- `adopted`: No clause changes. The peer's own `Passed`, `PassedConstant` and `PassedBad` rows, a holding, an unguarded and a malformed-reading declaration behind a joined lead on Number targets, agree with the account [spec/09](../../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join) states.
- `sync`: The two answers close the outbound queue; no new entry is created.

<a id="src-inbound-2026-10-26"></a>
## Reviewed October 26 handback: required-empty cells in a `FirstFilledValue` group walk and list reads past capacity

- `source`: Peer-session letter of 2026-10-26, `a12-kernel-lean-spec-corrections-2026-10-26.md`, SHA-256 `1d3afb62b6f66aea37645574b1064548c4b16eb7deb3be3a5ced4558d2a7dab5`, delivered by the a12-dmkits session. It answers no entry and replaces nothing.
- `revision`: a12-dmkits `eaabfc1dc` (group-walk lock `RequiredEmptyFirstFilledGroupDiffTest` and interpreter fix), `a7f502259` (lock `OverCapacityRowReadDiffTest`) and `9afbc42f0` (changelog line, beside an unrelated clock fix), read with `git` only; all three are ancestors of the checkout's HEAD. Both locks assert the Kernel's own output on both strategies through `DocumentDifferential`; they were not re-run here.
- `review`: A HIGH reconciliation on 2026-10-26. The group-walk rows extend SPEC-2026-10-13-06's measured reads to the group and keyed-row operand of `FirstFilledValue`: a required-empty contained field leaves the walk undecided in full and partial validation, while a computation reads it as ordinary empty.
- `adopted`: No clause changes. The rows are the composition of three existing clauses, the group operand's declaration-order expansion and the stop at reached formal unavailability in [spec/03](../../spec/03-empty-and-required.md#a3-what-an-all-empty-selection-folds-to-the-aggregate-identities), and the validation/computation asymmetry of required-empty cells in [spec/02](../../spec/02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state) and [spec/03](../../spec/03-empty-and-required.md#part-b--4-the-required-property). The over-capacity rows for `MaxValue`, `NotAllFieldsFilled` and a filtered `NumberOfFilledFields` corroborate the evaluation-domain exclusion in [spec/07](../../spec/07-repetition-and-iteration.md).
- `local-readback`: no local Lean lock reproduces these rows. The peer's §4 mechanism hypothesis, that the group walk asks each contained cell the field operand's availability question, is not adopted as a mechanism claim.
- `sync`: Inbound facts about clauses this project owns create no outbound entry.

<a id="src-inbound-2026-10-26a"></a>
## Reviewed October 26a handback: `RuleGroup` in every operand gate, type-defined value-list mixes and group error targets

- `source`: Peer-session letter of 2026-10-26, `a12-kernel-lean-spec-corrections-2026-10-26a.md`, SHA-256 `39d6489c891c29759d999f079f8331e2b3352bb594ba524aee66e1a2c4aba8a1`, delivered by the a12-dmkits session. It answers no entry and replaces nothing.
- `revision`: a12-dmkits `eadcd1fedb32ad444049d07c1ae0205b154a3161` (lock `CheckerRuleGroupOperandAgreementTest`), `20e1c58431fe35f5135d000f12c5eef8ef124826` (lock `CheckerTypeDefinedValueListAgreementTest`) and `3217f21aa5d657527ab5e93fa385b1a701b9edd6` (lock `CheckerGroupTargetIterationAgreementTest`), read with `git` only and all ancestors of the checkout's HEAD. Each lock pins the Kernel's `RuleValidator` answer per row; they were not re-run here.
- `review`: A HIGH reconciliation on 2026-10-26 against the clauses each section extends.
- `adopted`: [spec/08](../../spec/08-paths-and-references.md) now states that `RuleGroup` draws its spelled path's class in every measured operand gate and that only the unquoted keyword is the group. [spec/01](../../spec/01-data-model.md) replaces the untested config-bearing typedef case with the measured date-range and Number rows.
- `confirmed`: the group error-target rows, `MVK_ERROR_FIELDGROUP_ITERATION4_INVALID` on a fixed and a repeatable group target and admission without the field read, follow the role sorting [spec/07](../../spec/07-repetition-and-iteration.md) already states against an error field that is itself a group.
- `local-readback`: no local lock asserts these rows; [SG9](../gaps/paths-and-groups.md#gap-sg9) records the `RuleGroup` operand gates, and model expansion of type definitions is outside the modelled surface by [spec/01](../../spec/01-data-model.md).
- `sync`: Inbound facts about clauses this project owns create no outbound entry.

<a id="src-inbound-2026-10-27"></a>
## Reviewed October 27 handback of the thirty-three spec-rewrite entries

- `source`: Peer-session letter of 2026-10-27, `a12-kernel-lean-spec-corrections-2026-10-27.md`, SHA-256 `23f9ee0f516da10625a0e95458289b7cb4bd44afad9acacd142b0e19f6b840e7`, delivered by the a12-dmkits session. It answers `SPEC-2026-10-26-01` to `-30` and `SPEC-2026-10-27-01` to `-03` as handed off at `5192f2bb`, and replaces nothing.
- `revision`: a12-dmkits `fecf855251c1245fd7048b2a509ddbb2b72989dd`, read with `git` only. The findings KF623–KF645, KF71 and KF244 and the named locks exist at that revision. The letter's peer-session hypotheses about mechanisms are not adopted.
- `review`: A HIGH reconciliation on 2026-10-27 and 2026-10-28 against each acceptance condition. Two read-only surveys classified every row against `spec/`, and the rows that a Lean definition decides were probed against the theory.
- `corrected`: `-12`, `-24`, `-25`, `-28` and `SPEC-2026-10-27-01` contradicted the Lean account. The theory now poisons a joined target skipped at an invalid index column, arms the generated mandatory check of an index field nominated in a non-repeatable group, gives a `-1` maximum an unknown static scale, answers a root- or fixed-indexed chain over an unbound repetition by its walk, classes a keyed extent's star at the index level, and lifts three build failures under a deleting `ONLY` filter. On 2026-10-28 it also states a deleted field's, rule's or computation's empty name as its codeless sentence and admits a one-space one, so spec/01's build table, which admitted both, now separates them (KF626).
- `adopted`: spec/01 to spec/12 and spec/14 now state the measured cells the letter settles, keeps each part the letter leaves unmeasured as unmeasured, and carries this record on its `Sources:` lines.
- `agrees`: Lean already answered the letter's rows for `27-02`, `27-03` (b), `-07`, `-08` and `-10`, and the probed `-13`, `-17`, `-19`, `-21` and `-26` cells: diverging frames, `ValueAsDate` in `DateTime`'s Time argument, the blank S-value, `DateTime`'s Date-argument order and `Sum` over a raw String. The `-06` unstarred fixed group operand follows the field-by-field rule without a probe of its own.
- `open`: [SG4](../gaps/keystone.md#gap-sg4), [SG5](../gaps/numeric-and-temporal.md#gap-sg5) and [SG9](../gaps/paths-and-groups.md#gap-sg9) record the carriers the measurements leave unmeasured.
- `sync`: The thirty-three entries are terminal in the [ledger](../A12-DMKITS-SPEC-SYNC-LEDGER.md#current-queue). No new entry is created.
