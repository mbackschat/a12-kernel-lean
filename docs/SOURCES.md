# Authoritative sources and drill routes

<a id="authoritative-sources--how-to-drill"></a>
<a id="authoritative-sources-how-to-drill"></a>

This hub and bounded [`sources/`](sources/) records own provenance: routes from semantic questions to authoritative kernel layers and maintained a12-dmkits knowledge. Specification, findings, implementation, evidence inventory and review history have separate owners.

Authority order is **[`../../a12-kernel`](../../a12-kernel) → project-owned [`../spec/`](../spec/) and Lean theory → [a12-dmkits](../../a12-rulekit)**. The real kernel is the behavioral oracle. The spec and Lean theory are this project’s working semantics-of-record. a12-dmkits is a peer clean-room implementation, source of maintained kernel-executing differentials, and knowledge corpus.

All kernel source routes below target kernel **30.8.1**, inspected at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. Read source to learn behavior; never link, call, ship, or transcribe it.

## Query contract

Start from the relevant [`spec/` clause](../spec/SEMANTICS-MAP.md), then:

1. identify the claim class with the engine routing rule;
2. use the clause table for the subsystem, then the question-to-locus index for the exact decisive class, template, backing bean, method, or service;
3. follow a12-dmkits’ guard-checked [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) for its exhaustive prose/test/corpus inventory;
4. consult the [cross-layer packets](sources/cross-layer-routes.md#focused-cross-layer-packets) only for mechanisms not answered by one locus.

Search a topic with `rg -n '<topic>' docs/SOURCES.md`, then read only its linked record. The checkpoint and historical compatibility indexes preserve citations; they are not a required sequential read. Detailed claims and limits belong in the destination, so new navigation labels should name the topic briefly.

### How far to trust a 40-character revision receipt

**A revision citation certifies what was read when it was written, not that it still resolves.** Measured 2026-09-06: of 426 distinct 40-hex citations across `docs/` and `spec/`, **176 resolve in no local checkout**. Restricted to the live provenance owners — this file, `EVIDENCE.md`, the current ledger, and the `sources/` shards — **182 citations resolve at 80%**. The remaining dead ones concentrated in the since-deleted `archived/` directory, `LEAN-FORMALIZATION.md` and `PRODUCTION-RELEASE.md`, where they name frozen history or external repositories such as Cedar and Lean that no local checkout is expected to hold. Peer history is rewritten upstream and this repository's early history was rewritten too, so decay is the normal condition of an old receipt rather than evidence of a fabricated one.

Two consequences. A reader resolving an old citation and failing has learned nothing about the claim: re-derive it from the record's own `claim` and `separator` rows instead. And a *newly written* citation is different in kind — [`check-doc-hygiene.sh`](../scripts/check-doc-hygiene.sh) resolves every 40-hex string a commit range introduces that was not already in the tree, so a receipt is verified live at authoring time and never afterwards. Set `A12_REVISION_RANGE` to widen that range; the check reports `UNVERIFIABLE` rather than passing when a sibling checkout is absent.

Search reusable provenance entries with `rg -n '^<a id="src-' docs/SOURCES.md`, then follow the entry to its bounded family record under [`sources/`](sources/). Search the shard directly when updating a checkpoint. Add a route only when it is reusable by later work. A one-capsule source narrative belongs in working context and Git history, while a durable surprising mechanism belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).

### Engine routing rule — pick the layer by the question, not by habit

| Question | Authoritative layer | What it cannot establish |
|---|---|---|
| Which operations, diagnostics, or cases exist | runtime/tool class inventory and error enums | runtime behavior |
| General lowering, emission order, generated branch shape | semantics-bearing StringTemplate (`.st`) file | behavior delegated to a backing bean/runtime call |
| General lowering when the template interpolates a `*Code*` property | the corresponding codegen backing bean | runtime behavior of emitted calls |
| Exact order for one concrete authored shape | generated program for that shape | generality beyond the shape |
| One operation’s local meaning | runtime helper/class | reachability or interaction with other classes |
| Public result partition, application, or service orchestration | runtime-service/API layer | local evaluator details not visible there |
| Whether a source-derived account actually manifests | maintained kernel-executing differential/probe | completeness beyond its cases |

Use the CLI’s static consistency checks for admission claims; its runtime evaluation verbs run the peer interpreter. Follow the [static observation identity and limits](sources/cross-layer-routes.md#src-static-observation-route) before interpreting envelopes: `MVK_*` is extracted from a rendered message, and neither `verification` nor a code alone establishes a Kernel observation.

Observation commands use the owner-approved measurement checkout, while the primary peer checkout remains the read-only knowledge source. The [measurement pin and calibration](sources/cross-layer-routes.md#src-measurement-checkout-route) own exact identities and authorization limits. Revalidate availability before use; [probe procedures](TESTING-KERNEL-PROBES.md) own operating steps.

For runtime claims, consult the maintained probe’s [observation channels and limits](sources/cross-layer-routes.md#src-runtime-observation-route). Full, partial, computation and applied-result channels establish different claims; a schema version alone does not identify an artifact’s observed shape.

<a id="src-static-observation-route"></a>
- [Static observation identity and diagnostic limits](sources/cross-layer-routes.md#src-static-observation-route)
<a id="src-measurement-checkout-route"></a>
- [Measurement checkout, pin and calibration](sources/cross-layer-routes.md#src-measurement-checkout-route)
<a id="src-runtime-observation-route"></a>
- [Runtime observation channels and claim limits](sources/cross-layer-routes.md#src-runtime-observation-route)

The `.st` files are mandatory review inputs whenever generated control flow matters. They decide, among other things, rule-level early returns, computation alternative continuation, loop placement, exception handling, and validation-versus-computation structure. A template that only interpolates a backing-bean property does not decide the operation.

**Pass-through rule:** follow an interpolated attribute to the backing bean that computes it. Most small operation templates are pass-through. A citation such as “`CompositeOperation`” is ambiguous unless it says template, backing bean, or runtime class.

**Composition rule:** source reading of one runtime class can establish its local clause but not reachability, precedence, short-circuiting, or interaction between classes. Such claims remain hypotheses until a semantics-bearing template, backing bean, generated program, or probe establishes the composition.

**Route-engagement rule:** a size- or dialect-selected path must be shown to engage before its result is compared. Known Groovy-specific thresholds include calculation closure chunks and condition-line splitting. Template equality can be meaningless in pass-through regions; dialect asymmetry is a lead, not proof.

**Search hygiene:** exclude generated copies with an anchored `/build/` path. A bare `build` exclusion also removes `builder/` and `buildscripts/` and has already produced plausible undercounts. Treat a small count disagreement as a filter defect before a scope theory.

## Kernel repository entry points

<a id="a12-kernel--the-engine-ground-truth"></a>
<a id="a12-kernel-the-engine-ground-truth"></a>

The main reusable roots are:

- runtime core: [`kernel-rt/kernel-core-runtime/.../_30_8/internal/core/`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/core/);
- runtime format definitions: [`kernel-rt/kernel-core-runtime/.../_30_8/internal/formatdef/`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/formatdef/);
- parser/static checks: [`kernel-tool/kernel-core-parser/.../check/`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/java/com/mgmtp/a12/kernel/core/parser/internal/check/);
- parse-tree creation/representation: [`kernel-tool/kernel-core-parser/.../parsebaum/`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/java/com/mgmtp/a12/kernel/core/parser/internal/parsebaum/);
- static diagnostic identities and their message text: [`ParserErrorTypesEnum`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/java/com/mgmtp/a12/kernel/core/parser/internal/error/ParserErrorTypesEnum.java) and [`error_messages_en.properties`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/resources/internal/vk_parser_error_messages/error_messages_en.properties), which is where an `MVK_*` code found in an envelope is resolved back to its raising gate;
- declared field types and their format handling: [`kernel-md/kernel-md-a12internal/.../fieldtypes/`](../../a12-kernel/kernel-md/kernel-md-a12internal/src/main/java/com/mgmtp/a12/kernel/md/model/a12internal/fieldtypes/);
- condition grammar: [`GrammarOnly_ConditionParser.g4`](../../a12-kernel/kernel-tool/kernel-core-parser/src/main/antlr4/com/mgmtp/a12/kernel/core/parser/internal/grammar/gen/GrammarOnly_ConditionParser.g4), authoritative for surface spelling where an operator inventory is not;
- codegen templates: [`kernel-tool/kernel-core-codegen*/src/main/resources/internal/templates/`](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/resources/internal/templates/);
- codegen backing beans: [`kernel-tool/kernel-core-codegen/.../backingbeans/`](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/java/com/mgmtp/a12/kernel/core/codegen/internal/generator/backingbeans/);
- immutable DocumentV2 API: [`kernel-md-document-v2`](../../a12-kernel/kernel-md/kernel-md-document-v2/src/main/java/com/mgmtp/a12/kernel/md/document/apiV2/immutable/);
- runtime service/result assembly: [`kernel-md-runtime-service`](../../a12-kernel/kernel-md/kernel-md-runtime-service/src/main/java/com/mgmtp/a12/kernel/md/rt/);
- model API and codegen parameters: [`kernel-md-model-api`](../../a12-kernel/kernel-md/kernel-md-model-api/src/main/java/com/mgmtp/a12/kernel/md/model/api/) and [`kernel-md-model`](../../a12-kernel/kernel-md/kernel-md-model/src/main/java/com/mgmtp/a12/kernel/md/model/).

## Clause-to-source drill map

<a id="immutable-document-and-checked-input-construction-14"></a>
<a id="truth-scalar-operators-and-list-consumers-15-812"></a>
<a id="paths-repetition-and-checked-entities-910"></a>
<a id="presence-projection-and-extracted-sources-5-79-12"></a>
<a id="numeric-and-temporal-aggregate-primitives-56-11"></a>
<a id="group-lists-and-stringenumeration-policy-78-1214"></a>
<a id="temporal-values-and-calendar-behavior-6"></a>
<a id="computation-application-iteration-and-messages-9-1114"></a>

| Clause | Primary kernel loci | Typical peer route |
|---|---|---|
| §1 truth | `ValidierungsErgebnis`, `DreiWertBool`, condition templates, rule templates | interpreter truth/verdict algebra and property tests |
| §2 empty values | `BedingungsOperatorHelper`, `RuntimeController`, `VkBigDecimal`, `NumberCombiner`, type format definitions, row-gate templates | empty/polarity law and differential families |
| §3 formal/UNKNOWN | `CheckCommand`, `FormalChecker`, `ValidationCache`, `VkBigDecimal.NICHT_PRUEF_REL_ZAHL`, format definitions | formal-error, partial-validation, raw-cell tests |
| §4 required | `AutogeneratedRulesService`, `IndexFieldCache`, requiredness model API, preliminary validation controllers | required/partial-required differentials |
| §5 Number | numeric parser checkers, `CompositeOperation` backing bean, `VkBigDecimal`, `BedingungsOperatorHelper.vergleiche`, `FormatDefinitionZahl` | arithmetic, scale, power, wrapper, target, and aggregate laws |
| §6 temporal | date/time parser checkers and construction templates, `NoMetaModelChecks.checkTimeZone`, `MetaDataValidierungIntern.getTimeZone`, `ValidationDateParser`, `BedingungsOperatorHelper`, `DateUtil.clearTime`, `RuntimeController` | Date/Time/DateTime construction, DST, difference, shift, target tests |
| §7 String/pattern/custom field | `FormatDefinitionString`, `PatternUtils`, `LegalCharTester`, String checkers and conversion, custom-field model/runtime classes | String, pattern, charset, and custom-field tests |
| §8 Enumeration/value list | Enumeration model API, `CheckVergleichsBedingungImpl`, `CheckEntityListenUtils`, value-list checkers, `RuntimeController`, `ValidationCache` | Enumeration/category/value-list law and differential families |
| §9 repetition/iteration | `EntityIterator`, `KontextIterator`, `EbenenIterator`, `IterationNotValidVisitor`, `GroupFillCache`, RNU/index helpers, iteration templates | star, correlation, RNU, semantic-index, and partial-validation tests |
| §10 paths/references | parser path creators/checkers, `ExpandService`, `SemanticIndexLevelVisitor`, entity reference types, semantic-index routes | model loader, path, correlation, and static-legality tests |
| §11 computations | calculation dependency/normalization utilities, calculated-field backing beans, `calcDir/*.st`, `CalculationCache`, `CalculationController`, `CalculationCommand`, result service | computation engine plus computation differential/law families |
| §12 validation/polarity | rule backing beans/templates, `MainValidatorController`, `VkBigDecimal.kannGroesser`/`kannKleinerWerden`, partial-validation dispatch, message creation | full/partial/polarity and rule-emission tests |
| §13 messages | message model/API, `FehlerHandler`, `CheckCommand.ersetzeFeldParameter`, `DocumentComputationResultImpl`, service errortext grammar | message rendering/display and computation-channel tests |
| §14 custom condition | `ApplicationCondition.st`, `MainValidatorController.applikationsBedingung`, `CustomConditionWrapper`, `ICustomCondition` | custom-condition invocation tests |

This table names search loci, not semantic conclusions. The canonical account remains in [`spec/`](../spec/), and exact Lean coverage remains in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

### Reviewed inbound batches through 2026-09-08

Deleted from this hub; the records' full text is `docs/archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md` at `3831425df05ba9afecdf5805e80be4fad164ec6c`. The anchors below keep every existing citation resolving.

<a id="reviewed-numeric-scale-continuity"></a>
- Reviewed numeric-scale continuity
<a id="reviewed-pointer-and-operator-domain-batch"></a>
- Reviewed pointer and operator-domain batch
<a id="src-2026-09-06-ladder-handback-detail"></a>
<a id="reviewed-group-count-multiplicity-batch"></a>
- Reviewed group-count multiplicity batch
<a id="reviewed-group-operand-extent-and-coverage-batch"></a>
- Reviewed group-operand extent and coverage batch
<a id="reviewed-compute-result-granularity-and-cascade-clear-kinds--the-axis-the-computation-rows-were-queuing-measurements-for"></a>
- Reviewed compute result-granularity and cascade clear-kinds — the axis the computation rows were queuing measurements for
<a id="src-2026-09-07-extremum-and-orderability-handback"></a>
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
- `dependencies`: KF511’s dependency implementations and tests pin 21 static cases and 14 root observations in [the fixture](../../a12-rulekit/adapter/src/test/resources/checker-near-miss/containing-group-profiles.json). SPEC-02 acceptance covers singular GroupFilled, not ordinary lists.
- `filtered-fill`: KF512’s fill implementations and differential/replay tests check [the eighteen document/arm rows](../../a12-rulekit/adapter/src/test/resources/filtered-fill-decisions.json), 441 full plus 441 whole-root partial signatures. These reconcile SPEC-03.
- `limits`: finite single-level Number fields and fixed-root runtime scheduling; no new CLI or protocol. Wider scopes/kinds remain outside. SPEC-04 was excluded and remains pending.

### Inbound 2026-10-02c handback

<a id="inbound-2026-10-02c"></a>
#### Reviewed pending-queue dispositions

- `revision`: a12-dmkits `5ca76014c9bdcf8b9445b84e7343ea510ae91de8`; the cited count tests and common-read correction resolve and are ancestors of this tip.
- `receipt`: the received `2026-10-02c` letter has SHA-256 `8e0773c3b83ba1657ab3dbb2bf701a33383d7ebfe64800320af6d23dac228611`. Reconciliation uses the committed tests and replay, not the letter's prose.
- `count-route`: [count-side checkpoint](sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate) and [connective checkpoint](sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and); SPEC-06 is accepted for firing on the fixed full-validation carrier, without transferring polarity or attachment claims.
- `self-read-route`: [alternative-walk checkpoint](sources/computation-scheduling-probes.md#src-self-read-alternative-walk); SPEC-07 is accepted for ordered report placement and multiplicity on the three measured Number target topologies. This supersedes the earlier letter's common-first reading, not its rows.
- `scope`: SPEC-08 has no disposition in this handback. The peer's wider qualification summary is not a new local conformance claim.

### Inbound 2026-10-02a handback

<a id="inbound-2026-10-02a-provenance"></a>
#### Reviewed 2026-10-02a supplement — from two alternatives on an unguarded alternative's target reads go unjudged whatever its neighbours, each judged read reports its class in walk order, the projected class answers alone, and four division-walk controls pass or refuse as the walk predicts

The letter is the peer's `-2026-10-02a`, delivered by its session and frozen at SHA-256 `b4f98c0f12a3f470243aa75449d86a00b68e12ab03e7973fdfe41854cc680397`; it supplements the `-2026-10-02` letter. Its rows are `checkConsistency` verdicts at a12-dmkits `fb9f2720ed8d7ccd769c6566d7a8bcb4d07c3c82`, locked in adapter tests at three commits, each read here and holding the test file it names: `d56e5725afb8482de26a9dbcb737b6aa43143f6e` (`UnguardedAlternativeSelfReadAgreementTest`), `9c6e84d654062047d7b706921012b3d67acbfc90` (`SelfReadMultiplicityAgreementTest`) and `97cfb199a9d0844aa488e2ec7628b927b8750a8a` (`DivisionWalkAgreementTest`). Its carriers are root nonrepeatable targets only.

<a id="inbound-2026-10-02a-alternative-walk"></a>
**Claim.** Its §1 has two unconditional alternatives draw `MVK_ERROR_EMPTY_PRECONDITION` alone with no preconditioned neighbour, either one reading the target or both, while a sole unconditional alternative draws the target-read class; the projected class is reported in every arrangement, with no empty class beside it. Its §2 reports the plain target-read class once per judged read, a precondition's reads included, and the empty class once, at the first unconditional alternative. Its §3 has `[Amount] / [Rate] + [Rate] / [Amount]`, the same with `-`, and `[Amount] / {[Rate] / [Amount]}` reach the scale class and `{[Amount] / [Rate] / [Amount]}` draw `MVK_TOO_MANY_DIV_FOR_CALC`. Its §4 is a source reading of the division walk and a single-walk reading of §1 and §2, both offered as hypotheses.

**Classification.** Inbound from committed revisions; [`spec/09`](../spec/09-computations.md)'s stages bullet drops its "beside a preconditioned alternative" condition and places the projected class. The letter's reading that the common precondition is judged first does not hold: this project's [alternative-walk grid](sources/computation-scheduling-probes.md#src-self-read-alternative-walk) places it at the first judged alternative, now reconciled by the [2026-10-02c disposition](#inbound-2026-10-02c). §4 is not adopted: the spec's division-walk clause already states the cut the reading describes, and no row here separates the reading from it.

**Lean.** The Number table already left an unguarded alternative's own reads unjudged from two alternatives on, without needing a guarded neighbour. The String table now projects the empty class, and §3's four rows are locked in [`OperationNodeGates`](../A12Kernel/Conformance/NumericComputation/OperationNodeGates.lean). The projected class against the empty class has no Lean carrier, and a String operation reading its target is refused before the table can leave it unjudged ([SG29](gaps/paths-and-groups.md#gap-sg29), [SG7](gaps/strings-and-messages.md#gap-sg7)).

### Inbound 2026-10-02 handback

<a id="inbound-2026-10-02-provenance"></a>
#### Reviewed 2026-10-02 handback — every pending entry from `SPEC-2026-10-01-02` to `SPEC-2026-10-02-05` holds on the peer's own carriers, a day landing's re-fit is judged against the expected date, a partially known Date is selected as its earliest day, and two more rule shapes are evaluated without content

The letter is the peer's `-2026-10-02`, delivered by its session and frozen at SHA-256 `01501b22aa9b3783e42298cfb64a344dd45712289074470da742c8e736322594`; it replaces the `-2026-10-01a` letter. Its rows are the peer's adapter tests at six a12-dmkits commits, each read here and holding the test file it names: `cd37d3ccb6df7e7094cdc1b7d77f970f50199de9` (message parameters), `d3cb6f74f66a18c7be36e5c2e1dbdc87e89006b4` (static operand gates), `b88dc54ff62cc38c72e0d04d7de213fe1a93ca25` (runtime), `3bab32bccfb30681d7c86f44c4e40b4d82a6765a` (rule buckets), `a7ed04ad35925cd2fe459965db7e9c0fafce5100` (partial-Date selection) and `ed58c5139655fe34e3d4a3305ed34a3180f10829` (day-step rows). Static rows are the Kernel's consistency check; runtime rows are dynamic Groovy, static Java and the peer's interpreter agreeing on one document. Its §12 states mechanisms its rows do not separate and is recorded as no claim.

<a id="inbound-2026-10-02-dispositions"></a>
**Claim.** Its §1 to §11 confirm the delta rows of all eleven pending entries, each on the commit its ledger entry names, and the entries are accepted on them. Beyond those rows, their additions are recorded on the entries themselves.

<a id="inbound-2026-10-02-day-landing"></a>
**Claim.** Its §7 (`ComputedDateTimeJoinDiffTest` at `b88dc54f`, `DayStepLandingDiffTest` at `ed58c513`) separates two readings of the day landing's re-fit. `AddDays(2024-10-27T00:30, 1)` gives `2024-10-28T00:30` and the peer's own `AddDays(2024-03-30T23:30, 1)` gives `2024-03-31T23:30` on both strategies, where keeping a re-fit only when it preserves the raw landing's own date gives `2024-10-27T23:30` and `2024-04-01T00:30`. `DifferenceInDays(2024-10-26T00:30, 2024-10-28T00:00)` is `1` and `(2024-03-29T23:30, 2024-03-31T23:45)` is `2`, against `2` and `1` on that reading; the peer reports the JDK's `GregorianCalendar` agreeing.

**Classification.** Inbound from committed, reviewed revisions; [`spec/05`](../spec/05-dates-and-time.md) §5's landing bullet now names the expected date and these rows.

**Lean.** Already this account: the re-fit is compared with the expected date, and the four values are locked in [`BerlinLegacyCalendarArithmetic`](../A12Kernel/Conformance/BerlinLegacyCalendarArithmetic.lean) and [`DateTimeDayDifference`](../A12Kernel/Conformance/DateTimeDayDifference.lean). Its Date-source rows are not locked.

<a id="inbound-2026-10-02-partial-date-readers"></a>
**Claim.** Its §10 (`FirstFilledValuePartialDateDiffTest` at `a7ed04ad`) has `FirstFilledValue` select a partially known Date as its earliest day, `2024-06-00` as `2024-06-01` and `2024-00-00` as `2024-01-01`, directly, starred, over a group and keyed, while `0000-00-00` and a malformed value leave the selection unknown and end the walk. A copy of the selection into a full Date takes the first day, and a malformed or unknown-year value clears it. `PartialDatePresenceDiffTest` at `ed58c513` adds stored-text uniqueness at `MONTH_OPTIONAL` and `YEAR_OPTIONAL` and down a starred column.

**Classification.** Inbound; [`spec/05`](../spec/05-dates-and-time.md)'s partial-Date paragraph takes the selection.

**Lean.** Not yet compared on these rows.

<a id="inbound-2026-10-02-rule-buckets"></a>
**Claim.** Its §11 (`RuleBucketGateDiffTest` at `3bab32bc`) narrows which comparisons are evaluated on an instance without content: `2 > NumberOfFilledGroups(…)`, `Abs(NumberOfFilledGroups(…)) < 2`, `NumberOfFilledFields(…) < 1` and `NumberOfDifferentValues(…) < 1` fire over the three blank documents, while `NumberOfFilledGroups(…) > 5 Or [W] < 5` stays silent. A rule naming a second root fires there too, and a rule on a repeatable root whose error field it does not iterate fires once, at the root's first row.

**Classification.** Inbound and narrowing: [`spec/03`](../spec/03-empty-and-required.md) §2's "anywhere in either operation" no longer holds. This project's [rule-bucket grid](sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate) measures the remaining arms before the clause is restated.

**Lean.** Diverged on the large-side row and did not count `NumberOfDifferentValues`, and its once plan gated a repeatable-root rule on the root's content; all three are corrected with that grid. The [ordinary execution owner](implementation/validation-messages-and-custom.md#cap-ordinary-once-repeatable-execution) now records fixed cross-root numeric admission and its static content-gate projection. The same-root qualification in `spec/03` A.4 reconciles its field-only sentence with this already accepted second-root clause.

### Inbound 2026-10-01a handback

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `cdb479d937968be6e4a839191fe6cd9dd7c86fbd`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-10-01a-provenance"></a>
- Inbound 2026 10 01a provenance
<a id="inbound-2026-10-01a-event-order"></a>
- Inbound 2026 10 01a event order — [`SPEC-2026-10-01-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-10-01-01)
<a id="inbound-2026-10-01a-parent-walk-and-dotted-names"></a>
- Inbound 2026 10 01a parent walk and dotted names

### Inbound 2026-10-01 handback

Deleted from this hub; the records' full text is `docs/SOURCES.md` at `cdb479d937968be6e4a839191fe6cd9dd7c86fbd`. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-10-01-provenance"></a>
- Inbound 2026 10 01 provenance
<a id="inbound-2026-10-01-group-arguments"></a>
- Inbound 2026 10 01 group arguments — [`SPEC-2026-09-30-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-30-01)
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

## Provenance checkpoint index

Search stable `src-` anchors in this hub, then follow the link to the bounded family shard. Exact revisions and source-level claim limits remain in those records.

### Kernel lock source index

<a id="src-kernel-lock-index"></a>
- [Kernel lock index](sources/kernel-locks.md#src-kernel-lock-index)

### DateRange construction source checkpoints

<a id="src-full-date-stored-input"></a>
- [Full date stored input](sources/date-range-construction.md#src-full-date-stored-input)
<a id="src-date-range-stored-input"></a>
- [Date range stored input](sources/date-range-construction.md#src-date-range-stored-input)
<a id="src-date-range-construction-equality"></a>
- [Date range construction equality](sources/date-range-construction.md#src-date-range-construction-equality)
<a id="src-date-range-year-fragment-construction"></a>
- [Year-fragment DateRange construction](sources/date-range-construction.md#src-date-range-year-fragment-construction)
<a id="src-date-range-year-month-fragment-construction"></a>
- [Year-month-fragment DateRange construction](sources/date-range-construction.md#src-date-range-year-month-fragment-construction)
<a id="src-date-range-base-year-fragment-construction"></a>
- [Base-Year and yearless DateRange fragments](sources/date-range-construction.md#src-date-range-base-year-fragment-construction)
<a id="src-date-range-yearless-construction-target"></a>
- [Yearless DateRange construction targets](sources/date-range-construction.md#src-date-range-yearless-construction-target)
<a id="src-indexed-date-range-construction-target"></a>
- [Indexed date range construction target](sources/date-range-construction.md#src-indexed-date-range-construction-target)
<a id="src-date-range-bound-extraction"></a>
- [Date range bound extraction](sources/date-range-construction.md#src-date-range-bound-extraction)
<a id="src-date-range-plural-overlap"></a>
- [Date range plural overlap](sources/date-range-construction.md#src-date-range-plural-overlap)
<a id="src-date-range-fragment-first-filled"></a>
- [Date range fragment first filled](sources/date-range-construction.md#src-date-range-fragment-first-filled)
<a id="src-date-range-direct-first-filled"></a>
- [Date range direct first filled](sources/date-range-construction.md#src-date-range-direct-first-filled)
<a id="src-date-range-yearless-overlap"></a>
- [Date range yearless overlap](sources/date-range-construction.md#src-date-range-yearless-overlap)
<a id="src-date-range-mixed-year-overlap"></a>
- [Date range mixed year overlap](sources/date-range-construction.md#src-date-range-mixed-year-overlap)
<a id="src-date-range-bound-base-year"></a>
- [Date range bound base year](sources/date-range-construction.md#src-date-range-bound-base-year)
<a id="src-date-range-component-set-crossing"></a>
- [Date range component set crossing](sources/date-range-construction.md#src-date-range-component-set-crossing)
<a id="src-date-range-construction-operand-grid"></a>
- [Date range construction operand grid](sources/date-range-construction.md#src-date-range-construction-operand-grid)
<a id="src-date-range-exact-and-configured-constructor-targets"></a>
- [Date range exact and configured constructor targets](sources/date-range-construction.md#src-date-range-exact-and-configured-constructor-targets)
<a id="src-date-range-year-fragment-constructor-target"></a>
- [Date range year fragment constructor target](sources/date-range-construction.md#src-date-range-year-fragment-constructor-target)
<a id="src-date-range-construction-target-crossing"></a>
- [Date range construction target crossing](sources/date-range-construction.md#src-date-range-construction-target-crossing)

### Temporal and message source checkpoints

<a id="src-semantic-index-kind-independence"></a>
- [Semantic index kind independence](sources/temporal-and-message-probes.md#src-semantic-index-kind-independence)
<a id="src-rule-message-parameter-grammar"></a>
- [Rule message parameter grammar](sources/message-and-pointer-probes.md#src-rule-message-parameter-grammar)
<a id="src-rule-message-parameter-rendering"></a>
- [Rule message parameter rendering](sources/message-and-pointer-probes.md#src-rule-message-parameter-rendering)
<a id="src-time-datetime-stored-input"></a>
- [Time datetime stored input](sources/temporal-and-message-probes.md#src-time-datetime-stored-input)
<a id="src-temporal-operation-granularity-separability"></a>
- [Temporal operation granularity separability](sources/temporal-and-message-probes.md#src-temporal-operation-granularity-separability)
<a id="src-declared-format-temporal-input"></a>
- [Declared format temporal input](sources/temporal-and-message-probes.md#src-declared-format-temporal-input)
<a id="src-temporal-format-vocabulary"></a>
- [Temporal format vocabulary](sources/temporal-and-message-probes.md#src-temporal-format-vocabulary)
<a id="src-partial-date-input-causes"></a>
- [Partial date input causes](sources/temporal-and-message-probes.md#src-partial-date-input-causes)
<a id="src-partial-date-presence"></a>
- [Partial-Date, component-omitting Date and DateFragment presence, measured 2026-10-02](sources/temporal-and-message-probes.md#src-partial-date-presence)
<a id="src-partial-date-readers"></a>
- [Partial-Date requiredness, group content and uniqueness; computed fragment identity and yearless computation, measured 2026-10-02](sources/temporal-and-message-probes.md#src-partial-date-readers)
<a id="src-date-decoded-identity-witness"></a>
- [Date decoded identity witness](sources/temporal-and-message-probes.md#src-date-decoded-identity-witness)
<a id="src-temporal-aggregate-gate"></a>
- [Temporal aggregate gate](sources/temporal-and-message-probes.md#src-temporal-aggregate-gate)
<a id="src-pr2-date-extraction-diagnostics"></a>
- [Date-extraction diagnostics](sources/temporal-and-message-probes.md#src-pr2-date-extraction-diagnostics)
<a id="src-message-address-dialects"></a>
- [Operand-dependent message-address dialects](sources/message-and-pointer-probes.md#src-message-address-dialects)

<a id="src-omitting-date-formats"></a>
- [Component-omitting DATE storage](sources/temporal-and-message-probes.md#src-omitting-date-formats)
<a id="src-filled-field-count"></a>
- [`NumberOfFilledFields` formal invalidity](sources/temporal-and-message-probes.md#src-filled-field-count)
<a id="src-date-from-datetime"></a>
- [`DateFromDateTime` component gates](sources/temporal-and-message-probes.md#src-date-from-datetime)
<a id="src-date-from-datetime-computation"></a>
- [`DateFromDateTime` scalar targets](sources/temporal-and-message-probes.md#src-date-from-datetime-computation)
<a id="src-date-from-datetime-repeatable-computation"></a>
- [`DateFromDateTime` repeatable targets](sources/temporal-and-message-probes.md#src-date-from-datetime-repeatable-computation)
<a id="src-recursive-date-components"></a>
- [Date components](sources/temporal-runtime-fold-probes.md#src-recursive-date-components)
<a id="src-temporal-numeric-amounts"></a>
- [Temporal numeric amounts](sources/temporal-runtime-fold-probes.md#src-temporal-numeric-amounts)

<a id="src-mixed-baseyear-sources"></a>
- [Mixed BaseYear sources](sources/temporal-runtime-fold-probes.md#src-mixed-baseyear-sources)
<a id="src-recursive-difference-effects"></a>
- [Recursive difference effects](sources/temporal-runtime-fold-probes.md#src-recursive-difference-effects)
<a id="src-indexed-partial-date-endpoints"></a>
- [Indexed partial-Date endpoints and clearing](sources/temporal-and-message-probes.md#src-indexed-partial-date-endpoints)
<a id="src-value-as-date-locus"></a>
- [Partial-Date `ValueAsDate` operand placement](sources/temporal-and-message-probes.md#src-value-as-date-locus)
<a id="src-rule-message-semantic-index"></a>
- [Semantic-index suffixes in rule-message parameters](sources/message-and-pointer-probes.md#src-rule-message-semantic-index)
<a id="src-date-range-endpoint-shapes"></a>
- [Admitted DateRange endpoint shapes](sources/temporal-and-message-probes.md#src-date-range-endpoint-shapes)
<a id="src-nested-rule-locus"></a>
- [Nested rule locus](sources/temporal-and-message-probes.md#src-nested-rule-locus)
<a id="src-computation-operand-scope"></a>
- [Computation operand scope](sources/temporal-and-message-probes.md#src-computation-operand-scope)
<a id="src-string-integer-source-scale-suppression"></a>
- [String integer source scale suppression](sources/computation-placement-and-constant-probes.md#src-string-integer-source-scale-suppression)
<a id="src-date-range-bound-component-scale-suppression"></a>
- [Date range bound component scale suppression](sources/temporal-and-message-probes.md#src-date-range-bound-component-scale-suppression)
<a id="src-date-range-bound-component-runtime"></a>
- [Date range bound component runtime](sources/temporal-and-message-probes.md#src-date-range-bound-component-runtime)
<a id="src-date-range-bound-component"></a>
- [Date range bound component](sources/temporal-and-message-probes.md#src-date-range-bound-component)
<a id="src-date-range-yearless-locus"></a>
- [Date range yearless locus](sources/temporal-and-message-probes.md#src-date-range-yearless-locus)
<a id="src-date-range-rule-locus"></a>
- [Date range rule locus](sources/temporal-and-message-probes.md#src-date-range-rule-locus)
<a id="src-date-range-list-crossing"></a>
- [Date range list crossing](sources/temporal-and-message-probes.md#src-date-range-list-crossing)
<a id="src-date-range-interpretation-first-filled"></a>
- [Date range interpretation first filled](sources/temporal-and-message-probes.md#src-date-range-interpretation-first-filled)
<a id="src-date-range-interpretation-first-filled-star"></a>
- [Date range interpretation first filled star](sources/temporal-and-message-probes.md#src-date-range-interpretation-first-filled-star)
<a id="src-date-range-repeatable-first-filled"></a>
- [Date range repeatable first filled](sources/repeatable-temporal-computation-probes.md#src-date-range-repeatable-first-filled)
<a id="src-datetime-repeatable-first-filled"></a>
- [Datetime repeatable first filled](sources/repeatable-temporal-computation-probes.md#src-datetime-repeatable-first-filled)
<a id="src-full-date-repeatable-first-filled"></a>
- [Full date repeatable first filled](sources/repeatable-temporal-computation-probes.md#src-full-date-repeatable-first-filled)
<a id="src-time-repeatable-first-filled"></a>
- [Time repeatable first filled](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-first-filled)
<a id="src-time-repeatable-constant-construction"></a>
- [Time repeatable constant construction](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-constant-construction)
<a id="src-time-repeatable-number-components"></a>
- [Time repeatable number components](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-number-components)
<a id="src-time-repeatable-string-components"></a>
- [Time repeatable string components](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-string-components)
<a id="src-time-repeatable-direct-extractor-components"></a>
- [Time repeatable direct extractor components](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-direct-extractor-components)
<a id="src-datetime-component-sibling-parallel-refusal"></a>
- [Sibling-parallel refusal for DateTime component extractors, measured locally 2026-08-27](sources/temporal-and-message-probes.md#src-datetime-component-sibling-parallel-refusal)
<a id="src-date-range-unconfigured-interpretation-first-filled-star"></a>
- [Date range unconfigured interpretation first filled star](sources/temporal-and-message-probes.md#src-date-range-unconfigured-interpretation-first-filled-star)
<a id="src-date-range-unconfigured-bound"></a>
- [Date range unconfigured bound](sources/temporal-and-message-probes.md#src-date-range-unconfigured-bound)
<a id="src-date-range-interpretation-comparison"></a>
- [Date range interpretation comparison](sources/temporal-and-message-probes.md#src-date-range-interpretation-comparison)
<a id="src-date-range-stored-comparison"></a>
- [Date range stored comparison](sources/temporal-and-message-probes.md#src-date-range-stored-comparison)
<a id="src-date-range-interpretation-overlap-refusal"></a>
- [Date range interpretation overlap refusal](sources/temporal-and-message-probes.md#src-date-range-interpretation-overlap-refusal)
<a id="src-date-range-year-interpretation"></a>
- [Date range year interpretation](sources/temporal-and-message-probes.md#src-date-range-year-interpretation)
<a id="src-date-range-yearless-group-carrier"></a>
- [Date range yearless group carrier](sources/temporal-and-message-probes.md#src-date-range-yearless-group-carrier)
<a id="src-date-range-starred-yearless-overlap"></a>
- [Date range starred yearless overlap](sources/temporal-and-message-probes.md#src-date-range-starred-yearless-overlap)
<a id="src-date-range-plural-year-class"></a>
- [Date range plural year class](sources/temporal-and-message-probes.md#src-date-range-plural-year-class)
<a id="src-keyed-parameter-admits-the-index-field-only"></a>
- [Keyed parameter admits the index field only](sources/message-and-pointer-probes.md#src-keyed-parameter-admits-the-index-field-only)

<a id="src-rulegroup-shorthand-root-gate"></a>
- [Rulegroup shorthand root gate](sources/message-and-pointer-probes.md#src-rulegroup-shorthand-root-gate)
<a id="src-rulegroup-root-gate-on-the-rule-carrier"></a>
- [That same root-group refusal is the validation-rule carrier's too](sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier)

<a id="src-2026-09-05-german-shorthand-render-reconciliation"></a>
- [2026 09 05 german shorthand render reconciliation](sources/message-and-pointer-probes.md#src-2026-09-05-german-shorthand-render-reconciliation)

<a id="src-2026-09-05-group-parameter-render-reconciliation"></a>
- [2026 09 05 group parameter render reconciliation](sources/message-and-pointer-probes.md#src-2026-09-05-group-parameter-render-reconciliation)

<a id="src-2026-09-05-second-reconciliation"></a>
- [Reviewed a12-dmkits letter accepting the two-gate entry, correcting its attribution, and narrowing two clauses this project had already accepted](sources/computation-placement-and-constant-probes.md#src-2026-09-05-second-reconciliation) — also the route for their shipped `dmtool operators Having` gate text, read by running the launcher at `ede777e55`

<a id="src-2026-09-05-reconciliation"></a>
- [2026 09 05 reconciliation](sources/computation-placement-and-constant-probes.md#src-2026-09-05-reconciliation)

<a id="src-2026-09-06-ladder-handback"></a>
- [Reviewed 2026-09-06 a12-dmkits handback re-deriving the constant-assignment ladder and shipping its corrective](#src-2026-09-06-ladder-handback-detail)
<a id="src-2026-09-04-reconciliation"></a>
- [2026 09 04 reconciliation](sources/computation-placement-and-constant-probes.md#src-2026-09-04-reconciliation)
<a id="src-2026-09-03-reconciliation"></a>
- [2026 09 03 reconciliation](sources/computation-placement-and-constant-probes.md#src-2026-09-03-reconciliation)
<a id="src-2026-08-30-reconciliation"></a>
- [2026 08 30 reconciliation](sources/computation-placement-and-constant-probes.md#src-2026-08-30-reconciliation)
<a id="src-2026-08-29-reconciliation"></a>
- [2026 08 29 reconciliation](sources/computation-placement-and-constant-probes.md#src-2026-08-29-reconciliation)
<a id="src-date-range-direct-list-cross-group-sources"></a>
- [Date range direct list cross group sources](sources/computation-placement-and-constant-probes.md#src-date-range-direct-list-cross-group-sources)
<a id="src-having-filter-condition-scope"></a>
- [Having binds the filtered level and admits group-presence leaves](sources/having-filter-probes.md#src-having-filter-condition-scope)
<a id="src-having-filter-nontrue-row"></a>
- [A non-true `Having` conjunct drops its own row, and the empty-as-zero rule does not reach a malformed operand](sources/having-filter-probes.md#src-having-filter-nontrue-row)
<a id="src-having-filter-condition-grammar"></a>
- [Having uses ordinary condition grammar and observed refusal classes](sources/having-filter-probes.md#src-having-filter-condition-grammar)
<a id="src-having-filter-presence-leaf"></a>
- [Having filter presence leaf](sources/having-filter-probes.md#src-having-filter-presence-leaf)
<a id="src-having-filter-disjunction"></a>
- [Having filter disjunction](sources/having-filter-probes.md#src-having-filter-disjunction)
<a id="src-string-inequality-empty-operand"></a>
- [String inequality empty operand](sources/having-filter-probes.md#src-string-inequality-empty-operand)
<a id="src-filtered-aggregate-computation-arm"></a>
- [Filtered aggregate computation arm](sources/having-filter-probes.md#src-filtered-aggregate-computation-arm)
<a id="src-and-order-computation-arm"></a>
- [And order computation arm](sources/having-filter-probes.md#src-and-order-computation-arm)
<a id="src-off-path-captured-filter-runtime"></a>
- [Off path captured filter runtime](sources/having-filter-probes.md#src-off-path-captured-filter-runtime)

<a id="src-filter-scope-versus-iteration-gates"></a>
- [Filter scope versus iteration gates](sources/having-filter-probes.md#src-filter-scope-versus-iteration-gates)

<a id="src-repetition-numeric-source-kinds"></a>
- [Repetition numeric source kinds](sources/group-and-iteration-probes.md#src-repetition-numeric-source-kinds)

<a id="src-repetition-operand-partial-relevance"></a>
- [Repetition operand partial relevance](sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance)

<a id="src-ancestor-declared-repetition-computation"></a>
- [Ancestor declared repetition computation](sources/group-and-iteration-probes.md#src-ancestor-declared-repetition-computation)

<a id="src-repetition-aggregate-operand-scope"></a>
- [Repetition aggregate operand scope](sources/group-and-iteration-probes.md#src-repetition-aggregate-operand-scope)

<a id="src-repetition-source-kinds-runtime"></a>
- [Repetition source kinds runtime](sources/group-and-iteration-probes.md#src-repetition-source-kinds-runtime)
<a id="src-currentrepetition-operand-carriers"></a>
- [Currentrepetition operand carriers](sources/group-and-iteration-probes.md#src-currentrepetition-operand-carriers)

<a id="src-filter-repetition-reference-reads-its-path"></a>
- [Filter repetition reference reads its path](sources/having-filter-probes.md#src-filter-repetition-reference-reads-its-path)

<a id="src-fixed-repetition-having"></a>
- [Fixed repetition having](sources/having-filter-probes.md#src-fixed-repetition-having)

<a id="src-filter-reference-above-the-star"></a>
- [Filter reference above the star](sources/having-filter-probes.md#src-filter-reference-above-the-star)

<a id="src-parameter-token-versus-group-declaration-alphabet"></a>
- [Parameter token versus group declaration alphabet](sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet)

<a id="src-terminal-bundle-on-the-computation-carrier"></a>
- [Terminal bundle on the computation carrier](sources/message-and-pointer-probes.md#src-terminal-bundle-on-the-computation-carrier)

<a id="src-name-position-index-terminal"></a>
- [Name position index terminal](sources/message-and-pointer-probes.md#src-name-position-index-terminal)
<a id="src-message-template-character-repertoire"></a>
- [The rule-message template's repertoire is the BMP rather than printable ASCII, its control class covers the C1 block and the invisible format characters, the ASCII bound belongs to a parameter body alone, and the name position's condition-reference gate is `INVALID_FIELD`](sources/message-and-pointer-probes.md#src-message-template-character-repertoire)

<a id="src-message-repertoire-co-reporting"></a>
- [Rule-message repertoire findings coexist with named failures; full diagnostic lists correct the priority inferred from code-only observations](sources/message-and-pointer-probes.md#src-message-repertoire-co-reporting)

<a id="src-message-category-gate-order"></a>
- [Rule-message entity and membership/index failures precede an empty category name](sources/message-and-pointer-probes.md#src-message-category-gate-order)

<a id="src-message-parameter-surface-and-iteration-gates"></a>
- [Rule-message parameter grammar and iteration gates](sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates)

<a id="src-index-terminal-refusal-classes"></a>
- [The `index(...)` terminal's complete refusal-class set: `->Category` admitted on an Enumeration index field with its own `INVALID_CATEGORY`, multiplicity refused `INVALID_INDEX_FIELD_AMBIGUOUS`, and a cross-check against the rule's own condition refusing a keyed or starred reference `INVALID_INDEX_FIELD_REP_ITER`](sources/message-and-pointer-probes.md#src-index-terminal-refusal-classes)
<a id="src-starred-group-value-count-classes"></a>
- [A starred group naming nothing answers in the segment order on the filled-field and value-count carriers too, and a fixed group below a star is admitted on every one of them](sources/path-resolution-class-probes.md#src-starred-group-value-count-classes)
<a id="src-pattern-and-key-resolver-classes"></a>
- [Pattern and key resolver classes](sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)
<a id="src-group-operand-resolution-classes"></a>
- [Group operand resolution classes](sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)
<a id="src-short-name-ambiguity-every-carrier"></a>
- [Short name ambiguity every carrier](sources/path-resolution-class-probes.md#src-short-name-ambiguity-every-carrier)
<a id="src-starred-path-segment-order"></a>
- [Starred path segment order](sources/path-resolution-class-probes.md#src-starred-path-segment-order)
<a id="src-resolver-failure-classes-every-carrier"></a>
- [Resolver failure classes every carrier](sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)
<a id="src-condition-class-projection"></a>
- [Condition class projection](sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection)
<a id="src-computation-self-read-sweep"></a>
- [A computation reading its own target draws the target-read class on every carrier measured once the read is reached, once per occurrence, a precondition's read included](sources/diagnostic-class-vocabulary-and-sweeps.md#src-computation-self-read-sweep)
<a id="src-field-copy-comparison-grid"></a>
- [Field copy comparison grid](sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)
<a id="src-entity-list-kind-empty-and-root-carriers"></a>
- [Entity list kind empty and root carriers](sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)
<a id="src-value-list-slot-kind-set"></a>
- [The String-literal value list's slot gate is one class over seven kinds and does not read the slot's shape, with NUMBER inside the admitted set](sources/static-admission-and-class-probes.md#src-value-list-slot-kind-set)
<a id="src-variant-filter-declaration-omission"></a>
- [An `ONLY` variant filter removes a declaration from the model, so a broken rule reports clean while a filtered field breaks every reference to it](sources/static-admission-and-class-probes.md#src-variant-filter-declaration-omission)
<a id="src-comparison-constant-gate-immediacy"></a>
- [The comparison's constant gate asks whether both sides are immediate written-out literals, not whether either reads a cell](sources/static-admission-and-class-probes.md#src-comparison-constant-gate-immediacy)

<a id="src-numeric-field-forms"></a>
- [Numeric field forms, both-arm runtime](sources/evaluation-and-application-routes.md#src-numeric-field-forms)

<a id="src-rounding-argument"></a>
- [Rounding places distinguish signed-64-bit overflow from ordinary scale refusal](sources/static-admission-and-class-probes.md#src-rounding-argument)

<a id="src-temporal-extractor-entry"></a>
- [Numeric extractors reject direct temporal literals while DateTime projections admit complete ones](sources/static-admission-and-class-probes.md#src-temporal-extractor-entry)
<a id="src-enumeration-comparability-diagnostics"></a>
- [Direct Enumeration comparability retains display-class and mapping-conflict diagnostics](sources/static-admission-and-class-probes.md#src-enumeration-comparability-diagnostics)
<a id="src-comparison-entry-gates"></a>
- [Comparison entry, grouped clocks, pattern slots and tolerance dispatch](sources/static-admission-and-class-probes.md#src-comparison-entry-gates)

<a id="src-arithmetic-shape-gates"></a>
- [The four arithmetic shape gates: a division limit scoped per multiplicative region whose grouped form the Kernel deliberately admits, a left-only power test, an exponent gate over derived scale, and a constant limit counting constants rather than operands](sources/static-admission-and-class-probes.md#src-arithmetic-shape-gates)
<a id="src-nonrepeatable-index-field-gate"></a>
- [The non-repeatable indexed group's parameter gate, whose single admitting shape is an Enumeration index field declaring one value that is also its S-value, with the repeatable-carrier control that attributes the refusal to repeatability rather than to the field's kind](sources/message-and-pointer-probes.md#src-nonrepeatable-index-field-gate)

<a id="src-index-terminal-admitting-spelling"></a>
- [`index(...)` **is** admissible — a bare index-field short name plus the mandatory lowercase `.value` suffix, with the index field on the error field's own path — refuting the earlier no-witness row](sources/message-and-pointer-probes.md#src-index-terminal-admitting-spelling)

<a id="src-index-german-suffix"></a>
- [Across the `en_US` and `de_DE` message locales measured, the `index(...)` value suffix follows the condition language, `Wert` under German and `value` under English, each refusing the other](sources/message-and-pointer-probes.md#src-index-german-suffix)

<a id="src-value-list-base-type-cross-pairs"></a>
- [Value list base type cross pairs](sources/static-admission-and-class-probes.md#src-value-list-base-type-cross-pairs)
<a id="src-field-value-read-grid"></a>
- [Field value read grid](sources/static-admission-and-class-probes.md#src-field-value-read-grid)
<a id="src-field-value-read-carriers"></a>
- [Field value read carriers](sources/static-admission-and-class-probes.md#src-field-value-read-carriers)
<a id="src-field-value-read-remaining-sites"></a>
- [Field value read remaining sites](sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)
<a id="src-field-value-read-predictions"></a>
- [Field value read predictions](sources/static-admission-and-class-probes.md#src-field-value-read-predictions)
<a id="src-value-list-cross-list-repeat-order"></a>
- [Value list cross list repeat order](sources/static-admission-and-class-probes.md#src-value-list-cross-list-repeat-order)
<a id="src-ordering-date-class-reads-the-pair"></a>
- [Ordering date class reads the pair](sources/static-admission-and-class-probes.md#src-ordering-date-class-reads-the-pair)
<a id="src-value-list-quantifier-kind-gate-partitions-three-ways"></a>
- [The value-list quantifiers' kind gate partitions three ways, they admit a sole field operand, and an Enumeration field side is legal against valid tokens](sources/static-admission-and-class-probes.md#src-value-list-quantifier-kind-gate-partitions-three-ways)
<a id="src-partial-date-precision-operand-gate"></a>
- [A partially known Date is refused as an extremum or distinct-count operand and admitted as a uniqueness operand](sources/repeatable-temporal-computation-probes.md#src-partial-date-precision-operand-gate)
<a id="src-temporal-computed-target-gate-reads-format-not-kind"></a>
- [A temporal computed target admits a value by its declared format, never by its declared kind, across five computation families](sources/repeatable-temporal-computation-probes.md#src-temporal-computed-target-gate-reads-format-not-kind)
<a id="src-keyed-date-range-overlap-admits-both-sides"></a>
- [A semantic-index keyed operand is admitted on both sides of either overlap operator, and the duplicate identity includes the key](sources/static-admission-and-class-probes.md#src-keyed-date-range-overlap-admits-both-sides)
<a id="src-first-filled-admits-a-repeatable-target"></a>
- [A first-filled computation reading a starred source admits a repeatable target, on four carriers](sources/static-admission-and-class-probes.md#src-first-filled-admits-a-repeatable-target)
<a id="src-suppress-warning-directive-scopes-the-whole-condition"></a>
- [`@SuppressWarning` is a condition preamble whose scope is the whole condition, and only one warning is suppressible](sources/static-admission-and-class-probes.md#src-suppress-warning-directive-scopes-the-whole-condition)
<a id="src-value-list-literal-domain-is-the-union"></a>
- [A value list's Enumeration literals must name a token in the union of the selected domains, and the duplicate-operand gate splits by read form](sources/static-admission-and-class-probes.md#src-value-list-literal-domain-is-the-union)
<a id="src-having-filter-class-is-carrier-independent-and-first-defect-wins"></a>
- [A Having filter's static class is carrier-independent across six wrappers, and a multi-leaf filter reports its first defective leaf](sources/static-admission-and-class-probes.md#src-having-filter-class-is-carrier-independent-and-first-defect-wins)
<a id="src-temporal-group-operand-follows-its-own-operator"></a>
- [A group operand is admitted at both temporal uniqueness carriers, and its expansion is gated by that operator's own rule](sources/static-admission-and-class-probes.md#src-temporal-group-operand-follows-its-own-operator)
<a id="src-constant-computation-admits-a-repeatable-target"></a>
- [A constant computation admits a repeatable target at every declaring-group choice; only a star in a precondition refuses](sources/static-admission-and-class-probes.md#src-constant-computation-admits-a-repeatable-target)
<a id="src-pattern-comparison-left-kind-gate-is-total"></a>
- [Pattern comparison left kind gate is total](sources/static-admission-and-class-probes.md#src-pattern-comparison-left-kind-gate-is-total)
<a id="src-custom-validity-operand-refuses-every-kind-with-one-class"></a>
- [The custom-validity operand gate names its admitted set: every refused kind draws one class, where the Boolean constant's target gate partitions four ways](sources/static-admission-and-class-probes.md#src-custom-validity-operand-refuses-every-kind-with-one-class)
<a id="src-temporal-declaration-without-a-format"></a>
- [A temporal field may declare no format, and the Kernel resolves the default from its declared kind](sources/static-admission-and-class-probes.md#src-temporal-declaration-without-a-format)
<a id="src-having-filter-comparison-and-scope-classes"></a>
- [The `Having` filter's refusal classes belong to the filter rather than the wrapping operator, and its numeric and String-literal comparison columns disagree on six kinds of eight](sources/static-admission-and-class-probes.md#src-having-filter-comparison-and-scope-classes)
<a id="src-constant-assignment-diagnostic-ladder"></a>
- [A wrong-kind constant assignment's diagnostic is an ordered ladder over the (constant, target) pair; the complete eighty-cell grid is what makes it legible](sources/static-admission-and-class-probes.md#src-constant-assignment-diagnostic-ladder)
<a id="src-boolean-constant-target-kind-partitions-into-four-classes"></a>
- [The Boolean constant computation's wrong-kind target draws four different classes, not one; first use of the `computation add --dry-run` route](sources/static-admission-and-class-probes.md#src-boolean-constant-target-kind-partitions-into-four-classes)
<a id="src-daterange-scalar-slot-rejects-every-nonscalar-form"></a>
- [`AtLeastOneDateRangeOverlaps` rejects every non-scalar form in its scalar slot with one class, and admits all five in its `In` slot](sources/static-admission-and-class-probes.md#src-daterange-scalar-slot-rejects-every-nonscalar-form)
<a id="src-later-position-class-is-total-and-presence-is-admitted"></a>
- [Later position class is total and presence is admitted](sources/static-admission-and-class-probes.md#src-later-position-class-is-total-and-presence-is-admitted)
<a id="src-later-position-kinds-and-group-expansion-class"></a>
- [A Boolean in a temporal extremum's later position draws `MVK_DATE_AND_NONDATE`; a mixed starred-group expansion draws `MVK_NOT_SORTABLE` instead](sources/static-admission-and-class-probes.md#src-later-position-kinds-and-group-expansion-class)
<a id="src-parser-static-legality-sweep"></a>
- [Ten condition-level refusal classes named in one generated sweep: the type/arity gates `MVK_NO_STRING_OR_NUMBER_FOR_ADD`, `MVK_INVALID_TYPE_FOR_TOLERANCE_OP`, `MVK_PARAMSIZE_INVALID1`, `MVK_NO_FIELDS_ALLOWED`, the category twins `MVK_CATEGORY_UNKOWN` and `MVK_NO_ENUMERATION`, the constant-pair gate `MVK_INVALID_COMPARE_TO_CONST`, and the filter star gate `MVK_WILDCARDS_REQUIRED`](sources/diagnostic-class-vocabulary-and-sweeps.md#src-parser-static-legality-sweep)

<a id="src-typedef-resolves-to-base-kind"></a>
- [A typedef field is its base kind at three independent gates, which makes `spec/01`'s model-expansion exclusion measured rather than assumed](sources/static-admission-and-class-probes.md#src-typedef-resolves-to-base-kind)
<a id="src-first-filled-reads-the-format-string"></a>
- [The four entity-list carriers split two-and-two on one field pair: the extrema and the distinct count read the component set, `FirstFilledValue` and `FieldValuesNotUnique` read the format string](sources/static-admission-and-class-probes.md#src-first-filled-reads-the-format-string)
<a id="src-equal-set-spelling-families-carrier-split"></a>
- [Equal set spelling families carrier split](sources/static-admission-and-class-probes.md#src-equal-set-spelling-families-carrier-split)
<a id="src-filtered-star-supplies-the-leading-kind"></a>
- [A `Having`-filtered star supplies the extremum's leading kind exactly as a plain star does, measured on the pairing](sources/static-admission-and-class-probes.md#src-filtered-star-supplies-the-leading-kind)
<a id="src-filtered-star-temporal-carriers-and-binding-depth"></a>
- [A `Having`-filtered star is admitted wherever a plain star is on all three temporal carriers, the component gate reads through it, and the binding relation re-derives independently](sources/static-admission-and-class-probes.md#src-filtered-star-temporal-carriers-and-binding-depth)
<a id="src-distinct-count-component-set-and-locus"></a>
- [`NumberOfDifferentValues` gates temporal operands by component set, not declared format; date-first class and group-presence locus confirmed locally](sources/static-admission-and-class-probes.md#src-distinct-count-component-set-and-locus)
<a id="src-distinct-count-operand-domain"></a>
- [`NumberOfDifferentValues` admits Custom as string-like, splits homogeneity into two codes, and counts expanded operands for arity](sources/static-admission-and-class-probes.md#src-distinct-count-operand-domain)

<a id="src-extensible-enumeration-has-no-dm-json-carrier"></a>
- [Extensible enumeration has no dm json carrier](sources/static-admission-and-class-probes.md#src-extensible-enumeration-has-no-dm-json-carrier)
<a id="src-validtype-operand-gates"></a>
- [Validtype operand gates](sources/static-admission-and-class-probes.md#src-validtype-operand-gates)
<a id="src-entity-list-sole-operand-arity"></a>
- [`FirstFilledValue`'s sole-operand rule is the disjunction its own Kernel message states — more than one field **or** at least one group — while the entity-valued value list admits a sole field on each side](sources/static-admission-and-class-probes.md#src-entity-list-sole-operand-arity)

<a id="src-notind-declaration-properties-are-mapping-provenance"></a>
- [The six `@NotInD` declaration properties never reach validation codegen or the runtime, the structural-mapping tool is their sole semantic consumer and overrides the format there, and the annotation's own no-effect Javadoc is falsified by its use on the decimal separator](sources/diagnostic-class-vocabulary-and-sweeps.md#src-notind-declaration-properties-are-mapping-provenance)

<a id="src-aggregate-operand-list-takes-paths-only"></a>
- [Aggregate operand list takes paths only](sources/computation-placement-and-constant-probes.md#src-aggregate-operand-list-takes-paths-only)

<a id="src-number-operation-typing"></a>
- [Number operation typing](sources/computation-placement-and-constant-probes.md#src-number-operation-typing)

<a id="src-number-operation-node-gates"></a>
- [Number operation node gates](sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates)

<a id="src-number-operation-division-walk"></a>
- [Number operation division walk](sources/computation-placement-and-constant-probes.md#src-number-operation-division-walk)

<a id="src-power-derived-scale-and-operand-shapes"></a>
- [`^` restricts neither operand's shape; a non-literal exponent derives unknown scale, and that is what a computed target refuses](sources/computation-placement-and-constant-probes.md#src-power-derived-scale-and-operand-shapes)

<a id="src-computed-temporal-target-reads-the-format-not-the-kind"></a>
- [A computed temporal target is gated by its declared format string and not by its declared kind, on all three of the Time, Date, and DateTime families](sources/computation-placement-and-constant-probes.md#src-computed-temporal-target-reads-the-format-not-the-kind)
<a id="src-temporal-value-family-is-the-formats-not-the-kinds"></a>
- [A temporal field's value family is its declared format's, not its declared kind's](sources/computation-placement-and-constant-probes.md#src-temporal-value-family-is-the-formats-not-the-kinds)
<a id="src-cross-kind-temporal-reads"></a>
- [Cross-kind temporal comparison and extraction follow the format](sources/temporal-runtime-fold-probes.md#src-cross-kind-temporal-reads)
<a id="src-cross-kind-computation-reads"></a>
- [A computation reads a cross-kind temporal field by its format's family too, extracting, constructing a Date and selecting an indexed DateRange endpoint, measured locally 2026-10-02](sources/temporal-runtime-fold-probes.md#src-cross-kind-computation-reads)
<a id="src-temporal-operand-family-is-the-formats-not-the-kinds"></a>
- [A temporal operand's admitted family is its declared format's too, extractors and completed-period differences alike, with a Base Year completing the year the format omits](sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds)
<a id="src-temporal-difference-gates-read-the-format"></a>
- [Every temporal operand gate reads the declared format and never the declared kind — difference families, both DateTime extractors, the full-Date copy, and both `Date(...)` constructor source forms — removing nine under-admitting kind conjuncts](sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)
<a id="src-difference-gate-base-year-conditioning"></a>
- [A declared Base Year supplies the year position at `DifferenceInYears` too, and removing that gate moves which refusal class answers a clock operand](sources/computation-placement-and-constant-probes.md#src-difference-gate-base-year-conditioning)
<a id="src-yearless-day-bound-reads-the-base-year"></a>
- [A yearless stored day is bounded by its month's length in the declared Base Year](sources/temporal-constant-and-base-year-probes.md#src-yearless-day-bound-reads-the-base-year)
<a id="src-datetime-carrier-stores-by-its-format"></a>
- [The DATETIME carrier's cross-kind store is governed by its format too, inbound from a12-dmkits](sources/computation-placement-and-constant-probes.md#src-datetime-carrier-stores-by-its-format)
<a id="src-computed-target-gate-is-carrier-invariant"></a>
- [Neither the computed target's admission nor its store can read which carrier produced the value — a computation is a comparison condition, and one render locus erases the carrier — retiring four declared-kind narrowings without a per-family measurement](sources/computation-placement-and-constant-probes.md#src-computed-target-gate-is-carrier-invariant)
<a id="src-daterange-endpoint-reads-the-format"></a>
- [A `DateRange` construction endpoint is admitted by its declared format alone, with all three declared kinds on both sides of both outcomes](sources/computation-placement-and-constant-probes.md#src-daterange-endpoint-reads-the-format)
<a id="src-computed-value-is-not-retained-past-its-store"></a>
- [A computed value keeps no typed form past its store — all five store overloads render to text, so a computed DATE_TIME cell retains no instant and is indistinguishable from an authored one](sources/computation-placement-and-constant-probes.md#src-computed-value-is-not-retained-past-its-store)

<a id="src-two-positions-share-the-root-gate"></a>
- [Two positions share the root gate](sources/message-and-pointer-probes.md#src-two-positions-share-the-root-gate)
<a id="src-message-name-position-refusals"></a>
- [Message name position refusals](sources/message-and-pointer-probes.md#src-message-name-position-refusals)
<a id="src-message-name-position-carriers"></a>
- [Message name position carriers](sources/message-and-pointer-probes.md#src-message-name-position-carriers)
<a id="src-message-parameter-decoder"></a>
- [A rule message's parameter is parsed on its own and refused at its parser's first event: the name position's decision reads the whole entity first](sources/message-and-pointer-probes.md#src-message-parameter-decoder)

<a id="src-presence-confirm-custom-carriers"></a>
- [Presence confirm custom carriers](sources/having-filter-probes.md#src-presence-confirm-custom-carriers)
<a id="src-nested-self-exclusion"></a>
- [Nested self exclusion](sources/having-filter-probes.md#src-nested-self-exclusion)
<a id="src-three-level-filter-nesting"></a>
- [Three level filter nesting](sources/having-filter-probes.md#src-three-level-filter-nesting)
<a id="src-correlated-filter-string-computed-target"></a>
- [Correlated filter string computed target](sources/having-filter-probes.md#src-correlated-filter-string-computed-target)
<a id="src-currentrepetition-host-iteration"></a>
- [Currentrepetition host iteration](sources/having-filter-probes.md#src-currentrepetition-host-iteration)
<a id="src-self-exclusion-and-nested-filter-runtime"></a>
- [`CurrentRepetition` self-exclusion is an exact complement pair, `$` binds a per-row computed target, and a nested `Or` selects its own rows](sources/having-filter-probes.md#src-self-exclusion-and-nested-filter-runtime)
<a id="src-presence-leaf-operand-kinds"></a>
- [Presence leaf operand kinds](sources/having-filter-probes.md#src-presence-leaf-operand-kinds)
<a id="src-bare-outer-reference-redundant-marker"></a>
- [Bare outer reference redundant marker](sources/having-filter-probes.md#src-bare-outer-reference-redundant-marker)
<a id="src-correlated-filter-runtime"></a>
- [Correlated filter runtime](sources/having-filter-probes.md#src-correlated-filter-runtime)
<a id="src-pattern-invalid-string-cell"></a>
- [String formal-invalid input](sources/evaluation-and-application-routes.md#src-pattern-invalid-string-cell)
<a id="src-filter-condition-carrier-independence"></a>
- [Filter carrier independence](sources/having-filter-probes.md#src-filter-condition-carrier-independence)
<a id="src-nested-correlated-filter-and-poison-scope"></a>
- [Nested correlation and poison scope](sources/having-filter-probes.md#src-nested-correlated-filter-and-poison-scope)
<a id="src-outer-origin-filter-leaves"></a>
- [Outer origin filter leaves](sources/having-filter-probes.md#src-outer-origin-filter-leaves)

<a id="src-starred-operand-message-polarity"></a>
- [Starred operand message polarity](sources/group-and-iteration-probes.md#src-starred-operand-message-polarity)
<a id="src-filled-field-count-nested-capacity"></a>
- [Filled field count nested capacity](sources/group-list-and-capacity-probes.md#src-filled-field-count-nested-capacity)
<a id="src-filled-field-count-deep-capacity"></a>
- [Filled field count deep capacity](sources/group-list-and-capacity-probes.md#src-filled-field-count-deep-capacity)
<a id="src-filtered-field-fill-ranges"></a>
- [Filtered field-fill selected ranges and deciding polarity](sources/group-list-and-capacity-probes.md#src-filtered-field-fill-ranges)

<a id="src-group-field-fill-declared-slots"></a>
- [Group field fill declared slots](sources/group-list-and-capacity-probes.md#src-group-field-fill-declared-slots)
<a id="src-computation-star-binding-gate"></a>
- [A repeatable level a star leaves unstarred must be bound: below the first star it draws the missing-star class on every carrier measured, and above it a fixed-target computation's class follows where its target lies](sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)
<a id="src-validation-below-star-placement"></a>
- [Validation below star placement](sources/group-list-and-capacity-probes.md#src-validation-below-star-placement)
<a id="src-validation-below-star-placement-kinds"></a>
- [Validation below star placement kinds](sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)
<a id="src-walk-batch-reading-scope"></a>
- [Walk batch reading scope](sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)
<a id="src-ancestor-starred-group-count-computation"></a>
- [`NumberOfFilledGroups` counts a fixed group below a star on the computation arm by content per in-capacity instance, and a computation reading a malformed-only operand group emits no implicit message](sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation)
<a id="src-below-star-group-computation"></a>
- [Below star group computation](sources/group-list-and-capacity-probes.md#src-below-star-group-computation)
<a id="src-below-star-group-runtime"></a>
- [Below star group runtime](sources/group-list-and-capacity-probes.md#src-below-star-group-runtime)
<a id="src-group-count-list-extent"></a>
- [Group count list extent](sources/group-list-and-capacity-probes.md#src-group-count-list-extent)

<a id="src-group-count-unavailability"></a>
- [Group count unavailability](sources/group-list-and-capacity-probes.md#src-group-count-unavailability)

<a id="src-group-count-static-gates-both-arms"></a>
- [Group count static gates both arms](sources/group-list-and-capacity-probes.md#src-group-count-static-gates-both-arms)
<a id="src-group-count-gates-repeatable-scope"></a>
- [Group count gates repeatable scope](sources/group-list-and-capacity-probes.md#src-group-count-gates-repeatable-scope)
<a id="src-fixed-group-repeatable-ancestor-carriers"></a>
- [Fixed group repeatable ancestor carriers](sources/group-list-and-capacity-probes.md#src-fixed-group-repeatable-ancestor-carriers)

<a id="src-repeatability-declaration-domain"></a>
- [A repeatable group always carries a finite maximum, and absence means nonrepeatable](sources/group-list-and-capacity-probes.md#src-repeatability-declaration-domain)
<a id="src-group-declaration-admission-peer-measurement"></a>
- [The repeatability ceiling depends on the declaring carrier, and `Id` is the one reserved whole name](sources/inbound-group-operand-batches.md#src-group-declaration-admission-peer-measurement)
<a id="src-repeatability-domain-peer-measurement"></a>
- [The `repeatability` domain is `> 0` and `1` is admitted, measured by a12-dmkits](sources/inbound-group-operand-batches.md#src-repeatability-domain-peer-measurement)
<a id="src-erroneous-member-quantifier-undecidable"></a>
- [An erroneous member makes the quantifier undecidable rather than shrinking its list](sources/inbound-group-operand-batches.md#src-erroneous-member-quantifier-undecidable)
<a id="src-mandatory-information-narrowing"></a>
- [Mandatory-information derivation reads a 32-bit-narrowed threshold](sources/rule-set-meta-information.md#src-mandatory-information-narrowing)
<a id="src-mandatory-information-presence-matrix"></a>
- [Mandatory-information derivation separates field, root-only, and ignored rule shapes](sources/rule-set-meta-information.md#src-mandatory-information-presence-matrix)
<a id="src-mandatory-information-repeatable-presence"></a>
- [Mandatory information repeatable presence](sources/rule-set-meta-information.md#src-mandatory-information-repeatable-presence)
<a id="src-mandatory-information-composition-matrix"></a>
- [Mandatory-information derivation distinguishes root-relative fields and finite dependency closure](sources/rule-set-meta-information.md#src-mandatory-information-composition-matrix)
<a id="src-mandatory-information-boolean-formulas"></a>
- [Mandatory information boolean formulas](sources/rule-set-meta-information.md#src-mandatory-information-boolean-formulas)
<a id="src-mandatory-information-boolean-formula-positions"></a>
- [Mandatory information boolean formula positions](sources/rule-set-meta-information.md#src-mandatory-information-boolean-formula-positions)
<a id="src-mandatory-information-field-cycles"></a>
- [Mandatory information field cycles](sources/rule-set-meta-information.md#src-mandatory-information-field-cycles)
<a id="src-mandatory-information-field-list-cycles"></a>
- [Mandatory information field list cycles](sources/rule-set-meta-information.md#src-mandatory-information-field-list-cycles)
<a id="src-mandatory-information-longer-cycles"></a>
- [Mandatory information longer cycles](sources/rule-set-meta-information.md#src-mandatory-information-longer-cycles)
<a id="src-mandatory-information-field-list-guards"></a>
- [Mandatory information field list guards](sources/rule-set-meta-information.md#src-mandatory-information-field-list-guards)
<a id="src-mandatory-information-distinct-count"></a>
- [Mandatory information distinct count](sources/rule-set-meta-information.md#src-mandatory-information-distinct-count)
<a id="src-mandatory-information-info-severity"></a>
- [Mandatory information info severity](sources/rule-set-meta-information.md#src-mandatory-information-info-severity)
<a id="src-mandatory-information-reversed-strict-count"></a>
- [Mandatory information reversed strict count](sources/rule-set-meta-information.md#src-mandatory-information-reversed-strict-count)
<a id="src-mandatory-information-false-count-guards"></a>
- [Mandatory information false count guards](sources/rule-set-meta-information.md#src-mandatory-information-false-count-guards)
<a id="src-mandatory-information-count-seed-cardinality"></a>
- [Mandatory information count seed cardinality](sources/rule-set-meta-information.md#src-mandatory-information-count-seed-cardinality)
<a id="src-mandatory-information-count-dependencies"></a>
- [Mandatory information count dependencies](sources/rule-set-meta-information.md#src-mandatory-information-count-dependencies)
<a id="src-mandatory-information-count-chain"></a>
- [Mandatory information count chain](sources/rule-set-meta-information.md#src-mandatory-information-count-chain)
<a id="src-mandatory-information-count-chain-orders"></a>
- [Mandatory information count chain orders](sources/rule-set-meta-information.md#src-mandatory-information-count-chain-orders)
<a id="src-mandatory-information-count-target-only"></a>
- [Mandatory information count target only](sources/rule-set-meta-information.md#src-mandatory-information-count-target-only)
<a id="src-mandatory-information-distinct-target-only"></a>
- [Mandatory information distinct target only](sources/rule-set-meta-information.md#src-mandatory-information-distinct-target-only)
<a id="src-mandatory-information-distinct-comparisons"></a>
- [Mandatory information distinct comparisons](sources/rule-set-meta-information.md#src-mandatory-information-distinct-comparisons)
<a id="src-mandatory-information-declared-required"></a>
- [Mandatory information declared required](sources/rule-set-meta-information.md#src-mandatory-information-declared-required)
<a id="src-mandatory-information-declaration-closure"></a>
- [Mandatory information declaration closure](sources/rule-set-meta-information.md#src-mandatory-information-declaration-closure)
<a id="src-mandatory-information-semantic-index"></a>
- [Mandatory information semantic index](sources/rule-set-meta-information.md#src-mandatory-information-semantic-index)
<a id="src-mandatory-information-parallel-iteration"></a>
- [Mandatory information parallel iteration](sources/rule-set-meta-information.md#src-mandatory-information-parallel-iteration)
<a id="src-mandatory-information-cross-root"></a>
- [Mandatory information cross root](sources/rule-set-meta-information.md#src-mandatory-information-cross-root)
<a id="src-mandatory-information-generated-index"></a>
- [Mandatory information generated index](sources/rule-set-meta-information.md#src-mandatory-information-generated-index)
<a id="src-mandatory-information-generated-computation-validation"></a>
- [Mandatory information generated computation validation](sources/rule-set-meta-information.md#src-mandatory-information-generated-computation-validation)
<a id="src-dynamic-enumeration-legality"></a>
- [Dynamic-enumeration derivation refuses in four ordered stages, eleven of twelve classes attributed to one witness rule each](sources/rule-set-meta-information.md#src-dynamic-enumeration-legality)

<a id="src-index-and-sort-field-declaration"></a>
- [Index and sort field declaration](sources/model-structure-and-declaration-probes.md#src-index-and-sort-field-declaration)

<a id="src-temporal-constructor-operand-positions"></a>
- [A temporal constructor checks each operand position separately, and two classes distinguish a misplaced extractor from an inadmissible one](sources/static-admission-and-class-probes.md#src-temporal-constructor-operand-positions)

<a id="src-form-condition-constructs"></a>
- [Form condition constructs](sources/diagnostic-class-vocabulary-and-sweeps.md#src-form-condition-constructs)

<a id="src-generated-rule-identity"></a>
- [Generated rule identity](sources/model-structure-and-declaration-probes.md#src-generated-rule-identity)

<a id="src-entity-container-integrity"></a>
- [Entity container integrity](sources/model-structure-and-declaration-probes.md#src-entity-container-integrity)
<a id="src-error-target-declaration"></a>
- [Error target declaration](sources/model-structure-and-declaration-probes.md#src-error-target-declaration)
<a id="src-index-group-resolution"></a>
- [Index group resolution](sources/model-structure-and-declaration-probes.md#src-index-group-resolution)
<a id="src-rule-change-propagation"></a>
- [Rule change propagation](sources/model-structure-and-declaration-probes.md#src-rule-change-propagation)
<a id="src-repeatability-restriction"></a>
- [Repeatability restriction](sources/model-structure-and-declaration-probes.md#src-repeatability-restriction)
<a id="src-error-text-row-parameter"></a>
- [Error text row parameter](sources/model-structure-and-declaration-probes.md#src-error-text-row-parameter)
<a id="src-enumeration-category-constant"></a>
- [Enumeration category constant](sources/static-admission-and-class-probes.md#src-enumeration-category-constant)
<a id="src-computation-normal-form-generation"></a>
- [Computation normal form generation](sources/diagnostic-class-vocabulary-and-sweeps.md#src-computation-normal-form-generation)
<a id="src-table-enumeration-inertness"></a>
- [Table enumeration inertness](sources/diagnostic-class-vocabulary-and-sweeps.md#src-table-enumeration-inertness)
<a id="src-iteration-and-semantic-index-legality"></a>
- [Iteration and semantic index legality](sources/diagnostic-class-vocabulary-and-sweeps.md#src-iteration-and-semantic-index-legality)

<a id="src-over-limit-computation-target"></a>
- [Over limit computation target](sources/group-list-and-capacity-probes.md#src-over-limit-computation-target)
<a id="src-boolean-first-filled-false-is-filled"></a>
- [`FirstFilledValue` selects a Boolean `false` because its filled predicate is presence, and an all-empty selection mints no outcome](sources/evaluation-and-application-routes.md#src-boolean-first-filled-false-is-filled)
<a id="src-first-filled-malformed-terminates-and-inventory-reports"></a>
- [A malformed `FirstFilledValue` source terminates the scan where an empty one falls through, and the eager operand inventory still reports the suffix the scan never read](sources/evaluation-and-application-routes.md#src-first-filled-malformed-terminates-and-inventory-reports)
<a id="src-mixed-chain-string-target-rejection"></a>
- [Mixed chain string target rejection](sources/evaluation-and-application-routes.md#src-mixed-chain-string-target-rejection)

<a id="src-negation-pair-grid"></a>
- [Negation pair grid](sources/evaluation-and-application-routes.md#src-negation-pair-grid)
<a id="src-negated-corpus"></a>
- [Negated corpus](sources/evaluation-and-application-routes.md#src-negated-corpus)
<a id="src-peer-corpus-replay"></a>
- [Peer corpus replay](sources/evaluation-and-application-routes.md#src-peer-corpus-replay)
<a id="src-negation-pair-supplement"></a>
- [`Valid`/`Invalid` complement only over a `Date(...)` construction, and German spellings fire as English ones](sources/evaluation-and-application-routes.md#src-negation-pair-supplement)
<a id="src-field-fill-mixed-list"></a>
- [Field-fill lists mixing direct fields, fixed groups and a starred field read each operand by its own source](sources/evaluation-and-application-routes.md#src-field-fill-mixed-list)

<a id="src-firstfilled-string-boolean-runtime"></a>
- [Firstfilled string boolean runtime](sources/evaluation-and-application-routes.md#src-firstfilled-string-boolean-runtime)

<a id="src-selected-typed-first-filled"></a>
- [Selected first-filled](sources/evaluation-and-application-routes.md#src-selected-typed-first-filled)

<a id="src-first-filled-formal-branch-four-carriers"></a>
- [First-filled formal failure across six carriers](sources/evaluation-and-application-routes.md#src-first-filled-formal-branch-four-carriers)
<a id="src-number-formal-cascade-code-axis-and-load-canonicalisation"></a>
- [Number formal cascade code axis and load canonicalisation](sources/evaluation-and-application-routes.md#src-number-formal-cascade-code-axis-and-load-canonicalisation)
<a id="src-index-iteration-and-constant-refusal-classes"></a>
- [Index iteration and constant refusal classes](sources/diagnostic-class-vocabulary-and-sweeps.md#src-index-iteration-and-constant-refusal-classes)
<a id="src-codegen-classes-reach-ordinary-authoring"></a>
- [The Kernel code-generation check family is reachable from ordinary authoring, because the consistency check runs the generator](sources/diagnostic-class-vocabulary-and-sweeps.md#src-codegen-classes-reach-ordinary-authoring)
<a id="src-unraised-diagnostic-vocabulary"></a>
- [Unraised diagnostic vocabulary](sources/diagnostic-class-vocabulary-and-sweeps.md#src-unraised-diagnostic-vocabulary)
<a id="src-default-locale-message-bundles"></a>
- [Default locale message bundles](sources/diagnostic-class-vocabulary-and-sweeps.md#src-default-locale-message-bundles)
<a id="src-shipped-custom-field-type-vocabulary"></a>
- [Shipped custom field type vocabulary](sources/diagnostic-class-vocabulary-and-sweeps.md#src-shipped-custom-field-type-vocabulary)
<a id="src-universal-value-formal-precheck"></a>
- [Universal value formal precheck](sources/static-admission-and-class-probes.md#src-universal-value-formal-precheck)
<a id="src-unraised-diagnostic-runtime-corroboration"></a>
- [Unraised diagnostic runtime corroboration](sources/diagnostic-class-vocabulary-and-sweeps.md#src-unraised-diagnostic-runtime-corroboration)
<a id="src-date-range-list-iso-arity-and-fragment-suffix"></a>
- [Date range list iso arity and fragment suffix](sources/temporal-runtime-fold-probes.md#src-date-range-list-iso-arity-and-fragment-suffix)
<a id="src-yearless-extrema-base-year-ordering"></a>
- [The extrema order a yearless list under a declared Base Year on both strategies, and no document on such a model can say what they order on](sources/temporal-runtime-fold-probes.md#src-yearless-extrema-base-year-ordering)
<a id="src-extrema-component-omitting-fold"></a>
- [Extrema component omitting fold](sources/temporal-runtime-fold-probes.md#src-extrema-component-omitting-fold)
<a id="src-cross-kind-format-runtime-parser"></a>
- [The runtime text parser is the declared format's, not the declared kind's](sources/temporal-runtime-fold-probes.md#src-cross-kind-format-runtime-parser)
<a id="src-distinct-count-group-expansion-fold"></a>
- [Distinct count group expansion fold](sources/temporal-runtime-fold-probes.md#src-distinct-count-group-expansion-fold)
<a id="src-distinct-count-time-bearing-fold"></a>
- [Distinct count time bearing fold](sources/temporal-runtime-fold-probes.md#src-distinct-count-time-bearing-fold)
<a id="src-distinct-count-component-omitting-fold"></a>
- [Distinct count component omitting fold](sources/temporal-runtime-fold-probes.md#src-distinct-count-component-omitting-fold)
<a id="src-distinct-count-temporal-identity-both-strategies"></a>
- [Distinct temporal identity, both strategies](sources/temporal-runtime-fold-probes.md#src-distinct-count-temporal-identity-both-strategies)
<a id="src-having-numeric-expression-runtime"></a>
- [Numeric filters and captured repetition](sources/having-filter-probes.md#src-having-numeric-expression-runtime)

<a id="src-having-number-leaf-grid"></a>
- [Number/literal filters: all operators and operand orders, scale gates only on equality](sources/having-filter-probes.md#src-having-number-leaf-grid)
<a id="src-filter-reference-two-levels-above"></a>
- [Filter gates use path membership; the referenced level determines the admitted constant](sources/having-filter-probes.md#src-filter-reference-two-levels-above)
<a id="src-filter-reference-level-runtime"></a>
- [Non-reopened filter references are constant per host row or document](sources/having-filter-probes.md#src-filter-reference-level-runtime)
<a id="src-repeatable-computation-row-extent"></a>
- [Repeatable computation row extent](sources/group-list-and-capacity-probes.md#src-repeatable-computation-row-extent)
<a id="src-distinct-count-first-operand-class"></a>
- [`NumberOfDifferentValues` classifies by its first operand](sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)
<a id="src-extrema-operand-family-is-positional"></a>
- [`MinValue`/`MaxValue` pick their operand family from the first operand, and the two families draw different codes](sources/group-list-and-capacity-probes.md#src-extrema-operand-family-is-positional)
<a id="src-capacity-consumer-sweep"></a>
- [Capacity consumer sweep](sources/group-list-and-capacity-probes.md#src-capacity-consumer-sweep)
<a id="src-validation-capacity-consumers"></a>
- [Validation operand capacity](sources/group-list-and-capacity-probes.md#src-validation-capacity-consumers)
<a id="src-group-capacity-consumers"></a>
- [Group operand capacity](sources/group-list-and-capacity-probes.md#src-group-capacity-consumers)
<a id="src-over-limit-finding-text"></a>
- [`zuGrosseZeile` renders no coordinate, and two over-limit groups report independently](sources/over-repetition-probes.md#src-over-limit-finding-text)
<a id="src-starred-group-count-computation"></a>
- [Starred group count computation](sources/group-and-iteration-probes.md#src-starred-group-count-computation)
<a id="src-partial-coverage-group-operands"></a>
- [Partial coverage group operands](sources/group-list-and-capacity-probes.md#src-partial-coverage-group-operands)
<a id="src-group-count-empty-gate"></a>
- [Group count empty gate](sources/group-list-and-capacity-probes.md#src-group-count-empty-gate)
<a id="src-rule-bucket-empty-gate"></a>
- [Rule bucket empty gate](sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate)
<a id="src-empty-gate-count-beneath-and"></a>
- [A small-side count lifts the content gate from beneath `And` too, 2026-10-02](sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and)
<a id="src-starred-group-quantifier-capacity"></a>
- [The threshold quantifiers read the in-capacity extent, and an instantiated row is filled](sources/group-list-and-capacity-probes.md#src-starred-group-quantifier-capacity)
<a id="src-count-placement-overlap-list-grid"></a>
- [A lone repeatable group counted from a rule whose error field lies in it and in the rule's group draws the count's arity class, the overlap `In` list is an entity list of its own, and a field message's non-ASCII token is a wrong name](sources/group-list-and-capacity-probes.md#src-count-placement-overlap-list-grid)
<a id="src-count-placement-by-error-field"></a>
- [The sole count's placement class is decided by the error field's region](sources/group-list-and-capacity-probes.md#src-count-placement-by-error-field)
<a id="src-overlap-field-walk-order"></a>
- [Both DateRange overlap operators ask their list gates, then a kind and year-interpretation field walk, before the year agreement](sources/group-list-and-capacity-probes.md#src-overlap-field-walk-order)
<a id="src-address-dialect-selector"></a>
- [An unbound repeatable level is what selects a message pointer's slash spelling](sources/message-and-pointer-probes.md#src-address-dialect-selector)
<a id="src-repeatable-descendant-group-count"></a>
- [Repeatable descendant group count](sources/group-and-iteration-probes.md#src-repeatable-descendant-group-count)
<a id="src-deep-repeatable-descendant-group-count"></a>
- [Deep repeatable descendant group count](sources/group-and-iteration-probes.md#src-deep-repeatable-descendant-group-count)
<a id="src-nested-star-bound-outer-level"></a>
- [Nested star bound outer level](sources/group-and-iteration-probes.md#src-nested-star-bound-outer-level)
<a id="src-group-operand-over-limit-extent"></a>
- [Group operand over limit extent](sources/group-and-iteration-probes.md#src-group-operand-over-limit-extent)
<a id="src-group-count-row-domains"></a>
- [The half-instantiated shell, the starred group over a repeatable descendant, and the unreachable row-domain discriminator](sources/group-and-iteration-probes.md#src-group-count-row-domains)
<a id="src-over-limit-finding-multiplicity"></a>
- [An over-limit row stamps every node the document writes beneath it](sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)
<a id="src-nested-over-limit-attribution"></a>
- [An inner over-limit row is invisible beneath an outer one](sources/over-repetition-probes.md#src-nested-over-limit-attribution)
<a id="src-over-limit-absorption-depth"></a>
- [The absorption is transitive and suppresses the whole written subtree](sources/over-repetition-probes.md#src-over-limit-absorption-depth)

<a id="src-address-index-position-classes"></a>
- [The over-limit class follows the coordinate's position, and a repeatable root group draws the serial class throughout](sources/over-repetition-probes.md#src-address-index-position-classes)
<a id="src-nested-descendant-group-count-invalid"></a>
- [Nested descendant group count invalid](sources/group-and-iteration-probes.md#src-nested-descendant-group-count-invalid)
<a id="src-nested-descendant-group-count-runtime"></a>
- [Nested descendant group count runtime](sources/group-and-iteration-probes.md#src-nested-descendant-group-count-runtime)
<a id="src-nested-descendant-group-count-admission"></a>
- [Nested descendant group count admission](sources/group-and-iteration-probes.md#src-nested-descendant-group-count-admission)
<a id="src-empty-declared-group"></a>
- [Empty declared group](sources/group-and-iteration-probes.md#src-empty-declared-group)
<a id="src-short-name-flag-gates-the-model-wide-tier"></a>
- [Short name flag gates the model wide tier](sources/group-and-iteration-probes.md#src-short-name-flag-gates-the-model-wide-tier)
<a id="src-multi-root-short-name-reach"></a>
- [Multi root short name reach](sources/group-and-iteration-probes.md#src-multi-root-short-name-reach)
<a id="src-message-group-parameter"></a>
- [Message group parameter](sources/message-and-pointer-probes.md#src-message-group-parameter)
<a id="src-message-group-availability"></a>
- [Message group availability](sources/message-and-pointer-probes.md#src-message-group-availability)
<a id="src-message-group-argument-layers"></a>
- [A group argument is refused in layers, a lexer or separator fault before the lookup with its field short-name fallback, then a token left after the path](sources/message-and-pointer-probes.md#src-message-group-argument-layers)
<a id="src-message-group-argument-events"></a>
- [A group argument's classes follow its parser's events, and a keyword that is also a name is decided by the token after it](sources/message-and-pointer-probes.md#src-message-group-argument-events)
<a id="src-message-group-walk-and-dotted-names"></a>
- [Message group walk and dotted names](sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)
<a id="src-german-condition-language-terminals"></a>
- [German condition language terminals](sources/message-and-pointer-probes.md#src-german-condition-language-terminals)

<a id="src-message-group-parameter-rendered-index"></a>
- [Message group parameter rendered index](sources/message-and-pointer-probes.md#src-message-group-parameter-rendered-index)

<a id="src-message-group-parameter-resolution"></a>
- [Message group parameter resolution](sources/message-and-pointer-probes.md#src-message-group-parameter-resolution)
<a id="src-dmtool-2026-08-22-instrument-handback"></a>
- [Dmtool 2026 08 22 instrument handback](sources/temporal-and-message-probes.md#src-dmtool-2026-08-22-instrument-handback)
<a id="src-2026-08-23-reconciliation"></a>
- [2026 08 23 reconciliation](sources/temporal-and-message-probes.md#src-2026-08-23-reconciliation)
<a id="src-date-range-2026-08-19-reconciliation"></a>
- [Date range 2026 08 19 reconciliation](sources/temporal-and-message-probes.md#src-date-range-2026-08-19-reconciliation)

### Group and iteration source checkpoints

Three shards carry these: locally measured probes split between [`group-and-iteration-probes.md`](sources/group-and-iteration-probes.md) and [`group-list-and-capacity-probes.md`](sources/group-list-and-capacity-probes.md), plus reconciled inbound batches in [`inbound-group-operand-batches.md`](sources/inbound-group-operand-batches.md). Each entry below links to the shard that owns it.

<a id="inbound-entity-list-group-operand-validator-cardinality-and-cleared-value-batch"></a>
- [Inbound entity-list group-operand, validator-cardinality, and cleared-value batch](sources/inbound-group-operand-batches.md#inbound-entity-list-group-operand-validator-cardinality-and-cleared-value-batch)
<a id="src-first-filled-additional-kind-computations"></a>
- [First filled additional kind computations](sources/group-and-iteration-probes.md#src-first-filled-additional-kind-computations)
<a id="src-first-filled-kind-computations"></a>
- [First filled kind computations](sources/group-and-iteration-probes.md#src-first-filled-kind-computations)
<a id="src-current-repetition-root-condition"></a>
- [Current repetition root condition](sources/group-and-iteration-probes.md#src-current-repetition-root-condition)
<a id="src-current-repetition-repeatable-condition"></a>
- [Current repetition repeatable condition](sources/group-and-iteration-probes.md#src-current-repetition-repeatable-condition)
<a id="src-current-repetition-computation-dependency"></a>
- [Current repetition computation dependency](sources/group-and-iteration-probes.md#src-current-repetition-computation-dependency)
<a id="src-group-list-rnu-admission-correction"></a>
- [Group list rnu admission correction](sources/group-list-and-capacity-probes.md#src-group-list-rnu-admission-correction)
<a id="src-entity-list-group-gates"></a>
- [Entity-list group gates](sources/inbound-group-operand-batches.md#src-entity-list-group-gates)
<a id="src-field-values-not-unique-group-admission"></a>
- [Field-values-not-unique group admission](sources/inbound-group-operand-batches.md#src-field-values-not-unique-group-admission)
<a id="src-field-values-not-unique-group-runtime"></a>
- [Field-values-not-unique group runtime](sources/inbound-group-operand-batches.md#src-field-values-not-unique-group-runtime)
<a id="src-number-group-computation-runtime"></a>
- [Number group computation runtime](sources/inbound-group-operand-batches.md#src-number-group-computation-runtime)
<a id="src-number-group-value-count-computation-capacity"></a>
- [Number group value-count computation capacity](sources/inbound-group-operand-batches.md#src-number-group-value-count-computation-capacity)
<a id="src-token-group-partial-runtime"></a>
- [Token group partial runtime](sources/inbound-group-operand-batches.md#src-token-group-partial-runtime)
<a id="src-token-group-value-count-computation-capacity"></a>
- [Token group value-count computation capacity](sources/inbound-group-operand-batches.md#src-token-group-value-count-computation-capacity)
<a id="src-boolean-group-value-count-computation-capacity"></a>
- [Boolean group value count computation capacity](sources/inbound-group-operand-batches.md#src-boolean-group-value-count-computation-capacity)
<a id="src-false-boolean-group-value-count-computation-capacity"></a>
- [False Boolean-group value-count computation capacity](sources/inbound-group-operand-batches.md#src-false-boolean-group-value-count-computation-capacity)
<a id="src-boolean-group-value-count-computation-shape-matrix"></a>
- [Boolean-group value-count computation shape matrix](sources/inbound-group-operand-batches.md#src-boolean-group-value-count-computation-shape-matrix)
<a id="src-boolean-fixed-group-value-count-computation"></a>
- [Boolean fixed-group value-count computation](sources/inbound-group-operand-batches.md#src-boolean-fixed-group-value-count-computation)
<a id="src-boolean-confirm-constant-computation-targets"></a>
- [Boolean confirm constant computation targets](sources/inbound-group-operand-batches.md#src-boolean-confirm-constant-computation-targets)
<a id="src-token-value-count-group-runtime"></a>
- [Token group value-count runtime](sources/inbound-group-operand-batches.md#src-token-value-count-group-runtime)
<a id="src-token-value-count-fixed-group-admission"></a>
- [Token fixed-group value-count admission](sources/inbound-group-operand-batches.md#src-token-value-count-fixed-group-admission)
<a id="src-filled-field-group-runtime"></a>
- [Filled field group runtime](sources/inbound-group-operand-batches.md#src-filled-field-group-runtime)
<a id="src-group-operand-capacity-consumer-sweep"></a>
- [Fixed-group capacity: six carriers](sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep)
<a id="src-starred-group-operand-extent"></a>
- [Starred groups: extent and malformed cells](sources/group-and-iteration-probes.md#src-starred-group-operand-extent)
<a id="src-starred-field-operand-extent"></a>
- [Starred fields: extrema and count extents](sources/group-and-iteration-probes.md#src-starred-field-operand-extent)
<a id="src-token-starred-field-capacity"></a>
- [String starred-count capacity](sources/group-and-iteration-probes.md#src-token-starred-field-capacity)
<a id="src-boolean-starred-field-capacity"></a>
- [Boolean starred-count capacity](sources/group-and-iteration-probes.md#src-boolean-starred-field-capacity)
<a id="src-boolean-value-count-partial-loop"></a>
- [Boolean/Confirm partial counts](sources/group-and-iteration-probes.md#src-boolean-value-count-partial-loop)
<a id="src-confirm-starred-field-capacity"></a>
- [Confirm starred-count capacity and movement](sources/group-and-iteration-probes.md#src-confirm-starred-field-capacity)
<a id="src-filtered-starred-field-capacity"></a>
- [Filtered token/Boolean/Confirm count capacity](sources/group-and-iteration-probes.md#src-filtered-starred-field-capacity)
<a id="src-capacity-projection-computation-arm"></a>
- [Computation capacity projection](sources/group-and-iteration-probes.md#src-capacity-projection-computation-arm)
<a id="src-filtered-star-capacity-both-arms"></a>
- [Filtered star capacity both arms](sources/group-and-iteration-probes.md#src-filtered-star-capacity-both-arms)
<a id="src-starred-field-operand-peer-reproduction"></a>
- [Starred field operand, empty-domain zero, and the operand-scoped over-repetition channel, reproduced by a12-dmkits](sources/inbound-group-operand-batches.md#src-starred-field-operand-peer-reproduction)
<a id="src-star-over-repetition-domain"></a>
- [Star over repetition domain](sources/over-repetition-probes.md#src-star-over-repetition-domain)
<a id="src-temporal-field-values-not-unique-group-runtime"></a>
- [Temporal field-values-not-unique group runtime](sources/inbound-group-operand-batches.md#src-temporal-field-values-not-unique-group-runtime)
<a id="src-boolean-value-count-group-runtime"></a>
- [Boolean value-count group runtime](sources/inbound-group-operand-batches.md#src-boolean-value-count-group-runtime)
<a id="src-group-carrier-static-admission"></a>
- [Group-carrier static admission](sources/inbound-group-operand-batches.md#src-group-carrier-static-admission)
<a id="src-group-carrier-duplicate-precedence"></a>
- [Group-carrier duplicate precedence](sources/inbound-group-operand-batches.md#src-group-carrier-duplicate-precedence)
<a id="src-group-carrier-admission-sweep"></a>
- [Group-carrier admission sweep](sources/inbound-group-operand-batches.md#src-group-carrier-admission-sweep)
<a id="src-extrema-sortable-kind-set"></a>
- [The extrema's admitted kind set is Number or Date](sources/inbound-group-operand-batches.md#src-extrema-sortable-kind-set)
<a id="src-group-runtime-and-reference"></a>
- [Group runtime and reference](sources/inbound-group-operand-batches.md#src-group-runtime-and-reference)
<a id="src-group-first-filled-runtime-order"></a>
- [Group first filled runtime order](sources/inbound-group-operand-batches.md#src-group-first-filled-runtime-order)
<a id="src-star-group-first-filled-runtime-order"></a>
- [Star group first filled runtime order](sources/inbound-group-operand-batches.md#src-star-group-first-filled-runtime-order)
<a id="src-sum-of-products-owning-group"></a>
- [Sum of products owning group](sources/inbound-group-operand-batches.md#src-sum-of-products-owning-group)
<a id="src-count-partial-extent"></a>
- [Count partial extent](sources/inbound-group-operand-batches.md#src-count-partial-extent)
<a id="src-pr2-correlated-operand-identity"></a>
- [Correlated direct-operand identity inside `Having`, reviewed inbound 2026-09-01](sources/inbound-group-operand-batches.md#src-pr2-correlated-operand-identity)
<a id="src-pr2-distinct-count-kind-families"></a>
- [`NumberOfDifferentValues` Custom and DateFragment families, reviewed inbound 2026-09-01](sources/inbound-group-operand-batches.md#src-pr2-distinct-count-kind-families)
<a id="src-pr2-semantic-index-carrier-matrix"></a>
- [Semantic-index entity-slot carrier matrix, reviewed inbound 2026-09-01](sources/inbound-group-operand-batches.md#src-pr2-semantic-index-carrier-matrix)
<a id="src-pr2-rulegroup-semantic-index"></a>
- [`RuleGroup` literal semantic-index suffix, reviewed inbound 2026-09-01](sources/inbound-group-operand-batches.md#src-pr2-rulegroup-semantic-index)

### Cross-layer source routes

<a id="computation-definition-execution-and-result"></a>
- [Computation definition, execution, and result](sources/cross-layer-routes.md#computation-definition-execution-and-result)
<a id="src-fixed-computation-target-scope"></a>
- [Fixed computation target scope](sources/computation-placement-and-constant-probes.md#src-fixed-computation-target-scope)
<a id="src-cross-group-computation-authoring-block"></a>
- [Cross group computation authoring block](sources/computation-placement-and-constant-probes.md#src-cross-group-computation-authoring-block)
<a id="src-computation-declaring-group-gate"></a>
- [Computation declaring group gate](sources/computation-placement-and-constant-probes.md#src-computation-declaring-group-gate)
<a id="src-cross-group-repeatable-constant-target"></a>
- [Cross group repeatable constant target](sources/computation-placement-and-constant-probes.md#src-cross-group-repeatable-constant-target)
<a id="src-repeatable-string-constant-target-check"></a>
- [A String constant its target rejects keeps the exact attempted value](sources/computation-placement-and-constant-probes.md#src-repeatable-string-constant-target-check)
<a id="src-repeatable-number-constant-target-check"></a>
- [Repeatable number constant target check](sources/computation-placement-and-constant-probes.md#src-repeatable-number-constant-target-check)
<a id="src-repeatable-number-constant-scale-rendering"></a>
- [A Number constant's scale is read twice, differently: the gate keeps trailing zeros, the store strips them and pads](sources/computation-placement-and-constant-probes.md#src-repeatable-number-constant-scale-rendering)

<a id="src-date-constant-target-formatting"></a>
- [Date constant target formatting](sources/temporal-constant-and-base-year-probes.md#src-date-constant-target-formatting)

<a id="src-date-constant-pre-1900-target"></a>
- [Date constant pre 1900 target](sources/temporal-constant-and-base-year-probes.md#src-date-constant-pre-1900-target)
<a id="src-datetime-errored-target"></a>
- [A computed DateTime whose rendering its own target would reject is ERRORED and poisons its readers: a five-digit year, and a date one day below the Gregorian floor, measured locally 2026-10-02](sources/temporal-constant-and-base-year-probes.md#src-datetime-errored-target)

<a id="src-constant-literal-family-gate"></a>
- [A bare constant's admission is gated by the target's declared format string, never its kind](sources/temporal-constant-and-base-year-probes.md#src-constant-literal-family-gate)
<a id="src-temporal-format-gate-not-component-sets"></a>
- [Temporal format gate not component sets](sources/temporal-constant-and-base-year-probes.md#src-temporal-format-gate-not-component-sets)
<a id="src-yearless-anchor-is-the-base-year"></a>
- [Yearless anchor is the base year](sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year)
<a id="src-temporal-constant-literal-composition"></a>
- [The temporal literal vocabulary composes, and the Base Year gate reads year disagreement](sources/temporal-constant-and-base-year-probes.md#src-temporal-constant-literal-composition)
<a id="src-yearless-constant-family"></a>
- [An omitted-year literal is a temporal constant at every target, 2026-10-02](sources/temporal-constant-and-base-year-probes.md#src-yearless-constant-family)

<a id="src-datetime-constant-zone-split"></a>
- [Datetime constant zone split](sources/temporal-constant-and-base-year-probes.md#src-datetime-constant-zone-split)

<a id="src-component-omitting-date-formats"></a>
- [Component omitting date formats](sources/temporal-constant-and-base-year-probes.md#src-component-omitting-date-formats)

<a id="src-base-year-yearless-store"></a>
- [Base year yearless store](sources/temporal-constant-and-base-year-probes.md#src-base-year-yearless-store)
<a id="src-fixed-target-star-placement"></a>
- [Fixed target star placement](sources/computation-placement-and-constant-probes.md#src-fixed-target-star-placement)
<a id="src-unsuppressed-assignment-scale-reach"></a>
- [Unsuppressed assignment scale reach](sources/computation-placement-and-constant-probes.md#src-unsuppressed-assignment-scale-reach)
<a id="src-dotted-short-date-format"></a>
- [Dotted short date format](sources/temporal-and-message-probes.md#src-dotted-short-date-format)
<a id="src-valueless-outcome-minting-and-application"></a>
- [Valueless outcome minting and application](sources/evaluation-and-application-routes.md#src-valueless-outcome-minting-and-application)
<a id="src-errored-target-applied-state"></a>
- [Errored target applied state](sources/evaluation-and-application-routes.md#src-errored-target-applied-state)
<a id="src-applied-document-over-limit-unobservable"></a>
- [Applied document over limit unobservable](sources/evaluation-and-application-routes.md#src-applied-document-over-limit-unobservable)
<a id="src-repeatable-string-application"></a>
- [Repeatable string application](sources/evaluation-and-application-routes.md#src-repeatable-string-application)
<a id="src-repeatable-number-aggregate-cascade"></a>
- [Repeatable number aggregate cascade](sources/evaluation-and-application-routes.md#src-repeatable-number-aggregate-cascade)
<a id="src-repeatable-numeric-wrappers-extrema"></a>
- [Repeatable numeric wrappers extrema](sources/evaluation-and-application-routes.md#src-repeatable-numeric-wrappers-extrema)
<a id="src-operation-valued-extrema"></a>
- [Operation-valued extrema](sources/evaluation-and-application-routes.md#src-operation-valued-extrema)
<a id="src-aggregate-repeatable-suffixes"></a>
- [Aggregate repeatable suffixes](sources/evaluation-and-application-routes.md#src-aggregate-repeatable-suffixes)
<a id="src-nested-current-repetition-cascades"></a>
- [Nested current repetition cascades](sources/evaluation-and-application-routes.md#src-nested-current-repetition-cascades)
<a id="src-scalar-mixed-consumer-first-dependency-order"></a>
- [Scalar mixed consumer first dependency order](sources/computation-scheduling-probes.md#src-scalar-mixed-consumer-first-dependency-order)
<a id="src-repeatable-diamond-per-row-states"></a>
- [Repeatable diamond per row states](sources/computation-scheduling-probes.md#src-repeatable-diamond-per-row-states)
<a id="src-diamond-dependency-clear-kinds"></a>
- [A four-deep dependency diamond orders correctly, and a silently cleared producer reads EMPTY where an errored one poisons](sources/computation-scheduling-probes.md#src-diamond-dependency-clear-kinds)
<a id="src-join-poison-and-substitution"></a>
- [A malformed producer clears every Number join that reaches it, and a twelve-computation plan runs in dependency order, measured locally 2026-09-26](sources/computation-scheduling-probes.md#src-join-poison-and-substitution)
<a id="src-datetime-join"></a>
- [A DateTime shift reads computed amounts and DateTimes fresh, poison and absence cross the join by the shared rule, and a computed DateTime is read back from its rendering, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-datetime-join)
<a id="src-document-step-join"></a>
- [Full-Date and Enumeration copies are read fresh across a join, chained copies included, and a pre-1900 Date retained as errored reaches its readers as poison, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-document-step-join)
<a id="src-date-range-join"></a>
- [A DateRange construction reads a computed Date fresh, and its readers read a cleared range as empty and an errored one as poison, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-date-range-join)
<a id="src-guarded-document-steps"></a>
- [A presence guard on a whole-document step clears it as empty when not met and as poison when it reads poison, and a guard on a computed Number reads its completion, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-guarded-document-steps)
<a id="src-first-filled-join"></a>
- [First filled join](sources/computation-scheduling-probes.md#src-first-filled-join)
<a id="src-extractor-join"></a>
- [Extractor and mixed-shift joins](sources/computation-scheduling-probes.md#src-extractor-join)
<a id="src-guard-on-malformed-source"></a>
- [A fill guard on a malformed source field poisons both guarded copies and their readers, on a root and per repeatable row, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-guard-on-malformed-source)
<a id="src-repeatable-row-alternatives"></a>
- [A repeatable target's guarded alternatives select per row by first match and abort on a reached poisoned guard, and the fixed table's two refusals hold there, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-repeatable-row-alternatives)
<a id="src-self-read-alternative-walk"></a>
- [A common precondition's target-read findings appear once per written read at the first judged alternative; measured locally and by the peer 2026-10-02](sources/computation-scheduling-probes.md#src-self-read-alternative-walk)
<a id="src-row-table-guard-order"></a>
- [A row table asks every guard's row binding before any alternative's own class, and selects lazily, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-table-guard-order)
<a id="src-repeatable-row-producers"></a>
- [At a repeatable target `Max`, a rounded division, `Abs`, `FirstFilledValue` and `NumberOfValueInFields` read a computed row copy fresh at their own row, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-repeatable-row-producers)
<a id="src-row-target-boundary"></a>
- [At a row target further atoms and a guard by name read their own or the enclosing row, and placement answers ahead of a copy comparison, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-target-boundary)
<a id="src-row-current-repetition"></a>
- [At a row target `CurrentRepetition` reads its row's coordinate at each group's level, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-current-repetition)
<a id="src-row-star-aggregates"></a>
- [At a row target a Number aggregate's star binds the row only above its first starred level and its `$` filter operand reads the row, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-star-aggregates)
<a id="src-row-star-scans"></a>
- [At a row target the scans, value counts, product sum and starred group count bind the row, and on the computation arm each leaves an over-limit row out, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-star-scans)
<a id="src-row-groups"></a>
- [At a row target a group operand inside the row is that row's instance and a deeper row reads its ancestor's, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-groups)
<a id="src-fixed-group-descendants"></a>
- [At a fixed target a fixed group's repeatable descendant is read over its in-capacity rows declaration-major, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-fixed-group-descendants)
<a id="src-row-atoms"></a>
- [At a row target the remaining atoms each read from the computing row, three of them refused by Lean, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-row-atoms)
<a id="src-first-filled-capacity"></a>
- [A typed or filtered `FirstFilledValue` star leaves an over-limit row out on the computation arm, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-first-filled-capacity)
<a id="src-repeatable-nested-star-aggregate"></a>
- [Repeatable nested star aggregate](sources/computation-scheduling-probes.md#src-repeatable-nested-star-aggregate)
<a id="src-computation-precondition-names"></a>
- [A computation precondition's presence slot answers the rule slot's classes, bound by the target, ahead of its operation's and an unguarded sibling's classes, measured locally 2026-10-02](sources/computation-scheduling-probes.md#src-computation-precondition-names)
<a id="src-join-operators-and-guards"></a>
- [Operators and guards at a join, cycle classes, and a self-read asked after the authoring and scale gates on every shape, measured locally 2026-10-01](sources/computation-scheduling-probes.md#src-join-operators-and-guards)
<a id="src-two-level-repeatable-join"></a>
- [Poison and empty substitution cross repetition levels and rows by the same rule, measured locally 2026-09-26](sources/computation-scheduling-probes.md#src-two-level-repeatable-join)
<a id="src-repeatable-join-operators-and-guards"></a>
- [Operators, computed-target fill guards and a fixed computed read on two repetition levels, measured locally 2026-10-01](sources/computation-scheduling-probes.md#src-repeatable-join-operators-and-guards)
<a id="src-scalar-mixed-reverse-authored-triple"></a>
- [Scalar mixed reverse authored triple](sources/computation-scheduling-probes.md#src-scalar-mixed-reverse-authored-triple)
<a id="src-numeric-extremum-call-boundary"></a>
- [Numeric extremum call boundary](sources/evaluation-and-application-routes.md#src-numeric-extremum-call-boundary)
<a id="src-custom-field-type-spi"></a>
- [Custom field type SPI: full-check raise and the codec's single opt-in caller](sources/evaluation-and-application-routes.md#src-custom-field-type-spi)

<a id="src-custom-validity-route"></a>
- [Named-type validation](sources/evaluation-and-application-routes.md#src-custom-validity-route)
<a id="src-field-values-not-unique-route"></a>
- [Field values not unique route](sources/evaluation-and-application-routes.md#src-field-values-not-unique-route)
<a id="src-fieldless-numeric-computation"></a>
- [Fieldless numeric computation](sources/evaluation-and-application-routes.md#src-fieldless-numeric-computation)
<a id="src-addressed-numeric-binary"></a>
- [Addressed numeric binary](sources/evaluation-and-application-routes.md#src-addressed-numeric-binary)
<a id="src-number-repeatable-first-filled"></a>
- [Number repeatable first filled](sources/evaluation-and-application-routes.md#src-number-repeatable-first-filled)
<a id="src-computed-target-reference"></a>
- [Computed target reference](sources/evaluation-and-application-routes.md#src-computed-target-reference)
<a id="src-temporal-construction-route"></a>
- [Temporal construction route](sources/temporal-and-message-probes.md#src-temporal-construction-route)
<a id="src-message-construction-route"></a>
- [Message/reference rules](sources/message-and-pointer-probes.md#src-message-construction-route)
<a id="src-selected-message-reference-resolution"></a>
- [Selected message references](sources/message-and-pointer-probes.md#src-selected-message-reference-resolution)

### Inbound provenance checkpoints


### Additional family checkpoints

<a id="src-peer-adapter-diagnostics-replay"></a>
- [Peer adapter diagnostics replay](sources/evaluation-and-application-routes.md#src-peer-adapter-diagnostics-replay)

<a id="src-numeric-computation-guards"></a>
- [Numeric computation guards read empty as zero and distinguish arithmetic failure from reached poison](sources/computation-scheduling-probes.md#src-numeric-computation-guards)

<a id="src-comparison-computation-guards"></a>
- [Typed comparison guards](sources/computation-scheduling-probes.md#src-comparison-computation-guards)

<a id="src-overlap-computation-guards"></a>
- [Overlap guards](sources/computation-scheduling-probes.md#src-overlap-computation-guards)

<a id="src-compositional-computation-guards"></a>
- [Shared computation guards](sources/computation-scheduling-probes.md#src-compositional-computation-guards)

<a id="src-calendar-expression-family"></a>
- [Calendar expressions](sources/temporal-runtime-fold-probes.md#src-calendar-expression-family)

<a id="src-compositional-temporal-expressions"></a>
- [Scalar temporal expressions](sources/temporal-runtime-fold-probes.md#src-compositional-temporal-expressions)

<a id="src-peer-ba-computations-replay"></a>
- [Six transferred peer computation models replay on 30 runtime documents](sources/evaluation-and-application-routes.md#src-peer-ba-computations-replay)

<a id="src-text-computation-guards"></a>
- [Text computation guards](sources/computation-scheduling-probes.md#src-text-computation-guards)

<a id="src-peer-computation-shapes-replay"></a>
- [Invoice replay](sources/evaluation-and-application-routes.md#src-peer-computation-shapes-replay)

<a id="src-field-fill-computation-guards"></a>
- [Field-fill computation guards](sources/computation-scheduling-probes.md#src-field-fill-computation-guards)


<a id="src-group-presence-computation-guards"></a>
- [Group-presence guards](sources/computation-scheduling-probes.md#src-group-presence-computation-guards)


<a id="src-group-presence-conditional-dependencies"></a>
- [Group dependencies](sources/computation-scheduling-probes.md#src-group-presence-conditional-dependencies)

<a id="src-group-conditional-profiles"></a>
- [Group profiles](sources/computation-scheduling-probes.md#src-group-conditional-profiles)

<a id="src-repeatable-group-profiles"></a>
- [Repeatable target-profile guards](sources/computation-scheduling-probes.md#src-repeatable-group-profiles)

<a id="src-filled-field-count-expressions"></a>
- [Filled-field count expression admission, 2026-10-03](sources/group-list-and-capacity-probes.md#src-filled-field-count-expressions)

<a id="src-compositional-temporal-disposition"></a>
- [Temporal slots and label failures](sources/temporal-runtime-fold-probes.md#src-compositional-temporal-disposition).

<a id="src-string-expression-family"></a>
- [String expression family](sources/evaluation-and-application-routes.md#src-string-expression-family)

<a id="src-validation-iteration-domain"></a>
- [Rule iteration](sources/evaluation-and-application-routes.md#src-validation-iteration-domain)

<a id="src-recursive-temporal-numeric-expression"></a>
- [Recursive temporal numeric expression](sources/temporal-and-message-probes.md#src-recursive-temporal-numeric-expression)

<a id="src-uniqueness-computation-guards"></a>
- [Uniqueness guards](sources/computation-scheduling-probes.md#src-uniqueness-computation-guards)

<a id="src-type-validity-computation-guards"></a>
- [Named-type computation guards](sources/computation-scheduling-probes.md#src-type-validity-computation-guards)

<a id="src-product-partial-capacity"></a>
- [Partial product declared capacity](sources/group-and-iteration-probes.md#src-product-partial-capacity)

<a id="src-recursive-date-validity"></a>
- [Date validity](sources/temporal-runtime-fold-probes.md#src-recursive-date-validity)

<a id="src-indexed-time-components"></a>
- [Indexed Time components](sources/temporal-runtime-fold-probes.md#src-indexed-time-components)

<a id="src-indexed-type-validity"></a>
- [Indexed type validity](sources/computation-scheduling-probes.md#src-indexed-type-validity)

<a id="src-indexed-patterns"></a>
- [Indexed patterns](sources/computation-scheduling-probes.md#src-indexed-patterns)

<a id="src-partial-temporal-reads"></a>
- [Partial temporal reads](sources/temporal-runtime-fold-probes.md#src-partial-temporal-reads)

<a id="src-having-temporal-constant-effects"></a>
- [Temporal filter constants](sources/having-filter-probes.md#src-having-temporal-constant-effects)

<a id="src-having-range-family"></a>
- [Having ranges](sources/having-filter-probes.md#src-having-range-family)

## Question-to-locus index

Use the clause map for subsystems and this table for mechanisms. Search questions or symbols before auditing. “Decides” gives claim scope; the composition rule above governs cross-layer behavior.

| Semantic question | Decisive Kernel locus | Decides / caveat |
|---|---|---|
| Which DocumentV2 rows and cells physically exist? | `DocumentV2`, `GroupInstanceV2`, `FieldInstanceV2`, `RepetitionsV2` | Immutable physical topology and present instances; not checked semantic validity |
| How is immutable input projected into validation? | `DocumentAbstractRtService`, `ValidationData`, `CheckCommand.formalePruefung`, `FormalChecker` | Model/config selection and eager formal checking; later rule/computation behavior is separate |
| When does a checked cell become validation UNKNOWN or computation poison? | `ValidationCache`, `CalculationCache`, field format definitions, generated read sites | Phase-local read behavior; a generated program or template is needed for reachability/order |
| How are required and unique-index findings staged? | `AutogeneratedRulesService`, `ValidationCommand.processInternalVV`, `MainValidatorController.preliminaryError`, `IndexFieldCache` | Generated finding construction and invalid marking; not authored rule execution |
| What are the three-valued Boolean tables? | `DreiWertBool`, `ValidierungsErgebnis`, condition templates | Local truth/result algebra; template call order is required for short-circuit claims |
| How are empty scalar values compared? | `BedingungsOperatorHelper`, `VkBigDecimal.NICHT_PRUEF_REL_ZAHL`, type format definitions | Local empty substitution and comparison behavior; authoring legality comes from checkers |
| How are Number operations authored and lowered? | numeric operation checkers, `CheckOpUtils`, `CompositeOperation` backing bean | Static admission, tree shape, operand order, and emitted operation code; runtime helpers decide numeric results |
| What precision, rounding, comparison, and storage rules apply to Number? | `VkBigDecimal`, `NumberCombiner`, `BedingungsOperatorHelper.vergleiche`, `FormatDefinitionZahl` | Runtime arithmetic/comparison/storage mechanisms; reachability and target handling remain separate |
| Which numeric result becomes a target error, clear, or stored value? | `CalculationController.handleBerechnetenWert`, numeric format checks, `DocumentComputationResultImpl` | Target checking and public result classification across layers; inspect all three |
| How do `RangeAsNumber` and `FieldValueAsNumber` select and convert text? | their parser/checker classes, `RuntimeController`, host UTF-16 digit conversion | Selection/fallback and host digit behavior; declaration legality must be checked separately |
| How are Date/Time/DateTime values decoded and checked? | temporal format definitions, `ValidationDateParser`, Date/Time parser checkers | Field-kind/component admission and decoded values; model-zone instant resolution is separate |
| Which model zone is legal and selected? | `NoMetaModelChecks.checkTimeZone`, `MetaDataValidierungIntern.getTimeZone` | Static zone-id legality and configured zone selection |
| How is a fresh local temporal label resolved? | `DateUtil`, especially strict construction/clearing helpers | Fresh label resolution; do not infer calendar-addition behavior from it |
| How do temporal additions and differences behave? | `BedingungsOperatorHelper`, `GregorianCalendar` call sites, generated temporal operation code | Calendar mutation and completed-period/day behavior; exact emitted operand order needs backing bean/template review |
| How are Date/Time construction arguments ordered? | construction checkers, parse-tree constructors, `CodeGenCreator.createDatumParameter`, operation `.st` files | General authoring/lowering and generated argument order |
| How are String line breaks, patterns, lengths, and legal characters checked? | `FormatDefinitionString`, `PatternUtils`, `LegalCharTester`, String parser/checkers | Local formal and target policy; host matcher behavior remains an injected boundary in Lean |
| What is Enumeration value identity versus category identity? | Enumeration model API, `CheckVergleichsBedingungImpl`, runtime Enumeration projection | Stored token, category position, and comparability; display labels are not identity |
| How do value-list quantifiers scan operands? | value-list checkers/backing beans, `CheckEntityListenUtils`, generated condition code, `ValidationCache` | Static list shape and generated scan order; maintained differentials decide poison/order seams |
| Which repeatable rows are iterated? | `EntityIterator`, `KontextIterator`, `EbenenIterator`, `GroupFillCache`, iteration `.st` files | Actual-row extent, environment traversal, and loop nesting; do not infer rows from filled cells |
| How are filtered stars and outer correlation applied? | filter visitors, path/checker classes, iterator construction, generated rule code | Static filter discovery and runtime traversal; concrete generated shape may be needed for ordering |
| How is repetition-not-unique evaluated? | RNU checkers, `IterationNotValidVisitor`, generated uniqueness rule path | Key relation, cluster construction, and validation emission; `@From` legality is a separate path check |
| How does ordinary semantic-index lookup work? | semantic-index checkers, `SemanticIndexLevelVisitor`, ordinary indexed-read runtime path | Key/column construction and ordinary match-versus-column timing |
| How does parallel-index suppression/clearing work? | `CalculatedFieldIterationLimitCreator`, `CalculationCache.getIterationValuesForGroups`, `markFieldsUsingInvalidIndexGroupsAsIncorrectlyCalculated`, `CodeGenCalculatedField.st` | Parallel route participation, suppressed iteration, and post-loop invalid marking; it is not the ordinary semantic-index route |
| How are same-target computations combined? | `CalculationDependencies`, `CodeGenCalculatedFieldBuilder`, `CodeGenCalculationAlternative.st` | Order-preserving flattening and one first-selected table; selected empty/poison/failure ends the scan |
| What orders distinct computation targets? | `CodeGenCalcBuilder`, `CalculationDependencies`, `TopologicalSortHelper`, `CodeGenCalc.st` | Codegen-time dependency order, deterministic independent tie-break, and cycle rejection; runtime adds no scheduler |
| When is an invalid computed dependency observed? | `CalculationCache` value/presence reads plus generated condition/expression control flow | Read-driven poison only when the access is reached; a graph edge alone does not pre-skip |
| Which stored computed inputs are hidden and which completed values are visible? | `CalculationCommand` stripping and `CalculationCache` calculated-value overlay | Working-view stripping and completed producer visibility |
| How are computation result channels built? | `DocumentComputationResultImpl.init` | Exact pointer partition, source-relative change, cleared/with-errors/without-errors, and `noErrorOccurred` |
| In what order is a computation result applied? | `DocumentComputationResultImpl.applyTo(DocumentV2)` | Cleared → with-errors → with-changes on a caller-supplied document; no validation call |
| When is generated computation validation run? | `ValidationModelConverter`, `ComputationAlternativesJoiner`, validation service orchestration | Later validation owns all relevant alternatives; computation execution does not invoke it |
| When is a partial rule skipped? | `rulesDir/CodeGenRuleDefinition.st` in Java/Groovy/JavaScript-VK | Rule-level early return before iteration/condition; `CodeGenRules.st` is only the enclosing pass-through |
| How are validation messages rendered? | message model/API, `FehlerHandler`, `CheckCommand.ersetzeFeldParameter`, errortext grammar | Locale resource lookup and token replacement; computation pointer partition is a later separate mechanism |
| How is a custom condition invoked? | `ApplicationCondition.st`, `CodeGenRuleDefinition.st`, `ValidationCache`, `CustomConditionService`, `MainValidatorController` | Reached factory lookup, callback and classification; concrete host APIs remain external |

## a12-dmkits drill route

<a id="a12-dmkits--peer-clean-room-engine--verified-knowledge-a12-rulekit-checkout"></a>
<a id="a12-dmkits-peer-clean-room-engine-verified-knowledge-a12-rulekit-checkout"></a>
<a id="interpreter--a-peer-clean-room-kmp-evaluator-the-closest-reference"></a>
<a id="interpreter-a-peer-clean-room-kmp-evaluator-the-closest-reference"></a>
<a id="adapter--the-kernel-as-oracle-differential-jvm-kernel-linked"></a>
<a id="adapter-the-kernel-as-oracle-differential-jvm-kernel-linked"></a>
<a id="the-doc-set-indexed-by-the-hub"></a>
<a id="corpus-and-the-catalog"></a>
<a id="the-n-drill-down-topology-and-synchronization-provenance"></a>
<a id="what-the-coverage-tells-us"></a>

Use a12-dmkits as maintained knowledge and a kernel-executing test estate, never as the oracle:

- [`docs/SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) — exhaustive per-clause index;
- [`docs/KERNEL-SEMANTICS.md`](../../a12-rulekit/docs/KERNEL-SEMANTICS.md) — peer canonical prose;
- [`docs/KERNEL-FINDINGS.md`](../../a12-rulekit/docs/KERNEL-FINDINGS.md) and [`docs/INTERPRETER-FINDINGS.md`](../../a12-rulekit/docs/INTERPRETER-FINDINGS.md) — evidence-qualified findings and implementation consequences;
- [`docs/RT-SEMANTICS-LEDGER.md`](../../a12-rulekit/docs/RT-SEMANTICS-LEDGER.md) and [`docs/MVK-LEDGER.md`](../../a12-rulekit/docs/MVK-LEDGER.md) — kernel-mined runtime/static inventories;
- [`interpreter/`](../../a12-rulekit/interpreter/) — peer clean-room semantics and common tests;
- [`adapter/src/test/`](../../a12-rulekit/adapter/src/test/) — kernel-executing laws and differentials;
- [`corpus/`](../../a12-rulekit/corpus/) and catalog semantics facets — retained reusable model/case families where present.

An a12-dmkits interpreter agreement is triangulation. A maintained adapter test that executes the kernel is a Kernel lock. Neither is a project-local retained observation; [`EVIDENCE.md`](EVIDENCE.md) owns that stronger replay boundary.

## Maintenance rule

Edit the source shard when its provenance or drill route changes; change this hub only for navigation. [Documentation discipline](DOC-DISCIPLINE.md) owns the update boundaries.
