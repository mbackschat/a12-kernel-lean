# Authoritative sources and drill routes

<a id="authoritative-sources--how-to-drill"></a>
<a id="authoritative-sources-how-to-drill"></a>

This hub and its bounded [`sources/`](sources/) records are the repository’s provenance owner. They map semantic questions to the authoritative kernel layer and to maintained a12-dmkits knowledge. They are not a second specification, findings ledger, implementation map, evidence inventory, or review history.

Authority order is **[`../../a12-kernel`](../../a12-kernel) → project-owned [`../spec/`](../spec/) and Lean theory → [a12-dmkits](../../a12-rulekit)**. The real kernel is the behavioral oracle. The spec and Lean theory are this project’s working semantics-of-record. a12-dmkits is a peer clean-room implementation, source of maintained kernel-executing differentials, and knowledge corpus.

All kernel source routes below target kernel **30.8.1**, inspected at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. Read source to learn behavior; never link, call, ship, or transcribe it.

## Query contract

Start from the relevant [`spec/` clause](../spec/SEMANTICS-MAP.md), then:

1. identify the claim class with the engine routing rule;
2. use the clause table for the subsystem, then the question-to-locus index for the exact decisive class, template, backing bean, method, or service;
3. follow a12-dmkits’ guard-checked [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) for its exhaustive prose/test/corpus inventory;
4. consult this file’s focused packets only for cross-layer mechanisms not answered by one locus.

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

**What the CLI *does* reach is the static consistency oracle, and that is a first-class local route.** `model check`, `workspace check`, `rule check`, and computation dry-run validation call the real kernel's `checkConsistency` and can therefore support a static `KERNEL_CONFIRMED` claim, with the kernel message surfaced as the diagnostic summary and the extracted `MVK_*` as its code. So a **static-legality** question, such as which diagnostic class an illegal model draws, whether a gate reads the whole operand list, or whether a spelling is admitted, is measurable here and does not belong upstream.

**The CLI's own fail-fast spec validation pre-empts kernel declaration gates, and then the route measures the tool.** Confirmed 2026-08-29 on two independent gates.

**Partly resolved the same day.** From a12-dmkits `01bc94279f0aee06fd8d9ccfad2e116354aa409e` these refusals carry the standard `rejected` envelope with `RK_INVALID_VALUE` and `source: PRECHECK`, so the layer is machine-readable, and the messages no longer attribute a local refusal to the kernel. The preflight itself stays, and `model check` over a hand-edited **copy** of a model reaches the kernel's own verdict ([reconciliation](#src-2026-08-29-reconciliation)). From the [2026-08-30 handback](#src-2026-08-30-reconciliation) the peer's own skill rule scopes rather than forbids that route: hand-writing a shape into a copy is measurement and never authoring, and the copy is never persisted from or kept.

The originating observation, before the envelope fix: `field add` refused `maxFractionalDigits` above 14 with stderr *"invalid field spec: maxFractionalDigits must be ≤ 14 (the kernel's cap)"*, and refused an Enumeration category whose value list is shorter, longer, or empty against its enum's values, both exiting 2 with **no envelope at all** while attributing the rule to the kernel. That is how such a row becomes a false attribution, and it is why neither the kernel's `fieldScaleCap` gate nor its category-alignment gate is reachable through the `field add` route itself.

One limit on the replacement envelope: `RK_INVALID_VALUE` with `source: PRECHECK` does not discriminate **which** local gate refused, since the schema gate emits the same pair.

The tell is the envelope, not the message: a kernel verdict carries `verification: KERNEL_CONFIRMED` and an `MVK_*` diagnostic, while a front-end refusal carries neither and writes plain stderr. Read it before attributing any refusal. **It really is the pair, and neither field attributes on its own** — measured at a12-dmkits `041346095`, after this project asserted the opposite and was corrected.

`source: KERNEL` reaches a **codeless** deserialize-tier refusal, and an `MVK_*` code rides `source: PRECHECK` on eleven client-side codes that rulekit's typed builders mint deliberately, so an author sees the class the kernel would name. Only both together resolve to a kernel notification, and `verification` is weaker than either: the DSL-bearing authoring verbs asserted it unconditionally before `842ef01a6` ([reconciliation](#src-2026-08-30-reconciliation)). Treat every **declaration-shape** claim whose gate the CLI duplicates as not re-dischargeable here until an escape hatch exists, and note that this affects re-verification only: an accepted declaration still reaches the kernel's own oracle normally.

The reusable provenance route is `../a12-rulekit/scripts/prepare-dmtool-source.sh`: it accepts only the sibling's exact clean HEAD, reuses or rebuilds the JVM launcher as needed, and verifies its reported revision before returning it. Each retained observation records the actual launcher and kernel versions from that run rather than inheriting the historical 2026-08-06 launcher identity. [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback) owns the probe method and the required persisted-read-back check.

**The route's method is calibrated at a clean exact-source launcher.** Before using this route for a new claim it was run against an answer already measured independently, so a method error would surface as disagreement rather than as a plausible new fact. At clean a12-dmkits revision `cd41ea94b470a190f7d766ea6d7adf26b6ba74cf`, dmtool `0.12.1` with built/runtime kernel `30.8.1` accepted `FieldValuesNotUnique(CountedOn, DueOn)`, rejected the two-operand Date/String list with `MVK_VARYING_TYPES_NOT_ALLOWED`, and rejected both Date/String/Boolean and Date/Boolean/String with `MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED` and the mixing code absent.

That reproduces a12-dmkits `5f1c08dc`/`618d2847` for [`SPEC-2026-08-05-04`](archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-05-04--a-field-list-admission-gate-applies-to-the-whole-operand-list-so-authored-position-does-not-select-the-diagnostic-class). The two-operand rejection proves the mixing gate is live in the same model. The accepted rule persisted, read back structurally as `FieldValuesNotUnique(/Probe/CountedOn, /Probe/DueOn)`, and survived `model check`, all `KERNEL_CONFIRMED`.

**The same clean route establishes fixed filled-group computation admission and its nearest boundaries.** Computation dry-run accepts two and three distinct disjoint fixed groups, including a nested fixed terminal beside a disjoint sibling, and rejects a one-group plain list with `MVK_PARAMSIZE_INVALIDGN`, an exact duplicate with `MVK_DUPLICATE_PARAM1`, an ancestor/descendant pair and root/descendant pair with `MVK_DUPLICATE_PARAM2`, and an unstarred repeatable group with `MVK_NO_WILDCARD`. No fixed list above three was measured, so correspondence for larger lists remains unverified. A starred repeatable group is accepted alone and beside a fixed group; matching `rule check` controls admit both spellings. The ordinary nonrepeatable root with `*` is rejected `MVK_INVALID_WILDCARD`.

The accepted two-fixed-group computation persisted, read back as `NumberOfFilledGroups(Beta, Gamma)`, and survived `model check`, all `KERNEL_CONFIRMED`. This is static consistency evidence only and does not widen the measured compute-time presence account to repeatable operands or nested descendants of an operand group.

**The `dmtool` CLI is not a route to kernel runtime, and no flag makes it one.** Its runtime verbs — `model eval`, `rule eval`, `model compute` — run on the kernel-free `dm.interpreter` as the sole eval engine on every target. The opt-in `--kernel` eval engine was **retired** at a12-dmkits Set V on 2026-07-12 and the flag is now actively rejected on every profile, because kernel runtime validation needs Groovy code generation that the native binary cannot host. The kernel remains reachable through the CLI **only** for the static consistency gate, `rule check` and `model check`. So a `model compute` reading answers what the *interpreter* computes, which is never the oracle. Kernel runtime is reached only from a12-dmkits' JVM estate, and it now has **two** shapes there: a purpose-written maintained differential, and the parameterized probe below.

**Kernel runtime has a maintained parameterized route, accepted upstream on request.** The `:adapter:kernelProbe` Gradle task runs the real kernel over a supplied model and documents on **both** codegen strategies and writes one deterministic JSON artifact this project pins by SHA-256 and replays, so a runtime question no longer costs a purpose-written Kotlin test. Accepted at a12-dmkits `06b84701969979a2e5a2b63de7445a6a1d521473` for the `compute` exposure, on top of `34e1c7c5` for the original `validateFull` probe; the normative contract is [`KERNEL-PROBE-SPEC.md`](../../a12-rulekit/docs/KERNEL-PROBE-SPEC.md) §2 to §4 with the request and artifact schemas beside it under `../a12-rulekit/adapter/src/test/resources/kernel-probe/`.

```sh
./gradlew :adapter:kernelProbe -Prequest=<request.json> -Pout=<artifact.json>
```

The request's `observe` key selects the entry points. `validateFull` is always observed and cannot be dropped, because an engine block's `messages` is a required key of `schemaVersion` 1 and an unlooked-at empty list would be indistinguishable from nothing firing; `observe: ["compute"]` is refused for exactly that reason, and a compute-only consumer therefore pays a validation pass per row per strategy. Adding `compute` adds a per-engine `computations` block: `outcomes` sorted by `field`, each carrying `cleared`, `errored`, and a `value` that is **absent on a clear**, plus the `formalErrorsInOperands` channel. `enginesAgree` is derived over every channel a block reports rather than over the messages alone. Three claim limits travel with the route, and each one defeats a tempting reading.

**`validatePart` is a third observation, accepted upstream at a12-dmkits `8cad1224f86e91c46f0db3573adb4f0fe894a959` after this project recorded the coverage leg as unreachable.** Asking for it makes each row's `relevant` required — a set of `{path}` objects naming the covered fields — and adds a `partialMessages` block to each engine block, so a retained artifact produced without it keeps its bytes and its digest. An **absent** `relevant` is "not observed" and an **empty** one is the `noneRelevant` request; the two stay distinct end to end and `partialMessages` renders even when empty, so an empty result is readable as a measurement rather than as an omission. Omit `reps` unless a specific repetition is the point: it takes one entry per path *part*, not per repeatable part, and the probe otherwise fills the all-wildcard form.

`validateFull` remains the invariant control on a `validatePart` row, because it cannot see the coverage and must answer identically whatever it is.

`formalErrorsInOperands` is the checked-plan inventory of [`09-computations.md` §3.3](../spec/09-computations.md#33-what-compute-reports), never a cause edge: it is emitted whether or not anything was skipped, its operand set includes fields merely *contained by* a referenced group rather than a read trace, and a target cleared because the computation it read was itself ERRORED names nothing in it. The ERRORED producer's own per-instance error message is **not exposed** by the artifact, so a run-fault cause is still unreachable through this route. And `schemaVersion` stayed `1` by deliberate byte-compatibility, so the version no longer determines the artifact's shape and a retained artifact must record what its request asked for.

[`TESTING.md`](TESTING.md#the-kernel-runtime-probe-route) owns the operating method; the [fixed-group first-filled checkpoint](#src-group-first-filled-runtime-order) records this repository's first use and its exact claim boundary.

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

### Reviewed numeric-scale continuity

Clean a12-dmkits revision `0e303b56cc1a605b1daee6fadc46408258fdf8d9` retains the accepted `SPEC-2026-07-19-09` account at all three maintained evidence routes: [`NumericScaleSummary`](../../a12-rulekit/rulekit/src/main/java/io/github/mbackschat/a12/dm/rulekit/dsl/NumericScaleSummary.java) returns a non-expandable summary from every power branch, [`NumericScaleGateTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/dsl/operators/NumericScaleGateTest.java) separates the narrow known-scale power from an expandable literal result, and the [`§5 numeric-scale finding`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf43) states that power remains non-capable even when the scale-0 exception derives a known scale. This reviewed inbound continuity makes the capability sentence in [`spec/04`](../spec/04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time) explicit without creating another outbound sync-ledger request.

### Reviewed pointer and operator-domain batch

a12-dmkits revisions `ffe0066bedcef9d8dbf8b4881986ec1b419e4543`, `751d45b082697ba718b2d5ecd571ff20ce3e00e0`, and `61705844fd4766eb0fa5c2900da7d4508e6cb3ac` separate exact document pointers from `PartiallyKnownDocumentMultiPointer`, route every message-address channel through the latter, and retain the kernel-factory matrix in [`A12PointerKernelDomainDiffTest`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/A12PointerKernelDomainDiffTest.java). That test distinguishes value factories, the exact string codec, message construction, exact conversion, the root, assertion-dependent production behavior, and the raw arity asymmetry instead of attributing one entry point's rule to every pointer type.

a12-dmkits revision `ddf5dd921ee55752ca24e18174bbaed47dcfe924` is the reviewed operator-domain batch behind the 2026-08-01/02 spec reconciliation.

Its maintained owners include [`MixedDateTimeOrderingDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/MixedDateTimeOrderingDiffTest.kt), [`DateRangeEqualityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/DateRangeEqualityDiffTest.kt), [`FirstFilledValueAdditionalKindDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueAdditionalKindDiffTest.kt), [`FirstFilledValueEntitySpecDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueEntitySpecDiffTest.kt), [`CurrentRepetitionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CurrentRepetitionDiffTest.kt)

[`PredefinedTypeValidityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PredefinedTypeValidityDiffTest.kt), [`TemporalLiteralFormatGateLawsTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/TemporalLiteralFormatGateLawsTest.java), [`DateShiftAmountAdmissionLawsTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/DateShiftAmountAdmissionLawsTest.java), and [`SemanticIndexSlotLawsTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/SemanticIndexSlotLawsTest.java).

The peer revision is inbound reviewed provenance, so its accepted canonical corrections do not create a second outbound sync-ledger request.

### Reviewed group-count multiplicity batch

a12-dmkits revision `856465c37` (clean) carries two Kernel observations this project consumes at the [starred group-count checkpoint](sources/group-and-iteration-probes.md#src-starred-group-count-computation): the compute arm's over-limit exclusion reproduced on the peer's own fixture with the four-row control this project's capture lacked, and the first measurement anywhere of a list holding **two starred operands**, including the same group named twice. Both live in [`NestedGroupFillCountLawsTest`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/NestedGroupFillCountLawsTest.java) and were read here rather than taken on report; that suite drives the real Kernel runtime rather than the peer interpreter.

Revision `7967f5cb3` completes that batch with the two-star shapes' **static** admission, through the Kernel's own `checkConsistency`, after this project pointed out that runtime acceptance is not an authoring verdict. The same revision retracts a provenance line that had cited this project as having pinned those rows; the rows came from a window this project could not certify clean and were never citable.

Revision `531a2c769` adds two more from the same exchange: the separating document for the self-validation message's **direction**, which this project named but could not reach, and the `fillToFix` all-or-nothing projection reproduced on an all-filled document. Both are recorded at the [message-polarity checkpoint](sources/group-and-iteration-probes.md#src-starred-operand-message-polarity), and the second closes [`SPEC-2026-08-30-06`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-30-06).

The over-limit half originated in this project and is now measured on both estates, so it needs no outbound request. The two-star halves are inbound and create none by the rule above. Both rest on the peer's estate alone — the checkpoint's `two-star-limit` record owns that.

### Reviewed group-operand extent and coverage batch

a12-dmkits revision `4e174d86a` disposes three outbound entries from this project and carries two Kernel observations it consumes, each read here rather than taken on report.

[`StarredGroupQuantifierCapacityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/StarredGroupQuantifierCapacityDiffTest.kt) first **refuted** [`SPEC-2026-08-31-17`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-17), **retracted that refutation at `b145ce565`**, and then settled the entry at source revision `abe50e717dcde31b85ecfda9b98093e797bacf5b` inside reviewed integration revision `b9e7fbdc6b4806e15945bf7f993c04724a83437c`. The third route separates the threshold extent through descendants present only below an in-capacity or over-limit parent and confirms it independently through one-level partial exact-row relevance. The [capacity checkpoint](sources/group-list-and-capacity-probes.md#src-starred-group-quantifier-capacity) owns the exact observations and limits.

[`PartialCoverageGroupOperandDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialCoverageGroupOperandDiffTest.kt) reproduces [`SPEC-2026-08-31-18`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-18)'s count rule exactly and **splits its predicate half three ways**, with a coverage this project's batch did not run — a whole operand group left uncovered, where `NotAllGroupsFilled` is silent because an uncovered group is undecided rather than empty. The [partial-coverage checkpoint](sources/group-list-and-capacity-probes.md#src-partial-coverage-group-operands) owns it.

The same revision reports that a12-dmkits **cannot corroborate** [`SPEC-2026-08-31-16`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-16) through its renderer, which is what that entry's acceptance condition anticipated. `b145ce565` then corroborates the substantive half on the typed value instead, as `KF228` in [`MessagePointerVectorDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/MessagePointerVectorDiffTest.kt): one referenced field's `repetitionIndexes()` reads `[1, 0, 1]` from a rule leaving its repeatable level free and `[1, 1, 1]` from a rule bound to that row.
Reading that revision also settled the premise a12-dmkits had flagged: no kernel class emits either spelling. `KernelRuntimeProbe.address` renders one typed pointer two ways by a documented branch, so the "two spellings" half of that entry was a claim about the instrument and is withdrawn. The [selector checkpoint](sources/message-and-pointer-probes.md#src-address-dialect-selector) owns both halves.

The reviewed revisions are inbound provenance and create no new outbound request. Their accepted corrections land in [`spec/02`](../spec/02-logic-and-formal-errors.md) and [`spec/10`](../spec/10-validation-and-polarity.md), while the existing ledger entries retain the reconciliation dispositions.

## Provenance checkpoint index

Search stable `src-` anchors in this hub, then follow the link to the bounded family shard. Exact revisions and source-level claim limits remain in those records.

### Kernel lock source index

<a id="src-kernel-lock-index"></a>
- [Known Kernel locks and deliberate non-locks](sources/kernel-locks.md#src-kernel-lock-index)

### DateRange construction source checkpoints

<a id="src-full-date-stored-input"></a>
- [Stored full-Date input and formal causes](sources/date-range-construction.md#src-full-date-stored-input)
<a id="src-date-range-stored-input"></a>
- [Stored DateRange input and formal causes](sources/date-range-construction.md#src-date-range-stored-input)
<a id="src-date-range-construction-equality"></a>
- [Filled DateRange construction equality](sources/date-range-construction.md#src-date-range-construction-equality)
<a id="src-date-range-year-fragment-construction"></a>
- [Year-fragment DateRange construction](sources/date-range-construction.md#src-date-range-year-fragment-construction)
<a id="src-date-range-year-month-fragment-construction"></a>
- [Year-month-fragment DateRange construction](sources/date-range-construction.md#src-date-range-year-month-fragment-construction)
<a id="src-date-range-base-year-fragment-construction"></a>
- [Base-Year and yearless DateRange fragments](sources/date-range-construction.md#src-date-range-base-year-fragment-construction)
<a id="src-date-range-yearless-construction-target"></a>
- [Yearless DateRange construction targets](sources/date-range-construction.md#src-date-range-yearless-construction-target)
<a id="src-indexed-date-range-construction-target"></a>
- [String-indexed DateRange construction targets](sources/date-range-construction.md#src-indexed-date-range-construction-target)
<a id="src-date-range-bound-extraction"></a>
- [Stored DateRange bound extraction](sources/date-range-construction.md#src-date-range-bound-extraction)
<a id="src-date-range-plural-overlap"></a>
- [Plural scalar-versus-list DateRange overlap](sources/date-range-construction.md#src-date-range-plural-overlap)
<a id="src-date-range-fragment-first-filled"></a>
- [Fragment DateRange `FirstFilledValue`](sources/date-range-construction.md#src-date-range-fragment-first-filled)
<a id="src-date-range-direct-first-filled"></a>
- [Direct-field-list DateRange `FirstFilledValue`](sources/date-range-construction.md#src-date-range-direct-first-filled)
<a id="src-date-range-yearless-overlap"></a>
- [Unconfigured yearless DateRange overlap, measured locally 2026-08-22](sources/date-range-construction.md#src-date-range-yearless-overlap)
<a id="src-date-range-mixed-year-overlap"></a>
- [Mixed-year DateRange overlap admission and completion, measured locally 2026-08-22](sources/date-range-construction.md#src-date-range-mixed-year-overlap)
<a id="src-date-range-bound-base-year"></a>
- [DateRange bound extraction and Base-Year completion, measured locally 2026-08-22](sources/date-range-construction.md#src-date-range-bound-base-year)
<a id="src-date-range-component-set-crossing"></a>
- [DateRange component-set crossing, measured locally 2026-08-22](sources/date-range-construction.md#src-date-range-component-set-crossing)
<a id="src-date-range-construction-operand-grid"></a>
- [DateRange construction-operand refusal grid, measured locally 2026-08-23](sources/date-range-construction.md#src-date-range-construction-operand-grid)
<a id="src-date-range-exact-and-configured-constructor-targets"></a>
- [Exact ISO and configured-fragment constructor targets, measured locally 2026-08-23](sources/date-range-construction.md#src-date-range-exact-and-configured-constructor-targets)
<a id="src-date-range-year-fragment-constructor-target"></a>
- [Year-bearing fragment constructor targets, measured locally 2026-08-23](sources/date-range-construction.md#src-date-range-year-fragment-constructor-target)
<a id="src-date-range-construction-target-crossing"></a>
- [DateRange construction target spellings, measured locally 2026-08-23](sources/date-range-construction.md#src-date-range-construction-target-crossing)

### Temporal and message source checkpoints

<a id="src-semantic-index-kind-independence"></a>
- [The index field's kind and the selected target's kind are independent, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-semantic-index-kind-independence)
<a id="src-rule-message-parameter-grammar"></a>
- [The rule-message parameter grammar: paths, quoting, category, and Base Year, measured locally 2026-08-24](sources/message-and-pointer-probes.md#src-rule-message-parameter-grammar)
<a id="src-rule-message-parameter-rendering"></a>
- [What a rule-message parameter renders, measured locally 2026-08-24](sources/message-and-pointer-probes.md#src-rule-message-parameter-rendering)
<a id="src-time-datetime-stored-input"></a>
- [Stored Time and DateTime input causes, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-time-datetime-stored-input)
<a id="src-declared-format-temporal-input"></a>
- [Declared-format temporal input correction and widened grid, reviewed inbound 2026-08-29](sources/temporal-and-message-probes.md#src-declared-format-temporal-input)
<a id="src-temporal-format-vocabulary"></a>
- [Cross-kind temporal format admission in the original measured subset, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-temporal-format-vocabulary)
<a id="src-partial-date-input-causes"></a>
- [Which formal cause a partially known Date draws, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-partial-date-input-causes)
<a id="src-date-decoded-identity-witness"></a>
- [Whether two stored Date texts can decode to one instant, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-decoded-identity-witness)
<a id="src-temporal-aggregate-gate"></a>
- [Which temporal format gate each aggregate carrier uses, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-temporal-aggregate-gate)
<a id="src-pr2-date-extraction-diagnostics"></a>
- [Date-extraction diagnostic matrix, reviewed inbound 2026-09-01](sources/temporal-and-message-probes.md#src-pr2-date-extraction-diagnostics)
<a id="src-message-address-dialects"></a>
- [A message address is written in one of two dialects, and which one depends on the operand](sources/message-and-pointer-probes.md#src-message-address-dialects)

<a id="src-omitting-date-formats"></a>
- [What a component-omitting DATE format stores, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-omitting-date-formats)
<a id="src-filled-field-count"></a>
- [What a formally invalid operand does to `NumberOfFilledFields`, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-filled-field-count)
<a id="src-date-from-datetime"></a>
- [What `DateFromDateTime` reads, and the source gate both component extractors share, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-from-datetime)
<a id="src-date-from-datetime-computation"></a>
- [`DateFromDateTime` scalar computation reaches the full-Date target channels, measured locally 2026-08-24](sources/temporal-and-message-probes.md#src-date-from-datetime-computation)
<a id="src-date-from-datetime-repeatable-computation"></a>
- [`DateFromDateTime` computes exact repeatable rows, measured locally 2026-08-24](sources/temporal-and-message-probes.md#src-date-from-datetime-repeatable-computation)
<a id="src-value-as-date-locus"></a>
- [Where a partial-Date `ValueAsDate` operand may be read, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-value-as-date-locus)
<a id="src-rule-message-semantic-index"></a>
- [The semantic-index suffix on a rule-message parameter, measured locally 2026-08-23](sources/message-and-pointer-probes.md#src-rule-message-semantic-index)
<a id="src-date-range-endpoint-shapes"></a>
- [Which operand shapes a DateRange endpoint admits, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-endpoint-shapes)
<a id="src-nested-rule-locus"></a>
- [A rule locus that iterates two repeatable levels, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-nested-rule-locus)
<a id="src-computation-operand-scope"></a>
- [Which repeatable scopes a computation operand may sit in, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-computation-operand-scope)
<a id="src-date-range-bound-component-runtime"></a>
- [What a computed DateRange-endpoint component evaluates to, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-bound-component-runtime)
<a id="src-date-range-bound-component"></a>
- [The numeric component of a selected DateRange endpoint, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-bound-component)
<a id="src-date-range-yearless-locus"></a>
- [The rule-locus gate over unconfigured yearless DateRange carriers, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-yearless-locus)
<a id="src-date-range-rule-locus"></a>
- [The rule-locus gate over four DateRange condition carriers, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-rule-locus)
<a id="src-date-range-list-crossing"></a>
- [Direct-list DateRange `FirstFilledValue` gates and rendered crossing, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-list-crossing)
<a id="src-date-range-interpretation-first-filled"></a>
- [Direct-list DateRange `FirstFilledValue` across year interpretations, measured locally 2026-08-24](sources/temporal-and-message-probes.md#src-date-range-interpretation-first-filled)
<a id="src-date-range-interpretation-first-filled-star"></a>
- [Direct-star DateRange `FirstFilledValue` across year interpretations, measured locally 2026-08-24](sources/temporal-and-message-probes.md#src-date-range-interpretation-first-filled-star)
<a id="src-date-range-repeatable-first-filled"></a>
- [Sibling-star DateRange `FirstFilledValue` into exact repeatable targets, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-date-range-repeatable-first-filled)
<a id="src-datetime-repeatable-first-filled"></a>
- [Sibling-star DateTime `FirstFilledValue` into exact repeatable targets, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-datetime-repeatable-first-filled)
<a id="src-full-date-repeatable-first-filled"></a>
- [Checked sibling-star FULL Date target admission, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-full-date-repeatable-first-filled)
<a id="src-time-repeatable-first-filled"></a>
- [Sibling-star Time `FirstFilledValue` target admission and runtime, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-first-filled)
<a id="src-time-repeatable-constant-construction"></a>
- [Repeatable constant `Time(...)` construction result classification, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-constant-construction)
<a id="src-time-repeatable-number-components"></a>
- [Repeatable Number-backed `Time(...)` construction across root, enclosing, and leaf scopes, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-number-components)
<a id="src-time-repeatable-string-components"></a>
- [Repeatable digit-String-backed `Time(...)` construction across root, enclosing, and leaf scopes, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-string-components)
<a id="src-time-repeatable-direct-extractor-components"></a>
- [Repeatable direct-extractor `Time(...)` construction across root, enclosing, and leaf scopes, measured locally 2026-08-27](sources/repeatable-temporal-computation-probes.md#src-time-repeatable-direct-extractor-components)
<a id="src-datetime-component-sibling-parallel-refusal"></a>
- [Sibling-parallel refusal for DateTime component extractors, measured locally 2026-08-27](sources/temporal-and-message-probes.md#src-datetime-component-sibling-parallel-refusal)
<a id="src-date-range-unconfigured-interpretation-first-filled-star"></a>
- [Unconfigured interpreted DateRange declaration-order discriminator, corrected 2026-08-24](sources/temporal-and-message-probes.md#src-date-range-unconfigured-interpretation-first-filled-star)
<a id="src-date-range-unconfigured-bound"></a>
- [Unconfigured yearless bound extraction and its component-set consumer gates, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-unconfigured-bound)
<a id="src-date-range-interpretation-comparison"></a>
- [Equality across declared year interpretations, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-interpretation-comparison)
<a id="src-date-range-stored-comparison"></a>
- [Stored-versus-stored DateRange comparability and cross-spelling identity, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-stored-comparison)
<a id="src-date-range-interpretation-overlap-refusal"></a>
- [`interpretationOfYear` as an overlap operand and its placed-year calendar check, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-interpretation-overlap-refusal)
<a id="src-date-range-year-interpretation"></a>
- [Wrapping yearless ranges and `interpretationOfYear`, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-year-interpretation)
<a id="src-date-range-yearless-group-carrier"></a>
- [Yearless DateRange group carriers, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-yearless-group-carrier)
<a id="src-date-range-starred-yearless-overlap"></a>
- [Starred yearless DateRange overlap, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-starred-yearless-overlap)
<a id="src-date-range-plural-year-class"></a>
- [Plural DateRange overlap year class and fragment operands, measured locally 2026-08-23](sources/temporal-and-message-probes.md#src-date-range-plural-year-class)
<a id="src-2026-08-30-reconciliation"></a>
- [Reviewed 2026-08-30 a12-dmkits reconciliation, retraction, and instrument answers](sources/computation-placement-and-constant-probes.md#src-2026-08-30-reconciliation)
<a id="src-2026-08-29-reconciliation"></a>
- [Reviewed 2026-08-29 a12-dmkits reconciliation and correction batch](sources/computation-placement-and-constant-probes.md#src-2026-08-29-reconciliation)
<a id="src-date-range-direct-list-cross-group-sources"></a>
- [A direct-list `FirstFilledValue` places its sources freely](sources/computation-placement-and-constant-probes.md#src-date-range-direct-list-cross-group-sources)
<a id="src-starred-operand-message-polarity"></a>
- [A computation's message type follows what can still grow](sources/group-and-iteration-probes.md#src-starred-operand-message-polarity)
<a id="src-filled-field-count-nested-capacity"></a>
- [A group `NumberOfFilledFields` moves against declared slot capacity, not declared field count](sources/group-list-and-capacity-probes.md#src-filled-field-count-nested-capacity)
<a id="src-filled-field-count-deep-capacity"></a>
- [Slot capacity compounds through nested repetition levels and stops at the operand group](sources/group-list-and-capacity-probes.md#src-filled-field-count-deep-capacity)
<a id="src-group-count-list-extent"></a>
- [A group-count list's extent is its operand list, and a starred member breaks that](sources/group-list-and-capacity-probes.md#src-group-count-list-extent)

<a id="src-group-count-unavailability"></a>
- [A group error makes a filled-group count unknown only when that group has no admitted content](sources/group-list-and-capacity-probes.md#src-group-count-unavailability)

<a id="src-group-count-static-gates-both-arms"></a>
- [The group-count static gate table is the same on both arms](sources/group-list-and-capacity-probes.md#src-group-count-static-gates-both-arms)
<a id="src-group-count-gates-repeatable-scope"></a>
- [The group-count gate table survives a repeatable declaring group, and a filter refuses a group operand](sources/group-list-and-capacity-probes.md#src-group-count-gates-repeatable-scope)
<a id="src-fixed-group-repeatable-ancestor-carriers"></a>
- [Fixed child groups bind to the declaring repeatable row on every measured carrier](sources/group-list-and-capacity-probes.md#src-fixed-group-repeatable-ancestor-carriers)

<a id="src-repeatability-declaration-domain"></a>
- [A repeatable group always carries a finite maximum, and absence means nonrepeatable](sources/group-list-and-capacity-probes.md#src-repeatability-declaration-domain)
<a id="src-repeatability-domain-peer-measurement"></a>
- [The `repeatability` domain is `> 0` and `1` is admitted, measured by a12-dmkits](sources/inbound-group-operand-batches.md#src-repeatability-domain-peer-measurement)
<a id="src-erroneous-member-quantifier-undecidable"></a>
- [An erroneous member makes the quantifier undecidable rather than shrinking its list](sources/inbound-group-operand-batches.md#src-erroneous-member-quantifier-undecidable)
<a id="src-mandatory-information-narrowing"></a>
- [Mandatory-information derivation reads a 32-bit-narrowed threshold](sources/rule-set-meta-information.md#src-mandatory-information-narrowing)
<a id="src-mandatory-information-presence-matrix"></a>
- [Mandatory-information derivation separates field, root-only, and ignored rule shapes](sources/rule-set-meta-information.md#src-mandatory-information-presence-matrix)
<a id="src-mandatory-information-composition-matrix"></a>
- [Mandatory-information derivation distinguishes root-relative fields and finite dependency closure](sources/rule-set-meta-information.md#src-mandatory-information-composition-matrix)
<a id="src-mandatory-information-field-list-guards"></a>
- [Mandatory-information derivation distinguishes existential and universal filled-field guards](sources/rule-set-meta-information.md#src-mandatory-information-field-list-guards)
<a id="src-mandatory-information-distinct-count"></a>
- [Mandatory-information derivation preserves filled-count and distinct-count operator identity](sources/rule-set-meta-information.md#src-mandatory-information-distinct-count)
<a id="src-mandatory-information-info-severity"></a>
- [Mandatory-information derivation ignores INFO negative field rules](sources/rule-set-meta-information.md#src-mandatory-information-info-severity)

<a id="src-over-limit-computation-target"></a>
- [An over-limit row receives no computed value](sources/group-list-and-capacity-probes.md#src-over-limit-computation-target)
<a id="src-distinct-count-first-operand-class"></a>
- [`NumberOfDifferentValues` classifies by its first operand](sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)
<a id="src-capacity-consumer-sweep"></a>
- [The declared-capacity extent reaches the last four operand-stream consumers](sources/group-list-and-capacity-probes.md#src-capacity-consumer-sweep)
<a id="src-over-limit-finding-text"></a>
- [`zuGrosseZeile` renders no coordinate, and two over-limit groups report independently](sources/over-repetition-probes.md#src-over-limit-finding-text)
<a id="src-starred-group-count-computation"></a>
- [The computation arm counts a starred repeatable group's instantiated rows](sources/group-and-iteration-probes.md#src-starred-group-count-computation)
<a id="src-partial-coverage-group-operands"></a>
- [The count needs every operand field covered, where the presence predicates read what they can see](sources/group-list-and-capacity-probes.md#src-partial-coverage-group-operands)
<a id="src-starred-group-quantifier-capacity"></a>
- [The threshold quantifiers read the in-capacity extent, and an instantiated row is filled](sources/group-list-and-capacity-probes.md#src-starred-group-quantifier-capacity)
<a id="src-address-dialect-selector"></a>
- [An unbound repeatable level is what selects a message pointer's slash spelling](sources/message-and-pointer-probes.md#src-address-dialect-selector)
<a id="src-repeatable-descendant-group-count"></a>
- [A repeatable descendant makes its shell count structurally](sources/group-and-iteration-probes.md#src-repeatable-descendant-group-count)
<a id="src-deep-repeatable-descendant-group-count"></a>
- [Repetition depth does not bound a group-count operand's row constituent](sources/group-and-iteration-probes.md#src-deep-repeatable-descendant-group-count)
<a id="src-nested-star-bound-outer-level"></a>
- [A nested star answers from its own enclosing row](sources/group-and-iteration-probes.md#src-nested-star-bound-outer-level)
<a id="src-group-operand-over-limit-extent"></a>
- [A fixed group operand's extent excludes an over-limit row, and the count is zero rather than unknown](sources/group-and-iteration-probes.md#src-group-operand-over-limit-extent)
<a id="src-group-count-row-domains"></a>
- [The half-instantiated shell, the starred group over a repeatable descendant, and the unreachable row-domain discriminator](sources/group-and-iteration-probes.md#src-group-count-row-domains)
<a id="src-over-limit-finding-multiplicity"></a>
- [An over-limit row stamps every node the document writes beneath it](sources/over-repetition-probes.md#src-over-limit-finding-multiplicity)
<a id="src-nested-over-limit-attribution"></a>
- [An inner over-limit row is invisible beneath an outer one](sources/over-repetition-probes.md#src-nested-over-limit-attribution)
<a id="src-over-limit-absorption-depth"></a>
- [The absorption is transitive and suppresses the whole written subtree](sources/over-repetition-probes.md#src-over-limit-absorption-depth)
<a id="src-nested-descendant-group-count-invalid"></a>
- [A formally invalid nested descendant still fills its group](sources/group-and-iteration-probes.md#src-nested-descendant-group-count-invalid)
<a id="src-nested-descendant-group-count-runtime"></a>
- [A group-count operand reads its whole subtree](sources/group-and-iteration-probes.md#src-nested-descendant-group-count-runtime)
<a id="src-nested-descendant-group-count-admission"></a>
- [A fixed group-count operand admits nested descendants](sources/group-and-iteration-probes.md#src-nested-descendant-group-count-admission)
<a id="src-empty-declared-group"></a>
- [An empty declared group is kernel-valid](sources/group-and-iteration-probes.md#src-empty-declared-group)
<a id="src-multi-root-short-name-reach"></a>
- [A model may declare more than one root group, and the short-name tier spans them](sources/group-and-iteration-probes.md#src-multi-root-short-name-reach)
<a id="src-message-group-parameter"></a>
- [The rule-message group parameter `$#…$`](sources/message-and-pointer-probes.md#src-message-group-parameter)
<a id="src-message-group-parameter-resolution"></a>
- [How the rule-message group parameter resolves](sources/message-and-pointer-probes.md#src-message-group-parameter-resolution)
<a id="src-dmtool-2026-08-22-instrument-handback"></a>
- [Reviewed 2026-08-22 instrument handback and its two Kernel measurements](sources/temporal-and-message-probes.md#src-dmtool-2026-08-22-instrument-handback)
<a id="src-2026-08-23-reconciliation"></a>
- [Reviewed 2026-08-23 a12-dmkits reconciliation and correction batch](sources/temporal-and-message-probes.md#src-2026-08-23-reconciliation)
<a id="src-date-range-2026-08-19-reconciliation"></a>
- [Reviewed 2026-08-19 DateRange reconciliation and correction batch](sources/temporal-and-message-probes.md#src-date-range-2026-08-19-reconciliation)

### Group and iteration source checkpoints

Three shards carry these: locally measured probes split between [`group-and-iteration-probes.md`](sources/group-and-iteration-probes.md) and [`group-list-and-capacity-probes.md`](sources/group-list-and-capacity-probes.md), plus reconciled inbound batches in [`inbound-group-operand-batches.md`](sources/inbound-group-operand-batches.md). Each entry below links to the shard that owns it.

<a id="inbound-entity-list-group-operand-validator-cardinality-and-cleared-value-batch"></a>
- [Inbound entity-list group-operand, validator-cardinality, and cleared-value batch](sources/inbound-group-operand-batches.md#inbound-entity-list-group-operand-validator-cardinality-and-cleared-value-batch)
<a id="src-first-filled-additional-kind-computations"></a>
- [Direct one-star additional-kind `FirstFilledValue` computations](sources/group-and-iteration-probes.md#src-first-filled-additional-kind-computations)
<a id="src-first-filled-kind-computations"></a>
- [Direct one-star established-kind `FirstFilledValue` computations](sources/group-and-iteration-probes.md#src-first-filled-kind-computations)
<a id="src-current-repetition-root-condition"></a>
- [Nonrepeatable-root `CurrentRepetition` condition](sources/group-and-iteration-probes.md#src-current-repetition-root-condition)
<a id="src-current-repetition-repeatable-condition"></a>
- [Same-group repeatable `CurrentRepetition` validation](sources/group-and-iteration-probes.md#src-current-repetition-repeatable-condition)
<a id="src-current-repetition-computation-dependency"></a>
- [Computation `CurrentRepetition` structural dependency](sources/group-and-iteration-probes.md#src-current-repetition-computation-dependency)
<a id="src-group-list-rnu-admission-correction"></a>
- [Group-list and RNU admission correction](sources/group-list-and-capacity-probes.md#src-group-list-rnu-admission-correction)
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
- [Token group partial-validation runtime](sources/inbound-group-operand-batches.md#src-token-group-partial-runtime)
<a id="src-token-group-value-count-computation-capacity"></a>
- [Token group value-count computation capacity](sources/inbound-group-operand-batches.md#src-token-group-value-count-computation-capacity)
<a id="src-boolean-group-value-count-computation-capacity"></a>
- [Boolean/Confirm group value-count computation capacity](sources/inbound-group-operand-batches.md#src-boolean-group-value-count-computation-capacity)
<a id="src-false-boolean-group-value-count-computation-capacity"></a>
- [False Boolean-group value-count computation capacity](sources/inbound-group-operand-batches.md#src-false-boolean-group-value-count-computation-capacity)
<a id="src-boolean-group-value-count-computation-shape-matrix"></a>
- [Boolean-group value-count computation shape matrix](sources/inbound-group-operand-batches.md#src-boolean-group-value-count-computation-shape-matrix)
<a id="src-boolean-fixed-group-value-count-computation"></a>
- [Boolean fixed-group value-count computation](sources/inbound-group-operand-batches.md#src-boolean-fixed-group-value-count-computation)
<a id="src-boolean-confirm-constant-computation-targets"></a>
- [Boolean and Confirm constant computation targets](sources/inbound-group-operand-batches.md#src-boolean-confirm-constant-computation-targets)
<a id="src-token-value-count-group-runtime"></a>
- [Token group value-count runtime](sources/inbound-group-operand-batches.md#src-token-value-count-group-runtime)
<a id="src-token-value-count-fixed-group-admission"></a>
- [Token fixed-group value-count admission](sources/inbound-group-operand-batches.md#src-token-value-count-fixed-group-admission)
<a id="src-filled-field-group-runtime"></a>
- [Filled-field group-count runtime](sources/inbound-group-operand-batches.md#src-filled-field-group-runtime)
<a id="src-group-operand-capacity-consumer-sweep"></a>
- [Fixed-group over-limit extent across six carriers](sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep)
<a id="src-starred-group-operand-extent"></a>
- [Starred group operand extent and the malformed separator](sources/group-and-iteration-probes.md#src-starred-group-operand-extent)
<a id="src-starred-field-operand-extent"></a>
- [Starred field operand extent across the extrema, distinct count, and value count](sources/group-and-iteration-probes.md#src-starred-field-operand-extent)
<a id="src-token-starred-field-capacity"></a>
- [Plain starred String value-count capacity](sources/group-and-iteration-probes.md#src-token-starred-field-capacity)
<a id="src-boolean-starred-field-capacity"></a>
- [Plain starred Boolean value-count capacity](sources/group-and-iteration-probes.md#src-boolean-starred-field-capacity)
<a id="src-confirm-starred-field-capacity"></a>
- [Plain starred Confirm value-count capacity and movement](sources/group-and-iteration-probes.md#src-confirm-starred-field-capacity)
<a id="src-filtered-starred-field-capacity"></a>
- [Filtered starred String, Boolean, and Confirm value-count capacity](sources/group-and-iteration-probes.md#src-filtered-starred-field-capacity)
<a id="src-capacity-projection-computation-arm"></a>
- [Declared-capacity projection on the computation arm](sources/group-and-iteration-probes.md#src-capacity-projection-computation-arm)
<a id="src-starred-field-operand-peer-reproduction"></a>
- [Starred field operand, empty-domain zero, and the operand-scoped over-repetition channel, reproduced by a12-dmkits](sources/inbound-group-operand-batches.md#src-starred-field-operand-peer-reproduction)
<a id="src-star-over-repetition-domain"></a>
- [Over-repetition exclusion from starred numeric domains](sources/over-repetition-probes.md#src-star-over-repetition-domain)
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
<a id="src-group-runtime-and-reference"></a>
- [Group runtime and reference correction](sources/inbound-group-operand-batches.md#src-group-runtime-and-reference)
<a id="src-group-first-filled-runtime-order"></a>
- [Fixed-group first-filled runtime order](sources/inbound-group-operand-batches.md#src-group-first-filled-runtime-order)
<a id="src-star-group-first-filled-runtime-order"></a>
- [Starred-group first-filled runtime order](sources/inbound-group-operand-batches.md#src-star-group-first-filled-runtime-order)
<a id="src-sum-of-products-owning-group"></a>
- [`SumOfProducts` owning-group and diagnostic matrix, reviewed inbound 2026-08-29](sources/inbound-group-operand-batches.md#src-sum-of-products-owning-group)
<a id="src-count-partial-extent"></a>
- [Direct starred count partial-extent checkpoint](sources/inbound-group-operand-batches.md#src-count-partial-extent)
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
- [Fixed target owns cross-group computation scope](sources/computation-placement-and-constant-probes.md#src-fixed-computation-target-scope)
<a id="src-cross-group-computation-authoring-block"></a>
- [Cross-group computation placement is unauthorable through the structured verbs](sources/computation-placement-and-constant-probes.md#src-cross-group-computation-authoring-block)
<a id="src-computation-declaring-group-gate"></a>
- [Computation declaring group: containment gate and target-owned execution](sources/computation-placement-and-constant-probes.md#src-computation-declaring-group-gate)
<a id="src-cross-group-repeatable-constant-target"></a>
- [A repeatable target declared cross-group iterates from its own scope](sources/computation-placement-and-constant-probes.md#src-cross-group-repeatable-constant-target)
<a id="src-repeatable-string-constant-target-check"></a>
- [A String constant its target rejects keeps the exact attempted value](sources/computation-placement-and-constant-probes.md#src-repeatable-string-constant-target-check)
<a id="src-repeatable-number-constant-target-check"></a>
- [A Number constant: scale refuses at authoring, range errors per row](sources/computation-placement-and-constant-probes.md#src-repeatable-number-constant-target-check)
<a id="src-repeatable-number-constant-scale-rendering"></a>
- [A Number constant's scale is read twice, differently: the gate keeps trailing zeros, the store strips them and pads](sources/computation-placement-and-constant-probes.md#src-repeatable-number-constant-scale-rendering)

<a id="src-date-constant-target-formatting"></a>
- [A Date constant is classified by its own spelling and stored in the target's format](sources/computation-placement-and-constant-probes.md#src-date-constant-target-formatting)

<a id="src-date-constant-pre-1900-target"></a>
- [A Date constant reaches the target's opt-in pre-1900 policy after rendering](sources/computation-placement-and-constant-probes.md#src-date-constant-pre-1900-target)

<a id="src-constant-literal-family-gate"></a>
- [A bare constant's admission is gated by the target's declared format string, never its kind](sources/computation-placement-and-constant-probes.md#src-constant-literal-family-gate)
<a id="src-temporal-constant-literal-composition"></a>
- [The temporal literal vocabulary composes, and the Base Year gate reads year disagreement](sources/computation-placement-and-constant-probes.md#src-temporal-constant-literal-composition)

<a id="src-datetime-constant-zone-split"></a>
- [A DateTime constant is checked against two different zones at two different phases](sources/computation-placement-and-constant-probes.md#src-datetime-constant-zone-split)

<a id="src-component-omitting-date-formats"></a>
- [A component-omitting date target needs every component its format names, and the Base Year supplies the year](sources/computation-placement-and-constant-probes.md#src-component-omitting-date-formats)

<a id="src-base-year-yearless-store"></a>
- [A declared Base Year gates a yearless target's authoring and contributes nothing to its store](sources/computation-placement-and-constant-probes.md#src-base-year-yearless-store)
<a id="src-fixed-target-star-placement"></a>
- [Fixed computation target under a star operand: no placement gate](sources/computation-placement-and-constant-probes.md#src-fixed-target-star-placement)
<a id="src-unsuppressed-assignment-scale-reach"></a>
- [The unsuppressed assignment-scale overflow has no authored witness](sources/computation-placement-and-constant-probes.md#src-unsuppressed-assignment-scale-reach)
<a id="src-repeatable-string-application"></a>
- [Finite one- and two-level String separate-destination application, measured locally 2026-08-26](sources/evaluation-and-application-routes.md#src-repeatable-string-application)
<a id="src-repeatable-number-aggregate-cascade"></a>
- [Repeatable Number producer and aggregate cascade](sources/evaluation-and-application-routes.md#src-repeatable-number-aggregate-cascade)
<a id="src-repeatable-numeric-wrappers-extrema"></a>
- [Repeatable numeric wrappers and extrema](sources/evaluation-and-application-routes.md#src-repeatable-numeric-wrappers-extrema)
<a id="src-operation-valued-extrema"></a>
- [Operation-valued extrema](sources/evaluation-and-application-routes.md#src-operation-valued-extrema)
<a id="src-aggregate-repeatable-suffixes"></a>
- [Aggregate-to-repeatable suffixes](sources/evaluation-and-application-routes.md#src-aggregate-repeatable-suffixes)
<a id="src-nested-current-repetition-cascades"></a>
- [Nested `CurrentRepetition` cascades](sources/evaluation-and-application-routes.md#src-nested-current-repetition-cascades)
<a id="src-scalar-mixed-consumer-first-dependency-order"></a>
- [Consumer-first mixed scalar dependency order, measured locally 2026-08-25](sources/evaluation-and-application-routes.md#src-scalar-mixed-consumer-first-dependency-order)
<a id="src-scalar-mixed-reverse-authored-triple"></a>
- [Reverse-authored mixed scalar triple, measured locally 2026-09-01](sources/evaluation-and-application-routes.md#src-scalar-mixed-reverse-authored-triple)
<a id="src-numeric-extremum-call-boundary"></a>
- [Numeric extremum call boundary](sources/evaluation-and-application-routes.md#src-numeric-extremum-call-boundary)
<a id="src-custom-validity-route"></a>
- [Custom validity source route](sources/evaluation-and-application-routes.md#src-custom-validity-route)
<a id="src-field-values-not-unique-route"></a>
- [`FieldValuesNotUnique` source route](sources/evaluation-and-application-routes.md#src-field-values-not-unique-route)
<a id="src-fieldless-numeric-computation"></a>
- [Fieldless repeatable numeric computation](sources/evaluation-and-application-routes.md#src-fieldless-numeric-computation)
<a id="src-addressed-numeric-binary"></a>
- [Addressed numeric binary computation](sources/evaluation-and-application-routes.md#src-addressed-numeric-binary)
<a id="src-number-repeatable-first-filled"></a>
- [Sibling-star Number `FirstFilledValue` target admission and ordered runtime, measured locally 2026-08-27](sources/evaluation-and-application-routes.md#src-number-repeatable-first-filled)
<a id="src-computed-target-reference"></a>
- [Computed-target reference source route](sources/evaluation-and-application-routes.md#src-computed-target-reference)
<a id="src-temporal-construction-route"></a>
- [Temporal construction and calendar profiles](sources/temporal-and-message-probes.md#src-temporal-construction-route)
<a id="src-message-construction-route"></a>
- [Message construction](sources/message-and-pointer-probes.md#src-message-construction-route)

### Inbound provenance checkpoints


## Question-to-locus index

The clause map gets a reader into the right subsystem; this table gets a working agent to the decisive mechanism. Search the question or symbol before starting a new audit. “Decides” names the claim class that the locus can actually establish; cross-layer behavior still follows the composition rule above.

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
| How is a custom condition invoked? | `ApplicationCondition.st`, `MainValidatorController.applikationsBedingung`, `CustomConditionWrapper`, `ICustomCondition` | Generated invocation and host callback boundary; registration/failure policy requires the service/model path |

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

Update this owner only when an authoritative locus, reusable drill route, source tension, or inbound provenance checkpoint changes. Edit the matching shard record and change this hub only when navigation or its stable entry set changes. Do not append Lean implementation status, current exclusions, capsule summaries, theorem/test counts, or a chronological research narrative. Replace superseded source guidance and rely on Git for the old review path.
