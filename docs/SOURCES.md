# Authoritative sources and drill routes

<a id="authoritative-sources--how-to-drill"></a>
<a id="authoritative-sources-how-to-drill"></a>

This is the repository’s provenance and source-navigation hub. It maps semantic questions to the authoritative kernel layer and to maintained a12-dmkits knowledge. It is not a second specification, findings ledger, implementation map, evidence inventory, or review history.

Authority order is **[`../../a12-kernel`](../../a12-kernel) → project-owned [`../spec/`](../spec/) and Lean theory → [a12-dmkits](../../a12-rulekit)**. The real kernel is the behavioral oracle. The spec and Lean theory are this project’s working semantics-of-record. a12-dmkits is a peer clean-room implementation, source of maintained kernel-executing differentials, and knowledge corpus.

All kernel source routes below target kernel **30.8.1**, inspected at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. Read source to learn behavior; never link, call, ship, or transcribe it.

## Query contract

Start from the relevant [`spec/` clause](../spec/SEMANTICS-MAP.md), then:

1. identify the claim class with the engine routing rule;
2. use the clause table for the subsystem, then the question-to-locus index for the exact decisive class, template, backing bean, method, or service;
3. follow a12-dmkits’ guard-checked [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) for its exhaustive prose/test/corpus inventory;
4. consult this file’s focused packets only for cross-layer mechanisms not answered by one locus.

Search with `rg -n '^### |Semantic question|OperatorName|RuntimeHelper|SPEC-' docs/SOURCES.md`. Add a route here only when it is reusable by later work. A one-capsule source narrative belongs in working context and Git history, while a durable surprising mechanism belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).

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

## Focused cross-layer packets

### Immutable document and checked-input construction

[`DocumentV2`](../../a12-kernel/kernel-md/kernel-md-document-v2/src/main/java/com/mgmtp/a12/kernel/md/document/apiV2/immutable/DocumentV2.java), `GroupInstanceV2`, `FieldInstanceV2`, and `RepetitionsV2` own physical topology and present instances independently of the model. `DocumentAbstractRtService` selects the exact model and passes a separate [`DocumentProcessingConfig`](../../a12-kernel/kernel-md/kernel-md-runtime-api/src/main/java/com/mgmtp/a12/kernel/md/rt/api/DocumentProcessingConfig.java). `ValidationData` projects the immutable document into runtime checking; `CheckCommand.formalePruefung`, `FormalChecker.checkIndices`, and `ValidationCache` establish address-formal ordering and the later value cache. The cache omits ordinary empty cells, so it cannot substitute for the immutable input when placement, group content, requiredness, display, or application is observed.

Generated required/index findings are later stages. `AutogeneratedRulesService`, `ValidationCommand.processInternalVV`, and `MainValidatorController.preliminaryError` own generated mandatory/uniqueness checks and exact invalid marking. Partial validation rebuilds a relevance-selected view rather than filtering a full result after evaluation. Computation’s eager operand prepass is another selected view; it does not redefine the checked document.

Scalar formal-read construction has two reachability-sensitive routes. `IBooleanType`/`IConfirmType` mark their alternative display tokens `@NotInD`; `TypeConverter.convertBoolean`/`convertConfirm` consult them only when `considerNotInD` is true, while A12's supported `ExternalDocumentModelService` construction takes the default false route. `FormatDefinitionJaNein` and `FormatDefinitionJa` therefore receive the fixed lowercase tokens and own the case-sensitive formal codes; neighboring ingress conversion does not change that validation contract. For Number, `ValidationData.getValue` returns a stored `String` unchanged but sends a non-String basic value through `FormatDefinitionZahl.convertFromBasicType`, which strips decimal trailing zeros, reapplies the declared minimum fractional scale, and renders plain text. Every evaluation consumer, including `RuntimeController.feldWertAlsString`, reads that selected text. `IndexFieldCache.normalizeValue` separately converts Number keys for numeric semantic-index identity, and `CheckSemanticIndexImpl` format-checks each literal before code generation.

Stored temporal conversion is non-lenient. `FieldValueConverter` delegates Date, Time, DateTime, and DateRange conversion through the declared formats; `ValidationDateParser` disables leniency. `DocumentJsonAndXmlDeserializationInfoImpl` retains a nonempty value that fails conversion as its exact stored text rather than dropping the placement. These are in-memory input semantics; JSON mapper syntax and permissiveness remain outside the evaluation account.

### Ordered validation and partial rule execution

`rulesDir/CodeGenRuleDefinition.st` in Java, Groovy, and JavaScript-VK owns the filter-bearing partial-rule early return before iteration and condition evaluation. The enclosing `CodeGenRules.st` mainly orders preliminary checking and delegates rule bodies; it is not the source for that skip.

`CodeGenParseTreeHelper.FilterConditionVisitor` discovers filters statically. `ValidationCommand.processTVInternal`, relevance caches, `EbenenIterator`, and the relevant runtime controller methods establish actual-row iteration, per-cell relevance, aggregate extent, and exact error placement. Use a generated program or maintained differential when a claim composes those layers.

### Computation definition, execution, and result

`CalculationUtils.expandCommonPrecondition` distributes a common guard. `CalculationDependencies` groups computations per target and builds the dependency order. `CodeGeneratorParameters`, `CodeGeneratorService`, and `CodeGeneratorParametersWrapper` preserve the supplied computation-information list into grouping; the producer of that original list is not fully traced, so the safe claim is supplied order, not generic “document order.”

`CodeGenCalculatedFieldBuilder` flattens all rows for one target into one generated method. [`CodeGenCalculationAlternative.st`](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/resources/internal/templates/validation/java/calcDir/CodeGenCalculationAlternative.st) makes false guards fall through and makes a selected, poisoned, or failing row end the scan. The continuation after a selected operation is unconditional, including when storage produces no value. Generated validation is separate: `ValidationModelConverter` and `ComputationAlternativesJoiner` retain every relevant mismatch rather than reusing first selection.

`CodeGenCalcBuilder`, `CalculationDependencies`, `TopologicalSortHelper`, and [`CodeGenCalc.st`](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/resources/internal/templates/validation/java/calcDir/CodeGenCalc.st) establish codegen-time dependency ordering, deterministic independent tie-breaking, and cycle rejection. Runtime adds no scheduler.

`CalculationCommand` owns stripping, eager formal-operand checking, and computation orchestration. `CalculationCache` owns read-driven poison and the calculated-value overlay. Value/presence reads throw only when reached; generated `And`/`Or` can hide an invalid suffix. Calculation-field poison marks the target invalid without adding a message.

[`DocumentComputationResultImpl`](../../a12-kernel/kernel-md/kernel-md-runtime-service/src/main/java/com/mgmtp/a12/kernel/md/rt/a12internal/service/DocumentComputationResultImpl.java) owns the five public projections, exact pointer-based message partition, source-relative change, `noErrorOccurred`, and V2 application order. A value-less local target error has no computed instance to absorb its message, so it remains in the residual channel; inherited poison emits no message. `applyTo` processes cleared, with-errors, and with-changes against a caller-supplied document; validation remains a separate call.

Repeatable computation additionally uses `CalculatedFieldIterationLimitCreator`, `CalculationCache.getIterationValuesForGroups`, `markFieldsUsingInvalidIndexGroupsAsIncorrectlyCalculated`, `GroupFillCache.getExistingFieldInstances`, and `CodeGenCalculatedField.st`. These establish static route participation, suppression by invalid index columns, exact target-instance overlays, and locus-dependent coarser invalid marking. Hash-backed internal iteration order is not a public result-order contract.

### Temporal construction and calendar profiles

Date/Time component authoring is distributed across `CheckBaseDateConstructionImpl`, `CheckDatumKonstruktImpl`, `CheckDatumExtractOpImpl`, `CheckDatumAngabeImpl`, the grammar/parse-tree constructors, and `CodeGenCreator.createDatumParameter`. The generated operation templates preserve source and component order; runtime `RuntimeController` supplies field conversion, `BaseYear`, `Today`, `Now`, construction, and component projection.

Computed Time closes through one narrower route. `CheckTimeKonstruktImpl` and `TimeConstructionOperationImpl` assign complete `HH:mm:ss`; the Java, Groovy, and JavaScript [`TimeConstructionOperation.st`](../../a12-kernel/kernel-tool/kernel-core-codegen-condition/src/main/resources/internal/templates/validation/java/operationsDir/TimeConstructionOperation.st) dialects all call `RuntimeController.constructTime` with hour/minute/second in authored order. `DateUtil.createTime` validates the clock on 1970-01-01 in the model zone as a runtime transport value. [`CodeGenCalculationAlternative.st`](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/resources/internal/templates/validation/java/calcDir/CodeGenCalculationAlternative.st) then routes the resulting `VkDate` to `CalculationController.handleBerechnetenWert`; that handler renders through the target `FormatDefinitionDatum`, applies only the basic target check, and stores the exact `HH:mm:ss` string. The parser rejects any other Time field format, so a real constructed clock has no reachable target-local rejection. The transport date and zone must not become Time identity.

`DateUtil` owns strict fresh local-label construction under the model zone. `CheckDatumAddOpImpl` admits DateTime only for `AddDays` and rejects it for `AddMonths`/`AddYears`. [`DateAddOperation.st`](../../a12-kernel/kernel-tool/kernel-core-codegen-condition/src/main/resources/internal/templates/validation/java/operationsDir/DateAddOperation.st), its backing bean, and `RuntimeMethodNameFactory` preserve source-then-signed-amount order into `RuntimeController`; `BedingungsOperatorHelper` then owns the unit-specific `GregorianCalendar` mutation and completed-period/day differences. The recursive date-operand grammar and checkers admit a generated Add result as the operand of another Add or Difference, and all three template dialects inline that inner call. The outer runtime helper therefore receives the inner `VkDate.getDate()` exact instant and constructs its next calendar from that value; no rendered label or source text intervenes. Direct Date comparison provides an independent observer: `BedingungsOperatorHelper.vergleicheDATUM` delegates equality and inequality to the exact underlying `java.util.Date` instant, while a12-dmkits' converter separately supports a left-hand Date shift and a constructed-Date operand. Their combined authorability still requires kernel measurement before it is stated. `getDatumsDiff` independently ORs `isNichtAngegeben` from both `VkDate` operands, including value-carrying shift results, into both numeric fillability directions. Fresh construction and calendar addition must not be merged, and calendar units must not share an inferred overlap selector. `Calendar.DAY_OF_MONTH` carries the source instant's offset into the nominal target, preserves the millisecond field, and re-fits to the actual target offset only when the re-fit preserves the target civil date; travel direction is not the discriminator. Adjacent ±1-day probes do not separate those accounts because their source offset is correlated with direction. `addiereMonate` and `addiereJahre` instead use sign-independent compute-time resolution, normalizing gaps to the post-gap label; the latter also applies both February-28 corrections, and the leap-to-nonleap branch clears the entire clock. `getDifferenzInMonaten` seeds `12 × getDifferenzInJahren`, tests each increasing candidate through a fresh `addiereMonate` copy, and returns the predecessor of the first overshoot; it must not be reduced to one final year/month-coordinate landing because an intermediate gap normalization can already pass the endpoint. For example, `1916-03-30T23:30 → 1916-05-01T00:00` returns zero months when the fresh one-month landing normalizes to `00:30` and already overshoots. The result is also not `12 × completed years`. `getDifferenzInJahren` calls that same year helper before `DifferenceInDays` makes its `365 × years` day jump, after which each day landing carries the offset of its own current instant. Direct OpenJDK 21 controls over the pinned Berlin profile separate long-range overlap, both gap directions, date-preserving fallback, millisecond retention, month/year sign independence, the `369`-day day-mechanism composite, and the `7670`-versus-`7671` long spring-gap year qualifier. A short overlap placement self-corrects through the residual day loop and is not evidence for the year resolver. Audit each field mutation independently rather than extrapolating from sign or an adjacent transition.

The kernel accepts a wider legal zone-id domain than the current Lean profile. UTC/GMT and the pinned full historical `Europe/Berlin` profile are established local capabilities; general zone dispatch remains a separate source and representation question.

### Message construction

Validation messages are rendered before public result assembly. `FehlerHandler` selects locale resources and `CheckCommand.ersetzeFeldParameter` performs the computation-target field token replacement. Authored `$Field$`/`$Field.value$` template handling is a different syntax and must not be reused for generated target text.

Computation produces one formal-message stream. `DocumentComputationResultImpl` partitions it solely by exact error pointer against nonempty computed instances. `PartiallyKnownDocumentMultiPointer` admits concrete coordinates plus wildcard and unknown; `CellAddr` alone cannot represent the full message-pointer domain. Payload text, code, and locale do not affect partition membership.

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

## Inbound provenance checkpoints

The detailed review chronology is recoverable from Git. These consolidated checkpoints retain exact reviewed routes without an outbound feedback loop. Historical identifiers `27afb555aae29d3acd4ed04e3aea4772ae85505a` and `45d24b73549124bf7da342a1ee19401408438fc6` no longer resolve at reviewed a12-dmkits checkpoint `5093cfb8a500a1093fce80520b64d7b1a02641d5`; they remain receipt history rather than current drill routes. The [ledger receipt-continuity note](A12-DMKITS-SPEC-SYNC-LEDGER.md#receipt-continuity) owns the complete measured list and avoids inferring replacement mappings.

| Reviewed a12-dmkits revision | Inbound scope |
|---|---|
| `a8b86ff6` | last complete inbound spec audit, including the initial model-zone/DST corrections and `IF128` modern-Berlin slice |
| `53507298b3ca8dee4a73d851ecc3ca5f5e6b70ba` | observation-anchor policy, star/RNU legality, decimal storage, pattern admission, legacy zone history |
| `71775c9905b057831253348c31ce39e321e61889` | numeric arithmetic, tolerance, Date construction, calendar steps, reason propagation |
| `20230e403fa085c782534025f890669a975999a8` | numeric aggregate order/missingness and message display-policy corrections |
| `27afb555aae29d3acd4ed04e3aea4772ae85505a` | nested wrappers, star relevance/value-list extent, and related maintained controls |
| `83dd514f9283b9f62dbe6ee6f238e5c67a00e9c6` | aggregate uncertainty and corrected `FirstFilledValue` no-row behavior |
| `29b3ef53` and `dda6ba01` | engine-routing corrections plus engaged condition-line and calculation-closure split locks |
| `ee2f5d84` | consolidated host-conversion/static-legality review; supersedes the temporary 2026-07-25 drafts |
| `45d24b73549124bf7da342a1ee19401408438fc6` | RNU `@From` reference-boundary lock |
| `d2755319` | computation result-channel laws, including value-less target errors in the residual channel |
| `2f7cb8526bdda21bee5fb5a2c3eb1ea310f023f3` | consolidated scalar codec-boundary and declared-token reachability review, incorporating the corrections at `40fca1dadb00f08716069fffeaa39046c2d43f5f`, `ff1c85eb8d48c323e261b2ed336f2d4bc61d362a`, and `c4c16399e021a5080e4192bf190e2629b5a8d0f9` |
| `422dda2626cea8689935c87ea380a17bcd15cdfe` | Date-construction validity, hybrid-calendar, and component-projection review |
| `11526d9cc6d522add97494f60e7b4389131b8f1f` | Java-compatible Date/DateTime shift-amount narrowing, narrow-before-unit multiplication, and neighboring amount-result controls |
| `3c27df48e3aae20372e0db3a69197470036ccaa6` | corrected `ValueAsDate` placement matrix and initial nested runtime compositions |
| `976474a4c70f4acdf6c7080b0d4a4ef4bf1495b3` | route-complete `ValueAsDate` nested-placement evidence across kernel admission, dynamic Groovy, static Java, JVM, and Node |
| `b6fa6eb82678081b40594ab3c33ededac31f5a6e` | repeated-star group-list occurrence preservation and the zero-row polarity correction |
| `0005740c60f1db558cdcb9ad54df11b997302ffe` | exact static `HH:mm:ss` literal gate and initial partial-Date DateTime context witness |
| `751715fff53006bd47c65d2596395e13664ade1a` | Berlin/UTC dual-kernel and multiplatform separation of the Time literal's transport carrier from its decoded clock |
| `e32d1a0c3fe5d89c2f3ada4a426fdd202b127af4` | JVM/Node partial-Date DateTime composition completing the Time-literal acceptance routes |
| `4ebe84fc5e9a342c042e4b0f488f416a6e7771e1` | same-target computation root correction and dual-kernel/JVM/Node separation of selected-empty termination from false-guard fall-through |
| `5716a964794e7b6e2e102ef56d898c5524f1d16a` | partial calendar-field reconciliation: source-instant day landing and the dual-kernel/interpreter 369-day composite; month/year, millisecond, February-clear, and constructed-Date exact-instant peer evidence remains open |
| `17f95bcc7f0bd86b44413f1f41c5d2d351d84951` | sign-independent year-field landing and the dual-kernel 7670 versus pre-fix interpreter 7671 long spring-gap separator; month, millisecond, February-clear, and constructed-Date exact-instant peer evidence remains open |
| `8529c7200d1b5cdcd1ef7ba4364e905d73d4270b` | measured Time arities, wider Date precisions, and Date/Time component declaration gates recorded under a12-dmkits `IG105`–`IG107` and `DG26`–`DG27` |
| `5093cfb8a500a1093fce80520b64d7b1a02641d5` | handback checkpoint retaining the measured constant, extractor, and `TimeFromDateTime` static matrices under a12-dmkits `IG108` |

Additional exact checkpoints retained from the pre-consolidation drill map:

| Reviewed a12-dmkits revision | Narrow provenance retained |
|---|---|
| `f753a652` | generated Java/Groovy template-diff measurement and its pass-through blind spot |
| `5469c168`, `cd33d09e` | codegen backing-bean count and the anchored `/build/` search-filter correction preceding `29b3ef53` |
| `30bdce600fad00ef68a68f64fadace3146c0e54a` | `RuleGroup` declaring-group and group-presence behavior (`IF63`) |
| `a002c66aee25f55fde98d521b188654f9b95e26f` | validation/computation field-fill scans and filtered formal-invalidity traversal |
| `0f2a5687822797ed7b4f897b0320793ae22eb7b6` | `RangeAsString`/`RangeAsNumber` selection and fallback behavior |
| `793a6308332097b1dd4001693a06a48265a5dd05` | `FieldValueAsNumber` clean-room evaluation route |
| `553f447e2bf26d4f5d079135a4871f5e3d44166c`, `0093fc860f85b24ce4aede03c817aee1e151553b`, `0ccaf010bafe3d811443d8459c9d48fcacfcaf6f` | ordinary String formal checking, CRLF normalization, and computed-target checking |
| `7eaf1f82a26d03e2c183af129b229b9fdc621841`, `e57c29a704cd66d54630119f3506abdc5d1b8a75`, `2a940b961ba6237ebdeaafc2c2659692ae2c1cfe`, `38b1e18deb605b9698dca3f2ff32f7e2cac42d8f`, `a3a8f407cb3a280a811b783259e5f05475c12f4c`, `2abe3ceddb20a60102d9576a6d15e439aa7b6c88` | temporal typed authoring, sub-day shifts, computed extraction, model-zone exactness, dynamic `Now`, and the `IF95` component-source correction |
| `b9964c5242ac6311bfb8a6c6ec806d416bfd8be4` | filtered-iteration authoring gates and outer-correlation boundaries |
| `cdf79872`, `5212afabb6f8dad08fa96a818944b3b2e753bef3`, `e6f88c72754b46d0d99f0d2bc46c9c64bf4cda98` | earlier full-spec checkpoint, focused pattern/Berlin follow-up, and scalar membership synchronization |
| `dde8ce79` → `0e3ce991`, `bae06439` → `0b93e7ff`, `126d6672` → `c22c04c1`, `3fc5e979` → `db308369`, `43824168` → `74354d35` | patch-identical rebases of accepted temporal/power receipts; immutable original receipt hashes remain authoritative |
| `a1e39e18e4a74276da73b5a665d30521dcd99563`, `40fca1dadb00f08716069fffeaa39046c2d43f5f` | fixed lowercase Boolean/Confirm formal tokens, exact error codes, and the measured refutation of declared `@NotInD` token reachability |
| `43f8e5f460a2fddd8fbcfa58bdcb3f3f0f87e203`, `ff1c85eb8d48c323e261b2ed336f2d4bc61d362a`, `c4c16399e021a5080e4192bf190e2629b5a8d0f9` | decimal-valued versus String-valued Number formal-read regimes, length-bound and `FieldValueAsString` separators, and the executed refutation of unconditional re-rendering |
| `4b144f89be51a14f8facdff5ee81b590e5294fb5`, `2f7cb8526bdda21bee5fb5a2c3eb1ea310f023f3` | exact decimal transport host obligation plus malformed, leading-zero, Boolean, and temporal codec boundaries; wire-format mechanics remain excluded |

Accepted and pending locally originated changes remain in [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](A12-DMKITS-SPEC-SYNC-LEDGER.md). A reviewed inbound correction is recorded here and in the canonical spec; it does not create a new outbound entry.

## Maintenance rule

Update this file only when an authoritative locus, reusable drill route, source tension, or inbound provenance checkpoint changes. Do not append Lean implementation status, current exclusions, capsule summaries, theorem/test counts, or a chronological research narrative. Replace superseded source guidance and rely on Git for the old review path.
