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

### How far to trust a 40-character revision receipt

**A revision citation certifies what was read when it was written, not that it still resolves.** Measured 2026-09-06: of 426 distinct 40-hex citations across `docs/` and `spec/`, **176 resolve in no local checkout**. Restricted to the live provenance owners — this file, `EVIDENCE.md`, the current ledger, and the `sources/` shards — **182 citations resolve at 80%**. The remaining dead ones concentrate in `archived/`, `LEAN-FORMALIZATION.md` and `PRODUCTION-RELEASE.md`, where they name frozen history or external repositories such as Cedar and Lean that no local checkout is expected to hold. Peer history is rewritten upstream and this repository's early history was rewritten too, so decay is the normal condition of an old receipt rather than evidence of a fabricated one.

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

**What the CLI *does* reach is the static consistency oracle, and that is a first-class local route.** `model check`, `workspace check`, `rule check`, and computation dry-run validation call the real kernel's `checkConsistency` and can therefore support a static `KERNEL_CONFIRMED` claim, with the kernel message surfaced as the diagnostic summary and the extracted `MVK_*` as its code. So a **static-legality** question, such as which diagnostic class an illegal model draws, whether a gate reads the whole operand list, or whether a spelling is admitted, is measurable here and does not belong upstream.

**The CLI's own fail-fast spec validation pre-empts kernel declaration gates, and then the route measures the tool.** Confirmed 2026-08-29 on two independent gates.

**Partly resolved the same day.** From a12-dmkits `01bc94279f0aee06fd8d9ccfad2e116354aa409e` these refusals carry the standard `rejected` envelope with `RK_INVALID_VALUE` and `source: PRECHECK`, so the layer is machine-readable, and the messages no longer attribute a local refusal to the kernel. The preflight itself stays, and `model check` over a hand-edited **copy** of a model reaches the kernel's own verdict ([reconciliation](#src-2026-08-29-reconciliation)). From the [2026-08-30 handback](#src-2026-08-30-reconciliation) the peer's own skill rule scopes rather than forbids that route: hand-writing a shape into a copy is measurement and never authoring, and the copy is never persisted from or kept.

The originating observation, before the envelope fix: `field add` refused `maxFractionalDigits` above 14 with stderr *"invalid field spec: maxFractionalDigits must be ≤ 14 (the kernel's cap)"*, and refused an Enumeration category whose value list is shorter, longer, or empty against its enum's values, both exiting 2 with **no envelope at all** while attributing the rule to the kernel. That is how such a row becomes a false attribution, and it is why neither the kernel's `fieldScaleCap` gate nor its category-alignment gate is reachable through the `field add` route itself.

One limit on the replacement envelope: `RK_INVALID_VALUE` with `source: PRECHECK` does not discriminate **which** local gate refused, since the schema gate emits the same pair.

The tell is the envelope, not the message: a kernel verdict carries `verification: KERNEL_CONFIRMED` and an `MVK_*` diagnostic, while a front-end refusal carries neither and writes plain stderr. Read it before attributing any refusal. **It really is the pair, and neither field attributes on its own** — measured at a12-dmkits `041346095`, after this project asserted the opposite and was corrected.

**The `MVK_*` code itself is derived, not reported, and every claim phrased as "the Kernel reports `MVK_X`" is one layer off.** The kernel's `Notification` carries a severity and a message and **no code field at all**; a12-dmkits extracts the code from the message's terminal bracketed key, so what this route hands back is that extraction ([inbound](#inbound-2026-09-06b)).

The codes stay usable as refusal-class identities, because the bracketed key is the kernel's own identifier inside its own message — but the accurate phrasing is that the kernel's message *carries* the key, not that the kernel reports a code, and a claim about the code as an **object** — its form, its presence, its absence — is a claim about the extraction, while a claim about its *identity* is not, because `MVKErrorLookup` is what places the key in the message and does so for every key. That distinction is not pedantic: a peer finding stood from June to 2026-09-06 asserting a code-shape quirk that was only ever a property of the extractor, and it survived because it was written as though it were the kernel's.

`source: KERNEL` reaches a **codeless** deserialize-tier refusal, and an `MVK_*` code rides `source: PRECHECK` on eleven client-side codes that rulekit's typed builders mint deliberately, so an author sees the class the kernel would name. Only both together resolve to a kernel notification, and `verification` is weaker than either: the DSL-bearing authoring verbs asserted it unconditionally before `842ef01a6` ([reconciliation](#src-2026-08-30-reconciliation)). Treat every **declaration-shape** claim whose gate the CLI duplicates as not re-dischargeable here until an escape hatch exists, and note that this affects re-verification only: an accepted declaration still reaches the kernel's own oracle normally.

The reusable provenance route is `scripts/prepare-dmtool-source.sh`: it accepts only the checkout's exact clean HEAD, reuses or rebuilds the JVM launcher as needed, and verifies its reported revision before returning it. Each retained observation records the actual launcher and kernel versions from that run rather than inheriting the historical 2026-08-06 launcher identity. [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback) owns the probe method and the required persisted-read-back check.

**Two checkouts, and measurement runs in the second one.** `../a12-rulekit` stays the source of truth for reading peer code, findings, and specs, and remains strictly immutable. Observation commands run instead in the owner-approved read-only measurement checkout `../a12-rulekit-measure`, **pinned to a12-dmkits `4178ef6d11ec7d31f5f2cfb956d12b1fb3f925ea`**, re-pinned 2026-09-07 from `fc2b3187c43d0ac29cb335628dde676b69464260` to consume that revision's handback; verified at the new pin as `dmtool` 0.13.0, source clean, kernel `30.8.1` built and runtime, catalog verified against `30.8.1`. The root [`CLAUDE.md`](../CLAUDE.md) carve-out owns the exception's limits, and nothing in it permits editing, staging, or extending either checkout. The reason is availability rather than capability: the primary checkout is normally dirty because a peer session is working it, and the preparation script refuses a dirty tree, which had reduced kernel correspondence to windows lasting under a minute.

Receipts stamped an earlier pin keep their meaning, because a pin is recorded and never rewritten — which is the point of recording it. Re-pin the measurement checkout only deliberately, for an upstream instrument fix this project actually needs, and record the new revision here in the same change.

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

<a id="src-2026-09-06-ladder-handback-detail"></a>
a12-dmkits revision `7bdfa7470f7aa0baea539ffea7bd36828af19445` is the reviewed handback on [`SPEC-2026-09-06-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md). It re-derives all three ladder rungs and both pair-dependent cells on an independently built fixture, carries them as `ConstantAssignmentDiagnosticLadderLawsTest` and `KF257`, and ships the corrective the ladder implied — `MVK_INVALID_COMPARE_TO_DATE` previously had none, so an author assigning a date-shaped literal to a String field was told about dates and sent to inspect the target rather than the constant.

Two facts travel with it. Their diagnostic ledger had recorded `MVK_INCONSISTENT_TYPES_COMPARED`, `MVK_INVALID_COMPARE_TO_YES`, and `MVK_INVALID_COMPARE_TO_YESNO` as unconstructible on the strength of the **comparison** surface, where their references are kind-typed; assignment is a second live firing site those rows did not name, and all three are amended there. And the kernel lexer has **one** string-literal syntax, so a temporal constant is a string literal whose content parses as a date rather than a distinct spelling — [the ladder checkpoint](sources/static-admission-and-class-probes.md#src-constant-assignment-diagnostic-ladder) carries the local witness for that, which is prior to and independent of the grammar reading.

Revision `33411f1e2a7bc4e7dcd7b8c3cf6eba84ed911eb6` follows it and carries a third carrier for the same vocabulary, measured after this project reported the filter one: `[Handler] == "05.03.2024"` on a String field in an **ordinary rule condition** — no computation, no assignment, no filter — draws `MVK_INVALID_COMPARE_TO_DATE`, with a non-date literal at the identical site admitted as the control. That is the cleanest of the three carriers, because it removes both constructs the other two could otherwise be about. The same revision corrects the corrective shipped an hour earlier, whose text spoke of a "target" that has no referent on the two non-assignment carriers.

Both sessions independently reached the **generated equality rule** as the account of why an assignment lands in comparison vocabulary, and both record it as an open hypothesis rather than a measured mechanism: it fits every row and no rival has been eliminated.

These inbound revisions answer an existing pending entry, so they update that entry's disposition and create no new outbound request.



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

### Reviewed compute result-granularity and cascade clear-kinds — the axis the computation rows were queuing measurements for

The peer's [`§11 result-granularity finding`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf22) holds the result/application axis that a dozen `docs/implementation/computations.md` rows list as `external evidence pending`, so those rows were **not** re-measured here. `IDocumentComputationResult` is a **full** result with five channels, not a delta: successes without errors, the changed subset of those, the errored instances, the cleared instances, and operand-level formal errors. The three-channel VALUE/CLEARED/ERRORED view this project consumes — and that `:adapter:kernelProbe` writes as `computations.outcomes` — is a **projection** of that, which is the fact a consumer of these artifacts most needs and cannot see from the artifact alone.

Three rules from it bear directly on records written here. **Source identity is decided by the ingress route, per kind**: on A12's typed reader an identical seed is a silent unchanged success, while its V1 String factory leaves the cell holding unconverted text, so every non-STRING kind is unconditionally changed — with STRING as the polarity control, unchanged on both. **`getClearedFieldInstances` reports only instances filled in the input**, so clearing an already-empty computed cell reports nothing. And **the errored channel is not change-gated**, unlike the value channel.

That first rule is why every probe-based checkpoint here now states its ingress route. Two written earlier on 2026-09-07 did not, and both were corrected in place rather than left implicit: the probe reads documents through the typed `IDocumentV2Serializer`, which does not touch a claim about which value a selection returns or which rules fire, but is decisive for any claim about the change projection. The [Boolean first-filled record](sources/evaluation-and-application-routes.md#src-boolean-first-filled-false-is-filled)'s own open question — whether a seeded target would be cleared — is answered by the filled-in-input rule rather than by a measurement this project still owes.

The cascade half is jointly held and needs nothing further: the peer's [`§11 clear-kinds finding`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf240) **confirms** this project's [`SPEC-2026-09-03-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md) on a four-deep diamond, establishing that the two kinds of clear part ways at a plain operand read — an unmet precondition substitutes empty while a malformed source's poison crosses the join — and that one failing branch does not abort the plan. An out-of-range value is ERRORED and a computation reading an errored dependency is SKIPPED ([`§11`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf19)).

Inbound provenance from committed reviewed revisions, so no outbound entry. What the computations rows still owe is **family-specific** rather than mechanistic — a DateRange-specific result claim, the fixed-String first-filled target-policy composition, structural-failure scheduling — and each stays pending because a general mechanism does not discharge a claim about a carrier it was not measured on.

### Reviewed 2026-09-07 handback — the extremum leader set and the power's derived scale

a12-dmkits `4178ef6d11ec7d31f5f2cfb956d12b1fb3f925ea` disposes all thirteen actionable ledger entries, every row re-measured on the peer's own fixtures against Kernel 30.8.1 rather than carried from this project's evidence. Nine reproduce as reported. Four carry corrections, and **two of those correct clauses this project had already published**.

**The extremum's sortable leader set was wrong here.** It is `{NUMBER}` together with every temporal kind — TIME, DATE_TIME and DATE_FRAGMENT each lead successfully — and a later position admits **the leader's own class**, so DATE follows DATE and TIME follows TIME; only after a Number leader is NUMBER the sole survivor. The `limit` claiming the declared-kind axis complete was false three ways.

The peer's grid also settles the axis itself: two format strings over one component set are admitted (DATE `yyyy-MM-dd` beside DATE `dd.MM.yyyy`) while one declared kind over two sets is refused, and the bottom-left control — DATE `yyyy-MM-dd` beside DATE_FRAGMENT `yyyy-MM-dd`, ACCEPT across two kinds — is what makes it a control rather than two observations. So `MVK_DATEFORMATS_NOT_COMPATIBLE` reports the component set and never the format string it is named for. This project's Lean gate already read the set and discarded the kind, so the defect was confined to prose; `validate.laws.ExtremumOperandKindGridLawsTest` locks it there. A **typedef** field resolves to its base kind at this gate, which this project does not model at all.

**The power derives scale 0, never the base's**, and only from a scale-0 base under a nonnegative literal exponent; the discriminating cell is a scale-2 base against a scale-2 literal, refused `MVK_INVALID_COMPARE_DEC_PLACES` where the base's-scale reading predicts admission, armed by `[Rate] * [Rate] == 100.00` admitted beside it. And the **exponent is restricted** on two grounds — a known scale above 0, and an unknown-scale expression — each drawing `MVK_INVALID_NUMBER_FOR_EXP`. This project's own `spec/04` already carried both corrected facts two sentences below the false clause, so the paragraph contradicted itself and neither estate saw it; `validate.laws.PowerDerivedScaleWaiverLawsTest` locks the peer's rows.

**`SPEC-2026-09-06-04` was never a divergence.** Ordering (`< <= > >=`) runs an **orderability** gate over both operands before any kind match, and whichever side fails it the refusal is `MVK_INVALID_TYPE_FOR_COMPARISON`; equality never meets that gate and reaches the kind-match classes instead. Orderable: NUMBER, DATE, TIME, DATETIME. The discriminator is `[Boolean] > [Boolean]` refused against `[Boolean] == [Boolean]` admitted — one field, one kind, the operator the only variable. So this project's numeric column and the peer's String column are both equality columns and agree cell for cell. A CONFIRM field's comparand domain is the `True` constant alone, which is why its self-equality is refused where the other five are admitted.

Three further rows worth carrying, none of them this project's to re-measure: a **mixed-precision group expansion** is refused at all three decoding carriers **regardless of its leading declaration**, so that gate reads the whole expansion while the kind gate reads only the leader; supplementation uses the **declared** Base Year and not a sibling operand's year; and an admitted Base-Year extractor is **runtime-inert** — `YearFromDate` on a pure `HH:mm:ss` field is admitted and then decides nothing, neither the base year nor another year firing, against a liveness control that does. A consumer reading the admission row as a usable year would be wrong.

Two asks are **not** answered and stay open rather than being quietly filled. The exact resolved format literal of a format-less temporal declaration is unread on the peer's side too, and they flag the trap this project was about to walk into: `field read` returns `"format": "yyyy-MM-dd"` because their own writer substitutes the kind default into the stored bytes, so the value never reached the kernel. And which leaf reports in a multi-leaf or nested filter was not measured; carrier invariance says nothing about leaf selection.

Inbound from a committed reviewed revision, so the existing ledger entries carry the dispositions and no new outbound entry is created.

### Reviewed per-carrier group-operand admission — the extrema row this project had queued was already held

The peer's [`§9 group-operand admission table`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf187) (kernel `rule check`, 2026-08-14 with four dated amendments, locked in `validate.laws.GroupOperandCarrierAdmissionLawsTest`) answers the static row [SG23](SEMANTICS-GAPS.md#sg23--the-temporal-extrema) had recorded as this family's next ready measurement. `MinValue` and `MaxValue` over a **DATE** group are ACCEPT in both repetition shapes, unstarred and starred; over a homogeneous **STRING** group both are `MVK_NOT_SORTABLE` in both shapes, with the equivalent explicit field list drawing the same code — so the refusal is the kind's and a group behaves exactly as its expansion does at that gate. A mixed-kind expansion is a separate row and also `MVK_NOT_SORTABLE`.

Two of its rows are load-bearing here beyond admission. **ACCEPT means the kernel expanded the group and type-checked the result**, established by a DATE group against a STRING value list drawing `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` where a String group is admitted — so a consumer may rely on the expansion rather than treating ACCEPT as a waved-through group. And **arity does not count the expansion**: a group slot satisfies the param law unconditionally, exactly as a starred slot does, measured by `MoreThanOneFieldFilled(<single-field group>)` being accepted while the same lone field draws `MVK_PARAMSIZE_INVALIDN`. This project's shared gate already agrees — `ResolvedFieldEntityOperand.isAlreadyMany` is unconditionally `true` for every group and starred form — so the row is a confirmation rather than a correction, and it was checked here rather than assumed from the finding.

The internal splits are the part no analogy would have supplied: `Min`/`Max`, the operand-**list** form, refuse a group `MVK_NO_GROUPS_ALLOWED` while their `MinValue`/`MaxValue` siblings accept one, and a starred *field* there draws the separable `MVK_NO_WILDCARDS_ALLOWED`. So the min/max name does not predict the gate, and this project's separate carriers for the two forms are the right shape.

Inbound provenance from a committed reviewed revision, so it creates no outbound ledger entry. What SG23 still owes is narrower than the row it replaces: a **filtered** slot supplying the leading kind, which this table does not cover. Adjacent but not the same question, and worth not conflating: the peer's [`§6 yearless day bound`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf247) measures a yearless stored day's *validity* against the declared Base Year's leapness, not an extremum's *ordering* under one — that ordering row remains unmeasured.

### Reviewed custom-field-type, leaf-observability, and filtered-carrier batch

a12-dmkits revision `989f33bae` on `main` disposes all ten outbound entries of 2026-09-01 and 2026-09-02, arriving as a dated handback note rather than over the peer channel because no session here was reachable when it was written. Every claim in it names a lock inline, and each was resolved here by `git show` and `git ls-tree` on the revision before any disposition was written, per [`LF84`](LEAN-FINDINGS.md) rule 3.

Two of its results correct or extend clauses of this project. [`CustomFieldTypeSpiInvocationLawsTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CustomFieldTypeSpiInvocationLawsTest.kt) supplies the **full-check qualifier** the unregistered-validator paragraph lacked, the factory-versus-registry alternatives correction, and the codec's single opt-in caller — the [SPI checkpoint](sources/evaluation-and-application-routes.md#src-custom-field-type-spi) owns them.
[`FilteredStarCapacityExtentDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FilteredStarCapacityExtentDiffTest.kt) reproduces the filtered capacity extent and shows the **OMISSION polarity reaches all eight filtered carriers unconditionally**, aggregates included, where this project had measured only the three token counts; the [filtered-capacity checkpoint](sources/group-and-iteration-probes.md#src-filtered-starred-field-capacity) owns that row.

[`GroupNotFilledErroneousLeafDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupNotFilledErroneousLeafDiffTest.kt) establishes that the message-typing channel is blind to the disputed negative-presence leaf on both disjunct polarities, leaving the two estates' accounts a free choice rather than a disagreement; [`SPEC-2026-09-02-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-02-03) carries the remaining discriminator. The six remaining entries reproduced first-run on independently authored carriers.

All are inbound from a committed reviewed revision and create no outbound request by the rule above.

Revision `033fe3ef6` follows from that exchange and settles one question this project raised rather than one it reported. Asked whether `SPEC-2026-09-02-03`'s remaining discriminator is authorable at all, a12-dmkits measured it: a group-presence leaf **is** admitted inside a field-list filter, and the gate that refuses an out-of-scope condition is one gate about **scope** rather than two gates about groups. That refutes a speculation this project had written into [`spec/07`](../spec/07-repetition-and-iteration.md) — a filter naming a different group's field draws the same `MVK_NO_ITERATION_FOR_WILDCARD` and not a refusal of its own — and leaves the entry's discriminator a document run away. The [filter-condition checkpoint](sources/having-filter-probes.md#src-having-filter-condition-scope) owns the rows, the denominator, and the untested `$` remedy.

That document run happened locally on 2026-09-03 and **refuted the discriminator's own premise** rather than settling the leaf: a non-true `Having` conjunct drops its own row and leaves the aggregate available, so the filter position collapses false and unknown exactly as firing and message typing already did. The [non-true-row checkpoint](sources/having-filter-probes.md#src-having-filter-nontrue-row) owns that measurement, the empty-versus-malformed separator it produced, and the local prior art that made the premise refutable without a run.

<a id="inbound-2026-09-05b"></a>
### Reviewed 2026-09-05b handback — three entries accepted, one peer premise retracted, and one overlap found by reading

a12-dmkits revision `31348a7db` on `main` (three commits from `d1c528273`, clean before and after; the range and its subjects were resolved here with `git log` before any disposition was written) accepts [`SPEC-2026-09-05-11`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-05-11), [`-12`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-05-12) and [`-13`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-05-13), each **re-measured on the peer's own independently authored carriers** rather than carried on this project's report. Each entry holds its own disposition; three results reach beyond them.

**One clause widens.** The extrema's positional family rule was measured here on the field-list forms only, and the peer enumerated **all four** operators — `MinValue`, `MaxValue`, `Min`, `Max` — with the same two codes in the same two orders and a family-homogeneous control in both forms (`adapter.laws.ExtremaOperandFamilyRefusalLawsTest`). The value-expression pair is a different operator from the field-list pair, so this is coverage this project did not have. [`spec/07`](../spec/07-repetition-and-iteration.md) now states all four.

**One overlap this project should have found first.** The handback cites the peer's `KF211` for the temporal *classifier*, and reading that entry shows it also carries the **operand** gate — the `YearFromDate`/`HoursFromTime` pair on one date-declared TIME field, and `DifferenceInDays` beside them, kernel-oracled on both codegen strategies and dated 2026-08-28. So most of [`SPEC-2026-09-05-14`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-05-14)'s delta was already held upstream, and that entry is narrowed to the three rows `KF211` does not carry. Searching this project's own record for the mechanism would not have found it; searching the peer's would. `KF211`'s exhaustive **12-format × 3-kind** vocabulary grid is the measurement this project's [SG21](SEMANTICS-GAPS.md#sg21--the-declared-kindformat-split-across-temporal-carriers) classifier row was waiting for.

**One peer premise retracted.** [`SPEC-2026-09-01-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-01-02)'s disposition recorded a residual as theirs, and recorded their stated reason for filing rather than fixing it: that their public `compute()` exposes no operand-error channel. The peer now reports that premise was false — the channel was published and already populated — and the residual is closed. Their `KF231` is marked corrected with its measured rows unchanged. That entry's disposition is updated; nothing in this project's clause depended on it.

All three acceptances and both corrections are inbound from a committed reviewed revision and create no outbound request. The one thing that does leave this project is the *narrowing* of `-14`, which is a reduction of an already-queued entry rather than a new one.

<a id="inbound-2026-09-05c"></a>
### Reviewed 2026-09-05c handback — the reassigned row measured, and one over-admission found from a description of this project's code

a12-dmkits revision `25191913b` on `main` (two commits from `31348a7db`, clean before and after) closes the row this project reassigned to the peer and settles a policy question it had flagged without asking for.

**The reassigned row holds.** A **DATE**-declared `HH:mm:ss` field admits `HoursFromTime` — firing on `10:30:00`, silent on `11:30:00`, all three engines — and refuses `YearFromDate` with `MVK_WRONG_DATE_FORMAT_FOR_OP`, beside an ordinary-clock counterpart control. That is `KF211`'s sharpest row with **both axes flipped**, so the pair rather than either carrier is what shows the operand gate keying on the format. Their `KF250`, locked in `adapter.laws.ClockDeclaredDateGateDiffTest`. [`SPEC-2026-09-05-14`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-05-14) records the reassignment; this is its result.

**The pre-1900 policy has a third answer, and it corrected this project's `.date` arm.** The question was framed here as a two-way choice — kind-keyed or format-keyed — and is neither. A **DATE** declared `HH:mm:ss` with the opt-in check set is refused at model admission with `MVK_ADDITIONAL_CHECK_INVALID`, and the Kernel's own message keys on the components: *date fields without a year*. So the rule is that the guard requires the declared format to carry a **year**, whatever the kind. `TemporalTargetPolicy.errorFor?` had admitted every year-free Date declaration carrying it — an **over**-admission of a model the Kernel rejects, and the opposite direction from the under-admissions the declared-kind sweep was finding, which is why no case flipped when the rule landed: none carried the combination.

**And the `.time`/`.dateTime` refusals are right for a better reason than they stated.** The Kernel's `TimeType` and `DateTimeType` carry only a format and annotations at 30.8.1, so neither the opt-in check nor a date precision is a property those declaration objects have; the peer read that from source and closed the remaining link by attack, injecting the key into a `TimeType` in DM-JSON and observing the **deserializer** reject the model one layer before any gate. The shape never reaches something that could be inert, so the arms are schema facts rather than behavioural rules — which is also why they now stand redundant with the components check rather than load-bearing against it.

Both results are inbound from a committed reviewed revision and create no outbound request. The peer notes one defect of their own that the same measurement exposed and deliberately left open as delegation under-reporting rather than a wrong answer, and it is theirs to hold.

<a id="inbound-2026-09-05d"></a>
### Reviewed 2026-09-05d handback — the DateTime family's cross-kind comparison, the last item open between the two projects

a12-dmkits revision `0aca9e624` on `main` closes the one question both estates had recorded as open and neither owned. A **DATE** declared `yyyy-MM-dd'T'HH:mm:ss` is admitted against an ordinary DATE_TIME and refused `MVK_INVALID_COMPARE_TO_DATE` against an ordinary DATE; a **DATE_TIME** declared `yyyy-MM-dd` does the exact opposite; the two ordinary fields refuse each other as the control. Both admitted arms **run** tri-engine — equal operands fire, unequal stay silent — so neither admission verdict stands in for a runtime one. Oracle `checkConsistency` plus the three engines, carriers asserted from the model bytes to be the kinds they claim, locked in `adapter.laws.CrossKindTemporalComparisonGateDiffTest` beside the DATE/TIME 2x2 because it is one gate and one claim.

**So the declared format decides the family across all three date-bearing kinds, with each kind on both sides of both outcomes in every family.** Neither project's DATE/TIME grid could give that, and neither could the peer's twelve-format classifier grid: it reaches a DATE_TIME *declaration* only for the classifier, so a comparison row read off it would have been the scope transfer both projects spent the week catching in each other. The peer measured it rather than leaving it correctly declined, on the ground that four rounds of naming it open had cost more than one model would.

**This project's cases had already committed to the answer.** The ordinary comparison gate is one component-keyed function shared with the measured pair — `compareFields` reads the two component sets and carries the declared kinds into the operand without consulting them — so the account was live and merely unstated. The cases landed as *committed but unmeasured* and the confirmation arrived the same day, first run, every cell. What stays internal is the **equality/ordering split** across a cross-kind pair: the inbound rows measure equality only, and the pair equality refuses is ordering-comparable through the same gate.

Inbound from a committed reviewed revision, so no outbound request. Nothing is now open between the two projects on this class.

<a id="inbound-2026-09-05e"></a>
### Reported 2026-09-05e — `NumberOfDifferentValues`' temporal admission gate, peer-reported and not yet re-derived here

a12-dmkits reports, from `validate.laws.TemporalAggregateComponentSetLawsTest` at revision `13287df21` on `main`, that this operator's temporal admission is the extrema's **component-set** gate rather than `FieldValuesNotUnique`'s identical-declared-format gate. Three rows in one model: `NumberOfDifferentValues(yyyy-MM-dd, dd.MM.yyyy)` admitted, `NumberOfDifferentValues(yyyy-MM-dd, yyyy-MM)` refused `MVK_DATEFORMATS_NOT_COMPATIBLE`, and `FieldValuesNotUnique` refused on that same admitted first pair. A declared Base Year supplements YEAR into both sets before the comparison and does not lift the uniqueness refusal.

**This is a peer report, not a pin, and it is recorded that way deliberately.** The peer characterised it as a read of their committed test source with a confirming run still in flight, and asked that it be re-derived on this project's own fixtures before any clause rests on it. No local `dmtool` row exists: a clean-sibling window opened at `13287df21` and closed within the minute when the peer began their identity measurement, so nothing was measured here and the sibling was not written to. [SG22](SEMANTICS-GAPS.md#sg22--numberofdifferentvalues-operand-domain-and-its-two-homogeneity-codes) owns the re-derivation obligation.

Two consequences for this project's own records, both corrections of local error rather than inbound deltas. SG22's stated **recommendation** was format-equality, which would have over-rejected the admitted differently-spelled pair — the inverse of the over-admission class it was guarding against, and a case where [`LF116`](LEAN-FINDINGS.md)'s refusal to carry a gate across a carrier was the correct instinct. SG22's **premise** for the compared-identity question — that a mandatory single format makes the decoded and stored-text accounts agree on every constructible input — is refuted by the same rows, since the admitted pair supplies the separating witness. That premise was an unmeasured reachability claim and is withdrawn.

The compared-identity question itself is a runtime claim requiring a kernel/interpreter differential, which is a12-dmkits' harness; it stays with them and is not routed through `dmtool` from here.

<a id="inbound-2026-09-05f"></a>
### Reported 2026-09-05f — the distinct count's temporal identity is the decoded date, and the first-operand grid's envelope

a12-dmkits reports `NumberOfDifferentValues` counting temporal operands by **decoded date**, not stored text, from `adapter.laws.DistinctCountTemporalIdentityDiffTest` — an adapter differential asserting kernel dynamic-Groovy and their interpreter agree per cell before any value is pinned. Three DATE fields on one root group, component set {YEAR, MONTH, DAY}, no Base Year declared so supplementation is not a second variable, rule shape `FieldFilled(Reference) And NumberOfDifferentValues(A, B) == N` with `N` probed at both 1 and 2.

The four cells are a genuine separating matrix rather than one witness. `2024-03-05` beside `05.03.2024` counts **1**; the same cross-spelling pair with `06.03.2024` counts **2**; and a same-spelling arm counts 1 and 2 on equal and unequal dates. Row one alone would not settle it — a count of 1 is equally consistent with a decoded comparison and with an engine that cannot compare across spellings and folds the pair — and row two is what defeats that second reading. The peer states row one's admission is asserted inside the test rather than assumed, without which all four cells would measure a model that does not exist.

The same message carries their `KF226` envelope for the first-operand grid, oracle `checkConsistency` via `BoundModel.ofJson`, each refusal pinning the rival code **absent** rather than only the expected one. Number-first draws `MVK_NUMBER_AND_NON_NUMBER`, String-first `MVK_STRING_ENUM_AND_NON_STRING_ENUM`, Date-first `MVK_DATE_AND_NONDATE`, Boolean-first `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED`, each against its flipped pair, with a homogeneous accept control. Their Date field is `dd.MM.yyyy` so the date-first row is a real cross-family mix; `MVK_DATEFORMATS_NOT_COMPATIBLE` is reachable from a same-family pair on this operator and would be easy to mistake for the class result.

**Two limits the peer stated and this project must carry.** The grid is two-operand throughout, so "the first operand fixes the class" is measured at arity 2 and not where a third family enters; and every row places the offender second, so the flip separates naming-the-offender from naming-the-leading-class but does not measure a list violating the leading class twice.

Peer-reported when received and **now locally re-derived on both codegen strategies** ([checkpoint](sources/evaluation-and-application-routes.md#src-distinct-count-temporal-identity-both-strategies)). [SG24](SEMANTICS-GAPS.md#sg24--the-temporal-distinct-counts-fold) owns the re-derivation obligation and this project's own rows already agree with the grid independently, on different fixtures against the same terminal oracle.

<a id="inbound-2026-09-06b"></a>
### Reported 2026-09-06b — the kernel supplies no diagnostic code at all, and every `MVK_*` this project consumes is a12-dmkits' extraction from the message

a12-dmkits reports, committed `9b3ca5a6b`, that the kernel's `Notification` carries only a **severity and a message**: there is no code field, and every `code` in their output — including the `codes` array this project's `batch --observations` artifacts retain — is derived by them from the message's terminal bracketed key. Measured at both their layers, `RuleValidator` and `dmtool rule check`, agreeing with this project's own rows for `@SuppressWarning`.

The correction they landed is to their own [`KF75`](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf75), which had stated since June that a rejected suppression name's *code* is the attempted name itself. That was never a statement about the kernel; it described their extractor while reading as a kernel quirk. They explicitly declined to claim the tidier history — that an older extraction rule once produced the attempted name — because the pre-2026-08-23 last-match `MVK_*` scan also lands on the bracketed key, so the story is unsubstantiated rather than merely unrecorded.

**Consequence here, and it is a phrasing rule rather than a data correction.** No retained code changes and no conformance case moves: the bracketed key is the kernel's own identifier inside its own message, so the codes remain sound refusal-class identities. What changes is the class of claim this project may make about them — the kernel's message carries the key; the kernel does not report a code — and therefore that any future claim about a code's *shape* is a claim about the extractor and needs their layer to settle it, not a `rule check` row. The [engine routing rule](#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) owns that limit.

This is an inbound correction from a committed, reviewed revision, so it is recorded as provenance and raises no outbound ledger entry.

<a id="inbound-2026-09-06a"></a>
### Reported 2026-09-06a — the operand/target binding relation transfers from the computation carrier to the rule carrier unchanged

a12-dmkits reports the binding relation holding on every cell of a nine-row table, committed `d7344e6c9`, oracle `checkConsistency`, run executed with 3 tests and 0 failures, recorded as their `KF255`. The fixture is the computation law's verbatim, so the carrier is the only variable: root policy, repeatable `Claims` with nested repeatable `Items`, and three repeatable siblings of `Claims` differing only in their index declaration. Form-level into one-level and two-level targets, one level up into a two-level target, own level, and a sibling whose index field carries the same name are all admitted; one level below the target, a repeatable into a form-level target, and a sibling with no index field draw `MVK_NO_WILDCARD`; a sibling whose index field has another name draws `MVK_ERROR_FIELD_INVALID_INDEX`.

Two readings the peer supplied with it. Vacuity is excluded by the sibling triple rather than by a separate control: one helper returns three different outcomes over three groups differing only in their index declaration, which neither a defaulting harness nor an unreached condition can produce. And the carriers are genuinely asymmetric — a rule's condition must reference its error field, so every rule row carries two operands where the computation rows carried one, and the error-field read is itself a scope participant. The verdict is identical anyway, so the relation does not count operands, but that was not derivable in advance.

The peer flagged their own epistemic position: they expected the computation rows and every row matched, which is weaker than a run that surprised them, and invited independent re-derivation. Done — seven of the nine rows reproduce on this project's own fixture, plus a depth-2 row their table does not carry ([checkpoint](sources/static-admission-and-class-probes.md#src-filtered-star-temporal-carriers-and-binding-depth)).

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
<a id="src-temporal-operation-granularity-separability"></a>
- [A temporal operation's operand gate needs the unit's own component, and only two of its axes are separable on declared formats](sources/temporal-and-message-probes.md#src-temporal-operation-granularity-separability)
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
<a id="src-keyed-parameter-admits-the-index-field-only"></a>
- [A keyed parameter admits the condition's own keyed field or the group's index field, and nothing else](sources/message-and-pointer-probes.md#src-keyed-parameter-admits-the-index-field-only)

<a id="src-rulegroup-shorthand-root-gate"></a>
- [`$#RuleGroup$` alone is refused when its owning declaration sits directly in the root group](sources/message-and-pointer-probes.md#src-rulegroup-shorthand-root-gate)
<a id="src-rulegroup-root-gate-on-the-rule-carrier"></a>
- [That same root-group refusal is the validation-rule carrier's too](sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier)

<a id="src-2026-09-05-german-shorthand-render-reconciliation"></a>
- [Reviewed a12-dmkits handback rendering the German shorthands, closing the retired-terminal row, and confirming the computation carrier on render](sources/message-and-pointer-probes.md#src-2026-09-05-german-shorthand-render-reconciliation)

<a id="src-2026-09-05-group-parameter-render-reconciliation"></a>
- [Reviewed a12-dmkits handback completing the group position's bilingual table and separating the rendered coordinate on a doubly nested topology](sources/message-and-pointer-probes.md#src-2026-09-05-group-parameter-render-reconciliation)

<a id="src-2026-09-05-second-reconciliation"></a>
- [Reviewed a12-dmkits letter accepting the two-gate entry, correcting its attribution, and narrowing two clauses this project had already accepted](sources/computation-placement-and-constant-probes.md#src-2026-09-05-second-reconciliation) — also the route for their shipped `dmtool operators Having` gate text, read by running the launcher at `ede777e55`

<a id="src-2026-09-05-reconciliation"></a>
- [Reviewed 2026-09-04 a12-dmkits letter closing all four outbound entries, correcting one clause of ours, and shipping all four instrument fixes](sources/computation-placement-and-constant-probes.md#src-2026-09-05-reconciliation)

<a id="src-2026-09-06-ladder-handback"></a>
- [Reviewed 2026-09-06 a12-dmkits handback re-deriving the constant-assignment ladder and shipping its corrective](#src-2026-09-06-ladder-handback-detail)
<a id="src-2026-09-04-reconciliation"></a>
- [Reviewed 2026-09-04 a12-dmkits handback adopting both temporal corrections, and refuting one claim of ours](sources/computation-placement-and-constant-probes.md#src-2026-09-04-reconciliation)
<a id="src-2026-09-03-reconciliation"></a>
- [Reviewed 2026-09-03 a12-dmkits handback on the nine `Having`, capture, and temporal entries](sources/computation-placement-and-constant-probes.md#src-2026-09-03-reconciliation)
<a id="src-2026-08-30-reconciliation"></a>
- [Reviewed 2026-08-30 a12-dmkits reconciliation, retraction, and instrument answers](sources/computation-placement-and-constant-probes.md#src-2026-08-30-reconciliation)
<a id="src-2026-08-29-reconciliation"></a>
- [Reviewed 2026-08-29 a12-dmkits reconciliation and correction batch](sources/computation-placement-and-constant-probes.md#src-2026-08-29-reconciliation)
<a id="src-date-range-direct-list-cross-group-sources"></a>
- [A direct-list `FirstFilledValue` places its sources freely](sources/computation-placement-and-constant-probes.md#src-date-range-direct-list-cross-group-sources)
<a id="src-having-filter-condition-scope"></a>
- [A `Having` condition must bind the filtered list's own iterated level, and admits a group-presence leaf](sources/having-filter-probes.md#src-having-filter-condition-scope)
<a id="src-having-filter-nontrue-row"></a>
- [A non-true `Having` conjunct drops its own row, and the empty-as-zero rule does not reach a malformed operand](sources/having-filter-probes.md#src-having-filter-nontrue-row)
<a id="src-having-filter-condition-grammar"></a>
- [A `Having` condition is the ordinary condition grammar, and every refusal reached is an ordinary one](sources/having-filter-probes.md#src-having-filter-condition-grammar)
<a id="src-having-filter-presence-leaf"></a>
- [Both presence polarities are real per-row filter predicates and exact complements over clean cells](sources/having-filter-probes.md#src-having-filter-presence-leaf)
<a id="src-having-filter-disjunction"></a>
- [A filter's `Or` is strong-Kleene, so a true disjunct keeps its row against an unavailable one](sources/having-filter-probes.md#src-having-filter-disjunction)
<a id="src-string-inequality-empty-operand"></a>
- [An absent String operand suppresses its comparison under inequality too](sources/having-filter-probes.md#src-string-inequality-empty-operand)
<a id="src-filtered-aggregate-computation-arm"></a>
- [A filtered aggregate's computation arm poisons on a reached operand and never reads an excluded one](sources/having-filter-probes.md#src-filtered-aggregate-computation-arm)
<a id="src-and-order-computation-arm"></a>
- [A filter's conjunction short-circuits on a false operand too, so the computation arm's order sensitivity is not the disjunction's alone](sources/having-filter-probes.md#src-and-order-computation-arm)
<a id="src-off-path-captured-filter-runtime"></a>
- [An admitted off-path `$` reference is evaluated per host row](sources/having-filter-probes.md#src-off-path-captured-filter-runtime)

<a id="src-filter-scope-versus-iteration-gates"></a>
- [A filter's scope gate and its other-iteration prohibition are two gates, separated by one conjunct](sources/having-filter-probes.md#src-filter-scope-versus-iteration-gates)

<a id="src-currentrepetition-operand-carriers"></a>
- [The operand is an ordinary Number expression wherever one is legal, while `$` is filter-only by site and no aggregate accepts it](sources/group-and-iteration-probes.md#src-currentrepetition-operand-carriers)

<a id="src-filter-repetition-reference-reads-its-path"></a>
- [A `CurrentRepetition` leaf answers both filter gates through its path's repeatable scope, so a nonrepeatable group under the star satisfies the scope gate alone](sources/having-filter-probes.md#src-filter-repetition-reference-reads-its-path)

<a id="src-filter-reference-above-the-star"></a>
- [A level above the star but still on the operand's path is scope-gated and rescuable, not iteration-prohibited](sources/having-filter-probes.md#src-filter-reference-above-the-star)

<a id="src-parameter-token-versus-group-declaration-alphabet"></a>
- [The parameter's name token is wider than any group may be named, and a quoted segment is refused where the bare spelling reaches lookup](sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet)

<a id="src-terminal-bundle-on-the-computation-carrier"></a>
- [The parameter terminal bundle is shared with the computation message carrier, where `RuleGroup` names the computation's own group](sources/message-and-pointer-probes.md#src-terminal-bundle-on-the-computation-carrier)

<a id="src-name-position-index-terminal"></a>
- [`index(...)` is a live name-position terminal with three refusal codes of its own, and the group position has no index syntax at all](sources/message-and-pointer-probes.md#src-name-position-index-terminal)

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
- [The pattern comparison's left-kind gate is total: DATE_RANGE draws the same class as the other seven kinds](sources/static-admission-and-class-probes.md#src-pattern-comparison-left-kind-gate-is-total)
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
- [Every later-position kind draws `MVK_DATE_AND_NONDATE` at the temporal extrema, and a starred group over a nonrepeatable terminal is admitted with its expansion gated](sources/static-admission-and-class-probes.md#src-later-position-class-is-total-and-presence-is-admitted)
<a id="src-later-position-kinds-and-group-expansion-class"></a>
- [A Boolean in a temporal extremum's later position draws `MVK_DATE_AND_NONDATE`; a mixed starred-group expansion draws `MVK_NOT_SORTABLE` instead](sources/static-admission-and-class-probes.md#src-later-position-kinds-and-group-expansion-class)
<a id="src-first-filled-reads-the-format-string"></a>
- [The four entity-list carriers split two-and-two on one field pair: the extrema and the distinct count read the component set, `FirstFilledValue` and `FieldValuesNotUnique` read the format string](sources/static-admission-and-class-probes.md#src-first-filled-reads-the-format-string)
<a id="src-filtered-star-supplies-the-leading-kind"></a>
- [A `Having`-filtered star supplies the extremum's leading kind exactly as a plain star does, measured on the pairing](sources/static-admission-and-class-probes.md#src-filtered-star-supplies-the-leading-kind)
<a id="src-filtered-star-temporal-carriers-and-binding-depth"></a>
- [A `Having`-filtered star is admitted wherever a plain star is on all three temporal carriers, the component gate reads through it, and the binding relation re-derives independently](sources/static-admission-and-class-probes.md#src-filtered-star-temporal-carriers-and-binding-depth)
<a id="src-distinct-count-component-set-and-locus"></a>
- [`NumberOfDifferentValues` gates temporal operands by component set, not declared format; date-first class and group-presence locus confirmed locally](sources/static-admission-and-class-probes.md#src-distinct-count-component-set-and-locus)
<a id="src-distinct-count-operand-domain"></a>
- [`NumberOfDifferentValues` admits Custom as string-like, splits homogeneity into two codes, and counts expanded operands for arity](sources/static-admission-and-class-probes.md#src-distinct-count-operand-domain)

<a id="src-extensible-enumeration-has-no-dm-json-carrier"></a>
- [Extensible Enumeration is a String type's runtime quality with no DM-JSON carrier](sources/static-admission-and-class-probes.md#src-extensible-enumeration-has-no-dm-json-carrier)
<a id="src-validtype-operand-gates"></a>
- [The custom-type validity operand gates, with their exact codes and the two confusable wildcard refusals](sources/static-admission-and-class-probes.md#src-validtype-operand-gates)

<a id="src-aggregate-operand-list-takes-paths-only"></a>
- [Composition is one-way: an aggregate nests inside a wrapper, but no expression nests inside an aggregate's operand list](sources/computation-placement-and-constant-probes.md#src-aggregate-operand-list-takes-paths-only)

<a id="src-power-derived-scale-and-operand-shapes"></a>
- [`^` restricts neither operand's shape; a non-literal exponent derives unknown scale, and that is what a computed target refuses](sources/computation-placement-and-constant-probes.md#src-power-derived-scale-and-operand-shapes)

<a id="src-computed-temporal-target-reads-the-format-not-the-kind"></a>
- [A computed temporal target is gated by its declared format string and not by its declared kind, on all three of the Time, Date, and DateTime families](sources/computation-placement-and-constant-probes.md#src-computed-temporal-target-reads-the-format-not-the-kind)
<a id="src-temporal-value-family-is-the-formats-not-the-kinds"></a>
- [A temporal field's value family is its declared format's, not its declared kind's](sources/computation-placement-and-constant-probes.md#src-temporal-value-family-is-the-formats-not-the-kinds)
<a id="src-temporal-operand-family-is-the-formats-not-the-kinds"></a>
- [A temporal operand's admitted family is its declared format's too, extractors and completed-period differences alike, with a Base Year completing the year the format omits](sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds)
<a id="src-yearless-day-bound-reads-the-base-year"></a>
- [A yearless stored day is bounded by its month's length in the declared Base Year](sources/computation-placement-and-constant-probes.md#src-yearless-day-bound-reads-the-base-year)
<a id="src-datetime-carrier-stores-by-its-format"></a>
- [The DATETIME carrier's cross-kind store is governed by its format too, inbound from a12-dmkits](sources/computation-placement-and-constant-probes.md#src-datetime-carrier-stores-by-its-format)

<a id="src-two-positions-share-the-root-gate"></a>
- [Both parameter positions share one root gate and then split, the name position answering `INVALID_ENTITY` where the group position answers `INVALID_GROUP`](sources/message-and-pointer-probes.md#src-two-positions-share-the-root-gate)

<a id="src-presence-confirm-custom-carriers"></a>
- [The presence leaf admits Confirm and Custom, and an unregistered Custom type faults only on a present value](sources/having-filter-probes.md#src-presence-confirm-custom-carriers)
<a id="src-nested-self-exclusion"></a>
- [Self-exclusion survives nesting under a disjunction and still tracks the evaluating row](sources/having-filter-probes.md#src-nested-self-exclusion)
<a id="src-three-level-filter-nesting"></a>
- [A filter's bracketing is honoured at three levels, separated from two flattenings by one document](sources/having-filter-probes.md#src-three-level-filter-nesting)
<a id="src-correlated-filter-string-computed-target"></a>
- [A correlated filter drives a String computed target, and an empty candidate set produces no outcome](sources/having-filter-probes.md#src-correlated-filter-string-computed-target)
<a id="src-currentrepetition-host-iteration"></a>
- [`CurrentRepetition` is admitted exactly where the enclosing iteration binds its group](sources/having-filter-probes.md#src-currentrepetition-host-iteration)
<a id="src-self-exclusion-and-nested-filter-runtime"></a>
- [`CurrentRepetition` self-exclusion is an exact complement pair, `$` binds a per-row computed target, and a nested `Or` selects its own rows](sources/having-filter-probes.md#src-self-exclusion-and-nested-filter-runtime)
<a id="src-presence-leaf-operand-kinds"></a>
- [The presence leaf reads the same three states on a temporal, Enumeration, DateRange, and Boolean operand](sources/having-filter-probes.md#src-presence-leaf-operand-kinds)
<a id="src-bare-outer-reference-redundant-marker"></a>
- [On a level the star does not reopen, the `$` marker is admitted, redundant, and not what satisfies the scope gate](sources/having-filter-probes.md#src-bare-outer-reference-redundant-marker)
<a id="src-correlated-filter-runtime"></a>
- [`$` binds the captured outer row and the candidate set includes it](sources/having-filter-probes.md#src-correlated-filter-runtime)
<a id="src-pattern-invalid-string-cell"></a>
- [A pattern or length violation makes the cell formally invalid on the validation arm](sources/evaluation-and-application-routes.md#src-pattern-invalid-string-cell)
<a id="src-filter-condition-carrier-independence"></a>
- [The filter is checked and evaluated identically on every operand carrier](sources/having-filter-probes.md#src-filter-condition-carrier-independence)
<a id="src-nested-correlated-filter-and-poison-scope"></a>
- [Multi-level correlation matches the one-level account, the scope gate is syntactic, and computation poison is per instance](sources/having-filter-probes.md#src-nested-correlated-filter-and-poison-scope)
<a id="src-outer-origin-filter-leaves"></a>
- [A `$`-marked reference does not bind the filtered level, and both newer leaves read the captured row](sources/having-filter-probes.md#src-outer-origin-filter-leaves)

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
<a id="src-mandatory-information-repeatable-presence"></a>
- [Mandatory-information derivation preserves connective and starred presence-operator identity](sources/rule-set-meta-information.md#src-mandatory-information-repeatable-presence)
<a id="src-mandatory-information-composition-matrix"></a>
- [Mandatory-information derivation distinguishes root-relative fields and finite dependency closure](sources/rule-set-meta-information.md#src-mandatory-information-composition-matrix)
<a id="src-mandatory-information-boolean-formulas"></a>
- [Mandatory-information derivation preserves two-level negative-field Boolean structure](sources/rule-set-meta-information.md#src-mandatory-information-boolean-formulas)
<a id="src-mandatory-information-boolean-formula-positions"></a>
- [Mandatory-information 2×2 negative-field formulas ignore shared-field position](sources/rule-set-meta-information.md#src-mandatory-information-boolean-formula-positions)
<a id="src-mandatory-information-field-cycles"></a>
- [Mandatory-information derivation closes a seeded direct field cycle and leaves an unseeded cycle inert](sources/rule-set-meta-information.md#src-mandatory-information-field-cycles)
<a id="src-mandatory-information-field-list-cycles"></a>
- [Mandatory-information derivation closes seeded existential and universal field-list cycles without self-support](sources/rule-set-meta-information.md#src-mandatory-information-field-list-cycles)
<a id="src-mandatory-information-longer-cycles"></a>
- [Mandatory-information derivation closes exact four-node direct and multi-list-edge cycles without self-support](sources/rule-set-meta-information.md#src-mandatory-information-longer-cycles)
<a id="src-mandatory-information-field-list-guards"></a>
- [Mandatory-information derivation distinguishes existential and universal filled-field guards](sources/rule-set-meta-information.md#src-mandatory-information-field-list-guards)
<a id="src-mandatory-information-distinct-count"></a>
- [Mandatory-information derivation preserves filled-count and distinct-count operator identity](sources/rule-set-meta-information.md#src-mandatory-information-distinct-count)
<a id="src-mandatory-information-info-severity"></a>
- [Mandatory-information derivation ignores INFO negative field rules](sources/rule-set-meta-information.md#src-mandatory-information-info-severity)
<a id="src-mandatory-information-reversed-strict-count"></a>
- [Mandatory-information derivation recognizes reversed strict filled-count guards](sources/rule-set-meta-information.md#src-mandatory-information-reversed-strict-count)
<a id="src-mandatory-information-false-count-guards"></a>
- [Mandatory-information derivation admits false filled-count guards](sources/rule-set-meta-information.md#src-mandatory-information-false-count-guards)
<a id="src-mandatory-information-count-seed-cardinality"></a>
- [Mandatory-information derivation returns the zero-, one-, and two-seed filled-count results](sources/rule-set-meta-information.md#src-mandatory-information-count-seed-cardinality)
<a id="src-mandatory-information-count-dependencies"></a>
- [Mandatory-information derivation closes through a dependency-derived filled-count operand and reused target](sources/rule-set-meta-information.md#src-mandatory-information-count-dependencies)
<a id="src-mandatory-information-count-chain"></a>
- [Mandatory-information derivation closes one filled-count target-to-operand chain](sources/rule-set-meta-information.md#src-mandatory-information-count-chain)
<a id="src-mandatory-information-count-chain-orders"></a>
- [Mandatory-information count-chain closure is stable across all six measured category orders](sources/rule-set-meta-information.md#src-mandatory-information-count-chain-orders)
<a id="src-mandatory-information-count-target-only"></a>
- [Mandatory-information derivation returns an isolated true count target and its root](sources/rule-set-meta-information.md#src-mandatory-information-count-target-only)
<a id="src-mandatory-information-distinct-target-only"></a>
- [Mandatory-information derivation keeps isolated distinct-count targets inert](sources/rule-set-meta-information.md#src-mandatory-information-distinct-target-only)
<a id="src-mandatory-information-distinct-comparisons"></a>
- [Mandatory-information derivation preserves the isolated distinct-count comparison matrix](sources/rule-set-meta-information.md#src-mandatory-information-distinct-comparisons)
<a id="src-mandatory-information-declared-required"></a>
- [Mandatory-information derivation separates unconditional and parent-present field declarations](sources/rule-set-meta-information.md#src-mandatory-information-declared-required)
<a id="src-mandatory-information-declaration-closure"></a>
- [Parent-present field declarations close from declaration, root, and direct-field seeds](sources/rule-set-meta-information.md#src-mandatory-information-declaration-closure)
<a id="src-mandatory-information-semantic-index"></a>
- [A semantic-indexed operand excludes every referenced field from mandatory-information derivation](sources/rule-set-meta-information.md#src-mandatory-information-semantic-index)
<a id="src-mandatory-information-parallel-iteration"></a>
- [A parallel-iterated rule contributes no referenced field to mandatory information](sources/rule-set-meta-information.md#src-mandatory-information-parallel-iteration)
<a id="src-mandatory-information-cross-root"></a>
- [A cross-root negative disjunction contributes neither referenced field nor its independent root](sources/rule-set-meta-information.md#src-mandatory-information-cross-root)
<a id="src-mandatory-information-generated-index"></a>
- [A generated optional repeatable String index requirement contributes nothing and supplies no global root seed](sources/rule-set-meta-information.md#src-mandatory-information-generated-index)
<a id="src-mandatory-information-generated-computation-validation"></a>
- [A direct nonrepeatable scale-0 Number copy's generated validation contributes nothing and supplies no global root seed](sources/rule-set-meta-information.md#src-mandatory-information-generated-computation-validation)

<a id="src-over-limit-computation-target"></a>
- [An over-limit row receives no computed value](sources/group-list-and-capacity-probes.md#src-over-limit-computation-target)
<a id="src-boolean-first-filled-false-is-filled"></a>
- [`FirstFilledValue` selects a Boolean `false` because its filled predicate is presence, and an all-empty selection mints no outcome](sources/evaluation-and-application-routes.md#src-boolean-first-filled-false-is-filled)
<a id="src-yearless-extrema-base-year-ordering"></a>
- [The extrema order a yearless list under a declared Base Year on both strategies, and no document on such a model can say what they order on](sources/evaluation-and-application-routes.md#src-yearless-extrema-base-year-ordering)
<a id="src-extrema-component-omitting-fold"></a>
- [The extrema fold a component-omitting operand, yearless included, and order it correctly](sources/evaluation-and-application-routes.md#src-extrema-component-omitting-fold)
<a id="src-cross-kind-format-runtime-parser"></a>
- [The runtime text parser is the declared format's, not the declared kind's](sources/evaluation-and-application-routes.md#src-cross-kind-format-runtime-parser)
<a id="src-distinct-count-group-expansion-fold"></a>
- [A group operand's distinct count reaches its whole subtree at runtime, and an uninstantiated row contributes nothing](sources/evaluation-and-application-routes.md#src-distinct-count-group-expansion-fold)
<a id="src-distinct-count-time-bearing-fold"></a>
- [The distinct count folds a time-bearing operand too, and a TIME agrees with a time-only DATETIME](sources/evaluation-and-application-routes.md#src-distinct-count-time-bearing-fold)
<a id="src-distinct-count-component-omitting-fold"></a>
- [The distinct count folds a component-omitting date at its declared precision](sources/evaluation-and-application-routes.md#src-distinct-count-component-omitting-fold)
<a id="src-distinct-count-temporal-identity-both-strategies"></a>
- [The distinct count's temporal identity is the decoded date on both codegen strategies](sources/evaluation-and-application-routes.md#src-distinct-count-temporal-identity-both-strategies)
<a id="src-filter-reference-two-levels-above"></a>
- [Both filter gates read path membership and nothing about depth, and the admitted constant is keyed to the referenced level](sources/having-filter-probes.md#src-filter-reference-two-levels-above)
<a id="src-filter-reference-level-runtime"></a>
- [An admitted filter reference the star does not reopen is a constant, per host row or per document](sources/having-filter-probes.md#src-filter-reference-level-runtime)
<a id="src-repeatable-computation-row-extent"></a>
- [A repeatable computation's row extent is exactly the instantiated rows, with no phantom tail](sources/group-list-and-capacity-probes.md#src-repeatable-computation-row-extent)
<a id="src-distinct-count-first-operand-class"></a>
- [`NumberOfDifferentValues` classifies by its first operand](sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)
<a id="src-extrema-operand-family-is-positional"></a>
- [`MinValue`/`MaxValue` pick their operand family from the first operand, and the two families draw different codes](sources/group-list-and-capacity-probes.md#src-extrema-operand-family-is-positional)
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
<a id="src-short-name-flag-gates-the-model-wide-tier"></a>
- [`fieldRefByShortNameAllowed` gates the model-wide short-name tier and not the declaring-group one](sources/group-and-iteration-probes.md#src-short-name-flag-gates-the-model-wide-tier)
<a id="src-multi-root-short-name-reach"></a>
- [A model may declare more than one root group, and the short-name tier spans them](sources/group-and-iteration-probes.md#src-multi-root-short-name-reach)
<a id="src-message-group-parameter"></a>
- [The rule-message group parameter `$#…$`](sources/message-and-pointer-probes.md#src-message-group-parameter)
<a id="src-german-condition-language-terminals"></a>
- [The group position's keyword set is selected by condition language in both directions, and the retired terminals are not](sources/message-and-pointer-probes.md#src-german-condition-language-terminals)

<a id="src-message-group-parameter-rendered-index"></a>
- [An admitted group parameter renders the firing row's repetition index](sources/message-and-pointer-probes.md#src-message-group-parameter-rendered-index)

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
<a id="src-extrema-sortable-kind-set"></a>
- [The extrema's admitted kind set is Number or Date](sources/inbound-group-operand-batches.md#src-extrema-sortable-kind-set)
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
<a id="src-temporal-format-gate-not-component-sets"></a>
- [The temporal admission gate reads family and year agreement, never component sets](sources/computation-placement-and-constant-probes.md#src-temporal-format-gate-not-component-sets)
<a id="src-yearless-anchor-is-the-base-year"></a>
- [A yearless temporal literal resolves against the model's Base Year, while its calendar check ignores that year](sources/computation-placement-and-constant-probes.md#src-yearless-anchor-is-the-base-year)
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
<a id="src-repeatable-diamond-per-row-states"></a>
- [A repeatable dependency diamond keeps all three producer states apart within one call](sources/evaluation-and-application-routes.md#src-repeatable-diamond-per-row-states)
<a id="src-diamond-dependency-clear-kinds"></a>
- [A four-deep dependency diamond orders correctly, and a silently cleared producer reads EMPTY where an errored one poisons](sources/evaluation-and-application-routes.md#src-diamond-dependency-clear-kinds)
<a id="src-scalar-mixed-reverse-authored-triple"></a>
- [Reverse-authored mixed scalar triple, measured locally 2026-09-01](sources/evaluation-and-application-routes.md#src-scalar-mixed-reverse-authored-triple)
<a id="src-numeric-extremum-call-boundary"></a>
- [Numeric extremum call boundary](sources/evaluation-and-application-routes.md#src-numeric-extremum-call-boundary)
<a id="src-custom-field-type-spi"></a>
- [Custom field type SPI: full-check raise and the codec's single opt-in caller](sources/evaluation-and-application-routes.md#src-custom-field-type-spi)

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
